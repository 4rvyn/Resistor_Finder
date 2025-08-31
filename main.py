##################################################################################
# Author:    Arvin Parvizinia
# Date:      2025-05-16
# Version:   1.0
##################################################################################

import sys
import time
import html
import datetime

import heapq
import bisect
import traceback

import mmap
import math
import os
import struct
from array import array


from PyQt6.QtWidgets import (
    QApplication, QMainWindow, QWidget, QVBoxLayout, QHBoxLayout,
    QGridLayout, QLabel, QLineEdit, QComboBox, QSpinBox,
    QCheckBox, QPushButton, QTextEdit, QFrame, QGroupBox,
    QDialog
)
from PyQt6.QtCore import Qt, QThread, pyqtSignal, QObject
from PyQt6.QtGui import QFont, QTextCursor

# --- Constants ---
OHM_SYMBOL = "\u03A9"  # Ohm symbol

CONFIG_COLORS = {
    "Single": "#1E90FF",      # DodgerBlue
    "Series (2)": "#32CD32",  # LimeGreen
    "Parallel (2)": "#FF8C00", # DarkOrange
    "Series (3)": "#228B22",  # ForestGreen
    "Parallel (3)": "#FFA500", # Orange
    "Mixed S-P": "#9932CC",   # DarkOrchid
    "Mixed P-S": "#4682B4",   # SteelBlue
    "default": "#000000"      # Black for any unexpected case
}

# --- E-Series Definitions ---
E12_BASE_VALUES = [1.0, 1.2, 1.5, 1.8, 2.2, 2.7, 3.3, 3.9, 4.7, 5.6, 6.8, 8.2]
E24_BASE_VALUES = [1.0, 1.1, 1.2, 1.3, 1.5, 1.6, 1.8, 2.0, 2.2, 2.4, 2.7, 3.0, 3.3, 3.6, 3.9, 4.3, 4.7, 5.1, 5.6, 6.2, 6.8, 7.5, 8.2, 9.1]
E96_BASE_VALUES = [1.00, 1.02, 1.05, 1.07, 1.10, 1.13, 1.15, 1.18, 1.21, 1.24, 1.27, 1.30, 1.33, 1.37, 1.40, 1.43, 1.47, 1.50, 1.54, 1.58, 1.62, 1.65, 1.69, 1.74, 1.78, 1.82, 1.87, 1.91, 1.96, 2.00, 2.05, 2.10, 2.15, 2.21, 2.26, 2.32, 2.37, 2.43, 2.49, 2.55, 2.61, 2.67, 2.74, 2.80, 2.87, 2.94, 3.01, 3.09, 3.16, 3.24, 3.32, 3.40, 3.48, 3.57, 3.65, 3.74, 3.83, 3.92, 4.02, 4.12, 4.22, 4.32, 4.42, 4.53, 4.64, 4.75, 4.87, 4.99, 5.11, 5.23, 5.36, 5.49, 5.62, 5.76, 5.90, 6.04, 6.19, 6.34, 6.49, 6.65, 6.81, 6.98, 7.15, 7.32, 7.50, 7.68, 7.87, 8.06, 8.25, 8.45, 8.66, 8.87, 9.09, 9.31, 9.53, 9.76]

# --- Helper Functions ---
def format_resistor_value(r_value):
    if r_value is None: return "N/A"
    if r_value == float('inf'): return "Inf"
    abs_r = abs(r_value)
    if abs_r >= 1_000_000_000: return f"{r_value / 1_000_000_000:.3f} G{OHM_SYMBOL}"
    if abs_r >= 1_000_000:     return f"{r_value / 1_000_000:.3f} M{OHM_SYMBOL}"
    if abs_r >= 1_000:         return f"{r_value / 1_000:.3f} k{OHM_SYMBOL}"
    if abs_r < 1 and abs_r > 1e-4: return f"{r_value * 1000:.3f} m{OHM_SYMBOL}"
    return f"{r_value:.3f} {OHM_SYMBOL}"

def parallel_calc(*resistors):
    inv_sum = 0
    for r in resistors:
        if r is None or r <= 0: return float('inf')
        try:
            inv_sum += 1.0 / r
        except ZeroDivisionError: return float('inf')
    if inv_sum == 0: return float('inf')
    return 1.0 / inv_sum

def _get_deviation_color(perc_dev, max_dev):
    if max_dev <= 0: max_dev = 1
    ratio = max(0.0, min(1.0, perc_dev / max_dev))
    red = int(255 * ratio)
    green = int(255 * (1 - ratio))
    blue = 0
    return f'#{red:02x}{green:02x}{blue:02x}'



# ===========================
# Precompute loader & helpers
# ===========================

ROOT_DIR = os.path.dirname(os.path.abspath(__file__))
ASSET_FILES = {
    'E12': os.path.join(ROOT_DIR, 'assets', 'rcf_e12.bin'),
    'E24': os.path.join(ROOT_DIR, 'assets', 'rcf_e24.bin'),
    'E96': os.path.join(ROOT_DIR, 'assets', 'rcf_e96.bin'),
}


# Fixed-point scales used when generating the binaries
R_SCALE = 10**8    # integer units per ohm for R-arrays
G_SCALE = 10**12   # integer units per siemens for G-arrays

# Header layout used by the generator/validator we built earlier.
# Fields (little-endian):
#   magic[4] = b'RCF1'
#   version  = u32 (1)
#   nSingles = u32 (n)
#   nPairs   = u32 (m)
#   off_R, off_G, off_mant, off_dec, off_S_sum, off_S_i, off_S_j, off_G_sum, off_G_i, off_G_j = 10 * u64
#   payload_crc32 = u32  (CRC of everything after the header)
_HEADER_FMT = '<4sIII' + 'Q'*10 + 'I'
_HEADER_SIZE = struct.calcsize(_HEADER_FMT)

class Precomp:
    __slots__ = ('path', 'n', 'm',
                 'R', 'G', 'mant', 'dec',
                 'S_sum', 'S_i', 'S_j',
                 'P_sum', 'P_i', 'P_j')
    def __init__(self): pass

_PRECOMP_CACHE = {}  # keyed by series 'E12'/'E24'/'E96'

def _read_array(f, off, count, code):
    """Read a numeric array from offset using array('code')."""
    if count == 0:
        return array(code)
    bps = array(code).itemsize
    f.seek(off)
    buf = f.read(count * bps)
    a = array(code)
    a.frombytes(buf)
    if sys.byteorder != 'little':
        a.byteswap()
    return a

def load_precomp(series: str, log):
    """
    Load precompute container created by precomp.py.
    Returns an object with typed memoryviews into the mmapped file, e.g.:
      H.R, H.G, H.mant, H.dec, H.S_sum, H.S_i, H.S_j, H.G_sum, H.G_i, H.G_j
    Plus metadata: H.n, H.m, H.scale_R, H.scale_G, etc.
    """
    path = ASSET_FILES.get(series)
    if not path:
        raise ValueError(f"Unknown E-series '{series}'")
    log(f"  Opening precompute: {path}", level=1)

    f = open(path, 'rb')
    mm = mmap.mmap(f.fileno(), 0, access=mmap.ACCESS_READ)

    # Header is little-endian; layout must match precomp.py::pack_header
    # Fixed part (through scales):
    # <4s I B B b b H I Q Q Q Q Q Q
    hdr_fixed_fmt = "<4s I B B b b H I Q Q Q Q Q Q"
    hdr_fixed_size = struct.calcsize(hdr_fixed_fmt)
    if len(mm) < hdr_fixed_size:
        mm.close(); f.close()
        raise ValueError("Precompute file too small to contain fixed header")

    hdr_fixed = struct.unpack_from(hdr_fixed_fmt, mm, 0)
    magic, version, endian_flag, e_series_id, dec_min, dec_max, _pad0, \
        n_singles, n_pairs_series, n_pairs_parallel, \
        R_SCALE_NUM, R_SCALE_DEN, G_SCALE_NUM, G_SCALE_DEN = hdr_fixed

    # === checks ===
    if magic != b"RCF\x00":
        mm.close(); f.close()
        raise ValueError(
            f"Bad magic in precompute file (got {magic!r}) at {path}. "
            f"Expected b'RCF\\x00'."
        )
    if version != 1:
        mm.close(); f.close()
        raise ValueError(f"Unsupported precompute version {version} (expected 1)")
    if endian_flag != 0:
        mm.close(); f.close()
        raise ValueError("Only little-endian payloads are supported (endian_flag != 0)")
    expected_id = {'E12':12, 'E24':24, 'E96':96}[series]
    if e_series_id != expected_id:
        mm.close(); f.close()
        raise ValueError(f"E-series id mismatch: file={e_series_id}, requested {expected_id}")

    # Offsets/lengths for 10 arrays (offset,len) pairs
    names = [
        "R","G","mantissa_idx","decade",
        "S_sum","S_i","S_j",
        "G_sum","G_i","G_j"
    ]
    pairs_fmt = "<" + "QQ"*len(names)
    pairs_size = struct.calcsize(pairs_fmt)
    pairs_off = hdr_fixed_size
    if len(mm) < pairs_off + pairs_size + 8:  # +8 for checksum
        mm.close(); f.close()
        raise ValueError("Precompute file too small to contain array offset table")

    pairs_vals = struct.unpack_from(pairs_fmt, mm, pairs_off)
    offsets = {}
    for i, nm in enumerate(names):
        off = pairs_vals[2*i+0]
        ln  = pairs_vals[2*i+1]
        offsets[nm] = (off, ln)

    # payload checksum (we don't recompute here; precompval.py already did)
    checksum = struct.unpack_from("<Q", mm, pairs_off + pairs_size)[0]

    # Helper to create typed memoryviews (no copies)
    mv = memoryview(mm)

    def view_q(off, count):  # int64
        if off == 0 or count == 0: return None
        b = mv[off: off + count*8]
        return b.cast('q')

    def view_Q(off, count):  # uint64 (not used here, but for symmetry)
        if off == 0 or count == 0: return None
        b = mv[off: off + count*8]
        return b.cast('Q')

    def view_I(off, count):  # uint32
        if off == 0 or count == 0: return None
        b = mv[off: off + count*4]
        return b.cast('I')

    def view_H(off, count):  # uint16
        if off == 0 or count == 0: return None
        b = mv[off: off + count*2]
        return b.cast('H')

    def view_b(off, count):  # int8
        if off == 0 or count == 0: return None
        b = mv[off: off + count*1]
        return b.cast('b')

    # Build the holder object
    class Holder: pass
    H = Holder()
    H.mm = mm
    H.f = f  # (optional) file handle; mm keeps mapping alive regardless
    H.path = path

    H.n = n_singles
    H.m_series = n_pairs_series
    H.m_parallel = n_pairs_parallel
    H.decade_min = dec_min
    H.decade_max = dec_max

    # Scales (as floats for convenience)
    H.scale_R = (R_SCALE_NUM, R_SCALE_DEN)
    H.scale_G = (G_SCALE_NUM, G_SCALE_DEN)
    H.R_units_per_ohm = R_SCALE_NUM / R_SCALE_DEN     # 1e8
    H.G_units_per_S   = G_SCALE_NUM / G_SCALE_DEN     # 1e12 (pS)

    # Views
    off,len_ = offsets["R"];             H.R = view_q(off, len_)
    off,len_ = offsets["G"];             H.G = view_q(off, len_)
    off,len_ = offsets["mantissa_idx"];  H.mant = view_H(off, len_)
    off,len_ = offsets["decade"];        H.dec = view_b(off, len_)

    off,len_ = offsets["S_sum"];         H.S_sum = view_q(off, len_)
    off,len_ = offsets["S_i"];           H.S_i   = view_I(off, len_)
    off,len_ = offsets["S_j"];           H.S_j   = view_I(off, len_)

    off,len_ = offsets["G_sum"];         H.G_sum = view_q(off, len_)
    off,len_ = offsets["G_i"];           H.G_i   = view_I(off, len_)
    off,len_ = offsets["G_j"];           H.G_j   = view_I(off, len_)


    off,len_ = offsets["G_sum"];         H.G_sum = view_q(off, len_)
    off,len_ = offsets["G_i"];           H.G_i   = view_I(off, len_)
    off,len_ = offsets["G_j"];           H.G_j   = view_I(off, len_)

    # Back-compat aliases so the search code can use P_* for parallel (conductance)
    H.P_sum = H.G_sum
    H.P_i   = H.G_i
    H.P_j   = H.G_j


    # Quick sanity (optional)
    if H.R is None or len(H.R) != H.n:
        mm.close(); f.close()
        raise ValueError("R array missing or length mismatch")
    if H.G is None or len(H.G) != H.n:
        mm.close(); f.close()
        raise ValueError("G array missing or length mismatch")

    return H


# ---------- integer math helpers ----------
def ceil_div_pos(a, b):  # a,b > 0
    return (a + b - 1) // b

def band_on_sorted(arr, lo, hi):
    """Return [l, r) indices such that lo <= arr[idx] <= hi; arr is nondecreasing."""
    l = bisect.bisect_left(arr, lo)
    r = bisect.bisect_right(arr, hi)
    if r < l: r = l
    return l, r

def build_allowed(dec_arr, dec_lo, dec_hi):
    """Boolean mask of singles allowed by decade range inclusive."""
    return [ (dec_lo <= d <= dec_hi) for d in dec_arr ]



# --- Core Calculation Logic ---
def find_resistor_combinations(
    target_value,
    allowed_deviation_percent,
    max_components,
    selected_e_series,
    range_min_factor,
    range_max_factor,
    series_allowed,
    parallel_allowed,
    mixed_allowed,
    stop_event,
    queue_func
):
    start_time = time.time()
    results = []

    # dedicated logger
    def log(message, level=0):
        timestamp = datetime.datetime.now().strftime('%H:%M:%S.%f')[:-3]
        indent = "  " * level
        queue_func(f"[{timestamp}] {indent}{message}")

    try:
        # ================
        # LOAD PRECOMPUTE
        # ================
        log("[SETUP]")
        log(f"E-Series: {selected_e_series}", 1)
        H = load_precomp(selected_e_series, log)

        # Build decade filter
        dec_lo = int(range_min_factor); dec_hi = int(range_max_factor)
        allowed = build_allowed(H.dec, dec_lo, dec_hi)

        # Convert UI target & tolerance → integer bands
        tol = allowed_deviation_percent / 100.0
        T_min = target_value * (1.0 - tol)
        T_max = target_value * (1.0 + tol)

        # Scaled bands
        R_min = int(math.ceil(T_min * R_SCALE))
        R_max = int(math.floor(T_max * R_SCALE))
        # For parallel: conductance band  [G_min, G_max]
        if T_max <= 0 or T_min <= 0:
            return [], 0
        G_min = int(math.ceil(G_SCALE / T_max))
        G_max = int(math.floor(G_SCALE / T_min))

        log(f"Target: {format_resistor_value(target_value)}", 1)
        log(f"Tolerance: {allowed_deviation_percent:.6f}%", 1)
        log(f"Decades allowed: 10^{dec_lo} .. 10^{dec_hi}", 1)

        # progress bookkeeping (rough but monotone)
        total_steps = 1
        steps_done = 0
        def bump(n=1):
            nonlocal steps_done
            steps_done += n
            if steps_done % 200 == 0:
                queue_func({'type':'progress', 'current': steps_done, 'total': max(total_steps, steps_done)})

        # Small helpers to emit results
        def emit_single(k):
            r1 = H.R[k] / R_SCALE
            combined = r1
            abs_dev = abs(combined - target_value)
            perc_dev = (abs_dev / target_value) * 100.0
            results.append({
                'config': 'Single',
                'topology': 'R1',
                'r1': r1, 'r2': None, 'r3': None,
                'combined_r': combined,
                'abs_dev': abs_dev,
                'perc_dev': perc_dev
            })

        def emit_series2(i,j):
            r1 = H.R[i] / R_SCALE; r2 = H.R[j] / R_SCALE
            combined = r1 + r2
            abs_dev = abs(combined - target_value)
            perc_dev = (abs_dev / target_value) * 100.0
            results.append({
                'config': 'Series (2)', 'topology': 'R1+R2',
                'r1': r1, 'r2': r2, 'r3': None,
                'combined_r': combined, 'abs_dev': abs_dev, 'perc_dev': perc_dev
            })

        def emit_parallel2(i,j):
            gsum = H.G[i] + H.G[j]
            if gsum <= 0: return
            combined = (G_SCALE / gsum)
            r1 = H.R[i] / R_SCALE; r2 = H.R[j] / R_SCALE
            abs_dev = abs(combined - target_value)
            perc_dev = (abs_dev / target_value) * 100.0
            results.append({
                'config': 'Parallel (2)', 'topology': 'R1||R2',
                'r1': r1, 'r2': r2, 'r3': None,
                'combined_r': combined, 'abs_dev': abs_dev, 'perc_dev': perc_dev
            })

        def emit_series3(i,j,k):
            r1 = H.R[i] / R_SCALE; r2 = H.R[j] / R_SCALE; r3 = H.R[k] / R_SCALE
            combined = r1 + r2 + r3
            abs_dev = abs(combined - target_value)
            perc_dev = (abs_dev / target_value) * 100.0
            results.append({
                'config': 'Series (3)', 'topology': 'R1+R2+R3',
                'r1': r1, 'r2': r2, 'r3': r3,
                'combined_r': combined, 'abs_dev': abs_dev, 'perc_dev': perc_dev
            })

        def emit_parallel3(i,j,k):
            gsum = H.G[i] + H.G[j] + H.G[k]
            if gsum <= 0: return
            combined = (G_SCALE / gsum)
            r1 = H.R[i] / R_SCALE; r2 = H.R[j] / R_SCALE; r3 = H.R[k] / R_SCALE
            abs_dev = abs(combined - target_value)
            perc_dev = (abs_dev / target_value) * 100.0
            results.append({
                'config': 'Parallel (3)', 'topology': 'R1||R2||R3',
                'r1': r1, 'r2': r2, 'r3': r3,
                'combined_r': combined, 'abs_dev': abs_dev, 'perc_dev': perc_dev
            })

        def emit_mixed_SP(i,j,k):
            # R1 + (R2||R3)
            gsum = H.G[i] + H.G[j]
            if gsum <= 0: return
            r_par = (G_SCALE / gsum)
            r1 = H.R[k] / R_SCALE
            combined = r1 + r_par
            r2 = H.R[i] / R_SCALE; r3 = H.R[j] / R_SCALE
            abs_dev = abs(combined - target_value)
            perc_dev = (abs_dev / target_value) * 100.0
            results.append({
                'config': 'Mixed S-P', 'topology': 'R1+(R2||R3)',
                'r1': r1, 'r2': r2, 'r3': r3,
                'combined_r': combined, 'abs_dev': abs_dev, 'perc_dev': perc_dev
            })

        def emit_mixed_PS(i,j,k):
            # R1 || (R2+R3)
            ssum = H.R[i] + H.R[j]
            denom = (H.R[k] + ssum)
            if denom <= 0: return
            # compute in float for display
            r1 = H.R[k] / R_SCALE; s = ssum / R_SCALE
            combined = (r1 * s) / (r1 + s)
            r2 = H.R[i] / R_SCALE; r3 = H.R[j] / R_SCALE
            abs_dev = abs(combined - target_value)
            perc_dev = (abs_dev / target_value) * 100.0
            results.append({
                'config': 'Mixed P-S', 'topology': 'R1||(R2+R3)',
                'r1': r1, 'r2': r2, 'r3': r3,
                'combined_r': combined, 'abs_dev': abs_dev, 'perc_dev': perc_dev
            })

        # ==========================
        # N=1 (band on singles R[])
        # ==========================
        log("[SEARCHING]", 0)
        if max_components >= 1:
            l, r = band_on_sorted(H.R, R_min, R_max)
            total_steps += (r - l)
            log(f"Singles band: {r-l} candidates", 1)
            for k in range(l, r):
                if stop_event.is_set(): raise InterruptedError()
                if allowed[k]:
                    emit_single(k)
                bump()

        # ==========================
        # N=2 (Series / Parallel)
        # ==========================
        if max_components >= 2:
            if series_allowed:
                l, r = band_on_sorted(H.S_sum, R_min, R_max)
                total_steps += (r - l)
                log(f"Series(2) band: {r-l} pairs", 1)
                for idx in range(l, r):
                    if stop_event.is_set(): raise InterruptedError()
                    i = H.S_i[idx]; j = H.S_j[idx]
                    if allowed[i] and allowed[j]:
                        emit_series2(i, j)
                    bump()

            if parallel_allowed:
                l, r = band_on_sorted(H.P_sum, G_min, G_max)
                total_steps += (r - l)
                log(f"Parallel(2) band: {r-l} pairs", 1)
                for idx in range(l, r):
                    if stop_event.is_set(): raise InterruptedError()
                    i = H.P_i[idx]; j = H.P_j[idx]
                    if allowed[i] and allowed[j]:
                        emit_parallel2(i, j)
                    bump()

        # ==========================================
        # N=3 (Series, Parallel, Mixed S-P, Mixed P-S)
        # ==========================================
        if max_components >= 3:
            # Precompute list of allowed singles to loop outer k
            allowed_indices = [k for k in range(H.n) if allowed[k]]

            if series_allowed:
                log("Series(3): scanning per-k windows over S_sum ...", 1)
                for k in allowed_indices:
                    if stop_event.is_set(): raise InterruptedError()
                    Rk = H.R[k]
                    lo = R_min - Rk
                    hi = R_max - Rk
                    if hi < lo: 
                        continue
                    l, r = band_on_sorted(H.S_sum, lo, hi)
                    total_steps += (r - l)
                    for idx in range(l, r):
                        i = H.S_i[idx]; j = H.S_j[idx]
                        # de-dup: ensure the outer k is >= j (emit each unordered triple once)
                        if not (allowed[i] and allowed[j]): 
                            continue
                        if j > k:
                            continue
                        emit_series3(i, j, k)
                    bump()

            if parallel_allowed:
                log("Parallel(3): scanning per-k windows over P_sum ...", 1)
                for k in allowed_indices:
                    if stop_event.is_set(): raise InterruptedError()
                    Gk = H.G[k]
                    lo = G_min - Gk
                    hi = G_max - Gk
                    if hi < lo:
                        continue
                    l, r = band_on_sorted(H.P_sum, lo, hi)
                    total_steps += (r - l)
                    for idx in range(l, r):
                        i = H.P_i[idx]; j = H.P_j[idx]
                        if not (allowed[i] and allowed[j]):
                            continue
                        if j > k:
                            continue
                        emit_parallel3(i, j, k)
                    bump()

            if mixed_allowed:
                # Mixed S-P : R1 + (R2||R3)  → for each R1 use a G_sum window derived from R-band
                log("Mixed S-P: per-k G_sum windows derived from R-band ...", 1)
                for k in allowed_indices:
                    if stop_event.is_set(): raise InterruptedError()
                    r1_ohm = H.R[k] / R_SCALE
                    # Desired parallel branch must satisfy: r_par ∈ [T_min - r1, T_max - r1]
                    tp_min_ohm = T_min - r1_ohm
                    tp_max_ohm = T_max - r1_ohm
                    # If the parallel part must be positive, clip the lower bound slightly above 0
                    if tp_max_ohm <= 0:
                        continue
                    if tp_min_ohm <= 0:
                        tp_min_ohm = 1e-12  # avoid div-by-zero; any tiny positive number is fine

                    # Convert resistance window → conductance window in pS
                    gL = int(math.ceil(G_SCALE / tp_max_ohm))   # lower conductance bound
                    gU = int(math.floor(G_SCALE / tp_min_ohm))  # upper conductance bound
                    if gU < gL:
                        continue

                    l, r = band_on_sorted(H.P_sum, gL, gU)

                    total_steps += (r - l)
                    for idx in range(l, r):
                        i = H.P_i[idx]; j = H.P_j[idx]
                        if allowed[i] and allowed[j]:
                            emit_mixed_SP(i, j, k)
                    bump()

                # Mixed P-S : R1 || (R2+R3)  → feasible only if R1 > R_max
                log("Mixed P-S: per-k S_sum windows derived from parallel algebra ...", 1)
                for k in allowed_indices:
                    if stop_event.is_set(): raise InterruptedError()
                    R1 = H.R[k]
                    if R1 <= R_max:
                        continue
                    # S in [S_min, S_max] where:
                    # S_min = ceil( R_min*R1 / (R1 - R_min) )
                    # S_max = floor( R_max*R1 / (R1 - R_max) )
                    # All integer in R_SCALE domain:
                    S_min_num = R_min * R1
                    S_min_den = (R1 - R_min)
                    if S_min_den <= 0:
                        continue
                    S_min = ceil_div_pos(S_min_num, S_min_den)

                    S_max_num = R_max * R1
                    S_max_den = (R1 - R_max)
                    if S_max_den <= 0:
                        continue
                    S_max = S_max_num // S_max_den

                    if S_max < S_min:
                        continue
                    l, r = band_on_sorted(H.S_sum, S_min, S_max)
                    total_steps += (r - l)
                    for idx in range(l, r):
                        i = H.S_i[idx]; j = H.S_j[idx]
                        if allowed[i] and allowed[j]:
                            emit_mixed_PS(i, j, k)
                    bump()

        # wrap up
        queue_func({'type':'progress', 'current': steps_done, 'total': max(total_steps, steps_done)})
        log("[SUMMARY]")
        log(f"Found {len(results)} combinations within tolerance.", 1)
        log(f"Total time: {time.time() - start_time:.3f} s", 1)
        return results, max(total_steps, steps_done)

    except InterruptedError:
        queue_func({'type':'progress', 'current': 1, 'total': 1, 'status':'Stopped'})
        return None, 0
    except Exception as e:
        queue_func({'type':'progress', 'current': 1, 'total': 1, 'status':'Error'})
        tb = traceback.format_exc()
        log("[CALCULATION ERROR] " + str(e), 0)
        for line in tb.splitlines():
            log(line, 1)
        return None, 0


# --- Qt Worker for Calculations ---
class CalculationWorker(QObject):
    progress_updated = pyqtSignal(int, int, str)
    text_output_signal = pyqtSignal(str)
    calculation_finished_signal = pyqtSignal(object, int)

    def __init__(self, *calc_args):
        super().__init__()
        self.args_for_calc_func = calc_args

    def run_calculation(self):
        class StopEventChecker:
            def is_set(self):
                return QThread.currentThread().isInterruptionRequested()

        def qt_queue_func_adapter(message):
            if isinstance(message, dict) and message.get('type') == 'progress':
                self.progress_updated.emit(
                    message.get('current', 0),
                    message.get('total', 0),
                    message.get('status', '')
                )
            else:
                self.text_output_signal.emit(str(message))

        actual_calc_args = list(self.args_for_calc_func)
        actual_calc_args.append(StopEventChecker()) # Append stop event
        actual_calc_args.append(qt_queue_func_adapter) # Append queue func

        results, total_checks = find_resistor_combinations(*actual_calc_args)
        self.calculation_finished_signal.emit(results, total_checks)

# --- Qt6 GUI Application ---
class ResistorCalculatorApp(QMainWindow):
    def __init__(self):
        super().__init__()
        self.setWindowTitle(f"Resistor Combination Finder")
        self.setGeometry(100, 100, 1300, 800)

        self.central_widget = QWidget()
        self.setCentralWidget(self.central_widget)
        self.main_layout = QVBoxLayout(self.central_widget)

        self.calculation_qthread = None
        self.worker = None
        self.current_results = []
        self.last_used_deviation_limit = 0.1
        self.estimated_total_checks = 0
        self.help_dialog = None

        # --- Default control values ---
        self._default_max_components = 3
        self._default_e_series = 'E12'
        self._default_range_min = -3
        self._default_range_max = 7
        self._default_series_allowed = True
        self._default_parallel_allowed = True
        self._default_mixed_allowed = True

        self._setup_ui()
        self._connect_signals()

    def _setup_ui(self):
        top_part_widget = QWidget()
        top_part_layout = QHBoxLayout(top_part_widget)
        top_part_layout.setContentsMargins(0, 0, 0, 0)
        self.control_widget = QWidget()
        control_main_v_layout = QVBoxLayout(self.control_widget)
        control_grid_layout = QGridLayout()
        control_main_v_layout.addLayout(control_grid_layout)
        self.output_widget = QWidget()
        self.output_layout = QVBoxLayout(self.output_widget)
        top_part_layout.addWidget(self.control_widget, 0)
        top_part_layout.addWidget(self.output_widget, 1)
        self.control_widget.setMaximumWidth(270)
        self.main_layout.addWidget(top_part_widget, 1)
        row_num = 0
        control_grid_layout.addWidget(QLabel("Target Value:"), row_num, 0, Qt.AlignmentFlag.AlignLeft)
        self.target_entry = QLineEdit("866")
        control_grid_layout.addWidget(self.target_entry, row_num, 1)
        self.unit_combo = QComboBox()
        self.unit_combo.addItems([f"m{OHM_SYMBOL}", f"{OHM_SYMBOL}", f"k{OHM_SYMBOL}", f"M{OHM_SYMBOL}", f"G{OHM_SYMBOL}"])
        self.unit_combo.setCurrentText(f"k{OHM_SYMBOL}")
        control_grid_layout.addWidget(self.unit_combo, row_num, 2)
        row_num += 1
        control_grid_layout.addWidget(QLabel("Max Deviation (%):"), row_num, 0, Qt.AlignmentFlag.AlignLeft)
        self.deviation_entry = QLineEdit("0.1")
        control_grid_layout.addWidget(self.deviation_entry, row_num, 1, 1, 2)
        row_num += 1
        self.disclaimer_label = QLabel("Caution: E96, E24, wide range or N=3\ncan increase calculation time significantly.")
        self.disclaimer_label.setStyleSheet("color: #FF4500;")
        default_font = QApplication.font()
        disclaimer_font = QFont(default_font.family(), int(default_font.pointSize() * 0.9) if default_font.pointSize() > 0 else 8)
        self.disclaimer_label.setFont(disclaimer_font)
        control_grid_layout.addWidget(self.disclaimer_label, row_num, 0, 1, 3)
        row_num += 1
        control_grid_layout.addWidget(QLabel("E-Series:"), row_num, 0, Qt.AlignmentFlag.AlignLeft)
        self.eseries_combo = QComboBox()
        self.eseries_combo.addItems(['E12', 'E24', 'E96'])
        self.eseries_combo.setCurrentText(self._default_e_series)
        control_grid_layout.addWidget(self.eseries_combo, row_num, 1, 1, 2)
        row_num += 1
        control_grid_layout.addWidget(QLabel("Max Components (N):"), row_num, 0, Qt.AlignmentFlag.AlignLeft)
        self.max_comp_spin = QSpinBox()
        self.max_comp_spin.setRange(1, 3)
        self.max_comp_spin.setValue(self._default_max_components)
        control_grid_layout.addWidget(self.max_comp_spin, row_num, 1, 1, 2)
        row_num += 1
        control_grid_layout.addWidget(QLabel("Range Min (10^):"), row_num, 0, Qt.AlignmentFlag.AlignLeft)
        self.range_min_spin = QSpinBox()
        self.range_min_spin.setRange(-3, 9)
        self.range_min_spin.setValue(self._default_range_min)
        control_grid_layout.addWidget(self.range_min_spin, row_num, 1, 1, 2)
        row_num += 1
        control_grid_layout.addWidget(QLabel("Range Max (10^):"), row_num, 0, Qt.AlignmentFlag.AlignLeft)
        self.range_max_spin = QSpinBox()
        self.range_max_spin.setRange(-3, 9)
        self.range_max_spin.setValue(self._default_range_max)
        control_grid_layout.addWidget(self.range_max_spin, row_num, 1, 1, 2)
        row_num += 1
        separator1 = QFrame()
        separator1.setFrameShape(QFrame.Shape.HLine)
        separator1.setFrameShadow(QFrame.Shadow.Sunken)
        control_grid_layout.addWidget(separator1, row_num, 0, 1, 3)
        row_num += 1
        control_grid_layout.addWidget(QLabel("Allowed Configurations:"), row_num, 0, 1, 3, Qt.AlignmentFlag.AlignLeft)
        row_num += 1
        self.series_check = QCheckBox("Series (N=2, N=3)")
        self.series_check.setChecked(self._default_series_allowed)
        control_grid_layout.addWidget(self.series_check, row_num, 0, 1, 3)
        row_num += 1
        self.parallel_check = QCheckBox("Parallel (N=2, N=3)")
        self.parallel_check.setChecked(self._default_parallel_allowed)
        control_grid_layout.addWidget(self.parallel_check, row_num, 0, 1, 3)
        row_num += 1
        self.mixed_check = QCheckBox("Mixed (N=3 Only)")
        self.mixed_check.setChecked(self._default_mixed_allowed)
        control_grid_layout.addWidget(self.mixed_check, row_num, 0, 1, 3)
        self._update_mixed_check_state()
        row_num += 1
        button_container = QWidget()
        button_box_layout = QHBoxLayout(button_container)
        button_box_layout.setContentsMargins(0,0,0,0)
        self.run_button = QPushButton("Run"); self.run_button.setFixedWidth(80)
        button_box_layout.addWidget(self.run_button)
        self.stop_button = QPushButton("Stop"); self.stop_button.setFixedWidth(80)
        self.stop_button.setEnabled(False)
        button_box_layout.addWidget(self.stop_button)
        self.clear_button = QPushButton("Clear"); self.clear_button.setFixedWidth(80)
        button_box_layout.addWidget(self.clear_button)
        button_box_layout.addStretch(1)
        control_grid_layout.addWidget(button_container, row_num, 0, 1, 3)
        row_num += 1
        sort_group_box = QGroupBox("Sort Results By")
        sort_layout = QHBoxLayout()
        self.sort_dev_button = QPushButton("Deviation (%)")
        self.sort_dev_button.setEnabled(False)
        sort_layout.addWidget(self.sort_dev_button)
        self.sort_config_button = QPushButton("Config Type")
        self.sort_config_button.setEnabled(False)
        sort_layout.addWidget(self.sort_config_button)
        sort_group_box.setLayout(sort_layout)
        control_grid_layout.addWidget(sort_group_box, row_num, 0, 1, 3)
        row_num += 1

        control_grid_layout.setRowStretch(row_num, 1)
        control_main_v_layout.addStretch(1)
        self.help_button = QPushButton("Help?")
        self.help_button.setFixedWidth(80)
        help_button_layout = QHBoxLayout()
        help_button_layout.addWidget(self.help_button)
        help_button_layout.addStretch(1)
        control_main_v_layout.addLayout(help_button_layout)
        self.output_layout.addWidget(QLabel("Results:"))
        self.output_text = QTextEdit()
        self.output_text.setReadOnly(True)
        self.output_text.setFont(QFont("Courier New", 9))
        self.output_text.setMinimumWidth(700)
        self.output_layout.addWidget(self.output_text, 1)
        self.progress_label = QLabel("")
        self.progress_label.setFont(QFont("Courier New", 9))
        self.output_layout.addWidget(self.progress_label)
        log_group_box = QGroupBox("Calculation Log")
        log_group_box.setCheckable(True)
        log_group_box.setChecked(False)
        log_layout = QVBoxLayout(log_group_box)
        log_layout.setContentsMargins(5, 5, 5, 5)
        self.log_console = QTextEdit()
        self.log_console.setReadOnly(True)
        self.log_console.setFont(QFont("Courier New", 9))
        self.log_console.setVisible(False)
        log_group_box.toggled.connect(self.log_console.setVisible)
        log_layout.addWidget(self.log_console)
        self.main_layout.addWidget(log_group_box, 0)

    def _connect_signals(self):
        self.run_button.clicked.connect(self.start_calculation)
        self.stop_button.clicked.connect(self.stop_calculation)
        self.clear_button.clicked.connect(self.clear_fields)
        self.sort_dev_button.clicked.connect(lambda: self.sort_by_deviation(display_message=True))
        self.sort_config_button.clicked.connect(lambda: self.sort_by_config(display_message=True))
        self.help_button.clicked.connect(self.show_help_window)
        self.max_comp_spin.valueChanged.connect(self._update_mixed_check_state)

    def _update_mixed_check_state(self):
        is_n_less_than_3 = self.max_comp_spin.value() < 3
        self.mixed_check.setEnabled(not is_n_less_than_3)
        if is_n_less_than_3:
            self.mixed_check.setChecked(False)

    def _update_button_states(self, is_running):
        widgets_to_disable_during_run = [
            self.target_entry, self.deviation_entry, self.max_comp_spin,
            self.range_min_spin, self.range_max_spin, self.series_check,
            self.parallel_check, self.mixed_check,
            self.unit_combo, self.eseries_combo,
            self.help_button,
        ]
        self.run_button.setEnabled(not is_running)
        self.stop_button.setEnabled(is_running)
        self.clear_button.setEnabled(not is_running)
        for widget in widgets_to_disable_during_run: widget.setEnabled(not is_running)
        if not is_running:
            self._update_mixed_check_state()
            self._update_sort_button_state()
        else:
            self.sort_dev_button.setEnabled(False)
            self.sort_config_button.setEnabled(False)

    def _update_sort_button_state(self):
        calculation_running = self.calculation_qthread and self.calculation_qthread.isRunning()
        has_results = bool(self.current_results)
        self.sort_dev_button.setEnabled(has_results and not calculation_running)
        self.sort_config_button.setEnabled(has_results and not calculation_running)

    def _log_gui_event(self, message):
        """Logs a GUI-side event with a timestamp to the log console."""
        timestamp = datetime.datetime.now().strftime('%H:%M:%S.%f')[:-3]
        self.log_console.append(f"[{timestamp}] [GUI] {message}")
        self.log_console.moveCursor(QTextCursor.MoveOperation.End)

    def append_text_to_output(self, text_message):
        """Handles messages from the worker thread."""
        if text_message == "__DISPLAY_RESULTS__":
            self._display_results(self.current_results)
            if self.estimated_total_checks > 0:
                bar_width = 40
                bar_text = '[' + '#' * bar_width + ']'
                final_text = f"Progress: {bar_text} 100.0% ({self.estimated_total_checks:,}/{self.estimated_total_checks:,}) [Complete]"
            else:
                final_text = "Calculation Complete (No checks performed)."
            self.progress_label.setText(final_text)
        else:
            self.log_console.append(str(text_message))
            self.log_console.moveCursor(QTextCursor.MoveOperation.End)

    def update_progress_display(self, current, total, status_str):
        self.estimated_total_checks = total
        if total > 0:
            percent = (current / total) * 100
            bar_width = 40
            filled_width = int(bar_width * current / total)
            bar_text = '[' + '#' * filled_width + '-' * (bar_width - filled_width) + ']'
            progress_display_text = f"Progress: {bar_text} {percent:.1f}% ({current:,}/{total:,})"
            if status_str: progress_display_text += f" [{status_str}]"
        elif status_str: progress_display_text = f"Status: {status_str}"
        else: progress_display_text = "Starting..."
        self.progress_label.setText(progress_display_text)

    def clear_output_console(self):
        self.output_text.clear()
        self.current_results = []
        self._update_sort_button_state()

    def clear_fields(self):
        if self.calculation_qthread and self.calculation_qthread.isRunning():
            self.stop_calculation()
        self.clear_output_console()
        self.progress_label.setText("")
        self.estimated_total_checks = 0
        self._log_gui_event("Results window cleared.")

    def start_calculation(self):
        if self.calculation_qthread and self.calculation_qthread.isRunning():
            self._log_gui_event("Calculation already in progress.")
            return

        self.clear_output_console()
        self.progress_label.setText("Preparing calculation...")
        self.estimated_total_checks = 0

        self.log_console.append("\n" + "="*50)
        self._log_gui_event("New calculation initiated.")
        self.current_results = []

        try:
            target_val_part = float(self.target_entry.text())
            target_unit = self.unit_combo.currentText()
            deviation = float(self.deviation_entry.text())
            max_comp = self.max_comp_spin.value()
            e_series = self.eseries_combo.currentText()
            range_min = self.range_min_spin.value()
            range_max = self.range_max_spin.value()
            series_allowed = self.series_check.isChecked()
            parallel_allowed = self.parallel_check.isChecked()
            mixed_allowed = self.mixed_check.isChecked() and (max_comp >= 3)

            if deviation < 0: raise ValueError("Deviation cannot be negative.")
            if target_val_part <= 0: raise ValueError("Target value must be positive.")
            if range_min > range_max: raise ValueError("Range Min cannot be greater than Range Max.")
            if not (series_allowed or parallel_allowed or mixed_allowed):
                 raise ValueError("At least one config type must be allowed.")

            self.last_used_deviation_limit = deviation

            if target_unit == f"m{OHM_SYMBOL}": target_value_ohms = target_val_part / 1000
            elif target_unit == f"k{OHM_SYMBOL}": target_value_ohms = target_val_part * 1000
            elif target_unit == f"M{OHM_SYMBOL}": target_value_ohms = target_val_part * 1000000
            elif target_unit == f"G{OHM_SYMBOL}": target_value_ohms = target_val_part * 1000000000
            else: target_value_ohms = target_val_part

            self._update_button_states(is_running=True)
            self.calculation_qthread = QThread()
            worker_args = (
                target_value_ohms, deviation, max_comp, e_series, range_min,
                range_max, series_allowed, parallel_allowed, mixed_allowed
            )
            self.worker = CalculationWorker(*worker_args)
            self.worker.moveToThread(self.calculation_qthread)
            self.worker.text_output_signal.connect(self.append_text_to_output)
            self.worker.progress_updated.connect(self.update_progress_display)
            self.worker.calculation_finished_signal.connect(self._calculation_finished_slot)
            self.calculation_qthread.started.connect(self.worker.run_calculation)
            self.calculation_qthread.finished.connect(self.worker.deleteLater)
            self.calculation_qthread.finished.connect(self.calculation_qthread.deleteLater)
            self.calculation_qthread.finished.connect(self._on_thread_actually_finished)
            self.calculation_qthread.start()

        except ValueError as ve:
            self._log_gui_event(f"INPUT ERROR: {ve}")
            self.progress_label.setText("Input Error")
            self._update_button_states(is_running=False)
        except Exception as e:
            self._log_gui_event(f"GUI ERROR: {e}")
            self._log_gui_event(traceback.format_exc())
            self.progress_label.setText("GUI Error")
            self._update_button_states(is_running=False)

    def _on_thread_actually_finished(self):
        self.calculation_qthread = None
        self.worker = None
        self._update_button_states(is_running=False)

    def _calculation_finished_slot(self, results, total_checks_from_worker):
        self.estimated_total_checks = total_checks_from_worker
        if results is not None:
            self.current_results = results
            self.sort_by_config(display_message=False) # Default sort
            self.append_text_to_output("__DISPLAY_RESULTS__")
            self._log_gui_event(f"Calculation finished. {len(self.current_results)} total combinations found.")
        else:
            self.current_results = []
        if self.calculation_qthread: self.calculation_qthread.quit()
        else: self._update_button_states(is_running=False)

    def stop_calculation(self):
        if self.calculation_qthread and self.calculation_qthread.isRunning():
            self._log_gui_event("Stop request sent to calculation thread.")
            self.calculation_qthread.requestInterruption()
            self.stop_button.setEnabled(False)
        else:
            self._log_gui_event("No calculation running to stop.")

    def _display_results(self, results_to_display):
        self.output_text.clear()
        col_widths = {
            "config": 13, "topology": 12, "r1": 12, "r2": 12, "r3": 12,
            "combined_r": 17, "abs_dev": 17, "perc_dev": 9
        }
        separator_char = "|"; padding = " "
        html_lines = []
        header_parts_text = [
            'Configuration'.ljust(col_widths['config']), 'Topology'.ljust(col_widths['topology']),
            'R1'.ljust(col_widths['r1']), 'R2'.ljust(col_widths['r2']), 'R3'.ljust(col_widths['r3']),
            'Result (R)'.ljust(col_widths['combined_r']), 'Abs Dev'.ljust(col_widths['abs_dev']),
            '% Dev'.ljust(col_widths['perc_dev'])
        ]
        header_str = f"{padding}{separator_char}{padding}".join(header_parts_text)
        separator_line_str = "-" * (len(header_str) - header_str.count(padding) * (len(padding)-1) - header_str.count(separator_char)*(len(separator_char)-1))
        html_lines.append(html.escape(header_str))
        html_lines.append(html.escape(separator_line_str))
        if not results_to_display:
            html_lines.append("No matching combinations found within the specified parameters.")
        else:
            max_dev_for_color = self.last_used_deviation_limit
            for res_item in results_to_display:
                config_str_padded = res_item['config'].ljust(col_widths['config'])
                topology_str_padded = res_item['topology'].ljust(col_widths['topology'])
                r1_str_padded = format_resistor_value(res_item['r1']).ljust(col_widths['r1'])
                r2_str_padded = format_resistor_value(res_item['r2']).ljust(col_widths['r2'])
                r3_str_padded = format_resistor_value(res_item['r3']).ljust(col_widths['r3'])
                combined_r_str_padded = format_resistor_value(res_item['combined_r']).ljust(col_widths['combined_r'])
                abs_dev_str_padded = format_resistor_value(res_item['abs_dev']).ljust(col_widths['abs_dev'])
                perc_dev_val = res_item['perc_dev']
                perc_dev_str_padded = f"{perc_dev_val:.3f}%".ljust(col_widths['perc_dev'])
                config_color_hex = CONFIG_COLORS.get(res_item['config'], CONFIG_COLORS["default"])
                dev_color_hex = _get_deviation_color(perc_dev_val, max_dev_for_color)
                line_parts_html = [
                    f"<font color='{config_color_hex}'>{html.escape(config_str_padded)}</font>",
                    html.escape(topology_str_padded), html.escape(r1_str_padded), html.escape(r2_str_padded),
                    html.escape(r3_str_padded), html.escape(combined_r_str_padded), html.escape(abs_dev_str_padded),
                    f"<font color='{dev_color_hex}'>{html.escape(perc_dev_str_padded)}</font>"
                ]
                html_lines.append(f"{html.escape(padding)}{html.escape(separator_char)}{html.escape(padding)}".join(line_parts_html))
            html_lines.append(html.escape(separator_line_str))
        full_html = "<pre>" + "<br>".join(html_lines) + "</pre>"
        self.output_text.setHtml(full_html)
        self.output_text.moveCursor(QTextCursor.MoveOperation.Start)

    def sort_by_deviation(self, display_message=True):
        if not self.current_results:
            if display_message: self._log_gui_event("No results to sort.")
            return
        if display_message: self._log_gui_event("Sorting results by Deviation (% Ascending)...")
        self.current_results.sort(key=lambda x: x['perc_dev'])
        if display_message:
            self.progress_label.setText("Re-displaying sorted results...")
            self.append_text_to_output("__DISPLAY_RESULTS__")

    def sort_by_config(self, display_message=True):
        if not self.current_results:
            if display_message: self._log_gui_event("No results to sort.")
            return
        if display_message: self._log_gui_event("Sorting results by Configuration Type (then Deviation)...")
        config_priority_map = {
            'Single': 0, 'Series (2)': 1, 'Parallel (2)': 2,
            'Series (3)': 3, 'Parallel (3)': 4, 'Mixed S-P': 5, 'Mixed P-S': 6
        }
        self.current_results.sort(key=lambda x: (config_priority_map.get(x['config'], 99), x['perc_dev']))
        if display_message:
            self.progress_label.setText("Re-displaying sorted results...")
            self.append_text_to_output("__DISPLAY_RESULTS__")

    def show_help_window(self):
        if self.help_dialog and self.help_dialog.isVisible():
            self.help_dialog.activateWindow(); self.help_dialog.raise_()
            return
        self.help_dialog = QDialog(self)
        self.help_dialog.setWindowTitle("Help - Resistor Combination Finder")
        self.help_dialog.setGeometry(150, 150, 700, 550)
        self.help_dialog.setModal(False)
        layout = QVBoxLayout(self.help_dialog)
        help_text_edit = QTextEdit()
        help_text_edit.setReadOnly(True)
        help_text_edit.setFont(QApplication.font())
        help_content = f"""{self._get_help_text_content()}"""
        help_text_edit.setHtml(help_content)
        layout.addWidget(help_text_edit)
        close_button = QPushButton("Close")
        close_button.clicked.connect(self.help_dialog.accept)
        layout.addWidget(close_button, 0, Qt.AlignmentFlag.AlignCenter)
        self.help_dialog.finished.connect(self._on_help_dialog_closed)
        self.help_dialog.show()

    def _get_help_text_content(self):
        return f"""to be filled in"""

    def _on_help_dialog_closed(self):
        self.help_dialog = None

    def closeEvent(self, event):
        print("Closing application...")
        if self.help_dialog and self.help_dialog.isVisible():
            print("Closing help window..."); self.help_dialog.close()
        if self.calculation_qthread and self.calculation_qthread.isRunning():
            print("Stopping calculation thread...")
            self.calculation_qthread.requestInterruption()
            if not self.calculation_qthread.wait(1000):
                print("Warning: Calculation thread did not exit cleanly after 1s.")
            else:
                print("Calculation thread stopped.")
        print("Exiting.")
        event.accept()

if __name__ == "__main__":
    app = QApplication(sys.argv)
    main_window = ResistorCalculatorApp()
    main_window.show()
    sys.exit(app.exec())