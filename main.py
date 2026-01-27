##################################################################################
# Author:    Arvin Parvizinia
# Date:      01.09.2025
# Version:   2.0
##################################################################################

import sys
import time
import html
import datetime
import heapq
import bisect
import traceback
import mmap
import os
import struct
from decimal import Decimal, ROUND_HALF_UP, InvalidOperation

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
    "default": "#000000"
}

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
ASSET_FILES = {f'E{n}': os.path.join(ROOT_DIR, 'assets', f'rcf_e{n}.bin')
               for n in (3, 6, 12, 24, 48, 96, 192)}

# Fixed-point scales used when generating the binaries
R_SCALE = 10**8    # integer units per ohm for R-arrays
G_SCALE = 10**12   # integer units per siemens for G-arrays

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
    if not os.path.isfile(path):
        raise FileNotFoundError(
            f"Precompute file not found: {path}\n"
            f"Generate it with precomp.py and place it under the 'assets' folder."
        )

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
    expected_id = {'E3':3, 'E6':6, 'E12':12, 'E24':24, 'E48':48, 'E96':96, 'E192':192}[series]
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

    # Helper to create typed memoryviews (no copies)
    mv = memoryview(mm)

    def view_q(off, count):  # int64
        if off == 0 or count == 0: return None
        b = mv[off: off + count*8]
        return b.cast('q')

    def view_Q(off, count):  # uint64 (not used, but for symmetry)
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
    H.f = f  # file handle; mm keeps mapping alive regardless
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

    # Back-compat aliases so the search code can use P_* for parallel (conductance)
    H.P_sum = H.G_sum
    H.P_i   = H.G_i
    H.P_j   = H.G_j

    # Quick sanity bianry checks
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

def build_allowed(dec_arr, dec_lo, dec_hi):
    """Boolean mask of singles allowed by decade range inclusive."""
    return [ (dec_lo <= d <= dec_hi) for d in dec_arr ]


# --- Calculation Logic: Best-first search ---
def find_resistor_combinations_bestfirst(
    target_value,
    max_components,
    selected_e_series,
    range_min_factor,
    range_max_factor,
    series_allowed,
    parallel_allowed,
    mixed_allowed,
    search_mode,     # "topk" or "tolerance"
    mode_value,      # int for topk, Decimal for tolerance (%)
    stop_event,
    queue_func
):
    """
    Unified best-first search.

    Modes:
      - "topk": emit the best K unique results (by absolute error in scaled-ohms)
      - "tolerance": emit ALL unique results with percent deviation <= mode_value

    Completeness for tolerance mode relies on the stream invariant:
      - Each stream is enumerated in nondecreasing absolute error (scaled-ohms),
        seeded at an exact pivot and advanced outward
      - stop only when the minimum frontier error exceeds the tolerance threshold
    """
    start_time = time.time()
    results = []
    accepted = 0
    uid = 0  # tie-breaker for heap stability

    def log(message, level=0):
        ts = datetime.datetime.now().strftime('%H:%M:%S.%f')[:-3]
        queue_func(f"[{ts}] {'  '*level}{message}")

    try:
        log("[SETUP]")
        log(f"E-Series: {selected_e_series}", 1)
        H = load_precomp(selected_e_series, log)

        dec_lo = int(range_min_factor)
        dec_hi = int(range_max_factor)
        allowed = build_allowed(H.dec, dec_lo, dec_hi)

        # Normalize target input: exact integer target for ranking + float only for display fields
        if isinstance(target_value, Decimal):
            if target_value <= 0:
                return [], 0
            target_float = float(target_value)
            R_t = int((target_value * Decimal(R_SCALE)).to_integral_value(rounding=ROUND_HALF_UP))
        else:
            target_float = float(target_value)
            if target_float <= 0:
                return [], 0
            R_t = int(round(target_float * R_SCALE))

        G_R = G_SCALE * R_SCALE  # constant used for exact rational comparisons

        # Mode config
        mode = str(search_mode).strip().lower()
        if mode not in ("topk", "tolerance"):
            raise ValueError(f"Unknown search_mode '{search_mode}' (expected 'topk' or 'tolerance').")

        total_goal = None
        tol_percent_dec = None

        # For integer-only tolerance comparisons:
        # abs_diff_scaled <= (tol_percent/100) * R_t
        # abs_diff_scaled = dev.num / dev.den
        # dev.num * 100 <= tol_percent * R_t * dev.den
        # represent tol_percent as tol_int / P_SCALE
        P_SCALE = 10**6
        tol_int = None

        if mode == "topk":
            total_goal = max(1, int(mode_value))
            log(f"Mode: Top-K, K={total_goal}", 1)

        else:
            if isinstance(mode_value, Decimal):
                tol_percent_dec = mode_value
            else:
                try:
                    tol_percent_dec = Decimal(str(mode_value))
                except InvalidOperation:
                    raise ValueError("Tolerance mode requires a numeric percent value.")
            if tol_percent_dec < 0:
                raise ValueError("Tolerance (%) cannot be negative.")
            tol_int = int((tol_percent_dec * Decimal(P_SCALE)).to_integral_value(rounding=ROUND_HALF_UP))
            log(f"Mode: Tolerance, band=±{tol_percent_dec}%", 1)

        log(f"Target: {format_resistor_value(target_float)}", 1)
        log(f"Decades allowed: 10^{dec_lo} .. 10^{dec_hi}", 1)

        Q = []
        seen = set()

        class DevFrac:
            __slots__ = ("num", "den")
            def __init__(self, num: int, den: int):
                self.num = int(num) if num >= 0 else int(-num)
                self.den = int(den)
            def __lt__(self, other):
                return self.num * other.den < other.num * self.den
            def __eq__(self, other):
                return self.num * other.den == other.num * self.den

        def push(dev_frac, tag, st):
            nonlocal uid
            heapq.heappush(Q, (dev_frac, uid, tag, st))
            uid += 1

        def dev_exceeds_tolerance(dev: DevFrac) -> bool:
            # dev.num/dev.den > (tol_percent/100)*R_t
            # dev.num * 100 * P_SCALE > tol_int * R_t * dev.den
            lhs = dev.num * 100 * P_SCALE
            rhs = tol_int * R_t * dev.den
            return lhs > rhs

        def dev_within_tolerance(dev: DevFrac) -> bool:
            lhs = dev.num * 100 * P_SCALE
            rhs = tol_int * R_t * dev.den
            return lhs <= rhs

        def emit_result(config, topology, i=None, j=None, k=None):
            nonlocal accepted

            # Canonical keys for dedup
            if config == "Single":
                key = ("Single", i)

            elif config in ("Series (2)", "Parallel (2)"):
                a = i if i <= j else j
                b = j if i <= j else i
                key = (config, a, b)

            elif config in ("Series (3)", "Parallel (3)"):
                t0, t1, t2 = i, j, k
                if t0 > t1:
                    t0, t1 = t1, t0
                if t1 > t2:
                    t1, t2 = t2, t1
                if t0 > t1:
                    t0, t1 = t1, t0
                key = (config, t0, t1, t2)

            elif config in ("Mixed S-P", "Mixed P-S"):
                a = i if i <= j else j
                b = j if i <= j else i
                key = (config, k, a, b)

            else:
                return False

            if key in seen:
                return False
            seen.add(key)

            # Compute display values in float (ranking uses DevFrac elsewhere)
            if config == "Single":
                r1 = H.R[i] / R_SCALE
                r2 = None
                r3 = None
                combined = r1

            elif config == "Series (2)":
                r1 = H.R[i] / R_SCALE
                r2 = H.R[j] / R_SCALE
                r3 = None
                combined = r1 + r2

            elif config == "Parallel (2)":
                gsum = H.G[i] + H.G[j]
                if gsum <= 0:
                    return False
                r1 = H.R[i] / R_SCALE
                r2 = H.R[j] / R_SCALE
                r3 = None
                combined = G_SCALE / gsum

            elif config == "Series (3)":
                r1 = H.R[i] / R_SCALE
                r2 = H.R[j] / R_SCALE
                r3 = H.R[k] / R_SCALE
                combined = r1 + r2 + r3

            elif config == "Parallel (3)":
                gsum = H.G[i] + H.G[j] + H.G[k]
                if gsum <= 0:
                    return False
                r1 = H.R[i] / R_SCALE
                r2 = H.R[j] / R_SCALE
                r3 = H.R[k] / R_SCALE
                combined = G_SCALE / gsum

            elif config == "Mixed S-P":
                gsum = H.G[i] + H.G[j]
                if gsum <= 0:
                    return False
                r_par = G_SCALE / gsum
                r1 = H.R[k] / R_SCALE
                r2 = H.R[i] / R_SCALE
                r3 = H.R[j] / R_SCALE
                combined = r1 + r_par

            elif config == "Mixed P-S":
                ssum = H.R[i] + H.R[j]
                denom = H.R[k] + ssum
                if denom <= 0:
                    return False
                r1 = H.R[k] / R_SCALE
                s = ssum / R_SCALE
                r2 = H.R[i] / R_SCALE
                r3 = H.R[j] / R_SCALE
                combined = (r1 * s) / (r1 + s)

            else:
                return False

            abs_dev = abs(combined - target_float)
            perc_dev = (abs_dev / target_float) * 100.0

            results.append({
                "config": config,
                "topology": topology,
                "r1": r1,
                "r2": r2,
                "r3": r3,
                "combined_r": combined,
                "abs_dev": abs_dev,
                "perc_dev": perc_dev
            })
            accepted += 1
            return True

        # Exact deviation keys (absolute error in scaled-ohms) using fixed-point integers
        def dev_single(idx):
            return DevFrac(abs(H.R[idx] - R_t), 1)

        def dev_s2(p):
            return DevFrac(abs(H.S_sum[p] - R_t), 1)

        def dev_p2(p):
            gsum = H.P_sum[p]
            if gsum <= 0:
                return None
            num = abs(G_R - (R_t * gsum))
            return DevFrac(num, gsum)

        def dev_s3(p, k):
            sum_scaled = H.S_sum[p] + H.R[k]
            return DevFrac(abs(sum_scaled - R_t), 1)

        def dev_p3(p, k):
            gsum = H.P_sum[p] + H.G[k]
            if gsum <= 0:
                return None
            num = abs(G_R - (R_t * gsum))
            return DevFrac(num, gsum)

        def dev_sp(p, k):
            gsum = H.P_sum[p]
            if gsum <= 0:
                return None
            # |(Rk + G_R/gsum) - R_t| = |Rk*gsum + G_R - R_t*gsum| / gsum
            num = abs((H.R[k] * gsum + G_R) - (R_t * gsum))
            return DevFrac(num, gsum)

        def dev_ps(p, k):
            ssum = H.S_sum[p]
            denom = H.R[k] + ssum
            if denom <= 0:
                return None
            # |(Rk*ssum/(Rk+ssum)) - R_t| = |Rk*ssum - R_t*(Rk+ssum)| / (Rk+ssum)
            num = abs((H.R[k] * ssum) - (R_t * denom))
            return DevFrac(num, denom)

        # Stream initializers and advancers
        def init_singles():
            if max_components < 1:
                return
            pos = bisect.bisect_left(H.R, R_t)
            left = pos - 1
            right = pos
            if 0 <= left < H.n:
                push(dev_single(left), "S1", {"idx": left, "side": "L"})
            if 0 <= right < H.n:
                push(dev_single(right), "S1", {"idx": right, "side": "R"})

        def advance_singles(st):
            idx = st["idx"]
            side = st["side"]
            nxt = idx - 1 if side == "L" else idx + 1
            if 0 <= nxt < H.n:
                push(dev_single(nxt), "S1", {"idx": nxt, "side": side})

        def init_pairs(tag, sum_arr, target_scaled):
            pos = bisect.bisect_left(sum_arr, target_scaled)
            for side, p in (("L", pos - 1), ("R", pos)):
                if 0 <= p < len(sum_arr):
                    if tag == "S2":
                        dv = dev_s2(p)
                    else:
                        dv = dev_p2(p)
                        if dv is None:
                            continue
                    push(dv, tag, {"p": p, "side": side})

        def advance_pairs(tag, st, sum_arr):
            p = st["p"]
            side = st["side"]
            nxt = p - 1 if side == "L" else p + 1
            if 0 <= nxt < len(sum_arr):
                if tag == "S2":
                    dv = dev_s2(nxt)
                else:
                    dv = dev_p2(nxt)
                    if dv is None:
                        return
                push(dv, tag, {"p": nxt, "side": side})

        def init_triples(tag, base_arr, target_scaled_fn, k_indices):
            for k in k_indices:
                t_scaled = target_scaled_fn(k)
                if t_scaled is None:
                    continue
                pos = bisect.bisect_left(base_arr, t_scaled)
                for side, p in (("L", pos - 1), ("R", pos)):
                    if 0 <= p < len(base_arr):
                        if tag == "S3":
                            dv = dev_s3(p, k)
                        elif tag == "P3":
                            dv = dev_p3(p, k)
                            if dv is None:
                                continue
                        elif tag == "SP":
                            dv = dev_sp(p, k)
                            if dv is None:
                                continue
                        elif tag == "PS":
                            dv = dev_ps(p, k)
                            if dv is None:
                                continue
                        else:
                            continue
                        push(dv, tag, {"k": k, "p": p, "side": side})

        def advance_triples(tag, st, base_arr):
            k = st["k"]
            p = st["p"]
            side = st["side"]
            nxt = p - 1 if side == "L" else p + 1
            if not (0 <= nxt < len(base_arr)):
                return

            if tag == "S3":
                dv = dev_s3(nxt, k)
            elif tag == "P3":
                dv = dev_p3(nxt, k)
                if dv is None:
                    return
            elif tag == "SP":
                dv = dev_sp(nxt, k)
                if dv is None:
                    return
            elif tag == "PS":
                dv = dev_ps(nxt, k)
                if dv is None:
                    return
            else:
                return

            push(dv, tag, {"k": k, "p": nxt, "side": side})

        # Seed streams
        init_singles()

        if max_components >= 2 and series_allowed:
            init_pairs("S2", H.S_sum, R_t)

        if max_components >= 2 and parallel_allowed:
            g_star_ceil = ceil_div_pos(G_R, R_t)
            init_pairs("P2", H.P_sum, g_star_ceil)

        allowed_k = [k for k in range(H.n) if allowed[k]] if max_components >= 3 else []

        if max_components >= 3 and series_allowed:
            def t_scaled_S3(k):
                return R_t - H.R[k]
            init_triples("S3", H.S_sum, t_scaled_S3, allowed_k)

        if max_components >= 3 and parallel_allowed:
            def t_scaled_P3(k):
                num = G_R - (R_t * H.G[k])
                if num <= 0:
                    return 0
                return ceil_div_pos(num, R_t)
            init_triples("P3", H.P_sum, t_scaled_P3, allowed_k)

        if max_components >= 3 and mixed_allowed:
            def t_scaled_SP(k):
                denom_scaled = R_t - H.R[k]
                if denom_scaled <= 0:
                    return int(H.P_sum[-1]) + 1
                return ceil_div_pos(G_R, denom_scaled)
            init_triples("SP", H.P_sum, t_scaled_SP, allowed_k)

        if max_components >= 3 and mixed_allowed:
            def t_scaled_PS(k):
                Rk = H.R[k]
                if Rk <= R_t:
                    return int(H.S_sum[-1]) + 1
                num = R_t * Rk
                den = Rk - R_t
                return ceil_div_pos(num, den)
            init_triples("PS", H.S_sum, t_scaled_PS, allowed_k)

        popped = 0
        last_progress_emit = -1

        # Run
        while Q and (mode != "topk" or accepted < total_goal):
            if stop_event.is_set():
                raise InterruptedError()

            # Tolerance mode: stop when the best frontier candidate exceeds threshold
            if mode == "tolerance":
                best_dev = Q[0][0]
                if dev_exceeds_tolerance(best_dev):
                    break

            dev, _id, tag, st = heapq.heappop(Q)
            popped += 1

            if tag == "S1":
                idx = st["idx"]
                if 0 <= idx < H.n:
                    if allowed[idx]:
                        if mode == "topk" or dev_within_tolerance(dev):
                            emit_result("Single", "R1", i=idx)
                    advance_singles(st)

            elif tag == "S2":
                p = st["p"]
                i = H.S_i[p]
                j = H.S_j[p]
                if allowed[i] and allowed[j]:
                    if mode == "topk" or dev_within_tolerance(dev):
                        emit_result("Series (2)", "R1+R2", i=i, j=j)
                advance_pairs("S2", st, H.S_sum)

            elif tag == "P2":
                p = st["p"]
                i = H.P_i[p]
                j = H.P_j[p]
                if allowed[i] and allowed[j]:
                    if mode == "topk" or dev_within_tolerance(dev):
                        emit_result("Parallel (2)", "R1||R2", i=i, j=j)
                advance_pairs("P2", st, H.P_sum)

            elif tag in ("S3", "P3", "SP", "PS"):
                p = st["p"]
                k = st["k"]

                if tag == "S3":
                    i = H.S_i[p]
                    j = H.S_j[p]
                    if allowed[i] and allowed[j] and allowed[k]:
                        if mode == "topk" or dev_within_tolerance(dev):
                            emit_result("Series (3)", "R1+R2+R3", i=i, j=j, k=k)
                    advance_triples("S3", st, H.S_sum)

                elif tag == "P3":
                    i = H.P_i[p]
                    j = H.P_j[p]
                    if allowed[i] and allowed[j] and allowed[k]:
                        if mode == "topk" or dev_within_tolerance(dev):
                            emit_result("Parallel (3)", "R1||R2||R3", i=i, j=j, k=k)
                    advance_triples("P3", st, H.P_sum)

                elif tag == "SP":
                    i = H.P_i[p]
                    j = H.P_j[p]
                    if allowed[i] and allowed[j] and allowed[k]:
                        if mode == "topk" or dev_within_tolerance(dev):
                            emit_result("Mixed S-P", "R1+(R2||R3)", i=i, j=j, k=k)
                    advance_triples("SP", st, H.P_sum)

                else:  # "PS"
                    i = H.S_i[p]
                    j = H.S_j[p]
                    if allowed[i] and allowed[j] and allowed[k]:
                        if mode == "topk" or dev_within_tolerance(dev):
                            emit_result("Mixed P-S", "R1||(R2+R3)", i=i, j=j, k=k)
                    advance_triples("PS", st, H.S_sum)

            # Progress
            if mode == "topk":
                if accepted != last_progress_emit and (accepted % max(1, total_goal // 200) == 0 or accepted == total_goal):
                    last_progress_emit = accepted
                    queue_func({"type": "progress", "current": accepted, "total": total_goal})
            else:
                if accepted != last_progress_emit and (accepted % 200 == 0 or (popped % 5000 == 0)):
                    last_progress_emit = accepted
                    queue_func({"type": "progress", "current": 0, "total": 0, "status": f"Found {accepted} (scanned {popped})"})

        # Final progress marker
        if mode == "topk":
            queue_func({"type": "progress", "current": accepted, "total": total_goal})
        else:
            queue_func({"type": "progress", "current": accepted, "total": max(accepted, 1)})

        log("[SUMMARY]")
        log(f"Emitted {accepted} best unique results.", 1)
        log(f"Popped {popped} candidates across streams.", 1)
        log(f"Total time: {time.time() - start_time:.3f} s", 1)

        total_checks = total_goal if mode == "topk" else max(accepted, 1)
        return results, total_checks

    except InterruptedError:
        queue_func({"type": "progress", "current": 1, "total": 1, "status": "Stopped"})
        return None, 0

    except Exception as e:
        queue_func({"type": "progress", "current": 1, "total": 1, "status": "Error"})
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
        """
        calc_args (GUI-side, excluding stop_event + queue_func):
          (target_value_ohms, maxN, e_series, range_min, range_max,
           allow_series, allow_parallel, allow_mixed,
           search_mode, mode_value)

        search_mode: "topk" or "tolerance"
        mode_value: int (Top-K) or Decimal (tolerance percent)
        """
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

        args = list(self.args_for_calc_func)
        args.append(StopEventChecker())
        args.append(qt_queue_func_adapter)

        results, total_checks = find_resistor_combinations_bestfirst(*args)
        self.calculation_finished_signal.emit(results, total_checks)


# --- Qt6 GUI Application ---
class ResistorCalculatorApp(QMainWindow):
    def __init__(self):
        super().__init__()
        self.setWindowTitle("Resistor Combination Finder")
        self.setGeometry(100, 100, 1300, 800)

        self.central_widget = QWidget()
        self.setCentralWidget(self.central_widget)
        self.main_layout = QVBoxLayout(self.central_widget)

        self.calculation_qthread = None
        self.worker = None

        self.current_results = []
        self.last_used_deviation_limit = 1.0
        self.estimated_total_checks = 0
        self.help_dialog = None

        # Remember last search mode for display behavior
        self._last_search_mode = "topk"
        self._last_mode_value = 50

        # --- Default control values ---
        self._default_max_components = 3
        self._default_e_series = "E12"
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

        # Target
        control_grid_layout.addWidget(QLabel("Target Value:"), row_num, 0, Qt.AlignmentFlag.AlignLeft)
        self.target_entry = QLineEdit("866")
        control_grid_layout.addWidget(self.target_entry, row_num, 1)

        self.unit_combo = QComboBox()
        self.unit_combo.addItems([f"m{OHM_SYMBOL}", f"{OHM_SYMBOL}", f"k{OHM_SYMBOL}", f"M{OHM_SYMBOL}", f"G{OHM_SYMBOL}"])
        self.unit_combo.setCurrentText(f"k{OHM_SYMBOL}")
        control_grid_layout.addWidget(self.unit_combo, row_num, 2)
        row_num += 1

        # Search mode + single shared field
        control_grid_layout.addWidget(QLabel("Search Mode:"), row_num, 0, Qt.AlignmentFlag.AlignLeft)
        self.search_mode_combo = QComboBox()
        self.search_mode_combo.addItems(["Top-K", "Tolerance (±%)"])
        self.search_mode_combo.setCurrentIndex(0)  # default: Top-K
        control_grid_layout.addWidget(self.search_mode_combo, row_num, 1, 1, 2)
        row_num += 1

        self.mode_value_label = QLabel("Top-K (N results):")
        control_grid_layout.addWidget(self.mode_value_label, row_num, 0, Qt.AlignmentFlag.AlignLeft)

        self.mode_value_entry = QLineEdit("50")  # default: Top-K N=50
        control_grid_layout.addWidget(self.mode_value_entry, row_num, 1, 1, 2)
        row_num += 1

        # Disclaimer
        self.disclaimer_label = QLabel(
            "Caution: E48/E96/E192, wide ranges, or N=3\ncan increase calculation time significantly."
        )
        self.disclaimer_label.setStyleSheet("color: #FF4500;")
        default_font = QApplication.font()
        disclaimer_font = QFont(
            default_font.family(),
            int(default_font.pointSize() * 0.9) if default_font.pointSize() > 0 else 8
        )
        self.disclaimer_label.setFont(disclaimer_font)
        control_grid_layout.addWidget(self.disclaimer_label, row_num, 0, 1, 3)
        row_num += 1

        # E-series
        control_grid_layout.addWidget(QLabel("E-Series:"), row_num, 0, Qt.AlignmentFlag.AlignLeft)
        self.eseries_combo = QComboBox()
        self.eseries_combo.addItems(["E3", "E6", "E12", "E24", "E48", "E96", "E192"])
        self.eseries_combo.setCurrentText(self._default_e_series)
        control_grid_layout.addWidget(self.eseries_combo, row_num, 1, 1, 2)
        row_num += 1

        # N, range
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

        # Allowed configurations
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
        row_num += 1

        self._update_mixed_check_state()
        self._update_search_mode_ui()

        # Buttons
        button_container = QWidget()
        button_box_layout = QHBoxLayout(button_container)
        button_box_layout.setContentsMargins(0, 0, 0, 0)

        self.run_button = QPushButton("Run")
        self.run_button.setFixedWidth(80)
        button_box_layout.addWidget(self.run_button)

        self.stop_button = QPushButton("Stop")
        self.stop_button.setFixedWidth(80)
        self.stop_button.setEnabled(False)
        button_box_layout.addWidget(self.stop_button)

        self.clear_button = QPushButton("Clear")
        self.clear_button.setFixedWidth(80)
        button_box_layout.addWidget(self.clear_button)

        button_box_layout.addStretch(1)
        control_grid_layout.addWidget(button_container, row_num, 0, 1, 3)
        row_num += 1

        # Sort group
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

        # Help
        self.help_button = QPushButton("Help?")
        self.help_button.setFixedWidth(80)
        help_button_layout = QHBoxLayout()
        help_button_layout.addWidget(self.help_button)
        help_button_layout.addStretch(1)
        control_main_v_layout.addLayout(help_button_layout)

        # Output area
        self.output_layout.addWidget(QLabel("Results:"))

        self.output_text = QTextEdit()
        self.output_text.setReadOnly(True)
        self.output_text.setFont(QFont("Courier New", 9))
        self.output_text.setMinimumWidth(700)
        self.output_layout.addWidget(self.output_text, 1)

        self.progress_label = QLabel("")
        self.progress_label.setFont(QFont("Courier New", 9))
        self.output_layout.addWidget(self.progress_label)

        # Log console
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

        self.search_mode_combo.currentIndexChanged.connect(self._on_search_mode_changed)


    def _update_mixed_check_state(self):
        is_n_less_than_3 = self.max_comp_spin.value() < 3
        self.mixed_check.setEnabled(not is_n_less_than_3)
        if is_n_less_than_3:
            self.mixed_check.setChecked(False)


    def _on_search_mode_changed(self, idx):
        self._update_search_mode_ui()

    def _update_search_mode_ui(self):
        topk_mode = (self.search_mode_combo.currentIndex() == 0)

        current_text = self.mode_value_entry.text().strip()

        if topk_mode:
            self.mode_value_label.setText("Top-K (N results):")
            # If the field is empty or looks like the tolerance default, reset to Top-K default.
            if current_text == "" or current_text == "1" or current_text == "1.0":
                self.mode_value_entry.setText("50")
        else:
            self.mode_value_label.setText("Max Deviation (%):")
            # If the field is empty or looks like the Top-K default, reset to tolerance default.
            if current_text == "" or current_text == "50":
                self.mode_value_entry.setText("1")


    def _update_button_states(self, is_running):
        widgets_to_disable_during_run = [
            self.target_entry,
            self.max_comp_spin,
            self.range_min_spin,
            self.range_max_spin,
            self.series_check,
            self.parallel_check,
            self.mixed_check,
            self.unit_combo,
            self.eseries_combo,
            self.help_button,

            self.search_mode_combo,
            self.mode_value_entry,
        ]
        self.run_button.setEnabled(not is_running)
        self.stop_button.setEnabled(is_running)
        self.clear_button.setEnabled(not is_running)
        for widget in widgets_to_disable_during_run:
            widget.setEnabled(not is_running)

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
            target_text = self.target_entry.text().strip()
            target_unit = self.unit_combo.currentText()

            max_comp = self.max_comp_spin.value()
            e_series = self.eseries_combo.currentText()
            range_min = self.range_min_spin.value()
            range_max = self.range_max_spin.value()
            series_allowed = self.series_check.isChecked()
            parallel_allowed = self.parallel_check.isChecked()
            mixed_allowed = self.mixed_check.isChecked() and (max_comp >= 3)

            if range_min > range_max:
                raise ValueError("Range Min cannot be greater than Range Max.")
            if not (series_allowed or parallel_allowed or mixed_allowed):
                raise ValueError("At least one config type must be allowed.")

            # Parse target as Decimal always (single backend now)
            try:
                target_val_dec = Decimal(target_text)
            except InvalidOperation:
                raise ValueError("Target value must be a number.")
            if target_val_dec <= 0:
                raise ValueError("Target value must be positive.")

            if target_unit == f"m{OHM_SYMBOL}":
                target_value_ohms = target_val_dec / Decimal(1000)
            elif target_unit == f"k{OHM_SYMBOL}":
                target_value_ohms = target_val_dec * Decimal(1000)
            elif target_unit == f"M{OHM_SYMBOL}":
                target_value_ohms = target_val_dec * Decimal(1000000)
            elif target_unit == f"G{OHM_SYMBOL}":
                target_value_ohms = target_val_dec * Decimal(1000000000)
            else:
                target_value_ohms = target_val_dec

            # Search mode + single entry field
            mode_text = self.mode_value_entry.text().strip()
            topk_mode = (self.search_mode_combo.currentIndex() == 0)

            if topk_mode:
                try:
                    k_best = int(mode_text)
                except Exception:
                    raise ValueError("Top-K value must be an integer.")
                if k_best < 1:
                    raise ValueError("Top-K must be at least 1.")
                if k_best > 10000:
                    raise ValueError("Top-K cannot exceed 10000.")
                search_mode = "topk"
                mode_value = k_best
                self._last_search_mode = "topk"
                self._last_mode_value = k_best

            else:
                try:
                    dev_percent = Decimal(mode_text)
                except InvalidOperation:
                    raise ValueError("Deviation (%) must be a number.")
                if dev_percent < 0:
                    raise ValueError("Deviation cannot be negative.")
                search_mode = "tolerance"
                mode_value = dev_percent
                self._last_search_mode = "tolerance"
                self._last_mode_value = dev_percent
                self.last_used_deviation_limit = float(dev_percent) if dev_percent > 0 else 1.0

            # --- start worker ---
            self._update_button_states(is_running=True)
            self.calculation_qthread = QThread()

            calc_args = (
                target_value_ohms,
                max_comp,
                e_series,
                range_min,
                range_max,
                series_allowed,
                parallel_allowed,
                mixed_allowed,
                search_mode,
                mode_value,
            )

            self.worker = CalculationWorker(*calc_args)

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

            # Always sort by deviation for both Top-K and tolerance band
            self.sort_by_deviation(display_message=False)

            # Color scaling:
            # - tolerance mode: use the user band
            # - topk mode: scale to max deviation in the emitted set (fallback 1.0)
            if getattr(self, "_last_search_mode", "topk") == "tolerance":
                try:
                    v = float(self._last_mode_value)
                    self.last_used_deviation_limit = v if v > 0 else 1.0
                except Exception:
                    self.last_used_deviation_limit = 1.0
            else:
                if self.current_results:
                    mx = max((x.get("perc_dev", 0.0) for x in self.current_results), default=0.0)
                    self.last_used_deviation_limit = mx if mx > 0 else 1.0
                else:
                    self.last_used_deviation_limit = 1.0

            self.append_text_to_output("__DISPLAY_RESULTS__")
            self._log_gui_event(f"Calculation finished. {len(self.current_results)} total combinations found.")
        else:
            self.current_results = []

        if self.calculation_qthread:
            self.calculation_qthread.quit()
        else:
            self._update_button_states(is_running=False)


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