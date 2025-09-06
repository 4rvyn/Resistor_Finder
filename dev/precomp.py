# precomp.py
# Generates memory-mappable precompute files for Path A (Meet-in-the-Middle)
# One file per E-series: rcf_e{N}.bin for N in {3,6,12,24,48,96,192}
#
# Binary format (little-endian), designed for Python/Rust:
# Header (written at file start; we reserve 512 bytes for it, padded with zeros):
#   magic[4]          = b"RCF\0"
#   version           = u32 (1)
#   endian_flag       = u8  (0 = little-endian)
#   e_series_id       = u8  (3, 6, 12, 24, 48, 96, 192)
#   decade_min        = i8  (-3)
#   decade_max        = i8  (+9)
#   _pad0             = u16 (padding)
#   n_singles         = u32
#   n_pairs_series    = u64
#   n_pairs_parallel  = u64
#   R_scale_num       = u64 (1e8)  -- int64 units per ohm (avoids int64 overflow up to 9.76 GΩ)
#   R_scale_den       = u64 (1)
#   G_scale_num       = u64 (1e12) -- picosiemens per siemens (pS units)
#   G_scale_den       = u64 (1)
#   For each array below: [offset: u64][length_elems: u64]
#     R[int64]           -- singles, scaled ohms (R_scale = 1e8 per ohm)
#     G[int64]           -- singles, scaled pS (G_scale = 1e12 per S)
#     mantissa_idx[u16]  -- index into base mantissa list
#     decade[i8]         -- decade k in base*10^k
#     S_sum[int64]       -- series pair sums (i<=j), sorted asc
#     S_i[u32], S_j[u32] -- indices of the singles that formed S_sum
#     G_sum[int64]       -- parallel pair conductance sums (i<=j), sorted asc
#     G_i[u32], G_j[u32] -- indices of the singles that formed G_sum
#   checksum_payload   = u64  -- blake2b-64 of concatenated array bytes (no header, no padding)
#
# Arrays are 8-byte aligned in the file. All arrays are stored as raw columns (SoA).
#
# Notes:
# - R_scale = 1e8 (not 1e9) to keep max(9.76 GΩ) within int64 when summed (pair sums < 2e18).
# - Parallel queries are performed in conductance (pS) using G_sum.
# - This script builds both pair tables in one pass, then sorts each by its sum.
# - No external deps; uses only Python stdlib. Designed for Windows (little-endian).

import sys
import os
import math
import struct
import hashlib
from array import array
from typing import List, Tuple

HEADER_RESERVED_SIZE = 512  # bytes to reserve at start; actual header is smaller

# Fixed-point scales
R_SCALE_NUM = 10**8   # int64 units per ohm (prevents int64 overflow at 9.76 GΩ)
R_SCALE_DEN = 1
G_SCALE_NUM = 10**12  # pS per S
G_SCALE_DEN = 1

DECADE_MIN = -3
DECADE_MAX = 9

# --- IEC 60063 official base-value tables (hard-coded, normative) ---

E3_BASE_VALUES  = [1.0, 2.2, 4.7]

E6_BASE_VALUES  = [1.0, 1.5, 2.2, 3.3, 4.7, 6.8]

E12_BASE_VALUES = [1.0, 1.2, 1.5, 1.8, 2.2, 2.7, 3.3, 3.9, 4.7, 5.6, 6.8, 8.2]

E24_BASE_VALUES = [
    1.0, 1.1, 1.2, 1.3, 1.5, 1.6, 1.8, 2.0, 2.2, 2.4, 2.7, 3.0,
    3.3, 3.6, 3.9, 4.3, 4.7, 5.1, 5.6, 6.2, 6.8, 7.5, 8.2, 9.1
]

E48_BASE_VALUES = [
    1.00, 1.05, 1.10, 1.15, 1.21, 1.27, 1.33, 1.40, 1.47, 1.54, 1.62, 1.69,
    1.78, 1.87, 1.96, 2.05, 2.15, 2.26, 2.37, 2.49, 2.61, 2.74, 2.87, 3.01,
    3.16, 3.32, 3.48, 3.65, 3.83, 4.02, 4.22, 4.42, 4.64, 4.87, 5.11, 5.36,
    5.62, 5.90, 6.19, 6.49, 6.81, 7.15, 7.50, 7.87, 8.25, 8.66, 9.09, 9.53
]

E96_BASE_VALUES = [
    1.00, 1.02, 1.05, 1.07, 1.10, 1.13, 1.15, 1.18, 1.21, 1.24, 1.27, 1.30,
    1.33, 1.37, 1.40, 1.43, 1.47, 1.50, 1.54, 1.58, 1.62, 1.65, 1.69, 1.74,
    1.78, 1.82, 1.87, 1.91, 1.96, 2.00, 2.05, 2.10, 2.15, 2.21, 2.26, 2.32,
    2.37, 2.43, 2.49, 2.55, 2.61, 2.67, 2.74, 2.80, 2.87, 2.94, 3.01, 3.09,
    3.16, 3.24, 3.32, 3.40, 3.48, 3.57, 3.65, 3.74, 3.83, 3.92, 4.02, 4.12,
    4.22, 4.32, 4.42, 4.53, 4.64, 4.75, 4.87, 4.99, 5.11, 5.23, 5.36, 5.49,
    5.62, 5.76, 5.90, 6.04, 6.19, 6.34, 6.49, 6.65, 6.81, 6.98, 7.15, 7.32,
    7.50, 7.68, 7.87, 8.06, 8.25, 8.45, 8.66, 8.87, 9.09, 9.31, 9.53, 9.76
]

E192_BASE_VALUES = [
    1.00, 1.01, 1.02, 1.04, 1.05, 1.06, 1.07, 1.09, 1.10, 1.11, 1.13, 1.14,
    1.15, 1.17, 1.18, 1.20, 1.21, 1.23, 1.24, 1.26, 1.27, 1.29, 1.30, 1.32,
    1.33, 1.35, 1.37, 1.38, 1.40, 1.42, 1.43, 1.45, 1.47, 1.49, 1.50, 1.52,
    1.54, 1.56, 1.58, 1.60, 1.62, 1.64, 1.65, 1.67, 1.69, 1.72, 1.74, 1.76,
    1.78, 1.80, 1.82, 1.84, 1.87, 1.89, 1.91, 1.93, 1.96, 1.98, 2.00, 2.03,
    2.05, 2.08, 2.10, 2.13, 2.15, 2.18, 2.21, 2.23, 2.26, 2.29, 2.32, 2.34,
    2.37, 2.40, 2.43, 2.46, 2.49, 2.52, 2.55, 2.58, 2.61, 2.64, 2.67, 2.71,
    2.74, 2.77, 2.80, 2.84, 2.87, 2.91, 2.94, 2.98, 3.01, 3.05, 3.09, 3.12,
    3.16, 3.20, 3.24, 3.28, 3.32, 3.36, 3.40, 3.44, 3.48, 3.52, 3.57, 3.61,
    3.65, 3.70, 3.74, 3.79, 3.83, 3.88, 3.92, 3.97, 4.02, 4.07, 4.12, 4.17,
    4.22, 4.27, 4.32, 4.37, 4.42, 4.48, 4.53, 4.59, 4.64, 4.70, 4.75, 4.81,
    4.87, 4.93, 4.99, 5.05, 5.11, 5.17, 5.23, 5.30, 5.36, 5.42, 5.49, 5.56,
    5.62, 5.69, 5.76, 5.83, 5.90, 5.97, 6.04, 6.12, 6.19, 6.26, 6.34, 6.42,
    6.49, 6.57, 6.65, 6.73, 6.81, 6.90, 6.98, 7.06, 7.15, 7.23, 7.32, 7.41,
    7.50, 7.59, 7.68, 7.77, 7.87, 7.96, 8.06, 8.16, 8.25, 8.35, 8.45, 8.56,
    8.66, 8.76, 8.87, 8.98, 9.09, 9.20, 9.31, 9.42, 9.53, 9.65, 9.76, 9.88
]

E_SERIES_BASE = {
    3:   E3_BASE_VALUES,
    6:   E6_BASE_VALUES,
    12:  E12_BASE_VALUES,
    24:  E24_BASE_VALUES,
    48:  E48_BASE_VALUES,
    96:  E96_BASE_VALUES,
    192: E192_BASE_VALUES,
}

SUPPORTED_SERIES = set(E_SERIES_BASE.keys())


def info(msg: str):
    print(msg, flush=True)

def align8(pos: int) -> int:
    rem = pos & 7
    return pos if rem == 0 else pos + (8 - rem)

def build_singles(base_values: List[float], dec_min: int, dec_max: int):
    """
    Build singles:
      R: int64 (R_SCALE_NUM per ohm)
      G: int64 (pS)
      mantissa_idx: u16
      decade: i8
    Sorted by R ascending.
    """
    R = array('q')
    G = array('q')
    mant_idx = array('H')
    decade = array('b')

    # We use exact integer arithmetic for R via mantissa * 100 and decade.
    # R_scaled = (mantissa*100) * 10^(k+6)  (because R_scale=1e8 => 1e8/100 = 1e6)
    # For G (pS), we compute: G_pS = round(1e12 / (mantissa * 10^k))
    # Using integers: with m = round(mantissa*100), G = round(10^(14 - k) / m)
    for mi, m in enumerate(base_values):
        m100 = int(round(m * 100.0))  # integer mantissa * 100
        if m100 <= 0:
            raise ValueError("Mantissa rounding produced non-positive value")
        for k in range(dec_min, dec_max + 1):
            # R in fixed-point (int64)
            pow10 = 10 ** (k + 6)  # note: Python int is unbounded
            R_scaled = m100 * pow10  # will fit in int64 given our k-range and R_SCALE
            # G in pS, integer rounding: 10^(14 - k) / m100
            num = 10 ** (14 - k)
            G_pS = (num + m100 // 2) // m100  # nearest integer

            # Bounds check for int64
            if not (-2**63 <= R_scaled < 2**63):
                raise OverflowError(f"R_scaled out of int64 range for mantissa {m}, decade {k}")
            if not (-2**63 <= G_pS < 2**63):
                raise OverflowError(f"G_pS out of int64 range for mantissa {m}, decade {k}")

            R.append(int(R_scaled))
            G.append(int(G_pS))
            mant_idx.append(mi)
            decade.append(k)

    # Sort by R ascending and reorder other arrays to match
    idx_sorted = sorted(range(len(R)), key=R.__getitem__)
    R_sorted = array('q', (R[i] for i in idx_sorted))
    G_sorted = array('q', (G[i] for i in idx_sorted))
    mant_sorted = array('H', (mant_idx[i] for i in idx_sorted))
    dec_sorted = array('b', (decade[i] for i in idx_sorted))

    return R_sorted, G_sorted, mant_sorted, dec_sorted

def build_pair_tables(R: array, G: array):
    """
    Build BOTH pair tables in one pass (i <= j):
      Series:  S_sum = R[i] + R[j], arrays: S_sum[q], S_i[I], S_j[I]
      Parallel conductance: G_sum = G[i] + G[j], arrays: G_sum[q], G_i[I], G_j[I]
    Then sort each table by its sum (ascending).
    """
    n = len(R)
    m_pairs = n * (n + 1) // 2

    info(f"Singles: n={n} ; Pair entries per table: m={m_pairs:,}")

    S_sum = array('q'); S_i = array('I'); S_j = array('I')
    G_sum = array('q'); G_i = array('I'); G_j = array('I')

    # Generate pair sums
    # In Python this is fine (O(7.8e5) appends for E96 over -3..9)
    for i in range(n):
        Ri = R[i]
        Gi = G[i]
        for j in range(i, n):
            S_sum.append(Ri + R[j])
            S_i.append(i); S_j.append(j)

            G_sum.append(Gi + G[j])
            G_i.append(i); G_j.append(j)

    # Sort series pairs by S_sum
    info("Sorting series pair table ...")
    order_S = sorted(range(m_pairs), key=S_sum.__getitem__)
    S_sum_sorted = array('q', (S_sum[k] for k in order_S))
    S_i_sorted   = array('I', (S_i[k]   for k in order_S))
    S_j_sorted   = array('I', (S_j[k]   for k in order_S))

    # Sort parallel pairs by G_sum
    info("Sorting parallel (conductance) pair table ...")
    order_G = sorted(range(m_pairs), key=G_sum.__getitem__)
    G_sum_sorted = array('q', (G_sum[k] for k in order_G))
    G_i_sorted   = array('I', (G_i[k]   for k in order_G))
    G_j_sorted   = array('I', (G_j[k]   for k in order_G))

    # free intermediates (let GC reclaim)
    return (S_sum_sorted, S_i_sorted, S_j_sorted,
            G_sum_sorted, G_i_sorted, G_j_sorted)

def write_arrays_with_offsets(f, hasher, arrays: List[Tuple[str, array]], start_pos: int):
    """
    Writes arrays in order, 8-byte aligned.
    Returns dict: name -> (offset, length_elements), and the final file position.
    Updates hasher (blake2b) with the raw array bytes (no padding).
    """
    offsets = {}
    pos = start_pos
    for name, arr in arrays:
        # align
        aligned = align8(pos)
        if aligned != pos:
            f.seek(aligned)
            pos = aligned
        # remember offset
        offset = pos

        # obtain bytes once; update hash and write
        data = arr.tobytes()  # local copy; manageable (<= ~12MB per large column)
        hasher.update(data)
        f.write(data)
        pos += len(data)

        # record offset & length (in elements)
        offsets[name] = (offset, len(arr))

    return offsets, pos

def pack_header(e_series_id: int,
                n_singles: int,
                n_pairs_series: int,
                n_pairs_parallel: int,
                offsets: dict,
                checksum_u64: int) -> bytes:
    """
    Build the binary header.
    """
    magic = b"RCF\x00"
    version = 1
    endian_flag = 0  # little-endian
    decade_min = DECADE_MIN
    decade_max = DECADE_MAX
    _pad0 = 0

    # Helper to extract (offset,len) or (0,0) if absent
    def off_len(name):
        return offsets.get(name, (0, 0))

    # Header fixed part
    hdr_fixed_fmt = (
        "<4s I B B b b H I Q Q Q Q Q Q"
    )
    hdr_fixed = struct.pack(
        hdr_fixed_fmt,
        magic,                # 4s
        version,              # I
        endian_flag,          # B
        e_series_id,          # B
        decade_min,           # b
        decade_max,           # b
        _pad0,                # H
        n_singles,            # I
        n_pairs_series,       # Q
        n_pairs_parallel,     # Q
        R_SCALE_NUM,          # Q
        R_SCALE_DEN,          # Q
        G_SCALE_NUM,          # Q
        G_SCALE_DEN           # Q
    )

    # Arrays metadata (offset,len) pairs in the agreed order
    names = [
        "R", "G", "mantissa_idx", "decade",
        "S_sum", "S_i", "S_j",
        "G_sum", "G_i", "G_j",
    ]
    pairs_fmt = "<" + "QQ" * len(names)
    pairs_vals = []
    for nm in names:
        off, length = off_len(nm)
        pairs_vals.extend([off, length])
    hdr_pairs = struct.pack(pairs_fmt, *pairs_vals)

    # Checksum (u64)
    hdr_checksum = struct.pack("<Q", checksum_u64)

    header = hdr_fixed + hdr_pairs + hdr_checksum
    if len(header) > HEADER_RESERVED_SIZE:
        raise RuntimeError(f"Header ({len(header)} bytes) exceeds reserved size {HEADER_RESERVED_SIZE} bytes")
    # pad to reserved size
    header += b"\x00" * (HEADER_RESERVED_SIZE - len(header))
    return header

def write_container(path: str,
                    e_series_id: int,
                    R: array, G: array, mant: array, dec: array,
                    S_sum: array, S_i: array, S_j: array,
                    G_sum: array, G_i: array, G_j: array):
    """
    Write the full binary container with header + arrays.
    """
    info(f"Writing {path} ...")
    # Prepare hasher for payload arrays (no header, no padding)
    h = hashlib.blake2b(digest_size=8)

    # Arrays to write, in order
    arrays = [
        ("R", R),
        ("G", G),
        ("mantissa_idx", mant),
        ("decade", dec),
        ("S_sum", S_sum),
        ("S_i", S_i),
        ("S_j", S_j),
        ("G_sum", G_sum),
        ("G_i", G_i),
        ("G_j", G_j),
    ]

    # Open file and reserve header space
    with open(path, "wb") as f:
        f.write(b"\x00" * HEADER_RESERVED_SIZE)  # placeholder
        start_pos = f.tell()
        # Write arrays
        offsets, final_pos = write_arrays_with_offsets(f, h, arrays, start_pos)
        checksum_u64 = int.from_bytes(h.digest(), byteorder="little", signed=False)

        # Build and write header at the front
        header = pack_header(
            e_series_id=e_series_id,
            n_singles=len(R),
            n_pairs_series=len(S_sum),
            n_pairs_parallel=len(G_sum),
            offsets=offsets,
            checksum_u64=checksum_u64
        )
        f.seek(0)
        f.write(header)

    size_mb = os.path.getsize(path) / (1024 * 1024)
    info(f"Wrote {path} ({size_mb:.2f} MB)")

def generate_series_file(e_series_id: int, base_values: List[float], out_path: str):
    info("=" * 72)
    info(f"Generating E{e_series_id} precompute → {out_path}")
    info(f"Decades: {DECADE_MIN} .. {DECADE_MAX}")
    # 1) Singles
    R, G, mant, dec = build_singles(base_values, DECADE_MIN, DECADE_MAX)
    info(f"Singles built: n={len(R)}")
    # 2) Pair tables
    (S_sum, S_i, S_j,
     G_sum, G_i, G_j) = build_pair_tables(R, G)
    # 3) Write container
    write_container(out_path, e_series_id, R, G, mant, dec, S_sum, S_i, S_j, G_sum, G_i, G_j)

def _parse_series_args(argv: list[str]) -> set[int]:
    if not argv:
        return set(SUPPORTED_SERIES)   # default = ALL
    wanted: set[int] = set()
    for tok in argv:
        t = tok.strip().lower().lstrip('e')
        if t == "all":
            return set(SUPPORTED_SERIES)
        if t.isdigit():
            n = int(t)
            if n in SUPPORTED_SERIES:
                wanted.add(n)
    return wanted or set(SUPPORTED_SERIES)


def main():
    if sys.byteorder != "little":
        print("WARNING: Host is not little-endian. This script assumes Windows little-endian for array.tofile().", file=sys.stderr)

    series_to_build = sorted(_parse_series_args(sys.argv[1:]))

    for n in series_to_build:
        base = E_SERIES_BASE[n]
        out_path = f"rcf_e{n}.bin"
        generate_series_file(n, base, out_path)
    info("=" * 72)
    info("Done.")


if __name__ == "__main__":
    main()
