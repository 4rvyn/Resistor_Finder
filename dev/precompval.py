# validate_precomp.py
# Verifies rcf_e{N}.bin (N in {3,6,12,24,48,96,192}) created by precomp.py
# - Parses header and section directory
# - Checks 8-byte alignment, lengths, bounds
# - Recomputes payload checksum (blake2b-64)
# - Verifies singles sort order and fixed-point relation G ~= 1e12 / R
# - Verifies pair tables:
#     * sums consistent with singles
#     * indices within range and i <= j
#     * sums are nondecreasing
#     * min/max bounds match extremes of singles
#
# Usage:
#   py validate_precomp.py                       # validates rcf_e12/e24/e96.bin if present
#   py validate_precomp.py rcf_e96.bin           # validate one file
#   py validate_precomp.py file1.bin file2.bin   # validate specific files
#
# Exit code is 0 when all checked files pass; non-zero if any fail.

import sys
import os
import struct
import hashlib
import random
from array import array
from typing import Dict, Tuple, List

HEADER_RESERVED_SIZE = 512

# Expected constants (as written by precomp.py)
EXPECTED_VERSION = 1
EXPECTED_R_SCALE_NUM = 10**8
EXPECTED_R_SCALE_DEN = 1
EXPECTED_G_SCALE_NUM = 10**12
EXPECTED_G_SCALE_DEN = 1
EXPECTED_DECADE_MIN = -3
EXPECTED_DECADE_MAX = 9

SUPPORTED_SERIES = {3, 6, 12, 24, 48, 96, 192}
DECADES = EXPECTED_DECADE_MAX - EXPECTED_DECADE_MIN + 1  # should be 13


# Section names in the exact order the payload checksum is computed
SECTION_ORDER = [
    "R", "G", "mantissa_idx", "decade",
    "S_sum", "S_i", "S_j",
    "G_sum", "G_i", "G_j",
]

def fail(msg: str) -> None:
    print(f"[FAIL] {msg}", flush=True)

def ok(msg: str) -> None:
    print(f"[ OK ] {msg}", flush=True)

def info(msg: str) -> None:
    print(f"[INFO] {msg}", flush=True)

def read_header(f) -> Tuple[Dict, Dict]:
    """
    Reads and parses the fixed header and the (offset, length) directory for all arrays.
    Returns (hdr, sections), where:
      hdr      = dict of top-level fields (magic, version, e_series_id, counts, scales, checksum, etc.)
      sections = dict name -> (offset_bytes, length_elements)
    """
    f.seek(0, os.SEEK_SET)
    raw = f.read(HEADER_RESERVED_SIZE)
    if len(raw) != HEADER_RESERVED_SIZE:
        raise RuntimeError("File shorter than reserved header size.")

    # Fixed part
    # <4s I B B b b H I Q Q Q Q Q Q
    fixed_fmt = "<4s I B B b b H I Q Q Q Q Q Q"
    fixed_sz = struct.calcsize(fixed_fmt)
    if fixed_sz >= HEADER_RESERVED_SIZE:
        raise RuntimeError("Header fixed format larger than reserved header.")
    (magic, version, endian_flag, e_series_id,
     decade_min, decade_max, _pad0,
     n_singles, n_pairs_series, n_pairs_parallel,
     R_scale_num, R_scale_den, G_scale_num, G_scale_den) = struct.unpack_from(fixed_fmt, raw, 0)

    # Pairs (offset,len) for 10 arrays (QQ * 10)
    pairs_fmt = "<" + "QQ" * len(SECTION_ORDER)
    pairs_sz = struct.calcsize(pairs_fmt)
    pairs_off = fixed_sz
    pairs_vals = struct.unpack_from(pairs_fmt, raw, pairs_off)

    # Checksum at the end
    checksum_off = pairs_off + pairs_sz
    (checksum_u64,) = struct.unpack_from("<Q", raw, checksum_off)

    hdr = {
        "magic": magic,
        "version": version,
        "endian_flag": endian_flag,
        "e_series_id": e_series_id,
        "decade_min": decade_min,
        "decade_max": decade_max,
        "n_singles": n_singles,
        "n_pairs_series": n_pairs_series,
        "n_pairs_parallel": n_pairs_parallel,
        "R_scale_num": R_scale_num,
        "R_scale_den": R_scale_den,
        "G_scale_num": G_scale_num,
        "G_scale_den": G_scale_den,
        "checksum_u64": checksum_u64,
    }

    sections: Dict[str, Tuple[int, int]] = {}
    it = iter(pairs_vals)
    for name in SECTION_ORDER:
        off = next(it)
        ln  = next(it)
        sections[name] = (off, ln)

    return hdr, sections

def check_header(hdr: Dict) -> List[str]:
    errs = []
    if hdr["magic"] != b"RCF\x00":
        errs.append("Bad magic.")
    if hdr["version"] != EXPECTED_VERSION:
        errs.append(f"Unexpected version: {hdr['version']}")
    if hdr["endian_flag"] != 0:
        errs.append("Unexpected endian_flag (expected 0 for little-endian).")
    if hdr["e_series_id"] not in SUPPORTED_SERIES:
        errs.append(f"Unexpected E-series id: {hdr['e_series_id']}")
    if hdr["decade_min"] != EXPECTED_DECADE_MIN or hdr["decade_max"] != EXPECTED_DECADE_MAX:
        errs.append(f"Unexpected decade range: {hdr['decade_min']}..{hdr['decade_max']}")
    if hdr["R_scale_num"] != EXPECTED_R_SCALE_NUM or hdr["R_scale_den"] != EXPECTED_R_SCALE_DEN:
        errs.append(f"Unexpected R scale: {hdr['R_scale_num']}/{hdr['R_scale_den']}")
    if hdr["G_scale_num"] != EXPECTED_G_SCALE_NUM or hdr["G_scale_den"] != EXPECTED_G_SCALE_DEN:
        errs.append(f"Unexpected G scale: {hdr['G_scale_num']}/{hdr['G_scale_den']}")
    if hdr["n_pairs_series"] != hdr["n_pairs_parallel"]:
        errs.append("n_pairs_series != n_pairs_parallel")
    return errs

def align8(x: int) -> bool:
    return (x & 7) == 0

def elem_size(typecode: str) -> int:
    # array('q').itemsize etc.
    return array(typecode).itemsize

def read_array(f, offset: int, length: int, typecode: str) -> array:
    """Reads a column from file into an array(typecode). Assumes little-endian host."""
    sz = elem_size(typecode)
    f.seek(offset, os.SEEK_SET)
    data = f.read(length * sz)
    if len(data) != length * sz:
        raise RuntimeError(f"Short read at offset={offset} type={typecode} length={length}")
    arr = array(typecode)
    arr.frombytes(data)  # native endianness (we wrote LE and assume Windows/LE host)
    return arr

def validate_file(path: str) -> bool:
    info(f"Validating: {path}")
    if not os.path.isfile(path):
        fail("File does not exist.")
        return False

    with open(path, "rb") as f:
        file_size = os.path.getsize(path)
        hdr, sections = read_header(f)

        # Header checks
        errs = check_header(hdr)
        if errs:
            for e in errs: fail(e)
            return False

        n = hdr["n_singles"]
        mS = hdr["n_pairs_series"]
        mG = hdr["n_pairs_parallel"]

        # Derived sanity checks consistent with how precomp.py writes:
        if n % DECADES != 0:
            fail(f"n_singles={n} not divisible by number of decades={DECADES}.")
            return False

        base_count = n // DECADES
        if base_count != hdr["e_series_id"]:
            fail(f"Base count derived from n_singles ({base_count}) != e_series_id ({hdr['e_series_id']}).")
            return False

        expected_pairs = n * (n + 1) // 2
        if mS != expected_pairs or mG != expected_pairs:
            fail(f"Pair count mismatch: expected {expected_pairs}; S={mS}, G={mG}.")
            return False


        # Section sanity checks: alignment, bounds
        for name in SECTION_ORDER:
            off, ln = sections[name]
            if off == 0 and ln == 0:
                fail(f"Section {name} has zero offset and length.")
                return False
            if not align8(off):
                fail(f"Section {name} offset not 8-byte aligned: {off}")
                return False
            # size bound
            tcode = {"R":"q","G":"q","mantissa_idx":"H","decade":"b",
                     "S_sum":"q","S_i":"I","S_j":"I",
                     "G_sum":"q","G_i":"I","G_j":"I"}[name]
            need = ln * elem_size(tcode)
            if off < HEADER_RESERVED_SIZE or off + need > file_size:
                fail(f"Section {name} out of file bounds. off={off} need={need} size={file_size}")
                return False

        # Cross-check lengths
        lens_ok = True
        if sections["R"][1] != n: lens_ok = False
        if sections["G"][1] != n: lens_ok = False
        if sections["mantissa_idx"][1] != n: lens_ok = False
        if sections["decade"][1] != n: lens_ok = False
        if sections["S_sum"][1] != mS or sections["S_i"][1] != mS or sections["S_j"][1] != mS: lens_ok = False
        if sections["G_sum"][1] != mG or sections["G_i"][1] != mG or sections["G_j"][1] != mG: lens_ok = False
        if not lens_ok:
            fail("One or more section lengths do not match header counts.")
            return False

        # Recompute checksum over payload arrays in SECTION_ORDER
        hasher = hashlib.blake2b(digest_size=8)
        for name in SECTION_ORDER:
            off, ln = sections[name]
            tcode = {"R":"q","G":"q","mantissa_idx":"H","decade":"b",
                     "S_sum":"q","S_i":"I","S_j":"I",
                     "G_sum":"q","G_i":"I","G_j":"I"}[name]
            size_bytes = ln * elem_size(tcode)
            f.seek(off, os.SEEK_SET)
            chunk = f.read(size_bytes)
            if len(chunk) != size_bytes:
                fail(f"Checksum read short for section {name}.")
                return False
            hasher.update(chunk)
        checksum_calc = int.from_bytes(hasher.digest(), "little", signed=False)
        if checksum_calc != hdr["checksum_u64"]:
            fail(f"Checksum mismatch: header={hdr['checksum_u64']:016x} calc={checksum_calc:016x}")
            return False
        else:
            ok("Payload checksum matches.")

        # Load arrays (we’ve already read bytes for checksum, but load into typed arrays for checks)
        R  = read_array(f, *sections["R"], "q")
        G  = read_array(f, *sections["G"], "q")
        mi = read_array(f, *sections["mantissa_idx"], "H")
        dk = read_array(f, *sections["decade"], "b")

        S_sum = read_array(f, *sections["S_sum"], "q")
        S_i   = read_array(f, *sections["S_i"], "I")
        S_j   = read_array(f, *sections["S_j"], "I")

        G_sum = read_array(f, *sections["G_sum"], "q")
        G_i   = read_array(f, *sections["G_i"], "I")
        G_j   = read_array(f, *sections["G_j"], "I")

    # === Mantissa/decade integrity ===
    # 1) mantissa_idx range and decade range
    for k in range(n):
        if mi[k] >= base_count:
            fail(f"mantissa_idx out of range at k={k}: mi={mi[k]} >= base_count={base_count}")
            return False
        if dk[k] < EXPECTED_DECADE_MIN or dk[k] > EXPECTED_DECADE_MAX:
            fail(f"decade out of range at k={k}: {dk[k]}")
            return False

    # 2) R encodes m100 * 10^(decade+6) exactly (no rounding error allowed)
    m100_per_mi = [None] * base_count
    for k in range(n):
        pow10 = 10 ** (dk[k] + 6)  # matches precomp.py generation
        if pow10 == 0:
            fail("Internal pow10 error.")
            return False
        if R[k] % pow10 != 0:
            fail(f"R[{k}] not divisible by 10^(decade+6). R={R[k]} decade={dk[k]}")
            return False
        m100 = R[k] // pow10
        idx = mi[k]
        if m100_per_mi[idx] is None:
            m100_per_mi[idx] = m100
        elif m100_per_mi[idx] != m100:
            fail(f"Inconsistent base mantissa*100 for mantissa_idx={idx}: "
                f"{m100_per_mi[idx]} vs {m100}")
            return False

    # 3) Even distribution: exactly base_count singles per decade
    counts_by_decade = {d: 0 for d in range(EXPECTED_DECADE_MIN, EXPECTED_DECADE_MAX + 1)}
    for d in dk:
        counts_by_decade[d] += 1
    if any(c != base_count for c in counts_by_decade.values()):
        fail(f"Singles not evenly distributed per decade: {counts_by_decade}")
        return False

    ok("Mantissa/decade integrity verified.")


    # === Singles checks ===
    # 1) R strictly increasing
    inc_ok = True
    for k in range(len(R) - 1):
        if not (R[k] < R[k+1]):
            inc_ok = False
            break
    if not inc_ok:
        fail("Singles R[] is not strictly increasing.")
        return False
    else:
        ok("Singles R[] strictly increasing.")

    # 2) G is consistent with R: G_pS == round(1e12 / (R_ohm)) where R_ohm = R/1e8
    #    Equivalent integer form: G == floor((1e20 + R/2) / R)
    CONSISTENCY_SAMPLES = min(1000, len(R))  # sample to keep runtime small; can switch to full scan if desired
    rng = random.Random(12345)
    for _ in range(CONSISTENCY_SAMPLES):
        k = rng.randrange(0, len(R))
        R_scaled = int(R[k])
        if R_scaled <= 0:
            fail(f"Non-positive R at index {k}.")
            return False
        expected_G = (10**20 + R_scaled//2) // R_scaled
        if G[k] != expected_G:
            fail(f"G/R mismatch at k={k}: G={G[k]} expected={expected_G} (R={R_scaled})")
            return False
    ok(f"Singles R/G fixed-point relation holds for {CONSISTENCY_SAMPLES} samples.")

    # === Pair tables checks ===
    # 3) Indices valid and i<=j
    def check_idx_pair(I: array, J: array, n_singles: int, label: str) -> bool:
        for k in range(len(I)):
            i = I[k]; j = J[k]
            if i > j:
                fail(f"{label}: i>j at row {k}.")
                return False
            if i >= n_singles or j >= n_singles:
                fail(f"{label}: index out of range at row {k}: i={i} j={j} n={n_singles}")
                return False
        return True

    if not check_idx_pair(S_i, S_j, len(R), "Series pairs"):
        return False
    if not check_idx_pair(G_i, G_j, len(R), "Parallel pairs"):
        return False
    ok("Pair index bounds and i<=j verified.")

    # 4) S_sum monotone nondecreasing; G_sum monotone nondecreasing
    def is_nondecreasing(arr: array) -> bool:
        return all(arr[k] <= arr[k+1] for k in range(len(arr)-1))
    if not is_nondecreasing(S_sum):
        fail("S_sum not nondecreasing.")
        return False
    if not is_nondecreasing(G_sum):
        fail("G_sum not nondecreasing.")
        return False
    ok("S_sum and G_sum are nondecreasing.")

    # 5) S_sum equals R[i]+R[j]; G_sum equals G[i]+G[j] (spot-check + boundary checks)
    # Boundary checks:
    if S_sum[0] != R[0] + R[0] or S_sum[-1] != R[-1] + R[-1]:
        fail("Series S_sum boundary values do not match 2*minR or 2*maxR.")
        return False


    # G is anti-sorted vs R: as R increases, G decreases.
    # First, confirm that monotonic relation explicitly:
    noninc_ok = all(G[k] >= G[k+1] for k in range(len(G)-1))
    if not noninc_ok:
        fail("Singles G[] is not non-increasing as R[] increases.")
        return False

    # Then the true boundaries for the sorted G_sum table are:
    #   min pair sum = 2*min(G)  → at the tail of G (G[-1])
    #   max pair sum = 2*max(G)  → at the head of G (G[0])
    g_min = G[-1]
    g_max = G[0]
    if G_sum[0] != g_min + g_min or G_sum[-1] != g_max + g_max:
        fail("Parallel G_sum boundary values do not match 2*min(G) or 2*max(G).")
        return False


    # Random spot-checks across arrays
    SPOT = min(5000, len(S_sum))  # 5k random rows is cheap but thorough
    for _ in range(SPOT):
        k = rng.randrange(0, len(S_sum))
        if S_sum[k] != R[S_i[k]] + R[S_j[k]]:
            fail(f"S_sum mismatch at row {k}: {S_sum[k]} != R[{S_i[k]}]+R[{S_j[k]}]")
            return False
    for _ in range(min(5000, len(G_sum))):
        k = rng.randrange(0, len(G_sum))
        if G_sum[k] != G[G_i[k]] + G[G_j[k]]:
            fail(f"G_sum mismatch at row {k}: {G_sum[k]} != G[{G_i[k]}]+G[{G_j[k]}]")
            return False
    ok("Pair sums consistent with singles (spot-checked).")

    # 6) File size consistency (last array should end at file size)
    last_end = 0
    with open(path, "rb") as f:
        size = os.path.getsize(path)
        for name in SECTION_ORDER:
            off, ln = sections[name]
            tcode = {"R":"q","G":"q","mantissa_idx":"H","decade":"b",
                     "S_sum":"q","S_i":"I","S_j":"I",
                     "G_sum":"q","G_i":"I","G_j":"I"}[name]
            end = off + ln * array(tcode).itemsize
            if end > last_end:
                last_end = end
        if last_end != size:
            fail(f"Trailing bytes or truncation detected: last_end={last_end}, file_size={size}")
            return False

    ok("File size matches end of last array.")
    ok(f"All checks passed for E{hdr['e_series_id']} (n={n}, m={mS}).")
    return True

def main(argv: List[str]) -> int:
    if sys.byteorder != "little":
        print("WARNING: Non little-endian host; this validator assumes little-endian for array.frombytes().", file=sys.stderr)

    files = argv[1:]
    if not files:
        # Try all known outputs if present
        defaults = [f"rcf_e{n}.bin" for n in (3, 6, 12, 24, 48, 96, 192)]
        files = [p for p in defaults if os.path.isfile(p)]
        if not files:
            print("Usage: py validate_precomp.py [files...]", file=sys.stderr)
            return 2

    all_ok = True
    for p in files:
        print("=" * 72)
        ok_flag = validate_file(p)
        all_ok = all_ok and ok_flag

    print("=" * 72)
    if all_ok:
        print("ALL REQUESTED FILES PASSED ✅")
        return 0
    else:
        print("VALIDATION FAILED ❌")
        return 1

if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
