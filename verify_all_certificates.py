"""
Standalone Zero-Solver Exact-Rational Certificate Verifier
==========================================================
Imports only Python standard library (`argparse`, `fractions`, `hashlib`, `json`,
`pathlib`, `time`) and `numpy` (exact integer `.npz` loader and object-array arithmetic).
No LP/MIP solver, no SciPy, no floating-point inequalities or quadratures.
All checks raise explicit `ValueError` (safe under `python3 -O`).
Upper bounds are rounded strictly UP (exact ceil); lower bounds strictly DOWN (exact floor).

Verifies all exact-rational certificates in `certificates/`:
  1. 2x2 U[0,1] DSIC RT_0 H(div) Dual UB (M = 10):        exact_cert_dsic_b2_m10.npz
  2. 2x2 U[0,1] BIC Polygon Menu + Explicit Ex-Post Rule: cert_bic_b2_n36.npz + cert_expost_bic_b2.json
  3. 3x2 U[0,1] DSIC RT_0 H(div) Dual UB (M = 5):         exact_cert_dsic_b3_m5.npz
  4. 3x2 U[0,1] BIC Polygon Menu + Explicit Ex-Post Rule: cert_bic_b3_n24.npz + cert_expost_bic_b3.json
  5. 2x2 Beta(1,2) Zero-Slack RT_0 DSIC Dual UB (M=8):    exact_cert_dsic_beta12_m8.npz
  6. 6D 2x3 U[0,1]^3 S_3-Equivariant RT_0 DSIC UB (M=4):  exact_cert_dsic_2x3_m4.npz
"""

import argparse
from fractions import Fraction
import hashlib
import json
import os
from pathlib import Path
import time
import numpy as np

ROOT = Path(__file__).resolve().parent
CERT_DIR = ROOT / "certificates"


def require(cond: bool, msg: str) -> None:
    if not cond:
        raise ValueError(f"CERTIFICATE CHECK FAILED: {msg}")


def require_int_array(arr: np.ndarray, name: str) -> None:
    require(isinstance(arr, np.ndarray), f"{name} must be an ndarray")
    require(arr.dtype.kind in ("i", "u"), f"{name} must have exact integer dtype, got {arr.dtype}")


def require_int_scalar(arr: np.ndarray, name: str) -> int:
    require(isinstance(arr, np.ndarray) and arr.ndim == 0, f"{name} must be a 0-d scalar array")
    require(arr.dtype.kind in ("i", "u"), f"{name} must have exact integer dtype, got {arr.dtype}")
    return int(arr.item())


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(65536), b""):
            h.update(chunk)
    return h.hexdigest()


def verify_pinned_hashes(cert_dir: Path) -> dict:
    sums_path = cert_dir / "SHA256SUMS"
    require(sums_path.is_file(), f"Missing pinned digest manifest: {sums_path}")
    expected = {}
    for line in sums_path.read_text().splitlines():
        line = line.strip()
        if not line:
            continue
        parts = line.split()
        require(len(parts) == 2 and len(parts[0]) == 64, f"Malformed SHA256SUMS line: {line!r}")
        digest, fname = parts[0], parts[1]
        fpath = cert_dir / fname
        require(fpath.is_file(), f"Pinned certificate missing: {fpath}")
        actual = sha256_file(fpath)
        require(actual == digest, f"SHA-256 mismatch for {fname}: expected {digest}, got {actual}")
        expected[fname] = actual
    return expected


def fmt_ceil(q: Fraction, digits: int = 10) -> str:
    """Exact directed decimal upper bound (ceil) of Fraction q to `digits` decimal places."""
    scale = 10**digits
    num = q.numerator * scale
    den = q.denominator
    k = -(-num // den)
    sign = "-" if k < 0 else ""
    k = abs(k)
    return f"{sign}{k // scale}.{k % scale:0{digits}d}"


def fmt_floor(q: Fraction, digits: int = 10) -> str:
    """Exact directed decimal lower bound (floor) of Fraction q to `digits` decimal places."""
    scale = 10**digits
    num = q.numerator * scale
    den = q.denominator
    k = num // den
    sign = "-" if k < 0 else ""
    k = abs(k)
    return f"{sign}{k // scale}.{k % scale:0{digits}d}"


def frac_clip_polygon(poly, A: Fraction, B: Fraction, C: Fraction):
    """Exact rational Sutherland-Hodgman clipping to A*x + B*y <= C."""
    if not poly:
        return []
    out = []
    n = len(poly)
    for i in range(n):
        p1, p2 = poly[i], poly[(i + 1) % n]
        d1 = A * p1[0] + B * p1[1] - C
        d2 = A * p2[0] + B * p2[1] - C
        in1, in2 = (d1 <= 0), (d2 <= 0)
        if in1 and in2:
            out.append(p2)
        elif in1 and not in2:
            t = d1 / (d1 - d2)
            out.append((p1[0] + t * (p2[0] - p1[0]), p1[1] + t * (p2[1] - p1[1])))
        elif not in1 and in2:
            t = d1 / (d1 - d2)
            out.append((p1[0] + t * (p2[0] - p1[0]), p1[1] + t * (p2[1] - p1[1])))
            out.append(p2)
    return out


def frac_poly_area(poly) -> Fraction:
    n = len(poly)
    if n < 3:
        return Fraction(0)
    s = Fraction(0)
    for i in range(n):
        x1, y1 = poly[i]
        x2, y2 = poly[(i + 1) % n]
        s += x1 * y2 - x2 * y1
    return abs(s) / 2


def frac_poly_lin_integral(poly, c0: Fraction, c1: Fraction, c2: Fraction) -> Fraction:
    n = len(poly)
    if n < 3:
        return Fraction(0)
    x0, y0 = poly[0]
    total = Fraction(0)
    for i in range(1, n - 1):
        x1, y1 = poly[i]
        x2, y2 = poly[i + 1]
        area = abs((x1 - x0) * (y2 - y0) - (x2 - x0) * (y1 - y0)) / 2
        if area > 0:
            uc = (x0 + x1 + x2) / 3
            vc = (y0 + y1 + y2) / 3
            total += area * (c0 + c1 * uc + c2 * vc)
    return total


def frac_integral_max0_2lin(a0: Fraction, a1: Fraction, b0: Fraction, b1: Fraction) -> Fraction:
    """Exact integral of int_0^1 int_0^1 max(0, a0+(a1-a0)u, b0+(b1-b0)v) du dv."""
    da, db = a1 - a0, b1 - b0
    if da == 0 and db == 0:
        return max(Fraction(0), a0, b0)
    sq = [(Fraction(0), Fraction(0)), (Fraction(1), Fraction(0)), (Fraction(1), Fraction(1)), (Fraction(0), Fraction(1))]
    p1 = frac_clip_polygon(sq, -da, Fraction(0), a0)
    if len(p1) >= 3:
        p1 = frac_clip_polygon(p1, -da, db, a0 - b0)
    v1 = frac_poly_lin_integral(p1, a0, da, Fraction(0))
    p2 = frac_clip_polygon(sq, Fraction(0), -db, b0)
    if len(p2) >= 3:
        p2 = frac_clip_polygon(p2, da, -db, b0 - a0)
    v2 = frac_poly_lin_integral(p2, b0, Fraction(0), db)
    return v1 + v2


def frac_integral_max0_3lin(a0: Fraction, a1: Fraction, b0: Fraction, b1: Fraction, c0: Fraction, c1: Fraction) -> Fraction:
    """Exact integral of int_[0,1]^3 max(0, L_a(u), L_b(v), L_c(w)) via exact cubic Simpson on breakpoints."""
    def cdf_lim(t: Fraction, x0: Fraction, x1: Fraction, side: int) -> Fraction:
        lo, hi = (x0, x1) if x0 <= x1 else (x1, x0)
        if hi == lo:
            if t > hi:
                return Fraction(1)
            if t < hi:
                return Fraction(0)
            return Fraction(1) if side > 0 else Fraction(0)
        if t <= lo:
            return Fraction(0)
        if t >= hi:
            return Fraction(1)
        return (t - lo) / (hi - lo)

    hi_all = max(Fraction(0), a0, a1, b0, b1, c0, c1)
    if hi_all <= 0:
        return Fraction(0)
    bps = sorted(set([Fraction(0), hi_all] + [x for x in (a0, a1, b0, b1, c0, c1) if 0 < x < hi_all]))
    total = Fraction(0)
    for idx in range(len(bps) - 1):
        t0, t1 = bps[idx], bps[idx + 1]
        tm = (t0 + t1) / 2
        g0 = 1 - cdf_lim(t0, a0, a1, +1) * cdf_lim(t0, b0, b1, +1) * cdf_lim(t0, c0, c1, +1)
        gm = 1 - cdf_lim(tm, a0, a1, 0) * cdf_lim(tm, b0, b1, 0) * cdf_lim(tm, c0, c1, 0)
        g1 = 1 - cdf_lim(t1, a0, a1, -1) * cdf_lim(t1, b0, b1, -1) * cdf_lim(t1, c0, c1, -1)
        total += (t1 - t0) * (g0 + 4 * gm + g1) / 6
    return total


def verify_dsic_2x2_u01(path: Path, quiet: bool = False) -> Fraction:
    t0 = time.time()
    digest = sha256_file(path)
    with np.load(path, allow_pickle=False) as d:
        require(set(d.files) >= {"F_int", "denom", "M"}, "2x2 DSIC archive missing required keys")
        F_int = d["F_int"]
        require_int_array(F_int, "F_int")
        D = require_int_scalar(d["denom"], "denom")
        M = require_int_scalar(d["M"], "M")
    require(D > 0 and M > 0, "D, M must be positive")
    require(F_int.shape == (M, M, M + 1, M), "F_int shape mismatch")
    F_q = np.empty((M, M, M + 1, M), dtype=object)
    for k in range(M):
        for l in range(M):
            for i in range(M + 1):
                for j in range(M):
                    F_q[k, l, i, j] = Fraction(int(F_int[k, l, i, j]), D)
    rhs_div = Fraction(3, M)
    for k in range(M):
        for l in range(M):
            for j in range(M):
                require(F_q[k, l, 0, j] <= 0, "2x2 b0")
                require(F_q[k, l, M, j] >= 1, "2x2 b1")
            for i in range(M):
                for j in range(M):
                    require((F_q[k, l, i + 1, j] - F_q[k, l, i, j]) + (F_q[l, k, j + 1, i] - F_q[l, k, j, i]) <= rhs_div, "2x2 div")
    n_cells = M * M
    exact_sum = Fraction(0)
    for a in range(n_cells):
        i, j = a // M, a % M
        for b in range(a, n_cells):
            k, l = b // M, b % M
            mult = 1 if a == b else 2
            exact_sum += mult * frac_integral_max0_2lin(
                F_q[k, l, i, j], F_q[k, l, i + 1, j], F_q[i, j, k, l], F_q[i, j, k + 1, l]
            )
    ub = Fraction(2, M**4) * exact_sum
    if not quiet:
        print(f"[PASS] 2x2 U[0,1] DSIC UB (M={M}):     <= {fmt_ceil(ub)}  (sha256={digest[:16]}.., t={time.time()-t0:.2f}s)")
    return ub


def verify_dsic_3x2_u01(path: Path, quiet: bool = False) -> Fraction:
    t0 = time.time()
    digest = sha256_file(path)
    with np.load(path, allow_pickle=False) as d:
        require(set(d.files) >= {"F_int", "denom", "M"}, "3x2 DSIC archive missing required keys")
        F_int = d["F_int"]
        require_int_array(F_int, "F_int")
        D = require_int_scalar(d["denom"], "denom")
        M = require_int_scalar(d["M"], "M")
    require(D > 0 and M > 0, "D, M must be positive")
    n_cells = M * M
    opp_pairs = [(b, c) for b in range(n_cells) for c in range(b, n_cells)]
    pair_id = {p: idx for idx, p in enumerate(opp_pairs)}
    get_pid = lambda b, c: pair_id[(b, c) if b <= c else (c, b)]
    tcell = lambda a: (a % M) * M + (a // M)
    n_opp = len(opp_pairs)
    require(F_int.shape == (n_opp, M + 1, M), "3x2 F_int shape mismatch")
    F_q = np.empty((n_opp, M + 1, M), dtype=object)
    for pid in range(n_opp):
        for i in range(M + 1):
            for j in range(M):
                F_q[pid, i, j] = Fraction(int(F_int[pid, i, j]), D)
    rhs_div = Fraction(3, M)
    for pid, (b, c) in enumerate(opp_pairs):
        pid_T = get_pid(tcell(b), tcell(c))
        for j in range(M):
            require(F_q[pid, 0, j] <= 0, "3x2 b0")
            require(F_q[pid, M, j] >= 1, "3x2 b1")
        for i in range(M):
            for j in range(M):
                require((F_q[pid, i + 1, j] - F_q[pid, i, j]) + (F_q[pid_T, j + 1, i] - F_q[pid_T, j, i]) <= rhs_div, "3x2 div")
    exact_sum = Fraction(0)
    for a in range(n_cells):
        ia, ja = a // M, a % M
        for b in range(a, n_cells):
            ib, jb = b // M, b % M
            for c in range(b, n_cells):
                ic, jc = c // M, c % M
                mult = 1 if (a == b == c) else (3 if (a == b or b == c) else 6)
                pbc, pac, pab = get_pid(b, c), get_pid(a, c), get_pid(a, b)
                exact_sum += mult * frac_integral_max0_3lin(
                    F_q[pbc, ia, ja], F_q[pbc, ia + 1, ja],
                    F_q[pac, ib, jb], F_q[pac, ib + 1, jb],
                    F_q[pab, ic, jc], F_q[pab, ic + 1, jc],
                )
    ub = Fraction(2, M**6) * exact_sum
    if not quiet:
        print(f"[PASS] 3x2 U[0,1] DSIC UB (M={M}):      <= {fmt_ceil(ub)}  (sha256={digest[:16]}.., t={time.time()-t0:.2f}s)")
    return ub


def require_exact_int(val, name: str) -> int:
    require(type(val) is int, f"{name} must be an exact int (not bool/float), got {type(val).__name__}")
    return val


def parse_json_no_dupes(text: str) -> dict:
    def hook(pairs):
        out = {}
        for k, v in pairs:
            require(k not in out, f"Duplicate JSON key: {k!r}")
            out[k] = v
        return out

    obj = json.loads(text, object_pairs_hook=hook)
    require(isinstance(obj, dict), "JSON certificate root must be an object")
    return obj


def _load_and_clip_bic_menu(path: Path, expected_B: int):
    digest = sha256_file(path)
    with np.load(path, allow_pickle=False) as d:
        require(set(d.files) >= {"a_int", "b_int", "p_int", "denom", "B"}, "BIC archive missing required exact-integer keys")
        a_int, b_int, p_int = d["a_int"], d["b_int"], d["p_int"]
        require_int_array(a_int, "a_int")
        require_int_array(b_int, "b_int")
        require_int_array(p_int, "p_int")
        D = require_int_scalar(d["denom"], "denom")
        B = require_int_scalar(d["B"], "B")
    require(D > 0 and B >= 2 and B == expected_B, f"Invalid D={D} or B={B} (expected {expected_B})")
    require(a_int.ndim == 1 and a_int.shape == b_int.shape == p_int.shape and len(a_int) >= 1, "BIC array shapes mismatch")

    K = len(a_int)
    seen = set()
    has_zero = False
    a_q, b_q, p_q = [], [], []
    tuples = []
    for i in range(K):
        ai, bi, pi = int(a_int[i]), int(b_int[i]), int(p_int[i])
        require(0 <= ai <= D and 0 <= bi <= D, f"Allocation out of [0,1] at index {i}: ({ai},{bi})/{D}")
        require(pi >= 0, f"Negative menu price at index {i}: {pi}")
        tup = (ai, bi, pi)
        require(tup not in seen, f"Duplicate menu option at index {i}: {tup}")
        seen.add(tup)
        tuples.append(tup)
        if tup == (0, 0, 0):
            has_zero = True
        a_q.append(Fraction(ai, D))
        b_q.append(Fraction(bi, D))
        p_q.append(Fraction(pi, D))
    require(has_zero, "Menu must explicitly contain outside option (0, 0, 0) for IR")

    sq = [(Fraction(0), Fraction(0)), (Fraction(1), Fraction(0)), (Fraction(1), Fraction(1)), (Fraction(0), Fraction(1))]
    ai_list = [t[0] for t in tuples]
    bi_list = [t[1] for t in tuples]
    pi_list = [t[2] for t in tuples]
    areas = [Fraction(0)] * K
    for m in range(K):
        poly = sq
        am, bm, pm = ai_list[m], bi_list[m], pi_list[m]
        xmin, xmax, ymin, ymax = Fraction(0), Fraction(1), Fraction(0), Fraction(1)
        for k in range(K):
            if k == m:
                continue
            A = ai_list[k] - am
            Bc = bi_list[k] - bm
            C = pi_list[k] - pm
            if (A * xmax if A > 0 else A * xmin) + (Bc * ymax if Bc > 0 else Bc * ymin) <= C:
                continue
            if (A * xmin if A > 0 else A * xmax) + (Bc * ymin if Bc > 0 else Bc * ymax) >= C:
                poly = []
                break
            poly = frac_clip_polygon(poly, Fraction(A), Fraction(Bc), Fraction(C))
            if len(poly) < 3:
                poly = []
                break
            xs, ys = [pt[0] for pt in poly], [pt[1] for pt in poly]
            xmin, xmax, ymin, ymax = min(xs), max(xs), min(ys), max(ys)
        areas[m] = frac_poly_area(poly)
    require(sum(areas, Fraction(0)) == Fraction(1, 1), "sum(Area) != 1")
    return digest, B, D, tuples, a_q, b_q, p_q, areas


def verify_bic_u01(path: Path, expected_B: int, quiet: bool = False) -> Fraction:
    t0 = time.time()
    digest, B, _D, _tuples, a_q, b_q, p_q, areas = _load_and_clip_bic_menu(path, expected_B)
    K = len(a_q)

    def border_ratio(q_list):
        order = sorted(range(K), key=lambda idx: q_list[idx], reverse=True)
        S, Q, max_rho = Fraction(0), Fraction(0), Fraction(1, 1)
        for idx in order:
            w = areas[idx]
            if w == 0:
                continue
            S += w
            Q += q_list[idx] * w
            rhs = (1 - (1 - S) ** B) / B
            if rhs > 0:
                r = Q / rhs
                if r > max_rho:
                    max_rho = r
        return max_rho

    rho = max(Fraction(1, 1), border_ratio(a_q), border_ratio(b_q))
    lb = Fraction(B) * sum((p_q[m] * areas[m] for m in range(K)), Fraction(0)) / rho
    n_act = sum(1 for w in areas if w > 0)
    if not quiet:
        print(f"[PASS] {B}x2 U[0,1] BIC Border LB ({n_act} act): >= {fmt_floor(lb)}  (sum(Area)==1, rho={fmt_ceil(rho, 8)}, sha256={digest[:16]}.., t={time.time()-t0:.2f}s)")
    return lb


def verify_expost_bic_u01(menu_path: Path, expost_path: Path, expected_B: int, quiet: bool = False) -> Fraction:
    """
    Verify an explicit exact-rational priority-tier ex-post BIC allocation rule without Border's theorem.

    Each bidder maps its report x in [0,1]^2 to its canonical active menu polygon r(x) (smallest active
    index with positive area attaining max_k (a_k x_1 + b_k x_2 - p_k)), independently draws priority
    level L in {0, 1, ..., M} with probability pi_{r, m} = P_{r, m} / A_r for item 1 (and pi_{swap(r), m}
    for item 2), wins an item by highest level >= 1 with uniform tie-breaking, and pays the realized-bundle
    ratio tariff t_b = lambda(x) * (x_1 b_1 + x_2 b_2) with lambda(x) = p_{r(x)} / (a_{r(x)} x_1 + b_{r(x)} x_2) in [0,1].
    """
    t0 = time.time()
    menu_digest, B, _D, tuples, a_q, _b_q, p_q, areas = _load_and_clip_bic_menu(menu_path, expected_B)
    K = len(a_q)

    # Verify exact menu item-symmetry so item 2 uses the swapped region index swap(r)
    tup_to_idx = {tup: i for i, tup in enumerate(tuples)}
    for i, (ai, bi, pi) in enumerate(tuples):
        sw_tup = (bi, ai, pi)
        require(sw_tup in tup_to_idx, f"Menu is not item-symmetric at index {i}: missing {sw_tup}")
        sw = tup_to_idx[sw_tup]
        require(areas[i] == areas[sw], f"Polygon area symmetry mismatch at {i} <-> {sw}")

    expost_digest = sha256_file(expost_path)
    data = parse_json_no_dupes(expost_path.read_text(encoding="utf-8"))
    req_keys = {"format", "B", "menu_file", "item_symmetric", "M", "U_denom", "U_edges_num", "rho_num", "rho_den", "entries"}
    require(set(data.keys()) >= req_keys, "Ex-post BIC JSON missing required keys")
    require(data["format"] == "expost_priority_bic_v1", f"Unsupported ex-post format: {data['format']!r}")
    require(require_exact_int(data["B"], "B") == B, "Ex-post JSON B mismatch")
    require(data["item_symmetric"] is True, "Ex-post JSON must set item_symmetric=true")
    require(data["menu_file"] == menu_path.name, f"Ex-post JSON menu_file mismatch: {data['menu_file']!r}")

    M = require_exact_int(data["M"], "M")
    U_denom = require_exact_int(data["U_denom"], "U_denom")
    rho_num = require_exact_int(data["rho_num"], "rho_num")
    rho_den = require_exact_int(data["rho_den"], "rho_den")
    require(M >= 1 and U_denom > 0, "M and U_denom must be positive")
    require(rho_num > 0 and rho_den > 0, "rho_num and rho_den must be positive")
    rho = Fraction(rho_num, rho_den)
    require(rho >= Fraction(1, 1), f"Scaling factor rho must be >= 1, got {float(rho)}")

    U_edges_num = data["U_edges_num"]
    require(isinstance(U_edges_num, list) and len(U_edges_num) == M + 1, "U_edges_num length must equal M + 1")
    U_edges = []
    prev_u = -1
    for idx, val in enumerate(U_edges_num):
        iv = require_exact_int(val, f"U_edges_num[{idx}]")
        if idx == 0:
            require(iv == 0, "U_edges_num[0] must be 0")
        else:
            require(iv > prev_u, "U_edges_num must be strictly increasing")
        require(iv <= U_denom, "U_edges_num exceeds U_denom")
        prev_u = iv
        U_edges.append(Fraction(iv, U_denom))

    # Exact priority-level masses C_m and exact binomial tie-breaking win probabilities W_m
    C = [Fraction(1) - U_edges[M]] + [U_edges[m] - U_edges[m - 1] for m in range(1, M + 1)]
    W = [Fraction(0)] + [
        ((Fraction(1) - U_edges[m - 1]) ** B - (Fraction(1) - U_edges[m]) ** B) / (B * C[m])
        for m in range(1, M + 1)
    ]

    entries = data["entries"]
    require(isinstance(entries, list) and len(entries) > 0, "entries must be a non-empty list")
    row_sum = [Fraction(0)] * K
    col_sum = [Fraction(0)] * (M + 1)
    row_mean = [Fraction(0)] * K
    seen_rm = set()
    for idx, item in enumerate(entries):
        require(isinstance(item, list) and len(item) == 4, f"Malformed entry at index {idx}")
        r = require_exact_int(item[0], f"entries[{idx}][0]")
        m = require_exact_int(item[1], f"entries[{idx}][1]")
        num = require_exact_int(item[2], f"entries[{idx}][2]")
        den = require_exact_int(item[3], f"entries[{idx}][3]")
        require(0 <= r < K, f"Region index out of range at entry {idx}: {r}")
        require(0 <= m <= M, f"Priority level out of range at entry {idx}: {m}")
        require(num >= 0 and den > 0, f"Invalid rational mass at entry {idx}")
        pair = (r, m)
        require(pair not in seen_rm, f"Duplicate (r, m) pair in ex-post table: {pair}")
        seen_rm.add(pair)
        val = Fraction(num, den)
        row_sum[r] += val
        col_sum[m] += val
        row_mean[r] += W[m] * val

    for r in range(K):
        require(row_sum[r] == areas[r], f"Row probability sum mismatch at region r={r}")
        require(row_mean[r] == areas[r] * a_q[r] / rho, f"Item-1 marginal mismatch at region r={r}")
    for m in range(M + 1):
        require(col_sum[m] == C[m], f"Priority-level mass mismatch at level m={m}")

    lb_expost = Fraction(B) * sum((p_q[r] * areas[r] for r in range(K)), Fraction(0)) / rho
    n_act = sum(1 for w in areas if w > 0)
    if not quiet:
        print(
            f"[PASS] {B}x2 U[0,1] BIC Ex-Post LB ({n_act} act, M={M} tiers, nnz={len(entries)}): "
            f">= {fmt_floor(lb_expost)}  (menu={menu_digest[:12]}.., expost={expost_digest[:12]}.., t={time.time()-t0:.2f}s)"
        )
    return lb_expost


def verify_dsic_2x2_beta12(path: Path, S: int = 8, quiet: bool = False) -> Fraction:
    t0 = time.time()
    digest = sha256_file(path)
    with np.load(path, allow_pickle=False) as d:
        require(set(d.files) >= {"W_int", "denom", "M"}, "Beta(1,2) DSIC archive missing required keys")
        W_int = d["W_int"]
        require_int_array(W_int, "W_int")
        D = require_int_scalar(d["denom"], "denom")
        M = require_int_scalar(d["M"], "M")
    require(D > 0 and M > 0 and S > 0, "D, M, S must be positive")
    require(W_int.shape == (M, M, M + 1, M), "Beta12 W_int shape mismatch")
    for k in range(M):
        for l in range(M):
            for j in range(M):
                require(int(W_int[k, l, 0, j]) * M <= D * (M - j - 1), "Beta12 b0")
                require(int(W_int[k, l, M, j]) >= 0, "Beta12 b1")
            for i in range(M):
                for j in range(M):
                    div_num = (int(W_int[k, l, i + 1, j]) - int(W_int[k, l, i, j])) + (
                        int(W_int[l, k, j + 1, i]) - int(W_int[l, k, j, i])
                    )
                    require(div_num <= 0, "Beta12 div")
    G = M * S
    F_num = np.array([4 * (G - p) * (5 * p - G) + 5 for p in range(G + 1)], dtype=object)
    OM = np.array([G - p for p in range(G + 1)], dtype=object)
    wt1 = np.array([1 if r in (0, S) else 2 for r in range(S + 1)], dtype=object)
    WT4 = wt1[:, None, None, None] * wt1[None, :, None, None] * wt1[None, None, :, None] * wt1[None, None, None, :]
    rg = np.arange(S + 1, dtype=np.int64)
    R1, R2, S1, S2 = np.meshgrid(rg, rg, rg, rg, indexing="ij")
    R1_obj = R1.astype(object)
    S1_obj = S1.astype(object)
    SD = int(S * D)
    FOUR_G3 = int(4 * (G**3))
    n_cells = M * M
    total_num = 0
    for a in range(n_cells):
        i, j = a // M, a % M
        for b in range(a, n_cells):
            k, l = b // M, b % M
            mult = 1 if a == b else 2
            a0, a1 = int(W_int[k, l, i, j]), int(W_int[k, l, i + 1, j])
            b0, b1 = int(W_int[i, j, k, l]), int(W_int[i, j, k + 1, l])
            w_xy = F_num[i * S + R1] * OM[j * S + R2] * SD + ((S - R1_obj) * a0 + R1_obj * a1) * FOUR_G3
            w_yx = F_num[k * S + S1] * OM[l * S + S2] * SD + ((S - S1_obj) * b0 + S1_obj * b1) * FOUR_G3
            ry = 4 * OM[k * S + S1] * OM[l * S + S2]
            rx = 4 * OM[i * S + R1] * OM[j * S + R2]
            mx = np.maximum(0, np.maximum(w_xy * ry, w_yx * rx))
            total_num += mult * int(np.sum(mx * WT4))
    DEN = (M**4) * ((2 * S) ** 4) * (4 * (G**3) * S * D) * (G**2)
    ub = Fraction(2 * total_num, DEN)
    if not quiet:
        print(f"[PASS] 2x2 Beta(1,2) DSIC UB (M={M},S={S}): <= {fmt_ceil(ub)}  (denom={D}, max|W|={int(np.max(np.abs(W_int)))}, sha256={digest[:16]}.., t={time.time()-t0:.2f}s)")
    return ub


def verify_dsic_2x3_u01(path: Path, require_s3_equivariance: bool = True, quiet: bool = False) -> Fraction:
    t0 = time.time()
    digest = sha256_file(path)
    with np.load(path, allow_pickle=False) as d:
        require(set(d.files) >= {"F_int", "denom", "M"}, "2x3 DSIC archive missing required keys")
        F_int = d["F_int"]
        require_int_array(F_int, "F_int")
        D = require_int_scalar(d["denom"], "denom")
        M = require_int_scalar(d["M"], "M")
    require(D > 0 and M > 0, "D, M must be positive")
    n_cells = M**3
    require(F_int.shape == (n_cells, M + 1, M, M), "2x3 F_int shape mismatch")
    if require_s3_equivariance:
        arr6 = F_int.reshape((M, M, M, M + 1, M, M))
        require(np.array_equal(arr6, arr6.transpose(0, 2, 1, 3, 5, 4)), "2x3 (23) item-stabilizer equivariance failed")
    cid = lambda i, j, k: (i * M + j) * M + k
    decode = lambda c: (c // (M * M), (c // M) % M, c % M)
    swap12 = lambda c: cid(decode(c)[1], decode(c)[0], decode(c)[2])
    swap13 = lambda c: cid(decode(c)[2], decode(c)[1], decode(c)[0])
    F_q = np.empty((n_cells, M + 1, M, M), dtype=object)
    for b in range(n_cells):
        for i in range(M + 1):
            for j in range(M):
                for k in range(M):
                    F_q[b, i, j, k] = Fraction(int(F_int[b, i, j, k]), D)
    rhs_div = Fraction(4, M)
    for b in range(n_cells):
        b12, b13 = swap12(b), swap13(b)
        for j in range(M):
            for k in range(M):
                require(F_q[b, 0, j, k] <= 0, "2x3 b0")
                require(F_q[b, M, j, k] >= 1, "2x3 b1")
        for i in range(M):
            for j in range(M):
                for k in range(M):
                    require(
                        (F_q[b, i + 1, j, k] - F_q[b, i, j, k])
                        + (F_q[b12, j + 1, i, k] - F_q[b12, j, i, k])
                        + (F_q[b13, k + 1, j, i] - F_q[b13, k, j, i]) <= rhs_div,
                        "2x3 div",
                    )
    exact_sum = Fraction(0)
    for a in range(n_cells):
        ia, ja, ka = decode(a)
        for b in range(a, n_cells):
            ib, jb, kb = decode(b)
            mult = 1 if a == b else 2
            exact_sum += mult * frac_integral_max0_2lin(
                F_q[b, ia, ja, ka], F_q[b, ia + 1, ja, ka],
                F_q[a, ib, jb, kb], F_q[a, ib + 1, jb, kb],
            )
    ub = Fraction(3, M**6) * exact_sum
    if not quiet:
        print(f"[PASS] 6D 2x3 U[0,1]^3 DSIC UB (M={M}): <= {fmt_ceil(ub)}  (S_3 equivariant, sha256={digest[:16]}.., t={time.time()-t0:.2f}s)")
    return ub


def main() -> None:
    parser = argparse.ArgumentParser(description="Verify all exact-rational multi-item auction certificates.")
    parser.add_argument("--cert-dir", type=Path, default=CERT_DIR, help="Directory containing certificates and SHA256SUMS")
    parser.add_argument("--beta-subdiv", type=int, default=8, help="Subdivisions S per coarse cell for Beta(1,2) quadrature (default: 8)")
    parser.add_argument("--skip-hashes", action="store_true", help="Skip pinned SHA256SUMS verification (testing only)")
    parser.add_argument("--json", action="store_true", help="Emit machine-readable JSON summary to stdout")
    args = parser.parse_args()

    quiet = args.json
    hashes = {} if args.skip_hashes else verify_pinned_hashes(args.cert_dir)

    if not quiet:
        print("=" * 102)
        print("EXACT-RATIONAL CERTIFICATE VERIFICATION (ZERO-SOLVER, python3 -O SAFE)")
        print("=" * 102)
        if hashes:
            print(f"[PASS] Pinned SHA256SUMS verified for {len(hashes)} certificate files.")

    ub2 = verify_dsic_2x2_u01(args.cert_dir / "exact_cert_dsic_b2_m10.npz", quiet=quiet)
    lb2 = verify_expost_bic_u01(
        args.cert_dir / "cert_bic_b2_n36.npz",
        args.cert_dir / "cert_expost_bic_b2.json",
        expected_B=2,
        quiet=quiet,
    )
    require(ub2 <= Fraction(8817556131, 10**10), "2x2 DSIC headline UB regression")
    require(ub2 < Fraction(882351585488796576, 10**18), "2x2 DSIC did not beat Fang 2026 lower endpoint")
    require(lb2 >= Fraction(8911490551, 10**10), "2x2 explicit ex-post BIC headline LB regression")
    require(ub2 < lb2, "2x2 separation failed")
    if not quiet:
        print(f"  ==> 2x2 U[0,1]: DSIC <= {fmt_ceil(ub2)} < {fmt_floor(lb2)} <= BIC (explicit ex-post, gap >= +{fmt_floor(lb2 - ub2)})\n")

    ub3 = verify_dsic_3x2_u01(args.cert_dir / "exact_cert_dsic_b3_m5.npz", quiet=quiet)
    lb3 = verify_expost_bic_u01(
        args.cert_dir / "cert_bic_b3_n24.npz",
        args.cert_dir / "cert_expost_bic_b3.json",
        expected_B=3,
        quiet=quiet,
    )
    require(ub3 <= Fraction(11092371527, 10**10), "3x2 DSIC headline UB regression")
    require(ub3 < Fraction(112, 100), "3x2 DSIC did not beat JPW 2026 (1.120)")
    require(lb3 >= Fraction(11102826130, 10**10), "3x2 explicit ex-post BIC headline LB regression")
    require(ub3 < lb3, "3x2 separation failed")
    if not quiet:
        print(f"  ==> 3x2 U[0,1]: DSIC <= {fmt_ceil(ub3)} < {fmt_floor(lb3)} <= BIC (explicit ex-post, gap >= +{fmt_floor(lb3 - ub3)})\n")

    ub_beta = verify_dsic_2x2_beta12(args.cert_dir / "exact_cert_dsic_beta12_m8.npz", S=args.beta_subdiv, quiet=quiet)
    require(ub_beta <= Fraction(5878659834, 10**10) if args.beta_subdiv >= 8 else ub_beta <= Fraction(5881532649, 10**10), "Beta(1,2) DSIC headline UB regression")
    if not quiet:
        print(f"  ==> 2x2 Beta(1,2) full [0,1]^2: DSIC <= {fmt_ceil(ub_beta)} (exact S={args.beta_subdiv})\n")

    ub23 = verify_dsic_2x3_u01(args.cert_dir / "exact_cert_dsic_2x3_m4.npz", require_s3_equivariance=True, quiet=quiet)
    require(ub23 <= Fraction(13905597048, 10**10), "6D 2x3 DSIC headline UB regression")
    if not quiet:
        print(f"  ==> 6D 2x3 U[0,1]^3: DSIC <= {fmt_ceil(ub23)} (exact S_3-equivariant)\n")
        print("=" * 102)
        print("ALL EXACT-RATIONAL CERTIFICATES VERIFIED (python3 -O SAFE, ZERO FLOAT ERROR).")
        print("=" * 102)
    else:
        payload = {
            "status": "PASS",
            "hashes_verified": bool(hashes),
            "results": {
                "2x2_u01_dsic_ub": fmt_ceil(ub2),
                "2x2_u01_bic_expost_lb": fmt_floor(lb2),
                "2x2_u01_gap_lb": fmt_floor(lb2 - ub2),
                "3x2_u01_dsic_ub": fmt_ceil(ub3),
                "3x2_u01_bic_expost_lb": fmt_floor(lb3),
                "3x2_u01_gap_lb": fmt_floor(lb3 - ub3),
                "2x2_beta12_dsic_ub": fmt_ceil(ub_beta),
                "2x2_beta12_subdiv_S": args.beta_subdiv,
                "2x3_u01_dsic_ub": fmt_ceil(ub23),
            },
        }
        print(json.dumps(payload, indent=2))


if __name__ == "__main__":
    main()
