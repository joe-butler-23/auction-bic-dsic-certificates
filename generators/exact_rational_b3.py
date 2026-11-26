"""
Exact-rational certificate generator for 3x2 i.i.d. U[0,1]:
  - M=5 RT_0 H(div) DSIC upper bound (exact_cert_dsic_b3_m5.npz)
  - N=24 rationalized polygon BIC lower bound (cert_bic_b3_n24.npz)
"""
from pathlib import Path

from fractions import Fraction
import time
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import csc_matrix


def frac_integral_max0_3lin(a0: Fraction, a1: Fraction, b0: Fraction, b1: Fraction, c0: Fraction, c1: Fraction) -> Fraction:
    """
    100.000000000000% EXACT RATIONAL integral of
      int_0^1 int_0^1 int_0^1 max(0, a0+(a1-a0)u, b0+(b1-b0)v, c0+(c1-c0)w) du dv dw
    = int_0^{M_max} (1 - F_A(t) * F_B(t) * F_C(t)) dt !
    On each interval [t0, t1] between consecutive breakpoints of {0, a0, a1, b0, b1, c0, c1},
    each CDF F(t) is exact linear p + q*t, so F_A*F_B*F_C is an exact cubic polynomial!
    Simpson's rule (t1-t0)/6 * (g(t0+) + 4*g(tm) + g(t1-)) is 100% ALGEBRAICALLY EXACT for cubics!!
    """
    def cdf_lin_limit(t: Fraction, x0: Fraction, x1: Fraction, side: int) -> Fraction:
        """Exact linear CDF on (lo, hi); for degenerate lo==hi, returns limit from right (side=+1) or left (side=-1)."""
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
        g0 = 1 - cdf_lin_limit(t0, a0, a1, +1) * cdf_lin_limit(t0, b0, b1, +1) * cdf_lin_limit(t0, c0, c1, +1)
        gm = 1 - cdf_lin_limit(tm, a0, a1, 0) * cdf_lin_limit(tm, b0, b1, 0) * cdf_lin_limit(tm, c0, c1, 0)
        g1 = 1 - cdf_lin_limit(t1, a0, a1, -1) * cdf_lin_limit(t1, b0, b1, -1) * cdf_lin_limit(t1, c0, c1, -1)
        total += (t1 - t0) * (g0 + 4 * gm + g1) / 6
    return total


def certify_b3_dsic_exact_rational(M=5, denom=100000):
    t0 = time.time()
    h = 1.0 / M
    n_cells = M * M

    def transpose_cell(a):
        i, j = a // M, a % M
        return j * M + i

    opp_pairs = []
    pair_id = {}
    for b in range(n_cells):
        for c in range(b, n_cells):
            pair_id[(b, c)] = len(opp_pairs)
            opp_pairs.append((b, c))
    n_opp = len(opp_pairs)

    def get_pid(b, c):
        return pair_id[(b, c) if b <= c else (c, b)]

    n_F = n_opp * (M + 1) * M

    def idx_F(pid, i, j):
        return (pid * (M + 1) + i) * M + j

    triples = [(a, b, c) for a in range(n_cells) for b in range(a, n_cells) for c in range(b, n_cells)]
    n_triples = len(triples)
    n_t = 8 * n_triples
    n_vars = n_F + n_t

    def idx_t(tid, p, q, r):
        return n_F + tid * 8 + p * 4 + q * 2 + r

    obj = np.zeros(n_vars)
    for tid, (a, b, c) in enumerate(triples):
        mult = 1.0 if (a == b == c) else (3.0 if (a == b or b == c) else 6.0)
        w = 2.0 * (h**6) * mult * 0.125
        for p in (0, 1):
            for q in (0, 1):
                for r in (0, 1):
                    obj[idx_t(tid, p, q, r)] = w

    rows, cols, vals, rhs = [], [], [], []
    rc = 0

    def add_row(entries, b_val):
        nonlocal rc
        agg = {}
        for col, val in entries:
            agg[col] = agg.get(col, 0.0) + val
        for col, val in agg.items():
            if abs(val) > 1e-15:
                rows.append(rc)
                cols.append(col)
                vals.append(val)
        rhs.append(b_val)
        rc += 1

    for pid in range(n_opp):
        for j in range(M):
            add_row([(idx_F(pid, 0, j), 1.0)], 0.0)
            add_row([(idx_F(pid, M, j), -1.0)], -1.0)

    for pid, (b, c) in enumerate(opp_pairs):
        pid_T = get_pid(transpose_cell(b), transpose_cell(c))
        for i in range(M):
            for j in range(M):
                if (pid, i, j) > (pid_T, j, i):
                    continue
                add_row(
                    [
                        (idx_F(pid, i + 1, j), +1.0),
                        (idx_F(pid, i, j), -1.0),
                        (idx_F(pid_T, j + 1, i), +1.0),
                        (idx_F(pid_T, j, i), -1.0),
                    ],
                    3.0 * h,
                )

    for tid, (a, b, c) in enumerate(triples):
        ia, ja = a // M, a % M
        ib, jb = b // M, b % M
        ic, jc = c // M, c % M
        pbc, pac, pab = get_pid(b, c), get_pid(a, c), get_pid(a, b)
        for p in (0, 1):
            ca = idx_F(pbc, ia + p, ja)
            for q in (0, 1):
                cb = idx_F(pac, ib + q, jb)
                for r in (0, 1):
                    cc = idx_F(pab, ic + r, jc)
                    it = idx_t(tid, p, q, r)
                    for col in set((ca, cb, cc)):
                        add_row([(col, 1.0), (it, -1.0)], 0.0)

    res = linprog(obj, A_ub=csc_matrix((vals, (rows, cols)), shape=(rc, n_vars)), b_ub=np.array(rhs), bounds=[(None, None)] * n_F + [(0.0, None)] * n_t, method="highs")
    assert res.success, res.message
    F_float = res.x[:n_F].reshape((n_opp, M + 1, M))

    # Strict interior mix with (x1, x2) (div=2 <= 3) and round to EXACT Fractions!
    alpha = 2e-4
    lin_x = np.linspace(0.0, 1.0, M + 1)[None, :, None]
    F_strict = (1.0 - alpha) * F_float + alpha * lin_x
    D = denom
    F_q = np.empty((n_opp, M + 1, M), dtype=object)
    for pid in range(n_opp):
        for i in range(M + 1):
            for j in range(M):
                v = int(round(F_strict[pid, i, j] * D))
                if i == 0 and v > 0:
                    v = 0
                if i == M and v < D:
                    v = D
                F_q[pid, i, j] = Fraction(v, D)

    rhs_div = Fraction(3, M)
    for pid, (b, c) in enumerate(opp_pairs):
        pid_T = get_pid(transpose_cell(b), transpose_cell(c))
        for j in range(M):
            assert F_q[pid, 0, j] <= 0
            assert F_q[pid, M, j] >= 1
        for i in range(M):
            for j in range(M):
                d = (F_q[pid, i + 1, j] - F_q[pid, i, j]) + (F_q[pid_T, j + 1, i] - F_q[pid_T, j, i])
                assert d <= rhs_div

    exact_sum = Fraction(0)
    for a, b, c in triples:
        ia, ja = a // M, a % M
        ib, jb = b // M, b % M
        ic, jc = c // M, c % M
        mult = 1 if (a == b == c) else (3 if (a == b or b == c) else 6)
        pbc, pac, pab = get_pid(b, c), get_pid(a, c), get_pid(a, b)
        exact_sum += mult * frac_integral_max0_3lin(
            F_q[pbc, ia, ja], F_q[pbc, ia + 1, ja],
            F_q[pac, ib, jb], F_q[pac, ib + 1, jb],
            F_q[pab, ic, jc], F_q[pab, ic + 1, jc],
        )
    ub_exact = Fraction(2, M**6) * exact_sum
    print(f"  [EXACT RATIONAL B=3 DSIC UB | M={M}] UB_EXACT = {float(ub_exact):.10f} (t={time.time()-t0:.2f}s)")
    F_int = np.vectorize(lambda q: q.numerator * (denom // q.denominator))(F_q).astype(np.int64)
    np.savez(
        str(Path(__file__).resolve().parents[1] / "certificates" / f"exact_cert_dsic_b3_m{M}.npz"),
        F_int=F_int, denom=denom, M=M, ub_float=float(ub_exact),
    )
    return ub_exact


if __name__ == "__main__":
    # 1. Exact rational B=3, M=5 DSIC UB
    ub3 = certify_b3_dsic_exact_rational(M=5, denom=100000)

    # 2. Generate and exact-rational certify B=3, N=24 BIC polygon menu
    from bic_primal_menu_lp import solve_and_audit
    from exact_rational_certificate_2x2 import frac_clip_polygon, frac_poly_area
    npz3 = str(Path(__file__).resolve().parents[1] / "certificates" / "cert_bic_b3_n24.npz")
    solve_and_audit(B=3, N=24, L=80, save_path=npz3)

    # Exact rational verification for B=3 BIC menu!
    t0 = time.time()
    data = np.load(npz3)
    a_f, b_f, p_f = data["a"], data["b"], data["p"]
    D = 100000
    a_q = [Fraction(max(0, min(D, int(round(v * D)))), D) for v in a_f]
    b_q = [Fraction(max(0, min(D, int(round(v * D)))), D) for v in b_f]
    p_q = [Fraction(max(0, int(round(v * D))), D) for v in p_f]
    if not any(a == 0 and b == 0 and p == 0 for a, b, p in zip(a_q, b_q, p_q)):
        a_q.append(Fraction(0)); b_q.append(Fraction(0)); p_q.append(Fraction(0))
    uniq = list(dict.fromkeys(zip(a_q, b_q, p_q)))
    a_q, b_q, p_q = [u[0] for u in uniq], [u[1] for u in uniq], [u[2] for u in uniq]
    M = len(a_q)
    sq = [(Fraction(0), Fraction(0)), (Fraction(1), Fraction(0)), (Fraction(1), Fraction(1)), (Fraction(0), Fraction(1))]
    areas = [Fraction(0)] * M
    for m in range(M):
        poly = sq
        am, bm, pm = a_q[m], b_q[m], p_q[m]
        xmin, xmax, ymin, ymax = Fraction(0), Fraction(1), Fraction(0), Fraction(1)
        for k in range(M):
            if k == m:
                continue
            A, B, C = a_q[k] - am, b_q[k] - bm, p_q[k] - pm
            max_v = (A * xmax if A > 0 else A * xmin) + (B * ymax if B > 0 else B * ymin)
            if max_v <= C:
                continue
            min_v = (A * xmin if A > 0 else A * xmax) + (B * ymin if B > 0 else B * ymax)
            if min_v >= C:
                poly = []
                break
            poly = frac_clip_polygon(poly, A, B, C)
            if len(poly) < 3:
                poly = []
                break
            xs, ys = [pt[0] for pt in poly], [pt[1] for pt in poly]
            xmin, xmax, ymin, ymax = min(xs), max(xs), min(ys), max(ys)
        areas[m] = frac_poly_area(poly)
    assert sum(areas, Fraction(0)) == Fraction(1, 1)

    def border_ratio_b3(q_list):
        order = sorted(range(M), key=lambda idx: q_list[idx], reverse=True)
        S, Q, max_rho = Fraction(0), Fraction(0), Fraction(1, 1)
        for idx in order:
            w = areas[idx]
            if w == 0:
                continue
            S += w
            Q += q_list[idx] * w
            rhs = (1 - (1 - S) ** 3) / 3
            if rhs > 0:
                r = Q / rhs
                if r > max_rho:
                    max_rho = r
        return max_rho

    rho = max(Fraction(1, 1), border_ratio_b3(a_q), border_ratio_b3(b_q))
    lb3 = Fraction(3) * sum((p_q[m] * areas[m] for m in range(M)), Fraction(0)) / rho
    print(f"  [EXACT RATIONAL B=3 BIC LB | N=24] sum(Area)==1 EXACTLY! LB_EXACT = {float(lb3):.10f} (t={time.time()-t0:.2f}s)")
    assert ub3 < lb3, f"B=3 exact separation failed: {float(ub3)} vs {float(lb3)}"
    print("\n" + "=" * 94)
    print(">>> 100% EXACT RATIONAL PROOF COMPLETE FOR B=3, I=2, U[0,1] TOO!! <<<")
    print(f"    Rev*_DSIC(3, 2, U[0,1])  <=  {float(ub3):.10f}   (exact rational, M=5 RT_0 H(div) dual)")
    print(f"    Rev*_BIC (3, 2, U[0,1])  >=  {float(lb3):.10f}   (exact rational, N=24 polygon menu)")
    print(f"    PROVEN STRICT GAP        >=  {float(lb3 - ub3):+.10f} !!")
    print("=" * 94)
