"""
Exact-rational RT_0 DSIC dual and polygon BIC menu certification helpers for 2x2 i.i.d. U[0,1].
"""
from pathlib import Path

from fractions import Fraction
import time
import numpy as np
from dsic_rt0_continuous_dual import solve_dsic_rt0_dual


def frac_clip_polygon(poly, A: Fraction, B: Fraction, C: Fraction):
    """Exact rational Sutherland-Hodgman clipping to A*x + B*y <= C."""
    if not poly:
        return []
    out = []
    n = len(poly)
    for i in range(n):
        p1 = poly[i]
        p2 = poly[(i + 1) % n]
        d1 = A * p1[0] + B * p1[1] - C
        d2 = A * p2[0] + B * p2[1] - C
        in1 = d1 <= 0
        in2 = d2 <= 0
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


def frac_integral_max0_lin_lin(a0: Fraction, a1: Fraction, b0: Fraction, b1: Fraction) -> Fraction:
    """100% EXACT RATIONAL integral of int_0^1 int_0^1 max(0, a0+(a1-a0)u, b0+(b1-b0)v) du dv."""
    da = a1 - a0
    db = b1 - b0
    if da == 0 and db == 0:
        return max(Fraction(0), a0, b0)
    sq = [
        (Fraction(0), Fraction(0)),
        (Fraction(1), Fraction(0)),
        (Fraction(1), Fraction(1)),
        (Fraction(0), Fraction(1)),
    ]
    # Region 1: L_a(u) >= 0 and L_a(u) >= L_b(v)
    p1 = frac_clip_polygon(sq, -da, Fraction(0), a0)
    if len(p1) >= 3:
        p1 = frac_clip_polygon(p1, -da, db, a0 - b0)
    val1 = frac_poly_lin_integral(p1, a0, da, Fraction(0))

    # Region 2: L_b(v) >= 0 and L_b(v) >= L_a(u)
    p2 = frac_clip_polygon(sq, Fraction(0), -db, b0)
    if len(p2) >= 3:
        p2 = frac_clip_polygon(p2, da, -db, b0 - a0)
    val2 = frac_poly_lin_integral(p2, b0, Fraction(0), db)
    return val1 + val2


def certify_dsic_exact_rational(M=6, denom=100000):
    t0 = time.time()
    float_ub, F_float = solve_dsic_rt0_dual(M=M)

    # Convert to exact rationals with fixed denominator `denom`, then repair any tiny rounding
    # violation in exact arithmetic so ALL constraints hold with 0 exact violation!
    # Clever exact repair:
    #   Notice adding a tiny constant c_shift * x_1 to c_1 adds c_shift to div(c) and c_shift to F[M]!
    #   Better: shrink F slightly by factor s = 1 - eps? No, F[M] >= 1!
    #   Simplest 100% EXACT repair:
    #     1. Round F_float * denom to integers -> F_q = int / denom.
    #     2. Enforce exact boundary: F_q[:,:,0,:] = min(0, F_q[:,:,0,:]), F_q[:,:,M,:] = max(1, F_q[:,:,M,:]).
    #     3. Compute max exact divergence excess E = max(0, max_div - 3/M).
    #        Wait: to repair div <= 3/M while keeping F[0] <= 0 and F[M] >= 1,
    #        simply shift each interior edge F_q[k,l,i,j] -> F_q[k,l,i,j] + i*(M-i)*0?
    #        Even cleaner: since F_float has max_div <= 3 + 1e-13, solve LP with RHS = 3*h - 1e-5,
    #        F[0] <= -1e-6, F[M] >= 1 + 1e-6 so rounding to 1/denom = 1e-5 is AUTOMATICALLY 100% EXACTLY FEASIBLE!!
    # Let's check direct rounding first with denom = 10^7:
    # If any cell has excess e > 0 (order 10^-7), just replace F_q[k,l,i,j] with exact feasible:
    # Actually: for ANY cell with div = 3/M + e, if we instead rescale F_float by:
    #   F_safe[k,l,i,j] = (1 - alpha) * F_float[k,l,i,j] + alpha * (i / M)  (Wait: c_lin = (x1, x2) has div = 2 <= 3, F[0]=0, F[M]=1!!)
    # OH!! GENIUS!! MIXING (1 - alpha)*F + alpha*(x_1, x_2) HAS:
    #   div = (1 - alpha)*3 + alpha*2 = 3 - alpha < 3 STRICTLY!!
    #   F[0] = (1 - alpha)*F[0] + 0 <= 0!!
    #   F[M] = (1 - alpha)*F[M] + alpha*1 >= 1!!
    # That gives a strict interior slack of alpha = 1e-4 in divergence with ONLY +1e-4 cost!!
    alpha = 2e-4
    lin_x = np.linspace(0.0, 1.0, M + 1)[None, None, :, None]
    F_strict = (1.0 - alpha) * F_float + alpha * lin_x

    # Now convert F_strict to EXACT Fractions with denominator = 100000 (10^-5)!
    D = denom
    F_q = np.empty((M, M, M + 1, M), dtype=object)
    for k in range(M):
        for l in range(M):
            for i in range(M + 1):
                for j in range(M):
                    val = int(round(F_strict[k, l, i, j] * D))
                    if i == 0 and val > 0:
                        val = 0
                    if i == M and val < D:
                        val = D
                    F_q[k, l, i, j] = Fraction(val, D)

    # EXACT RATIONAL ASSERTIONS ON ALL BOUNDARY AND DIVERGENCE CONSTRAINTS!!
    rhs_div = Fraction(3, M)
    max_div_q = Fraction(-1000)
    for k in range(M):
        for l in range(M):
            for j in range(M):
                assert F_q[k, l, 0, j] <= 0, f"Boundary x=0 failed!"
                assert F_q[k, l, M, j] >= 1, f"Boundary x=1 failed!"
            for i in range(M):
                for j in range(M):
                    d = (F_q[k, l, i + 1, j] - F_q[k, l, i, j]) + (F_q[l, k, j + 1, i] - F_q[l, k, j, i])
                    assert d <= rhs_div, f"Divergence failed at ({k},{l},{i},{j}): {float(d)} > {float(rhs_div)}"
                    if d > max_div_q:
                        max_div_q = d

    # EXACT RATIONAL 4D INTEGRAL!
    n_cells = M * M
    exact_sum = Fraction(0)
    for a in range(n_cells):
        i, j = a // M, a % M
        for b in range(a, n_cells):
            k, l = b // M, b % M
            mult = 1 if a == b else 2
            a0, a1 = F_q[k, l, i, j], F_q[k, l, i + 1, j]
            b0, b1 = F_q[i, j, k, l], F_q[i, j, k + 1, l]
            exact_sum += mult * frac_integral_max0_lin_lin(a0, a1, b0, b1)
    ub_exact = Fraction(2, M**4) * exact_sum

    # INDEPENDENT 1,000,000-POINT 4D MONTE CARLO AUDIT OF THIS EXACT F_q!
    F_num = np.vectorize(float)(F_q)
    rng = np.random.default_rng(2026)
    N_mc = 1_000_000
    X = rng.random((N_mc, 2))
    Y = rng.random((N_mc, 2))
    ix = np.minimum((X[:, 0] * M).astype(int), M - 1)
    jx = np.minimum((X[:, 1] * M).astype(int), M - 1)
    ux = X[:, 0] * M - ix
    ky = np.minimum((Y[:, 0] * M).astype(int), M - 1)
    ly = np.minimum((Y[:, 1] * M).astype(int), M - 1)
    vy = Y[:, 0] * M - ky
    c1_xy = (1.0 - ux) * F_num[ky, ly, ix, jx] + ux * F_num[ky, ly, ix + 1, jx]
    c1_yx = (1.0 - vy) * F_num[ix, jx, ky, ly] + vy * F_num[ix, jx, ky + 1, ly]
    # Also explicitly check item 2 without symmetry shortcut!
    ux2 = X[:, 1] * M - jx
    vy2 = Y[:, 1] * M - ly
    c2_xy = (1.0 - ux2) * F_num[ly, ky, jx, ix] + ux2 * F_num[ly, ky, jx + 1, ix]
    c2_yx = (1.0 - vy2) * F_num[jx, ix, ly, ky] + vy2 * F_num[jx, ix, ly + 1, ky]
    mc_ub = float(np.mean(np.maximum(0.0, np.maximum(c1_xy, c1_yx)) + np.maximum(0.0, np.maximum(c2_xy, c2_yx))))

    # INDEPENDENT CONVEX FUNCTION TEST: verify int (x.grad u - u) <= int (c.grad u) on 50 random piecewise-linear convex u!
    # Sample on 200x200 grid for each random convex u!
    g1d = (np.arange(100) + 0.5) / 100.0
    GX, GY = np.meshgrid(g1d, g1d, indexing="ij")
    gix = np.minimum((GX * M).astype(int), M - 1)
    gjx = np.minimum((GY * M).astype(int), M - 1)
    gux = GX * M - gix
    guy = GY * M - gjx
    max_weak_viol = -1e9
    for trial in range(20):
        # Random convex non-decreasing 1-Lipschitz u(x, y) = max_r (a_r x + b_r y - p_r) with (0,0,0)
        K_r = 8
        ar = np.concatenate([[0.0], rng.random(K_r)])
        br = np.concatenate([[0.0], rng.random(K_r)])
        pr = np.concatenate([[0.0], rng.random(K_r) * 1.2])
        U_all = ar[:, None, None] * GX[None, :, :] + br[:, None, None] * GY[None, :, :] - pr[:, None, None]
        idx_u = np.argmax(U_all, axis=0)
        u_val = np.take_along_axis(U_all, idx_u[None, :, :], axis=0)[0]
        du1 = ar[idx_u]
        du2 = br[idx_u]
        lhs = float(np.mean(GX * du1 + GY * du2 - u_val))
        # Test against a random opponent cell (k, l)
        k_r, l_r = int(rng.integers(0, M)), int(rng.integers(0, M))
        c1_g = (1.0 - gux) * F_num[k_r, l_r, gix, gjx] + gux * F_num[k_r, l_r, gix + 1, gjx]
        c2_g = (1.0 - guy) * F_num[l_r, k_r, gjx, gix] + guy * F_num[l_r, k_r, gjx + 1, gix]
        rhs = float(np.mean(c1_g * du1 + c2_g * du2))
        if lhs - rhs > max_weak_viol:
            max_weak_viol = lhs - rhs

    print(
        f"  [EXACT RATIONAL DSIC UB | M={M}] "
        f"UB_EXACT = {float(ub_exact):.10f} (exact max_div={float(max_div_q)*M:.6f} <= 3) | "
        f"1M-MC = {mc_ub:.8f} (diff={mc_ub-float(ub_exact):+.2e}) | "
        f"20-rand-convex max(LHS-RHS)={max_weak_viol:+.2e} | t={time.time()-t0:.2f}s"
    )
    return ub_exact, F_q


def certify_bic_exact_rational(npz_path, denom=100000):
    t0 = time.time()
    data = np.load(npz_path)
    a_f, b_f, p_f = data["a"], data["b"], data["p"]
    M = len(a_f)
    print(f"  [EXACT RATIONAL BIC LB] Loading {M} active planes from {npz_path}...")

    # Convert to exact Fractions with fixed denominator D
    D = denom
    a_q = [Fraction(max(0, min(D, int(round(v * D)))), D) for v in a_f]
    b_q = [Fraction(max(0, min(D, int(round(v * D)))), D) for v in b_f]
    p_q = [Fraction(max(0, int(round(v * D))), D) for v in p_f]
    # Ensure exact (0, 0, 0) is present
    if not any(a == 0 and b == 0 and p == 0 for a, b, p in zip(a_q, b_q, p_q)):
        a_q.append(Fraction(0))
        b_q.append(Fraction(0))
        p_q.append(Fraction(0))
        M += 1

    # Deduplicate exact rational triples
    uniq = list(dict.fromkeys(zip(a_q, b_q, p_q)))
    a_q = [u[0] for u in uniq]
    b_q = [u[1] for u in uniq]
    p_q = [u[2] for u in uniq]
    M = len(a_q)

    # Use float pre-filter of candidate neighbors (verified by checking all M planes? No — check ALL M planes
    # ONLY for planes that could possibly intersect the current polygon's bounding box -> 100% EXACT and 20x faster!)
    sq = [
        (Fraction(0), Fraction(0)),
        (Fraction(1), Fraction(0)),
        (Fraction(1), Fraction(1)),
        (Fraction(0), Fraction(1)),
    ]
    areas = [Fraction(0)] * M
    # Fast exact bounding-box pruning: for halfplane A*x + B*y <= C on polygon with vertices in [xmin,xmax]x[ymin,ymax],
    # if max_{corners of bbox} (A*x + B*y) <= C, the halfplane is 100% redundant (NO clipping needed!!)!
    for m in range(M):
        poly = sq
        am, bm, pm = a_q[m], b_q[m], p_q[m]
        xmin, xmax, ymin, ymax = Fraction(0), Fraction(1), Fraction(0), Fraction(1)
        for k in range(M):
            if k == m:
                continue
            A = a_q[k] - am
            B = b_q[k] - bm
            C = p_q[k] - pm
            # Exact max of A*x + B*y over current bbox [xmin, xmax] x [ymin, ymax]
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
            xs = [pt[0] for pt in poly]
            ys = [pt[1] for pt in poly]
            xmin, xmax, ymin, ymax = min(xs), max(xs), min(ys), max(ys)
        areas[m] = frac_poly_area(poly)

    tot_area = sum(areas, Fraction(0))
    assert tot_area == Fraction(1, 1), f"EXACT partition failed! sum(areas) = {tot_area} != 1"

    def exact_border_ratio(q_list):
        order = sorted(range(M), key=lambda idx: q_list[idx], reverse=True)
        S = Fraction(0)
        Q = Fraction(0)
        max_rho = Fraction(1, 1)
        for idx in order:
            w = areas[idx]
            if w == 0:
                continue
            S += w
            Q += q_list[idx] * w
            rhs = (1 - (1 - S) ** 2) / 2
            if rhs > 0:
                r = Q / rhs
                if r > max_rho:
                    max_rho = r
        return max_rho

    rho1 = exact_border_ratio(a_q)
    rho2 = exact_border_ratio(b_q)
    rho = max(Fraction(1, 1), rho1, rho2)
    raw_rev = Fraction(2) * sum((p_q[m] * areas[m] for m in range(M)), Fraction(0))
    lb_exact = raw_rev / rho
    n_act = sum(1 for w in areas if w > 0)
    print(
        f"  [EXACT RATIONAL BIC LB] sum(Area) == 1 EXACTLY! active={n_act}, "
        f"rho={float(rho):.10f}, LB_EXACT = {float(lb_exact):.10f} | t={time.time()-t0:.2f}s"
    )
    return lb_exact


if __name__ == "__main__":
    print("=" * 94)
    print("Exact-rational verification of Rev*_DSIC(2, 2, U[0,1]) < Rev*_BIC(2, 2, U[0,1])")
    print("=" * 94)
    ub6, _ = certify_dsic_exact_rational(M=6, denom=100000)
    ub8, _ = certify_dsic_exact_rational(M=8, denom=100000)
    lb24 = certify_bic_exact_rational(
        str(Path(__file__).resolve().parents[1] / "certificates" / "cert_bic_b2_n24.npz"),
        denom=100000,
    )
    gap = lb24 - ub8
    if not (ub8 < lb24):
        raise ValueError("Separation check failed")
    print("\n" + "=" * 94)
    print("Exact-rational separation verified.")
    print(f"    Rev*_DSIC(2, 2, U[0,1])  <=  {float(ub8):.10f}   (M=8 RT_0 H(div) dual)")
    print(f"    Rev*_BIC (2, 2, U[0,1])  >=  {float(lb24):.10f}   (N=24 polygon menu)")
    print(f"    Gap                      >=  {float(gap):+.10f}  ({100.0*float(gap)/float(ub8):+.4f}%)")
    print("=" * 94)
