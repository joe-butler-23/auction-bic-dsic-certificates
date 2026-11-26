"""
Analytical Benchmark Calibration: Manelli-Vincent (B = 1, I = 2, i.i.d. U[0, 1])
================================================================================
Exact analytical optimum (Manelli & Vincent 2006; Daskalakis, Deckelbaum & Tzamos 2017):
    Rev*(1, 2, U[0,1]) = (12 + 2*sqrt(2)) / 27 = 0.5492010046202293...
    (where DSIC and BIC coincide).

Tests both halves of the exact-rational pipeline on B = 1:
  1. Conforming RT_0 H(div) weak dual (exact Fraction verification of div <= 3,
     b0 <= 0, b1 >= 1, and exact piecewise-linear integral).
  2. Exact-rational polygon-clipping primal menu lower bound (sum(Area) == 1).
"""

from fractions import Fraction
import math
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import csc_matrix
import sys, os

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from verify_all_certificates import frac_clip_polygon, frac_poly_area, fmt_ceil, fmt_floor, require

EXACT_MV = (12.0 + 2.0 * math.sqrt(2.0)) / 27.0


def frac_int_max0_lin(a0: Fraction, a1: Fraction) -> Fraction:
    """Exact integral of int_0^1 max(0, a0 + (a1 - a0)*u) du."""
    if a0 <= 0 and a1 <= 0:
        return Fraction(0)
    if a0 >= 0 and a1 >= 0:
        return (a0 + a1) / 2
    if a0 < 0 < a1:
        # positive on [u0, 1] where u0 = -a0 / (a1 - a0)
        return a1 * a1 / (2 * (a1 - a0))
    # a0 > 0 > a1: positive on [0, u0] where u0 = a0 / (a0 - a1)
    return a0 * a0 / (2 * (a0 - a1))


def solve_and_certify_b1_rt0(M: int, denom: int = 100000) -> Fraction:
    """Solve symmetric 1-bidder 2-item U[0,1] RT_0 H(div) dual and verify in exact Fractions."""
    # Variables: F[i, j] for i in 0..M, j in 0..M-1 (component 1 on vertical faces; component 2 by swap),
    # plus epigraph variables t[i, j, 0/1] >= max(0, F[i,j]), max(0, F[i+1,j]) for midpoint/trapezoid proxy.
    # For exact LP objective over int_0^1 max(0, L(u)) du, use 4-subinterval trapezoid upper bound in LP.
    nF = (M + 1) * M
    S = 4
    nT = M * M * (S + 1)
    idxF = lambda i, j: i * M + j
    idxT = lambda i, j, s: nF + (i * M + j) * (S + 1) + s

    c = np.zeros(nF + nT)
    for i in range(M):
        for j in range(M):
            for s in range(S + 1):
                w = 0.5 if s in (0, S) else 1.0
                c[idxT(i, j, s)] = 2.0 * w / (M * M * S)

    rows, cols, vals, ub_list = [], [], [], []
    r = 0
    # Divergence constraints: (F[i+1,j] - F[i,j]) + (F[j+1,i] - F[j,i]) <= 3/M
    for i in range(M):
        for j in range(i, M):
            rows.extend([r, r, r, r])
            cols.extend([idxF(i + 1, j), idxF(i, j), idxF(j + 1, i), idxF(j, i)])
            vals.extend([1.0, -1.0, 1.0, -1.0])
            ub_list.append(3.0 / M - 3e-5)  # interior slack > 2/denom for exact rational rounding
            r += 1
    # Epigraph t[i,j,s] >= (1 - s/S)*F[i,j] + (s/S)*F[i+1,j]
    for i in range(M):
        for j in range(M):
            for s in range(S + 1):
                u = s / S
                rows.extend([r, r, r])
                cols.extend([idxF(i, j), idxF(i + 1, j), idxT(i, j, s)])
                vals.extend([1.0 - u, u, -1.0])
                ub_list.append(0.0)
                r += 1

    bounds = []
    for i in range(M + 1):
        for j in range(M):
            if i == 0:
                bounds.append((None, 0.0))
            elif i == M:
                bounds.append((1.0, None))
            else:
                bounds.append((None, None))
    for _ in range(nT):
        bounds.append((0.0, None))

    A_ub = csc_matrix((vals, (rows, cols)), shape=(r, nF + nT))
    res = linprog(c, A_ub=A_ub, b_ub=np.array(ub_list), bounds=bounds, method="highs")
    require(res.success, f"B=1 RT_0 LP failed at M={M}: {res.message}")

    F_float = res.x[:nF].reshape((M + 1, M))
    # Round to exact rationals and strictly enforce boundary/divergence in Fraction arithmetic
    F_q = [[Fraction(int(round(float(F_float[i, j]) * denom)), denom) for j in range(M)] for i in range(M + 1)]
    for j in range(M):
        if F_q[0][j] > 0:
            F_q[0][j] = Fraction(0)
        if F_q[M][j] < 1:
            F_q[M][j] = Fraction(1)
    rhs_div = Fraction(3, M)
    for j in range(M):
        require(F_q[0][j] <= 0, "B=1 b0 failed")
        require(F_q[M][j] >= 1, "B=1 b1 failed")
    for i in range(M):
        for j in range(M):
            require((F_q[i + 1][j] - F_q[i][j]) + (F_q[j + 1][i] - F_q[j][i]) <= rhs_div, f"B=1 div failed at {(i,j)}")

    # Exact integral: 2 * (1/M^2) * sum_{i,j} int_0^1 max(0, L_{i,j}(u)) du
    total = Fraction(0)
    for i in range(M):
        for j in range(M):
            total += frac_int_max0_lin(F_q[i][j], F_q[i + 1][j])
    return Fraction(2, M * M) * total


def certify_b1_mv_primal() -> Fraction:
    """Certify exact rational approximation of Manelli-Vincent 4-menu optimal mechanism."""
    # Exact optimal menu: (0,0,0), (1,0,2/3), (0,1,2/3), (1,1,p_b) with p_b = 861929/1000000 ~ (4-sqrt(2))/3
    menu = [
        (Fraction(0), Fraction(0), Fraction(0)),
        (Fraction(1), Fraction(0), Fraction(2, 3)),
        (Fraction(0), Fraction(1), Fraction(2, 3)),
        (Fraction(1), Fraction(1), Fraction(861929, 1000000)),
    ]
    sq = [(Fraction(0), Fraction(0)), (Fraction(1), Fraction(0)), (Fraction(1), Fraction(1)), (Fraction(0), Fraction(1))]
    areas = []
    for m, (am, bm, pm) in enumerate(menu):
        poly = sq
        for k, (ak, bk, pk) in enumerate(menu):
            if k == m:
                continue
            poly = frac_clip_polygon(poly, ak - am, bk - bm, pk - pm)
        areas.append(frac_poly_area(poly))
    require(sum(areas, Fraction(0)) == Fraction(1), "B=1 polygon areas do not sum to 1")
    return sum((menu[m][2] * areas[m] for m in range(len(menu))), Fraction(0))


if __name__ == "__main__":
    print(f"Manelli-Vincent exact analytical optimum: (12 + 2*sqrt(2))/27 = {EXACT_MV:.12f}")
    lb = certify_b1_mv_primal()
    print(f"[PASS] B=1 Exact Polygon Primal LB (4-option menu): >= {fmt_floor(lb, 12)}")
    require(float(lb) <= EXACT_MV + 1e-15, "Primal LB exceeded exact Manelli-Vincent optimum!")
    for M in (8, 16, 24):
        ub = solve_and_certify_b1_rt0(M)
        print(f"[PASS] B=1 Exact RT_0 Dual UB (M={M:2d}):              <= {fmt_ceil(ub, 12)}  (gap vs exact = +{float(ub) - EXACT_MV:.6f})")
        require(float(ub) >= EXACT_MV - 1e-15, f"Dual UB undercut exact Manelli-Vincent optimum at M={M}!")
    print("CALIBRATION PASSED: Exact LB <= Manelli-Vincent <= Exact RT_0 UB.")
