"""
Exact-rational certificate generator for the 2x3 i.i.d. U[0,1]^3 DSIC upper bound
(exact_cert_dsic_2x3_m4.npz), enforcing full S_3 item-equivariance.
"""
from pathlib import Path

from fractions import Fraction
import time
import numpy as np
from dsic_rt0_2x3 import solve_dsic_rt0_2x3
from verify_all_certificates import frac_integral_max0_2lin

CERT_DIR = str(Path(__file__).resolve().parents[1] / "certificates")


def certify_2x3_exact_rational(M=4, denom=100000):
    t0 = time.time()
    _, F_float = solve_dsic_rt0_2x3(M=M)
    n_cells = M**3

    def cid(i, j, k):
        return (i * M + j) * M + k

    def decode(c):
        return c // (M * M), (c // M) % M, c % M

    def swap12(c):
        i, j, k = decode(c)
        return cid(j, i, k)

    def swap13(c):
        i, j, k = decode(c)
        return cid(k, j, i)

    # Strict interior mix with (x1, x2, x3) (div = 3 < 4, F[0]=0, F[M]=1)
    alpha = 2e-4
    lin_x = np.linspace(0.0, 1.0, M + 1)[None, :, None, None]
    F_strict = (1.0 - alpha) * F_float + alpha * lin_x

    D = denom
    F_int = np.rint(F_strict * D).astype(np.int64)
    F_int[:, 0, :, :] = np.minimum(F_int[:, 0, :, :], 0)
    F_int[:, M, :, :] = np.maximum(F_int[:, M, :, :], D)

    # Exact Fraction feasibility checks (ZERO float error!)
    F_q = np.empty((n_cells, M + 1, M, M), dtype=object)
    for b in range(n_cells):
        for i in range(M + 1):
            for j in range(M):
                for k in range(M):
                    F_q[b, i, j, k] = Fraction(int(F_int[b, i, j, k]), D)

    rhs_div = Fraction(4, M)
    max_div = Fraction(-1000)
    for b in range(n_cells):
        b12, b13 = swap12(b), swap13(b)
        for j in range(M):
            for k in range(M):
                assert F_q[b, 0, j, k] <= 0
                assert F_q[b, M, j, k] >= 1
        for i in range(M):
            for j in range(M):
                for k in range(M):
                    d = (
                        (F_q[b, i + 1, j, k] - F_q[b, i, j, k])
                        + (F_q[b12, j + 1, i, k] - F_q[b12, j, i, k])
                        + (F_q[b13, k + 1, j, i] - F_q[b13, k, j, i])
                    )
                    assert d <= rhs_div, f"3D div failed: {float(d)} > {float(rhs_div)}"
                    if d > max_div:
                        max_div = d

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
    ub_exact = Fraction(3, M**6) * exact_sum
    out_path = f"{CERT_DIR}/exact_cert_dsic_2x3_m{M}.npz"
    np.savez(out_path, F_int=F_int, denom=D, M=M, ub_float=float(ub_exact))
    print(
        f"[100% EXACT RATIONAL 6D 2x3 U[0,1]^3 DSIC UB | M={M}] "
        f"UB_EXACT = {float(ub_exact):.10f} (exact max_div={float(max_div)*M:.6f} <= 4) | t={time.time()-t0:.2f}s"
    )
    return ub_exact


if __name__ == "__main__":
    certify_2x3_exact_rational(M=4, denom=100000)
