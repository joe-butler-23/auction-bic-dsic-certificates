"""
Generate exact-rational explicit ex-post priority-tier BIC realizations for
2x2 and 3x2 i.i.d. U[0,1] additive auctions from the rationalized polygon menus.

Mechanism construction (for B bidders, 2 items, i.i.d. U[0,1]):
  - Each bidder b reports x^(b) in [0,1]^2 and is assigned its canonical active
    menu polygon r_b = r(x^(b)) in {0, ..., K-1} (breaking measure-zero boundary
    ties by smallest active index r with area A_r > 0).
  - For item 1, bidder b independently draws priority level L_{b,1} in {0, 1, ..., M}
    with exact rational probability pi_{r_b, m} = P_{r_b, m} / A_{r_b}, where m = 0
    is the skip level and m = 1 is highest priority (descending to m = M).
    Item 1 is awarded uniformly among bidders attaining max_b L_{b,1} if >= 1
    (and unallocated if all bidders draw 0).
  - For item 2, when the menu is item-symmetric (verified exactly), bidder b applies
    the same distribution to the swapped polygon index swap(r_b); otherwise an explicit
    second coupling table is exported.
  - Given realized deterministic bundle (b_1, b_2) in {0, 1}^2, bidder b pays
      t_b = lambda(x^(b)) * (x^(b)_1 * b_1 + x^(b)_2 * b_2),
    where lambda(x) = p_{r(x)} / (a_{r(x)} * x_1 + b_{r(x)} * x_2) in [0, 1]
    (0/0 := 0), ensuring realized-bundle ex-post IR and nonnegative transfers.

The exact coupling P_{r,m} is constructed constructively in pure rational arithmetic
via the finite-step Strassen convex-order balayage algorithm (no LP solver).
"""

from fractions import Fraction
import json
from pathlib import Path
import time
import numpy as np

ROOT = Path(__file__).resolve().parents[1]
CERT_DIR = ROOT / "certificates"


def clip_poly_q(poly, A: Fraction, B: Fraction, C: Fraction):
    if not poly:
        return []
    out = []
    n = len(poly)
    for i in range(n):
        p1, p2 = poly[i], poly[(i + 1) % n]
        d1 = A * p1[0] + B * p1[1] - C
        d2 = A * p2[0] + B * p2[1] - C
        if d1 <= 0 and d2 <= 0:
            out.append(p2)
        elif d1 <= 0 and d2 > 0:
            t = d1 / (d1 - d2)
            out.append((p1[0] + t * (p2[0] - p1[0]), p1[1] + t * (p2[1] - p1[1])))
        elif d1 > 0 and d2 <= 0:
            t = d1 / (d1 - d2)
            out.append((p1[0] + t * (p2[0] - p1[0]), p1[1] + t * (p2[1] - p1[1])))
            out.append(p2)
    return out


def area_q(poly) -> Fraction:
    if len(poly) < 3:
        return Fraction(0)
    s = Fraction(0)
    n = len(poly)
    for i in range(n):
        x1, y1 = poly[i]
        x2, y2 = poly[(i + 1) % n]
        s += x1 * y2 - x2 * y1
    return abs(s) / 2


def compute_exact_areas(a_int, b_int, p_int):
    K = len(a_int)
    ai = [int(x) for x in a_int]
    bi = [int(x) for x in b_int]
    pi = [int(x) for x in p_int]
    sq = [
        (Fraction(0), Fraction(0)),
        (Fraction(1), Fraction(0)),
        (Fraction(1), Fraction(1)),
        (Fraction(0), Fraction(1)),
    ]
    areas = [Fraction(0)] * K
    for m in range(K):
        poly = sq
        am, bm, pm = ai[m], bi[m], pi[m]
        xmin = ymin = 0.0
        xmax = ymax = 1.0
        for k in range(K):
            if k == m:
                continue
            A, Bc, C = ai[k] - am, bi[k] - bm, pi[k] - pm
            hi_f = (A * xmax if A > 0 else A * xmin) + (Bc * ymax if Bc > 0 else Bc * ymin)
            if hi_f < C - 1e-3:
                continue
            lo_f = (A * xmin if A > 0 else A * xmax) + (Bc * ymin if Bc > 0 else Bc * ymax)
            if lo_f > C + 1e-3:
                poly = []
                break
            poly = clip_poly_q(poly, Fraction(A), Fraction(Bc), Fraction(C))
            if len(poly) < 3:
                poly = []
                break
            xs = [float(pt[0]) for pt in poly]
            ys = [float(pt[1]) for pt in poly]
            xmin, xmax, ymin, ymax = min(xs), max(xs), min(ys), max(ys)
        areas[m] = area_q(poly)
    if sum(areas, Fraction(0)) != Fraction(1):
        raise ValueError("Polygon areas do not sum to 1")
    return areas


def check_convex_order(A_list, a_list, U_edges, B: int):
    M = len(U_edges) - 1
    C_act = [U_edges[m + 1] - U_edges[m] for m in range(M)]
    W_act = [((1 - U_edges[m]) ** B - (1 - U_edges[m + 1]) ** B) / (B * C_act[m]) for m in range(M)]
    S_act = U_edges[-1]
    mean_W = (1 - (1 - S_act) ** B) / B
    Q_tot = sum((A_list[r] * a_list[r] for r in range(len(A_list))), Fraction(0))
    rho_ex = Q_tot / mean_W
    if rho_ex < 1:
        return False, rho_ex, None, None

    C_full = [1 - S_act] + C_act
    W_full = [Fraction(0)] + W_act
    events = []
    for A, a in zip(A_list, a_list):
        if A > 0:
            events.append((a, 0, A))
    for C, W in zip(C_full, W_full):
        if C > 0:
            events.append((rho_ex * W, 1, C))
    events.sort(key=lambda e: e[0], reverse=True)

    diff_val = Fraction(0)
    diff_mass = Fraction(0)
    prev_u = events[0][0]
    for u, kind, mass in events:
        if u < prev_u:
            diff_val += diff_mass * (prev_u - u)
            if diff_val < 0:
                return False, rho_ex, C_full, W_full
            prev_u = u
        if kind == 1:
            diff_mass += mass
        else:
            diff_mass -= mass
    return True, rho_ex, C_full, W_full


def exact_strassen_coupling(A_list, q_list, C_list, W_list):
    K = len(A_list)
    M1 = len(C_list)
    r_order = sorted([r for r in range(K) if A_list[r] > 0], key=lambda r: q_list[r], reverse=True)
    A_rem = {r: A_list[r] for r in r_order}
    m_sorted = sorted([m for m in range(M1) if C_list[m] > 0], key=lambda m: W_list[m], reverse=True)
    C_rem = {m: C_list[m] for m in m_sorted}

    P = {}
    for r in r_order:
        q = q_list[r]
        while A_rem[r] > 0:
            exact_m = next((m for m in m_sorted if C_rem[m] > 0 and W_list[m] == q), None)
            if exact_m is not None:
                d = min(A_rem[r], C_rem[exact_m])
                P[(r, exact_m)] = P.get((r, exact_m), Fraction(0)) + d
                A_rem[r] -= d
                C_rem[exact_m] -= d
                continue
            above = [m for m in m_sorted if C_rem[m] > 0 and W_list[m] > q]
            below = [m for m in m_sorted if C_rem[m] > 0 and W_list[m] < q]
            if not above or not below:
                raise ValueError(f"Strassen coupling failed at region r={r}")
            mi, mj = above[-1], below[0]
            Wi, Wj = W_list[mi], W_list[mj]
            alpha = (q - Wj) / (Wi - Wj)
            beta = Fraction(1) - alpha
            d = min(A_rem[r], C_rem[mi] / alpha, C_rem[mj] / beta)
            P[(r, mi)] = P.get((r, mi), Fraction(0)) + d * alpha
            P[(r, mj)] = P.get((r, mj), Fraction(0)) + d * beta
            A_rem[r] -= d
            C_rem[mi] -= d * alpha
            C_rem[mj] -= d * beta

    if any(v != 0 for v in C_rem.values()):
        raise ValueError("Nonzero column residual after Strassen coupling")
    return P


def build_expost_cert(menu_fname: str, out_fname: str, M: int = 128, U_denom: int = 10**6):
    t0 = time.time()
    menu_path = CERT_DIR / menu_fname
    with np.load(menu_path, allow_pickle=False) as d:
        a_int = d["a_int"]
        b_int = d["b_int"]
        p_int = d["p_int"]
        D = int(d["denom"])
        B = int(d["B"])

    K = len(a_int)
    a_q = [Fraction(int(x), D) for x in a_int]
    b_q = [Fraction(int(x), D) for x in b_int]
    p_q = [Fraction(int(x), D) for x in p_int]

    # Verify exact item symmetry of menu
    tup_to_idx = {(int(a_int[i]), int(b_int[i]), int(p_int[i])): i for i in range(K)}
    item_sym = all((int(b_int[i]), int(a_int[i]), int(p_int[i])) in tup_to_idx for i in range(K))
    if not item_sym:
        raise ValueError(f"{menu_fname} is not item-symmetric")

    areas = compute_exact_areas(a_int, b_int, p_int)
    for i in range(K):
        sw = tup_to_idx[(int(b_int[i]), int(a_int[i]), int(p_int[i]))]
        if areas[i] != areas[sw]:
            raise ValueError(f"Area symmetry mismatch at index {i} <-> {sw}")

    Q_tot = sum((areas[r] * a_q[r] for r in range(K)), Fraction(0))
    rev_raw = Fraction(B) * sum((areas[r] * p_q[r] for r in range(K)), Fraction(0))
    S_exact_f = 1.0 - (1.0 - B * float(Q_tot)) ** (1.0 / B)

    lo, hi = S_exact_f * 0.98, S_exact_f
    best = None
    for _ in range(30):
        mid = 0.5 * (lo + hi)
        edges_int = [0]
        for j in range(1, M + 1):
            val = int(round((j / M) ** 1.4 * mid * U_denom))
            if val <= edges_int[-1]:
                val = edges_int[-1] + 1
            edges_int.append(val)
        if edges_int[-1] >= U_denom:
            hi = mid
            continue
        U_edges = [Fraction(v, U_denom) for v in edges_int]
        ok, rho_ex, C_full, W_full = check_convex_order(areas, a_q, U_edges, B)
        if ok:
            best = (edges_int, rho_ex, C_full, W_full)
            lo = mid
        else:
            hi = mid

    if best is None:
        raise ValueError(f"Could not find feasible priority grid for {menu_fname}")

    edges_int, rho_ex, C_full, W_full = best
    q_list = [a / rho_ex for a in a_q]
    P = exact_strassen_coupling(areas, q_list, C_full, W_full)

    # Exact self-check before serialization
    for r in range(K):
        s_row = sum((P.get((r, m), Fraction(0)) for m in range(M + 1)), Fraction(0))
        if s_row != areas[r]:
            raise ValueError(f"Row sum mismatch at r={r}")
        s_mean = sum((W_full[m] * P.get((r, m), Fraction(0)) for m in range(M + 1)), Fraction(0))
        if s_mean != areas[r] * q_list[r]:
            raise ValueError(f"Marginal mismatch at r={r}")
    for m in range(M + 1):
        s_col = sum((P.get((r, m), Fraction(0)) for r in range(K)), Fraction(0))
        if s_col != C_full[m]:
            raise ValueError(f"Column sum mismatch at m={m}")

    entries = []
    max_digits = 0
    for (r, m), val in sorted(P.items()):
        if val > 0:
            max_digits = max(max_digits, len(str(val.numerator)), len(str(val.denominator)))
            entries.append([r, m, val.numerator, val.denominator])

    if max_digits >= 4000:
        raise ValueError(f"Integer digit count {max_digits} approaches Python int_max_str_digits limit")

    payload = {
        "format": "expost_priority_bic_v1",
        "B": B,
        "menu_file": menu_fname,
        "item_symmetric": True,
        "M": M,
        "U_denom": U_denom,
        "U_edges_num": edges_int,
        "rho_num": rho_ex.numerator,
        "rho_den": rho_ex.denominator,
        "entries": entries,
    }
    out_path = CERT_DIR / out_fname
    out_path.write_text(json.dumps(payload, separators=(",", ":")) + "\n")
    rev_lb = rev_raw / rho_ex
    print(
        f"[OK] {out_fname}: B={B}, K={K}, M={M}, nnz={len(entries)}, max_digits={max_digits}, "
        f"size={out_path.stat().st_size/1024:.1f} KB, rho={float(rho_ex):.10f}, "
        f"expost_rev_lb={float(rev_lb):.10f} (t={time.time()-t0:.2f}s)"
    )


if __name__ == "__main__":
    build_expost_cert("cert_bic_b2_n36.npz", "cert_expost_bic_b2.json", M=128)
    build_expost_cert("cert_bic_b3_n24.npz", "cert_expost_bic_b3.json", M=128)
