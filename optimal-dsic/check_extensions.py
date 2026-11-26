#!/usr/bin/env python3
"""
Deterministic checks for optimal-dsic/EXTENSIONS.md (the general-alpha results that are
NOT formalised in Lean).  Nothing here is needed for PAPER.md, whose theorems are proved
in optimal-dsic/lean/.

What this script does, and all it does:
  1. SymPy: the algebraic identities used in the proofs of Lemmas E2, E4 and E5.
  2. mpmath: for a list of exponents alpha, compare the closed forms used in the proofs
     against direct quadrature of the density (two independent computations each), and
     print the constants t0(alpha), J*(alpha), C_A*(alpha), B_elem(alpha), L0(alpha).

It uses no random numbers and writes no files.  A numerical agreement is evidence that a
formula was transcribed correctly; it is not a proof.  Exit status is non-zero on failure.

    uv run --with sympy --with mpmath python3 optimal-dsic/check_extensions.py
"""
import sys
import mpmath as mp
import sympy as sp

FAILED = []


def check(cond, label, detail=""):
    print(f"  [{'ok' if cond else 'FAIL'}] {label}" + (f"  ({detail})" if detail else ""), flush=True)
    if not cond:
        FAILED.append(label)


def symbolic():
    print("1. Symbolic identities (SymPy)")
    a, t, u, x, y = sp.symbols("alpha t u x y", positive=True)
    rho = a**2 * x**(a - 1) * y**(a - 1)
    check(sp.simplify(sp.diff(x * rho, x) + sp.diff(y * rho, y) - 2 * a * rho) == 0,
          "Lemma E5 step 2: div(a rho, b rho) = 2 alpha rho")
    P = (1 + 2*a) / (2*a) * t - (1 - 2*a) * u + a * t / (1 - t) * u - 2 * a**2 / (1 - t) * u**2
    check(sp.simplify(P.subs(u, (1 + 2*a) / (2*a) * t) - (1 + 2*a) * t * (1 - (1 + a) * t) / (1 - t)) == 0,
          "Lemma E2(3): P at u = (1+2a)t/(2a)")
    check(sp.simplify(P.subs(u, 1 / (2*a)) - ((1 + 2*a) * t - (1 - a)) / (2*a)) == 0,
          "Lemma E2(3): P at u = 1/(2a)")
    check(sp.simplify((1 / (1 + a) - (1 - a) / (1 + 2*a)) - a * (a + 2) / ((1 + a) * (1 + 2*a))) == 0,
          "Lemma E2(3): the two t-ranges overlap")
    check(sp.simplify(sp.gamma(a + 1)**2 / sp.gamma(2*a + 1) - (a / 2) * sp.gamma(a)**2 / sp.gamma(2*a)) == 0,
          "Lemma E5 step 4: J*(alpha) = (alpha/2) B(alpha, alpha)")
    g, H, r_end = sp.symbols("g H r_end", positive=True)
    bracket = sp.simplify((-H * ((2*a - 1) * g - r_end) / (t * g)) + (2*a - 1) * H / t - (H / t) * (r_end / g))
    check(bracket == 0, "Lemma E4(3): 1 + H' + (2a-1)H/t = (H/t) rho(1,1-t)/g_T, given the ODE of E2(1)")
    d, q = sp.symbols("d q", positive=True)          # d = 1 - 2 alpha, q = z^d
    al = (1 - d) / 2
    # bound f(z) = ((1+2a) z - 2 z^(1+d)) / d, so f'(z) = ((1+2a) - 2(1+d) q)/d and f(z)/z = ((1+2a) - 2q)/d
    qs = (1 + 2*al) / (4 * (1 - al))
    check(sp.simplify(((1 + 2*al) - 2 * (1 + d) * qs) / d) == 0,
          "Lemma E5 step 5: stationary point z^(1-2a) = (1+2a)/(4(1-a)) of the Term-B bound")
    check(sp.simplify(((1 + 2*al) - 2 * qs) / d - (1 + 2*al) / (2 * (1 - al))) == 0,
          "Lemma E5 step 5: maximum equals B_elem(alpha)")

# --- direct quadrature of the density (substitution s = x^(1/alpha) removes the endpoint singularity)
def gT(al, t):
    return al * mp.quad(lambda x: (x**(1 / al) + t)**(al - 1), [0, (1 - t)**al])


def Iwing(al, s, t):
    return al * mp.quad(lambda x: (x**(1 / al) + t)**(al - 1), [0, s**al])


def tail_direct(al, t):          # P(a - b > t), straight from the product density
    return mp.quad(lambda x: 1 - (x**(1 / al) + t)**al, [0, (1 - t)**al])


def tail_closed(al, t):          # Lemma E2(1)
    return (1 - t)**al / 2 - t / (2 * al) * gT(al, t)


def numeric():
    print("2. Closed forms against direct quadrature (mpmath, 30 digits)")
    mp.mp.dps = 30
    rows = []
    for a_str in ["0.4", "0.25", "0.2", "0.1", "0.05", "0.01"]:
        al = mp.mpf(a_str)
        err = max(abs(tail_closed(al, tt) - tail_direct(al, tt)) for tt in map(mp.mpf, ["0.05", "0.3", "0.6", "0.9"]))
        check(err < mp.mpf("1e-20"), f"alpha={a_str}: tail formula of Lemma E2(1)", f"max err {mp.nstr(err, 3)}")
        ode = max(abs(tt * mp.diff(lambda v: gT(al, v), tt) - ((2*al - 1) * gT(al, tt) - al**2 * (1 - tt)**(al - 1)))
                  for tt in map(mp.mpf, ["0.2", "0.6"]))
        check(ode < mp.mpf("1e-15"), f"alpha={a_str}: ODE of Lemma E2(1)", f"max err {mp.nstr(ode, 3)}")
        t0 = mp.findroot(lambda v: v - tail_direct(al, v) / gT(al, v), mp.mpf("0.37"))
        H = lambda v: tail_closed(al, v) / gT(al, v)
        werr, wmax = mp.mpf(0), -mp.inf
        for tt in [t0 + (1 - t0) * mp.mpf(k) / 5 for k in (1, 2, 3, 4)]:
            for ss in [(1 - tt) * mp.mpf(k) / 10 for k in (1, 5, 9)] + [mp.mpf("1e-6")]:
                rho = al**2 * ss**(al - 1) * (ss + tt)**(al - 1)
                z_def = -Iwing(al, ss, tt) - mp.diff(lambda v: H(v) * Iwing(al, ss, v), tt)
                z_closed = (H(tt) / tt) * (ss * rho - al**2 * (1 - tt)**(al - 1) / gT(al, tt) * Iwing(al, ss, tt))
                werr = max(werr, abs(z_def - z_closed))
                wmax = max(wmax, z_closed / rho / ss)
        check(werr < mp.mpf("1e-15"), f"alpha={a_str}: wing flux closed form of Lemma E4(3)", f"max err {mp.nstr(werr, 3)}")
        check(wmax < 1, f"alpha={a_str}: z2/rho < b at the sampled wing points", f"max ratio {mp.nstr(wmax, 4)}")
        J = mp.gamma(al + 1)**2 / mp.gamma(2 * al + 1)
        K = lambda v: (1 + 2 * al) * gT(al, v) - al**2 * (1 - v)**(al - 1)
        CA = mp.quad(lambda v: v**(1 - 2 * al) * K(v), mp.linspace(0, t0, 6)) / J
        B = (1 + 2 * al) / (2 * (1 - al)) * ((1 + 2 * al) / (4 * (1 - al)))**(1 / (1 - 2 * al))
        rows.append((a_str, t0, J, CA, B, CA + B))
    print("\n   alpha   t0(alpha)        J*(alpha)      C_A*(alpha)    B_elem(alpha)  L0(alpha) = C_A* + B_elem")
    for a_str, t0, J, CA, B, L0 in rows:
        print(f"   {a_str:<6}  {mp.nstr(t0, 12):<15}  {mp.nstr(J, 10):<13}  {mp.nstr(CA, 10):<13}  {mp.nstr(B, 10):<13}  {mp.nstr(L0, 10)}")
    # alpha = 1/2: numerical value of the exact revenue formula proved in Lean (for orientation only)
    g = lambda v: mp.atanh(mp.sqrt(1 - v)) / 2
    Phi = lambda v: 2 * v - mp.sqrt(1 - v) / mp.atanh(mp.sqrt(1 - v))
    G = lambda v: 1 - (mp.sqrt(1 - v) / 2 - v * g(v))
    t0h = mp.findroot(Phi, mp.mpf("0.3658"))
    dR = 2 * mp.quad(lambda v: Phi(v) * g(v) * (2 * G(v) - 1), [t0h, 0.7, 0.99, 1])
    print(f"\n   alpha = 1/2:  t0 = {mp.nstr(t0h, 15)},  revenue - 2L = {mp.nstr(dR, 15)}  (numerical evaluation)")


if __name__ == "__main__":
    symbolic()
    numeric()
    if FAILED:
        print(f"\nFAILED: {len(FAILED)} check(s)")
        sys.exit(1)
    print("\nAll checks passed.")
