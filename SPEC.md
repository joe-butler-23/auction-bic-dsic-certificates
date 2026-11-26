# Formal Specification & Model Scope

This document states the exact economic setting, definitions, formal theorem statements, and verification bridges for the **additive BIC > DSIC separation track** in this repository (`lean/`, `certificates/`, `verify_all_certificates.py`). For the **unit-demand optimal auction track**, see [`optimal-dsic/PAPER.md`](optimal-dsic/PAPER.md) and [`optimal-dsic/lean/EconCSAuction/Spec.lean`](optimal-dsic/lean/EconCSAuction/Spec.lean).

---

## 1. Common Economic Setting

- **Bidders and items:** $B$ risk-neutral bidders and $I$ indivisible items with additive quasilinear valuations.
- **Type space and prior:** Each bidder $`b \in \{1,\dots,B\}`$ draws a valuation vector $`x^{(b)} \in [0,1]^I`$ independently from a product probability measure $`\mu^{\otimes B}`$:
  - Uniform instances: $`\mu = U([0,1]^I)`$ for $`2 \times 2`$, $`3 \times 2`$, and $`2 \times 3`$.
  - Non-uniform instance: $`\mu = \mathrm{Beta}(1,2)^{\otimes 2}`$ on $[0,1]^2$ with density $`\rho(x_1, x_2) = 4(1-x_1)(1-x_2)`$ for $`2 \times 2`$.
- **Direct revelation mechanism:** Maps each profile $`x = (x^{(1)},\dots,x^{(B)}) \in ([0,1]^I)^B`$ to item allocation probabilities $`q_{b,j}(x) \in [0,1]`$ and transfers $`t_b(x) \in \mathbb{R}`$.
- **Ex-post supply feasibility:** For every profile $`x \in ([0,1]^I)^B`$ and every item $`j \in \{1,\dots,I\}`$, $`q_{b,j}(x) \ge 0`$ and $`\sum_{b=1}^B q_{b,j}(x) \le 1`$. No symmetry, smoothness, continuity, or $u(0)=0$ normalization is assumed on DSIC competitors; randomized allocations and signed transfers are permitted.
- **Ex-post utility:** For bidder $b$ with true type $`x^{(b)}`$, report $r$, and opponent profile $`x^{(-b)}`$,

```math
u_b(x^{(b)}, r, x^{(-b)}) = \sum_{j=1}^{I} x^{(b)}_j q_{b,j}(r, x^{(-b)}) - t_b(r, x^{(-b)}).
```

- **Dominant-Strategy Incentive Compatibility (DSIC):** Truthful reporting maximizes $`u_b(x^{(b)}, r, x^{(-b)})`$ over all $`r \in [0,1]^I`$ for every opponent profile $`x^{(-b)}`$. (This class strictly contains universally truthful / deterministic DSIC mechanisms, so upper bounds over it are strictly stronger.)
- **Individual Rationality (IR):**
  - *Ex-post IR:* $`u_b(x^{(b)}, x^{(b)}, x^{(-b)}) \ge 0`$ for every profile $x$.
  - *Realized-bundle ex-post IR and No Positive Transfers (NPT):* For every realized deterministic bundle $`(b_1,\dots,b_I) \in \{0,1\}^I`$ allocated to bidder $b$, both realized payment $`t_b \ge 0`$ and realized utility $`\sum_j x^{(b)}_j b_j - t_b \ge 0`$.
  - *Interim IR:* $`\sum_{j=1}^I x^{(b)}_j Q_{b,j}(x^{(b)}) - T_b(x^{(b)}) \ge 0`$ for every type $`x^{(b)}`$, where $`Q_{b,j}(r) = \mathbb{E}_{x^{(-b)}}[q_{b,j}(r, x^{(-b)})]`$ and $`T_b(r) = \mathbb{E}_{x^{(-b)}}[t_b(r, x^{(-b)})]`$.
- **Bayesian Incentive Compatibility (BIC):** Truthful reporting maximizes interim expected utility $`\sum_{j=1}^I x^{(b)}_j Q_{b,j}(r) - T_b(r)`$ over all $`r \in [0,1]^I`$.
- **Objective:** Total expected seller revenue

```math
\mathrm{Rev}(M) = \mathbb{E}_{x \sim \mu^{\otimes B}}\!\left[\sum_{b=1}^{B} t_b(x)\right].
```

---

## 2. Lean 4 Formalization ($`2 \times 2`$, $U[0,1]$)

### 2.1 Headline Theorem (`AuctionSep.main_theorem_equal_ex_post_ir`)

Defined in [`lean/AuctionSep/EqualExPostIR.lean`](lean/AuctionSep/EqualExPostIR.lean) over the Mathlib Lebesgue-measure specification in [`lean/AuctionSep/Problem.lean`](lean/AuctionSep/Problem.lean).

The theorem constructs an explicit feasible mechanism $`M_{\mathrm{bic}}`$ (based on an explicit $`72 \times 72`$ ex-post allocation table in [`BICWitness.lean`](lean/AuctionSep/BICWitness.lean)), a ratio payment factor $`\lambda : [0,1]^2 \to [0,1]`$, and $c = 2324277 / 2621440$ satisfying:

1. `IsFeasible M_bic`, `IsBIC M_bic`, and `IsExPostIR M_bic` (including joint `IntegrableOn` of all allocation and payment maps on $`[0,1]^2 \times [0,1]^2`$ and slice `IntegrableOn` at every $`x, y \in [0,1]^2`$).
2. Pointwise No Positive Transfers: $`0 \le t_1(x,y)`$ and $`0 \le t_2(x,y)`$ for all $`x, y \in [0,1]^2`$.
3. Ratio payment structure: $`t_1(x,y) = \lambda(x)(x_1 q_{11}(x,y) + x_2 q_{12}(x,y))`$ and symmetrically for $`t_2`$, with $`0 \le \lambda(x) \le 1`$.
4. Realized-bundle ex-post IR and NPT: for every $`x \in [0,1]^2`$ and every $`b_1, b_2 \ge 0`$,

```math
0 \le \lambda(x)(x_1 b_1 + x_2 b_2) \le x_1 b_1 + x_2 b_2.
```

5. Strict separation: $`\mathrm{Rev}(M_{\mathrm{bic}}) = 62105 / 69984 > 2324277 / 2621440 = c`$ (exact gap $4447801 / 5733089280$).
6. Universal DSIC upper bound under **either** participation condition: for every `M_dsic` satisfying `IsFeasible M_dsic`, `IsDSIC M_dsic`, and `IsExPostIR M_dsic ∨ IsInterimIR M_dsic`,

```math
\mathrm{Rev}(M_{\mathrm{dsic}}) \le c.
```

The `IsInterimIR` DSIC bound (`AuctionSep.dsic_interimIR_expectedRevenue_le`) is proved by Fubini slice integrability on $`[0, \varepsilon]^2`$: shifting transfers by $`-t_1(x_0, y)`$ and $`-t_2(x, y_0)`$ preserves feasibility and DSIC, enforces `IsExPostIR`, and changes expected revenue by at most $`4\varepsilon \to 0`$.

### 2.2 Frozen Specification Theorem (`AuctionSep.main_theorem`)

[`lean/AuctionSep/Problem.lean`](lean/AuctionSep/Problem.lean) (`AuctionSep.MainGoal`, proved in [`Solution.lean`](lean/AuctionSep/Solution.lean)) is preserved unmodified as the original problem statement comparing `BIC + InterimIR` against `DSIC + ExPostIR`. Its raw flat-tariff witness is superseded by `M_bic_exPostIR` in `EqualExPostIR.lean`.

### 2.3 Kernel Verification

Both theorems compile under Lean `v4.36.0` with standard axioms `[propext, Classical.choice, Quot.sound]` only (zero `sorry`, zero `native_decide`), pass `lake env leanchecker` and `lake env leanchecker --fresh` ([`lean/logs/lean_kernel_check.log`](lean/logs/lean_kernel_check.log)), and pass the independent Rust kernel `nanoda 0.4.17` across all `43,445` exported declarations ([`lean/logs/lean_nanoda.log`](lean/logs/lean_nanoda.log)).

---

## 3. Exact-Rational Python Certificates (`verify_all_certificates.py`)

Verified offline with zero LP/convex-hull solver and zero floating-point inequalities. Every check raises `ValueError` via `require()` (`python3 -O` safe), rejects non-integer dtypes, booleans, floats, and duplicate JSON keys, and verifies pinned `certificates/SHA256SUMS` before evaluating exact `fractions.Fraction` bounds.

### 3.1 DSIC Upper Bounds ($`H(\mathrm{div})`$ $`RT_0`$ Weak Duality)

- **Analytic bridge (not formalized in Lean beyond the coarser $`2 \times 2`$ bound):** By Giannakopoulos and Koutsoupias (2014, 2015), any $`H(\mathrm{div})`$-conforming piecewise-smooth flux $`w^{(b)}(\cdot; x^{(-b)})`$ on $[0,1]^I$ with boundary traces $`w^{(b)}_j\vert_{x_j=0} \le 0`$, $`w^{(b)}_j\vert_{x_j=1} \ge \rho(x^{(b)})\vert_{x_j=1}`$ and cellwise divergence $`\mathrm{div}_{x^{(b)}} w^{(b)} \le (I+1)\rho(x^{(b)}) + x^{(b)} \cdot \nabla\rho(x^{(b)})`$ certifies

```math
\mathrm{Rev}(M) \le \int_{([0,1]^I)^B} \sum_{j=1}^{I} \max\!\left(0, \max_{b=1,\dots,B} w^{(b)}_j(x^{(b)}; x^{(-b)})\,\rho^{(-b)}(x^{(-b)})\right) dx
```

for every feasible DSIC mechanism under ex-post IR (and, by the corner-shift argument above, also under interim IR).

- **Exact integration per instance:**
  - $`2 \times 2`$, $U[0,1]$ ($M = 10$): exact piecewise-linear 2-variable cell integration in `Fraction` ($`\le 0.8817556131`$).
  - $`3 \times 2`$, $U[0,1]$ ($M = 5$): exact breakpoint-partitioned cubic Simpson integration on $[0,1]^3$, algebraically exact for piecewise cubic CDF products ($`\le 1.1092371527`$).
  - $`2 \times 3`$, $U[0,1]^3$ ($M = 4$): exact 6D cellwise integration with explicit $(23)$-stabilizer check confirming full $`S_3`$ item-equivariance ($`\le 1.3905597048`$).
  - $`2 \times 2`$, $`\mathrm{Beta}(1,2)`$ ($M = 8, S = 8$): decomposes $`w = w^{\mathrm{base}} + w^{\mathrm{res}}`$ with $`w^{\mathrm{base}}_1(x) = (1-x_2)(1-x_1)(5x_1-1)`$, which satisfies $`\mathrm{div}\,w^{\mathrm{base}} = m_\rho`$ identically without dividing by $`\rho`$; verifies $`\mathrm{div}\,w^{\mathrm{res}} \le 0`$ in exact integers; upper-bounds the 4D integral on subgrid $G = M S = 64$ via exact integer trapezoidal quadrature with the exact chord pad $+5/(4G^2)$ from $f''(t) = -10$ ($`\le 0.5878659834`$).

### 3.2 Explicit Ex-Post BIC Lower Bounds ($`2 \times 2`$ and $`3 \times 2`$, $U[0,1]$)

No appeal to Border's existence theorem is made at verification time.

- **Exact menu partition:** Given exact integer triples $`\{(a_r, b_r, p_r)/D\}_{r=0}^{K-1} \subset [0,1]^2 \times \mathbb{R}_{\ge 0}`$ containing $(0,0,0)$ with zero duplicates, exact rational half-plane clipping computes every cell polygon area $`A_r`$ and verifies $`\sum_{r=0}^{K-1} A_r = 1`$, together with exact item-symmetry $`(a_r, b_r, p_r) \mapsto (b_r, a_r, p_r)`$ preserving polygon areas $`A_{\mathrm{swap}(r)} = A_r`$.
- **Pointwise tie-breaking:** Because the union of closed positive-area polygons has Lebesgue measure $1$ inside $[0,1]^2$, it equals all of $[0,1]^2$. Mapping each $`x \in [0,1]^2`$ to the smallest active index $r(x)$ with $`A_{r(x)} > 0`$ attaining $`\max_k (a_k x_1 + b_k x_2 - p_k)`$ ensures every report selects an active polygon and achieves exact pointwise BIC everywhere on $[0,1]^2$.
- **Explicit priority-tier allocation rule:** Given exact rational tier thresholds $`0 = U_0 < U_1 < \dots < U_M \le 1`$ ($M = 128$), tier masses $`C_0 = 1 - U_M`$ and $`C_m = U_m - U_{m-1}`$ ($`m \ge 1`$), and exact rational joint probabilities $`P_{r,m} \ge 0`$, each bidder in active region $r$ independently draws tier $`L \in \{0,\dots,M\}`$ with probability $`\pi_{r,m} = P_{r,m}/A_r`$ for item 1 (and $`\pi_{\mathrm{swap}(r),m}`$ for item 2). Awarding each item uniformly among bidders attaining the highest positive tier guarantees $`\sum_{b=1}^B b_{b,j} \in \{0,1\}`$ ex-post on every realization. Against $B-1$ i.i.d. opponents whose tier probabilities are $`C_0, \dots, C_M`$, the exact binomial tie-breaking win probability of tier $`m \ge 1`$ is

```math
W_m = \sum_{k=0}^{B-1} \frac{1}{k+1} \binom{B-1}{k} C_m^k (1 - U_m)^{B-1-k} = \frac{(1 - U_{m-1})^B - (1 - U_m)^B}{B C_m}, \qquad W_0 = 0.
```

- **Exact rational identities checked by `verify_all_certificates.py`:**
  1. Valid conditional distributions: $`\sum_{m=0}^M P_{r,m} = A_r`$ for every $r$.
  2. Self-consistent tier masses: $`\sum_{r=0}^{K-1} P_{r,m} = C_m`$ for every $m$.
  3. Exact interim marginals: $`\sum_{m=0}^M W_m P_{r,m} = A_r a_r / \rho`$ for every $r$ (and $`b_r / \rho`$ for item 2 by verified item symmetry).
- **Realized-bundle ex-post IR and NPT:** Charging $`t_b = \lambda(x^{(b)})(x^{(b)}_1 b_1 + x^{(b)}_2 b_2)`$ with $`\lambda(x) = p_{r(x)}/(a_{r(x)} x_1 + b_{r(x)} x_2) \in [0,1]`$ ($0/0 := 0$) yields nonnegative utility and nonnegative transfer on every realized bundle $`(b_1, b_2) \in \{0,1\}^2`$, with exact expected revenue

```math
\mathrm{Rev} = \frac{B}{\rho} \sum_{r=0}^{K-1} p_r A_r.
```

- **Certified values:**
  - $`2 \times 2`$, $U[0,1]$ ($K = 854, M = 128, 1822$ nonzeros): $`\mathrm{Rev} \ge 0.8911490551`$ (within $`6.9 \times 10^{-6}`$ of the menu's Border limit $0.8911559131$).
  - $`3 \times 2`$, $U[0,1]$ ($K = 409, M = 128, 937$ nonzeros): $`\mathrm{Rev} \ge 1.1102826130`$ (within $`1.36 \times 10^{-5}`$ of the menu's Border limit $1.1102961768$).
