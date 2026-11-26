# An exactly revenue-optimal auction for two unit-demand bidders and two items

**Status of every claim in this file.** Theorems 1, 2 and 3 are proved in Lean 4.36 + Mathlib in
[`lean/`](lean/). The statements of Theorems 1 and 3 are the definitions `Theorem1Statement` and
`SharpThresholdStatement` in
[`lean/EconCSAuction/Spec.lean`](lean/EconCSAuction/Spec.lean), a 235-line file containing
definitions only. Section 4 is a reading guide to that proof; where the guide and the Lean source
differ, the Lean source is the authority. No numerical experiment is used anywhere in this file.
Results that are *not* formalised live in [`EXTENSIONS.md`](EXTENSIONS.md) and are not relied on here.

---

## 1. Setting

Two bidders, two indivisible items. Bidder $i$ has values $v_{i1}, v_{i2}$ for the items and is
unit-demand: a bundle $S$ is worth $\max_{j \in S} v_{ij}$ (and $\emptyset$ is worth $0$). The four
values are independent, each distributed as

$$
v_{ij} = L + U_{ij}^2, \qquad U_{ij} \sim \mathrm{Uniform}[0,1],
$$

so $v_{ij} \in [L, L+1]$ with continuous CDF $F(v) = \sqrt{v - L}$ (a shifted $\mathrm{Beta}(\tfrac{1}{2}, 1)$
law), where $L \ge 0$ is a parameter.

A (direct, possibly randomized) mechanism assigns to every bid profile a probability for each bundle
$\emptyset, \{1\}, \{2\}, \{1,2\}$ for each bidder, subject to each item being allocated with total
probability at most one, and a payment for each bidder. We use the standard notions:

- **DSIC**: truthful bidding maximises a bidder's utility at every profile of the other's bid.
- **Ex-post IR**: truthful utility is non-negative at every profile.
- **BIC** and **interim IR**: the same two requirements in expectation over the other bidder's value.

Every feasible DSIC and ex-post IR mechanism is BIC and interim IR. Revenue is the expected sum of
payments. The exact definitions are `IsFeasible`, `IsDSIC`, `IsExPostIR`, `IsBIC`, `IsInterimIR` and
`ExpectedRevenue` in `Spec.lean`. Three points about them are worth stating in words:

- `IsPointwiseFeasible` imposes the marginal probability and item-supply inequalities
  ($q_{i,1} + q_{i,2} + q_{i,12} \le 1$ and $(q_{1,j} + q_{1,12}) + (q_{2,j} + q_{2,12}) \le 1$).
  This marginal polytope strictly relaxes lotteries over deterministic feasible bundle allocations
  $\mathcal X_{\mathrm{det}}$ (for instance, $q_{1,12} = q_{2,1} = q_{2,2} = \tfrac{1}{2}$ satisfies the
  marginal inequalities without being a lottery over $\mathcal X_{\mathrm{det}}$). That relaxation
  strictly strengthens Theorem 1, since every lottery over $\mathcal X_{\mathrm{det}}$ lies inside
  `IsPointwiseFeasible`. Conversely, both $(g^\star, p^\star)$ and the explicit Theorem 2 witness
  `perturbedSymMechanism` are single-item mechanisms with non-negative payments
  (`flagshipMechanism_nonNegPayment`, `perturbedSymMechanism_nonNeg_singleItem`,
  `audit_flagship_deterministic_singleItem`, `audit_perturbedSymMechanism_nonNeg_singleItem`) and
  are formalized directly in Lean as exact lotteries over the 9 deterministic feasible allocations
  $\mathcal X_{\mathrm{det}}$ (`DetAlloc := Fin 2 → Option (Fin 2)`): `CleanRoomAudit.lean`
  proves constructive $2\times 2$ Birkhoff–von Neumann (`audit_singleItem_lotteryRealizable`),
  that $(g^\star, p^\star)$ is a pure deterministic allocation at every profile
  (`audit_flagship_deterministic_lottery`, `audit_flagship_lotteryRealizable`), and that Theorem 2's
  witness satisfies `NonNegPayment L M ∧ IsSingleItem M ∧ IsLotteryRealizable L M`
  (`audit_suboptimal_lotteryRealizable`). `flagshipMechanism_suboptimal_below_two_div_pi` in
  `Theorem2.lean` directly certifies `NonNegPayment L M ∧ IsSingleItem M` alongside
  `IsFeasible L M ∧ IsDSIC L M ∧ IsExPostIR L M` (and `CleanRoomAudit.lean` also checks the sharp
  threshold directly over the `NonNegPayment ∧ IsSingleItem` subclass), while
  `SharpThresholdStatement` in the frozen `Spec.lean` quantifies over
  `IsFeasible ∧ IsDSIC ∧ IsExPostIR` and `IsFeasible ∧ IsBIC ∧ IsInterimIR`.
- Competing mechanisms are **not** required to have non-negative payments, to be deterministic,
  symmetric or continuous. They are only required to be measurable with integrable payments.
- `IsBIC` asks that the interim payment $\mathbb{E}_{v_{-i}}[p_i(b_i, v_{-i})]$ exist as a finite
  integral for every report $b_i \in [L, L+1]^2$. Joint integrability already gives this for almost
  every $b_i$; the clause excludes only mechanisms whose interim payment fails to be integrable at
  some report $b_i$ (preventing Mathlib's `∫ = 0` convention on non-integrable slices), and is
  proved automatically for every feasible DSIC and ex-post IR mechanism (`Lemma1.lean`).

## 2. The mechanism

Write $t_i = b_{i1} - b_{i2}$ for bidder $i$'s reported difference. For $t \in (0,1)$ let

$$
g_T(t) = \tfrac{1}{2} \mathrm{artanh}\sqrt{1-t}, \qquad \Phi_+(t) = 2t - \frac{\sqrt{1-t}}{\mathrm{artanh}\sqrt{1-t}} .
$$

$g_T$ is the density of $v_{i1} - v_{i2}$ at $t > 0$ and $\Phi_+$ is its virtual value
(Myerson, 1981).
$\Phi_+$ has exactly one root $t_0$ in $(0,1)$, and $\tfrac{9}{25} < t_0 < \tfrac{7}{16}$.

The mechanism $(g^\star, p^\star)$ offers each bidder a two-price menu that depends only on the
*other* bidder's difference, and gives her the item she prefers at those prices:

| | price of item 1 | price of item 2 | receives item 1 iff |
|---|---|---|---|
| Bidder 1, if $t_2 \ge -t_0$ | $L + \max(t_0, t_2)$ | $L$ | $b_{11} - p_{1,1} > b_{12} - p_{1,2}$ |
| Bidder 1, if $t_2 < -t_0$ | $L$ | $L + \lvert t_2\rvert$ | $b_{11} - p_{1,1} > b_{12} - p_{1,2}$ |
| Bidder 2, if $t_1 \le t_0$ | $L$ | $L + \max(t_0, -t_1)$ | $b_{21} - p_{2,1} \ge b_{22} - p_{2,2}$ |
| Bidder 2, if $t_1 > t_0$ | $L + t_1$ | $L$ | $b_{21} - p_{2,1} \ge b_{22} - p_{2,2}$ |

Each bidder always receives exactly one item, and the two bidders never receive the same one. In
words: both items are always sold, a bidder with a strong enough preference ($\lvert t_i \rvert > t_0$)
competes for her preferred item, and otherwise the items are split at the base price $L$. This is
`flagshipMechanism` in `Spec.lean`.

## 3. Results

> **Theorem 1 (optimality for $L \ge 2/\pi$).** For every real $L \ge 2/\pi$ the mechanism
> $(g^\star, p^\star)$
> 1. is feasible, DSIC and ex-post IR, with every payment in $[L, L+1]$;
> 2. has expected revenue exactly
>
>    $$
>    2L + 2\int_{t_0}^{1} \Phi_+(t)\, g_T(t)\,\left(2G_T(t) - 1\right)\,dt, \qquad G_T(t) = 1 - \tfrac{1}{2}\sqrt{1-t} + t\, g_T(t);
>    $$
>
> 3. has revenue at least that of **every** feasible BIC and interim-IR mechanism, and in
>    particular of every feasible DSIC and ex-post IR mechanism.
>
> *Lean:* `theorem1_proof : Theorem1Statement` (`Proof.lean`).

> **Theorem 2 (failure for $L < 2/\pi$).** For every $0 \le L < 2/\pi$ there is a feasible, DSIC,
> ex-post IR mechanism with non-negative payments and at most one item per bidder that achieves
> strictly larger expected revenue than $(g^\star, p^\star)$.
>
> *Lean:* `flagshipMechanism_suboptimal_below_two_div_pi` (`Theorem2.lean`).

> **Theorem 3 (the threshold is exact).** For $L \ge 0$, the mechanism $(g^\star, p^\star)$ is
> revenue-optimal among feasible DSIC, ex-post IR mechanisms **if and only if** $L \ge 2/\pi$; and
> it is revenue-optimal among feasible BIC, interim-IR mechanisms **if and only if** $L \ge 2/\pi$.
>
> *Lean:* `sharpThreshold_proof : SharpThresholdStatement` (`Proof.lean`). It is Theorem 1 together
> with Theorem 2.

**Remarks.**

1. *What is and is not settled.* For this distribution the question "for which $L$ is
   $(g^\star, p^\star)$ optimal?" is answered completely: exactly for $L \ge 2/\pi \approx 0.6366$.
   What the optimal mechanism is when $L < 2/\pi$ is not known; Theorem 2 only shows that it is not
   $(g^\star, p^\star)$.
2. *Equality of the two benchmarks.* Since the optimum over the larger BIC class is attained by a
   DSIC mechanism, the optimal BIC and DSIC revenues coincide for this distribution when
   $L \ge 2/\pi$.
3. *Why this distribution, and what the result does not say.* The density
   $f(v) = \tfrac{1}{2\sqrt{v-L}}$ is unbounded at the lower endpoint. This is the feature that
   makes it unprofitable to exclude the lowest types: the probability that both of a bidder's
   values lie within $\varepsilon$ of $L$ is of order $\varepsilon$, not $\varepsilon^2$, so raising
   every price by $\varepsilon$ loses about as much as it gains, and loses more once $L$ is large
   enough (Theorem 2 is the other side of the same computation). Once nobody is excluded, each
   bidder's two-dimensional type matters only through the difference $t_i$, and the problem reduces
   to a one-dimensional one. The theorem therefore says nothing about distributions with bounded
   density such as the uniform distribution, for which the optimal mechanism is not known.
4. *A numerical value.* Evaluating the integral in Theorem 1 numerically gives revenue
   $\approx 2L + 0.128250$. This decimal is not part of the theorem. (Lean does prove that the
   integral is strictly positive: `audit_optimalRevenue_strictly_gt_two_L`.)

## 4. Proof

Throughout, shift values by $L$: write $(a, b) = (v_{i1} - L, v_{i2} - L) \in [0,1]^2$, with density
$\rho(a,b) = \frac{1}{4\sqrt{ab}}$, and $t = a - b$.

### 4.1 Reduction to at most one item per bidder (`Lemma1.lean`)

If a mechanism ever gives a bidder the bundle $\{1,2\}$, give her instead only the item she reported
as more valuable and keep all payments. Truthful utility is unchanged and a misreport can only do
worse, so feasibility, DSIC/BIC, IR and revenue are preserved (`reduceSingleItem_*`). The same file
proves that DSIC with ex-post IR implies BIC with interim IR
(`dsic_exPostIR_implies_bic_interimIR`). So it suffices to bound the revenue of BIC, interim-IR
mechanisms that allocate at most one item to each bidder.

### 4.2 The law of the difference (`Lemma2.lean`)

For $t \in (0,1)$: $\int_0^{1-t} \rho(s+t, s)\,ds = g_T(t)$; more generally
$I(r,t) := \int_0^r \rho(s+t,s)\,ds = \tfrac{1}{2} \ln\frac{\sqrt{r+t} + \sqrt r}{\sqrt t}$. The upper tail
is $1 - G_T(t) = \tfrac{1}{2}\sqrt{1-t} - t\,g_T(t)$. Put

$$
K(t) = 2 g_T(t) - \frac{1}{4\sqrt{1-t}} = \frac{d}{dt}\left[\,2t\,g_T(t) - \tfrac{1}{2}\sqrt{1-t}\,\right].
$$

Then $\Phi_+$ has a unique root $t_0 \in (\tfrac{9}{25}, \tfrac{7}{16})$ (`existsUnique_t0`,
`t0_mem_bounds`), is strictly increasing on $[t_0, 1)$ (`strictMonoOn_PhiPlus`), $K > 0$ on
$(0, t_0]$ (`K_pos`), and $\int_0^{t_0} K = \tfrac{1}{2}$ (`integral_K_Ioo_t0`).

### 4.3 Properties of $(g^\star, p^\star)$ (`Lemma3.lean`)

Each bidder's menu depends only on the other's bid and she receives her preferred option, so the
mechanism is DSIC; the cheaper option costs $L \le v_{ij}$, so it is ex-post IR; checking the four
menu threshold cases directly shows the two bidders never choose the same item
(`b2_decision_iff_not_b1`), and strict monotonicity of $\Phi_+$ on $[t_0,1)$ identifies bidder 1's
allocation with $\mathbf{1}[\bar\Phi(t_1) > \bar\Phi(t_2)]$ on $(-1,1)^2$
(`b1_decision_iff_PhiBar`). Under the measure-preserving bidder-and-item swap involution
$\sigma(b_1, b_2) = ((b_{22}, b_{21}),\,(b_{12}, b_{11}))$, $(g^\star, p^\star)$
interchanges bidders 1 and 2 together with items 1 and 2 (`flagshipMechanism_swap`,
`integral_swapProfile`), so $\mathbb{E}[p_2] = \mathbb{E}[p_1]$ immediately. Integrating bidder 1's
payment rule gives $\mathbb{E}[p_1] - L = t_0(1-G_T(t_0))(2G_T(t_0)-1) + 2\int_{t_0}^1 t(1-G_T(t))g_T(t)\,dt$;
differentiating the antiderivative $A(t) = t(1 - G_T(t))(2(1 - G_T(t)) - 1)$ on $[t_0, 1]$
yields $A'(t) = \Phi_+(t)g_T(t)(2G_T(t) - 1) - 2t(1 - G_T(t))g_T(t)$ (since $(1 - G_T)' = -g_T$ and
$\Phi_+ g_T = t g_T - (1 - G_T)$), with $A(1) = 0$ and $-A(t_0) = t_0(1-G_T(t_0))(2G_T(t_0)-1)$,
giving the revenue formula in Theorem 1 (`flagshipMechanism_isFeasible`, `flagshipMechanism_isDSIC`,
`flagshipMechanism_isExPostIR`, `flagshipMechanism_boundedPayment`,
`flagshipMechanism_expectedRevenue`).

### 4.4 Duality outside the strip (`Lemma4.lean`)

Split the open type square $(0,1)^2$ (full measure) into the strip
$S = \{(a,b) \in (0,1)^2 : \lvert a - b\rvert < t_0\}$ and the wings
$W_\pm = \{(a,b) \in (0,1)^2 : \pm(a-b) > t_0\}$. An *interim profile* is a triple $(u, g_1, g_2)$
on $[0,1]^2$ with $u \ge 0$, $g_1, g_2 \ge 0$, $g_1 + g_2 \le 1$ and the subgradient inequality
$u(x) \ge u(y) + (x - y)\cdot(g_1, g_2)(y)$: exactly what BIC and interim IR give for a bidder's
interim utility and interim allocation (Rochet, 1987). Her expected payment is
$\int ((L+a) g_1 + (L+b) g_2 - u)\rho$.

On the wings $W_+ \cup W_-$ there are explicit functions $\tilde\phi_1, \tilde\phi_2$ (`phi1Wing`,
`phi2Wing`) with

$$
\tilde\phi_1 - \tilde\phi_2 = \pm\Phi_+(\lvert a-b\rvert) \ \text{on } W_\pm, \qquad \tilde\phi_1, \tilde\phi_2 > L,
$$

such that for every interim profile (`lemma4_wing_decomposition`)

$$
\int_{[0,1]^2} \left((L+a) g_1 + (L+b) g_2 - u\right)\rho \;=\; \int_{W_+ \cup W_-} (\tilde\phi_1 g_1 + \tilde\phi_2 g_2)\,\rho \;+\; \mathcal{L}(u, g_1, g_2),
$$

where the *strip functional* is

$$
\mathcal{L} = \int_S \left((L+a) g_1 + (L+b) g_2 - u\right)\rho \;-\; \int_0^{1-t_0} \left(u(t_0+s, s) + u(s, t_0+s)\right)\, t_0\, \rho(t_0+s, s)\,ds .
$$

The identity is an integration by parts against an explicit divergence-form vector field
$(z_1, z_2)$ on the wings. Putting $H(t) = (1 - G_T(t))/g_T(t) = t - \Phi_+(t)$, in $(t, s) = (a-b, b)$
coordinates on $W_+$ ($a = s+t$, $b = s$) the flux is generated directly from the potential
$H(t)\,I(s, t)$ by

$$
z_2(t, s) = -I(s, t) - \partial_t\left(H(t)\,I(s, t)\right) = -\frac{H(t)}{4 t \sqrt{1-t}\, g_T(t)}\, I(s, t) + H(t)\,\frac{\sqrt{s}}{4 t \sqrt{s+t}},
$$

$$
z_1(t, s) - z_2(t, s) = \partial_s\left(H(t)\,I(s, t)\right) = H(t)\,\rho(s+t, s),
$$

with dual virtual values

$$
\tilde\phi_1(a, b) = L + a - \frac{z_1(a-b, b)}{\rho(a, b)}, \qquad \tilde\phi_2(a, b) = L + b - \frac{z_2(a-b, b)}{\rho(a, b)},
$$

and symmetrically on $W_-$ by swapping $(a, b)$ and the item indices $1 \leftrightarrow 2$. From the
generating identity, every boundary and PDE condition is structural (verified in Lean directly on
the expanded expressions `z2WingTS`, `wing_pde_ts`, `z2WingTS_zero`, `z1WingTS_boundary_a1`,
`wWingTS_t0`):
- $\partial_a z_1 + \partial_b z_2 = \partial_s z_2 + \partial_t(z_1 - z_2) = -\partial_s I = -\rho$
  by Clairaut's equality of mixed partials;
- $z_2(t, 0^+) = 0$ because $I(0, t) = 0$ identically in $t$;
- $z_1(t, 1-t) = 0$ by differentiating $H(t)\,I(1-t, t) = 1 - G_T(t)$ along $s = 1 - t$, which gives
  $-I(1-t, t) = \partial_t(H I) - \partial_s(H I) = -I(1-t, t) - z_1(t, 1-t)$;
- $(z_1 - z_2)(t_0, s) = t_0\,\rho(s+t_0, s)$ because $\Phi_+(t_0) = 0 \implies H(t_0) = t_0$.

Positivity of $I(s, t)$ and $H(t) < t$ on $(t_0, 1)$ give $z_2/\rho < \frac{H(t)}{t}s < b$, hence
$\tilde\phi_2 > L$ and $\tilde\phi_1 = \tilde\phi_2 + \Phi_+(t) > L$. Writing the divergence integrand
on $W_+$ as
$[(g_1 + g_2) z_2 + u\,\partial_s z_2] + [g_1(z_1 - z_2) + u\,\partial_t(z_1 - z_2)]$,
the Lean proof (`wingPos_ibp_identity`) applies two exact one-dimensional integrations by parts
(`SubgradIBP.lean`), needing only that $u$ has a monotone subgradient along each line: along each
diagonal $a - b = t$ against $z_2$, and along each horizontal line $b = s$ against $z_1 - z_2$. No
truncation or limit is needed, because $z_2$ vanishes on the edge $b = 0$, the two contributions on
the edge $a = 1$ cancel under $b = 1 - t$, and the two directional partials satisfy
$\lvert\partial_s z_2\rvert \le 4\rho$ and $\lvert\partial_t(z_1 - z_2)\rvert \le 4\rho$ (while
$\lvert z_2\rvert$ is bounded and $0 \le z_1 - z_2 \le \rho$; `dWing_abs_le`, `z2WingTS_abs_le`).

### 4.5 Strip dominance (`Lemma5.lean`, `Lemma5Sharp.lean`)

Let $M_1 = L\int_S\rho - \int_0^{1-t_0} (2s + t_0)\,t_0\,\rho(t_0 + s, s)\,ds$, the value of
$\mathcal{L}$ at $u = \tfrac{1}{2}(a+b)$, $g_1 = g_2 = \tfrac{1}{2}$.

> **Lemma 5.** For every $L \ge 2/\pi$ and every interim profile, $\mathcal{L} \le M_1$, with
> equality for every linear profile $u = ca + (1-c)b$, $g_1 = c$, $g_2 = 1 - c$ ($c \in [0, 1]$).
> (`lemma5_strip_dominance`, `stripFunctional_eq_M1_of_linear`.)

*Proof.* Symmetrising $(u, g_1, g_2)$ to
$(\tfrac{1}{2}(u(a,b)+u(b,a)),\,\tfrac{1}{2}(g_1(a,b)+g_2(b,a)),\,\tfrac{1}{2}(g_2(a,b)+g_1(b,a)))$
does not change $\mathcal{L}$, and subtracting the constant $u(0,0) \ge 0$ does not decrease it, so
assume the profile is symmetric with $u(0,0) = 0$. Put

$$
w = \tfrac{1}{2}(a+b) - u, \qquad D = 1 - (g_1 + g_2) \in [0,1],
$$

and let $S_+ = S \cap \{a > b\}$. Along any line segment in $[0,1]^2$, the convex function $u$ is
Lipschitz with directional subgradient given by $(g_1, g_2)$ (so the 1D fundamental theorem and
integration by parts of `SubgradIBP.lean` hold with the subgradient playing the role of the a.e.
derivative). Five steps.

**(i) Reduction to the half strip** (`radial_green_stripPos`, `lemma5_half_strip_eq`). Along the
ray $\lambda \mapsto (\lambda, \lambda\eta)$ one has $a g_1 + b g_2 = \lambda\,\partial_\lambda u(\lambda,\lambda\eta)$
a.e., and $\rho\,da\,db = \tfrac{1}{4\sqrt\eta}\,d\lambda\,d\eta$ has no singularity in $\lambda$. So
$\int_0^{\Lambda} (\lambda\,\partial_\lambda u + u)\,d\lambda = \Lambda\,u(\Lambda, \Lambda\eta)$ exactly on each ray,
where $\Lambda(\eta) = \min(1, \tfrac{t_0}{1-\eta})$ is where the ray leaves $S_+$. The substitutions
$\eta = 1 - t$ on $(1-t_0, 1)$ and $\eta = \tfrac{s}{s+t_0}$ on $(0, 1-t_0)$ turn the resulting
boundary integral into

$$
\int_{S_+} (a g_1 + b g_2 + u)\,\rho = \int_0^{t_0} u(1,1-t)\,\rho(1,1-t)\,dt + \int_0^{1-t_0} u(s+t_0,s)\,t_0\,\rho(s+t_0,s)\,ds,
$$

with no truncation or limiting argument. Applying this to $u$ and to the linear profile gives the
exact identity

$$
\tfrac{1}{2}(\mathcal{L} - M_1) = -L\int_{S_+} D\rho \;+\; 2\int_{S_+} w\rho \;-\; \int_0^{t_0} w(1, 1-t)\,\rho(1, 1-t)\,dt .
$$

**(ii) Along each diagonal** (`lemma5_diag_identity`). Fix $t \in (0, t_0)$. Along
$s \mapsto (s+t, s)$ the function $w$ has a.e. derivative $D$, so
$w(s+t,s) = w(t,0) + \int_0^s D(r+t,r)\,dr$. Substituting and exchanging the order of integration,

$$
2\int_0^{1-t} w(s+t,s)\,\rho(s+t,s)\,ds - w(1,1-t)\,\rho(1,1-t) \;=\; K(t)\,w(t,0) + \int_0^{1-t} D(r+t,r)\,\psi_t(r)\,dr,
$$

$$
\psi_t(r) = 2\left(g_T(t) - I(r,t)\right) - \rho(1, 1-t).
$$

Integrating over $t$ turns the last two terms of (i) into
$\int_0^{t_0} K(t)\,w(t,0)\,dt + \int_0^{t_0} \int_0^{1-t} D(r+t,r)\,\psi_t(r)\,dr\,dt$.

**(iii) Weighted radial bound in polar uniform coordinates** (`lemma5_ray_bound`). Pass to polar
coordinates in the underlying uniform variables $(U_1, U_2) = (\sqrt a, \sqrt b) = r(\cos\theta, \sin\theta)$
on $\{0 < b < a\}$, so $a = r^2\cos^2\theta$, $b = r^2\sin^2\theta$, $a + b = r^2$,
$\theta \in (0, \tfrac{\pi}{4})$, and the measure becomes simply $\rho(a,b)\,da\,db = r\,dr\,d\theta$.
For $c \in (0, t_0)$, the corner triangle $T_c = \{0 < b < a,\ a + b < c\} \subseteq S_+$ is the
circular sector $\{0 < r < \sqrt c,\ 0 < \theta < \tfrac{\pi}{4}\}$ of angle $\tfrac{\pi}{4}$.

Symmetry of $u$ and the subgradient inequality give $g_2 \le g_1$ on $\{b < a\}$. Along each fixed
ray $\theta \in (0, \tfrac{\pi}{4})$, the function $\tilde w(r) = w(r^2\cos^2\theta, r^2\sin^2\theta)$
satisfies $\tilde w(0) = 0$, and since $\cos^2\theta > \sin^2\theta$ and $g_1 \ge g_2$, its a.e.
derivative obeys

$$
\tilde w'(r) = r\left[1 - 2(\cos^2\theta\,g_1 + \sin^2\theta\,g_2)\right] \le r\left[1 - (g_1 + g_2)\right] = r\,D.
$$

At $r = \sqrt c$, the endpoint $(c\cos^2\theta, c\sin^2\theta)$ lies on the segment from $(c,0)$ to
$(0,c)$, where concavity and symmetry of $w$ give $w \ge w(c,0)$. Integrating from $0$ to $\sqrt c$
therefore gives the ray inequality

$$
w(c, 0) \;\le\; \int_0^{\sqrt c} D(r^2\cos^2\theta, r^2\sin^2\theta)\,r\,dr \qquad\text{for every }\theta \in (0, \tfrac{\pi}{4}).
$$

Averaging over $\theta \in (0, \tfrac{\pi}{4})$ against any bounded measurable weight $\gamma(\theta) \ge 0$
with $\int_0^{\pi/4}\gamma(\theta)\,d\theta = 1$ yields

$$
w(c, 0) \;\le\; \int_{T_c} D\,\rho\,\gamma(\theta).
$$

This immediately explains why the constant $\frac{2}{\pi}$ governs both Theorems 1 and 2: spreading the
total kernel mass $\int_0^{t_0} K = \tfrac{1}{2}$ uniformly across the angular sector of width $\tfrac{\pi}{4}$
produces height $\frac{1/2}{\pi/4} = \frac{2}{\pi}$, matching the quarter-disk $\{U_1^2 + U_2^2 < 2\varepsilon\}$
of Theorem 2. Two unit-integral angular weights are used:

$$
G_1 = \frac{4\sqrt{ab}}{a+b} = 2\sin(2\theta) \in (0, 2], \qquad G_2 = \frac{8}{\pi} - G_1 > 0,
$$

with $\int_0^{\pi/4} 2\sin(2\theta)\,d\theta = 1$ and $\int_0^{\pi/4}(\frac{8}{\pi} - 2\sin(2\theta))\,d\theta = 1$.
(Lean formalises this equivalently in the rationalised ray coordinates $(\lambda, \eta) = (a, b/a) = (r^2\cos^2\theta, \tan^2\theta)$,
where $d\theta = \frac{d\eta}{2\sqrt\eta(1+\eta)}$ is `arctanWeight` and $G_1 = \frac{4\sqrt\eta}{1+\eta}$
is `gw1`; see `G1`, `integral_gw1_arctanWeight`, `integral_gw2_arctanWeight`.)

**(iv) Smooth convex combination for Term A** (`Jtail`, `WA2`, `lemma5_termA_sharp`). Put
$J(x) = \int_x^{t_0} K(c)\,dc$ for $x \in (0, t_0)$ (and $0$ for $x \ge t_0$), so $J(0^+) = \tfrac{1}{2}$,
$J(t_0) = 0$, $J' = -K < 0$, and $2J(c) \in (0, 1)$. At each radius $c \in (0, t_0)$, apply (iii)
with the smooth convex combination

$$
G(c, \theta) = 2 J(c)\,G_1(\theta) + \left(1 - 2 J(c)\right)\,G_2(\theta).
$$

(Near $c = 0$, $2J(c) \to 1$, choosing $G_1$ to cancel the $\ln(a+b)$ singularity of $\psi/\rho$;
near $c = t_0$, $2J(c) \to 0$, shifting to $G_2$.) Multiply by $K(c) > 0$, integrate over
$c \in (0, t_0)$, and exchange the order of integration. The two exact antiderivatives
$\int_x^{t_0} K(c)\,2 J(c)\,dc = J(x)^2$ (`integral_K_mul_two_Jtail`) and
$\int_x^{t_0} K(c)(1 - 2J(c))\,dc = J(x)(1 - J(x))$
(`integral_K_mul_one_sub_two_Jtail`) yield

$$
\int_0^{t_0} K(c)\,w(c, 0)\,dc \;\le\; \int_{S_+} D\,\rho\,W_A, \qquad W_A(a, b) = J(x)^2 G_1 + J(x)\left(1 - J(x)\right)\left(\frac{8}{\pi} - G_1\right) \qquad (x = a + b).
$$

Writing $h(x) = 1 - 2 J(x) \in (0, 1)$ (so $J = \tfrac{1-h}{2}$), this simplifies algebraically to

$$
\frac{2}{\pi} - W_A = \frac{2}{\pi} h(x)^2 + \frac{1}{2} h(x)\left(1 - h(x)\right) G_1.
$$

**(v) Pointwise inequality** (`sharp_pointwise`, `sharp_key`). For $t \in (0,t_0)$ and $r > 0$,
at the point $(a, b) = (r+t, r)$,

$$
W_A + \frac{\psi_t(r)}{\rho(r+t, r)} \;\le\; \frac{2}{\pi} .
$$

Write $x = a + b$, $z = \sqrt{ab}$, so $\rho = \tfrac{1}{4z}$, $G_1 = \tfrac{4z}{x} \in (0, 2]$ and $2z \le x$.

*Bound on $\psi$* (`four_z_psiB_le`). $g_T(t) - I(r,t) = \tfrac{1}{2}\ln\frac{1 + \sqrt{1-t}}{\sqrt a + \sqrt b}$
and $(\sqrt a + \sqrt b)^2 = x + 2z$. Using $1 + \sqrt{1-t} \le 2$ and $\tfrac{1}{\sqrt{1-t}} \ge 1$,

$$
\frac{\psi}{\rho} \;\le\; 4z\ln 2 - 2z\ln(x + 2z) - z. \tag{*}
$$

*Case $x \ge t_0$* (`arith_case3`). Here $J(x) = 0$, so $W_A = 0$. Since $x + 2z \ge 4z$, $(\ast)$
gives $\tfrac{\psi}{\rho} \le -2z\ln z - z \le 2e^{-3/2} \le \tfrac{1}{2} < \tfrac{2}{\pi}$, by the tangent-line
bound $-z\ln z \le e^{-3/2} + \tfrac{1}{2} z$.

*Case $0 < x < t_0$* (`sharp_key`, `H_sq_le_39_10_mul`). Since $x + 2z = x(1 + G_1/2)$ and the
concave function $\ln$ lies above its chord $\ln(1 + u) \ge \tfrac{2}{3} u$ on $[0, 1]$
(`log_one_add_ge`), $(\ast)$ gives, with $z = G_1 x / 4$,

$$
\frac{\psi}{\rho} \;\le\; G_1\,x\left(\ln 2 - \tfrac{1}{2}\ln x - \tfrac{1}{4}\right) - \tfrac{1}{6} G_1^2\,x.
$$

Put $\sigma = \sqrt{1-x} \in (\tfrac{3}{4}, 1)$ (as $x < t_0 < \tfrac{7}{16}$) and
$q = \tfrac{1}{1+\sigma} \in (\tfrac{1}{2}, \tfrac{4}{7})$. From $J(x) = \tfrac{\sigma}{2} - 2x\,g_T(x)$,
$1 - \sigma = xq$, and $2x\,g_T(x) = x\ln(1+\sigma) - \tfrac{x}{2} \ln x$ (`two_x_gT`),

$$
h(x) = 1 - 2J(x) = x\left(q + 2\ln(1+\sigma)\right) - x\ln x.
$$

The logarithmic singularity cancels identically between $\tfrac{1}{2} h(x)$ and
$x(\ln 2 - \tfrac{1}{2}\ln x - \tfrac{1}{4})$: using $\ln\tfrac{2}{1+\sigma} \le \tfrac{2}{1+\sigma} - 1 = 2q - 1$
and $q < \tfrac{4}{7}$,

$$
\frac{1}{2} h(x) - x\left(\ln 2 - \tfrac{1}{2}\ln x - \tfrac{1}{4}\right) = x\left(\frac{q}{2} + \frac{1}{4} - \ln\frac{2}{1+\sigma}\right) \ge x\left(\frac{5}{4} - \frac{3}{2} q\right) > \frac{11}{28}\,x.
$$

Substituting this and the identity for $\tfrac{2}{\pi} - W_A$ produces the master gap bound

$$
\frac{2}{\pi} - W_A - \frac{\psi}{\rho} \;\ge\; \left(\frac{2}{\pi} - \frac{G_1}{2}\right) h(x)^2 + \frac{11}{28}\,G_1\,x + \frac{1}{6} G_1^2\,x.
$$

Two subcases finish the proof:
- *Subcase $G_1 \le \tfrac{4}{\pi}$:* every term on the right-hand side is non-negative.
- *Subcase $\tfrac{4}{\pi} < G_1 \le 2$:* put $v = \tfrac{1-\sigma}{2} > 0$, so
  $\ln\tfrac{1+\sigma}{2} = \ln(1-v) \le -v$ and $q - \tfrac{1}{2} = \tfrac{v}{1+\sigma} \le 2v$, giving
  $q + 2\ln(1+\sigma) \le \tfrac{1}{2} + 2\ln 2$. Applying $-u\ln u \le e^{-a} + (a-1)u$ to
  $u = \sqrt x$ with $a = \tfrac{3}{4} - \ln 2$ (`neg_mul_log_le`) cancels the linear term and gives
  $0 \le h(x) \le 4 e^{-3/4}\sqrt x$, hence

  $$
  h(x)^2 \;\le\; 16 e^{-3/2} x \;\le\; \frac{39}{10}\,x
  $$

  (`H_sq_le_39_10_mul`, `sixteen_exp_neg_3_2_le`, using $e^3 > 2.7^3 = 19.683 > (\tfrac{160}{39})^2$).
  Since $\tfrac{2}{\pi} - \tfrac{G_1}{2} < 0$, substituting $h(x)^2 \le \tfrac{39}{10}x$ into the master
  bound gives

  $$
  \frac{2}{\pi} - W_A - \frac{\psi}{\rho} \;\ge\; x\left[(2 - G_1)\left(\frac{39}{20} - \frac{11}{28} - \frac{2+G_1}{6}\right) + \left(\frac{39}{5\pi} - \frac{257}{105}\right)\right] \;\ge\; 0,
  $$

  where both summands in brackets are positive ($\tfrac{39}{20} - \tfrac{11}{28} - \tfrac{2}{3} = \tfrac{187}{210} > 0$,
  and $\tfrac{39}{5\pi} - \tfrac{257}{105} \ge \tfrac{273}{110} - \tfrac{257}{105} = \tfrac{79}{2310} > 0$
  using $\pi < \tfrac{22}{7}$).

**Assembly** (`lemma5_diag_bound`, `lemma5_strip_dominance_sym`). By (i), (ii) and (iv), and then
(v) together with $D \ge 0$,

$$
\tfrac{1}{2}(\mathcal{L} - M_1) \;\le\; -L\int_{S_+} D\rho + \int_0^{t_0} \int_0^{1-t} D(r+t,r)\left[\rho\,W_A + \psi_t(r)\right]dr\,dt \;\le\; \left(\frac{2}{\pi} - L\right)\int_{S_+} D\rho \;\le\; 0. \qquad\blacksquare
$$

The threshold $\tfrac{2}{\pi}$ in Lemma 5 cannot be lowered: if the lemma held for some $L < \tfrac{2}{\pi}$,
the argument of §4.6 would make $(g^\star, p^\star)$ optimal there, contradicting Theorem 2.

### 4.6 Proof of Theorem 1 (`Theorem1.lean`)

Parts 1 and 2 are §4.3. For part 3, take any BIC, interim-IR mechanism with ex-post single-item
allocations $q_{i1}(v), q_{i2}(v)$ (§4.1), and apply §4.4 and Lemma 5 to each bidder's interim
profile. Summing and rewriting the interim expectations as a joint expectation via Fubini gives
(writing $\tilde v_i = (v_{i1} - L, v_{i2} - L)$)

$$
\text{revenue} \;\le\; 2M_1 + \mathbb{E}\left[\,\sum_{i=1}^{2} \mathbf{1}[\tilde v_i \in W_+ \cup W_-]\,\left(\tilde\phi_1(\tilde v_i)\,q_{i1}(v) + \tilde\phi_2(\tilde v_i)\,q_{i2}(v)\right)\right]
$$

(`dual_revenue_identity`). For almost every $v$ (specifically whenever both shifted types lie in
$W_+ \cup W_- \cup S$, i.e. $(0,1)^2 \setminus \{\lvert a - b\rvert = t_0\}$), the integrand is at
most its maximum over the matchings of bidders to items. Because every $\tilde\phi_j > L \ge 0$ on
$W_+ \cup W_-$, that maximum is attained by one of the two perfect matchings, and because
$\tilde\phi_1 - \tilde\phi_2 = \bar\Phi(a - b)$ on $W_+ \cup W_-$, the better perfect matching is
the one $(g^\star, p^\star)$ chooses (`pointwise_wing_dominance`). For $(g^\star, p^\star)$ itself
each bidder's interim utility is linear on the strip (`flagship_strip_linear`), so Lemma 5 holds
with equality. Hence the bound equals the revenue of $(g^\star, p^\star)$. $\blacksquare$

### 4.7 Proof of Theorem 2 (`Theorem2.lean`)

Start from the symmetric twin mechanism (`symTwinMechanism`, `Lemma3.lean`): when
$\lvert t_{-i}\rvert > t_0$ it coincides with $(g^\star, p^\star)$, while when
$\lvert t_{-i}\rvert \le t_0$ bidder $i$ faces the three-option menu
$\{(\tfrac{1}{2}, \tfrac{1}{2};\, L),\ (1, 0;\, L + \tfrac{t_0}{2}),\ (0, 1;\, L + \tfrac{t_0}{2})\}$.
This mechanism is feasible, DSIC and ex-post IR, and has the same expected revenue as
$(g^\star, p^\star)$ (`symTwinMechanism_expectedRevenue`). Fix $0 < \varepsilon < \tfrac{t_0}{2}$.
When $\lvert t_2\rvert \le t_0$, raise every price on bidder 1's menu by $\varepsilon$ and add the
outside option $(0, 0;\, 0)$, leaving bidder 2 untouched. Because $a_1, b_1 \ge 0$ and
$\varepsilon < \tfrac{t_0}{2}$, whenever $a_1 + b_1 < 2\varepsilon$ we have
$\max(a_1, b_1) < 2\varepsilon < \tfrac{t_0}{2} + \varepsilon$ and $\lvert t_1\rvert < t_0$, so
bidder 1 walks away (previously paying $L$) **if and only if** $a_1 + b_1 < 2\varepsilon$; otherwise
she pays $\varepsilon$ more. In the uniform coordinates $(U_{11}, U_{12}) \in [0,1]^2$, the event
$\{a_1 + b_1 < 2\varepsilon\}$ is the quarter-disk $\{U_{11}^2 + U_{12}^2 < 2\varepsilon\}$ of
probability $\tfrac{\pi}{4}(2\varepsilon) = \tfrac{\pi}{2}\varepsilon$ (`prob_corner_triangle`).
The change in revenue is therefore

$$
\Pr\left(\lvert t_2\rvert \le t_0\right)\cdot\varepsilon\,\left(1 - \frac{\pi}{2}(L + \varepsilon)\right),
$$

which is strictly positive for $0 < \varepsilon < \min(\tfrac{t_0}{2}, \tfrac{2}{\pi} - L)$
whenever $0 \le L < 2/\pi$. The perturbed mechanism is feasible, DSIC, ex-post IR, single-item, and
has non-negative payments (`perturbedSymMechanism_*`, `perturbedSymMechanism_nonNeg_singleItem`,
`flagshipMechanism_suboptimal_below_two_div_pi`). Starting from `symTwinMechanism` rather than
$(g^\star, p^\star)$ directly is essential: under $(g^\star, p^\star)$, when $\lvert t_2\rvert \le t_0$
item 2 costs $L$ while item 1 costs $L + t_0 > L$, so raising both menu prices by $\varepsilon$ (the
minimal shift preserving feasibility and DSIC) causes bidder 1 to walk away whenever
$b_1 < \varepsilon$ and $a_1 < t_0 + \varepsilon$, an event of probability
$\sqrt\varepsilon\sqrt{t_0 + \varepsilon} = \Theta(\sqrt\varepsilon) \gg \varepsilon$; the symmetric
50/50 lottery priced at $L$ equalises the two coordinates so exclusion occurs only in the quarter-disk
$\{a_1 + b_1 < 2\varepsilon\}$ of probability $\tfrac{\pi}{2}\varepsilon$. $\blacksquare$

## 5. Checking the proof

```bash
cd optimal-dsic/lean
./replay.sh        # lake exe cache get; lake build; statement + axiom check; kernel replay
```

`replay.sh` regenerates [`lean/logs/`](lean/logs/):

- `cleanroom_audit.log`: deterministic SHA-256 manifest of all 14 `.lean` files followed by the
  output of [`lean/CleanRoomAudit.lean`](lean/CleanRoomAudit.lean), which re-states the theorems
  above against `Spec.lean`, proves sanity facts about the specification (the measure has total mass
  one, the CDF is $\sqrt{v-L}$, a constant-payment mechanism has the expected revenue), `#check`s
  the top-level theorem types, and prints the axioms each top-level theorem depends on. Each entry
  must list only `[propext, Classical.choice, Quot.sound]`.
- `leanchecker.log`: an independent kernel replay (`leanchecker`) of all 12 declaration-bearing
  library modules and of `CleanRoomAudit` (skipping the 0-declaration root import barrel
  `EconCSAuction.lean`, which `CleanRoomAudit` imports). Each line must read `PASS`. (Cached
  Mathlib `.olean`s are used; full `--fresh` kernel replay of Mathlib is not run by default.)

To trust Theorems 1, 2 and 3, one needs to read `Spec.lean` (plus the statement of
`flagshipMechanism_suboptimal_below_two_div_pi` in `Theorem2.lean` / `cleanroom_audit.log` for the
`NonNegPayment ∧ IsSingleItem` clauses on Theorem 2's witness) and trust the Lean kernel and
Mathlib. Nothing else in this repository needs to be trusted.

## 6. Context

The EconCS-Bench problem
[*Revenue Optimal DSIC Auction*](https://github.com/aieconcs/econcs-bench/blob/main/revenue-optimal-dsic-auction/PROBLEM.md)
(Jiang, Parkes and Wang, 2026) asks, as its characterisation goal, for an explicit revenue-optimal DSIC
and IR auction for some continuous product distribution with more than one bidder and more than one
item. Theorem 1 gives one for the distribution of §1. It does not address the problem's
computational goal (learning such an auction), and, as Remark 3 explains, it says nothing about
bounded densities.

That problem statement describes the multi-bidder, multi-item continuous case as open and records
the discrete two-point result of Liu, Liu and Wang
([arXiv:2610.11051](https://arxiv.org/abs/2610.11051)) as partial progress. We are not aware of an
earlier closed-form optimum in the continuous case, but we have not carried out an exhaustive
literature search and make no priority claim beyond that.

## References

- Jiang, Y., Parkes, D. C., and Wang, T. (2026). Duality for optimal multi-item, multi-bidder auction design: revenue certificates through deep learning. [arXiv:2606.10112](https://arxiv.org/abs/2606.10112).
- Liu, B., Liu, Z., and Wang, Z. (2026). Optimal multi-item auctions with i.i.d. values. [arXiv:2610.11051](https://arxiv.org/abs/2610.11051).
- Myerson, R. B. (1981). Optimal auction design. *Mathematics of Operations Research* 6(1), 58–73.
- Rochet, J.-C. (1987). A necessary and sufficient condition for rationalizability in a quasi-linear context. *Journal of Mathematical Economics* 16(2), 191–200.
