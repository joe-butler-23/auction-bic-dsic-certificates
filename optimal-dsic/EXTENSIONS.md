# Extensions that are not formalised

**Status.** Nothing in this file has been checked in Lean. The results below extend
[`PAPER.md`](PAPER.md) from the exponent $\tfrac{1}{2}$ to every exponent $\alpha \in (0, \tfrac{1}{2})$, by
the same method. The proofs are pen-and-paper arguments. Lemmas E2, E4 and E5 have been read
independently by two reviewers; Lemma E3 and the proof of Proposition E2 were rewritten in this
revision and have had a single reading. A reader who wants machine-checked certainty should rely
only on `PAPER.md`.
[`check_extensions.py`](check_extensions.py) checks the algebraic identities symbolically and
compares the closed forms with direct quadrature; that is evidence against transcription errors,
not a proof.

For $\alpha = \tfrac{1}{2}$ the Lean theorem (`PAPER.md`, Theorems 1–3, exact threshold $L \ge 2/\pi$) is stronger than
anything here, and this file makes no separate claim about that case.

---

## 1. Setting

Two unit-demand bidders, two items, as in `PAPER.md` §1, but with
$v_{ij} \stackrel{\text{i.i.d.}}{\sim} L + \mathrm{Beta}(\alpha, 1)$ on $[L, L+1]$, i.e. CDF
$F(v) = (v - L)^\alpha$, for a fixed $\alpha \in (0, \tfrac{1}{2}]$.

For any $\alpha \in (0, \tfrac{1}{2}]$, consider normalized shifted types $(a, b) \in [0, 1]^2$ with density $\rho_\alpha(a, b) = \alpha^2 a^{\alpha - 1} b^{\alpha - 1}$ and difference $t := a - b \in [-1, 1]$. For $t \in (0, 1)$, the density and survival function of $t$ are

$$
g_{T,\alpha}(t) := \int_0^{1-t} \rho_\alpha(s + t, s)\,ds = \alpha^2 t^{2\alpha - 1}\int_0^{(1-t)/t} u^{\alpha - 1}(1 + u)^{\alpha - 1}\,du, \qquad 1 - G_{T,\alpha}(t) = \frac{(1 - t)^\alpha}{2} - \frac{t}{2\alpha}\,g_{T,\alpha}(t).
$$

Define the one-sided virtual difference on $(0, 1)$ by

$$
\Phi_{+,\alpha}(t) := t - \frac{1 - G_{T,\alpha}(t)}{g_{T,\alpha}(t)} = \left(1 + \frac{1}{2\alpha}\right) t - \frac{(1 - t)^\alpha}{2\,g_{T,\alpha}(t)},
$$

the odd extension $\Phi_\alpha(t) := \mathrm{sgn}(t)\,\Phi_{+,\alpha}(|t|)$, and
$K_\alpha(t) := (1 + 2\alpha)\,g_{T,\alpha}(t) - \alpha^2 (1-t)^{\alpha-1}$. By Lemma E2,
$\Phi_{+,\alpha}$ has a unique root $t_0(\alpha) \in (0,1)$ and is strictly increasing on
$[t_0(\alpha), 1)$. The ironed virtual difference $\bar\Phi_\alpha$ equals $\Phi_\alpha$ where
$|t| > t_0(\alpha)$ and $0$ on $[-t_0(\alpha), t_0(\alpha)]$.

**Mechanism.** $(g^\star_\alpha, p^\star_\alpha)$ is the mechanism of `PAPER.md` §2 with $t_0$
replaced by $t_0(\alpha)$. Nothing else changes: the menu table is identical.

## 2. Results

Define, for $\alpha \in (0, \tfrac{1}{2})$,

$$
J^\star(\alpha) := \frac{\Gamma(\alpha+1)^2}{\Gamma(2\alpha+1)}, \qquad C_A^\star(\alpha) := \frac{1}{J^\star(\alpha)}\int_0^{t_0(\alpha)} t^{1-2\alpha} K_\alpha(t)\,dt, \qquad B_{\mathrm{elem}}(\alpha) := \frac{1+2\alpha}{2(1-\alpha)}\left(\frac{1+2\alpha}{4(1-\alpha)}\right)^{\frac{1}{1-2\alpha}},
$$

and $L_0(\alpha) := C_A^\star(\alpha) + B_{\mathrm{elem}}(\alpha)$.

> **Theorem E1 (not formalised).** Let $\alpha \in (0, \tfrac{1}{2})$ and $L \ge L_0(\alpha)$. Then
> $(g^\star_\alpha, p^\star_\alpha)$ is feasible, DSIC and ex-post IR with payments in $[L, L+1]$,
> and its revenue
>
> $$
> 2L + \mathbb{E}\left[\left(\bar\Phi_\alpha(t_1) - \bar\Phi_\alpha(t_2)\right)_+\right]
> $$
>
> is at least that of every feasible BIC, interim-IR mechanism.

> **Proposition E2 (not formalised).** Let $\alpha > \tfrac{1}{2}$ and $L > 0$ (this includes the
> uniform distribution, $\alpha = 1$). For every BIC, interim-IR mechanism that gives each bidder
> exactly one item almost surely, there is a BIC, interim-IR mechanism with strictly larger revenue.

Proposition E2 is a statement about BIC mechanisms only. Whether a *DSIC* improvement always
exists for $\alpha > \tfrac{1}{2}$ is not settled here.

Values of the constants, as printed by `check_extensions.py` (numerical evaluations, for orientation):

| $\alpha$ | $t_0(\alpha)$ | $J^\star(\alpha)$ | $C_A^\star(\alpha)$ | $B_{\mathrm{elem}}(\alpha)$ | $L_0(\alpha)$ |
|:---:|:---:|:---:|:---:|:---:|:---:|
| 0.40 | 0.370321 | 0.845234 | 0.366659 | 0.355957 | 0.722616 |
| 0.25 | 0.374466 | 0.927037 | 0.153059 | 0.250000 | 0.403059 |
| 0.20 | 0.374835 | 0.950150 | 0.109081 | 0.220617 | 0.329698 |
| 0.10 | 0.373393 | 0.985732 | 0.044270 | 0.168852 | 0.213123 |
| 0.05 | 0.371256 | 0.996174 | 0.020130 | 0.146025 | 0.166155 |
| 0.01 | 0.368668 | 0.999838 | 0.003745 | 0.129068 | 0.132812 |

The threshold $L_0(\alpha)$ is what this argument gives; it is not claimed to be sharp. In
particular $L_0(\alpha) \to \tfrac{2}{\pi} + 2e^{-3/2} \approx 1.083$ as $\alpha \uparrow \tfrac{1}{2}$,
which is weaker than the Lean-checked exact threshold $\tfrac{2}{\pi} \approx 0.637$ at $\alpha = \tfrac{1}{2}$.

## 3. Proof of Theorem E1

Write $(a, b) := (v_{i1} - L, v_{i2} - L) \in [0,1]^2$, with density
$\rho_\alpha(a,b) = \alpha^2 a^{\alpha-1} b^{\alpha-1}$, and $t := a - b$.

### Lemma E1 (one item per bidder)

Any feasible BIC, interim-IR mechanism can be replaced, without changing revenue, by one that never
allocates the bundle $\{1,2\}$: give the bidder only the item she reported as more valuable. This
argument does not depend on the distribution; for $\alpha = \tfrac{1}{2}$ it is `Lemma1.lean`.

### Lemma E2 (the law of the difference)
*For every $\alpha \in (0, \tfrac{1}{2}]$:*
1. *$t\,g_{T,\alpha}'(t) = (2\alpha - 1) g_{T,\alpha}(t) - \alpha^2(1 - t)^{\alpha - 1} < 0$ and $1 - G_{T,\alpha}(t) = \frac{(1 - t)^\alpha}{2} - \frac{t}{2\alpha} g_{T,\alpha}(t)$ for all $t \in (0, 1)$.*
2. *$F_{0,\alpha}(t) := g_{T,\alpha}(t)\Phi_{+,\alpha}(t)$ satisfies $F_{0,\alpha}'(t) = K_\alpha(t)$ and $K_\alpha'(t) < 0$ strictly on $(0, 1)$. Consequently, $\Phi_{+,\alpha}$ has a unique root $t_0(\alpha) \in (0, 1)$ (with $\Phi_{+,\alpha} < 0$ on $(0, t_0(\alpha))$ and $\Phi_{+,\alpha} > 0$ on $(t_0(\alpha), 1)$), $K_\alpha(t) > K_\alpha(t_0(\alpha)) > 0$ strictly on $(0, t_0(\alpha)]$, and $\int_0^{t_0(\alpha)} K_\alpha(t)\,dt = \frac{1}{2}$. At $\alpha = \tfrac{1}{2}$, $t_0(\tfrac{1}{2}) \in (\frac{9}{25}, \frac{7}{16})$.*
3. *$\Phi_{+,\alpha}'(t) > 0$ strictly on $[t_0(\alpha), 1)$, and $\lim_{t \uparrow 1}\Phi_{+,\alpha}(t) = 1$.*

**Proof.**
1. Substituting $s = t u$ into $g_{T,\alpha}(t) = \alpha^2 \int_0^{1-t} s^{\alpha-1}(s+t)^{\alpha-1}\,ds$ gives $g_{T,\alpha}(t) = \alpha^2 t^{2\alpha - 1}\int_0^{(1-t)/t} u^{\alpha - 1}(1+u)^{\alpha - 1}\,du$. Differentiating with respect to $t$ (using $\frac{d}{dt}((1-t)/t) = -1/t^2$) yields

   $$
   t\,g_{T,\alpha}'(t) = (2\alpha - 1) g_{T,\alpha}(t) - \alpha^2 (1 - t)^{\alpha - 1} = (2\alpha - 1) g_{T,\alpha}(t) - \rho_\alpha(1, 1 - t) < 0,
   $$

   as $2\alpha - 1 \le 0$. Integrating $x g_{T,\alpha}'(x)$ by parts over $[t, 1]$ (where $x g_{T,\alpha}(x) \to 0$ as $x \uparrow 1$ since $g_{T,\alpha}(x) \sim \alpha(1-x)^\alpha$) yields $-t g_{T,\alpha}(t) - (1 - G_{T,\alpha}(t)) = (2\alpha - 1)(1 - G_{T,\alpha}(t)) - \alpha(1-t)^\alpha$, hence $1 - G_{T,\alpha}(t) = \frac{(1-t)^\alpha}{2} - \frac{t}{2\alpha} g_{T,\alpha}(t)$.
2. Differentiating $F_{0,\alpha}(t) = t g_{T,\alpha}(t) - (1 - G_{T,\alpha}(t))$ via (1) gives $F_{0,\alpha}'(t) = 2 g_{T,\alpha}(t) + t g_{T,\alpha}'(t) = (1 + 2\alpha) g_{T,\alpha}(t) - \alpha^2 (1 - t)^{\alpha - 1} = K_\alpha(t)$, and differentiating again gives

   $$
   K_\alpha'(t) = (1 + 2\alpha) g_{T,\alpha}'(t) + \alpha^2 (\alpha - 1)(1 - t)^{\alpha - 2} < 0 \qquad \forall t \in (0, 1),
   $$

   since $g_{T,\alpha}'(t) < 0$ and $\alpha < 1$. Thus $F_{0,\alpha}$ is strictly concave on $(0, 1)$. As $t \downarrow 0$, $t g_{T,\alpha}(t) = O(t^{2\alpha})$ (or $O(t\ln(1/t))$ at $\alpha = \tfrac{1}{2}$) $\to 0$ and $1 - G_{T,\alpha}(0^+) = \frac{1}{2}$, so $F_{0,\alpha}(0^+) = -\frac{1}{2} < 0$ and $K_\alpha(0^+) = +\infty$; as $t \uparrow 1$, $F_{0,\alpha}(1^-) = 0$ and $K_\alpha(1^-) = -\infty$, so $F_{0,\alpha} > 0$ near $1^-$. By strict concavity, $F_{0,\alpha}$ rises strictly from $-\frac{1}{2}$ to a unique positive maximum at the unique root $t_{\max}$ of $K_\alpha(t_{\max}) = 0$, then falls strictly to $0$ at $1$. Therefore $\Phi_{+,\alpha} = F_{0,\alpha}/g_{T,\alpha}$ has a unique root $t_0(\alpha) \in (0, t_{\max})$, $K_\alpha(t) > K_\alpha(t_0(\alpha)) > 0$ on $(0, t_0(\alpha)]$, and $\int_0^{t_0(\alpha)} K_\alpha(t)\,dt = F_{0,\alpha}(t_0(\alpha)) - F_{0,\alpha}(0^+) = \frac{1}{2}$. For $\alpha = \tfrac{1}{2}$, putting $s = \sqrt{1-t}$, $\psi(s) := 2(1-s^2)\mathrm{artanh}(s) - s$ satisfies $\psi(\frac{3}{4}) = \frac{7}{16}\ln 7 - \frac{3}{4} > 0$ (since $7^7 = 823543 > e^{12}$) and $\psi(\frac{4}{5}) = \frac{18}{25}\ln 3 - \frac{4}{5} < 0$ (since $3^9 = 19683 < e^{10}$), giving $s_0 \in (\frac{3}{4}, \frac{4}{5})$ and $t_0(\tfrac{1}{2}) = 1 - s_0^2 \in (\frac{9}{25}, \frac{7}{16})$.
3. Put $u(t) := \frac{(1-t)^\alpha}{2 g_{T,\alpha}(t)} > 0$. By (1), $\Phi_{+,\alpha}(t) = \frac{1+2\alpha}{2\alpha} t - u(t)$. Differentiating $\ln u(t)$ via (1) gives $t u'(t) = (1 - 2\alpha) u - \frac{\alpha t}{1-t} u + \frac{2\alpha^2}{1-t} u^2$, so $t\,\Phi_{+,\alpha}'(t) = P(u(t))$, where

   $$
   P(u) := \frac{1 + 2\alpha}{2\alpha} t - (1 - 2\alpha) u + \frac{\alpha t}{1 - t} u - \frac{2\alpha^2}{1 - t} u^2
   $$

   is strictly concave in $u$. On $[t_0(\alpha), 1)$, $\Phi_{+,\alpha}(t) \ge 0$ gives $u(t) \le \frac{1+2\alpha}{2\alpha} t$; simultaneously, $(s+t)^{\alpha-1} > 1$ on $s \in (0, 1-t)$ gives $g_{T,\alpha}(t) > \alpha^2 \int_0^{1-t} s^{\alpha-1}\,ds = \alpha(1-t)^\alpha$, hence $u(t) < \frac{1}{2\alpha}$ on $(0, 1)$. Evaluating $P$:

   $$
   P(0) = \frac{1 + 2\alpha}{2\alpha} t > 0, \qquad P\left(\frac{1 + 2\alpha}{2\alpha} t\right) = (1 + 2\alpha) t\,\frac{1 - (1 + \alpha) t}{1 - t}, \qquad P\left(\frac{1}{2\alpha}\right) = \frac{(1 + 2\alpha) t - (1 - \alpha)}{2\alpha}.
   $$

   Since $\frac{1}{1+\alpha} - \frac{1-\alpha}{1+2\alpha} = \frac{\alpha(\alpha+2)}{(1+\alpha)(1+2\alpha)} > 0$, every $t \in [t_0(\alpha), 1)$ satisfies either $t < \frac{1}{1+\alpha}$ (where $P(\frac{1+2\alpha}{2\alpha} t) > 0$) or $t > \frac{1-\alpha}{1+2\alpha}$ (where $P(\frac{1}{2\alpha}) > 0$). Concavity of $P$ forces $P(u(t)) > 0$, hence $\Phi_{+,\alpha}'(t) > 0$ on $[t_0(\alpha), 1)$. Finally, as $t \uparrow 1$, $g_{T,\alpha}(t) \sim \alpha(1-t)^\alpha$ and $1 - G_{T,\alpha}(t) \sim \frac{\alpha}{\alpha+1}(1-t)^{\alpha+1}$, so $\Phi_{+,\alpha}(t) = t - \frac{1-t}{\alpha+1}(1 + o(1)) \to 1$. $\square$

### Lemma E3 (properties of the mechanism)

*For every $\alpha \in (0, \tfrac{1}{2}]$ and $L \ge 0$, $(g^\star_\alpha, p^\star_\alpha)$ is feasible,
DSIC, ex-post IR, has payments in $[L, L+1]$, and has revenue
$2L + \mathbb{E}[(\bar\Phi_\alpha(t_1) - \bar\Phi_\alpha(t_2))_+]$.*

**Proof.** Each bidder's menu depends only on the other's report and she receives a
utility-maximising option, so truthful reporting is dominant. The cheaper option costs
$L \le \min(v_{i1}, v_{i2})$, so truthful utility is non-negative, and all prices lie in $[L, L+1]$
because $t_0(\alpha) \le \max(t_0(\alpha), |t|) \le 1$.

*Feasibility.* Write $t_0 = t_0(\alpha)$. Reading off the menu, bidder 1 takes item 1 iff
$t_1 > \max(t_0, t_2)$ when $t_2 \ge -t_0$, and iff $t_1 > t_2$ when $t_2 < -t_0$. Bidder 2 takes
item 1 iff $t_2 \ge -\max(t_0, -t_1)$ when $t_1 \le t_0$, and iff $t_2 \ge t_1$ when $t_1 > t_0$. These
two events are complementary for all real $t_1, t_2$, by cases:
- $t_1 > t_0$: bidder 2 takes item 1 iff $t_2 \ge t_1$. If $t_2 \ge -t_0$, bidder 1 takes item 1 iff
  $t_1 > \max(t_0, t_2)$, i.e. iff $t_1 > t_2$. If $t_2 < -t_0$, bidder 1 takes item 1 (as
  $t_1 > t_0 > t_2$) and bidder 2 does not.
- $t_1 \le t_0$ and $t_2 \ge -t_0$: bidder 1 does not take item 1, and bidder 2 does, since
  $-\max(t_0, -t_1) \le -t_0 \le t_2$.
- $-t_0 \le t_1 \le t_0$ and $t_2 < -t_0$: bidder 1 takes item 1 (as $t_1 \ge -t_0 > t_2$); bidder 2
  would need $t_2 \ge -t_0$ and does not.
- $t_1 < -t_0$ and $t_2 < -t_0$: bidder 1 takes item 1 iff $t_1 > t_2$, bidder 2 iff $t_2 \ge t_1$.

So at every profile exactly one bidder takes item 1 and the other takes item 2. This uses only the
thresholds, not $\Phi_{+,\alpha}$ (compare `b2_decision_iff_not_b1` in `Lemma3.lean`).

*Revenue.* Let $q^\star(t_1, t_2)$ be the indicator that bidder 1 takes item 1. For $|t_1|, |t_2| < 1$,
strict monotonicity of $\Phi_{+,\alpha}$ on $[t_0, 1)$ (Lemma E2(3)) gives
$q^\star = \mathbf{1}[\bar\Phi_\alpha(t_1) > \bar\Phi_\alpha(t_2)]$; the excluded set has probability
zero. Integrating $p_1 = L + t_1 q^\star - \int_0^{t_1} q^\star(s, t_2)\,ds$ by parts in $t_1$ (and
symmetrically for $p_2$) gives
$\mathbb{E}[p_1 + p_2] = 2L + \mathbb{E}[(\Phi_\alpha(t_1) - \Phi_\alpha(t_2))\,q^\star]$. Replacing
$\Phi_\alpha$ by $\bar\Phi_\alpha$ in both arguments changes nothing, because $q^\star(\cdot, t_2)$ and
$q^\star(t_1, \cdot)$ are each constant on $[-t_0, t_0]$ and
$\int_{-t_0}^{t_0} \Phi_\alpha\,g_{T,\alpha} = 0$ by oddness. $\square$

### Lemma E4 (duality on the wings)
*Fix $\alpha \in (0, \tfrac{1}{2}]$ and $L \ge 0$. Partition $[0, 1]^2$ into the ironed strip $S := \{(a, b) \in [0, 1]^2 : |a - b| \le t_0(\alpha)\}$ and the wings $W_+ := \{a - b > t_0(\alpha)\}$, $W_- := \{b - a > t_0(\alpha)\}$. On $W_+$, parameterize $(a, b) = (s + t, s)$ with $t \in (t_0(\alpha), 1)$, $s \in (0, 1 - t]$, let $H_\alpha(t) := \frac{1 - G_{T,\alpha}(t)}{g_{T,\alpha}(t)} = t - \Phi_{+,\alpha}(t)$ and $I_\alpha(s, t) := \int_0^s \rho_\alpha(r + t, r)\,dr$, and define*

$$
z_2^{\mathrm{wing}}(s + t, s) := -I_\alpha(s, t) - \frac{\partial}{\partial t}\left(H_\alpha(t)\,I_\alpha(s, t)\right), \qquad z_1^{\mathrm{wing}}(s + t, s) := z_2^{\mathrm{wing}}(s + t, s) + \rho_\alpha(s + t, s)\,H_\alpha(t),
$$

*and symmetrically on $W_-$ by swapping $(a, b)$ and $(z_1, z_2)$. Set $\tilde{\phi}_1^{\mathrm{wing}} := L + a - z_1^{\mathrm{wing}}/\rho_\alpha$ and $\tilde{\phi}_2^{\mathrm{wing}} := L + b - z_2^{\mathrm{wing}}/\rho_\alpha$. Then:*
1. *$\nabla \cdot z^{\mathrm{wing}} = -\rho_\alpha$ identically on $W_+ \cup W_-$, with $z_1^{\mathrm{wing}}(1, 1-t) = 0$, $z_2^{\mathrm{wing}}(t, 0^+) = 0$ on $W_+$, and $(z_1^{\mathrm{wing}} - z_2^{\mathrm{wing}})(t_0 + s, s) = t_0 \rho_\alpha(t_0 + s, s)$ on $\partial_+ S$.*
2. *$\tilde{\phi}_1^{\mathrm{wing}}(a, b) - \tilde{\phi}_2^{\mathrm{wing}}(a, b) = \bar{\Phi}_\alpha(a - b)$ everywhere on $W_+ \cup W_-$.*
3. *Exact closed-form wing cancellation:*

   $$
   z_2^{\mathrm{wing}}(s + t, s) \;=\; \frac{H_\alpha(t)}{t}\left[s\,\rho_\alpha(s + t, s) \;-\; \frac{\rho_\alpha(1, 1 - t)}{g_{T,\alpha}(t)}\,I_\alpha(s, t)\right].
   $$

   *Consequently, $z_2^{\mathrm{wing}}/\rho_\alpha < \frac{H_\alpha(t)}{t} s < b$ everywhere on $W_+$, so $\tilde{\phi}_1^{\mathrm{wing}} > \tilde{\phi}_2^{\mathrm{wing}} > L \ge 0$ ($M_{\mathrm{wing}}(\alpha) := \sup_{W_+} (z_2^{\mathrm{wing}}/\rho_\alpha - b)_+ \equiv 0$) for every $\alpha \in (0, \tfrac{1}{2}]$.*
4. *For every convex $u : [0, 1]^2 \to \mathbb{R}_{\ge 0}$ with $\nabla u = (g_1, g_2) \ge 0$ and $g_1 + g_2 \le 1$ a.e.,*

   $$
   \int_{[0, 1]^2} \left((L + a)g_1 + (L + b)g_2 - u\right)\rho_\alpha\,da\,db \;=\; \int_{W_+ \cup W_-} \left(\tilde{\phi}_1^{\mathrm{wing}} g_1 + \tilde{\phi}_2^{\mathrm{wing}} g_2\right)\rho_\alpha\,da\,db \;+\; \mathcal{L}_\alpha(u\vert_S),
   $$

   *where*

   $$
   \mathcal{L}_\alpha(u) \;:=\; \int_S \left((L + a)\partial_a u + (L + b)\partial_b u - u\right)\rho_\alpha\,da\,db \;-\; \int_0^{1-t_0(\alpha)} \left(u(t_0 + s, s) + u(s, t_0 + s)\right)\,t_0 \rho_\alpha(t_0 + s, s)\,ds.
   $$

**Proof.**
1. Since $a = s + t, b = s$, $\partial_a = \partial_t$ and $\partial_b = \partial_s - \partial_t$, so $\partial_a z_1^{\mathrm{wing}} + \partial_b z_2^{\mathrm{wing}} = \partial_s z_2^{\mathrm{wing}} + \partial_t(z_1^{\mathrm{wing}} - z_2^{\mathrm{wing}}) = -\partial_s I_\alpha - \partial_t(H_\alpha \partial_s I_\alpha) + \partial_t(H_\alpha \rho_\alpha) = -\rho_\alpha$. At $s = 0$, $I_\alpha(0, t) = 0 \implies z_2^{\mathrm{wing}}(t, 0^+) = 0$. At $s = 1 - t$, using $I_\alpha(1 - t, t) = g_{T,\alpha}(t)$ and $\frac{d}{dt}(H_\alpha g_{T,\alpha}) = -g_{T,\alpha}$, the chain rule yields $\left.\partial_t(H_\alpha I_\alpha)\right|_{s=1-t} = -g_{T,\alpha}(t) + H_\alpha(t)\rho_\alpha(1, 1-t)$, giving $z_2^{\mathrm{wing}}(1, 1-t) = -H_\alpha(t)\rho_\alpha(1, 1-t)$ and $z_1^{\mathrm{wing}}(1, 1-t) \equiv 0$. At $t = t_0(\alpha)$, $H_\alpha(t_0) = t_0 - \Phi_{+,\alpha}(t_0) = t_0$.
2. Immediate: $\tilde{\phi}_1^{\mathrm{wing}} - \tilde{\phi}_2^{\mathrm{wing}} = t - H_\alpha(t) = \Phi_{+,\alpha}(t)$ on $W_+$ and $-\Phi_{+,\alpha}(b - a)$ on $W_-$.
3. Substituting $r = t u$ into $I_\alpha(s, t) = \alpha^2 t^{2\alpha - 1}\int_0^{s/t} u^{\alpha - 1}(1+u)^{\alpha - 1}\,du$ and differentiating with respect to $t$ gives $\partial_t I_\alpha(s, t) = \frac{2\alpha - 1}{t} I_\alpha(s, t) - \frac{s}{t}\rho_\alpha(s+t, s)$. Since $1 + H_\alpha'(t) = -H_\alpha(t) g_{T,\alpha}'(t)/g_{T,\alpha}(t)$, substituting Lemma E2(1) yields $1 + H_\alpha'(t) + \frac{2\alpha - 1}{t} H_\alpha(t) = \frac{H_\alpha(t)}{t}\frac{\rho_\alpha(1, 1-t)}{g_{T,\alpha}(t)}$. Expanding $z_2^{\mathrm{wing}} = -(1 + H_\alpha'(t))I_\alpha - H_\alpha \partial_t I_\alpha$ gives the exact closed form. Because the second bracketed term is strictly negative and $\Phi_{+,\alpha}(t) = t - H_\alpha(t) > 0 \implies H_\alpha(t)/t < 1$ on $W_+$, we get $z_2^{\mathrm{wing}}/\rho_\alpha < \frac{H_\alpha(t)}{t} s < s = b$, hence $\tilde{\phi}_1^{\mathrm{wing}} > \tilde{\phi}_2^{\mathrm{wing}} > L \ge 0$. *(Note: for $\alpha \le 0.30$, $z_2^{\mathrm{wing}}$ itself attains small positive values near $s = 0$, so this exact cancellation identity is strictly stronger than sign negativity of $z_2^{\mathrm{wing}}$ and essential for $\alpha < \tfrac{1}{2}$.)*
4. First note integrability for all $\alpha \in (0, \tfrac{1}{2}]$: since $H_\alpha(t) \sim \frac{1-t}{\alpha+1}$ as $t \uparrow 1$ and $0 \le I_\alpha(s, t) \le g_{T,\alpha}(t)$, the closed form in (3) yields

   $$
   |z_2^{\mathrm{wing}}(s+t, s)| \;\le\; \frac{H_\alpha(t)}{t}\left(s\,\rho_\alpha(s+t, s) + \rho_\alpha(1, 1-t)\right) \;=\; O\left((1-t)^\alpha\right) \;\in\; L^\infty(W_+),
   $$

   vanishing continuously at $(1, 0)$ and at rate $O_\varepsilon(\delta^\alpha)$ along $s = \delta$ for fixed $\varepsilon > 0$; meanwhile $z_1^{\mathrm{wing}} = z_2^{\mathrm{wing}} + H_\alpha \rho_\alpha \in L^1(W_+)$ since $\int_{t_0}^1 H_\alpha(t) g_{T,\alpha}(t)\,dt = \int_{t_0}^1 (1 - G_{T,\alpha}(t))\,dt < \infty$. For any $0 < \delta < \varepsilon < 1 - t_0(\alpha)$, on the Lipschitz trapezoid $W_+^{\delta,\varepsilon} := \{(s+t, s) : t \in [t_0, 1-\varepsilon],\; s \in [\delta, 1-t]\}$, $z^{\mathrm{wing}} \in C^\infty(\overline{W_+^{\delta,\varepsilon}})$ and $u$ is 1-Lipschitz ($W^{1,\infty}$), so $u z^{\mathrm{wing}} \in W^{1,\infty}(W_+^{\delta,\varepsilon}; \mathbb{R}^2)$ satisfies Gauss–Green exactly: $\int_{W_+^{\delta,\varepsilon}} (\nabla u \cdot z^{\mathrm{wing}} - u \rho_\alpha) = \int_{\partial W_+^{\delta,\varepsilon}} u (z^{\mathrm{wing}} \cdot \hat{n})\,dS$. On $a = 1$, $z_1^{\mathrm{wing}} \equiv 0$; on $s = \delta$, $\int_{t_0}^{1-\varepsilon} |u z_2^{\mathrm{wing}}|\,dt \le \|u\|_\infty O_\varepsilon(\delta^\alpha) \to 0$ as $\delta \downarrow 0$ (holding $\varepsilon$ fixed); then on $t = 1 - \varepsilon$, $\int_0^\varepsilon |u(z_1^{\mathrm{wing}} - z_2^{\mathrm{wing}})|\,ds \le \|u\|_\infty H_\alpha(1-\varepsilon) g_{T,\alpha}(1-\varepsilon) = \|u\|_\infty (1 - G_{T,\alpha}(1-\varepsilon)) \to 0$ as $\varepsilon \downarrow 0$. Passing $\delta \downarrow 0$ first and then $\varepsilon \downarrow 0$ via Dominated Convergence (and symmetrically on $W_-$) gives the exact identity. $\square$

### Lemma E5 (strip dominance)
*Fix $\alpha \in (0, \tfrac{1}{2})$, let $u^\star(a, b) := \frac{1}{2}(a + b)$ on $S$, and $M_1 := \mathcal{L}_\alpha(u^\star) = L\int_S \rho_\alpha - t_0(\alpha)\int_0^{1-t_0(\alpha)}(2s+t_0(\alpha))\rho_\alpha(t_0(\alpha)+s, s)\,ds$. For **every** $L \ge L_0(\alpha)$ and **every** convex $u : S \to \mathbb{R}_{\ge 0}$ with $\partial_a u, \partial_b u \ge 0$ and $\partial_a u + \partial_b u \le 1$ a.e.,*

$$
\mathcal{L}_\alpha(u) \;\le\; M_1,
$$

*with exact equality whenever $u(a, b) = c a + (1-c) b$ for any $c \in [0, 1]$.*

**Proof.**
1. *Linear invariance and symmetrization:* Direct substitution gives $\mathcal{L}_\alpha(a) = \mathcal{L}_\alpha(b) = M_1$, hence $\mathcal{L}_\alpha(c a + (1-c)b) = M_1$. Replacing $u(a, b)$ by $\frac{1}{2}(u(a, b) + u(b, a))$ preserves all constraints and $\mathcal{L}_\alpha(u)$. Subtracting $u(0, 0) \ge 0$ increases $\mathcal{L}_\alpha(u)$ by $u(0, 0)(\int_S \rho_\alpha + 2 t_0 g_{T,\alpha}(t_0)) = u(0, 0) \cdot 1 \ge 0$. Thus WLOG $u(a, b) = u(b, a)$ and $u(0, 0) = 0$.
2. *Radial Green identity on $S$:* Set $\vec{V}(a, b) := (a\rho_\alpha(a, b), b\rho_\alpha(a, b))$, which satisfies $\nabla \cdot \vec{V} = 2\alpha\rho_\alpha$ identically on $(0, 1]^2$. On the Lipschitz hexagon $S_\delta := S \cap [\delta, 1]^2$, $u\vec{V} \in W^{1,\infty}(S_\delta; \mathbb{R}^2)$, $\vec{V}\cdot\hat{n}\,dS = +t_0\rho_\alpha\,ds$ on $\partial_\pm S$ (cancelling the boundary term of $\mathcal{L}_\alpha(u)$ identically), and the edges $a = \delta, b = \delta$ are bounded by $\|u\|_\infty \alpha \delta^\alpha \to 0$ as $\delta \downarrow 0$. Passing $\delta \downarrow 0$ via Dominated Convergence gives

   $$
   \int_S (a\partial_a u + b\partial_b u - u)\rho_\alpha - \int_{\partial_\pm S} u\,t_0\rho_\alpha\,ds = \int_{1-t_0}^1 u(1, b)\rho_\alpha(1, b)\,db + \int_{1-t_0}^1 u(a, 1)\rho_\alpha(a, 1)\,da - (1 + 2\alpha)\int_S u\rho_\alpha.
   $$

3. *Exact deficit decomposition:* Set $w(a, b) := \frac{1}{2}(a + b) - u(a, b)$ (symmetric, concave, 1-Lipschitz, $w(0, 0) = 0$) and $D := \partial_a w + \partial_b w = 1 - (\partial_a u + \partial_b u) \in [0, 1]$ a.e. Subtracting Step 2 at $u^\star$ and halving onto $S_+ := \{(s + t, s) : t \in (0, t_0],\; s \in [0, 1-t]\}$ gives

   $$
   \frac{1}{2}\left(\mathcal{L}_\alpha(u) - M_1\right) = -L\int_{S_+} D\rho_\alpha + (1 + 2\alpha)\int_{S_+} w\rho_\alpha - \int_0^{t_0} w(1, 1 - t)\rho_\alpha(1, 1 - t)\,dt.
   $$

   By Rademacher's theorem and Fubini, for a.e. $t \in (0, t_0]$, $s \mapsto w(s+t, s)$ is Lipschitz with derivative $D(s+t, s)$ a.e., so $w(s+t, s) = w(t, 0) + \int_0^s D(r+t, r)\,dr$. Substituting this into both $w$ integrals and applying Tonelli ($D, \rho_\alpha \ge 0$) yields the identity

   $$
   \frac{1}{2}\left(\mathcal{L}_\alpha(u) - M_1\right) \;=\; -L\int_{S_+} D\rho_\alpha \;+\; \underbrace{\int_0^{t_0} K_\alpha(t)\,w(t, 0)\,dt}_{\text{Term A}} \;+\; \underbrace{\int_0^{t_0}\int_0^{1-t} \psi_{\alpha, t}(r)\,D(r + t, r)\,dr\,dt}_{\text{Term B}_{\mathrm{exact}}},
   $$

   where $\psi_{\alpha, t}(r) := (1 + 2\alpha)\int_r^{1-t}\rho_\alpha(s + t, s)\,ds - \rho_\alpha(1, 1 - t)$.
4. *Term A via $q \ge \tfrac{1}{2}D$ and the radial constant $J^\star(\alpha)$:*  
   On $S_+$ ($a > b$), for any $(p_a, p_b) \in \partial u(a, b)$, symmetry gives $(p_b, p_a) \in \partial u(b, a)$, so subgradient monotonicity on the convex set $S$ gives $2(a - b)(p_a - p_b) \ge 0 \implies p_a \ge p_b$. Writing $p := \partial_a w = \frac{1}{2} - p_a$ and $q := \partial_b w = \frac{1}{2} - p_b$, we have $p \le q$ and $p + q = D$, hence **$q \ge \frac{1}{2} D$ a.e. on $S_+$**. Fix any $c \in (0, t_0]$ and consider the corner triangle $T_c := \{(a, b) : 0 \le b \le a,\; a + b \le c\} \subseteq S_+$, parameterized smoothly by $a = \lambda, b = \lambda\eta$ ($\eta \in (0, 1)$, $\lambda \in (0, \lambda_1(\eta)]$, $\lambda_1(\eta) := \frac{c}{1+\eta}$, Jacobian $\lambda$, so $\rho_\alpha(\lambda, \lambda\eta)\lambda = \alpha^2 \lambda^{2\alpha - 1}\eta^{\alpha - 1}$). For a.e. $\eta$, $\phi_\eta(\lambda) := w(\lambda, \lambda\eta)$ is concave, Lipschitz, with $\phi_\eta(0) = 0$ and

   $$
   \phi_\eta'(\lambda) \;=\; p + \eta q \;=\; D - (1 - \eta) q \;\le\; \frac{1 + \eta}{2}\,D(\lambda, \lambda\eta) \qquad \text{a.e.}
   $$

   By concavity of $\phi_\eta$ ($\phi_\eta(\lambda) \ge \frac{\lambda}{\lambda_1}\phi_\eta(\lambda_1)$ for all $\lambda \in [0, \lambda_1]$, valid for *every* sign of $\phi_\eta(\lambda_1)$) and $1 - 2\alpha \ge 0$, integration by parts gives

   $$
   \int_0^{\lambda_1} \phi_\eta'(\lambda)\,\lambda^{2\alpha - 1}\,d\lambda = \lambda_1^{2\alpha - 1}\phi_\eta(\lambda_1) + (1 - 2\alpha)\int_0^{\lambda_1}\phi_\eta(\lambda)\,\lambda^{2\alpha - 2}\,d\lambda \;\ge\; \frac{\lambda_1^{2\alpha - 1}}{2\alpha}\,\phi_\eta(\lambda_1).
   $$

   By concavity and symmetry of $w$, $\phi_\eta(\lambda_1) = w(\frac{c}{1+\eta}, \frac{c\eta}{1+\eta}) \ge \frac{1}{1+\eta} w(c, 0) + \frac{\eta}{1+\eta} w(0, c) = w(c, 0)$. Hence

   $$
   \int_0^{\lambda_1} D(\lambda, \lambda\eta)\,\lambda^{2\alpha - 1}\,d\lambda \;\ge\; \frac{2}{1 + \eta}\cdot\frac{\lambda_1^{2\alpha - 1}}{2\alpha}\,w(c, 0) \;=\; \frac{c^{2\alpha - 1}}{\alpha}(1 + \eta)^{-2\alpha} w(c, 0).
   $$

   Multiplying by $\alpha^2 \eta^{\alpha - 1}$ and integrating $\eta \in (0, 1)$ (substituting $v = \frac{\eta}{1+\eta} \in (0, \frac{1}{2})$ gives $\alpha\int_0^1 \eta^{\alpha-1}(1+\eta)^{-2\alpha}\,d\eta = \frac{\alpha}{2} B(\alpha, \alpha) = \frac{\Gamma(\alpha+1)^2}{\Gamma(2\alpha+1)} = J^\star(\alpha)$), and using $D \ge 0$,

   $$
   \int_{T_c} D\rho_\alpha \;\ge\; J^\star(\alpha)\,c^{2\alpha - 1}\,(w(c, 0))_+ \qquad \forall c \in (0, t_0].
   $$

   Since $K_\alpha(t) > 0$ on $(0, t_0]$ and $w(t, 0) \le (w(t, 0))_+$, Tonelli-Fubini yields

   $$
   \text{Term A} \;\le\; \int_{S_+} W_A^\star(a + b)\,D(a, b)\rho_\alpha(a, b)\,da\,db, \qquad W_A^\star(x) := \frac{\mathbf{1}_{x \le t_0}}{J^\star(\alpha)}\int_x^{t_0} t^{1 - 2\alpha} K_\alpha(t)\,dt.
   $$

   Note $W_A^\star$ is finite ($t^{1-2\alpha}K_\alpha(t)$ is $O(1)$ for $\alpha < \tfrac{1}{2}$ and $O(\ln(1/t)) \in L^1$ for $\alpha = \tfrac{1}{2}$) and non-increasing on $[0, \infty)$.
5. *Pointwise bound on Term B.* Put $z := \sqrt{r(r+t)}$ and substitute $u = s(s+t)$ in $\int_r^{1-t} (s(s+t))^{\alpha-1}\,ds$; since $du = (2s+t)\,ds \ge 2\sqrt{s(s+t)}\,ds = 2\sqrt{u}\,ds$:

   $$
   \int_r^{1-t} \left(s(s+t)\right)^{\alpha-1}\,ds \;\le\; \frac{1}{2}\int_{z^2}^{1-t} u^{\alpha - 3/2}\,du \;=\; \frac{z^{2\alpha - 1} - (1-t)^{\alpha - 1/2}}{1 - 2\alpha}.
   $$

  Multiplying by $(1+2\alpha)z^{2-2\alpha}$ and subtracting $\frac{z^{2-2\alpha}}{(1-t)^{1-\alpha}}$ (using $(1-t)^{\alpha-1/2} \ge 1$ and $(1-t)^{\alpha-1} \ge 1$):

   $$
   \frac{\psi_{\alpha, t}(r)}{\rho_\alpha(r+t, r)} \;\le\; \frac{1 + 2\alpha}{1 - 2\alpha}\,z \;-\; \frac{2}{1 - 2\alpha}\,z^{2 - 2\alpha} \;\le\; \frac{1 + 2\alpha}{2(1 - \alpha)}\left(\frac{1 + 2\alpha}{4(1 - \alpha)}\right)^{\frac{1}{1 - 2\alpha}} = B_{\mathrm{elem}}(\alpha).
   $$

  Combined with $W_A^\star(a+b) \le W_A^\star(0) = C_A^\star(\alpha)$, we get $\frac{1}{2}(\mathcal{L}_\alpha(u) - M_1) \le (C_A^\star(\alpha) + B_{\mathrm{elem}}(\alpha) - L)\int_{S_+} D\rho_\alpha \le 0$ for all $L \ge L_0(\alpha)$. $\square$

### Assembly

Let $(g, p)$ be a feasible BIC, interim-IR mechanism; by Lemma E1 assume it allocates at most one
item per bidder. Bidder $i$'s interim utility $U_i$ is convex and non-negative on $[0,1]^2$ with
$\nabla U_i = (G_{i1}, G_{i2}) \ge 0$ and $G_{i1} + G_{i2} \le 1$ almost everywhere. Apply
Lemma E4(4) and Lemma E5 to each bidder and sum:

$$
\mathbb{E}[p_1 + p_2] \;\le\; 2M_1 + \mathbb{E}\left[\max_{\tilde g}\ \sum_{i=1}^{2} \mathbf{1}[v_i \notin S]\,\left(\tilde\phi_1^{\mathrm{wing}}(v_i)\,\tilde g_{i1} + \tilde\phi_2^{\mathrm{wing}}(v_i)\,\tilde g_{i2}\right)\right],
$$

the maximum being over feasible allocations of at most one item per bidder. By Lemma E4(2–3) all
four wing values exceed $L \ge 0$ and $\tilde\phi_1^{\mathrm{wing}} - \tilde\phi_2^{\mathrm{wing}} = \bar\Phi_\alpha$,
so at every profile the maximum is attained by the perfect matching that
$(g^\star_\alpha, p^\star_\alpha)$ selects. For $(g^\star_\alpha, p^\star_\alpha)$ itself $U_i$ is
linear on $S$, so Lemma E5 holds with equality. Hence the right-hand side equals the revenue of
$(g^\star_\alpha, p^\star_\alpha)$. $\blacksquare$

## 4. Proof of Proposition E2

Let $(g, p)$ be BIC and interim IR with $g_{i1} + g_{i2} = 1$ almost surely for both bidders.

*Symmetrize.* Averaging $(g,p)$ with its image under swapping the two items is again feasible, BIC
and interim IR, still allocates one item to each bidder, and has the same revenue, because the
distribution is invariant under the swap. So assume bidder 1's interim utility is symmetric:
$U(a,b) = U(b,a)$ on $[0,1]^2$.

*A lower bound on $U$.* $U$ is convex with $\partial_a U + \partial_b U = 1$ almost everywhere,
hence $U(a+s, b+s) = U(a,b) + s$ whenever both points lie in the square (true on almost every
diagonal, then everywhere by continuity). For fixed $c$ the function $\tau \mapsto U(c+\tau, c-\tau)$ is
convex and even, so it is minimised at $\tau = 0$. Therefore, with $U_0 := U(0,0) \ge 0$,

$$
U(a,b) \;\ge\; U\left(\tfrac{a+b}{2}, \tfrac{a+b}{2}\right) \;=\; U_0 + \tfrac{a+b}{2} \qquad \text{for all } (a,b) \in [0,1]^2 .
$$

*Perturb bidder 1 only.* Fix $\varepsilon \in (0, \tfrac{1}{2})$, let
$E := \{v_1 : U(v_1) < U_0 + \varepsilon\}$, and define a new mechanism that, when bidder 1 reports
$b_1 \in E$, gives her nothing and charges her nothing, and otherwise gives her the old allocation
and charges her the old payment plus $U_0 + \varepsilon$; bidder 2 is untouched. Supply constraints
still hold since bidder 1's allocation only shrinks. Bidder 1's new interim utility from reporting
$b_1$ at type $v_1$ is $0$ if $b_1 \in E$ and otherwise her old utility from that report minus
$U_0 + \varepsilon$, which is at most $U(v_1) - U_0 - \varepsilon$. So her best response gives
$\tilde U(v_1) = \max(0,\ U(v_1) - U_0 - \varepsilon)$, attained by reporting truthfully:
the new mechanism is BIC and interim IR.

*Revenue.* By the lower bound, $E \subseteq \{a + b < 2\varepsilon\}$, whose probability is
$c_\alpha (2\varepsilon)^{2\alpha}$ with $c_\alpha = \Gamma(\alpha+1)^2/\Gamma(2\alpha+1)$ (a Dirichlet
integral, valid as $2\varepsilon \le 1$). Off $E$ bidder 1 pays $U_0 + \varepsilon \ge \varepsilon$
more. On $E$ she used to pay $v_1 \cdot G_1 - U \le \max(v_{11}, v_{12}) \le L + 2\varepsilon$ in
expectation and now pays $0$. Hence

$$
\Delta\mathrm{Rev} \;\ge\; \varepsilon\left(1 - c_\alpha (2\varepsilon)^{2\alpha}\right) - (L + 2\varepsilon)\,c_\alpha (2\varepsilon)^{2\alpha},
$$

and since $2\alpha > 1$ the right-hand side is positive for all small $\varepsilon > 0$. $\blacksquare$

*Remark.* The same computation at $\alpha = \tfrac{1}{2}$ gives
$\Delta\mathrm{Rev} \ge \varepsilon\,(1 - \tfrac{\pi}{2}L - O(\varepsilon))$, positive when $L < 2/\pi$.
For the single mechanism $(g^\star, p^\star)$, an improvement that is moreover DSIC is proved in Lean
(`PAPER.md`, Theorem 2). Ruling out *every* full-allocation mechanism at $\alpha = \tfrac{1}{2}$,
$L < 2/\pi$ rests on the argument above and is not formalised.

## 5. What a formalisation would need

Theorem E1 follows the Lean proof of the $\alpha = \tfrac{1}{2}$ case step for step. The pieces that
would have to be redone for general $\alpha$ are the closed forms of Lemma E2 (which at
$\alpha = \tfrac{1}{2}$ are elementary functions and for general $\alpha$ are incomplete Beta integrals),
the wing bound of Lemma E4(3), and the radial constant $J^\star(\alpha)$ in Lemma E5, step 4.
