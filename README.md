# Continuous Multi-Item Auction Optimal DSIC Mechanisms & BIC–DSIC Certificates

This repository contains **two completely independent, self-contained tracks** on continuous multi-bidder, multi-item auction design. You can inspect, verify, or cite either track on its own without reading the other:

| Track | Question & Result | Standalone Entry Point | Verification |
|---|---|---|---|
| **Track 1: Optimal $2\times 2$ Unit-Demand DSIC Auction** | Explicit deterministic optimal DSIC (= BIC) auction for i.i.d. $v_{ij} = L + U_{ij}^2$ **if and only if** $L \ge 2/\pi$ (EconCS-Bench Characterization Goal for this distribution). | **[`optimal-dsic/`](optimal-dsic/)** ([README](optimal-dsic/README.md) · [PAPER](optimal-dsic/PAPER.md) · [Spec.lean](optimal-dsic/lean/EconCSAuction/Spec.lean)) | **Lean 4.36 + Mathlib** (`cd optimal-dsic/lean && ./replay.sh`) |
| **Track 2: Additive Continuous $\mathrm{BIC} > \mathrm{DSIC}$ Separation & Dual Bounds** | Strict $\mathrm{Rev}_{\mathrm{BIC}}^* > \mathrm{Rev}_{\mathrm{DSIC}}^*$ on $2\times 2$ and $3\times 2$ $U[0,1]$, plus tighter exact-rational $H(\mathrm{div})$ DSIC upper bounds for $U[0,1]$, $\mathrm{Beta}(1,2)$, and $2\times 3$ $U[0,1]^3$. | **Repo root** ([SPEC.md](SPEC.md) · [`lean/`](lean/) · [`certificates/`](certificates/) · [`verify_all_certificates.py`](verify_all_certificates.py)) | **Lean 4.36 + `nanoda`** + exact Python $\mathbb{Q}$ (`verify_all_certificates.py`) |

---

## Track 1: Optimal Auction for Two Unit-Demand Bidders and Two Items (`optimal-dsic/`)

*Fully self-contained in [`optimal-dsic/`](optimal-dsic/). Start at [`optimal-dsic/README.md`](optimal-dsic/README.md) or [`optimal-dsic/PAPER.md`](optimal-dsic/PAPER.md).*

Values are i.i.d. $v_{ij} = L + U_{ij}^2$ with $U_{ij} \sim \mathrm{Uniform}[0,1]$ (continuous CDF $\sqrt{v-L}$ on $[L, L+1]$). An explicit deterministic posted-price mechanism is proved in **Lean 4.36 + Mathlib** to be revenue-optimal among all measurable randomized BIC + interim-IR (hence all DSIC + ex-post IR) mechanisms **if and only if** $L \ge 2/\pi$. This addresses the Characterization Goal of [EconCS-Bench `revenue-optimal-dsic-auction`](https://github.com/aieconcs/econcs-bench/blob/main/revenue-optimal-dsic-auction/PROBLEM.md) for this distribution; its density is unbounded at the lower endpoint, and the theorem says nothing about bounded densities.

| Statement | Proof status | Where |
|---|---|---|
| $L \ge 2/\pi$: the explicit deterministic mechanism is feasible, DSIC, ex-post IR, has the stated exact revenue, and is optimal among all randomized BIC + interim-IR and DSIC + ex-post IR mechanisms | **Lean 4.36 + Mathlib** | [`PAPER.md`](optimal-dsic/PAPER.md) Theorem 1; [`Spec.lean`](optimal-dsic/lean/EconCSAuction/Spec.lean) |
| $0 \le L < 2/\pi$: an explicit DSIC + ex-post IR single-item mechanism with non-negative payments earns strictly more | **Lean 4.36 + Mathlib** | [`PAPER.md`](optimal-dsic/PAPER.md) Theorem 2; [`Theorem2.lean`](optimal-dsic/lean/EconCSAuction/Theorem2.lean) |
| $L \ge 0$: the mechanism is optimal (among DSIC + ex-post IR, and among BIC + interim-IR mechanisms) **if and only if** $L \ge 2/\pi$ | **Lean 4.36 + Mathlib** | [`PAPER.md`](optimal-dsic/PAPER.md) Theorem 3; [`Spec.lean`](optimal-dsic/lean/EconCSAuction/Spec.lean) |

- **Method:** Split each bidder's type square into the strip $\{\lvert a-b\rvert < t_0\}$ and the two wings. On the wings an explicit divergence-form flux yields virtual values whose difference is the ironed virtual value of $a-b$; on the strip a radial-weight dominance lemma in polar uniform coordinates shows any deviation from linear interim utility loses revenue once $L \ge 2/\pi$, with sharp constant $2/\pi$ matching the quarter-disk exclusion perturbation of Theorem 2. See [`optimal-dsic/PAPER.md`](optimal-dsic/PAPER.md) §4.
- **Verification & trust boundary:** 12 Lean modules plus `CleanRoomAudit` (`[propext, Classical.choice, Quot.sound]` only, `13/13` `leanchecker` `PASS`). To trust Theorems 1–3, read [`Spec.lean`](optimal-dsic/lean/EconCSAuction/Spec.lean) and trust the Lean kernel and Mathlib. What is optimal for $L < 2/\pi$ is open. (A separate, non-formalised pen-and-paper note on other exponents is in [`optimal-dsic/EXTENSIONS.md`](optimal-dsic/EXTENSIONS.md); nothing above depends on it.)

```bash
cd optimal-dsic/lean
./replay.sh   # rebuild from source, check source manifest + axioms, replay all 13 modules in leanchecker
```

---

## Track 2: Strict Continuous Additive $\mathrm{BIC} > \mathrm{DSIC}$ Separation & Dual Bounds (Repo Root)

*Fully self-contained at the repository root (`SPEC.md`, `lean/`, `certificates/`, `generators/`, `tests/`, `verify_all_certificates.py`). Full definitions in [`SPEC.md`](SPEC.md).*

Machine-checkable Lean 4 + `nanoda` and exact-rational $H(\mathrm{div})$ Raviart–Thomas certificates proving strict $\mathrm{Rev}_{\mathrm{BIC}}^* > \mathrm{Rev}_{\mathrm{DSIC}}^*$ on canonical continuous $2 \times 2$ and $3 \times 2$ $U[0,1]$ additive auctions, tightening continuous DSIC upper bounds against [Jiang, Parkes & Wang (2026)](https://arxiv.org/abs/2606.10112) and [Fang (2026)](https://github.com/Baymax-ray/two-bidder-two-item-dsic-certificates), and certifying full-support $2 \times 2$ $\mathrm{Beta}(1,2)$ and $2 \times 3$ $U[0,1]^3$ bounds. Total expected revenue summed over all $B$ bidders; decimals are exact outward bounds (ceil for UBs, floor for LBs).

| Instance | Result | Certified Bound | Track | Artifact |
|---|---|---|---|---|
| $2 \times 2$, $U[0,1]$ | $\mathrm{Rev}_{\mathrm{BIC}}^* > \mathrm{Rev}_{\mathrm{DSIC}}^*$ (ex-post IR, NPT) | $\frac{62105}{69984} > \frac{2324277}{2621440}$ (gap $\approx 7.76 \times 10^{-4}$) | Lean 4 + `nanoda` | [`EqualExPostIR.lean`](lean/AuctionSep/EqualExPostIR.lean) |
| $2 \times 2$, $U[0,1]$ | $\mathrm{Rev}_{\mathrm{DSIC}}^*$ UB ($M=10$, $RT_0$) | $\le 0.8817556131$ | Exact $\mathbb{Q}$ | [`exact_cert_dsic_b2_m10.npz`](certificates/exact_cert_dsic_b2_m10.npz) |
| $2 \times 2$, $U[0,1]$ | $\mathrm{Rev}_{\mathrm{BIC}}^*$ LB (explicit ex-post, $854$ cells, $128$ tiers) | $\ge 0.8911490551$ (gap $\ge 0.0093934420$) | Exact $\mathbb{Q}$ | [`cert_bic_b2_n36.npz`](certificates/cert_bic_b2_n36.npz), [`cert_expost_bic_b2.json`](certificates/cert_expost_bic_b2.json) |
| $3 \times 2$, $U[0,1]$ | $\mathrm{Rev}_{\mathrm{DSIC}}^*$ UB ($M=5$, $RT_0$) | $\le 1.1092371527$ | Exact $\mathbb{Q}$ | [`exact_cert_dsic_b3_m5.npz`](certificates/exact_cert_dsic_b3_m5.npz) |
| $3 \times 2$, $U[0,1]$ | $\mathrm{Rev}_{\mathrm{BIC}}^*$ LB (explicit ex-post, $409$ cells, $128$ tiers) | $\ge 1.1102826130$ (gap $\ge 0.0010454604$) | Exact $\mathbb{Q}$ | [`cert_bic_b3_n24.npz`](certificates/cert_bic_b3_n24.npz), [`cert_expost_bic_b3.json`](certificates/cert_expost_bic_b3.json) |
| $2 \times 2$, $\mathrm{Beta}(1,2)$ | $\mathrm{Rev}_{\mathrm{DSIC}}^*$ UB on full $[0,1]^2$ ($M=8, S=8$) | $\le 0.5878659834$ | Exact $\mathbb{Q}$ | [`exact_cert_dsic_beta12_m8.npz`](certificates/exact_cert_dsic_beta12_m8.npz) |
| $2 \times 3$, $U[0,1]^3$ | $\mathrm{Rev}_{\mathrm{DSIC}}^*$ UB ($M=4$, $S_3$-equivariant) | $\le 1.3905597048$ | Exact $\mathbb{Q}$ | [`exact_cert_dsic_2x3_m4.npz`](certificates/exact_cert_dsic_2x3_m4.npz) |

- **Method & trust boundary:** Parameterize Giannakopoulos–Koutsoupias continuous dual fluxes in $RT_0$ elements (zero grid-lifting error; exact integer inequalities); construct symmetric ex-post priority-tier BIC couplings with ratio payments (realized-bundle ex-post IR + NPT, no Border's theorem). Only the $2 \times 2$ $U[0,1]$ separation ($62105/69984 > 2324277/2621440$) is kernel-proved in Lean 4 + `nanoda 0.4.17` ([`EqualExPostIR.lean`](lean/AuctionSep/EqualExPostIR.lean), keeping [`Problem.lean`](lean/AuctionSep/Problem.lean) frozen; `43,445` declarations). Tighter bounds are verified in exact Python rational arithmetic (full $[0,1]^2$ $\mathrm{Beta}(1,2)$ uses chord-padded quadrature $+5/(4G^2)$ at $G=64$).

```bash
# Exact-rational certificates (~85s on 1 CPU core) & forgery/calibration suites
uv run --with numpy python3 -O verify_all_certificates.py        # or --json
uv run --with numpy python3 -O tests/test_verifier.py           # 22/22 forgery rejections
uv run --with numpy --with scipy python3 -O tests/calibration_b1.py

# Additive 2x2 U[0,1] Lean 4.36 proof (logs in lean/logs/)
cd lean && lake exe cache get && lake build
```

---

## Comparison with Prior Work

| Reference | Prior Result | Relation Here |
|---|---|---|
| **Pavlov (2011), GK (2014), DDT (2015/2017)** | Exact continuous optimal mechanisms for a single buyer ($B = 1$, $I \ge 2$). | **Track 1:** Exact optimum for two unit-demand bidders and two items for one family of continuous product distributions (`optimal-dsic/`). |
| **Yao (2017)**, *EC*, [`arXiv:1607.03685`](https://arxiv.org/abs/1607.03685) | Strict $\mathrm{BIC} > \mathrm{DSIC}$ on disconnected continuous support; exact DSIC on 2-item 2-point discrete support. | **Track 2:** Connected $U[0,1]$ separation ($2\times 2, 3\times 2$). **Track 1:** Continuous-support $2\times 2$ unit-demand optimum (`optimal-dsic/`). |
| **Liu–Liu–Wang (2026)**, [`arXiv:2610.11051`](https://arxiv.org/abs/2610.11051) | Exact deterministic DSIC optimum for general $n, m$ additive bidders on 2-point discrete i.i.d. support (plus #P-hardness for general finite support). | **Track 1:** Continuous-support $2\times 2$ unit-demand optimum (`optimal-dsic/`). |
| **KSTZ (2022)**, [`arXiv:2203.06837`](https://arxiv.org/abs/2203.06837) | Continuous BIC Beckmann duality; numerical $\approx +5.7\%$ over $5/6$ for $2\times 2$ $U[0,1]$. | **Track 2:** Certified explicit ex-post LB $\ge 0.8911490551$ ($\ge +6.9378\%$ over $5/6$). |
| **Jiang, Parkes & Wang (2026)**, [`arXiv:2606.10112`](https://arxiv.org/abs/2606.10112) & [EconCS-Bench](https://github.com/aieconcs/econcs-bench/blob/main/revenue-optimal-dsic-auction/PROBLEM.md) | Neural Lagrangian DSIC UBs ($0.8919$ $2\times 2$, $1.120$ $3\times 2$, $0.588$ clamped $\mathrm{Beta}(1,2)$) & open continuous optimal-DSIC benchmark. | **Track 2:** Tighter exact-rational UBs ($\le 0.881756$, $\le 1.109237$, full $[0,1]^2$ $\le 0.587866$). **Track 1:** Lean-checked closed-form optimum for one unit-demand distribution with unbounded endpoint density. |
| **Fang (2026)**, [`Baymax-ray/...`](https://github.com/Baymax-ray/two-bidder-two-item-dsic-certificates) | Exact-rational $2\times 2$ $U[0,1]$ DSIC UB $0.8823515855$. | **Track 2:** Tightened to $\le 0.8817556131$ ($\ge 5.96 \times 10^{-4}$ reduction). |

---

## Repository Layout & Integrity

- **[`optimal-dsic/`](optimal-dsic/)** — **Track 1** (self-contained): [`README.md`](optimal-dsic/README.md), [`PAPER.md`](optimal-dsic/PAPER.md), [`lean/`](optimal-dsic/lean/) (12 modules, `CleanRoomAudit.lean`, `replay.sh`, `logs/`), and non-formalised [`EXTENSIONS.md`](optimal-dsic/EXTENSIONS.md).
- **[`SPEC.md`](SPEC.md), [`lean/`](lean/), [`certificates/`](certificates/), [`generators/`](generators/), [`tests/`](tests/), [`verify_all_certificates.py`](verify_all_certificates.py)** — **Track 2** (self-contained): additive BIC > DSIC separation in Lean 4 + `nanoda` and exact-rational certificates.
- **[`SHA256SUMS`](SHA256SUMS), [`CITATION.cff`](CITATION.cff), [`LICENSE`](LICENSE)** — Combined integrity manifest (`sha256sum -c SHA256SUMS`), citation metadata, and MIT license.
