# Exact Optimal Auction for Two Unit-Demand Bidders and Two Items

Self-contained Lean 4.36 + Mathlib formalization and proof guide for an exact revenue-optimal DSIC (= BIC) continuous multi-bidder, multi-item auction (addressing the Characterization Goal of [EconCS-Bench `revenue-optimal-dsic-auction`](https://github.com/aieconcs/econcs-bench/blob/main/revenue-optimal-dsic-auction/PROBLEM.md) for this distribution family).

> **Standalone track:** Everything in this directory (`optimal-dsic/`) is completely independent of the additive BIC–DSIC separation track at the repository root. You do not need to read or build anything outside `optimal-dsic/`.

---

## Summary of Results

Two unit-demand bidders, two indivisible items, with all four values i.i.d.

$$
v_{ij} = L + U_{ij}^2, \qquad U_{ij} \sim \mathrm{Uniform}[0, 1],
$$

so $v_{ij} \in [L, L+1]$ with continuous CDF $F(v) = \sqrt{v - L}$ and parameter $L \ge 0$.

All three main theorems are kernel-checked in **Lean 4.36 + Mathlib** with standard axioms `[propext, Classical.choice, Quot.sound]` only (zero `sorry`, zero custom axioms):

| Result | Statement | Lean entry point |
|---|---|---|
| **Theorem 1** | For every $L \ge 2/\pi$, an explicit deterministic posted-price mechanism $(g^\star, p^\star)$ is feasible, DSIC, ex-post IR, has payments in $[L, L+1]$, has exact closed-form revenue, and is optimal among **all** measurable randomized BIC + interim-IR (hence all DSIC + ex-post IR) mechanisms. | `Theorem1Statement` ([`Spec.lean`](lean/EconCSAuction/Spec.lean)) / `theorem1_proof` ([`Proof.lean`](lean/EconCSAuction/Proof.lean)) |
| **Theorem 2** | For every $0 \le L < 2/\pi$, an explicit feasible, DSIC, ex-post IR, single-item mechanism with non-negative payments strictly beats $(g^\star, p^\star)$. | `flagshipMechanism_suboptimal_below_two_div_pi` ([`Theorem2.lean`](lean/EconCSAuction/Theorem2.lean)) |
| **Theorem 3** | For $L \ge 0$, $(g^\star, p^\star)$ is revenue-optimal (both over DSIC + ex-post IR and over BIC + interim-IR) **if and only if** $L \ge 2/\pi$. | `SharpThresholdStatement` ([`Spec.lean`](lean/EconCSAuction/Spec.lean)) / `sharpThreshold_proof` ([`Proof.lean`](lean/EconCSAuction/Proof.lean)) |

**Scope & limits:** This is one continuous distribution family whose endpoint density $f(v) = \frac{1}{2\sqrt{v - L}}$ is unbounded at $L$. What is optimal for $L < 2/\pi$ is open, and the theorems say nothing about bounded densities such as $\mathrm{Uniform}[0, 1]$ or about Goal (1) (the computational goal) of EconCS-Bench.

---

## Reading Order & Files

1. **[`PAPER.md`](PAPER.md)** — Complete, self-contained statement of the mechanism, Theorems 1–3, and a line-by-line guide to the Lean proof.
2. **[`lean/EconCSAuction/Spec.lean`](lean/EconCSAuction/Spec.lean)** — Isolated 235-line specification containing definitions and theorem statements only (no proofs).
3. **[`lean/CleanRoomAudit.lean`](lean/CleanRoomAudit.lean)** — Independent sanity checks on `Spec.lean` (measure normalization, CDF $\sqrt{v-L}$, non-vacuity of `ExpectedRevenue`, constructive $2\times 2$ Birkhoff–von Neumann lottery realizability over the 9 deterministic feasible allocations, `#check` signatures, and `#print axioms`).
4. **[`lean/logs/`](lean/logs/)** — Archived deterministic [`cleanroom_audit.log`](lean/logs/cleanroom_audit.log) (including SHA-256 manifest of all 14 `.lean` files) and [`leanchecker.log`](lean/logs/leanchecker.log) (`13/13 PASS`).
5. **[`EXTENSIONS.md`](EXTENSIONS.md)** & [`check_extensions.py`](check_extensions.py) — Separate pen-and-paper note on exponents $\alpha \neq 1/2$; **not formalised in Lean** and not relied on anywhere in `PAPER.md` or `lean/`.

---

## Independent Verification

```bash
cd optimal-dsic/lean
./replay.sh   # lake exe cache get; lake build; source manifest + axiom check; 13-module leanchecker replay
```

To trust Theorems 1–3, you only need to inspect [`Spec.lean`](lean/EconCSAuction/Spec.lean) (plus the `#check` output in [`cleanroom_audit.log`](lean/logs/cleanroom_audit.log) for the `NonNegPayment`, `IsSingleItem`, and `IsLotteryRealizable` checks) and trust the Lean 4.36 kernel and Mathlib.
