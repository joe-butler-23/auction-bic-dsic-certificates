import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# EconCS-Bench Revenue-Optimal Continuous DSIC (= BIC) Auction — Isolated Specification

Clean, proof-free specification of the `n = 2` bidders, `m = 2` indivisible items unit-demand
auction with i.i.d. shifted square-root valuations `v_ij = L + U_ij²` (`U_ij ~ U[0, 1]`,
continuous CDF `F(v) = √(v - L)` on `[L, L + 1]`), the full randomized 4-bundle competitor class,
the explicit deterministic optimal mechanism `flagshipMechanism`, and the Theorem 1 target statement.
-/

open MeasureTheory

namespace EconCSAuction

noncomputable section

/-- Valuation pair `(v_{i1}, v_{i2})` for one unit-demand bidder over 2 indivisible items. -/
abbrev Type2 := ℝ × ℝ

/-- Support `[L, L + 1]` of each single valuation `v_ij`. -/
def valInterval (L : ℝ) : Set ℝ := Set.Icc L (L + 1)

/-- Support `[L, L + 1]²` of one bidder's valuation vector. -/
def bidderDomain (L : ℝ) : Set Type2 := valInterval L ×ˢ valInterval L

/-- Joint type space `[L, L + 1]² × [L, L + 1]²`. -/
def profileDomain (L : ℝ) : Set (Type2 × Type2) := bidderDomain L ×ˢ bidderDomain L

/-- Distribution of `v_ij = L + U_ij²` with `U_ij ~ U[0, 1]` (continuous CDF `F(v) = √(v - L)`). -/
def singleValMeasure (L : ℝ) : Measure ℝ :=
  Measure.map (fun u : ℝ => L + u ^ 2) (volume.restrict (Set.Icc (0 : ℝ) 1))

/-- Independent product distribution for one bidder's `(v_{i1}, v_{i2})`. -/
def bidderMeasure (L : ℝ) : Measure Type2 :=
  (singleValMeasure L).prod (singleValMeasure L)

/-- Independent joint product distribution `F = ∏_{i,j} F_{ij}` over both bidders. -/
def jointMeasure (L : ℝ) : Measure (Type2 × Type2) :=
  (bidderMeasure L).prod (bidderMeasure L)

/-- Randomized 4-bundle direct revelation mechanism (`∅`, `{1}`, `{2}`, `{1, 2}`) for `n = 2, m = 2`. -/
structure Mechanism where
  q1_1  : Type2 → Type2 → ℝ
  q1_2  : Type2 → Type2 → ℝ
  q1_12 : Type2 → Type2 → ℝ
  q2_1  : Type2 → Type2 → ℝ
  q2_2  : Type2 → Type2 → ℝ
  q2_12 : Type2 → Type2 → ℝ
  p1    : Type2 → Type2 → ℝ
  p2    : Type2 → Type2 → ℝ

/-- Unit-demand expected value of bundle probabilities `(q1, q2, q12)` at true valuation `v`. -/
def UnitDemandVal (v : Type2) (q1 q2 q12 : ℝ) : ℝ :=
  v.1 * q1 + v.2 * q2 + max v.1 v.2 * q12

/-- Pointwise ex-post probability and item-supply feasibility for randomized 4-bundle allocations. -/
def IsPointwiseFeasible (L : ℝ) (M : Mechanism) : Prop :=
  ∀ v1 ∈ bidderDomain L, ∀ v2 ∈ bidderDomain L,
    0 ≤ M.q1_1 v1 v2 ∧ 0 ≤ M.q1_2 v1 v2 ∧ 0 ≤ M.q1_12 v1 v2 ∧
    0 ≤ M.q2_1 v1 v2 ∧ 0 ≤ M.q2_2 v1 v2 ∧ 0 ≤ M.q2_12 v1 v2 ∧
    M.q1_1 v1 v2 + M.q1_2 v1 v2 + M.q1_12 v1 v2 ≤ 1 ∧
    M.q2_1 v1 v2 + M.q2_2 v1 v2 + M.q2_12 v1 v2 ≤ 1 ∧
    (M.q1_1 v1 v2 + M.q1_12 v1 v2) + (M.q2_1 v1 v2 + M.q2_12 v1 v2) ≤ 1 ∧
    (M.q1_2 v1 v2 + M.q1_12 v1 v2) + (M.q2_2 v1 v2 + M.q2_12 v1 v2) ≤ 1

/-- Measurable, jointly integrable, ex-post supply-feasible randomized 4-bundle mechanism. -/
def IsFeasible (L : ℝ) (M : Mechanism) : Prop :=
  IsPointwiseFeasible L M ∧
  Measurable (Function.uncurry M.q1_1) ∧
  Measurable (Function.uncurry M.q1_2) ∧
  Measurable (Function.uncurry M.q1_12) ∧
  Measurable (Function.uncurry M.q2_1) ∧
  Measurable (Function.uncurry M.q2_2) ∧
  Measurable (Function.uncurry M.q2_12) ∧
  Measurable (Function.uncurry M.p1) ∧
  Measurable (Function.uncurry M.p2) ∧
  Integrable (Function.uncurry M.p1) (jointMeasure L) ∧
  Integrable (Function.uncurry M.p2) (jointMeasure L)

/-- Single-item mechanism (`q1_12 = 0` and `q2_12 = 0` everywhere). -/
def IsSingleItem (M : Mechanism) : Prop :=
  (∀ v1 v2, M.q1_12 v1 v2 = 0) ∧ (∀ v1 v2, M.q2_12 v1 v2 = 0)

/-- Ex-post utility of Bidder 1 with true type `v1` reporting `b1` against `b2`. -/
def u1Report (M : Mechanism) (v1 b1 b2 : Type2) : ℝ :=
  UnitDemandVal v1 (M.q1_1 b1 b2) (M.q1_2 b1 b2) (M.q1_12 b1 b2) - M.p1 b1 b2

/-- Ex-post utility of Bidder 2 with true type `v2` reporting `b2` against `b1`. -/
def u2Report (M : Mechanism) (b1 v2 b2 : Type2) : ℝ :=
  UnitDemandVal v2 (M.q2_1 b1 b2) (M.q2_2 b1 b2) (M.q2_12 b1 b2) - M.p2 b1 b2

/-- Dominant-Strategy Incentive Compatibility (DSIC) on `[L, L + 1]² × [L, L + 1]²`. -/
def IsDSIC (L : ℝ) (M : Mechanism) : Prop :=
  (∀ v1 ∈ bidderDomain L, ∀ b1 ∈ bidderDomain L, ∀ b2 ∈ bidderDomain L,
    u1Report M v1 b1 b2 ≤ u1Report M v1 v1 b2) ∧
  (∀ b1 ∈ bidderDomain L, ∀ v2 ∈ bidderDomain L, ∀ b2 ∈ bidderDomain L,
    u2Report M b1 v2 b2 ≤ u2Report M b1 v2 v2)

/-- Ex-Post Individual Rationality (IR). -/
def IsExPostIR (L : ℝ) (M : Mechanism) : Prop :=
  ∀ v1 ∈ bidderDomain L, ∀ v2 ∈ bidderDomain L,
    0 ≤ u1Report M v1 v1 v2 ∧ 0 ≤ u2Report M v1 v2 v2

/-- Nonnegative ex-post transfers (`p_i ≥ 0`). -/
def NonNegPayment (L : ℝ) (M : Mechanism) : Prop :=
  ∀ v1 ∈ bidderDomain L, ∀ v2 ∈ bidderDomain L,
    0 ≤ M.p1 v1 v2 ∧ 0 ≤ M.p2 v1 v2

/-- Ex-post transfers lying inside `[L, L + 1]`. -/
def BoundedPayment (L : ℝ) (M : Mechanism) : Prop :=
  ∀ v1 ∈ bidderDomain L, ∀ v2 ∈ bidderDomain L,
    M.p1 v1 v2 ∈ valInterval L ∧ M.p2 v1 v2 ∈ valInterval L

/-- Interim allocations and payments for Bidders 1 and 2. -/
def Q1_1  (L : ℝ) (M : Mechanism) (b1 : Type2) : ℝ := ∫ b2, M.q1_1  b1 b2 ∂(bidderMeasure L)
def Q1_2  (L : ℝ) (M : Mechanism) (b1 : Type2) : ℝ := ∫ b2, M.q1_2  b1 b2 ∂(bidderMeasure L)
def Q1_12 (L : ℝ) (M : Mechanism) (b1 : Type2) : ℝ := ∫ b2, M.q1_12 b1 b2 ∂(bidderMeasure L)
def P1    (L : ℝ) (M : Mechanism) (b1 : Type2) : ℝ := ∫ b2, M.p1    b1 b2 ∂(bidderMeasure L)

def Q2_1  (L : ℝ) (M : Mechanism) (b2 : Type2) : ℝ := ∫ b1, M.q2_1  b1 b2 ∂(bidderMeasure L)
def Q2_2  (L : ℝ) (M : Mechanism) (b2 : Type2) : ℝ := ∫ b1, M.q2_2  b1 b2 ∂(bidderMeasure L)
def Q2_12 (L : ℝ) (M : Mechanism) (b2 : Type2) : ℝ := ∫ b1, M.q2_12 b1 b2 ∂(bidderMeasure L)
def P2    (L : ℝ) (M : Mechanism) (b2 : Type2) : ℝ := ∫ b1, M.p2    b1 b2 ∂(bidderMeasure L)

/-- Bayesian Incentive Compatibility (BIC) with slice integrability of payments. -/
def IsBIC (L : ℝ) (M : Mechanism) : Prop :=
  (∀ b1 ∈ bidderDomain L, Integrable (fun b2 => M.p1 b1 b2) (bidderMeasure L)) ∧
  (∀ b2 ∈ bidderDomain L, Integrable (fun b1 => M.p2 b1 b2) (bidderMeasure L)) ∧
  (∀ v1 ∈ bidderDomain L, ∀ b1 ∈ bidderDomain L,
    UnitDemandVal v1 (Q1_1 L M b1) (Q1_2 L M b1) (Q1_12 L M b1) - P1 L M b1 ≤
    UnitDemandVal v1 (Q1_1 L M v1) (Q1_2 L M v1) (Q1_12 L M v1) - P1 L M v1) ∧
  (∀ v2 ∈ bidderDomain L, ∀ b2 ∈ bidderDomain L,
    UnitDemandVal v2 (Q2_1 L M b2) (Q2_2 L M b2) (Q2_12 L M b2) - P2 L M b2 ≤
    UnitDemandVal v2 (Q2_1 L M v2) (Q2_2 L M v2) (Q2_12 L M v2) - P2 L M v2)

/-- Interim Individual Rationality (IR). -/
def IsInterimIR (L : ℝ) (M : Mechanism) : Prop :=
  (∀ v1 ∈ bidderDomain L,
    0 ≤ UnitDemandVal v1 (Q1_1 L M v1) (Q1_2 L M v1) (Q1_12 L M v1) - P1 L M v1) ∧
  (∀ v2 ∈ bidderDomain L,
    0 ≤ UnitDemandVal v2 (Q2_1 L M v2) (Q2_2 L M v2) (Q2_12 L M v2) - P2 L M v2)

/-- Expected total seller revenue `E[p1 + p2]` under `jointMeasure L`. -/
def ExpectedRevenue (L : ℝ) (M : Mechanism) : ℝ :=
  ∫ x, (M.p1 x.1 x.2 + M.p2 x.1 x.2) ∂(jointMeasure L)

/-! ### Analytical Objects for `α = 1/2` -/

/-- Inverse hyperbolic tangent `artanh(s) = (1/2) ln((1 + s)/(1 - s))`. -/
def artanh (s : ℝ) : ℝ := (1 / 2) * Real.log ((1 + s) / (1 - s))

/-- Density `g_T(t) = (1/2) artanh(√(1 - t))` of `t = v_1 - v_2` on `(0, 1)`. -/
def gT (t : ℝ) : ℝ := (1 / 2) * artanh (Real.sqrt (1 - t))

/-- Upper tail `1 - G_T(t) = √(1 - t)/2 - t g_T(t)` on `(0, 1]`. -/
def tailGT (t : ℝ) : ℝ := Real.sqrt (1 - t) / 2 - t * gT t

/-- CDF `G_T(t) = 1 - (1 - G_T(t))` on `(0, 1]`. -/
def GT (t : ℝ) : ℝ := 1 - tailGT t

/-- One-sided Myerson virtual difference `Φ_+(t) = 2t - √(1 - t) / artanh(√(1 - t))`. -/
def PhiPlus (t : ℝ) : ℝ := 2 * t - Real.sqrt (1 - t) / artanh (Real.sqrt (1 - t))

/-- Unique root `t₀ ∈ (0, 1)` of `Φ_+(t₀) = 0` (`t₀ ≈ 0.36576558665 ∈ (9/25, 7/16)`). -/
def t0 : ℝ := Classical.epsilon (fun t : ℝ => t ∈ Set.Ioo (0 : ℝ) 1 ∧ PhiPlus t = 0)

/-- Odd ironed virtual difference `Φ̄(t)` (zero on `[-t₀, t₀]`). -/
def PhiBar (t : ℝ) : ℝ :=
  if t0 < t then PhiPlus t else if t < -t0 then -PhiPlus (-t) else 0

/-- Strip kernel `K(t) = 2 g_T(t) - 1/(4√(1 - t))`. -/
def K (t : ℝ) : ℝ := 2 * gT t - 1 / (4 * Real.sqrt (1 - t))

/-! ### Explicit Optimal Deterministic Auction `(g⋆, p⋆)` -/

/-- Bidder 1's posted prices `(p_{1,1}(t₂), p_{1,2}(t₂))` depending only on `t₂ = b_{21} - b_{22}`. -/
def p1Item1 (L t2 : ℝ) : ℝ := if -t0 ≤ t2 then L + max t0 t2 else L
def p1Item2 (L t2 : ℝ) : ℝ := if -t0 ≤ t2 then L else L + (-t2)

/-- Bidder 2's posted prices `(p_{2,1}(t₁), p_{2,2}(t₁))` depending only on `t₁ = b_{11} - b_{12}`. -/
def p2Item1 (L t1 : ℝ) : ℝ := if t1 ≤ t0 then L else L + t1
def p2Item2 (L t1 : ℝ) : ℝ := if t1 ≤ t0 then L + max t0 (-t1) else L

/-- Explicit closed-form deterministic optimal mechanism `(g⋆, p⋆)` of Theorem 1. -/
def flagshipMechanism (L : ℝ) : Mechanism where
  q1_1  b1 b2 := if b1.1 - p1Item1 L (b2.1 - b2.2) > b1.2 - p1Item2 L (b2.1 - b2.2) then 1 else 0
  q1_2  b1 b2 := if b1.1 - p1Item1 L (b2.1 - b2.2) > b1.2 - p1Item2 L (b2.1 - b2.2) then 0 else 1
  q1_12 _  _  := 0
  q2_1  b1 b2 := if b2.1 - p2Item1 L (b1.1 - b1.2) ≥ b2.2 - p2Item2 L (b1.1 - b1.2) then 1 else 0
  q2_2  b1 b2 := if b2.1 - p2Item1 L (b1.1 - b1.2) ≥ b2.2 - p2Item2 L (b1.1 - b1.2) then 0 else 1
  q2_12 _  _  := 0
  p1    b1 b2 :=
    if b1.1 - p1Item1 L (b2.1 - b2.2) > b1.2 - p1Item2 L (b2.1 - b2.2)
    then p1Item1 L (b2.1 - b2.2) else p1Item2 L (b2.1 - b2.2)
  p2    b1 b2 :=
    if b2.1 - p2Item1 L (b1.1 - b1.2) ≥ b2.2 - p2Item2 L (b1.1 - b1.2)
    then p2Item1 L (b1.1 - b1.2) else p2Item2 L (b1.1 - b1.2)

/-- Exact analytical optimal revenue `2L + 2 ∫_{t₀}^{1} Φ_+(t) g_T(t) (2 G_T(t) - 1) dt`. -/
def optimalRevenueFormula (L : ℝ) : ℝ :=
  2 * L + 2 * ∫ t in Set.Ioo t0 1, PhiPlus t * gT t * (2 * GT t - 1)

/-- Top-level Theorem 1 target specification. -/
def Theorem1Statement : Prop :=
  ∀ L : ℝ, 2 / Real.pi ≤ L →
    IsFeasible L (flagshipMechanism L) ∧
    IsDSIC L (flagshipMechanism L) ∧
    IsExPostIR L (flagshipMechanism L) ∧
    NonNegPayment L (flagshipMechanism L) ∧
    BoundedPayment L (flagshipMechanism L) ∧
    ExpectedRevenue L (flagshipMechanism L) = optimalRevenueFormula L ∧
    (∀ M : Mechanism, IsFeasible L M → IsBIC L M → IsInterimIR L M →
      ExpectedRevenue L M ≤ ExpectedRevenue L (flagshipMechanism L)) ∧
    (∀ M : Mechanism, IsFeasible L M → IsDSIC L M → IsExPostIR L M →
      ExpectedRevenue L M ≤ ExpectedRevenue L (flagshipMechanism L))

/-- Sharp threshold: for `L ≥ 0`, `flagshipMechanism L` is revenue-optimal among feasible DSIC,
ex-post IR mechanisms if and only if `L ≥ 2/π`, and likewise among feasible BIC, interim-IR
mechanisms. -/
def SharpThresholdStatement : Prop :=
  ∀ L : ℝ, 0 ≤ L →
    ((∀ M : Mechanism, IsFeasible L M → IsDSIC L M → IsExPostIR L M →
        ExpectedRevenue L M ≤ ExpectedRevenue L (flagshipMechanism L)) ↔ 2 / Real.pi ≤ L) ∧
    ((∀ M : Mechanism, IsFeasible L M → IsBIC L M → IsInterimIR L M →
        ExpectedRevenue L M ≤ ExpectedRevenue L (flagshipMechanism L)) ↔ 2 / Real.pi ≤ L)

end

end EconCSAuction
