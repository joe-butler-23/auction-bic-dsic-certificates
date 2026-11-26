import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Strict Separation of DSIC and BIC Optimal Revenue for 2 Bidders, 2 Items, i.i.d. U[0, 1]

This file defines the continuous 2-bidder, 2-item additive-valuation auction setting with
independent valuations uniformly distributed on `[0, 1]² × [0, 1]²`, and states the target
separation theorem (`MainGoal`).

DO NOT MODIFY THIS FILE.
-/

open MeasureTheory

namespace AuctionSep

/-- Type space for a single bidder with additive valuations for 2 items. -/
abbrev Type2 := ℝ × ℝ

/-- Unit square `[0, 1]²` (support of each bidder's valuation). -/
def unitSquare : Set Type2 := Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1

/-- Joint type profile domain `[0, 1]² × [0, 1]²` (Lebesgue measure 1). -/
def profileDomain : Set (Type2 × Type2) := unitSquare ×ˢ unitSquare

/-- A direct revelation mechanism for 2 bidders and 2 items. -/
structure Mechanism where
  /-- Allocation probability of item 1 to bidder 1. -/
  q11 : Type2 → Type2 → ℝ
  /-- Allocation probability of item 2 to bidder 1. -/
  q12 : Type2 → Type2 → ℝ
  /-- Allocation probability of item 1 to bidder 2. -/
  q21 : Type2 → Type2 → ℝ
  /-- Allocation probability of item 2 to bidder 2. -/
  q22 : Type2 → Type2 → ℝ
  /-- Payment of bidder 1. -/
  t1 : Type2 → Type2 → ℝ
  /-- Payment of bidder 2. -/
  t2 : Type2 → Type2 → ℝ

/-- Ex-post supply feasibility on `[0, 1]² × [0, 1]²` and joint Lebesgue integrability. -/
def IsFeasible (M : Mechanism) : Prop :=
  (∀ x ∈ unitSquare, ∀ y ∈ unitSquare,
    0 ≤ M.q11 x y ∧ 0 ≤ M.q21 x y ∧ M.q11 x y + M.q21 x y ≤ 1 ∧
    0 ≤ M.q12 x y ∧ 0 ≤ M.q22 x y ∧ M.q12 x y + M.q22 x y ≤ 1) ∧
  IntegrableOn (fun p : Type2 × Type2 => M.q11 p.1 p.2) profileDomain volume ∧
  IntegrableOn (fun p : Type2 × Type2 => M.q12 p.1 p.2) profileDomain volume ∧
  IntegrableOn (fun p : Type2 × Type2 => M.q21 p.1 p.2) profileDomain volume ∧
  IntegrableOn (fun p : Type2 × Type2 => M.q22 p.1 p.2) profileDomain volume ∧
  IntegrableOn (fun p : Type2 × Type2 => M.t1 p.1 p.2) profileDomain volume ∧
  IntegrableOn (fun p : Type2 × Type2 => M.t2 p.1 p.2) profileDomain volume

/-- Ex-post utility of bidder 1 with true type `x` reporting `x'` against opponent `y`. -/
def u1Report (M : Mechanism) (x x' y : Type2) : ℝ :=
  x.1 * M.q11 x' y + x.2 * M.q12 x' y - M.t1 x' y

/-- Ex-post utility of bidder 2 with true type `y` reporting `y'` against opponent `x`. -/
def u2Report (M : Mechanism) (x y y' : Type2) : ℝ :=
  y.1 * M.q21 x y' + y.2 * M.q22 x y' - M.t2 x y'

/-- Dominant-Strategy Incentive Compatibility (DSIC) on `[0, 1]² × [0, 1]²`. -/
def IsDSIC (M : Mechanism) : Prop :=
  (∀ x ∈ unitSquare, ∀ x' ∈ unitSquare, ∀ y ∈ unitSquare,
    u1Report M x x' y ≤ u1Report M x x y) ∧
  (∀ x ∈ unitSquare, ∀ y ∈ unitSquare, ∀ y' ∈ unitSquare,
    u2Report M x y y' ≤ u2Report M x y y)

/-- Ex-post Individual Rationality (IR) on `[0, 1]² × [0, 1]²`. -/
def IsExPostIR (M : Mechanism) : Prop :=
  ∀ x ∈ unitSquare, ∀ y ∈ unitSquare,
    0 ≤ u1Report M x x y ∧ 0 ≤ u2Report M x y y

/-- Interim allocation of item 1 to bidder 1. -/
noncomputable def Q11 (M : Mechanism) (x : Type2) : ℝ := ∫ y in unitSquare, M.q11 x y

/-- Interim allocation of item 2 to bidder 1. -/
noncomputable def Q12 (M : Mechanism) (x : Type2) : ℝ := ∫ y in unitSquare, M.q12 x y

/-- Interim payment of bidder 1. -/
noncomputable def T1 (M : Mechanism) (x : Type2) : ℝ := ∫ y in unitSquare, M.t1 x y

/-- Interim allocation of item 1 to bidder 2. -/
noncomputable def Q21 (M : Mechanism) (y : Type2) : ℝ := ∫ x in unitSquare, M.q21 x y

/-- Interim allocation of item 2 to bidder 2. -/
noncomputable def Q22 (M : Mechanism) (y : Type2) : ℝ := ∫ x in unitSquare, M.q22 x y

/-- Interim payment of bidder 2. -/
noncomputable def T2 (M : Mechanism) (y : Type2) : ℝ := ∫ x in unitSquare, M.t2 x y

/-- Bayesian Incentive Compatibility (BIC), including genuine slice integrability. -/
def IsBIC (M : Mechanism) : Prop :=
  (∀ x ∈ unitSquare,
    IntegrableOn (fun y => M.q11 x y) unitSquare volume ∧
    IntegrableOn (fun y => M.q12 x y) unitSquare volume ∧
    IntegrableOn (fun y => M.t1 x y) unitSquare volume) ∧
  (∀ y ∈ unitSquare,
    IntegrableOn (fun x => M.q21 x y) unitSquare volume ∧
    IntegrableOn (fun x => M.q22 x y) unitSquare volume ∧
    IntegrableOn (fun x => M.t2 x y) unitSquare volume) ∧
  (∀ x ∈ unitSquare, ∀ x' ∈ unitSquare,
    x.1 * Q11 M x' + x.2 * Q12 M x' - T1 M x' ≤ x.1 * Q11 M x + x.2 * Q12 M x - T1 M x) ∧
  (∀ y ∈ unitSquare, ∀ y' ∈ unitSquare,
    y.1 * Q21 M y' + y.2 * Q22 M y' - T2 M y' ≤ y.1 * Q21 M y + y.2 * Q22 M y - T2 M y)

/-- Interim Individual Rationality (IR). -/
def IsInterimIR (M : Mechanism) : Prop :=
  (∀ x ∈ unitSquare, 0 ≤ x.1 * Q11 M x + x.2 * Q12 M x - T1 M x) ∧
  (∀ y ∈ unitSquare, 0 ≤ y.1 * Q21 M y + y.2 * Q22 M y - T2 M y)

/-- Expected total seller revenue under i.i.d. `U[0, 1]² × U[0, 1]²` valuations. -/
noncomputable def ExpectedRevenue (M : Mechanism) : ℝ :=
  ∫ p in profileDomain, (M.t1 p.1 p.2 + M.t2 p.1 p.2)

/--
Main Target Statement:
There exists a feasible, BIC, interim-IR mechanism `M_bic` and a real threshold `c` strictly
below `ExpectedRevenue M_bic` such that EVERY feasible, DSIC, ex-post-IR mechanism `M_dsic`
has `ExpectedRevenue M_dsic ≤ c`.
-/
def MainGoal : Prop :=
  ∃ (M_bic : Mechanism) (c : ℝ),
    IsFeasible M_bic ∧ IsBIC M_bic ∧ IsInterimIR M_bic ∧
    c < ExpectedRevenue M_bic ∧
    ∀ M_dsic : Mechanism,
      IsFeasible M_dsic → IsDSIC M_dsic → IsExPostIR M_dsic →
        ExpectedRevenue M_dsic ≤ c

end AuctionSep
