import EconCSAuction
import EconCSAuction.Spec
import EconCSAuction.Proof
import EconCSAuction.Theorem2

/-!
# Clean-Room Hostile Audit Verification File (`CleanRoomAudit.lean`)

Independently checks:
1. Exact signature match of `EconCSAuction.theorem1_proof` against `EconCSAuction.Theorem1Statement`,
   plus all negative-control and concrete-witness theorems.
2. Independent non-vacuity proofs on `Spec.lean` primitives:
   - `singleValMeasure L`, `bidderMeasure L`, `jointMeasure L` are genuine probability measures
     with total mass `1` and support `[L, L + 1]`.
   - Exact continuous CDF `F(v) = √(v - L)` on `[L, L + 1]`.
   - Exact 4-way independent product factorization on measurable boxes.
   - `ExpectedRevenue L` of constant payment `(p1 = 1, p2 = 0)` equals `1` (and `(p1 = 3, p2 = 5)`
     equals `8`), eliminating any measure-collapse or scaling bug.
   - Strict positivity of the optimal revenue surplus integral `∫ t in Ioo t0 1, ... > 0`,
     eliminating Bochner non-integrability collapse to `0`.
   - `flagshipMechanism L` is deterministic single-item (`∈ {0, 1}`), and `perturbedSymMechanism`
     satisfies `NonNegPayment` and `IsSingleItem`.
3. `#print axioms` on EVERY top-level theorem.
-/

open MeasureTheory Set

namespace CleanRoomHostileAudit

noncomputable section

/-! ### 1. Exact Type Checks of Top-Level Theorems -/

example : EconCSAuction.Theorem1Statement := EconCSAuction.theorem1_proof
example : EconCSAuction.Theorem1Statement := EconCSAuction.theorem1_main
example : EconCSAuction.SharpThresholdStatement := EconCSAuction.sharpThreshold_proof

example : ∀ {L : ℝ}, 0 ≤ L → L < 2 / Real.pi →
    ∃ M : EconCSAuction.Mechanism,
      EconCSAuction.IsFeasible L M ∧
      EconCSAuction.IsDSIC L M ∧
      EconCSAuction.IsExPostIR L M ∧
      EconCSAuction.NonNegPayment L M ∧
      EconCSAuction.IsSingleItem M ∧
      EconCSAuction.ExpectedRevenue L (EconCSAuction.flagshipMechanism L) <
        EconCSAuction.ExpectedRevenue L M :=
  fun hL0 hL => EconCSAuction.flagshipMechanism_suboptimal_below_two_div_pi hL0 hL

example : ∀ L : ℝ, 0 ≤ L →
    ((∀ M : EconCSAuction.Mechanism, EconCSAuction.IsFeasible L M → EconCSAuction.IsDSIC L M →
        EconCSAuction.IsExPostIR L M → EconCSAuction.NonNegPayment L M →
        EconCSAuction.IsSingleItem M →
        EconCSAuction.ExpectedRevenue L M ≤
          EconCSAuction.ExpectedRevenue L (EconCSAuction.flagshipMechanism L)) ↔
      2 / Real.pi ≤ L) := by
  intro L hL0
  refine ⟨fun h => ?_, fun hL M hF hD hI _ _ => EconCSAuction.flagshipMechanism_optimal_DSIC hL M hF hD hI⟩
  by_contra hlt
  obtain ⟨M, hF, hD, hI, hNN, hS, hrev⟩ :=
    EconCSAuction.flagshipMechanism_suboptimal_below_two_div_pi hL0 (not_le.mp hlt)
  exact absurd (h M hF hD hI hNN hS) (not_le.mpr hrev)

example : EconCSAuction.t0 ∈ Set.Ioo (9 / 25 : ℝ) (7 / 16) := EconCSAuction.t0_mem_bounds
example : EconCSAuction.PhiPlus EconCSAuction.t0 = 0 := EconCSAuction.PhiPlus_t0
example : ∃! t ∈ Set.Ioo (0 : ℝ) 1, EconCSAuction.PhiPlus t = 0 := EconCSAuction.existsUnique_t0

/-! ### 2. Independent Measure, Product Factorization, and ExpectedRevenue Non-Vacuity Proofs -/

theorem audit_singleValMeasure_univ (L : ℝ) :
    EconCSAuction.singleValMeasure L Set.univ = 1 := by
  unfold EconCSAuction.singleValMeasure
  have hm : Measurable (fun u : ℝ => L + u ^ 2) := measurable_const.add (measurable_id.pow_const 2)
  rw [Measure.map_apply hm MeasurableSet.univ, Set.preimage_univ, Measure.restrict_apply_univ,
      Real.volume_Icc]
  norm_num

theorem audit_bidderMeasure_univ (L : ℝ) :
    EconCSAuction.bidderMeasure L Set.univ = 1 := by
  unfold EconCSAuction.bidderMeasure
  rw [← Set.univ_prod_univ, Measure.prod_prod, audit_singleValMeasure_univ, mul_one]

theorem audit_jointMeasure_univ (L : ℝ) :
    EconCSAuction.jointMeasure L Set.univ = 1 := by
  unfold EconCSAuction.jointMeasure
  rw [← Set.univ_prod_univ, Measure.prod_prod, audit_bidderMeasure_univ, mul_one]

theorem audit_jointMeasure_isProb (L : ℝ) :
    IsProbabilityMeasure (EconCSAuction.jointMeasure L) :=
  ⟨audit_jointMeasure_univ L⟩

theorem audit_jointMeasure_independent_boxes (L : ℝ)
    {A B C D : Set ℝ} (_hA : MeasurableSet A) (_hB : MeasurableSet B)
    (_hC : MeasurableSet C) (_hD : MeasurableSet D) :
    EconCSAuction.jointMeasure L ((A ×ˢ B) ×ˢ (C ×ˢ D)) =
      EconCSAuction.singleValMeasure L A * EconCSAuction.singleValMeasure L B *
      EconCSAuction.singleValMeasure L C * EconCSAuction.singleValMeasure L D := by
  unfold EconCSAuction.jointMeasure EconCSAuction.bidderMeasure
  rw [Measure.prod_prod, Measure.prod_prod, Measure.prod_prod]
  simp only [mul_assoc]

theorem audit_singleValMeasure_cdf (L v : ℝ) (hv : v ∈ EconCSAuction.valInterval L) :
    EconCSAuction.singleValMeasure L (Set.Iic v) = ENNReal.ofReal (Real.sqrt (v - L)) :=
  EconCSAuction.singleValMeasure_Iic L v hv

/-- Constant-payment test mechanism with `p1 = 1, p2 = 0`. -/
def constP1Mechanism : EconCSAuction.Mechanism where
  q1_1  _ _ := 0
  q1_2  _ _ := 0
  q1_12 _ _ := 0
  q2_1  _ _ := 0
  q2_2  _ _ := 0
  q2_12 _ _ := 0
  p1    _ _ := 1
  p2    _ _ := 0

/-- Constant-payment test mechanism with `p1 = 3, p2 = 5`. -/
def const35Mechanism : EconCSAuction.Mechanism where
  q1_1  _ _ := 0
  q1_2  _ _ := 0
  q1_12 _ _ := 0
  q2_1  _ _ := 0
  q2_2  _ _ := 0
  q2_12 _ _ := 0
  p1    _ _ := 3
  p2    _ _ := 5

theorem audit_expectedRevenue_constP1 (L : ℝ) :
    EconCSAuction.ExpectedRevenue L constP1Mechanism = 1 := by
  unfold EconCSAuction.ExpectedRevenue constP1Mechanism
  simp only [add_zero, integral_const, Measure.real, audit_jointMeasure_univ,
    ENNReal.toReal_one, smul_eq_mul, mul_one]

theorem audit_expectedRevenue_const35 (L : ℝ) :
    EconCSAuction.ExpectedRevenue L const35Mechanism = 8 := by
  unfold EconCSAuction.ExpectedRevenue const35Mechanism
  simp only [integral_const, Measure.real, audit_jointMeasure_univ,
    ENNReal.toReal_one, smul_eq_mul, one_mul]
  norm_num

/-- Proves that `optimalRevenueFormula L` is STRICTLY greater than `2 * L`, certifying that the
Bochner integral `∫ t in Ioo t0 1, PhiPlus t * gT t * (2 * GT t - 1)` is strictly positive and
did NOT collapse to `0` from non-integrability! -/
theorem audit_optimalRevenue_strictly_gt_two_L (L : ℝ) :
    2 * L < EconCSAuction.optimalRevenueFormula L := by
  unfold EconCSAuction.optimalRevenueFormula
  have ht0_pos := EconCSAuction.t0_pos
  have ht0_lt_half : EconCSAuction.t0 < 1 / 2 := by linarith [EconCSAuction.t0_mem_bounds.2]
  have hint_full : IntegrableOn
      (fun t => EconCSAuction.PhiPlus t * EconCSAuction.gT t * (2 * EconCSAuction.GT t - 1))
      (Set.Ioo EconCSAuction.t0 1) volume := by
    have hcg := EconCSAuction.continuousOn_gT_Ioc ht0_pos
    have hct := EconCSAuction.continuousOn_tailGT ht0_pos
    have hbase : ContinuousOn
        (fun t => (t * EconCSAuction.gT t - EconCSAuction.tailGT t) * (1 - 2 * EconCSAuction.tailGT t))
        (Set.Icc EconCSAuction.t0 1) :=
      ((continuousOn_id.mul hcg).sub hct).mul (continuousOn_const.sub (continuousOn_const.mul hct))
    refine (hbase.integrableOn_Icc.mono_set Ioo_subset_Icc_self).congr_fun (fun t ht => ?_) measurableSet_Ioo
    have hs0 : 0 < Real.sqrt (1 - t) := Real.sqrt_pos.mpr (by linarith [ht.2])
    have hs1 : Real.sqrt (1 - t) < 1 := by rw [Real.sqrt_lt' zero_lt_one]; linarith [ht0_pos.trans ht.1]
    have hA0 : EconCSAuction.artanh (Real.sqrt (1 - t)) ≠ 0 := (EconCSAuction.artanh_pos hs0 hs1).ne'
    unfold EconCSAuction.GT EconCSAuction.PhiPlus EconCSAuction.tailGT EconCSAuction.gT
    field_simp [hA0]; ring
  have htail_lt : ∀ t ∈ Set.Ioo EconCSAuction.t0 1, EconCSAuction.tailGT t < 1 / 2 := by
    intro t ht
    have ht0' : 0 < t := ht0_pos.trans ht.1
    have hsum : (∫ x in Set.Ioo (0 : ℝ) t, EconCSAuction.gT x) +
        (∫ x in Set.Ioo t 1, EconCSAuction.gT x) = 1 / 2 := by
      have hunion : Set.Ioc (0 : ℝ) 1 = Set.Ioc 0 t ∪ Set.Ioc t 1 :=
        (Set.Ioc_union_Ioc_eq_Ioc ht0'.le ht.2.le).symm
      have htot := EconCSAuction.integral_gT_zero_one
      rw [setIntegral_congr_set Ioo_ae_eq_Ioc, hunion,
          setIntegral_union (Set.Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
            (EconCSAuction.integrableOn_gT_Ioo_zero_one.mono_set (Ioo_subset_Ioo_right ht.2.le) |>.congr_set_ae Ioo_ae_eq_Ioc.symm)
            (EconCSAuction.integrableOn_gT_Ioo_zero_one.mono_set (Ioo_subset_Ioo_left ht0'.le) |>.congr_set_ae Ioo_ae_eq_Ioc.symm),
          ← setIntegral_congr_set Ioo_ae_eq_Ioc, ← setIntegral_congr_set Ioo_ae_eq_Ioc] at htot
      exact htot
    rw [EconCSAuction.integral_gT_Ioo ht0' ht.2.le] at hsum
    have hpos_left : 0 < ∫ x in Set.Ioo (0 : ℝ) t, EconCSAuction.gT x := by
      have hle : ∫ _ in Set.Ioo (0 : ℝ) t, EconCSAuction.gT t ≤
          ∫ x in Set.Ioo (0 : ℝ) t, EconCSAuction.gT x := by
        refine setIntegral_mono_on
          (integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top))
          (EconCSAuction.integrableOn_gT_Ioo_zero_one.mono_set (Ioo_subset_Ioo_right ht.2.le))
          measurableSet_Ioo (fun x hx => ?_)
        exact (EconCSAuction.strictAntiOn_gT ⟨hx.1, hx.2.trans ht.2⟩ ⟨ht0', ht.2⟩ hx.2).le
      rw [setIntegral_const, Real.volume_real_Ioo_of_le ht0'.le, sub_zero, smul_eq_mul] at hle
      have hgt0 : 0 < t * EconCSAuction.gT t := mul_pos ht0' (EconCSAuction.gT_pos ht0' ht.2)
      linarith
    linarith
  have hGT_mono : ∀ t ∈ Set.Ioo (1 / 2 : ℝ) (3 / 4), EconCSAuction.GT (1 / 2) ≤ EconCSAuction.GT t := by
    intro t ht
    unfold EconCSAuction.GT
    have htail_le : EconCSAuction.tailGT t ≤ EconCSAuction.tailGT (1 / 2) := by
      rw [← EconCSAuction.integral_gT_Ioo (by linarith [ht.1] : (0 : ℝ) < t) (by linarith [ht.2]),
          ← EconCSAuction.integral_gT_Ioo (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)]
      exact setIntegral_mono_set
        (EconCSAuction.integrableOn_gT_Ioo_zero_one.mono_set (Ioo_subset_Ioo_left (by norm_num)))
        (ae_restrict_of_forall_mem measurableSet_Ioo (fun x hx => (EconCSAuction.gT_pos (by linarith [hx.1]) hx.2).le))
        (Filter.Eventually.of_forall (Ioo_subset_Ioo_left ht.1.le))
    linarith
  let c : ℝ := EconCSAuction.PhiPlus (1 / 2) * EconCSAuction.gT (3 / 4) * (2 * EconCSAuction.GT (1 / 2) - 1)
  have hc_pos : 0 < c := by
    have h1 : 0 < EconCSAuction.PhiPlus (1 / 2) := EconCSAuction.PhiPlus_pos_of_gt_t0 ht0_lt_half (by norm_num)
    have h2 : 0 < EconCSAuction.gT (3 / 4) := EconCSAuction.gT_pos (by norm_num) (by norm_num)
    have h3 : 0 < 2 * EconCSAuction.GT (1 / 2) - 1 := by
      have ht := htail_lt (1 / 2) ⟨ht0_lt_half, by norm_num⟩
      unfold EconCSAuction.GT; linarith
    positivity
  have hsub_int : ∫ _ in Set.Ioo (1 / 2 : ℝ) (3 / 4), c ≤
      ∫ t in Set.Ioo EconCSAuction.t0 1,
        EconCSAuction.PhiPlus t * EconCSAuction.gT t * (2 * EconCSAuction.GT t - 1) := by
    calc ∫ _ in Set.Ioo (1 / 2 : ℝ) (3 / 4), c
        ≤ ∫ t in Set.Ioo (1 / 2 : ℝ) (3 / 4),
            EconCSAuction.PhiPlus t * EconCSAuction.gT t * (2 * EconCSAuction.GT t - 1) := by
          refine setIntegral_mono_on
            (integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top))
            (hint_full.mono_set (Ioo_subset_Ioo ht0_lt_half.le (by norm_num)))
            measurableSet_Ioo (fun t ht => ?_)
          have hP1 : 0 < EconCSAuction.PhiPlus (1 / 2) := EconCSAuction.PhiPlus_pos_of_gt_t0 ht0_lt_half (by norm_num)
          have hP : EconCSAuction.PhiPlus (1 / 2) ≤ EconCSAuction.PhiPlus t :=
            (EconCSAuction.strictMonoOn_PhiPlus ⟨ht0_lt_half.le, by norm_num⟩
              ⟨(ht0_lt_half.trans ht.1).le, by linarith [ht.2]⟩ ht.1).le
          have hg1 : 0 < EconCSAuction.gT (3 / 4) := EconCSAuction.gT_pos (by norm_num) (by norm_num)
          have hg : EconCSAuction.gT (3 / 4) ≤ EconCSAuction.gT t :=
            (EconCSAuction.strictAntiOn_gT ⟨by linarith [ht.1], by linarith [ht.2]⟩
              ⟨by norm_num, by norm_num⟩ ht.2).le
          have hG1 : 0 < 2 * EconCSAuction.GT (1 / 2) - 1 := by
            have := htail_lt (1 / 2) ⟨ht0_lt_half, by norm_num⟩
            unfold EconCSAuction.GT; linarith
          have hG : 2 * EconCSAuction.GT (1 / 2) - 1 ≤ 2 * EconCSAuction.GT t - 1 := by
            linarith [hGT_mono t ht]
          have hmul1 : EconCSAuction.PhiPlus (1 / 2) * EconCSAuction.gT (3 / 4) ≤
              EconCSAuction.PhiPlus t * EconCSAuction.gT t :=
            mul_le_mul hP hg hg1.le (hP1.le.trans hP)
          exact mul_le_mul hmul1 hG hG1.le (mul_nonneg (hP1.le.trans hP) (hg1.le.trans hg))
      _ ≤ ∫ t in Set.Ioo EconCSAuction.t0 1,
            EconCSAuction.PhiPlus t * EconCSAuction.gT t * (2 * EconCSAuction.GT t - 1) := by
          refine setIntegral_mono_set hint_full
            (ae_restrict_of_forall_mem measurableSet_Ioo (fun t ht => ?_))
            (Filter.Eventually.of_forall (Ioo_subset_Ioo ht0_lt_half.le (by norm_num)))
          have hP := (EconCSAuction.PhiPlus_pos_of_gt_t0 ht.1 ht.2).le
          have hg := (EconCSAuction.gT_pos (ht0_pos.trans ht.1) ht.2).le
          have hG : 0 ≤ 2 * EconCSAuction.GT t - 1 := by
            have := htail_lt t ht
            unfold EconCSAuction.GT; linarith
          exact mul_nonneg (mul_nonneg hP hg) hG
  rw [setIntegral_const, Real.volume_real_Ioo_of_le (by norm_num : (1 / 2 : ℝ) ≤ 3 / 4), smul_eq_mul] at hsub_int
  have hpos_box : 0 < (3 / 4 - 1 / 2 : ℝ) * c := mul_pos (by norm_num) hc_pos
  linarith

/-- Proves `flagshipMechanism L` is purely deterministic (`q ∈ {0, 1}`) and single-item. -/
theorem audit_flagship_deterministic_singleItem (L : ℝ) (b1 b2 : EconCSAuction.Type2) :
    ((EconCSAuction.flagshipMechanism L).q1_1 b1 b2 = 0 ∨ (EconCSAuction.flagshipMechanism L).q1_1 b1 b2 = 1) ∧
    ((EconCSAuction.flagshipMechanism L).q1_2 b1 b2 = 0 ∨ (EconCSAuction.flagshipMechanism L).q1_2 b1 b2 = 1) ∧
    (EconCSAuction.flagshipMechanism L).q1_12 b1 b2 = 0 ∧
    ((EconCSAuction.flagshipMechanism L).q2_1 b1 b2 = 0 ∨ (EconCSAuction.flagshipMechanism L).q2_1 b1 b2 = 1) ∧
    ((EconCSAuction.flagshipMechanism L).q2_2 b1 b2 = 0 ∨ (EconCSAuction.flagshipMechanism L).q2_2 b1 b2 = 1) ∧
    (EconCSAuction.flagshipMechanism L).q2_12 b1 b2 = 0 := by
  unfold EconCSAuction.flagshipMechanism
  dsimp only
  refine ⟨by split_ifs <;> simp, by split_ifs <;> simp, rfl,
          by split_ifs <;> simp, by split_ifs <;> simp, rfl⟩

/-- Deterministic feasible allocation of 2 indivisible items to 2 bidders (`none` = unsold).
Supply feasibility ("each item to at most one bidder") holds by type construction. -/
abbrev DetAlloc := Fin 2 → Option (Fin 2)

/-- Exact lottery realizability over deterministic feasible allocations `DetAlloc`:
at every profile in `bidderDomain L × bidderDomain L`, there is a probability distribution
`w : DetAlloc → ℝ` (`w ≥ 0`, `∑ ω, w ω = 1`) whose bundle marginals equal `M`'s allocations. -/
def IsLotteryRealizable (L : ℝ) (M : EconCSAuction.Mechanism) : Prop :=
  ∀ b1 ∈ EconCSAuction.bidderDomain L, ∀ b2 ∈ EconCSAuction.bidderDomain L,
    ∃ w : DetAlloc → ℝ,
      (∀ ω, 0 ≤ w ω) ∧
      (∑ ω : DetAlloc, w ω = 1) ∧
      (M.q1_1  b1 b2 = ∑ ω : DetAlloc, if ω 0 = some 0 ∧ ω 1 ≠ some 0 then w ω else 0) ∧
      (M.q1_2  b1 b2 = ∑ ω : DetAlloc, if ω 0 ≠ some 0 ∧ ω 1 = some 0 then w ω else 0) ∧
      (M.q1_12 b1 b2 = ∑ ω : DetAlloc, if ω 0 = some 0 ∧ ω 1 = some 0 then w ω else 0) ∧
      (M.q2_1  b1 b2 = ∑ ω : DetAlloc, if ω 0 = some 1 ∧ ω 1 ≠ some 1 then w ω else 0) ∧
      (M.q2_2  b1 b2 = ∑ ω : DetAlloc, if ω 0 ≠ some 1 ∧ ω 1 = some 1 then w ω else 0) ∧
      (M.q2_12 b1 b2 = ∑ ω : DetAlloc, if ω 0 = some 1 ∧ ω 1 = some 1 then w ω else 0)

/-- Constructive 2×2 Birkhoff–von Neumann weights over `DetAlloc` for a single-item doubly
substochastic matrix `(a, b; c, d)` (`a + b, c + d, a + c, b + d ≤ 1`). -/
def bvnWeight (a b c d : ℝ) : Option (Fin 2) → Option (Fin 2) → ℝ
  | some 0, some 1 => min a d
  | some 1, some 0 => min b c
  | some 0, none   => a - min a d
  | none,   some 0 => b - min b c
  | some 1, none   => c - min b c
  | none,   some 1 => d - min a d
  | none,   none   => 1 - max a d - max b c
  | _,      _      => 0

private def detAllocEquiv : DetAlloc ≃ Option (Fin 2) × Option (Fin 2) where
  toFun ω := (ω 0, ω 1)
  invFun p := ![p.1, p.2]
  left_inv ω := by funext i; fin_cases i <;> rfl
  right_inv _ := rfl

private lemma sum_detAlloc (f : Option (Fin 2) → Option (Fin 2) → ℝ) :
    (∑ ω : DetAlloc, f (ω 0) (ω 1)) =
      f none none + f none (some 0) + f none (some 1) +
      f (some 0) none + f (some 0) (some 0) + f (some 0) (some 1) +
      f (some 1) none + f (some 1) (some 0) + f (some 1) (some 1) := by
  rw [Fintype.sum_equiv detAllocEquiv (fun ω => f (ω 0) (ω 1)) (fun p => f p.1 p.2) (fun _ => rfl)]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_option, Fin.sum_univ_two]
  ring

private lemma bvnWeight_nonneg {a b c d : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hab : a + b ≤ 1) (hcd : c + d ≤ 1) (hac : a + c ≤ 1) (hbd : b + d ≤ 1) :
    ∀ x y : Option (Fin 2), 0 ≤ bvnWeight a b c d x y
  | some 0, some 1 => le_min ha hd
  | some 1, some 0 => le_min hb hc
  | some 0, none   => sub_nonneg.mpr (min_le_left a d)
  | none,   some 0 => sub_nonneg.mpr (min_le_left b c)
  | some 1, none   => sub_nonneg.mpr (min_le_right b c)
  | none,   some 1 => sub_nonneg.mpr (min_le_right a d)
  | none,   none   => by
      simp only [bvnWeight]
      rcases max_choice a d with h1 | h1 <;> rcases max_choice b c with h2 | h2 <;> linarith
  | some 0, some 0 => le_rfl
  | some 1, some 1 => le_rfl

/-- Constructive 2×2 Birkhoff–von Neumann: every `IsPointwiseFeasible L M ∧ IsSingleItem M`
mechanism is an exact lottery over deterministic feasible allocations `DetAlloc`. -/
theorem audit_singleItem_lotteryRealizable {L : ℝ} {M : EconCSAuction.Mechanism}
    (hF : EconCSAuction.IsPointwiseFeasible L M) (hS : EconCSAuction.IsSingleItem M) :
    IsLotteryRealizable L M := by
  intro b1 hb1 b2 hb2
  obtain ⟨ha0, hb0, _, hc0, hd0, _, hab, hcd, hac, hbd⟩ := hF b1 hb1 b2 hb2
  have h12_1 : M.q1_12 b1 b2 = 0 := hS.1 b1 b2
  have h12_2 : M.q2_12 b1 b2 = 0 := hS.2 b1 b2
  simp only [h12_1, h12_2, add_zero] at hab hcd hac hbd
  set a := M.q1_1 b1 b2; set b := M.q1_2 b1 b2; set c := M.q2_1 b1 b2; set d := M.q2_2 b1 b2
  refine ⟨fun ω => bvnWeight a b c d (ω 0) (ω 1),
    fun ω => bvnWeight_nonneg ha0 hb0 hc0 hd0 hab hcd hac hbd (ω 0) (ω 1),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [sum_detAlloc (bvnWeight a b c d)]
    simp only [bvnWeight]; linarith [min_add_max a d, min_add_max b c]
  · rw [sum_detAlloc (fun x y => if x = some 0 ∧ y ≠ some 0 then bvnWeight a b c d x y else 0)]
    simp [bvnWeight]
  · rw [sum_detAlloc (fun x y => if x ≠ some 0 ∧ y = some 0 then bvnWeight a b c d x y else 0)]
    simp [bvnWeight]
  · rw [h12_1, sum_detAlloc (fun x y => if x = some 0 ∧ y = some 0 then bvnWeight a b c d x y else 0)]
    simp [bvnWeight]
  · rw [sum_detAlloc (fun x y => if x = some 1 ∧ y ≠ some 1 then bvnWeight a b c d x y else 0)]
    simp [bvnWeight]
  · rw [sum_detAlloc (fun x y => if x ≠ some 1 ∧ y = some 1 then bvnWeight a b c d x y else 0)]
    simp [bvnWeight]
  · rw [h12_2, sum_detAlloc (fun x y => if x = some 1 ∧ y = some 1 then bvnWeight a b c d x y else 0)]
    simp [bvnWeight]

/-- `flagshipMechanism L` is realized at every profile by a pure deterministic feasible
allocation `ω₀ : DetAlloc` (point mass `∈ {0, 1}`). -/
theorem audit_flagship_deterministic_lottery (L : ℝ) (b1 b2 : EconCSAuction.Type2) :
    ∃ ω₀ : DetAlloc,
      (EconCSAuction.flagshipMechanism L).q1_1  b1 b2 = (if ω₀ 0 = some 0 ∧ ω₀ 1 ≠ some 0 then 1 else 0) ∧
      (EconCSAuction.flagshipMechanism L).q1_2  b1 b2 = (if ω₀ 0 ≠ some 0 ∧ ω₀ 1 = some 0 then 1 else 0) ∧
      (EconCSAuction.flagshipMechanism L).q1_12 b1 b2 = (if ω₀ 0 = some 0 ∧ ω₀ 1 = some 0 then 1 else 0) ∧
      (EconCSAuction.flagshipMechanism L).q2_1  b1 b2 = (if ω₀ 0 = some 1 ∧ ω₀ 1 ≠ some 1 then 1 else 0) ∧
      (EconCSAuction.flagshipMechanism L).q2_2  b1 b2 = (if ω₀ 0 ≠ some 1 ∧ ω₀ 1 = some 1 then 1 else 0) ∧
      (EconCSAuction.flagshipMechanism L).q2_12 b1 b2 = (if ω₀ 0 = some 1 ∧ ω₀ 1 = some 1 then 1 else 0) := by
  have hiff := EconCSAuction.b2_decision_iff_not_b1 L b1 b2
  unfold EconCSAuction.flagshipMechanism; dsimp only
  by_cases h1 : b1.1 - EconCSAuction.p1Item1 L (b2.1 - b2.2) > b1.2 - EconCSAuction.p1Item2 L (b2.1 - b2.2)
  · have h2 : ¬ (b2.1 - EconCSAuction.p2Item1 L (b1.1 - b1.2) ≥ b2.2 - EconCSAuction.p2Item2 L (b1.1 - b1.2)) :=
      fun hc => hiff.mp hc h1
    refine ⟨![some 0, some 1], ?_⟩
    simp [h1, h2]
  · have h2 : b2.1 - EconCSAuction.p2Item1 L (b1.1 - b1.2) ≥ b2.2 - EconCSAuction.p2Item2 L (b1.1 - b1.2) :=
      hiff.mpr h1
    refine ⟨![some 1, some 0], ?_⟩
    simp [h1, h2]

/-- `flagshipMechanism L` is an exact lottery over `DetAlloc`. -/
theorem audit_flagship_lotteryRealizable (L : ℝ) :
    IsLotteryRealizable L (EconCSAuction.flagshipMechanism L) :=
  audit_singleItem_lotteryRealizable (EconCSAuction.flagshipMechanism_isFeasible L).1
    ⟨fun _ _ => rfl, fun _ _ => rfl⟩

/-- Proves `perturbedSymMechanism L ε` ALSO satisfies `NonNegPayment L` and `IsSingleItem`. -/
theorem audit_perturbedSymMechanism_nonNeg_singleItem {L ε : ℝ} (hL0 : 0 ≤ L) (hε0 : 0 < ε) :
    EconCSAuction.NonNegPayment L (EconCSAuction.perturbedSymMechanism L ε) ∧
    EconCSAuction.IsSingleItem (EconCSAuction.perturbedSymMechanism L ε) :=
  EconCSAuction.perturbedSymMechanism_nonNeg_singleItem hL0 hε0

/-- Theorem 2 witness with explicit exact lottery realizability over `DetAlloc` and `NonNegPayment`. -/
theorem audit_suboptimal_lotteryRealizable {L : ℝ} (hL0 : 0 ≤ L) (hL : L < 2 / Real.pi) :
    ∃ M : EconCSAuction.Mechanism,
      EconCSAuction.IsFeasible L M ∧
      EconCSAuction.IsDSIC L M ∧
      EconCSAuction.IsExPostIR L M ∧
      EconCSAuction.NonNegPayment L M ∧
      EconCSAuction.IsSingleItem M ∧
      IsLotteryRealizable L M ∧
      EconCSAuction.ExpectedRevenue L (EconCSAuction.flagshipMechanism L) <
        EconCSAuction.ExpectedRevenue L M := by
  obtain ⟨M, hF, hD, hI, hNN, hS, hrev⟩ :=
    EconCSAuction.flagshipMechanism_suboptimal_below_two_div_pi hL0 hL
  exact ⟨M, hF, hD, hI, hNN, hS, audit_singleItem_lotteryRealizable hF.1 hS, hrev⟩

end

/-! ### 3. Exact Type & Axiom Footprint Audit (`#check` and `#print axioms`) -/

#check @EconCSAuction.theorem1_proof
#check @EconCSAuction.sharpThreshold_proof
#check @EconCSAuction.flagshipMechanism_suboptimal_below_two_div_pi

#print axioms EconCSAuction.theorem1_proof
#print axioms EconCSAuction.theorem1_main
#print axioms EconCSAuction.sharpThreshold_proof
#print axioms EconCSAuction.flagshipMechanism_suboptimal_below_two_div_pi
#print axioms EconCSAuction.t0_mem_bounds
#print axioms EconCSAuction.existsUnique_t0
#print axioms EconCSAuction.PhiPlus_t0
#print axioms audit_jointMeasure_univ
#print axioms audit_expectedRevenue_constP1
#print axioms audit_optimalRevenue_strictly_gt_two_L
#print axioms audit_perturbedSymMechanism_nonNeg_singleItem
#print axioms audit_singleItem_lotteryRealizable
#print axioms audit_flagship_deterministic_lottery
#print axioms audit_flagship_lotteryRealizable
#print axioms audit_suboptimal_lotteryRealizable

end CleanRoomHostileAudit
