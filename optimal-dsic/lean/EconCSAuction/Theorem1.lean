import EconCSAuction.Lemma5Sharp

/-!
# Theorem 1: Global Revenue Optimality of `(g⋆, p⋆)` Over ALL Randomized BIC & DSIC Mechanisms

Assembles Lemmas 1–5 to prove the complete, unconditional, zero-gap Theorem 1:
For EVERY real `L ≥ 2/π`, the explicit deterministic posted-price auction `flagshipMechanism L` is:
- feasible (`IsFeasible`),
- exact DSIC (`IsDSIC`),
- exact ex-post IR (`IsExPostIR`),
- strictly positive-transfer (`NonNegPayment`, `BoundedPayment` in `[L, L + 1]`),
- achieves `ExpectedRevenue L (flagshipMechanism L) = optimalRevenueFormula L`,
- and is **globally revenue-optimal over ALL measurable randomized 4-bundle BIC + interim IR
  (and hence ALL DSIC + ex-post IR) mechanisms**!
-/

open MeasureTheory Set

namespace EconCSAuction

noncomputable section

/-! ### 1. Exact 2×2 Doubly-Substochastic Matching LP Dual Certificate -/

/-- For any nonnegative weights `a, b, c, d ≥ 0` with `b + c ≤ a + d` and any doubly substochastic
matrix `(g11, g12, g21, g22)`, `a g11 + b g12 + c g21 + d g22 ≤ a + d`.
(5-line elementary LP dual witness: `v1 = min a c`, `u2 = c - v1`, `u1 = a - v1`, `v2 = d - u2`.) -/
lemma matching_bound_diag {a b c d g11 g12 g21 g22 : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (hdiag : b + c ≤ a + d)
    (hg11 : 0 ≤ g11) (hg12 : 0 ≤ g12) (hg21 : 0 ≤ g21) (hg22 : 0 ≤ g22)
    (hr1 : g11 + g12 ≤ 1) (hr2 : g21 + g22 ≤ 1) (hc1 : g11 + g21 ≤ 1) (hc2 : g12 + g22 ≤ 1) :
    a * g11 + b * g12 + c * g21 + d * g22 ≤ a + d := by
  let v1 : ℝ := min a c
  let u2 : ℝ := c - v1
  let u1 : ℝ := a - v1
  let v2 : ℝ := d - u2
  have hv1_nn : 0 ≤ v1 := le_min ha hc
  have hu1_nn : 0 ≤ u1 := sub_nonneg.mpr (min_le_left a c)
  have hu2_nn : 0 ≤ u2 := sub_nonneg.mpr (min_le_right a c)
  have hv2_nn : 0 ≤ v2 := by
    dsimp only [v2, u2, v1]
    rcases le_total a c with hac | hca
    · rw [min_eq_left hac]; linarith
    · rw [min_eq_right hca]; linarith
  have h11 : a ≤ u1 + v1 := by dsimp only [u1]; linarith
  have h12 : b ≤ u1 + v2 := by dsimp only [u1, v2, u2]; linarith
  have h21 : c ≤ u2 + v1 := by dsimp only [u2]; linarith
  have h22 : d ≤ u2 + v2 := by dsimp only [v2]; linarith
  calc a * g11 + b * g12 + c * g21 + d * g22
      ≤ (u1 + v1) * g11 + (u1 + v2) * g12 + (u2 + v1) * g21 + (u2 + v2) * g22 := by gcongr
    _ = u1 * (g11 + g12) + u2 * (g21 + g22) + v1 * (g11 + g21) + v2 * (g12 + g22) := by ring
    _ ≤ u1 * 1 + u2 * 1 + v1 * 1 + v2 * 1 := by gcongr
    _ = a + d := by dsimp only [u1, u2, v1, v2]; ring

/-- Pointwise dominance of `flagshipMechanism L` on the wing virtual-surplus objective over ANY
single-item doubly substochastic allocation `(g11, g12, g21, g22)`. -/
lemma pointwise_wing_dominance {L : ℝ} (hL : 0 ≤ L) {ab1 ab2 : Type2}
    (h1 : ab1 ∈ (wingPos ∪ wingNeg) ∪ stripSet) (h2 : ab2 ∈ (wingPos ∪ wingNeg) ∪ stripSet)
    {g11 g12 g21 g22 : ℝ}
    (hg11 : 0 ≤ g11) (hg12 : 0 ≤ g12) (hg21 : 0 ≤ g21) (hg22 : 0 ≤ g22)
    (hr1 : g11 + g12 ≤ 1) (hr2 : g21 + g22 ≤ 1) (hc1 : g11 + g21 ≤ 1) (hc2 : g12 + g22 ≤ 1) :
    phi1Wing L ab1 * g11 + phi2Wing L ab1 * g12 + phi1Wing L ab2 * g21 + phi2Wing L ab2 * g22 ≤
      phi1Wing L ab1 * (flagshipMechanism L).q1_1 (L + ab1.1, L + ab1.2) (L + ab2.1, L + ab2.2) +
      phi2Wing L ab1 * (flagshipMechanism L).q1_2 (L + ab1.1, L + ab1.2) (L + ab2.1, L + ab2.2) +
      phi1Wing L ab2 * (flagshipMechanism L).q2_1 (L + ab1.1, L + ab1.2) (L + ab2.1, L + ab2.2) +
      phi2Wing L ab2 * (flagshipMechanism L).q2_2 (L + ab1.1, L + ab1.2) (L + ab2.1, L + ab2.2) := by
  have hzero_strip : ∀ ab ∈ stripSet, phi1Wing L ab = 0 ∧ phi2Wing L ab = 0 := by
    intro ab hab
    have h1 : ¬ t0 < ab.1 - ab.2 := not_lt.mpr hab.2.2.le
    have h2 : ¬ t0 < ab.2 - ab.1 := not_lt.mpr (by have h := hab.2.1; dsimp only [mem_ofPred_eq] at h; linarith)
    unfold phi1Wing phi2Wing
    simp [h1, h2]
  have hopen1 : ab1 ∈ openUnitSquare := by
    rcases h1 with (hp | hm) | hs
    · exact hp.1
    · exact hm.1
    · exact hs.1
  have hopen2 : ab2 ∈ openUnitSquare := by
    rcases h2 with (hp | hm) | hs
    · exact hp.1
    · exact hm.1
    · exact hs.1
  have ht1_Ioo : (L + ab1.1, L + ab1.2).1 - (L + ab1.1, L + ab1.2).2 ∈ Ioo (-1 : ℝ) 1 := by
    dsimp only
    have : (L + ab1.1) - (L + ab1.2) = ab1.1 - ab1.2 := by ring
    rw [this]; exact ⟨by linarith [hopen1.1.1, hopen1.2.2], by linarith [hopen1.1.2, hopen1.2.1]⟩
  have ht2_Ioo : (L + ab2.1, L + ab2.2).1 - (L + ab2.1, L + ab2.2).2 ∈ Ioo (-1 : ℝ) 1 := by
    dsimp only
    have : (L + ab2.1) - (L + ab2.2) = ab2.1 - ab2.2 := by ring
    rw [this]; exact ⟨by linarith [hopen2.1.1, hopen2.2.2], by linarith [hopen2.1.2, hopen2.2.1]⟩
  have hdec1_raw := b1_decision_iff_PhiBar (L := L) (b1 := (L + ab1.1, L + ab1.2)) (b2 := (L + ab2.1, L + ab2.2)) ht1_Ioo ht2_Ioo
  dsimp only at hdec1_raw
  have hdec2 := b2_decision_iff_not_b1 L (L + ab1.1, L + ab1.2) (L + ab2.1, L + ab2.2)
  have hsub1 : (L + ab1.1) - (L + ab1.2) = ab1.1 - ab1.2 := by ring
  have hsub2 : (L + ab2.1) - (L + ab2.2) = ab2.1 - ab2.2 := by ring
  have hdec1 : ((L + ab1.1) - p1Item1 L ((L + ab2.1) - (L + ab2.2)) >
      (L + ab1.2) - p1Item2 L ((L + ab2.1) - (L + ab2.2))) ↔
      PhiBar (ab2.1 - ab2.2) < PhiBar (ab1.1 - ab1.2) := by
    rw [hdec1_raw, hsub1, hsub2]
  -- Case split on whether `ab1`, `ab2` are in `W_+ ∪ W_-` or `S`:
  rcases h1 with hw1 | hs1 <;> rcases h2 with hw2 | hs2
  · -- Case 1: BOTH `ab1, ab2 ∈ W_+ ∪ W_-`
    have hpos1 := phiWing_gt_L L hw1
    have hpos2 := phiWing_gt_L L hw2
    have hdiff1 := phi1Wing_sub_phi2Wing L hw1
    have hdiff2 := phi1Wing_sub_phi2Wing L hw2
    have ha : 0 ≤ phi1Wing L ab1 := by linarith [hpos1.1]
    have hb : 0 ≤ phi2Wing L ab1 := by linarith [hpos1.2]
    have hc : 0 ≤ phi1Wing L ab2 := by linarith [hpos2.1]
    have hd : 0 ≤ phi2Wing L ab2 := by linarith [hpos2.2]
    unfold flagshipMechanism; dsimp only
    by_cases hwin : (L + ab1.1) - p1Item1 L ((L + ab2.1) - (L + ab2.2)) >
        (L + ab1.2) - p1Item2 L ((L + ab2.1) - (L + ab2.2))
    · have hnot2 : ¬ ((L + ab2.1) - p2Item1 L ((L + ab1.1) - (L + ab1.2)) ≥
          (L + ab2.2) - p2Item2 L ((L + ab1.1) - (L + ab1.2))) := fun h => (hdec2.mp h) hwin
      simp only [hwin, hnot2, ite_true, ite_false, mul_one, mul_zero, add_zero, zero_add]
      have hphi_lt : PhiBar (ab2.1 - ab2.2) < PhiBar (ab1.1 - ab1.2) := hdec1.mp hwin
      have hdiag : phi2Wing L ab1 + phi1Wing L ab2 ≤ phi1Wing L ab1 + phi2Wing L ab2 := by linarith
      exact matching_bound_diag ha hb hc hd hdiag hg11 hg12 hg21 hg22 hr1 hr2 hc1 hc2
    · have hwin2 : (L + ab2.1) - p2Item1 L ((L + ab1.1) - (L + ab1.2)) ≥
          (L + ab2.2) - p2Item2 L ((L + ab1.1) - (L + ab1.2)) := hdec2.mpr hwin
      simp only [hwin, hwin2, ite_true, ite_false, mul_one, mul_zero, add_zero, zero_add]
      have hphi_le : PhiBar (ab1.1 - ab1.2) ≤ PhiBar (ab2.1 - ab2.2) := not_lt.mp (fun h => hwin (hdec1.mpr h))
      have hdiag : phi1Wing L ab1 + phi2Wing L ab2 ≤ phi2Wing L ab1 + phi1Wing L ab2 := by linarith
      have hm := matching_bound_diag hb ha hd hc hdiag hg12 hg11 hg22 hg21
        (by linarith) (by linarith) (by linarith) (by linarith)
      linarith
  · -- Case 2: `ab1 ∈ W_+ ∪ W_-`, `ab2 ∈ S`
    rcases hzero_strip ab2 hs2 with ⟨hz21, hz22⟩
    rw [hz21, hz22]; simp only [zero_mul, add_zero]
    have hpos1 := phiWing_gt_L L hw1
    have hdiff1 := phi1Wing_sub_phi2Wing L hw1
    have hP2 : PhiBar (ab2.1 - ab2.2) = 0 := PhiBar_zero_of_abs_le hs2.2.1.le hs2.2.2.le
    unfold flagshipMechanism; dsimp only
    rcases hw1 with hp1 | hm1
    · have hP1_pos : 0 < PhiBar (ab1.1 - ab1.2) := PhiBar_pos_of_gt hp1.2.1 hp1.2.2
      have hwin : (L + ab1.1) - p1Item1 L ((L + ab2.1) - (L + ab2.2)) >
          (L + ab1.2) - p1Item2 L ((L + ab2.1) - (L + ab2.2)) := hdec1.mpr (by linarith)
      simp only [hwin, ite_true, mul_one, mul_zero, add_zero]
      have hgt : phi2Wing L ab1 ≤ phi1Wing L ab1 := by linarith
      nlinarith [hpos1.1]
    · have hm1_1 : t0 < ab1.2 - ab1.1 := hm1.2.1
      have hm1_2 : ab1.2 - ab1.1 < 1 := hm1.2.2
      have hP1_neg : PhiBar (ab1.1 - ab1.2) < 0 := PhiBar_neg_of_lt (by linarith) (by linarith)
      have hnot : ¬ ((L + ab1.1) - p1Item1 L ((L + ab2.1) - (L + ab2.2)) >
          (L + ab1.2) - p1Item2 L ((L + ab2.1) - (L + ab2.2))) := fun h => by linarith [hdec1.mp h]
      simp only [hnot, ite_false, mul_one, mul_zero, zero_add]
      have hgt : phi1Wing L ab1 ≤ phi2Wing L ab1 := by linarith
      nlinarith [hpos1.2]
  · -- Case 3: `ab1 ∈ S`, `ab2 ∈ W_+ ∪ W_-`
    rcases hzero_strip ab1 hs1 with ⟨hz11, hz12⟩
    rw [hz11, hz12]; simp only [zero_mul, zero_add]
    have hpos2 := phiWing_gt_L L hw2
    have hdiff2 := phi1Wing_sub_phi2Wing L hw2
    have hP1 : PhiBar (ab1.1 - ab1.2) = 0 := PhiBar_zero_of_abs_le hs1.2.1.le hs1.2.2.le
    unfold flagshipMechanism; dsimp only
    rcases hw2 with hp2 | hm2
    · have hP2_pos : 0 < PhiBar (ab2.1 - ab2.2) := PhiBar_pos_of_gt hp2.2.1 hp2.2.2
      have hnot1 : ¬ ((L + ab1.1) - p1Item1 L ((L + ab2.1) - (L + ab2.2)) >
          (L + ab1.2) - p1Item2 L ((L + ab2.1) - (L + ab2.2))) := fun h => by linarith [hdec1.mp h]
      have hwin2 := hdec2.mpr hnot1
      simp only [hwin2, ite_true, mul_one, mul_zero, add_zero]
      have hgt : phi2Wing L ab2 ≤ phi1Wing L ab2 := by linarith
      nlinarith [hpos2.1]
    · have hm2_1 : t0 < ab2.2 - ab2.1 := hm2.2.1
      have hm2_2 : ab2.2 - ab2.1 < 1 := hm2.2.2
      have hP2_neg : PhiBar (ab2.1 - ab2.2) < 0 := PhiBar_neg_of_lt (by linarith) (by linarith)
      have hwin1 : (L + ab1.1) - p1Item1 L ((L + ab2.1) - (L + ab2.2)) >
          (L + ab1.2) - p1Item2 L ((L + ab2.1) - (L + ab2.2)) := hdec1.mpr (by linarith)
      have hnot2 : ¬ ((L + ab2.1) - p2Item1 L ((L + ab1.1) - (L + ab1.2)) ≥
          (L + ab2.2) - p2Item2 L ((L + ab1.1) - (L + ab1.2))) := fun h => (hdec2.mp h) hwin1
      simp only [hnot2, ite_false, mul_one, mul_zero, zero_add]
      have hgt : phi1Wing L ab2 ≤ phi2Wing L ab2 := by linarith
      nlinarith [hpos2.2]
  · -- Case 4: BOTH `ab1, ab2 ∈ S`
    rcases hzero_strip ab1 hs1 with ⟨hz11, hz12⟩
    rcases hzero_strip ab2 hs2 with ⟨hz21, hz22⟩
    simp [hz11, hz12, hz21, hz22]

/-! ### 2. Extracting `InterimProfile` from Any Single-Item BIC + Interim IR Mechanism -/

/-- Shifted Bidder 1 interim profile of a feasible single-item BIC + interim-IR mechanism. -/
def bidder1Profile (L : ℝ) (M : Mechanism)
    (hF : IsFeasible L M) (hS : IsSingleItem M) (hB : IsBIC L M) (hIR : IsInterimIR L M) :
    InterimProfile where
  u ab := (L + ab.1) * Q1_1 L M (L + ab.1, L + ab.2) +
    (L + ab.2) * Q1_2 L M (L + ab.1, L + ab.2) - P1 L M (L + ab.1, L + ab.2)
  g1 ab := Q1_1 L M (L + ab.1, L + ab.2)
  g2 ab := Q1_2 L M (L + ab.1, L + ab.2)
  u_nonneg ab hab := by
    have hv : (L + ab.1, L + ab.2) ∈ bidderDomain L :=
      ⟨⟨by linarith [hab.1.1], by linarith [hab.1.2]⟩, ⟨by linarith [hab.2.1], by linarith [hab.2.2]⟩⟩
    have h := hIR.1 (L + ab.1, L + ab.2) hv
    have h12 : Q1_12 L M (L + ab.1, L + ab.2) = 0 := by unfold Q1_12; simp [hS.1]
    unfold UnitDemandVal at h; rw [h12] at h; linarith
  g1_nonneg ab hab := by
    have hv : (L + ab.1, L + ab.2) ∈ bidderDomain L :=
      ⟨⟨by linarith [hab.1.1], by linarith [hab.1.2]⟩, ⟨by linarith [hab.2.1], by linarith [hab.2.2]⟩⟩
    unfold Q1_1; refine integral_nonneg_of_ae ?_
    filter_upwards [ae_mem_bidderDomain L] with v2 hv2
    exact (hF.1 _ hv v2 hv2).1
  g2_nonneg ab hab := by
    have hv : (L + ab.1, L + ab.2) ∈ bidderDomain L :=
      ⟨⟨by linarith [hab.1.1], by linarith [hab.1.2]⟩, ⟨by linarith [hab.2.1], by linarith [hab.2.2]⟩⟩
    unfold Q1_2; refine integral_nonneg_of_ae ?_
    filter_upwards [ae_mem_bidderDomain L] with v2 hv2
    exact (hF.1 _ hv v2 hv2).2.1
  g_sum_le ab hab := by
    have hv : (L + ab.1, L + ab.2) ∈ bidderDomain L :=
      ⟨⟨by linarith [hab.1.1], by linarith [hab.1.2]⟩, ⟨by linarith [hab.2.1], by linarith [hab.2.2]⟩⟩
    rcases (slice_q_integrable hF).1 _ hv with ⟨hi1, hi2, _⟩
    unfold Q1_1 Q1_2
    rw [← integral_add hi1 hi2]
    calc ∫ b2, (M.q1_1 (L + ab.1, L + ab.2) b2 + M.q1_2 (L + ab.1, L + ab.2) b2) ∂(bidderMeasure L)
        ≤ ∫ _ , (1 : ℝ) ∂(bidderMeasure L) := by
          refine integral_mono_ae (hi1.add hi2) (integrable_const 1) ?_
          filter_upwards [ae_mem_bidderDomain L] with v2 hv2
          have hsum := (hF.1 _ hv v2 hv2).2.2.2.2.2.2.1
          rw [hS.1] at hsum; linarith
      _ = 1 := by simp [probReal_univ]
  bic ab hab ab' hab' := by
    have hv : (L + ab.1, L + ab.2) ∈ bidderDomain L :=
      ⟨⟨by linarith [hab.1.1], by linarith [hab.1.2]⟩, ⟨by linarith [hab.2.1], by linarith [hab.2.2]⟩⟩
    have hv' : (L + ab'.1, L + ab'.2) ∈ bidderDomain L :=
      ⟨⟨by linarith [hab'.1.1], by linarith [hab'.1.2]⟩, ⟨by linarith [hab'.2.1], by linarith [hab'.2.2]⟩⟩
    have h := hB.2.2.1 _ hv _ hv'
    have h12 : Q1_12 L M (L + ab.1, L + ab.2) = 0 := by unfold Q1_12; simp [hS.1]
    have h12' : Q1_12 L M (L + ab'.1, L + ab'.2) = 0 := by unfold Q1_12; simp [hS.1]
    unfold UnitDemandVal at h; rw [h12, h12'] at h; linarith
  g1_meas := by
    have hm : StronglyMeasurable (fun v1 : Type2 => Q1_1 L M v1) :=
      hF.2.1.stronglyMeasurable.integral_prod_right
    exact hm.measurable.comp ((measurable_const.add measurable_fst).prodMk (measurable_const.add measurable_snd))
  g2_meas := by
    have hm : StronglyMeasurable (fun v1 : Type2 => Q1_2 L M v1) :=
      hF.2.2.1.stronglyMeasurable.integral_prod_right
    exact hm.measurable.comp ((measurable_const.add measurable_fst).prodMk (measurable_const.add measurable_snd))

/-- Shifted Bidder 2 interim profile of a feasible single-item BIC + interim-IR mechanism. -/
def bidder2Profile (L : ℝ) (M : Mechanism)
    (hF : IsFeasible L M) (hS : IsSingleItem M) (hB : IsBIC L M) (hIR : IsInterimIR L M) :
    InterimProfile where
  u ab := (L + ab.1) * Q2_1 L M (L + ab.1, L + ab.2) +
    (L + ab.2) * Q2_2 L M (L + ab.1, L + ab.2) - P2 L M (L + ab.1, L + ab.2)
  g1 ab := Q2_1 L M (L + ab.1, L + ab.2)
  g2 ab := Q2_2 L M (L + ab.1, L + ab.2)
  u_nonneg ab hab := by
    have hv : (L + ab.1, L + ab.2) ∈ bidderDomain L :=
      ⟨⟨by linarith [hab.1.1], by linarith [hab.1.2]⟩, ⟨by linarith [hab.2.1], by linarith [hab.2.2]⟩⟩
    have h := hIR.2 (L + ab.1, L + ab.2) hv
    have h12 : Q2_12 L M (L + ab.1, L + ab.2) = 0 := by unfold Q2_12; simp [hS.2]
    unfold UnitDemandVal at h; rw [h12] at h; linarith
  g1_nonneg ab hab := by
    have hv : (L + ab.1, L + ab.2) ∈ bidderDomain L :=
      ⟨⟨by linarith [hab.1.1], by linarith [hab.1.2]⟩, ⟨by linarith [hab.2.1], by linarith [hab.2.2]⟩⟩
    unfold Q2_1; refine integral_nonneg_of_ae ?_
    filter_upwards [ae_mem_bidderDomain L] with v1 hv1
    exact (hF.1 v1 hv1 _ hv).2.2.2.1
  g2_nonneg ab hab := by
    have hv : (L + ab.1, L + ab.2) ∈ bidderDomain L :=
      ⟨⟨by linarith [hab.1.1], by linarith [hab.1.2]⟩, ⟨by linarith [hab.2.1], by linarith [hab.2.2]⟩⟩
    unfold Q2_2; refine integral_nonneg_of_ae ?_
    filter_upwards [ae_mem_bidderDomain L] with v1 hv1
    exact (hF.1 v1 hv1 _ hv).2.2.2.2.1
  g_sum_le ab hab := by
    have hv : (L + ab.1, L + ab.2) ∈ bidderDomain L :=
      ⟨⟨by linarith [hab.1.1], by linarith [hab.1.2]⟩, ⟨by linarith [hab.2.1], by linarith [hab.2.2]⟩⟩
    rcases (slice_q_integrable hF).2 _ hv with ⟨hi1, hi2, _⟩
    unfold Q2_1 Q2_2
    rw [← integral_add hi1 hi2]
    calc ∫ b1, (M.q2_1 b1 (L + ab.1, L + ab.2) + M.q2_2 b1 (L + ab.1, L + ab.2)) ∂(bidderMeasure L)
        ≤ ∫ _ , (1 : ℝ) ∂(bidderMeasure L) := by
          refine integral_mono_ae (hi1.add hi2) (integrable_const 1) ?_
          filter_upwards [ae_mem_bidderDomain L] with v1 hv1
          have hsum := (hF.1 v1 hv1 _ hv).2.2.2.2.2.2.2.1
          rw [hS.2] at hsum; linarith
      _ = 1 := by simp [probReal_univ]
  bic ab hab ab' hab' := by
    have hv : (L + ab.1, L + ab.2) ∈ bidderDomain L :=
      ⟨⟨by linarith [hab.1.1], by linarith [hab.1.2]⟩, ⟨by linarith [hab.2.1], by linarith [hab.2.2]⟩⟩
    have hv' : (L + ab'.1, L + ab'.2) ∈ bidderDomain L :=
      ⟨⟨by linarith [hab'.1.1], by linarith [hab'.1.2]⟩, ⟨by linarith [hab'.2.1], by linarith [hab'.2.2]⟩⟩
    have h := hB.2.2.2 _ hv _ hv'
    have h12 : Q2_12 L M (L + ab.1, L + ab.2) = 0 := by unfold Q2_12; simp [hS.2]
    have h12' : Q2_12 L M (L + ab'.1, L + ab'.2) = 0 := by unfold Q2_12; simp [hS.2]
    unfold UnitDemandVal at h; rw [h12, h12'] at h; linarith
  g1_meas := by
    have hm : StronglyMeasurable (fun v2 : Type2 => Q2_1 L M v2) :=
      hF.2.2.2.2.1.stronglyMeasurable.integral_prod_left
    exact hm.measurable.comp ((measurable_const.add measurable_fst).prodMk (measurable_const.add measurable_snd))
  g2_meas := by
    have hm : StronglyMeasurable (fun v2 : Type2 => Q2_2 L M v2) :=
      hF.2.2.2.2.2.1.stronglyMeasurable.integral_prod_left
    exact hm.measurable.comp ((measurable_const.add measurable_fst).prodMk (measurable_const.add measurable_snd))

lemma measurable_phiWing (L : ℝ) : Measurable (phi1Wing L) ∧ Measurable (phi2Wing L) := by
  constructor
  · unfold phi1Wing z1WingTS z2WingTS wWingTS Hwing tailGT gT artanh Iwing rho
    exact Measurable.ite (measurableSet_lt measurable_const (measurable_fst.sub measurable_snd)) (by fun_prop)
      (Measurable.ite (measurableSet_lt measurable_const (measurable_snd.sub measurable_fst)) (by fun_prop) measurable_const)
  · unfold phi2Wing z1WingTS z2WingTS wWingTS Hwing tailGT gT artanh Iwing rho
    exact Measurable.ite (measurableSet_lt measurable_const (measurable_fst.sub measurable_snd)) (by fun_prop)
      (Measurable.ite (measurableSet_lt measurable_const (measurable_snd.sub measurable_fst)) (by fun_prop) measurable_const)

lemma phi2Wing_eq_phi1Wing_swap (L : ℝ) (ab : Type2) :
    phi2Wing L ab = phi1Wing L (ab.2, ab.1) := by
  unfold phi1Wing phi2Wing; dsimp only
  by_cases h1 : t0 < ab.1 - ab.2
  · have h2 : ¬ t0 < ab.2 - ab.1 := by linarith [t0_pos]
    simp [h1, h2]
  · by_cases h2 : t0 < ab.2 - ab.1
    · simp [h1, h2]
    · simp [h1, h2]

lemma integrable_phiWing_bidderMeasure (L : ℝ) :
    Integrable (fun v : Type2 => phi1Wing L (v.1 - L, v.2 - L)) (bidderMeasure L) ∧
    Integrable (fun v : Type2 => phi2Wing L (v.1 - L, v.2 - L)) (bidderMeasure L) := by
  have hphi_meas := measurable_phiWing L
  let Cz : ℝ := 1 / (4 * t0) + 1 / (4 * t0 * Real.sqrt t0)
  have hsub_meas : Measurable (fun v : Type2 => (v.1 - L, v.2 - L)) :=
    (measurable_fst.sub measurable_const).prodMk (measurable_snd.sub measurable_const)
  have hdom : IntegrableOn (fun ab : Type2 => Cz + (|L| + 2) * rho ab.1 ab.2) openUnitSquare volume := by
    have hvol : volume openUnitSquare ≠ ⊤ := by
      unfold openUnitSquare
      rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ioo]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    exact (integrableOn_const (hs := hvol)).add (integrableOn_rho_openUnitSquare.const_mul (|L| + 2))
  have hbound_pos : ∀ {a b : ℝ}, a ∈ Ioo (0 : ℝ) 1 → b ∈ Ioo (0 : ℝ) 1 → t0 < a - b →
      |(L + a - z1WingTS (a - b) b / rho a b) * rho a b| ≤ Cz + (|L| + 2) * rho a b ∧
      |(L + b - z2WingTS (a - b) b / rho a b) * rho a b| ≤ Cz + (|L| + 2) * rho a b := by
    intro a b ha hb hp
    have hrho_pos : 0 < rho a b := rho_pos ha.1 hb.1
    have ht1 : a - b < 1 := by linarith [ha.2, hb.1]
    have hz2 := z2WingTS_abs_le hp.le ht1 hb.1.le (by linarith [ha.2])
    have hH_le : Hwing (a - b) ≤ 1 := (Hwing_le_one_sub (t0_pos.trans hp) ht1).trans (by linarith [t0_pos])
    have hH_nn : 0 ≤ Hwing (a - b) := (Hwing_pos (t0_pos.trans hp) ht1).le
    have hz1 : |z1WingTS (a - b) b| ≤ Cz + rho a b := by
      unfold z1WingTS wWingTS
      have hs : b + (a - b) = a := by ring
      rw [hs]
      calc _ ≤ |z2WingTS (a - b) b| + |Hwing (a - b) * rho a b| := abs_add_le _ _
        _ ≤ Cz + 1 * rho a b := by rw [abs_of_nonneg (mul_nonneg hH_nn hrho_pos.le)]; gcongr
        _ = Cz + rho a b := by ring
    have hL1 : |L + a| ≤ |L| + 1 := (abs_add_le _ _).trans (by rw [abs_of_nonneg ha.1.le]; linarith [ha.2])
    have hL2 : |L + b| ≤ |L| + 1 := (abs_add_le _ _).trans (by rw [abs_of_nonneg hb.1.le]; linarith [hb.2])
    have h1 : (L + a - z1WingTS (a - b) b / rho a b) * rho a b = (L + a) * rho a b - z1WingTS (a - b) b := by
      field_simp [hrho_pos.ne']
    have h2 : (L + b - z2WingTS (a - b) b / rho a b) * rho a b = (L + b) * rho a b - z2WingTS (a - b) b := by
      field_simp [hrho_pos.ne']
    rw [h1, h2]
    constructor
    · calc |(L + a) * rho a b - z1WingTS (a - b) b|
          ≤ |L + a| * rho a b + |z1WingTS (a - b) b| := by
            have := abs_sub ((L + a) * rho a b) (z1WingTS (a - b) b)
            rwa [abs_mul, abs_of_nonneg hrho_pos.le] at this
        _ ≤ (|L| + 1) * rho a b + (Cz + rho a b) := by gcongr
        _ = Cz + (|L| + 2) * rho a b := by ring
    · calc |(L + b) * rho a b - z2WingTS (a - b) b|
          ≤ |L + b| * rho a b + |z2WingTS (a - b) b| := by
            have := abs_sub ((L + b) * rho a b) (z2WingTS (a - b) b)
            rwa [abs_mul, abs_of_nonneg hrho_pos.le] at this
        _ ≤ (|L| + 1) * rho a b + Cz := by gcongr
        _ ≤ Cz + (|L| + 2) * rho a b := by linarith [hrho_pos]
  have hint1 : Integrable (fun v : Type2 => phi1Wing L (v.1 - L, v.2 - L)) (bidderMeasure L) := by
    have hm1 : AEStronglyMeasurable (fun v : Type2 => phi1Wing L (v.1 - L, v.2 - L)) (bidderMeasure L) :=
      (hphi_meas.1.comp hsub_meas).aestronglyMeasurable
    rw [integrable_bidderMeasure_iff hm1]
    have hm_int1 : AEStronglyMeasurable
        (fun ab : Type2 => phi1Wing L (L + ab.1 - L, L + ab.2 - L) * rho ab.1 ab.2)
        (volume.restrict openUnitSquare) :=
      ((hphi_meas.1.comp (((measurable_const.add measurable_fst).sub measurable_const).prodMk
        ((measurable_const.add measurable_snd).sub measurable_const))).mul
        (by unfold rho; fun_prop : Measurable (fun ab : Type2 => rho ab.1 ab.2))).aestronglyMeasurable
    refine hdom.mono' hm_int1 ?_
    rw [ae_restrict_iff' measurableSet_openUnitSquare]; filter_upwards with ab hab
    simp only [add_sub_cancel_left, Real.norm_eq_abs]
    unfold phi1Wing
    by_cases hp : t0 < ab.1 - ab.2
    · rw [if_pos hp]; exact (hbound_pos hab.1 hab.2 hp).1
    · by_cases hm : t0 < ab.2 - ab.1
      · rw [if_neg hp, if_pos hm]
        have hrc : rho ab.2 ab.1 = rho ab.1 ab.2 := by unfold rho; rw [mul_comm ab.2 ab.1]
        rw [← hrc]; exact (hbound_pos hab.2 hab.1 hm).2
      · rw [if_neg hp, if_neg hm, zero_mul, abs_zero]
        have hCz : 0 ≤ Cz := by have := t0_pos; positivity
        have hrho_pos : 0 < rho ab.1 ab.2 := rho_pos hab.1.1 hab.2.1
        nlinarith [abs_nonneg L]
  refine ⟨hint1, ?_⟩
  have hcomp := ((measurePreserving_swap_bidderMeasure L).integrable_comp_emb
    MeasurableEquiv.prodComm.measurableEmbedding).mpr hint1
  exact hcomp.congr (ae_of_all _ (fun v => by
    simp only [Function.comp_apply, Prod.fst_swap, Prod.snd_swap]
    exact (phi2Wing_eq_phi1Wing_swap L (v.1 - L, v.2 - L)).symm))

/-- Joint integrability of the four wing virtual-surplus terms `phi_j * q_{i,j}` for any feasible mechanism. -/
lemma integrable_wing_terms {L : ℝ} {M : Mechanism} (hF : IsFeasible L M) :
    Integrable (fun x : Type2 × Type2 => phi1Wing L (x.1.1 - L, x.1.2 - L) * M.q1_1 x.1 x.2) (jointMeasure L) ∧
    Integrable (fun x : Type2 × Type2 => phi2Wing L (x.1.1 - L, x.1.2 - L) * M.q1_2 x.1 x.2) (jointMeasure L) ∧
    Integrable (fun x : Type2 × Type2 => phi1Wing L (x.2.1 - L, x.2.2 - L) * M.q2_1 x.1 x.2) (jointMeasure L) ∧
    Integrable (fun x : Type2 × Type2 => phi2Wing L (x.2.1 - L, x.2.2 - L) * M.q2_2 x.1 x.2) (jointMeasure L) := by
  have hphi_meas := measurable_phiWing L
  have hphi_int := integrable_phiWing_bidderMeasure L
  have hsub : Measurable (fun v : Type2 => (v.1 - L, v.2 - L)) :=
    (measurable_fst.sub measurable_const).prodMk (measurable_snd.sub measurable_const)
  have mk1 : ∀ {φ : Type2 → ℝ} {q : Type2 → Type2 → ℝ},
      Measurable φ → Integrable (fun v : Type2 => φ (v.1 - L, v.2 - L)) (bidderMeasure L) →
      Measurable (Function.uncurry q) →
      (∀ v1 ∈ bidderDomain L, ∀ v2 ∈ bidderDomain L, 0 ≤ q v1 v2 ∧ q v1 v2 ≤ 1) →
      Integrable (fun x : Type2 × Type2 => φ (x.1.1 - L, x.1.2 - L) * q x.1 x.2) (jointMeasure L) := by
    intro φ q hφm hφi hqm hqb
    refine (hφi.abs.mul_prod (integrable_const (1 : ℝ))).mono'
      ((hφm.comp (hsub.comp measurable_fst)).mul hqm).aestronglyMeasurable ?_
    filter_upwards [ae_mem_profileDomain L] with x hx
    have h := hqb x.1 hx.1 x.2 hx.2
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h.1]
    exact mul_le_mul_of_nonneg_left h.2 (abs_nonneg _)
  have mk2 : ∀ {φ : Type2 → ℝ} {q : Type2 → Type2 → ℝ},
      Measurable φ → Integrable (fun v : Type2 => φ (v.1 - L, v.2 - L)) (bidderMeasure L) →
      Measurable (Function.uncurry q) →
      (∀ v1 ∈ bidderDomain L, ∀ v2 ∈ bidderDomain L, 0 ≤ q v1 v2 ∧ q v1 v2 ≤ 1) →
      Integrable (fun x : Type2 × Type2 => φ (x.2.1 - L, x.2.2 - L) * q x.1 x.2) (jointMeasure L) := by
    intro φ q hφm hφi hqm hqb
    refine ((integrable_const (1 : ℝ)).mul_prod hφi.abs).mono'
      ((hφm.comp (hsub.comp measurable_snd)).mul hqm).aestronglyMeasurable ?_
    filter_upwards [ae_mem_profileDomain L] with x hx
    have h := hqb x.1 hx.1 x.2 hx.2
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h.1, one_mul]
    exact (mul_le_mul_of_nonneg_left h.2 (abs_nonneg _)).trans (by rw [mul_one])
  refine ⟨mk1 hphi_meas.1 hphi_int.1 hF.2.1 (fun v1 h1 v2 h2 => ?_),
          mk1 hphi_meas.2 hphi_int.2 hF.2.2.1 (fun v1 h1 v2 h2 => ?_),
          mk2 hphi_meas.1 hphi_int.1 hF.2.2.2.2.1 (fun v1 h1 v2 h2 => ?_),
          mk2 hphi_meas.2 hphi_int.2 hF.2.2.2.2.2.1 (fun v1 h1 v2 h2 => ?_)⟩
  · have hq := hF.1 v1 h1 v2 h2; exact ⟨hq.1, by linarith [hq.2.1, hq.2.2.1, hq.2.2.2.2.2.2.1]⟩
  · have hq := hF.1 v1 h1 v2 h2; exact ⟨hq.2.1, by linarith [hq.1, hq.2.2.1, hq.2.2.2.2.2.2.1]⟩
  · have hq := hF.1 v1 h1 v2 h2; exact ⟨hq.2.2.2.1, by linarith [hq.2.2.2.2.1, hq.2.2.2.2.2.1, hq.2.2.2.2.2.2.2.1]⟩
  · have hq := hF.1 v1 h1 v2 h2; exact ⟨hq.2.2.2.2.1, by linarith [hq.2.2.2.1, hq.2.2.2.2.2.1, hq.2.2.2.2.2.2.2.1]⟩

/-- Dual revenue identity for ANY feasible single-item BIC + interim-IR mechanism `M`:
`ExpectedRevenue L M = stripFunctional L P1 + stripFunctional L P2 + E_{joint}[wingVirtualSurplus M]`. -/
lemma dual_revenue_identity {L : ℝ} {M : Mechanism}
    (hF : IsFeasible L M) (hS : IsSingleItem M) (hB : IsBIC L M) (hIR : IsInterimIR L M) :
    ExpectedRevenue L M =
      stripFunctional L (bidder1Profile L M hF hS hB hIR) +
      stripFunctional L (bidder2Profile L M hF hS hB hIR) +
      ∫ x, (phi1Wing L (x.1.1 - L, x.1.2 - L) * M.q1_1 x.1 x.2 +
            phi2Wing L (x.1.1 - L, x.1.2 - L) * M.q1_2 x.1 x.2 +
            phi1Wing L (x.2.1 - L, x.2.2 - L) * M.q2_1 x.1 x.2 +
            phi2Wing L (x.2.1 - L, x.2.2 - L) * M.q2_2 x.1 x.2) ∂(jointMeasure L) := by
  let P1p := bidder1Profile L M hF hS hB hIR
  let P2p := bidder2Profile L M hF hS hB hIR
  have hp1_int : Integrable (fun x : Type2 × Type2 => M.p1 x.1 x.2) (jointMeasure L) :=
    hF.2.2.2.2.2.2.2.2.2.1
  have hp2_int : Integrable (fun x : Type2 × Type2 => M.p2 x.1 x.2) (jointMeasure L) :=
    hF.2.2.2.2.2.2.2.2.2.2
  -- Express `E[p1]` and `E[p2]` via `lemma4_wing_decomposition`
  have hp1_eq : ∫ x, M.p1 x.1 x.2 ∂(jointMeasure L) =
      (∫ ab in (wingPos ∪ wingNeg), (phi1Wing L ab * P1p.g1 ab + phi2Wing L ab * P1p.g2 ab) * rho ab.1 ab.2) +
      stripFunctional L P1p := by
    unfold jointMeasure
    rw [integral_prod _ hp1_int]
    have hP1_meas : AEStronglyMeasurable (P1 L M) (bidderMeasure L) :=
      hp1_int.integral_prod_left.aestronglyMeasurable
    change ∫ v1, P1 L M v1 ∂(bidderMeasure L) = _
    rw [integral_bidderMeasure_eq hP1_meas]
    have hcongr : ∀ ab ∈ openUnitSquare,
        P1 L M (L + ab.1, L + ab.2) * rho ab.1 ab.2 =
        ((L + ab.1) * P1p.g1 ab + (L + ab.2) * P1p.g2 ab - P1p.u ab) * rho ab.1 ab.2 := by
      intro ab _; dsimp only [P1p, bidder1Profile]; ring
    rw [setIntegral_congr_fun measurableSet_openUnitSquare hcongr]
    exact lemma4_wing_decomposition L P1p
  have hp2_eq : ∫ x, M.p2 x.1 x.2 ∂(jointMeasure L) =
      (∫ ab in (wingPos ∪ wingNeg), (phi1Wing L ab * P2p.g1 ab + phi2Wing L ab * P2p.g2 ab) * rho ab.1 ab.2) +
      stripFunctional L P2p := by
    unfold jointMeasure
    rw [integral_prod_symm _ hp2_int]
    have hP2_meas : AEStronglyMeasurable (P2 L M) (bidderMeasure L) :=
      hp2_int.integral_prod_right.aestronglyMeasurable
    change ∫ v2, P2 L M v2 ∂(bidderMeasure L) = _
    rw [integral_bidderMeasure_eq hP2_meas]
    have hcongr : ∀ ab ∈ openUnitSquare,
        P2 L M (L + ab.1, L + ab.2) * rho ab.1 ab.2 =
        ((L + ab.1) * P2p.g1 ab + (L + ab.2) * P2p.g2 ab - P2p.u ab) * rho ab.1 ab.2 := by
      intro ab _; dsimp only [P2p, bidder2Profile]; ring
    rw [setIntegral_congr_fun measurableSet_openUnitSquare hcongr]
    exact lemma4_wing_decomposition L P2p
  -- Rewrite each bidder's wing integral as a `jointMeasure L` integral via Fubini!
  have hphi_meas := measurable_phiWing L
  have hsub_meas : Measurable (fun v : Type2 => (v.1 - L, v.2 - L)) :=
    (measurable_fst.sub measurable_const).prodMk (measurable_snd.sub measurable_const)
  rcases integrable_wing_terms hF with ⟨hj11, hj12, hj21, hj22⟩
  -- Helper: `∫ ab in wingPos ∪ wingNeg, (phi1 * g1 + phi2 * g2) * rho = ∫ ab in openUnitSquare, (phi1 * g1 + phi2 * g2) * rho`!
  have hwing_eq_open : ∀ g1 g2 : Type2 → ℝ,
      (∫ ab in (wingPos ∪ wingNeg), (phi1Wing L ab * g1 ab + phi2Wing L ab * g2 ab) * rho ab.1 ab.2) =
      ∫ ab in openUnitSquare, (phi1Wing L ab * g1 ab + phi2Wing L ab * g2 ab) * rho ab.1 ab.2 := by
    intro g1 g2
    have hsub_open : wingPos ∪ wingNeg ⊆ openUnitSquare := union_subset Set.inter_subset_left Set.inter_subset_left
    have hzero_out : ∀ ab ∈ openUnitSquare \ (wingPos ∪ wingNeg),
        (phi1Wing L ab * g1 ab + phi2Wing L ab * g2 ab) * rho ab.1 ab.2 = 0 := by
      intro ab hab
      have h1 : ¬ t0 < ab.1 - ab.2 := fun h =>
        hab.2 (Or.inl ⟨hab.1, h, show ab.1 - ab.2 < 1 by linarith [hab.1.1.2, hab.1.2.1]⟩)
      have h2 : ¬ t0 < ab.2 - ab.1 := fun h =>
        hab.2 (Or.inr ⟨hab.1, h, show ab.2 - ab.1 < 1 by linarith [hab.1.1.1, hab.1.2.2]⟩)
      unfold phi1Wing phi2Wing; simp [h1, h2]
    rw [← inter_eq_right.mpr hsub_open, ← setIntegral_indicator (measurableSet_wingPos.union measurableSet_wingNeg)]
    refine setIntegral_congr_fun measurableSet_openUnitSquare (fun ab hab => ?_)
    by_cases hw : ab ∈ wingPos ∪ wingNeg
    · rw [indicator_of_mem hw]
    · rw [indicator_of_notMem hw]; exact (hzero_out ab ⟨hab, hw⟩).symm
  -- Equate each of the 4 joint integrals to its 1-bidder wing integral!
  have hw1_eq : (∫ ab in (wingPos ∪ wingNeg), (phi1Wing L ab * P1p.g1 ab + phi2Wing L ab * P1p.g2 ab) * rho ab.1 ab.2) =
      (∫ x, phi1Wing L (x.1.1 - L, x.1.2 - L) * M.q1_1 x.1 x.2 ∂(jointMeasure L)) +
      (∫ x, phi2Wing L (x.1.1 - L, x.1.2 - L) * M.q1_2 x.1 x.2 ∂(jointMeasure L)) := by
    rw [hwing_eq_open]
    unfold jointMeasure
    rw [integral_prod _ hj11, integral_prod _ hj12]
    have h1 : (∫ v1, ∫ v2, phi1Wing L (v1.1 - L, v1.2 - L) * M.q1_1 v1 v2 ∂(bidderMeasure L) ∂(bidderMeasure L)) =
        ∫ ab in openUnitSquare, phi1Wing L ab * P1p.g1 ab * rho ab.1 ab.2 := by
      have hrew : ∀ v1 : Type2, (∫ v2, phi1Wing L (v1.1 - L, v1.2 - L) * M.q1_1 v1 v2 ∂(bidderMeasure L)) =
          phi1Wing L (v1.1 - L, v1.2 - L) * Q1_1 L M v1 := fun v1 => integral_const_mul _ _
      simp_rw [hrew]
      have hm : AEStronglyMeasurable (fun v1 : Type2 => phi1Wing L (v1.1 - L, v1.2 - L) * Q1_1 L M v1) (bidderMeasure L) :=
        ((hphi_meas.1.comp hsub_meas).mul hF.2.1.stronglyMeasurable.integral_prod_right.measurable).aestronglyMeasurable
      rw [integral_bidderMeasure_eq hm]
      refine setIntegral_congr_fun measurableSet_openUnitSquare (fun ab _ => by simp [P1p, bidder1Profile])
    have h2 : (∫ v1, ∫ v2, phi2Wing L (v1.1 - L, v1.2 - L) * M.q1_2 v1 v2 ∂(bidderMeasure L) ∂(bidderMeasure L)) =
        ∫ ab in openUnitSquare, phi2Wing L ab * P1p.g2 ab * rho ab.1 ab.2 := by
      have hrew : ∀ v1 : Type2, (∫ v2, phi2Wing L (v1.1 - L, v1.2 - L) * M.q1_2 v1 v2 ∂(bidderMeasure L)) =
          phi2Wing L (v1.1 - L, v1.2 - L) * Q1_2 L M v1 := fun v1 => integral_const_mul _ _
      simp_rw [hrew]
      have hm : AEStronglyMeasurable (fun v1 : Type2 => phi2Wing L (v1.1 - L, v1.2 - L) * Q1_2 L M v1) (bidderMeasure L) :=
        ((hphi_meas.2.comp hsub_meas).mul hF.2.2.1.stronglyMeasurable.integral_prod_right.measurable).aestronglyMeasurable
      rw [integral_bidderMeasure_eq hm]
      refine setIntegral_congr_fun measurableSet_openUnitSquare (fun ab _ => by simp [P1p, bidder1Profile])
    rw [h1, h2]
    have hi1 : IntegrableOn (fun ab : Type2 => phi1Wing L ab * P1p.g1 ab * rho ab.1 ab.2) openUnitSquare volume := by
      have hm1 : AEStronglyMeasurable (fun v1 : Type2 => phi1Wing L (v1.1 - L, v1.2 - L) * Q1_1 L M v1) (bidderMeasure L) :=
        ((hphi_meas.1.comp hsub_meas).mul hF.2.1.stronglyMeasurable.integral_prod_right.measurable).aestronglyMeasurable
      have hint1 : Integrable (fun v1 : Type2 => phi1Wing L (v1.1 - L, v1.2 - L) * Q1_1 L M v1) (bidderMeasure L) :=
        hj11.integral_prod_left.congr (ae_of_all _ (fun v1 => by dsimp only; exact integral_const_mul _ _))
      have h := (integrable_bidderMeasure_iff hm1).mp hint1
      exact h.congr_fun (fun ab _ => by simp [P1p, bidder1Profile]) measurableSet_openUnitSquare
    have hi2 : IntegrableOn (fun ab : Type2 => phi2Wing L ab * P1p.g2 ab * rho ab.1 ab.2) openUnitSquare volume := by
      have hm2 : AEStronglyMeasurable (fun v1 : Type2 => phi2Wing L (v1.1 - L, v1.2 - L) * Q1_2 L M v1) (bidderMeasure L) :=
        ((hphi_meas.2.comp hsub_meas).mul hF.2.2.1.stronglyMeasurable.integral_prod_right.measurable).aestronglyMeasurable
      have hint2 : Integrable (fun v1 : Type2 => phi2Wing L (v1.1 - L, v1.2 - L) * Q1_2 L M v1) (bidderMeasure L) :=
        hj12.integral_prod_left.congr (ae_of_all _ (fun v1 => by dsimp only; exact integral_const_mul _ _))
      have h := (integrable_bidderMeasure_iff hm2).mp hint2
      exact h.congr_fun (fun ab _ => by simp [P1p, bidder1Profile]) measurableSet_openUnitSquare
    rw [← integral_add hi1 hi2]
    refine setIntegral_congr_fun measurableSet_openUnitSquare (fun ab _ => by ring)
  have hw2_eq : (∫ ab in (wingPos ∪ wingNeg), (phi1Wing L ab * P2p.g1 ab + phi2Wing L ab * P2p.g2 ab) * rho ab.1 ab.2) =
      (∫ x, phi1Wing L (x.2.1 - L, x.2.2 - L) * M.q2_1 x.1 x.2 ∂(jointMeasure L)) +
      (∫ x, phi2Wing L (x.2.1 - L, x.2.2 - L) * M.q2_2 x.1 x.2 ∂(jointMeasure L)) := by
    rw [hwing_eq_open]
    unfold jointMeasure
    rw [integral_prod_symm _ hj21, integral_prod_symm _ hj22]
    have h1 : (∫ v2, ∫ v1, phi1Wing L (v2.1 - L, v2.2 - L) * M.q2_1 v1 v2 ∂(bidderMeasure L) ∂(bidderMeasure L)) =
        ∫ ab in openUnitSquare, phi1Wing L ab * P2p.g1 ab * rho ab.1 ab.2 := by
      have hrew : ∀ v2 : Type2, (∫ v1, phi1Wing L (v2.1 - L, v2.2 - L) * M.q2_1 v1 v2 ∂(bidderMeasure L)) =
          phi1Wing L (v2.1 - L, v2.2 - L) * Q2_1 L M v2 := fun v2 => integral_const_mul _ _
      simp_rw [hrew]
      have hm : AEStronglyMeasurable (fun v2 : Type2 => phi1Wing L (v2.1 - L, v2.2 - L) * Q2_1 L M v2) (bidderMeasure L) :=
        ((hphi_meas.1.comp hsub_meas).mul hF.2.2.2.2.1.stronglyMeasurable.integral_prod_left.measurable).aestronglyMeasurable
      rw [integral_bidderMeasure_eq hm]
      refine setIntegral_congr_fun measurableSet_openUnitSquare (fun ab _ => by simp [P2p, bidder2Profile])
    have h2 : (∫ v2, ∫ v1, phi2Wing L (v2.1 - L, v2.2 - L) * M.q2_2 v1 v2 ∂(bidderMeasure L) ∂(bidderMeasure L)) =
        ∫ ab in openUnitSquare, phi2Wing L ab * P2p.g2 ab * rho ab.1 ab.2 := by
      have hrew : ∀ v2 : Type2, (∫ v1, phi2Wing L (v2.1 - L, v2.2 - L) * M.q2_2 v1 v2 ∂(bidderMeasure L)) =
          phi2Wing L (v2.1 - L, v2.2 - L) * Q2_2 L M v2 := fun v2 => integral_const_mul _ _
      simp_rw [hrew]
      have hm : AEStronglyMeasurable (fun v2 : Type2 => phi2Wing L (v2.1 - L, v2.2 - L) * Q2_2 L M v2) (bidderMeasure L) :=
        ((hphi_meas.2.comp hsub_meas).mul hF.2.2.2.2.2.1.stronglyMeasurable.integral_prod_left.measurable).aestronglyMeasurable
      rw [integral_bidderMeasure_eq hm]
      refine setIntegral_congr_fun measurableSet_openUnitSquare (fun ab _ => by simp [P2p, bidder2Profile])
    rw [h1, h2]
    have hi1 : IntegrableOn (fun ab : Type2 => phi1Wing L ab * P2p.g1 ab * rho ab.1 ab.2) openUnitSquare volume := by
      have hm1 : AEStronglyMeasurable (fun v2 : Type2 => phi1Wing L (v2.1 - L, v2.2 - L) * Q2_1 L M v2) (bidderMeasure L) :=
        ((hphi_meas.1.comp hsub_meas).mul hF.2.2.2.2.1.stronglyMeasurable.integral_prod_left.measurable).aestronglyMeasurable
      have hint1 : Integrable (fun v2 : Type2 => phi1Wing L (v2.1 - L, v2.2 - L) * Q2_1 L M v2) (bidderMeasure L) :=
        hj21.integral_prod_right.congr (ae_of_all _ (fun v2 => by dsimp only; exact integral_const_mul _ _))
      have h := (integrable_bidderMeasure_iff hm1).mp hint1
      exact h.congr_fun (fun ab _ => by simp [P2p, bidder2Profile]) measurableSet_openUnitSquare
    have hi2 : IntegrableOn (fun ab : Type2 => phi2Wing L ab * P2p.g2 ab * rho ab.1 ab.2) openUnitSquare volume := by
      have hm2 : AEStronglyMeasurable (fun v2 : Type2 => phi2Wing L (v2.1 - L, v2.2 - L) * Q2_2 L M v2) (bidderMeasure L) :=
        ((hphi_meas.2.comp hsub_meas).mul hF.2.2.2.2.2.1.stronglyMeasurable.integral_prod_left.measurable).aestronglyMeasurable
      have hint2 : Integrable (fun v2 : Type2 => phi2Wing L (v2.1 - L, v2.2 - L) * Q2_2 L M v2) (bidderMeasure L) :=
        hj22.integral_prod_right.congr (ae_of_all _ (fun v2 => by dsimp only; exact integral_const_mul _ _))
      have h := (integrable_bidderMeasure_iff hm2).mp hint2
      exact h.congr_fun (fun ab _ => by simp [P2p, bidder2Profile]) measurableSet_openUnitSquare
    rw [← integral_add hi1 hi2]
    refine setIntegral_congr_fun measurableSet_openUnitSquare (fun ab _ => by ring)
  unfold ExpectedRevenue
  rw [integral_add hp1_int hp2_int, hp1_eq, hp2_eq, hw1_eq, hw2_eq]
  have hj12_add : Integrable (fun x : Type2 × Type2 =>
      phi1Wing L (x.1.1 - L, x.1.2 - L) * M.q1_1 x.1 x.2 +
      phi2Wing L (x.1.1 - L, x.1.2 - L) * M.q1_2 x.1 x.2) (jointMeasure L) := hj11.add hj12
  have hj123_add : Integrable (fun x : Type2 × Type2 =>
      phi1Wing L (x.1.1 - L, x.1.2 - L) * M.q1_1 x.1 x.2 +
      phi2Wing L (x.1.1 - L, x.1.2 - L) * M.q1_2 x.1 x.2 +
      phi1Wing L (x.2.1 - L, x.2.2 - L) * M.q2_1 x.1 x.2) (jointMeasure L) := hj12_add.add hj21
  rw [integral_add hj123_add hj22, integral_add hj12_add hj21, integral_add hj11 hj12]
  ring

/-! ### 3. Exact Linearity of `flagshipMechanism L` Interim Profiles on `S` -/

lemma flagship_strip_linear {L : ℝ} (hL : 0 ≤ L) :
    let hF := flagshipMechanism_isFeasible L
    let hS : IsSingleItem (flagshipMechanism L) := ⟨fun _ _ => rfl, fun _ _ => rfl⟩
    let hBI := dsic_exPostIR_implies_bic_interimIR hL hF (flagshipMechanism_isDSIC L) (flagshipMechanism_isExPostIR L)
    stripFunctional L (bidder1Profile L (flagshipMechanism L) hF hS hBI.1 hBI.2) = M1 L ∧
    stripFunctional L (bidder2Profile L (flagshipMechanism L) hF hS hBI.1 hBI.2) = M1 L := by
  intro hF hS hBI
  have hprob_lt : ∫ v, (if v.1 - v.2 < -t0 then (1 : ℝ) else 0) ∂(bidderMeasure L) = tailGT t0 :=
    prob_diff_lt_neg L t0_pos t0_lt_one.le
  -- On `|a - b| ≤ t0`: Bidder 1 always pays `L`! And wins Item 1 iff `t2 < -t0`!
  have hb1_strip : ∀ ab : Type2, -t0 ≤ ab.1 - ab.2 → ab.1 - ab.2 ≤ t0 →
      (bidder1Profile L (flagshipMechanism L) hF hS hBI.1 hBI.2).g1 ab = tailGT t0 ∧
      (bidder1Profile L (flagshipMechanism L) hF hS hBI.1 hBI.2).g2 ab = 1 - tailGT t0 ∧
      (bidder1Profile L (flagshipMechanism L) hF hS hBI.1 hBI.2).u ab =
        tailGT t0 * ab.1 + (1 - tailGT t0) * ab.2 := by
    intro ab h1 h2
    -- Pointwise check for every `b2` with `b2.1 - b2.2 ≠ -t0` (actually for ALL `b2`!):
    have hq1_pt : ∀ b2 : Type2, (flagshipMechanism L).q1_1 (L + ab.1, L + ab.2) b2 =
        if b2.1 - b2.2 < -t0 then 1 else 0 := by
      intro b2
      unfold flagshipMechanism; dsimp only
      have hd := b1_decision_iff L (L + ab.1, L + ab.2) b2
      dsimp only at hd
      have hs : (L + ab.1) - (L + ab.2) = ab.1 - ab.2 := by ring
      simp only [hd, hs]
      by_cases hlt : b2.1 - b2.2 < -t0
      · have hnot : ¬ -t0 ≤ b2.1 - b2.2 := not_le.mpr hlt
        simp only [hnot, hlt, ite_false, ite_true]
        rw [if_pos (by linarith)]
      · have hge : -t0 ≤ b2.1 - b2.2 := not_lt.mp hlt
        simp only [hge, hlt, ite_true, ite_false]
        rw [if_neg (not_lt.mpr (h2.trans (le_max_left _ _)))]
    have hq2_pt : ∀ b2 : Type2, (flagshipMechanism L).q1_2 (L + ab.1, L + ab.2) b2 =
        1 - (if b2.1 - b2.2 < -t0 then 1 else 0) := by
      intro b2
      have := hq1_pt b2
      unfold flagshipMechanism at this ⊢; dsimp only at this ⊢
      split_ifs at this ⊢ <;> linarith
    have hp1_pt : ∀ b2 : Type2, (flagshipMechanism L).p1 (L + ab.1, L + ab.2) b2 = L := by
      intro b2
      unfold flagshipMechanism; dsimp only
      have hd := b1_decision_iff L (L + ab.1, L + ab.2) b2
      dsimp only at hd
      have hs : (L + ab.1) - (L + ab.2) = ab.1 - ab.2 := by ring
      simp only [hd, hs]
      unfold p1Item1 p1Item2
      by_cases hge : -t0 ≤ b2.1 - b2.2
      · simp only [hge, ite_true]
        rw [if_neg (not_lt.mpr (h2.trans (le_max_left _ _)))]
      · simp only [hge, ite_false]
        rw [if_pos (by linarith)]
    have hg1 : Q1_1 L (flagshipMechanism L) (L + ab.1, L + ab.2) = tailGT t0 := by
      unfold Q1_1; simp_rw [hq1_pt]; exact hprob_lt
    have hg2 : Q1_2 L (flagshipMechanism L) (L + ab.1, L + ab.2) = 1 - tailGT t0 := by
      unfold Q1_2; simp_rw [hq2_pt]
      have hint_ind : Integrable (fun b2 : Type2 => if b2.1 - b2.2 < -t0 then (1 : ℝ) else 0) (bidderMeasure L) :=
        integrable_of_bounded_bidderMeasure (C := 1)
          (Measurable.ite (measurableSet_lt (measurable_fst.sub measurable_snd) measurable_const)
            measurable_const measurable_const).aestronglyMeasurable
          (fun _ _ => by split_ifs <;> norm_num)
      rw [integral_sub (integrable_const (1 : ℝ)) hint_ind, integral_const, probReal_univ, one_smul, hprob_lt]
    have hp1 : P1 L (flagshipMechanism L) (L + ab.1, L + ab.2) = L := by
      unfold P1; simp_rw [hp1_pt]; simp [probReal_univ]
    dsimp only [bidder1Profile]
    rw [hg1, hg2, hp1]
    exact ⟨rfl, rfl, by ring⟩
  -- Bidder 2's strip values follow directly from Bidder 1's via `flagshipMechanism_swap`:
  have hb2_strip : ∀ ab : Type2, -t0 ≤ ab.1 - ab.2 → ab.1 - ab.2 ≤ t0 →
      (bidder2Profile L (flagshipMechanism L) hF hS hBI.1 hBI.2).g1 ab = 1 - tailGT t0 ∧
      (bidder2Profile L (flagshipMechanism L) hF hS hBI.1 hBI.2).g2 ab = tailGT t0 ∧
      (bidder2Profile L (flagshipMechanism L) hF hS hBI.1 hBI.2).u ab =
        (1 - tailGT t0) * ab.1 + tailGT t0 * ab.2 := by
    intro ab h1 h2
    have hsw := hb1_strip (ab.2, ab.1) (by linarith) (by linarith)
    have hmp (f : Type2 → ℝ) :
        ∫ b, f (b.2, b.1) ∂(bidderMeasure L) = ∫ b, f b ∂(bidderMeasure L) :=
      (measurePreserving_swap_bidderMeasure L).integral_comp
        MeasurableEquiv.prodComm.measurableEmbedding f
    have hg1 : Q2_1 L (flagshipMechanism L) (L + ab.1, L + ab.2) =
        Q1_2 L (flagshipMechanism L) (L + ab.2, L + ab.1) := by
      unfold Q2_1 Q1_2; rw [← hmp]
      refine integral_congr_ae (ae_of_all _ (fun b1 => ?_))
      exact (flagshipMechanism_swap L (L + ab.2, L + ab.1) b1).1
    have hg2 : Q2_2 L (flagshipMechanism L) (L + ab.1, L + ab.2) =
        Q1_1 L (flagshipMechanism L) (L + ab.2, L + ab.1) := by
      unfold Q2_2 Q1_1; rw [← hmp]
      refine integral_congr_ae (ae_of_all _ (fun b1 => ?_))
      exact (flagshipMechanism_swap L (L + ab.2, L + ab.1) b1).2.1
    have hp2 : P2 L (flagshipMechanism L) (L + ab.1, L + ab.2) =
        P1 L (flagshipMechanism L) (L + ab.2, L + ab.1) := by
      unfold P2 P1; rw [← hmp]
      refine integral_congr_ae (ae_of_all _ (fun b1 => ?_))
      exact (flagshipMechanism_swap L (L + ab.2, L + ab.1) b1).2.2
    dsimp only [bidder1Profile, bidder2Profile] at hsw ⊢
    rw [hg1, hg2, hp2, hsw.1, hsw.2.1]
    have hu := hsw.2.2; rw [hsw.1, hsw.2.1] at hu
    exact ⟨rfl, rfl, by linarith⟩
  constructor
  · exact stripFunctional_eq_M1_of_linear L (tailGT t0) _
      (fun ab hab => (hb1_strip ab hab.2.1.le hab.2.2.le).2.2)
      (fun ab hab => (hb1_strip ab hab.2.1.le hab.2.2.le).1)
      (fun ab hab => (hb1_strip ab hab.2.1.le hab.2.2.le).2.1)
      (fun s _ => by
        have h1 := (hb1_strip (s + t0, s) (by linarith [t0_pos]) (by linarith)).2.2
        have h2 := (hb1_strip (s, s + t0) (by linarith) (by linarith [t0_pos])).2.2
        dsimp only at h1 h2; linarith)
  · exact stripFunctional_eq_M1_of_linear L (1 - tailGT t0) _
      (fun ab hab => by
        have h := (hb2_strip ab hab.2.1.le hab.2.2.le).2.2
        have hsub : 1 - (1 - tailGT t0) = tailGT t0 := by ring
        rw [hsub]; exact h)
      (fun ab hab => (hb2_strip ab hab.2.1.le hab.2.2.le).1)
      (fun ab hab => by
        have h := (hb2_strip ab hab.2.1.le hab.2.2.le).2.1
        have hsub : 1 - (1 - tailGT t0) = tailGT t0 := by ring
        rw [hsub]; exact h)
      (fun s _ => by
        have h1 := (hb2_strip (s + t0, s) (by linarith [t0_pos]) (by linarith)).2.2
        have h2 := (hb2_strip (s, s + t0) (by linarith) (by linarith [t0_pos])).2.2
        dsimp only at h1 h2; linarith)

/-! ### 4. Main Theorem 1 (Global Optimality Over ALL Randomized BIC & DSIC Mechanisms) -/

/-- Global revenue optimality of `flagshipMechanism L` over EVERY measurable randomized 4-bundle
BIC + interim-IR mechanism for every `L ≥ 2/π`. -/
theorem flagshipMechanism_optimal_BIC {L : ℝ} (hL : 2 / Real.pi ≤ L) (M : Mechanism)
    (hF : IsFeasible L M) (hB : IsBIC L M) (hIR : IsInterimIR L M) :
    ExpectedRevenue L M ≤ ExpectedRevenue L (flagshipMechanism L) := by
  have hL0 : 0 ≤ L := (le_trans (div_nonneg zero_le_two Real.pi_pos.le) hL)
  -- Lemma 1: Reduce `M` to single-item mechanism `M1 := reduceSingleItem M`
  let M1m : Mechanism := reduceSingleItem M
  have hF1 : IsFeasible L M1m := reduceSingleItem_isFeasible hF
  have hS1 : IsSingleItem M1m := reduceSingleItem_isSingleItem M
  have hB1 : IsBIC L M1m := reduceSingleItem_isBIC hF hB
  have hIR1 : IsInterimIR L M1m := reduceSingleItem_isInterimIR hF hIR
  rw [← reduceSingleItem_expectedRevenue L M]
  -- Properties of `flagshipMechanism L`
  have hFs := flagshipMechanism_isFeasible L
  have hSs : IsSingleItem (flagshipMechanism L) := ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  have hBIs := dsic_exPostIR_implies_bic_interimIR hL0 hFs (flagshipMechanism_isDSIC L) (flagshipMechanism_isExPostIR L)
  -- Apply dual revenue identity to BOTH `M1m` and `flagshipMechanism L`
  rw [dual_revenue_identity hF1 hS1 hB1 hIR1, dual_revenue_identity hFs hSs hBIs.1 hBIs.2]
  -- Strip dominance (Lemma 5) for `M1m` + exact strip equality for `flagshipMechanism L`
  have hstrip1 : stripFunctional L (bidder1Profile L M1m hF1 hS1 hB1 hIR1) ≤ M1 L :=
    lemma5_strip_dominance hL _
  have hstrip2 : stripFunctional L (bidder2Profile L M1m hF1 hS1 hB1 hIR1) ≤ M1 L :=
    lemma5_strip_dominance hL _
  rcases flagship_strip_linear hL0 with ⟨hs1_eq, hs2_eq⟩
  -- Wing dominance: integrate `pointwise_wing_dominance` over `jointMeasure L`!
  -- First note that `∀ᵐ v ∂(bidderMeasure L), (v.1 - L, v.2 - L) ∈ (wingPos ∪ wingNeg) ∪ stripSet`!
  have hae_part_bidder : ∀ᵐ v ∂(bidderMeasure L), (v.1 - L, v.2 - L) ∈ (wingPos ∪ wingNeg) ∪ stripSet := by
    have hm_set : MeasurableSet ((wingPos ∪ wingNeg) ∪ stripSet) :=
      (measurableSet_wingPos.union measurableSet_wingNeg).union measurableSet_stripSet
    have hsub_meas : Measurable (fun v : Type2 => (v.1 - L, v.2 - L)) :=
      (measurable_fst.sub measurable_const).prodMk (measurable_snd.sub measurable_const)
    -- `bidderMeasure L` is pushforward of `(volume.restrict openUnitSquare).withDensity rho` by `(a, b) ↦ (L + a, L + b)`!
    rw [ae_iff, bidderMeasure_eq_map_withDensity L]
    have hshift_meas : Measurable (fun ab : Type2 => (L + ab.1, L + ab.2)) :=
      (measurable_const.add measurable_fst).prodMk (measurable_const.add measurable_snd)
    have hmeas_c : MeasurableSet {a : Type2 | (a.1 - L, a.2 - L) ∉ (wingPos ∪ wingNeg) ∪ stripSet} :=
      (hsub_meas hm_set).compl
    rw [Measure.map_apply hshift_meas hmeas_c, withDensity_apply _ (hshift_meas hmeas_c)]
    have hnull_open : volume (((wingPos ∪ wingNeg) ∪ stripSet)ᶜ ∩ openUnitSquare) = 0 := by
      rw [inter_comm]
      exact (MeasureTheory.ae_eq_set.mp ae_eq_wing_union_strip).1
    have hpre_eq : (fun ab : Type2 => (L + ab.1, L + ab.2)) ⁻¹' {v : Type2 | ¬ (v.1 - L, v.2 - L) ∈ (wingPos ∪ wingNeg) ∪ stripSet} =
        ((wingPos ∪ wingNeg) ∪ stripSet)ᶜ := by
      ext ab; simp [add_sub_cancel_left]
    rw [hpre_eq, Measure.restrict_restrict hm_set.compl, setLIntegral_measure_zero _ _ hnull_open]
  -- Integrability of the wing integrand for ANY feasible mechanism `N`:
  have hwing_int : ∀ (N : Mechanism), IsFeasible L N →
      Integrable (fun x : Type2 × Type2 =>
        phi1Wing L (x.1.1 - L, x.1.2 - L) * N.q1_1 x.1 x.2 +
        phi2Wing L (x.1.1 - L, x.1.2 - L) * N.q1_2 x.1 x.2 +
        phi1Wing L (x.2.1 - L, x.2.2 - L) * N.q2_1 x.1 x.2 +
        phi2Wing L (x.2.1 - L, x.2.2 - L) * N.q2_2 x.1 x.2) (jointMeasure L) := fun N hFN => by
    rcases integrable_wing_terms hFN with ⟨h1, h2, h3, h4⟩
    exact ((h1.add h2).add h3).add h4
  have hwing_le :
      (∫ x, (phi1Wing L (x.1.1 - L, x.1.2 - L) * M1m.q1_1 x.1 x.2 +
             phi2Wing L (x.1.1 - L, x.1.2 - L) * M1m.q1_2 x.1 x.2 +
             phi1Wing L (x.2.1 - L, x.2.2 - L) * M1m.q2_1 x.1 x.2 +
             phi2Wing L (x.2.1 - L, x.2.2 - L) * M1m.q2_2 x.1 x.2) ∂(jointMeasure L)) ≤
      (∫ x, (phi1Wing L (x.1.1 - L, x.1.2 - L) * (flagshipMechanism L).q1_1 x.1 x.2 +
             phi2Wing L (x.1.1 - L, x.1.2 - L) * (flagshipMechanism L).q1_2 x.1 x.2 +
             phi1Wing L (x.2.1 - L, x.2.2 - L) * (flagshipMechanism L).q2_1 x.1 x.2 +
             phi2Wing L (x.2.1 - L, x.2.2 - L) * (flagshipMechanism L).q2_2 x.1 x.2) ∂(jointMeasure L)) := by
    refine integral_mono_ae (hwing_int M1m hF1) (hwing_int (flagshipMechanism L) hFs) ?_
    have hae1 : ∀ᵐ x : Type2 × Type2 ∂(jointMeasure L), (x.1.1 - L, x.1.2 - L) ∈ (wingPos ∪ wingNeg) ∪ stripSet :=
      QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_fst hae_part_bidder
    have hae2 : ∀ᵐ x : Type2 × Type2 ∂(jointMeasure L), (x.2.1 - L, x.2.2 - L) ∈ (wingPos ∪ wingNeg) ∪ stripSet :=
      QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_snd hae_part_bidder
    filter_upwards [ae_mem_profileDomain L, hae1, hae2] with x hx hp1 hp2
    have hq := hF1.1 x.1 hx.1 x.2 hx.2
    have hs1 : M1m.q1_12 x.1 x.2 = 0 := hS1.1 x.1 x.2
    have hs2 : M1m.q2_12 x.1 x.2 = 0 := hS1.2 x.1 x.2
    have hdom := pointwise_wing_dominance hL0 hp1 hp2 hq.1 hq.2.1 hq.2.2.2.1 hq.2.2.2.2.1
      (by linarith [hq.2.2.2.2.2.2.1]) (by linarith [hq.2.2.2.2.2.2.2.1])
      (by linarith [hq.2.2.2.2.2.2.2.2.1]) (by linarith [hq.2.2.2.2.2.2.2.2.2])
    have heq1 : (L + (x.1.1 - L), L + (x.1.2 - L)) = x.1 := by ext <;> dsimp <;> ring
    have heq2 : (L + (x.2.1 - L), L + (x.2.2 - L)) = x.2 := by ext <;> dsimp <;> ring
    rw [heq1, heq2] at hdom
    exact hdom
  linarith

/-- Global revenue optimality of `flagshipMechanism L` over EVERY measurable randomized 4-bundle
DSIC + ex-post IR mechanism for every `L ≥ 2/π`. -/
theorem flagshipMechanism_optimal_DSIC {L : ℝ} (hL : 2 / Real.pi ≤ L) (M : Mechanism)
    (hF : IsFeasible L M) (hD : IsDSIC L M) (hIR : IsExPostIR L M) :
    ExpectedRevenue L M ≤ ExpectedRevenue L (flagshipMechanism L) := by
  have hBI := dsic_exPostIR_implies_bic_interimIR (le_trans (div_nonneg zero_le_two Real.pi_pos.le) hL) hF hD hIR
  exact flagshipMechanism_optimal_BIC hL M hF hBI.1 hBI.2

/-- **Main Theorem 1 (Continuous Multi-Bidder Multi-Item Revenue Optimality, `α = 1/2`)**:
Satisfies the exact top-level `Theorem1Statement` from `EconCSAuction/Spec.lean` with no
unproved obligations and strictly core axioms `[propext, Classical.choice, Quot.sound]`. -/
theorem theorem1_main : Theorem1Statement := by
  intro L hL
  have hL0 : 0 ≤ L := (le_trans (div_nonneg zero_le_two Real.pi_pos.le) hL)
  exact ⟨flagshipMechanism_isFeasible L,
    flagshipMechanism_isDSIC L,
    flagshipMechanism_isExPostIR L,
    flagshipMechanism_nonNegPayment hL0,
    flagshipMechanism_boundedPayment L,
    flagshipMechanism_expectedRevenue L,
    fun M hF hB hIR => flagshipMechanism_optimal_BIC hL M hF hB hIR,
    fun M hF hD hIR => flagshipMechanism_optimal_DSIC hL M hF hD hIR⟩

end

end EconCSAuction
