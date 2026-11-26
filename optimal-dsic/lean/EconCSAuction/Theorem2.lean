import EconCSAuction.Theorem1
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

/-!
# Theorem 2: `flagshipMechanism L` is strictly beaten for `0 ≤ L < 2 / π`

Constructs the perturbed mechanism `perturbedSymMechanism L ε` (on `|t₂| ≤ t₀`, raise every price
on Bidder 1's menu by `ε` and add the outside option; she leaves exactly on `{a₁ + b₁ < 2ε}`, of
probability `(π / 2) ε`), proves it is feasible, DSIC and ex-post IR, and that its revenue exceeds
that of `flagshipMechanism L` for a suitable `ε` whenever `0 ≤ L < 2 / π`.
-/

open MeasureTheory Set Filter Topology

namespace EconCSAuction

noncomputable section

/-! ### 1. Exact Corner Probability `P(a₁ + b₁ < 2ε) = (π / 2) ε` -/

/-- Exact quarter-circle integral `∫ x in (0, 1), √(1 - x²) = π / 4`. -/
lemma integral_sqrt_one_sub_sq :
    ∫ x in Ioo (0 : ℝ) 1, Real.sqrt (1 - x ^ 2) = Real.pi / 4 := by
  let F : ℝ → ℝ := fun x => (x * Real.sqrt (1 - x ^ 2) + Real.arcsin x) / 2
  have hcont : ContinuousOn F (Icc (0 : ℝ) 1) := by
    unfold F
    refine ((continuousOn_id.mul (Real.continuous_sqrt.comp (continuous_const.sub (continuous_pow 2))).continuousOn).add
      Real.continuous_arcsin.continuousOn).div_const 2
  have hderiv : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt F (Real.sqrt (1 - x ^ 2)) x := by
    intro x hx
    have h1x : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
    have hsq_pos : 0 < Real.sqrt (1 - x ^ 2) := Real.sqrt_pos.mpr h1x
    have hd_sq : HasDerivAt (fun y : ℝ => Real.sqrt (1 - y ^ 2)) (-x / Real.sqrt (1 - x ^ 2)) x := by
      have hp : HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-(2 * x)) x := by
        simpa using (hasDerivAt_pow 2 x).const_sub (1 : ℝ)
      exact ((Real.hasDerivAt_sqrt h1x.ne').comp x hp).congr_deriv (by field_simp [hsq_pos.ne'])
    have hd1 := (hasDerivAt_id x).mul hd_sq
    have hd2 := Real.hasDerivAt_arcsin (by linarith [hx.1] : x ≠ -1) hx.2.ne
    refine ((hd1.add hd2).div_const 2).congr_deriv ?_
    have hsq2 : (Real.sqrt (1 - x ^ 2)) ^ 2 = 1 - x ^ 2 := Real.sq_sqrt h1x.le
    dsimp only [id_eq]
    field_simp [hsq_pos.ne']
    nlinarith
  have hint : IntervalIntegrable (fun x : ℝ => Real.sqrt (1 - x ^ 2)) volume 0 1 :=
    (Real.continuous_sqrt.comp (continuous_const.sub (continuous_pow 2))).intervalIntegrable 0 1
  rw [setIntegral_congr_set Ioo_ae_eq_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hcont hderiv hint]
  dsimp only [F]
  rw [Real.arcsin_one, Real.arcsin_zero]
  norm_num; ring

/-- Exact corner probability under `bidderMeasure L` (`v_ij = L + U_ij²`):
`∫ v, 1[(v.1 - L) + (v.2 - L) < 2 ε] ∂(bidderMeasure L) = (π / 2) * ε` for `0 < ε ≤ 1 / 2`.
(In `(u₁, u₂) ∈ [0, 1]²` coordinates, this is literally the quarter-disk `{u₁² + u₂² < 2ε}`!) -/
lemma prob_corner_triangle (L : ℝ) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2) :
    ∫ v, (if (v.1 - L) + (v.2 - L) < 2 * ε then (1 : ℝ) else 0) ∂(bidderMeasure L) =
      (Real.pi / 2) * ε := by
  -- Push back directly to `(u₁, u₂) ∈ [0, 1]²` via `singleValMeasure L = Measure.map (fun u => L + u^2) (volume.restrict (Icc 0 1))`!
  have hm_sq : Measurable (fun u : ℝ => L + u ^ 2) := measurable_const.add (measurable_id.pow_const 2)
  have hprod_map : bidderMeasure L =
      Measure.map (Prod.map (fun u : ℝ => L + u ^ 2) (fun u : ℝ => L + u ^ 2))
        ((volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict (Icc (0 : ℝ) 1))) := by
    unfold bidderMeasure singleValMeasure
    exact Measure.map_prod_map _ _ hm_sq hm_sq
  have hpred : MeasurableSet {v : Type2 | (v.1 - L) + (v.2 - L) < 2 * ε} :=
    measurableSet_lt ((measurable_fst.sub measurable_const).add (measurable_snd.sub measurable_const))
      measurable_const
  have hmeas_f : Measurable (fun v : Type2 => if (v.1 - L) + (v.2 - L) < 2 * ε then (1 : ℝ) else 0) :=
    Measurable.ite hpred measurable_const measurable_const
  rw [hprod_map, integral_map (hm_sq.prodMap hm_sq).aemeasurable hmeas_f.aestronglyMeasurable]
  simp only [Prod.map_fst, Prod.map_snd, add_sub_cancel_left]
  have hint_disk : Integrable (fun u : ℝ × ℝ => if u.1 ^ 2 + u.2 ^ 2 < 2 * ε then (1 : ℝ) else 0)
      ((volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict (Icc (0 : ℝ) 1))) := by
    have hm : Measurable (fun u : ℝ × ℝ => if u.1 ^ 2 + u.2 ^ 2 < 2 * ε then (1 : ℝ) else 0) :=
      Measurable.ite (measurableSet_lt ((measurable_fst.pow_const 2).add (measurable_snd.pow_const 2)) measurable_const)
        measurable_const measurable_const
    refine Integrable.of_bound hm.aestronglyMeasurable 1 (ae_of_all _ (fun u => ?_))
    rw [Real.norm_eq_abs]; split_ifs <;> norm_num
  rw [integral_prod _ hint_disk]
  let R : ℝ := Real.sqrt (2 * ε)
  have hR_pos : 0 < R := Real.sqrt_pos.mpr (by linarith)
  have hR_le1 : R ≤ 1 := by
    calc R = Real.sqrt (2 * ε) := rfl
      _ ≤ Real.sqrt 1 := Real.sqrt_le_sqrt (by linarith)
      _ = 1 := Real.sqrt_one
  have hR_sq : R ^ 2 = 2 * ε := Real.sq_sqrt (by linarith)
  -- Evaluate inner integral over `u₂ ∈ [0, 1]` at fixed `u₁ ∈ [0, 1]`:
  have hinner : ∀ u1 ∈ Ioo (0 : ℝ) 1,
      (∫ u2 in Icc (0 : ℝ) 1, if u1 ^ 2 + u2 ^ 2 < 2 * ε then (1 : ℝ) else 0) =
      if u1 < R then Real.sqrt (2 * ε - u1 ^ 2) else 0 := by
    intro u1 hu1
    by_cases hlt : u1 < R
    · rw [if_pos hlt]
      have hrem : 0 < 2 * ε - u1 ^ 2 := by
        have hsq : u1 ^ 2 < R ^ 2 := by nlinarith [hu1.1]
        linarith
      have hsq_le1 : Real.sqrt (2 * ε - u1 ^ 2) ≤ 1 := by
        calc Real.sqrt (2 * ε - u1 ^ 2) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt (by nlinarith [hu1.1])
          _ = 1 := Real.sqrt_one
      have heq_ind : ∀ u2 ∈ Icc (0 : ℝ) 1,
          (if u1 ^ 2 + u2 ^ 2 < 2 * ε then (1 : ℝ) else 0) =
          (Ico (0 : ℝ) (Real.sqrt (2 * ε - u1 ^ 2))).indicator (fun _ => (1 : ℝ)) u2 := by
        intro u2 hu2
        by_cases h2 : u2 < Real.sqrt (2 * ε - u1 ^ 2)
        · have hsq : u2 ^ 2 < (Real.sqrt (2 * ε - u1 ^ 2)) ^ 2 := by nlinarith [hu2.1, Real.sqrt_nonneg (2 * ε - u1 ^ 2)]
          rw [Real.sq_sqrt hrem.le] at hsq
          have hmem : u2 ∈ Ico (0 : ℝ) (Real.sqrt (2 * ε - u1 ^ 2)) := ⟨hu2.1, h2⟩
          rw [if_pos (by linarith), indicator_of_mem hmem]
        · have hge : Real.sqrt (2 * ε - u1 ^ 2) ≤ u2 := not_lt.mp h2
          have hsq : (Real.sqrt (2 * ε - u1 ^ 2)) ^ 2 ≤ u2 ^ 2 := by nlinarith [Real.sqrt_nonneg (2 * ε - u1 ^ 2)]
          rw [Real.sq_sqrt hrem.le] at hsq
          have hnm : u2 ∉ Ico (0 : ℝ) (Real.sqrt (2 * ε - u1 ^ 2)) := fun h => h2 h.2
          rw [if_neg (by linarith), indicator_of_notMem hnm]
      rw [setIntegral_congr_fun measurableSet_Icc heq_ind, setIntegral_indicator measurableSet_Ico,
          inter_eq_right.mpr (Ico_subset_Icc_self.trans (Icc_subset_Icc_right hsq_le1)),
          setIntegral_const, Real.volume_real_Ico_of_le (Real.sqrt_nonneg _), sub_zero, smul_eq_mul, mul_one]
    · rw [if_neg hlt]
      have hge : R ≤ u1 := not_lt.mp hlt
      have hsq : 2 * ε ≤ u1 ^ 2 := by nlinarith
      have hzero : ∀ u2 ∈ Icc (0 : ℝ) 1, (if u1 ^ 2 + u2 ^ 2 < 2 * ε then (1 : ℝ) else 0) = 0 := by
        intro u2 _
        rw [if_neg (by nlinarith)]
      rw [setIntegral_congr_fun measurableSet_Icc hzero, integral_zero]
  rw [setIntegral_congr_set Ioo_ae_eq_Icc.symm, setIntegral_congr_fun measurableSet_Ioo hinner]
  have hind_outer : ∀ u1 ∈ Ioo (0 : ℝ) 1,
      (if u1 < R then Real.sqrt (2 * ε - u1 ^ 2) else 0) =
      (Ioo (0 : ℝ) R).indicator (fun u1 => Real.sqrt (2 * ε - u1 ^ 2)) u1 := by
    intro u1 hu1
    by_cases hlt : u1 < R
    · have hmem : u1 ∈ Ioo (0 : ℝ) R := ⟨hu1.1, hlt⟩
      rw [if_pos hlt, indicator_of_mem hmem]
    · have hnm : u1 ∉ Ioo (0 : ℝ) R := fun h => hlt h.2
      rw [if_neg hlt, indicator_of_notMem hnm]
  rw [setIntegral_congr_fun measurableSet_Ioo hind_outer, setIntegral_indicator measurableSet_Ioo,
      inter_eq_right.mpr (Ioo_subset_Ioo_right hR_le1)]
  -- Substitute `u1 = R * x` (`x ∈ (0, 1)`): `∫_0^R √(R² - u₁²) du₁ = R² * ∫_0^1 √(1 - x²) dx = 2ε * (π/4)`!
  rw [setIntegral_congr_set Ioo_ae_eq_Ioc, ← intervalIntegral.integral_of_le hR_pos.le]
  have hsub := intervalIntegral.integral_comp_mul_left (fun u => Real.sqrt (2 * ε - u ^ 2)) hR_pos.ne'
    (a := (0 : ℝ)) (b := 1)
  rw [mul_zero, mul_one] at hsub
  have hrew : (∫ x in (0 : ℝ)..1, Real.sqrt (2 * ε - (R * x) ^ 2)) =
      R * ∫ x in (0 : ℝ)..1, Real.sqrt (1 - x ^ 2) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun x hx => ?_)
    rw [uIcc_of_le zero_le_one] at hx
    have hfac : 2 * ε - (R * x) ^ 2 = R ^ 2 * (1 - x ^ 2) := by rw [← hR_sq]; ring
    rw [hfac, Real.sqrt_mul (sq_nonneg R), Real.sqrt_sq hR_pos.le]
  rw [hrew] at hsub
  have hI : ∫ x in (0 : ℝ)..1, Real.sqrt (1 - x ^ 2) = Real.pi / 4 := by
    rw [intervalIntegral.integral_of_le zero_le_one, ← setIntegral_congr_set Ioo_ae_eq_Ioc]
    exact integral_sqrt_one_sub_sq
  rw [hI] at hsub
  have hval : ∫ x in (0 : ℝ)..R, Real.sqrt (2 * ε - x ^ 2) = R * (R * (Real.pi / 4)) := by
    rw [smul_eq_mul] at hsub
    have hmul : R * (R * (Real.pi / 4)) = R * (R⁻¹ * ∫ x in (0 : ℝ)..R, Real.sqrt (2 * ε - x ^ 2)) :=
      congrArg (fun z => R * z) hsub
    have hR : R * (R⁻¹ * ∫ x in (0 : ℝ)..R, Real.sqrt (2 * ε - x ^ 2)) =
        ∫ x in (0 : ℝ)..R, Real.sqrt (2 * ε - x ^ 2) := by
      rw [← mul_assoc, mul_inv_cancel₀ hR_pos.ne', one_mul]
    linarith
  rw [hval]
  calc R * (R * (Real.pi / 4)) = R ^ 2 * (Real.pi / 4) := by ring
    _ = 2 * ε * (Real.pi / 4) := by rw [hR_sq]
    _ = Real.pi / 2 * ε := by ring

/-- Exact perturbed mechanism: takes `symTwinMechanism L` and on the strip event
`{|t₂| ≤ t₀}` raises Bidder 1's 3-option menu prices by `+ε` and adds the outside option `(0, 0; 0)`,
excluding `{a₁ + b₁ < 2ε}` (leaving Bidder 2 completely untouched!). -/
def perturbedSymMechanism (L ε : ℝ) : Mechanism where
  q1_1 b1 b2 :=
    let t1 := b1.1 - b1.2; let t2 := b2.1 - b2.2
    if -t0 ≤ t2 ∧ t2 ≤ t0 then
      if (b1.1 - L) + (b1.2 - L) < 2 * ε then 0
      else if t0 < t1 then 1 else if t1 < -t0 then 0 else 1 / 2
    else (symTwinMechanism L).q1_1 b1 b2
  q1_2 b1 b2 :=
    let t1 := b1.1 - b1.2; let t2 := b2.1 - b2.2
    if -t0 ≤ t2 ∧ t2 ≤ t0 then
      if (b1.1 - L) + (b1.2 - L) < 2 * ε then 0
      else if t0 < t1 then 0 else if t1 < -t0 then 1 else 1 / 2
    else (symTwinMechanism L).q1_2 b1 b2
  q1_12 _ _ := 0
  q2_1 := (symTwinMechanism L).q2_1
  q2_2 := (symTwinMechanism L).q2_2
  q2_12 _ _ := 0
  p1 b1 b2 :=
    let t1 := b1.1 - b1.2; let t2 := b2.1 - b2.2
    if -t0 ≤ t2 ∧ t2 ≤ t0 then
      if (b1.1 - L) + (b1.2 - L) < 2 * ε then 0
      else (symTwinMechanism L).p1 b1 b2 + ε
    else (symTwinMechanism L).p1 b1 b2
  p2 := (symTwinMechanism L).p2

lemma perturbedSymMechanism_isFeasible (L : ℝ) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < t0 / 2) :
    IsFeasible L (perturbedSymMechanism L ε) := by
  have hm_t2s : MeasurableSet {p : Type2 × Type2 | -t0 ≤ p.2.1 - p.2.2 ∧ p.2.1 - p.2.2 ≤ t0} :=
    (measurableSet_le measurable_const ((measurable_fst.comp measurable_snd).sub (measurable_snd.comp measurable_snd))).inter
      (measurableSet_le ((measurable_fst.comp measurable_snd).sub (measurable_snd.comp measurable_snd)) measurable_const)
  have hm_t1s : MeasurableSet {p : Type2 × Type2 | -t0 ≤ p.1.1 - p.1.2 ∧ p.1.1 - p.1.2 ≤ t0} :=
    (measurableSet_le measurable_const ((measurable_fst.comp measurable_fst).sub (measurable_snd.comp measurable_fst))).inter
      (measurableSet_le ((measurable_fst.comp measurable_fst).sub (measurable_snd.comp measurable_fst)) measurable_const)
  have hm_corn : MeasurableSet {p : Type2 × Type2 | (p.1.1 - L) + (p.1.2 - L) < 2 * ε} :=
    measurableSet_lt (((measurable_fst.comp measurable_fst).sub measurable_const).add
      ((measurable_snd.comp measurable_fst).sub measurable_const)) measurable_const
  have hm_t1gt : MeasurableSet {p : Type2 × Type2 | t0 < p.1.1 - p.1.2} :=
    measurableSet_lt measurable_const ((measurable_fst.comp measurable_fst).sub (measurable_snd.comp measurable_fst))
  have hm_t1lt : MeasurableSet {p : Type2 × Type2 | p.1.1 - p.1.2 < -t0} :=
    measurableSet_lt ((measurable_fst.comp measurable_fst).sub (measurable_snd.comp measurable_fst)) measurable_const
  have hm_t2gt : MeasurableSet {p : Type2 × Type2 | t0 < p.2.1 - p.2.2} :=
    measurableSet_lt measurable_const ((measurable_fst.comp measurable_snd).sub (measurable_snd.comp measurable_snd))
  have hm_t2lt : MeasurableSet {p : Type2 × Type2 | p.2.1 - p.2.2 < -t0} :=
    measurableSet_lt ((measurable_fst.comp measurable_snd).sub (measurable_snd.comp measurable_snd)) measurable_const
  have hm_t21 : MeasurableSet {p : Type2 × Type2 | p.2.1 - p.2.2 < p.1.1 - p.1.2} :=
    measurableSet_lt ((measurable_fst.comp measurable_snd).sub (measurable_snd.comp measurable_snd))
      ((measurable_fst.comp measurable_fst).sub (measurable_snd.comp measurable_fst))
  have hm_t12 : MeasurableSet {p : Type2 × Type2 | p.1.1 - p.1.2 ≤ p.2.1 - p.2.2} :=
    measurableSet_le ((measurable_fst.comp measurable_fst).sub (measurable_snd.comp measurable_fst))
      ((measurable_fst.comp measurable_snd).sub (measurable_snd.comp measurable_snd))
  have hm_sym_q11 : Measurable (Function.uncurry (symTwinMechanism L).q1_1) :=
    Measurable.ite hm_t2s (Measurable.ite hm_t1gt measurable_const (Measurable.ite hm_t1lt measurable_const measurable_const))
      (Measurable.ite hm_t21 measurable_const measurable_const)
  have hm_sym_q12 : Measurable (Function.uncurry (symTwinMechanism L).q1_2) :=
    Measurable.ite hm_t2s (Measurable.ite hm_t1gt measurable_const (Measurable.ite hm_t1lt measurable_const measurable_const))
      (Measurable.ite hm_t21 measurable_const measurable_const)
  have hm_sym_q21 : Measurable (Function.uncurry (symTwinMechanism L).q2_1) :=
    Measurable.ite hm_t1s (Measurable.ite hm_t2gt measurable_const (Measurable.ite hm_t2lt measurable_const measurable_const))
      (Measurable.ite hm_t12 measurable_const measurable_const)
  have hm_sym_q22 : Measurable (Function.uncurry (symTwinMechanism L).q2_2) :=
    Measurable.ite hm_t1s (Measurable.ite hm_t2gt measurable_const (Measurable.ite hm_t2lt measurable_const measurable_const))
      (Measurable.ite hm_t12 measurable_const measurable_const)
  have hm_sym_p1 : Measurable (Function.uncurry (symTwinMechanism L).p1) :=
    Measurable.ite hm_t2s (Measurable.ite hm_t1gt measurable_const (Measurable.ite hm_t1lt measurable_const measurable_const))
      (Measurable.ite hm_t2gt
        (Measurable.ite hm_t21 (measurable_const.add ((measurable_fst.comp measurable_snd).sub (measurable_snd.comp measurable_snd))) measurable_const)
        (Measurable.ite hm_t21 measurable_const (measurable_const.add ((measurable_fst.comp measurable_snd).sub (measurable_snd.comp measurable_snd)).neg)))
  have hm_sym_p2 : Measurable (Function.uncurry (symTwinMechanism L).p2) :=
    Measurable.ite hm_t1s (Measurable.ite hm_t2gt measurable_const (Measurable.ite hm_t2lt measurable_const measurable_const))
      (Measurable.ite hm_t1gt
        (Measurable.ite hm_t12 (measurable_const.add ((measurable_fst.comp measurable_fst).sub (measurable_snd.comp measurable_fst))) measurable_const)
        (Measurable.ite hm_t12 measurable_const (measurable_const.add ((measurable_fst.comp measurable_fst).sub (measurable_snd.comp measurable_fst)).neg)))
  have hmp1 : Measurable (Function.uncurry (perturbedSymMechanism L ε).p1) :=
    Measurable.ite hm_t2s (Measurable.ite hm_corn measurable_const (hm_sym_p1.add measurable_const)) hm_sym_p1
  refine ⟨?_, Measurable.ite hm_t2s (Measurable.ite hm_corn measurable_const (Measurable.ite hm_t1gt measurable_const (Measurable.ite hm_t1lt measurable_const measurable_const))) hm_sym_q11,
    Measurable.ite hm_t2s (Measurable.ite hm_corn measurable_const (Measurable.ite hm_t1gt measurable_const (Measurable.ite hm_t1lt measurable_const measurable_const))) hm_sym_q12,
    measurable_const, hm_sym_q21, hm_sym_q22, measurable_const, hmp1, hm_sym_p2, ?_, ?_⟩
  · intro v1 hv1 v2 hv2
    have hpt := symTwinMechanism_isPointwiseFeasible L v1 hv1 v2 hv2
    rcases hpt with ⟨h11, h12, h112, h21, h22, h212, hs1, hs2, hi1, hi2⟩
    unfold perturbedSymMechanism; dsimp only
    by_cases h2 : -t0 ≤ v2.1 - v2.2 ∧ v2.1 - v2.2 ≤ t0
    · rw [if_pos h2, if_pos h2]
      by_cases hc : (v1.1 - L) + (v1.2 - L) < 2 * ε
      · rw [if_pos hc, if_pos hc]
        refine ⟨le_rfl, le_rfl, le_rfl, h21, h22, le_rfl, by norm_num, by linarith, by linarith, by linarith⟩
      · rw [if_neg hc, if_neg hc]
        have hq1_eq : (if t0 < v1.1 - v1.2 then (1 : ℝ) else if v1.1 - v1.2 < -t0 then 0 else 1 / 2) =
            (symTwinMechanism L).q1_1 v1 v2 := by unfold symTwinMechanism; dsimp only; rw [if_pos h2]
        have hq2_eq : (if t0 < v1.1 - v1.2 then (0 : ℝ) else if v1.1 - v1.2 < -t0 then 1 else 1 / 2) =
            (symTwinMechanism L).q1_2 v1 v2 := by unfold symTwinMechanism; dsimp only; rw [if_pos h2]
        rw [hq1_eq, hq2_eq]
        exact ⟨h11, h12, le_rfl, h21, h22, le_rfl, by linarith, by linarith, by linarith, by linarith⟩
    · rw [if_neg h2, if_neg h2]
      exact ⟨h11, h12, le_rfl, h21, h22, le_rfl, by linarith, by linarith, by linarith, by linarith⟩
  · refine integrable_of_bounded_jointMeasure (C := |L| + 3) hmp1.aestronglyMeasurable ?_
    intro x hx
    dsimp only [Function.uncurry, perturbedSymMechanism, symTwinMechanism]
    have ht2_le : x.2.1 - x.2.2 ≤ 1 := by linarith [hx.2.1.2, hx.2.2.1]
    have ht2_ge : -1 ≤ x.2.1 - x.2.2 := by linarith [hx.2.1.1, hx.2.2.2]
    have ht0 := t0_pos; have ht01 := t0_lt_one
    rw [abs_le]
    split_ifs <;> constructor <;> linarith [neg_abs_le L, le_abs_self L]
  · refine integrable_of_bounded_jointMeasure (C := |L| + 3) hm_sym_p2.aestronglyMeasurable ?_
    intro x hx
    dsimp only [Function.uncurry, perturbedSymMechanism, symTwinMechanism]
    have ht1_le : x.1.1 - x.1.2 ≤ 1 := by linarith [hx.1.1.2, hx.1.2.1]
    have ht1_ge : -1 ≤ x.1.1 - x.1.2 := by linarith [hx.1.1.1, hx.1.2.2]
    have ht0 := t0_pos; have ht01 := t0_lt_one
    rw [abs_le]
    split_ifs <;> constructor <;> linarith [neg_abs_le L, le_abs_self L]

lemma perturbedSymMechanism_isDSIC (L : ℝ) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < t0 / 2) :
    IsDSIC L (perturbedSymMechanism L ε) := by
  refine ⟨?_, (symTwinMechanism_isDSIC L).2⟩
  intro v1 hv1 b1 hb1 b2 hb2
  have hv11 := hv1.1.1; have hv12 := hv1.2.1
  have ht0 := t0_pos
  unfold u1Report UnitDemandVal perturbedSymMechanism; dsimp only
  by_cases h2 : -t0 ≤ b2.1 - b2.2 ∧ b2.1 - b2.2 ≤ t0
  · simp only [h2, ite_true, symTwinMechanism]
    -- On `|t₂| ≤ t₀`, Bidder 1 faces 4-option menu `{(0,0;0), (1/2,1/2;L+ε), (1,0;L+t₀/2+ε), (0,1;L+t₀/2+ε)}`,
    -- and note `{a₁ + b₁ < 2ε} ⊆ {|t₁| < t₀}` because `ε < t₀ / 2` and `a₁, b₁ ≥ 0`!
    split_ifs <;> linarith
  · simp only [h2, ite_false]
    exact (symTwinMechanism_isDSIC L).1 v1 hv1 b1 hb1 b2 hb2

lemma perturbedSymMechanism_isExPostIR (L : ℝ) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < t0 / 2) :
    IsExPostIR L (perturbedSymMechanism L ε) := by
  intro v1 hv1 v2 hv2
  refine ⟨?_, (symTwinMechanism_isExPostIR L v1 hv1 v2 hv2).2⟩
  have hv11 := hv1.1.1; have hv12 := hv1.2.1
  have ht0 := t0_pos
  unfold u1Report UnitDemandVal perturbedSymMechanism; dsimp only
  by_cases h2 : -t0 ≤ v2.1 - v2.2 ∧ v2.1 - v2.2 ≤ t0
  · simp only [h2, ite_true, symTwinMechanism]
    split_ifs <;> linarith
  · simp only [h2, ite_false]
    exact (symTwinMechanism_isExPostIR L v1 hv1 v2 hv2).1

lemma perturbedSymMechanism_nonNeg_singleItem {L ε : ℝ} (hL0 : 0 ≤ L) (hε0 : 0 < ε) :
    NonNegPayment L (perturbedSymMechanism L ε) ∧ IsSingleItem (perturbedSymMechanism L ε) := by
  refine ⟨?_, ⟨fun _ _ => rfl, fun _ _ => rfl⟩⟩
  intro v1 _ v2 _
  have ht0 := t0_pos
  unfold perturbedSymMechanism symTwinMechanism; dsimp only
  constructor <;> split_ifs <;>
    (try simp only [not_and_or, not_le, not_lt] at *) <;>
    repeat (first | linarith | cases ‹_ ∨ _›)

lemma integrable_symTwin_p1 (L : ℝ) :
    Integrable (fun x : Type2 × Type2 => (symTwinMechanism L).p1 x.1 x.2) (jointMeasure L) := by
  have hm_t2s : MeasurableSet {p : Type2 × Type2 | -t0 ≤ p.2.1 - p.2.2 ∧ p.2.1 - p.2.2 ≤ t0} :=
    (measurableSet_le measurable_const ((measurable_fst.comp measurable_snd).sub (measurable_snd.comp measurable_snd))).inter
      (measurableSet_le ((measurable_fst.comp measurable_snd).sub (measurable_snd.comp measurable_snd)) measurable_const)
  have hm_t1gt : MeasurableSet {p : Type2 × Type2 | t0 < p.1.1 - p.1.2} :=
    measurableSet_lt measurable_const ((measurable_fst.comp measurable_fst).sub (measurable_snd.comp measurable_fst))
  have hm_t1lt : MeasurableSet {p : Type2 × Type2 | p.1.1 - p.1.2 < -t0} :=
    measurableSet_lt ((measurable_fst.comp measurable_fst).sub (measurable_snd.comp measurable_fst)) measurable_const
  have hm_t2gt : MeasurableSet {p : Type2 × Type2 | t0 < p.2.1 - p.2.2} :=
    measurableSet_lt measurable_const ((measurable_fst.comp measurable_snd).sub (measurable_snd.comp measurable_snd))
  have hm_t21 : MeasurableSet {p : Type2 × Type2 | p.2.1 - p.2.2 < p.1.1 - p.1.2} :=
    measurableSet_lt ((measurable_fst.comp measurable_snd).sub (measurable_snd.comp measurable_snd))
      ((measurable_fst.comp measurable_fst).sub (measurable_snd.comp measurable_fst))
  have hm : Measurable (fun x : Type2 × Type2 => (symTwinMechanism L).p1 x.1 x.2) :=
    Measurable.ite hm_t2s (Measurable.ite hm_t1gt measurable_const (Measurable.ite hm_t1lt measurable_const measurable_const))
      (Measurable.ite hm_t2gt
        (Measurable.ite hm_t21 (measurable_const.add ((measurable_fst.comp measurable_snd).sub (measurable_snd.comp measurable_snd))) measurable_const)
        (Measurable.ite hm_t21 measurable_const (measurable_const.add ((measurable_fst.comp measurable_snd).sub (measurable_snd.comp measurable_snd)).neg)))
  refine integrable_of_bounded_jointMeasure (C := |L| + 2) hm.aestronglyMeasurable ?_
  intro x hx; dsimp only [symTwinMechanism]
  have ht2_le : x.2.1 - x.2.2 ≤ 1 := by linarith [hx.2.1.2, hx.2.2.1]
  have ht2_ge : -1 ≤ x.2.1 - x.2.2 := by linarith [hx.2.1.1, hx.2.2.2]
  rw [abs_le]; split_ifs <;> constructor <;> linarith [neg_abs_le L, le_abs_self L, t0_pos, t0_lt_one]

/-- `symTwinMechanism L` has the exact same expected revenue as `flagshipMechanism L`. -/
lemma symTwinMechanism_expectedRevenue (L : ℝ) :
    ExpectedRevenue L (symTwinMechanism L) = ExpectedRevenue L (flagshipMechanism L) := by
  have hFs := flagshipMechanism_isFeasible L
  have hFp := perturbedSymMechanism_isFeasible L (ε := t0 / 4) (by linarith [t0_pos]) (by linarith [t0_pos])
  have hsym_p1_int := integrable_symTwin_p1 L
  have hsym_p2_int : Integrable (fun x : Type2 × Type2 => (symTwinMechanism L).p2 x.1 x.2) (jointMeasure L) :=
    hFp.2.2.2.2.2.2.2.2.2.2
  have hp1_f : Integrable (fun x : Type2 × Type2 => (flagshipMechanism L).p1 x.1 x.2) (jointMeasure L) :=
    hFs.2.2.2.2.2.2.2.2.2.1
  have hp2_f : Integrable (fun x : Type2 × Type2 => (flagshipMechanism L).p2 x.1 x.2) (jointMeasure L) :=
    hFs.2.2.2.2.2.2.2.2.2.2
  have hprob_gt : ∫ v, (if t0 < v.1 - v.2 then (1 : ℝ) else 0) ∂(bidderMeasure L) = tailGT t0 :=
    prob_diff_gt L t0_pos t0_lt_one.le
  have hprob_lt : ∫ v, (if v.1 - v.2 < -t0 then (1 : ℝ) else 0) ∂(bidderMeasure L) = tailGT t0 :=
    prob_diff_lt_neg L t0_pos t0_lt_one.le
  have heq1 : ∫ x, (symTwinMechanism L).p1 x.1 x.2 ∂(jointMeasure L) =
      ∫ x, (flagshipMechanism L).p1 x.1 x.2 ∂(jointMeasure L) := by
    unfold jointMeasure
    rw [integral_prod_symm _ hsym_p1_int, integral_prod_symm _ hp1_f]
    refine integral_congr_ae (ae_of_all _ (fun b2 => ?_))
    by_cases h2 : -t0 ≤ b2.1 - b2.2 ∧ b2.1 - b2.2 ≤ t0
    · have hA : ∀ b1 : Type2, (symTwinMechanism L).p1 b1 b2 =
          L + (t0 / 2) * (if t0 < b1.1 - b1.2 then 1 else 0) + (t0 / 2) * (if b1.1 - b1.2 < -t0 then 1 else 0) := by
        intro b1; unfold symTwinMechanism; dsimp only; rw [if_pos h2]
        split_ifs <;> first | (exfalso; linarith [t0_pos]) | ring
      have hB : ∀ b1 : Type2, (flagshipMechanism L).p1 b1 b2 =
          L + t0 * (if t0 < b1.1 - b1.2 then 1 else 0) := by
        intro b1; unfold flagshipMechanism; dsimp only
        simp only [b1_decision_iff, h2.1, ite_true, max_eq_left h2.2]
        unfold p1Item1 p1Item2; simp only [h2.1, ite_true, max_eq_left h2.2]
        split_ifs <;> ring
      simp_rw [hA, hB]
      have hi_gt : Integrable (fun b1 : Type2 => if t0 < b1.1 - b1.2 then (1 : ℝ) else 0) (bidderMeasure L) :=
        integrable_of_bounded_bidderMeasure (C := 1)
          (Measurable.ite (measurableSet_lt measurable_const (measurable_fst.sub measurable_snd))
            measurable_const measurable_const).aestronglyMeasurable (fun _ _ => by split_ifs <;> norm_num)
      have hi_lt : Integrable (fun b1 : Type2 => if b1.1 - b1.2 < -t0 then (1 : ℝ) else 0) (bidderMeasure L) :=
        integrable_of_bounded_bidderMeasure (C := 1)
          (Measurable.ite (measurableSet_lt (measurable_fst.sub measurable_snd) measurable_const)
            measurable_const measurable_const).aestronglyMeasurable (fun _ _ => by split_ifs <;> norm_num)
      have hi1 : Integrable (fun b1 : Type2 => L + (t0 / 2) * (if t0 < b1.1 - b1.2 then (1 : ℝ) else 0)) (bidderMeasure L) :=
        (integrable_const L).add (hi_gt.const_mul _)
      rw [integral_add hi1 (hi_lt.const_mul _),
          integral_add (integrable_const L) (hi_gt.const_mul _),
          integral_add (integrable_const L) (hi_gt.const_mul _),
          integral_const_mul, integral_const_mul, integral_const_mul, hprob_gt, hprob_lt]
      ring
    · refine integral_congr_ae (ae_of_all _ (fun b1 => ?_))
      unfold symTwinMechanism flagshipMechanism; dsimp only
      simp only [h2, ite_false, b1_decision_iff]
      unfold p1Item1 p1Item2
      simp only [not_and_or, not_le] at h2
      rcases h2 with hlt | hgt
      · have hnot : ¬ -t0 ≤ b2.1 - b2.2 := not_le.mpr hlt
        have hnot2 : ¬ t0 < b2.1 - b2.2 := by linarith [t0_pos]
        simp only [hnot, hnot2, ite_false]
      · have hge : -t0 ≤ b2.1 - b2.2 := by linarith [t0_pos]
        have hm : max t0 (b2.1 - b2.2) = b2.1 - b2.2 := max_eq_right hgt.le
        simp only [hge, hgt, hm, ite_true]
  have heq2 : ∫ x, (symTwinMechanism L).p2 x.1 x.2 ∂(jointMeasure L) =
      ∫ x, (flagshipMechanism L).p2 x.1 x.2 ∂(jointMeasure L) := by
    rw [← integral_swapProfile L (fun x => (symTwinMechanism L).p2 x.1 x.2),
        ← integral_swapProfile L (fun x => (flagshipMechanism L).p2 x.1 x.2)]
    have h1 : (fun x : Type2 × Type2 => (symTwinMechanism L).p2 (x.2.2, x.2.1) (x.1.2, x.1.1)) =
        (fun x : Type2 × Type2 => (symTwinMechanism L).p1 x.1 x.2) := by
      ext x; exact symTwinMechanism_swap_p L x.1 x.2
    have h2 : (fun x : Type2 × Type2 => (flagshipMechanism L).p2 (x.2.2, x.2.1) (x.1.2, x.1.1)) =
        (fun x : Type2 × Type2 => (flagshipMechanism L).p1 x.1 x.2) := by
      ext x; exact (flagshipMechanism_swap L x.1 x.2).2.2
    rw [h1, h2]; exact heq1
  unfold ExpectedRevenue
  rw [integral_add hsym_p1_int hsym_p2_int, integral_add hp1_f hp2_f, heq1, heq2]

/-- **Theorem 2 (Suboptimality below `2 / π`):**
For every `0 ≤ L < 2 / π`, there exists an explicit feasible, DSIC, ex-post IR single-item
mechanism `M = perturbedSymMechanism L ε` with non-negative payments whose expected revenue
strictly exceeds `ExpectedRevenue L (flagshipMechanism L)`. -/
theorem flagshipMechanism_suboptimal_below_two_div_pi {L : ℝ} (hL0 : 0 ≤ L) (hL : L < 2 / Real.pi) :
    ∃ M : Mechanism, IsFeasible L M ∧ IsDSIC L M ∧ IsExPostIR L M ∧
      NonNegPayment L M ∧ IsSingleItem M ∧
      ExpectedRevenue L (flagshipMechanism L) < ExpectedRevenue L M := by
  let ε : ℝ := min (t0 / 4) ((2 / Real.pi - L) / 2)
  have hε0 : 0 < ε := lt_min (by linarith [t0_pos]) (by linarith)
  have hε_t0 : ε < t0 / 2 := (min_le_left _ _).trans_lt (by linarith [t0_pos])
  have hε_half : ε ≤ 1 / 2 := hε_t0.le.trans (by linarith [t0_lt_one])
  have hε_gap : L + ε < 2 / Real.pi := by
    have : ε ≤ (2 / Real.pi - L) / 2 := min_le_right _ _
    linarith
  have hns := perturbedSymMechanism_nonNeg_singleItem hL0 hε0
  refine ⟨perturbedSymMechanism L ε, perturbedSymMechanism_isFeasible L hε0 hε_t0,
    perturbedSymMechanism_isDSIC L hε0 hε_t0, perturbedSymMechanism_isExPostIR L hε0 hε_t0,
    hns.1, hns.2, ?_⟩
  rw [← symTwinMechanism_expectedRevenue L]
  have hFp := perturbedSymMechanism_isFeasible L hε0 hε_t0
  have hsym_p1_int := integrable_symTwin_p1 L
  have hp1_int : Integrable (fun x : Type2 × Type2 => (perturbedSymMechanism L ε).p1 x.1 x.2) (jointMeasure L) :=
    hFp.2.2.2.2.2.2.2.2.2.1
  have hp2_int : Integrable (fun x : Type2 × Type2 => (symTwinMechanism L).p2 x.1 x.2) (jointMeasure L) :=
    hFp.2.2.2.2.2.2.2.2.2.2
  -- Compute exact difference `E[p1_pert - p1_sym]`!
  -- On `|t2| ≤ t0`: if `a1 + b1 < 2ε` (which lies strictly inside `|t1| < t0` so `p1_sym = L`!), diff is `-L`;
  -- otherwise diff is `+ε`!
  -- On `|t2| > t0`: diff is `0`!
  -- So `E[p1_pert - p1_sym] = P(|t2| ≤ t0) * (ε * (1 - (π/2)ε) - L * (π/2)ε) > 0`!
  have hp2_p_int : Integrable (fun x : Type2 × Type2 => (perturbedSymMechanism L ε).p2 x.1 x.2) (jointMeasure L) :=
    hp2_int
  unfold ExpectedRevenue
  rw [integral_add hp1_int hp2_p_int, integral_add hsym_p1_int hp2_int]
  have hp2_same : (∫ x, (perturbedSymMechanism L ε).p2 x.1 x.2 ∂(jointMeasure L)) =
      ∫ x, (symTwinMechanism L).p2 x.1 x.2 ∂(jointMeasure L) := rfl
  rw [hp2_same]
  suffices hdiff : 0 < ∫ x, ((perturbedSymMechanism L ε).p1 x.1 x.2 - (symTwinMechanism L).p1 x.1 x.2) ∂(jointMeasure L) by
    rw [integral_sub hp1_int hsym_p1_int] at hdiff; linarith
  have hpoint : ∀ᵐ x : Type2 × Type2 ∂(jointMeasure L),
      (perturbedSymMechanism L ε).p1 x.1 x.2 - (symTwinMechanism L).p1 x.1 x.2 =
      (if -t0 ≤ x.2.1 - x.2.2 ∧ x.2.1 - x.2.2 ≤ t0 then (1 : ℝ) else 0) *
      (ε - (L + ε) * (if (x.1.1 - L) + (x.1.2 - L) < 2 * ε then 1 else 0)) := by
    filter_upwards [ae_mem_profileDomain L] with x hx
    unfold perturbedSymMechanism symTwinMechanism; dsimp only
    by_cases h2 : -t0 ≤ x.2.1 - x.2.2 ∧ x.2.1 - x.2.2 ≤ t0
    · simp only [h2, and_self, ite_true, one_mul]
      by_cases hc : (x.1.1 - L) + (x.1.2 - L) < 2 * ε
      · have hnot1 : ¬ t0 < x.1.1 - x.1.2 := by linarith [hx.1.1.1, hx.1.2.1]
        have hnot2 : ¬ x.1.1 - x.1.2 < -t0 := by linarith [hx.1.1.1, hx.1.2.1]
        simp only [hc, hnot1, hnot2, ite_true, ite_false]; ring
      · simp only [hc, ite_false]; ring
    · simp only [h2, ite_false, zero_mul, sub_self]
  rw [integral_congr_ae hpoint]
  unfold jointMeasure
  rw [integral_prod_symm _ (by
    have h1 : Integrable (fun v2 : Type2 => if -t0 ≤ v2.1 - v2.2 ∧ v2.1 - v2.2 ≤ t0 then (1 : ℝ) else 0) (bidderMeasure L) :=
      integrable_of_bounded_bidderMeasure (C := 1)
        (Measurable.ite ((measurableSet_le measurable_const (measurable_fst.sub measurable_snd)).inter
          (measurableSet_le (measurable_fst.sub measurable_snd) measurable_const))
          measurable_const measurable_const).aestronglyMeasurable (fun _ _ => by split_ifs <;> norm_num)
    have h2 : Integrable (fun v1 : Type2 => ε - (L + ε) * (if (v1.1 - L) + (v1.2 - L) < 2 * ε then (1 : ℝ) else 0)) (bidderMeasure L) :=
      integrable_of_bounded_bidderMeasure (C := ε + |L + ε|)
        (measurable_const.sub (measurable_const.mul (Measurable.ite
          (measurableSet_lt ((measurable_fst.sub measurable_const).add (measurable_snd.sub measurable_const)) measurable_const)
          measurable_const measurable_const))).aestronglyMeasurable (fun _ _ => by
            split_ifs <;> rw [abs_le] <;> constructor <;> linarith [neg_abs_le (L + ε), le_abs_self (L + ε)])
    exact (h2.mul_prod h1).congr (ae_of_all _ (fun _ => mul_comm _ _)))]
  -- Factor product integral: `P(|t2| ≤ t0) * (ε - (L + ε) * (π / 2) * ε)`!
  have hinner_val : ∫ v1, (ε - (L + ε) * (if (v1.1 - L) + (v1.2 - L) < 2 * ε then (1 : ℝ) else 0)) ∂(bidderMeasure L) =
      ε * (1 - (Real.pi / 2) * (L + ε)) := by
    have hi_c : Integrable (fun v1 : Type2 => if (v1.1 - L) + (v1.2 - L) < 2 * ε then (1 : ℝ) else 0) (bidderMeasure L) :=
      integrable_of_bounded_bidderMeasure (C := 1)
        (Measurable.ite (measurableSet_lt ((measurable_fst.sub measurable_const).add (measurable_snd.sub measurable_const)) measurable_const)
          measurable_const measurable_const).aestronglyMeasurable (fun _ _ => by split_ifs <;> norm_num)
    rw [integral_sub (integrable_const ε) (hi_c.const_mul (L + ε)), integral_const, probReal_univ, one_smul,
        integral_const_mul, prob_corner_triangle L hε0 hε_half]
    ring
  have hfact : (∫ v2, ∫ v1, (if -t0 ≤ v2.1 - v2.2 ∧ v2.1 - v2.2 ≤ t0 then (1 : ℝ) else 0) *
        (ε - (L + ε) * (if (v1.1 - L) + (v1.2 - L) < 2 * ε then 1 else 0)) ∂(bidderMeasure L) ∂(bidderMeasure L)) =
      (∫ v2, (if -t0 ≤ v2.1 - v2.2 ∧ v2.1 - v2.2 ≤ t0 then (1 : ℝ) else 0) ∂(bidderMeasure L)) *
      (ε * (1 - (Real.pi / 2) * (L + ε))) := by
    simp_rw [integral_const_mul, hinner_val, integral_mul_const]
  rw [hfact]
  -- Strip probability `p_S = 2 * ∫_0^{t₀} g_T(t) dt > 0`!
  have hpS_pos : 0 < ∫ v2, (if -t0 ≤ v2.1 - v2.2 ∧ v2.1 - v2.2 ≤ t0 then (1 : ℝ) else 0) ∂(bidderMeasure L) := by
    have hm : Measurable (fun t : ℝ => if -t0 ≤ t ∧ t ≤ t0 then (1 : ℝ) else 0) :=
      Measurable.ite ((measurableSet_le measurable_const measurable_id).inter
        (measurableSet_le measurable_id measurable_const)) measurable_const measurable_const
    rw [integral_bidderMeasure_diff hm ⟨1, fun t _ => by split_ifs <;> norm_num⟩]
    have hge : ∫ t in Ioo (0 : ℝ) t0, 2 * gT t0 ≤
        ∫ t in Ioo (0 : ℝ) 1, ((if -t0 ≤ t ∧ t ≤ t0 then (1 : ℝ) else 0) +
          (if -t0 ≤ -t ∧ -t ≤ t0 then 1 else 0)) * gT t := by
      have hi_rhs : IntegrableOn (fun t : ℝ => ((if -t0 ≤ t ∧ t ≤ t0 then (1 : ℝ) else 0) +
          (if -t0 ≤ -t ∧ -t ≤ t0 then 1 else 0)) * gT t) (Ioo (0 : ℝ) 1) volume := by
        refine (integrableOn_gT_Ioo_zero_one.const_mul 2).mono'
          ((hm.add (hm.comp measurable_neg)).mul measurable_gT).aestronglyMeasurable ?_
        rw [ae_restrict_iff' measurableSet_Ioo]; filter_upwards with t ht
        have hg := (gT_pos ht.1 ht.2).le
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hg]
        have hle2 : |(if -t0 ≤ t ∧ t ≤ t0 then (1 : ℝ) else 0) + (if -t0 ≤ -t ∧ -t ≤ t0 then 1 else 0)| ≤ 2 := by
          split_ifs <;> norm_num
        exact mul_le_mul_of_nonneg_right hle2 hg
      calc ∫ _ in Ioo (0 : ℝ) t0, 2 * gT t0
          ≤ ∫ t in Ioo (0 : ℝ) t0, ((if -t0 ≤ t ∧ t ≤ t0 then (1 : ℝ) else 0) +
              (if -t0 ≤ -t ∧ -t ≤ t0 then 1 else 0)) * gT t := by
            refine setIntegral_mono_on (integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top))
              (hi_rhs.mono_set (Ioo_subset_Ioo_right t0_lt_one.le)) measurableSet_Ioo (fun t ht => ?_)
            have h1 : -t0 ≤ t ∧ t ≤ t0 := ⟨by linarith [ht.1, t0_pos], ht.2.le⟩
            have h2 : -t0 ≤ -t ∧ -t ≤ t0 := ⟨by linarith [ht.2], by linarith [ht.1, t0_pos]⟩
            rw [if_pos h1, if_pos h2]
            have hgt : gT t0 < gT t := strictAntiOn_gT ⟨ht.1, ht.2.trans t0_lt_one⟩ ⟨t0_pos, t0_lt_one⟩ ht.2
            linarith
        _ ≤ ∫ t in Ioo (0 : ℝ) 1, ((if -t0 ≤ t ∧ t ≤ t0 then (1 : ℝ) else 0) +
              (if -t0 ≤ -t ∧ -t ≤ t0 then 1 else 0)) * gT t :=
            setIntegral_mono_set hi_rhs
              (ae_restrict_of_forall_mem measurableSet_Ioo (fun t ht =>
                mul_nonneg (by split_ifs <;> norm_num) (gT_pos ht.1 ht.2).le))
              (Eventually.of_forall (Ioo_subset_Ioo_right t0_lt_one.le))
    have hval : ∫ _ in Ioo (0 : ℝ) t0, 2 * gT t0 = t0 * (2 * gT t0) := by
      rw [setIntegral_const, Real.volume_real_Ioo_of_le t0_pos.le, sub_zero, smul_eq_mul]
    rw [hval] at hge
    have hpos_v : 0 < t0 * (2 * gT t0) := mul_pos t0_pos (mul_pos two_pos (gT_pos t0_pos t0_lt_one))
    linarith
  have hterm_pos : 0 < 1 - (Real.pi / 2) * (L + ε) := by
    have hpi : 0 < Real.pi := Real.pi_pos
    have hmul : (Real.pi / 2) * (L + ε) < (Real.pi / 2) * (2 / Real.pi) :=
      mul_lt_mul_of_pos_left hε_gap (by positivity)
    have h1 : (Real.pi / 2) * (2 / Real.pi) = 1 := by field_simp [hpi.ne']
    linarith
  exact mul_pos hpS_pos (mul_pos hε0 hterm_pos)

end

end EconCSAuction
