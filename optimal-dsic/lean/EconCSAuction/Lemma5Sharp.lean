import EconCSAuction.Lemma5
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Lemma 5 (sharp form): strip dominance for every `L ≥ 2/π`

* Radial bound with an angular weight `G`: `w(c, 0) ≤ ∫_{T_c} D ρ G` whenever `G` is constant
  along rays and normalised (`∫ gw · arctanWeight = 1`); uses `g₂ ≤ g₁` below the diagonal.
* Smooth convex-combination weight `G(c, ·) = 2 J(c) G₁ + (1 - 2 J(c)) (8/π - G₁)`, where
  `J(c) = ∫_c^{t₀} K = √(1 - c)/2 - 2 c g_T(c) ∈ [0, 1/2]` and `G₁ = 4√(ab)/(a + b)`.
* Exact Fubini rewriting of Term A and Term B as integrals against the deficit `D`.
* Two-case elementary pointwise inequality `W_A + ψ/ρ ≤ 2/π` on the half strip (`sharp_pointwise`).

The constant `2/π` is sharp: see `flagshipMechanism_suboptimal_below_two_div_pi`.
-/

open MeasureTheory Set

namespace EconCSAuction

noncomputable section

/-! ### 0. A sublevel-set Fubini swap -/

lemma integral_swap_sublevel {X : Type*} [MeasurableSpace X] {ν : Measure X} [SFinite ν]
    {S : Set X} (hS : MeasurableSet S) {h : X → ℝ} (hh : Measurable h)
    {k : ℝ → ℝ} {F : X → ℝ} {c0 T : ℝ}
    (hk : IntegrableOn k (Ioo c0 T) volume) (hF : IntegrableOn F S ν) :
    ∫ c in Ioo c0 T, k c * (∫ x in S ∩ {x | h x < c}, F x ∂ν) =
      ∫ x in S, F x * (∫ c in Ioo (max (h x) c0) T, k c) ∂ν := by
  let E : Set (ℝ × X) := {p | h p.2 < p.1}
  have hE : MeasurableSet E := measurableSet_lt (hh.comp measurable_snd) measurable_fst
  have hint : Integrable (E.indicator (fun p : ℝ × X => k p.1 * F p.2))
      ((volume.restrict (Ioo c0 T)).prod (ν.restrict S)) :=
    (Integrable.mul_prod hk hF).indicator hE
  have hswap := integral_integral_swap
    (f := fun c x => E.indicator (fun p : ℝ × X => k p.1 * F p.2) (c, x)) hint
  have hL : ∀ c : ℝ, ∫ x, E.indicator (fun p : ℝ × X => k p.1 * F p.2) (c, x) ∂(ν.restrict S) =
      k c * ∫ x in S ∩ {x | h x < c}, F x ∂ν := by
    intro c
    have hm : MeasurableSet {x : X | h x < c} := measurableSet_lt hh measurable_const
    have e1 : (fun x => E.indicator (fun p : ℝ × X => k p.1 * F p.2) (c, x)) =
        {x : X | h x < c}.indicator (fun x => k c * F x) := by
      ext x; by_cases hx : h x < c
      · rw [indicator_of_mem (show (c, x) ∈ E from hx),
          indicator_of_mem (show x ∈ {x : X | h x < c} from hx)]
      · rw [indicator_of_notMem (show (c, x) ∉ E from hx),
          indicator_of_notMem (show x ∉ {x : X | h x < c} from hx)]
    rw [e1, integral_indicator hm, Measure.restrict_restrict hm, inter_comm, integral_const_mul]
  have hR : ∀ x : X,
      ∫ c, E.indicator (fun p : ℝ × X => k p.1 * F p.2) (c, x) ∂(volume.restrict (Ioo c0 T)) =
      F x * ∫ c in Ioo (max (h x) c0) T, k c := by
    intro x
    have e1 : (fun c => E.indicator (fun p : ℝ × X => k p.1 * F p.2) (c, x)) =
        (Ioi (h x)).indicator (fun c => k c * F x) := by
      ext c; by_cases hc : h x < c
      · rw [indicator_of_mem (show (c, x) ∈ E from hc),
          indicator_of_mem (show c ∈ Ioi (h x) from hc)]
      · rw [indicator_of_notMem (show (c, x) ∉ E from hc),
          indicator_of_notMem (show c ∉ Ioi (h x) from hc)]
    have e2 : Ioi (h x) ∩ Ioo c0 T = Ioo (max (h x) c0) T := by
      ext c
      exact ⟨fun hc => ⟨max_lt hc.1 hc.2.1, hc.2.2⟩,
        fun hc => ⟨(le_max_left _ _).trans_lt hc.1, (le_max_right _ _).trans_lt hc.1, hc.2⟩⟩
    rw [e1, integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi, e2,
      integral_mul_const, mul_comm]
  calc ∫ c in Ioo c0 T, k c * (∫ x in S ∩ {x | h x < c}, F x ∂ν)
      = ∫ c in Ioo c0 T,
          ∫ x, E.indicator (fun p : ℝ × X => k p.1 * F p.2) (c, x) ∂(ν.restrict S) :=
        integral_congr_ae (ae_of_all _ fun c => (hL c).symm)
    _ = ∫ x in S, ∫ c, E.indicator (fun p : ℝ × X => k p.1 * F p.2) (c, x)
          ∂(volume.restrict (Ioo c0 T)) ∂ν := hswap
    _ = ∫ x in S, F x * (∫ c in Ioo (max (h x) c0) T, k c) ∂ν :=
        integral_congr_ae (ae_of_all _ hR)

/-! ### 1. The radial weight `1 / (2 √η (1 + η))` integrates to `π / 4` -/

/-- Radial weight `1 / (2 √η (1 + η))`. -/
def arctanWeight (η : ℝ) : ℝ := 1 / (2 * Real.sqrt η * (1 + η))

lemma hasDerivAt_arctan_sqrt {η : ℝ} (hη : 0 < η) :
    HasDerivAt (fun x => Real.arctan (Real.sqrt x)) (arctanWeight η) η := by
  refine (Real.hasDerivAt_sqrt hη.ne').arctan.congr_deriv ?_
  unfold arctanWeight
  rw [Real.sq_sqrt hη.le, div_mul_div_comm, one_mul]
  congr 1; ring

lemma integrableOn_arctanWeight : IntegrableOn arctanWeight (Ioo (0 : ℝ) 1) volume := by
  refine integrableOn_density1D_Ioo.mono'
    (by unfold arctanWeight; fun_prop : Measurable arctanWeight).aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ioo]; filter_upwards with η hη
  have hs : 0 < Real.sqrt η := Real.sqrt_pos.mpr hη.1
  have h2s : 0 < 2 * Real.sqrt η := by linarith
  have hden : 0 < 2 * Real.sqrt η * (1 + η) := mul_pos h2s (by linarith [hη.1])
  unfold arctanWeight density1D
  rw [Real.norm_eq_abs, abs_of_nonneg (one_div_pos.mpr hden).le]
  apply one_div_le_one_div_of_le h2s
  nlinarith [mul_pos hs hη.1]

lemma integral_arctanWeight : ∫ η in Ioo (0 : ℝ) 1, arctanWeight η = Real.pi / 4 := by
  have hcont : ContinuousOn (fun x => Real.arctan (Real.sqrt x)) (Icc (0 : ℝ) 1) :=
    (Real.continuous_arctan.comp Real.continuous_sqrt).continuousOn
  have hint : IntervalIntegrable arctanWeight volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mpr integrableOn_arctanWeight
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hcont
    (fun x hx => hasDerivAt_arctan_sqrt hx.1) hint
  rw [intervalIntegral.integral_of_le zero_le_one, ← setIntegral_congr_set Ioo_ae_eq_Ioc] at h
  rw [h]; simp [Real.arctan_one]

/-! ### 2. Closed form of `∫_x^{t₀} K` and the weight `W_A` -/

lemma hasDerivAt_F0 {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) :
    HasDerivAt (fun t : ℝ => 2 * t * gT t - Real.sqrt (1 - t) / 2) (K c) c := by
  have h1c : 0 < 1 - c := by linarith
  have hd1 : HasDerivAt (fun t : ℝ => 2 * t * gT t)
      (2 * gT c + 2 * c * (-(1 / (4 * c * Real.sqrt (1 - c))))) c := by
    have h2t : HasDerivAt (fun t : ℝ => 2 * t) 2 c := by
      simpa using (hasDerivAt_id c).const_mul (2 : ℝ)
    exact h2t.mul (hasDerivAt_gT hc0 hc1)
  have hd2 : HasDerivAt (fun t : ℝ => Real.sqrt (1 - t) / 2) (-(1 / (4 * Real.sqrt (1 - c)))) c := by
    have h1 : HasDerivAt (fun t : ℝ => 1 - t) (-1) c := by
      simpa using (hasDerivAt_id c).const_sub (1 : ℝ)
    exact (((Real.hasDerivAt_sqrt h1c.ne').comp c h1).div_const (2 : ℝ)).congr_deriv (by ring)
  refine (hd1.sub hd2).congr_deriv ?_
  unfold K
  have hsq : Real.sqrt (1 - c) ≠ 0 := (Real.sqrt_pos.mpr h1c).ne'
  field_simp [hc0.ne', hsq]
  ring

lemma F0_t0 : 2 * t0 * gT t0 - Real.sqrt (1 - t0) / 2 = 0 := by
  have hphi := PhiPlus_t0
  unfold PhiPlus at hphi
  have hs0 : 0 < Real.sqrt (1 - t0) := Real.sqrt_pos.mpr (by linarith [t0_lt_one])
  have hs1 : Real.sqrt (1 - t0) < 1 := by rw [Real.sqrt_lt' zero_lt_one]; linarith [t0_pos]
  have hA : artanh (Real.sqrt (1 - t0)) ≠ 0 := (artanh_pos hs0 hs1).ne'
  have hmul : 2 * t0 * artanh (Real.sqrt (1 - t0)) = Real.sqrt (1 - t0) := by
    have : Real.sqrt (1 - t0) / artanh (Real.sqrt (1 - t0)) = 2 * t0 := by linarith
    exact ((div_eq_iff hA).mp this).symm
  unfold gT
  linarith

lemma integral_K_Ioo {x : ℝ} (hx0 : 0 < x) (hx : x ≤ t0) :
    ∫ c in Ioo x t0, K c = Real.sqrt (1 - x) / 2 - 2 * x * gT x := by
  have hcont : ContinuousOn (fun t : ℝ => 2 * t * gT t - Real.sqrt (1 - t) / 2) (Icc x t0) :=
    fun c hc => (hasDerivAt_F0 (hx0.trans_le hc.1) (hc.2.trans_lt t0_lt_one)).continuousAt.continuousWithinAt
  have hint : IntervalIntegrable K volume x t0 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hx).mpr
      (integrableOn_K_Ioo_t0.mono_set (Ioo_subset_Ioo_left hx0.le))
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx hcont
    (fun c hc => hasDerivAt_F0 (hx0.trans hc.1) (hc.2.trans t0_lt_one)) hint
  rw [intervalIntegral.integral_of_le hx, ← setIntegral_congr_set Ioo_ae_eq_Ioc] at h
  rw [h, F0_t0]; ring

/-! ### 3. Elementary numeric and logarithmic inequalities -/

/-- `-z log z ≤ e^{-a} + (a - 1) z` for every `z > 0` (tangent-line bound for `log`). -/
lemma neg_mul_log_le {z : ℝ} (hz : 0 < z) (a : ℝ) :
    -(z * Real.log z) ≤ Real.exp (-a) + (a - 1) * z := by
  have hpos : 0 < Real.exp (-a) / z := div_pos (Real.exp_pos _) hz
  have h := Real.log_le_sub_one_of_pos hpos
  rw [Real.log_div (Real.exp_pos _).ne' hz.ne', Real.log_exp] at h
  have hmul := mul_le_mul_of_nonneg_left h hz.le
  have hcancel : z * (Real.exp (-a) / z - 1) = Real.exp (-a) - z := by field_simp
  rw [hcancel] at hmul
  nlinarith

lemma exp_neg_3_2_le : Real.exp (-(3 / 2)) ≤ 1 / 4 := by
  have h1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have h2 : (1 : ℝ) / 2 + 1 ≤ Real.exp (1 / 2) := Real.add_one_le_exp _
  have h3 : Real.exp (3 / 2) = Real.exp 1 * Real.exp (1 / 2) := by
    rw [← Real.exp_add]; norm_num
  have h4 : (4 : ℝ) ≤ Real.exp (3 / 2) := by rw [h3]; nlinarith
  have hke : Real.exp (-(3 / 2)) * Real.exp (3 / 2) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  nlinarith [Real.exp_pos (-(3 / 2))]

lemma sixteen_exp_neg_3_2_le : 16 * Real.exp (-(3 / 2)) ≤ 39 / 10 := by
  have h1 : (2.7 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
  have h3 : Real.exp 3 = Real.exp 1 * Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add, ← Real.exp_add]; norm_num
  have hsq : Real.exp (3 / 2) ^ 2 = Real.exp 3 := by
    rw [sq, ← Real.exp_add]; norm_num
  have he3 : (19.683 : ℝ) < Real.exp (3 / 2) ^ 2 := by
    rw [hsq, h3]; nlinarith [mul_pos (by norm_num : (0 : ℝ) < 2.7) (by norm_num : (0 : ℝ) < 2.7)]
  have hge : (160 : ℝ) / 39 ≤ Real.exp (3 / 2) := by
    by_contra h
    have hlt : Real.exp (3 / 2) < 160 / 39 := not_le.mp h
    nlinarith [Real.exp_pos (3 / 2)]
  have hke : Real.exp (-(3 / 2)) * Real.exp (3 / 2) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  nlinarith [Real.exp_pos (-(3 / 2))]

lemma log_four : Real.log 4 = 2 * Real.log 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring

/-- Chord bound for the concave function `log`: `log (1 + u) ≥ (2/3) u` on `[0, 1]`. -/
lemma log_one_add_ge {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) : 2 / 3 * u ≤ Real.log (1 + u) := by
  have hc := strictConcaveOn_log_Ioi.concaveOn.2 (show (1 : ℝ) ∈ Ioi 0 by norm_num)
    (show (2 : ℝ) ∈ Ioi 0 by norm_num) (sub_nonneg.mpr hu1) hu0 (by ring : 1 - u + u = 1)
  simp only [smul_eq_mul, Real.log_one, mul_zero, zero_add] at hc
  have h2 : (1 - u) * 1 + u * 2 = 1 + u := by ring
  rw [h2] at hc
  nlinarith [Real.log_two_gt_d9]

/-! ### 4. Tail kernel `J(x) = ∫_x^{t₀} K` and the smooth Term-A weight `W_A` -/

/-- Tail integral `J(x) = ∫_{max(x, 0)}^{t₀} K(c) dc`. -/
def Jtail (x : ℝ) : ℝ := ∫ c in Ioo (max x 0) t0, K c

lemma K_nonneg_ae_Ioo {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ t0) :
    0 ≤ᵐ[volume.restrict (Ioo a b)] K :=
  ae_restrict_of_forall_mem measurableSet_Ioo
    (fun c hc => (K_pos (ha.trans_lt hc.1) (hc.2.le.trans hb)).le)

lemma antitone_Jtail : Antitone Jtail := fun x y hxy =>
  setIntegral_mono_set
    (integrableOn_K_Ioo_t0.mono_set (Ioo_subset_Ioo (le_max_right _ _) le_rfl))
    (K_nonneg_ae_Ioo (le_max_right _ _) le_rfl)
    (Filter.Eventually.of_forall (Ioo_subset_Ioo_left (max_le_max_right 0 hxy)))

lemma Jtail_nonneg (x : ℝ) : 0 ≤ Jtail x :=
  setIntegral_nonneg measurableSet_Ioo
    (fun c hc => (K_pos ((le_max_right x 0).trans_lt hc.1) hc.2.le).le)

lemma Jtail_le_half (x : ℝ) : Jtail x ≤ 1 / 2 := by
  rw [← integral_K_Ioo_t0]
  exact setIntegral_mono_set integrableOn_K_Ioo_t0
    (K_nonneg_ae_Ioo le_rfl le_rfl)
    (Filter.Eventually.of_forall (Ioo_subset_Ioo_left (le_max_right _ _)))

lemma Jtail_of_pos_le {x : ℝ} (hx0 : 0 < x) (hx : x ≤ t0) :
    Jtail x = Real.sqrt (1 - x) / 2 - 2 * x * gT x := by
  unfold Jtail; rw [max_eq_left hx0.le]; exact integral_K_Ioo hx0 hx

lemma Jtail_of_ge_t0 {x : ℝ} (hx : t0 ≤ x) : Jtail x = 0 := by
  unfold Jtail
  rw [Ioo_eq_empty (not_lt.mpr (hx.trans (le_max_left _ _))), Measure.restrict_empty,
    integral_zero_measure]

/-- Exact antiderivative identity: `∫_{max(x, 0)}^{t₀} K(c) (2 J(c)) dc = J(x)²` for `x > 0`. -/
lemma integral_K_mul_two_Jtail {x : ℝ} (hx0 : 0 < x) :
    ∫ c in Ioo (max x 0) t0, K c * (2 * Jtail c) = Jtail x ^ 2 := by
  by_cases hxt : x < t0
  · rw [max_eq_left hx0.le, Jtail_of_pos_le hx0 hxt.le]
    let Jf : ℝ → ℝ := fun t => Real.sqrt (1 - t) / 2 - 2 * t * gT t
    have hJf_deriv : ∀ c ∈ Ioo x t0, HasDerivAt Jf (-K c) c := fun c hc => by
      have hd := (hasDerivAt_F0 (hx0.trans hc.1) (hc.2.trans t0_lt_one)).neg
      exact (hd.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => by dsimp [Jf]; ring))
    have hcont : ContinuousOn (fun t => -(Jf t ^ 2)) (Icc x t0) := by
      intro c hc
      have hd := (hasDerivAt_F0 (hx0.trans_le hc.1) (hc.2.trans_lt t0_lt_one)).neg
      have hcJ : ContinuousAt Jf c :=
        (hd.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => by dsimp [Jf]; ring)).continuousAt
      exact ((hcJ.pow 2).neg).continuousWithinAt
    have hderiv : ∀ c ∈ Ioo x t0, HasDerivAt (fun t => -(Jf t ^ 2)) (K c * (2 * Jf c)) c := by
      intro c hc
      exact (((hJf_deriv c hc).pow 2).neg).congr_deriv (by ring)
    have hcongr : ∀ c ∈ Ioo x t0, K c * (2 * Jtail c) = K c * (2 * Jf c) := fun c hc => by
      rw [Jtail_of_pos_le (hx0.trans hc.1) hc.2.le]
    have hint_on : IntegrableOn (fun c => K c * (2 * Jf c)) (Ioo x t0) volume := by
      refine ((integrableOn_K_Ioo_t0.mono_set (Ioo_subset_Ioo_left hx0.le)).abs).mono'
        (((by unfold K gT artanh; fun_prop : Measurable K).mul
          (measurable_const.mul (antitone_Jtail.measurable))).aestronglyMeasurable.congr
          (ae_restrict_of_forall_mem measurableSet_Ioo hcongr)) ?_
      rw [ae_restrict_iff' measurableSet_Ioo]; filter_upwards with c hc
      rw [← hcongr c hc, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (by linarith [Jtail_nonneg c] : 0 ≤ 2 * Jtail c)]
      exact mul_le_of_le_one_right (abs_nonneg _) (by linarith [Jtail_le_half c])
    have hint : IntervalIntegrable (fun c => K c * (2 * Jf c)) volume x t0 :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le hxt.le).mpr hint_on
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hxt.le hcont hderiv hint
    rw [intervalIntegral.integral_of_le hxt.le, ← setIntegral_congr_set Ioo_ae_eq_Ioc] at hftc
    rw [setIntegral_congr_fun measurableSet_Ioo hcongr, hftc]
    have hJt0 : Jf t0 = 0 := by dsimp [Jf]; linarith [F0_t0]
    rw [hJt0]; ring
  · have hge : t0 ≤ x := not_lt.mp hxt
    rw [Jtail_of_ge_t0 hge, Ioo_eq_empty (not_lt.mpr (hge.trans (le_max_left _ _))),
      Measure.restrict_empty, integral_zero_measure]
    ring

/-- Complementary integral: `∫_{max(x, 0)}^{t₀} K(c) (1 - 2 J(c)) dc = J(x) (1 - J(x))` for `x > 0`. -/
lemma integral_K_mul_one_sub_two_Jtail {x : ℝ} (hx0 : 0 < x) :
    ∫ c in Ioo (max x 0) t0, K c * (1 - 2 * Jtail c) = Jtail x * (1 - Jtail x) := by
  have hmK : Measurable K := by unfold K gT artanh; fun_prop
  have hK_int : IntegrableOn K (Ioo (max x 0) t0) volume :=
    integrableOn_K_Ioo_t0.mono_set (Ioo_subset_Ioo_left (le_max_right _ _))
  have hKJ_int : IntegrableOn (fun c => K c * (2 * Jtail c)) (Ioo (max x 0) t0) volume := by
    refine hK_int.abs.mono'
      (hmK.mul (measurable_const.mul antitone_Jtail.measurable)).aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Ioo]; filter_upwards with c _
    rw [Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (by linarith [Jtail_nonneg c] : 0 ≤ 2 * Jtail c)]
    exact mul_le_of_le_one_right (abs_nonneg _) (by linarith [Jtail_le_half c])
  have hrew : ∀ c ∈ Ioo (max x 0) t0, K c * (1 - 2 * Jtail c) = K c - K c * (2 * Jtail c) :=
    fun c _ => by ring
  rw [setIntegral_congr_fun measurableSet_Ioo hrew, integral_sub hK_int hKJ_int,
    integral_K_mul_two_Jtail hx0]
  unfold Jtail; ring

/-- Angular factor `2 sin(2θ) = 4 √(ab) / (a + b)` (constant along rays through the origin). -/
def G1 (ab : Type2) : ℝ := 4 * Real.sqrt (ab.1 * ab.2) / (ab.1 + ab.2)

/-- Smooth Term-A weight: `J(a+b)² G₁ + J(a+b)(1 - J(a+b)) (8/π - G₁)`. -/
def WA2 (ab : Type2) : ℝ :=
  Jtail (ab.1 + ab.2) ^ 2 * G1 ab +
    Jtail (ab.1 + ab.2) * (1 - Jtail (ab.1 + ab.2)) * (8 * (1 / Real.pi) - G1 ab)

/-! ### 5. Pointwise inequality `W_A + ψ/ρ ≤ 2/π` on the half strip -/

/-- Term-B kernel `ψ_t(r) = 2 ∫_r^{1-t} ρ(s + t, s) ds - ρ(1, 1 - t)`. -/
def psiB (t r : ℝ) : ℝ := 2 * (gT t - Iwing r t) - rho 1 (1 - t)

lemma two_x_gT {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    2 * x * gT x = x * Real.log (1 + Real.sqrt (1 - x)) - x / 2 * Real.log x := by
  unfold gT artanh
  set σ := Real.sqrt (1 - x) with hσ
  have hs_sq : σ ^ 2 = 1 - x := Real.sq_sqrt (by linarith)
  have hσ0 : 0 ≤ σ := Real.sqrt_nonneg _
  have hσ1 : σ < 1 := by rw [hσ, Real.sqrt_lt' zero_lt_one]; linarith
  have h1s : 0 < 1 - σ := by linarith
  have hY : (1 + σ) / (1 - σ) = (1 + σ) ^ 2 / x := by
    rw [div_eq_div_iff h1s.ne' hx0.ne', show x = 1 - σ ^ 2 by linarith]; ring
  rw [hY, Real.log_div (pow_pos (by linarith) 2).ne' hx0.ne', Real.log_pow]
  push_cast; ring

lemma four_z_psiB_le {t r : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (hr0 : 0 < r) :
    4 * Real.sqrt ((r + t) * r) * psiB t r ≤
      4 * Real.sqrt ((r + t) * r) * Real.log 2 -
        2 * Real.sqrt ((r + t) * r) * Real.log (r + t + r + 2 * Real.sqrt ((r + t) * r)) -
        Real.sqrt ((r + t) * r) := by
  have hrt : 0 < r + t := by linarith
  have ha : 0 < Real.sqrt (r + t) := Real.sqrt_pos.mpr hrt
  have hb : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr0
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have hz_eq : Real.sqrt ((r + t) * r) = Real.sqrt (r + t) * Real.sqrt r := Real.sqrt_mul hrt.le r
  have hz : 0 ≤ Real.sqrt ((r + t) * r) := Real.sqrt_nonneg _
  have hDn_sq : (Real.sqrt (r + t) + Real.sqrt r) ^ 2 =
      r + t + r + 2 * Real.sqrt ((r + t) * r) := by
    rw [hz_eq, add_sq, Real.sq_sqrt hrt.le, Real.sq_sqrt hr0.le]; ring
  have hlogDn : Real.log (Real.sqrt (r + t) + Real.sqrt r) =
      Real.log (r + t + r + 2 * Real.sqrt ((r + t) * r)) / 2 := by
    rw [← hDn_sq, Real.log_pow]; push_cast; ring
  have hs1 : Real.sqrt (1 - t) ≤ 1 := by
    calc Real.sqrt (1 - t) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt (by linarith)
      _ = 1 := Real.sqrt_one
  have hN0 : 0 < 1 + Real.sqrt (1 - t) := by linarith [Real.sqrt_nonneg (1 - t)]
  have h1 : Real.log (1 + Real.sqrt (1 - t)) ≤ Real.log 2 := Real.log_le_log hN0 (by linarith)
  have hG : gT t - Iwing r t ≤
      (Real.log 2 - Real.log (r + t + r + 2 * Real.sqrt ((r + t) * r)) / 2) / 2 := by
    rw [← Iwing_one_sub ht0 ht1]
    unfold Iwing
    have hsub : 1 - t + t = 1 := by ring
    rw [hsub, Real.sqrt_one, Real.log_div hN0.ne' hst.ne',
      Real.log_div (by linarith : Real.sqrt (r + t) + Real.sqrt r ≠ 0) hst.ne', hlogDn]
    linarith
  have hGz := mul_le_mul_of_nonneg_left hG hz
  have hs0 : 0 < Real.sqrt (1 * (1 - t)) := Real.sqrt_pos.mpr (by linarith)
  have hs1' : Real.sqrt (1 * (1 - t)) ≤ 1 := by
    calc Real.sqrt (1 * (1 - t)) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt (by linarith)
      _ = 1 := Real.sqrt_one
  have hrho : (1 : ℝ) / 4 ≤ rho 1 (1 - t) := by
    unfold rho
    have h := one_div_le_one_div_of_le (by linarith : (0 : ℝ) < 4 * Real.sqrt (1 * (1 - t)))
      (by linarith : 4 * Real.sqrt (1 * (1 - t)) ≤ 4)
    linarith
  have hR := mul_le_mul_of_nonneg_left hrho hz
  unfold psiB
  linarith

lemma arith_case3 {z l2 lz Cc p e Ψ4 : ℝ} (hz : 0 ≤ z)
    (hm : -(z * lz) ≤ e + (3 / 2 - 1) * z) (he : e ≤ 1 / 4) (hC4 : 2 * l2 + lz ≤ Cc)
    (hp1 : 7 / 22 ≤ p) (hU : Ψ4 ≤ 4 * z * l2 - 2 * z * Cc - z) : Ψ4 ≤ 2 * p := by
  have h := mul_le_mul_of_nonneg_left hC4 (by linarith : (0 : ℝ) ≤ 2 * z)
  linarith

/-- Tangent-line bound `(1 - 2 J(x))² ≤ (39/10) x` for `x ∈ (0, t₀)`. -/
lemma H_sq_le_39_10_mul {x : ℝ} (hx0 : 0 < x) (hxt : x < t0) :
    (1 - 2 * Jtail x) ^ 2 ≤ 39 / 10 * x := by
  have hx716 : x < 7 / 16 := hxt.trans t0_mem_bounds.2
  have hx1 : x < 1 := by linarith
  obtain ⟨σ, hσ⟩ : ∃ σ : ℝ, σ = Real.sqrt (1 - x) := ⟨_, rfl⟩
  have hs_sq : σ ^ 2 = 1 - x := by rw [hσ]; exact Real.sq_sqrt (by linarith)
  have hσ34 : 3 / 4 ≤ σ := by
    by_contra h; have h' : σ < 3 / 4 := not_le.mp h
    nlinarith [mul_pos (sub_pos.mpr h') (by linarith [Real.sqrt_nonneg (1 - x)] : (0 : ℝ) < 3 / 4 + σ)]
  have hσ1 : σ < 1 := by by_contra h; have h' : 1 ≤ σ := not_lt.mp h; nlinarith
  have h1σ : 0 < 1 + σ := by linarith
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = 1 / (1 + σ) := ⟨_, rfl⟩
  have hq_mul : q * (1 + σ) = 1 := by rw [hq]; field_simp
  have h1subσ : 1 - σ = x * q := by
    have hxf : x = (1 - σ) * (1 + σ) := by nlinarith [hs_sq]
    calc 1 - σ = (1 - σ) * (q * (1 + σ)) := by rw [hq_mul, mul_one]
      _ = (1 - σ) * (1 + σ) * q := by ring
      _ = x * q := by rw [← hxf]
  have hH0 : 0 ≤ 1 - 2 * Jtail x := by linarith [Jtail_le_half x]
  have hH_expr : 1 - 2 * Jtail x = x * (q + 2 * Real.log (1 + σ)) - x * Real.log x := by
    rw [Jtail_of_pos_le hx0 hxt.le, two_x_gT hx0 hx1, ← hσ]; linarith [h1subσ]
  have hcoeff_log : q + 2 * Real.log (1 + σ) ≤ 1 / 2 + 2 * Real.log 2 := by
    obtain ⟨v, hv⟩ : ∃ v : ℝ, v = (1 - σ) / 2 := ⟨_, rfl⟩
    have hv0 : 0 ≤ v := by linarith
    have hv1 : 1 - v = (1 + σ) / 2 := by linarith
    have hlv : Real.log (1 + σ) - Real.log 2 ≤ -v := by
      have h := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 1 - v)
      rw [hv1, Real.log_div h1σ.ne' two_ne_zero] at h; linarith
    have hinv : q - 1 / 2 ≤ 2 * v := by
      have hprod : 0 ≤ (2 * v - (q - 1 / 2)) * (1 + σ) := by
        have h1 : (2 * v - (q - 1 / 2)) * (1 + σ) = v * (1 + 2 * σ) := by
          linear_combination -hq_mul + hv
        rw [h1]; exact mul_nonneg hv0 (by linarith)
      linarith [nonneg_of_mul_nonneg_left hprod h1σ]
    linarith
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hlogx : Real.log x = 2 * Real.log (Real.sqrt x) := by
    calc Real.log x = Real.log (Real.sqrt x ^ 2) := by rw [Real.sq_sqrt hx0.le]
      _ = 2 * Real.log (Real.sqrt x) := by rw [Real.log_pow]; push_cast; ring
  have htan := neg_mul_log_le hsx (3 / 4 - Real.log 2)
  have hexp_rw : Real.exp (-(3 / 4 - Real.log 2)) = 2 * Real.exp (-(3 / 4)) := by
    rw [show -(3 / 4 - Real.log 2) = Real.log 2 + -(3 / 4) by ring, Real.exp_add, Real.exp_log two_pos]
  rw [hexp_rw] at htan
  have hmul := mul_le_mul_of_nonneg_left htan (by linarith : (0 : ℝ) ≤ 2 * Real.sqrt x)
  have hsqx : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
  have hneg_xlogx : -(x * Real.log x) ≤ 4 * Real.exp (-(3 / 4)) * Real.sqrt x -
      (1 / 2 + 2 * Real.log 2) * x := by
    have hrew1 : 2 * Real.sqrt x * -(Real.sqrt x * Real.log (Real.sqrt x)) = -(x * Real.log x) := by
      rw [hlogx]; linear_combination -2 * Real.log (Real.sqrt x) * hsqx
    have hrew2 : 2 * Real.sqrt x * (2 * Real.exp (-(3 / 4)) + (3 / 4 - Real.log 2 - 1) * Real.sqrt x) =
        4 * Real.exp (-(3 / 4)) * Real.sqrt x - (1 / 2 + 2 * Real.log 2) * x := by
      linear_combination -(1 / 2 + 2 * Real.log 2) * hsqx
    linarith
  have hH_le : 1 - 2 * Jtail x ≤ 4 * Real.exp (-(3 / 4)) * Real.sqrt x := by
    have hmul_c := mul_le_mul_of_nonneg_left hcoeff_log hx0.le
    linarith
  have hsq1 : (1 - 2 * Jtail x) ^ 2 ≤ (4 * Real.exp (-(3 / 4)) * Real.sqrt x) ^ 2 :=
    pow_le_pow_left₀ hH0 hH_le 2
  have hsq2 : (4 * Real.exp (-(3 / 4)) * Real.sqrt x) ^ 2 = 16 * Real.exp (-(3 / 2)) * x := by
    have hexp2 : Real.exp (-(3 / 4)) ^ 2 = Real.exp (-(3 / 2)) := by
      rw [sq, ← Real.exp_add]; norm_num
    calc (4 * Real.exp (-(3 / 4)) * Real.sqrt x) ^ 2
        = 16 * Real.exp (-(3 / 4)) ^ 2 * Real.sqrt x ^ 2 := by ring
      _ = 16 * Real.exp (-(3 / 2)) * x := by rw [hexp2, Real.sq_sqrt hx0.le]
  have h39 := mul_le_mul_of_nonneg_right sixteen_exp_neg_3_2_le hx0.le
  linarith

/-- Core inequality in the coordinates `x = a + b`, `z = √(ab)`. -/
lemma sharp_key {x z Ψ : ℝ} (hx0 : 0 < x) (hzpos : 0 < z) (h2z : 2 * z ≤ x)
    (hU : 4 * z * Ψ ≤ 4 * z * Real.log 2 - 2 * z * Real.log (x + 2 * z) - z) :
    Jtail x ^ 2 * (4 * z / x) + Jtail x * (1 - Jtail x) * (8 * (1 / Real.pi) - 4 * z / x) +
        4 * z * Ψ ≤ 2 * (1 / Real.pi) := by
  obtain ⟨s2, hs2⟩ : ∃ s2, s2 = 4 * z / x := ⟨_, rfl⟩
  rw [← hs2]
  have hs2x : s2 * x = 4 * z := by rw [hs2]; field_simp
  have hs2_0 : 0 ≤ s2 := by rw [hs2]; positivity
  have hs2_2 : s2 ≤ 2 := by rw [hs2, div_le_iff₀ hx0]; linarith
  have hp1 : (7 : ℝ) / 22 ≤ 1 / Real.pi := by
    have h := one_div_le_one_div_of_le Real.pi_pos (by linarith [Real.pi_lt_d4] : Real.pi ≤ 22 / 7)
    linarith
  by_cases hxt : x < t0
  · have hx716 : x < 7 / 16 := hxt.trans t0_mem_bounds.2
    have hx1 : x < 1 := by linarith
    obtain ⟨σ, hσ⟩ : ∃ σ, σ = Real.sqrt (1 - x) := ⟨_, rfl⟩
    have hs_sq : σ ^ 2 = 1 - x := by rw [hσ]; exact Real.sq_sqrt (by linarith)
    have hσ0 : 0 ≤ σ := by rw [hσ]; exact Real.sqrt_nonneg _
    have hσ34 : 3 / 4 ≤ σ := by
      by_contra h
      have h' : σ < 3 / 4 := not_le.mp h
      nlinarith [mul_pos (sub_pos.mpr h') (by linarith : (0 : ℝ) < 3 / 4 + σ)]
    have hσ1 : σ < 1 := by
      by_contra h
      have h' : 1 ≤ σ := not_lt.mp h
      nlinarith
    have h1σ : 0 < 1 + σ := by linarith
    have hJ0 : 0 ≤ Jtail x := Jtail_nonneg x
    have hJhalf : Jtail x ≤ 1 / 2 := Jtail_le_half x
    have hJ_eq : Jtail x = σ / 2 - (x * Real.log (1 + σ) - x / 2 * Real.log x) := by
      rw [Jtail_of_pos_le hx0 hxt.le, two_x_gT hx0 hx1, ← hσ]
    -- `H = 1 - 2 J(x) ∈ [0, 1]` satisfies `2/π - W_A = (2/π) H² + (1/2) H (1 - H) s2`
    obtain ⟨H, hH⟩ : ∃ H : ℝ, H = 1 - 2 * Jtail x := ⟨_, rfl⟩
    obtain ⟨p, hp⟩ : ∃ p : ℝ, p = 1 / Real.pi := ⟨_, rfl⟩
    rw [← hp] at hp1 ⊢
    have hH0 : 0 ≤ H := by linarith
    have hWA_id : 2 * p -
        (Jtail x ^ 2 * s2 + Jtail x * (1 - Jtail x) * (8 * p - s2)) =
        2 * p * H ^ 2 + (1 / 2) * H * (1 - H) * s2 := by
      rw [hH]; ring
    -- Chord bound `log (x + 2z) ≥ log x + s2 / 3`
    have h1s2 : 0 < 1 + s2 / 2 := by linarith
    have hCc_ge : Real.log x + s2 / 3 ≤ Real.log (x + 2 * z) := by
      have hfac : x + 2 * z = x * (1 + s2 / 2) := by linarith [hs2x]
      have hu := log_one_add_ge (by linarith : (0 : ℝ) ≤ s2 / 2) (by linarith)
      rw [hfac, Real.log_mul hx0.ne' h1s2.ne']
      linarith
    have hzs : z = s2 * x / 4 := by linarith [hs2x]
    have e_l2 : z * Real.log 2 = s2 * x * Real.log 2 / 4 := by rw [hzs]; ring
    have e_B : z * Real.log x = s2 * x * Real.log x / 4 := by rw [hzs]; ring
    have e_s : z * s2 = s2 * x * s2 / 4 := by rw [hzs]; ring
    have h1 := mul_le_mul_of_nonneg_left hCc_ge (by linarith : (0 : ℝ) ≤ 2 * z)
    have hT : 4 * z * Ψ ≤ s2 * x * Real.log 2 - s2 * x * Real.log x / 2 -
        s2 * x * s2 / 6 - s2 * x / 4 := by linarith
    -- Exact `x log x` cancellation: `H/2 - x (log 2 - log x / 2 - 1/4) ≥ (11/28) x`
    obtain ⟨q, hq⟩ : ∃ q : ℝ, q = 1 / (1 + σ) := ⟨_, rfl⟩
    have hq_mul : q * (1 + σ) = 1 := by rw [hq]; field_simp
    have h1subσ : 1 - σ = x * q := by
      have hxf : x = (1 - σ) * (1 + σ) := by nlinarith [hs_sq]
      calc 1 - σ = (1 - σ) * (q * (1 + σ)) := by rw [hq_mul, mul_one]
        _ = (1 - σ) * (1 + σ) * q := by ring
        _ = x * q := by rw [← hxf]
    have hH_expr : H = x * q + 2 * x * Real.log (1 + σ) - x * Real.log x := by
      rw [hH, hJ_eq]; linarith [h1subσ]
    have hlog_ratio : Real.log 2 - Real.log (1 + σ) ≤ 2 * q - 1 := by
      have h := Real.log_le_sub_one_of_pos (div_pos two_pos h1σ)
      rw [Real.log_div two_ne_zero h1σ.ne'] at h
      have h2q : 2 / (1 + σ) = 2 * q := by rw [hq]; ring
      linarith
    have hinv_le : q ≤ 4 / 7 := by rw [hq, div_le_iff₀ h1σ]; linarith
    have hlin_rem : 11 / 28 * x ≤ H / 2 - x * (Real.log 2 - Real.log x / 2 - 1 / 4) := by
      have hmid : H / 2 - x * (Real.log 2 - Real.log x / 2 - 1 / 4) =
          x * (q / 2 + 1 / 4 - (Real.log 2 - Real.log (1 + σ))) := by
        rw [hH_expr]; ring
      rw [hmid]
      have hcoeff : 11 / 28 ≤ q / 2 + 1 / 4 - (Real.log 2 - Real.log (1 + σ)) := by linarith
      linarith [mul_le_mul_of_nonneg_left hcoeff hx0.le]
    -- Combine into master gap bound: `2p - WA - Ψ4 ≥ (2p - s2/2) H² + (11/28) x s2 + s2² x / 6`
    have hmaster : (2 * p - s2 / 2) * H ^ 2 + 11 / 28 * x * s2 + s2 ^ 2 * x / 6 ≤
        2 * p - (Jtail x ^ 2 * s2 + Jtail x * (1 - Jtail x) * (8 * p - s2)) - 4 * z * Ψ := by
      rw [hWA_id]
      have hmul_rem := mul_le_mul_of_nonneg_right hlin_rem hs2_0
      have hring1 : 2 * p * H ^ 2 + (1 / 2) * H * (1 - H) * s2 -
          (s2 * x * Real.log 2 - s2 * x * Real.log x / 2 - s2 * x * s2 / 6 - s2 * x / 4) =
          (2 * p - s2 / 2) * H ^ 2 + (H / 2 - x * (Real.log 2 - Real.log x / 2 - 1 / 4)) * s2 +
          s2 ^ 2 * x / 6 := by ring
      linarith
    by_cases hs2_pi : s2 ≤ 4 * p
    · -- Case 1: `s2 ≤ 4/π`, every term is manifestly nonnegative
      have hterm1 : 0 ≤ (2 * p - s2 / 2) * H ^ 2 := mul_nonneg (by linarith) (sq_nonneg H)
      have hterm2 : 0 ≤ 11 / 28 * x * s2 := by positivity
      have hterm3 : 0 ≤ s2 ^ 2 * x / 6 := by positivity
      linarith
    · -- Case 2: `4/π < s2 ≤ 2`, apply `H² ≤ (39/10) x`
      have hneg_coeff : 2 * p - s2 / 2 < 0 := by linarith
      have hH_sq : H ^ 2 ≤ 39 / 10 * x := by rw [hH]; exact H_sq_le_39_10_mul hx0 hxt
      have hQ_nn : 0 ≤ (2 * p - s2 / 2) * (39 / 10) + 11 / 28 * s2 + s2 ^ 2 / 6 := by
        have hfac : (2 * p - s2 / 2) * (39 / 10) + 11 / 28 * s2 + s2 ^ 2 / 6 =
            (2 - s2) * (39 / 20 - 11 / 28 - (2 + s2) / 6) +
              (2 / 3 + 11 / 14 - 39 / 10 + 39 / 5 * p) := by ring
        rw [hfac]
        have h1 : 0 ≤ (2 - s2) * (39 / 20 - 11 / 28 - (2 + s2) / 6) :=
          mul_nonneg (by linarith) (by linarith)
        linarith
      have hstep : (2 * p - s2 / 2) * (39 / 10 * x) ≤ (2 * p - s2 / 2) * H ^ 2 :=
        mul_le_mul_of_nonpos_left hH_sq hneg_coeff.le
      have hQx : 0 ≤ x * ((2 * p - s2 / 2) * (39 / 10) + 11 / 28 * s2 + s2 ^ 2 / 6) :=
        mul_nonneg hx0.le hQ_nn
      have hQrew : x * ((2 * p - s2 / 2) * (39 / 10) + 11 / 28 * s2 + s2 ^ 2 / 6) =
          (2 * p - s2 / 2) * (39 / 10 * x) + 11 / 28 * x * s2 + s2 ^ 2 * x / 6 := by ring
      linarith
  · have hxt' : t0 ≤ x := not_lt.mp hxt
    rw [Jtail_of_ge_t0 hxt']
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, sub_zero,
      zero_add]
    have hC4 : 2 * Real.log 2 + Real.log z ≤ Real.log (x + 2 * z) := by
      have h := Real.log_le_log (by linarith : (0 : ℝ) < 4 * z) (by linarith : 4 * z ≤ x + 2 * z)
      rw [Real.log_mul (by norm_num) hzpos.ne', log_four] at h
      exact h
    exact arith_case3 hzpos.le (neg_mul_log_le hzpos (3 / 2)) exp_neg_3_2_le hC4 hp1 hU

/-- The sharp pointwise bound: on the half strip, `ρ · W_A + ψ ≤ (2/π) ρ`. -/
lemma sharp_pointwise {t r : ℝ} (ht : t ∈ Ioo (0 : ℝ) t0) (hr0 : 0 < r) :
    rho (r + t) r * WA2 (r + t, r) + psiB t r ≤ 2 * (1 / Real.pi) * rho (r + t) r := by
  have ht1 : t < 1 := ht.2.trans t0_lt_one
  have hprod : 0 < (r + t) * r := mul_pos (by linarith [ht.1]) hr0
  have hzpos : 0 < Real.sqrt ((r + t) * r) := Real.sqrt_pos.mpr hprod
  have hz_sq : Real.sqrt ((r + t) * r) ^ 2 = (r + t) * r := Real.sq_sqrt hprod.le
  have hx0 : 0 < r + t + r := by linarith [ht.1]
  have h2z : 2 * Real.sqrt ((r + t) * r) ≤ r + t + r := by
    by_contra h
    have h' : r + t + r < 2 * Real.sqrt ((r + t) * r) := not_le.mp h
    nlinarith [mul_pos (sub_pos.mpr h')
      (by linarith : (0 : ℝ) < 2 * Real.sqrt ((r + t) * r) + (r + t + r)), sq_nonneg t]
  have key := sharp_key hx0 hzpos h2z (four_z_psiB_le ht.1 ht1 hr0)
  have hWdef : WA2 (r + t, r) =
      Jtail (r + t + r) ^ 2 * (4 * Real.sqrt ((r + t) * r) / (r + t + r)) +
        Jtail (r + t + r) * (1 - Jtail (r + t + r)) *
          (8 * (1 / Real.pi) - 4 * Real.sqrt ((r + t) * r) / (r + t + r)) := rfl
  rw [hWdef]
  unfold rho
  obtain ⟨Wv, hWv⟩ : ∃ Wv, Wv = Jtail (r + t + r) ^ 2 * (4 * Real.sqrt ((r + t) * r) / (r + t + r)) +
      Jtail (r + t + r) * (1 - Jtail (r + t + r)) *
        (8 * (1 / Real.pi) - 4 * Real.sqrt ((r + t) * r) / (r + t + r)) := ⟨_, rfl⟩
  rw [← hWv] at key ⊢
  have hrw : 1 / (4 * Real.sqrt ((r + t) * r)) * Wv + psiB t r =
      1 / (4 * Real.sqrt ((r + t) * r)) * (Wv + 4 * Real.sqrt ((r + t) * r) * psiB t r) := by
    have h4 : 4 * Real.sqrt ((r + t) * r) ≠ 0 := by positivity
    rw [mul_add, ← mul_assoc, one_div_mul_cancel h4, one_mul]
  rw [hrw, mul_comm (2 * (1 / Real.pi))]
  exact mul_le_mul_of_nonneg_left key (by positivity)


/-! ### 6. Weighted radial bound -/

lemma integrableOn_mul_bdd_on {X : Type*} [MeasurableSpace X] {μ : Measure X} {S : Set X}
    (hS : MeasurableSet S) {F A : X → ℝ} {C : ℝ} (hF : IntegrableOn F S μ) (hA : Measurable A)
    (h0 : ∀ x ∈ S, 0 ≤ A x) (hC : ∀ x ∈ S, A x ≤ C) :
    IntegrableOn (fun x => F x * A x) S μ := by
  refine (hF.abs.const_mul C).mono' (hF.aestronglyMeasurable.mul hA.aestronglyMeasurable) ?_
  rw [ae_restrict_iff' hS]; filter_upwards with x hx
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (h0 x hx), mul_comm]
  exact mul_le_mul_of_nonneg_right (hC x hx) (abs_nonneg _)

lemma arctanWeight_eq {η : ℝ} (hη : 0 < η) :
    1 / (4 * Real.sqrt η) * (2 / (1 + η)) = arctanWeight η := by
  have hs : Real.sqrt η ≠ 0 := (Real.sqrt_pos.mpr hη).ne'
  have h1 : (1 + η) ≠ 0 := by linarith
  unfold arctanWeight
  rw [div_mul_div_comm, div_eq_div_iff (mul_ne_zero (mul_ne_zero four_ne_zero hs) h1)
    (mul_ne_zero (mul_ne_zero two_ne_zero hs) h1)]
  ring

lemma arctanWeight_nonneg {η : ℝ} (hη : 0 < η) : 0 ≤ arctanWeight η := by
  unfold arctanWeight
  exact one_div_nonneg.mpr (mul_nonneg (mul_nonneg zero_le_two (Real.sqrt_nonneg η)) (by linarith))

/-- Radial bound with an angular weight `G` that is constant (`= gw η`) along each ray. -/
lemma lemma5_ray_bound (Q : InterimProfile)
    (hQ_sym_u : ∀ a b, Q.u (b, a) = Q.u (a, b))
    (hQ_u0 : Q.u (0, 0) = 0) {c : ℝ} (hc : c ∈ Ioo (0 : ℝ) t0)
    {G : Type2 → ℝ} {gw : ℝ → ℝ} {C : ℝ} (hG_meas : Measurable G) (hgw_meas : Measurable gw)
    (hG : ∀ lam : ℝ, 0 < lam → ∀ η ∈ Ioo (0 : ℝ) 1, G (lam, lam * η) = gw η)
    (hg0 : ∀ η ∈ Ioo (0 : ℝ) 1, 0 ≤ gw η) (hgC : ∀ η ∈ Ioo (0 : ℝ) 1, gw η ≤ C) :
    let w : Type2 → ℝ := fun ab => (ab.1 + ab.2) / 2 - Q.u ab
    let D : Type2 → ℝ := fun ab => 1 - (Q.g1 ab + Q.g2 ab)
    (∫ η in Ioo (0 : ℝ) 1, gw η * arctanWeight η) * w (c, 0) ≤
      ∫ ab in {ab : Type2 | ab ∈ openUnitSquare ∧ ab.2 < ab.1 ∧ ab.1 + ab.2 < c},
        D ab * rho ab.1 ab.2 * G ab := by
  intro w D
  have hD_meas : Measurable D := measurable_const.sub (Q.g1_meas.add Q.g2_meas)
  have hD_bounds : ∀ ab ∈ unitSquare, 0 ≤ D ab ∧ D ab ≤ 1 := fun ab hab =>
    ⟨by dsimp only [D]; linarith [Q.g_sum_le ab hab],
     by dsimp only [D]; linarith [Q.g1_nonneg ab hab, Q.g2_nonneg ab hab]⟩
  have hD_int_S : IntegrableOn (fun ab : Type2 => D ab * rho ab.1 ab.2) stripPos volume :=
    integrableOn_deficit_stripPos Q
  have hg2_le_g1 : ∀ ab ∈ unitSquare, ab.2 < ab.1 → Q.g2 ab ≤ Q.g1 ab := by
    intro ab hab hba
    have hbic := Q.bic (ab.2, ab.1) ⟨hab.2, hab.1⟩ ab hab
    rw [hQ_sym_u ab.1 ab.2] at hbic
    nlinarith
  have hc1 : c ≤ 1 := hc.2.le.trans t0_lt_one.le
  let Tc : Set Type2 := {ab : Type2 | ab ∈ openUnitSquare ∧ ab.2 < ab.1 ∧ ab.1 + ab.2 < c}
  have hTc_sub : Tc ⊆ stripPos := by
    intro ab hab
    simp only [Tc, stripPos, openUnitSquare, mem_inter_iff, mem_ofPred_eq, mem_prod, mem_Ioo] at hab ⊢
    exact ⟨hab.1, by linarith [hab.2.1], by linarith [hab.1.2.1, hab.2.2, hc.2]⟩
  have hray_pt : ∀ η ∈ Ioo (0 : ℝ) 1,
      2 / (1 + η) * w (c, 0) ≤ ∫ lam in Ioo (0 : ℝ) (c / (1 + η)), D (lam, lam * η) := by
    intro η hη
    let lam1 : ℝ := c / (1 + η)
    have h1η : 0 < 1 + η := by linarith [hη.1]
    have hlam1_pos : 0 < lam1 := div_pos hc.1 h1η
    have hlam1_le1 : lam1 ≤ 1 := (div_le_one h1η).mpr (by linarith [hc1, hη.1])
    have hconc : w (c, 0) ≤ w (lam1, lam1 * η) := by
      have hp_mem : (lam1, lam1 * η) ∈ unitSquare :=
        ⟨⟨hlam1_pos.le, hlam1_le1⟩, ⟨mul_nonneg hlam1_pos.le hη.1.le,
          (mul_le_of_le_one_right hlam1_pos.le hη.2.le).trans hlam1_le1⟩⟩
      have hc0_mem : (c, (0 : ℝ)) ∈ unitSquare := ⟨⟨hc.1.le, hc1⟩, ⟨le_rfl, zero_le_one⟩⟩
      have h0c_mem : ((0 : ℝ), c) ∈ unitSquare := ⟨⟨le_rfl, zero_le_one⟩, ⟨hc.1.le, hc1⟩⟩
      have hb1 := Q.bic (c, 0) hc0_mem (lam1, lam1 * η) hp_mem
      have hb2 := Q.bic (0, c) h0c_mem (lam1, lam1 * η) hp_mem
      rw [hQ_sym_u c 0] at hb2
      have hlam_eq : lam1 * (1 + η) = c := div_mul_cancel₀ c h1η.ne'
      have hadd := add_le_add hb1 (mul_le_mul_of_nonneg_left hb2 hη.1.le)
      have hcoeff1 : (c - lam1) + η * (0 - lam1) = 0 := by linarith
      have hcoeff2 : (0 - lam1 * η) + η * (c - lam1 * η) = 0 := by
        have : η * c = (1 + η) * (lam1 * η) := by nlinarith [hlam_eq]
        linarith
      have hcomb : (1 + η) * Q.u (lam1, lam1 * η) ≤ (1 + η) * Q.u (c, 0) := by
        dsimp only at hadd
        have hrew : Q.u (lam1, lam1 * η) + (c - lam1) * Q.g1 (lam1, lam1 * η) + (0 - lam1 * η) * Q.g2 (lam1, lam1 * η) +
            η * (Q.u (lam1, lam1 * η) + (0 - lam1) * Q.g1 (lam1, lam1 * η) + (c - lam1 * η) * Q.g2 (lam1, lam1 * η)) =
            (1 + η) * Q.u (lam1, lam1 * η) + ((c - lam1) + η * (0 - lam1)) * Q.g1 (lam1, lam1 * η) +
            ((0 - lam1 * η) + η * (c - lam1 * η)) * Q.g2 (lam1, lam1 * η) := by ring
        rw [hrew, hcoeff1, hcoeff2] at hadd
        linarith
      have hQle : Q.u (lam1, lam1 * η) ≤ Q.u (c, 0) := by nlinarith
      dsimp only [w]
      have hsum : lam1 + lam1 * η = c := by linarith
      linarith
    have hftc := subgrad_integral_eq hlam1_pos.le (Q.raySubgrad hη.1.le hη.2.le hlam1_le1)
    rw [intervalIntegral.integral_of_le hlam1_pos.le, ← setIntegral_congr_set Ioo_ae_eq_Ioc] at hftc
    have h0_zero : ((0 : ℝ), (0 : ℝ) * η) = (0, 0) := by simp
    rw [h0_zero, hQ_u0, sub_zero] at hftc
    have hg_int : IntegrableOn (fun lam => Q.g1 (lam, lam * η) + η * Q.g2 (lam, lam * η))
        (Ioo (0 : ℝ) lam1) volume :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le hlam1_pos.le).mp
        ((Q.raySubgrad hη.1.le hη.2.le hlam1_le1).intervalIntegrable hlam1_pos.le)
    have hD_int_ray : IntegrableOn (fun lam => D (lam, lam * η)) (Ioo (0 : ℝ) lam1) volume := by
      refine (integrableOn_const (C := (1 : ℝ)) (hs := by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)).mono'
        (hD_meas.comp (measurable_id.prodMk (measurable_id.mul measurable_const))).aestronglyMeasurable ?_
      rw [ae_restrict_iff' measurableSet_Ioo]; filter_upwards with lam hlam
      have hsq : (lam, lam * η) ∈ unitSquare :=
        ⟨⟨hlam.1.le, hlam.2.le.trans hlam1_le1⟩, ⟨mul_nonneg hlam.1.le hη.1.le,
          (mul_le_of_le_one_right hlam.1.le hη.2.le).trans (hlam.2.le.trans hlam1_le1)⟩⟩
      rw [Real.norm_eq_abs, abs_of_nonneg (hD_bounds _ hsq).1]
      exact (hD_bounds _ hsq).2
    have hw_eq : w (lam1, lam1 * η) =
        ∫ lam in Ioo (0 : ℝ) lam1, ((1 + η) / 2 - (Q.g1 (lam, lam * η) + η * Q.g2 (lam, lam * η))) := by
      have hconst : ∫ _ in Ioo (0 : ℝ) lam1, ((1 + η) / 2 : ℝ) = lam1 * ((1 + η) / 2) := by
        rw [setIntegral_const, Real.volume_real_Ioo_of_le hlam1_pos.le, sub_zero, smul_eq_mul]
      rw [integral_sub (integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)) hg_int,
          hconst, hftc]
      dsimp only [w]; ring
    have hle_ray : w (lam1, lam1 * η) ≤
        (1 + η) / 2 * ∫ lam in Ioo (0 : ℝ) lam1, D (lam, lam * η) := by
      rw [hw_eq, ← integral_const_mul]
      refine setIntegral_mono_on
        ((integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)).sub hg_int)
        (hD_int_ray.const_mul _) measurableSet_Ioo (fun lam hlam => ?_)
      have hsq : (lam, lam * η) ∈ unitSquare :=
        ⟨⟨hlam.1.le, hlam.2.le.trans hlam1_le1⟩, ⟨mul_nonneg hlam.1.le hη.1.le,
          (mul_le_of_le_one_right hlam.1.le hη.2.le).trans (hlam.2.le.trans hlam1_le1)⟩⟩
      have hg := hg2_le_g1 (lam, lam * η) hsq (by nlinarith [hlam.1, hη.2])
      dsimp only [D]
      nlinarith [mul_nonneg (by linarith [hη.2] : (0 : ℝ) ≤ 1 - η) (sub_nonneg.mpr hg)]
    have hfin := hconc.trans hle_ray
    have hgoal : 2 / (1 + η) * w (c, 0) ≤ ∫ lam in Ioo (0 : ℝ) lam1, D (lam, lam * η) := by
      rw [div_mul_eq_mul_div, div_le_iff₀ h1η]
      linarith
    exact hgoal
  have hη_int_rhs : IntegrableOn (fun η : ℝ => (1 / (4 * Real.sqrt η)) *
      ∫ lam in Ioo (0 : ℝ) (c / (1 + η)), D (lam, lam * η)) (Ioo (0 : ℝ) 1) volume := by
    have hdom : IntegrableOn (fun η : ℝ => (1 / 2 : ℝ) * density1D η) (Ioo (0 : ℝ) 1) volume :=
      integrableOn_density1D_Ioo.const_mul (1 / 2 : ℝ)
    have hmeas : AEStronglyMeasurable (fun η : ℝ => (1 / (4 * Real.sqrt η)) *
        ∫ lam in Ioo (0 : ℝ) (c / (1 + η)), D (lam, lam * η)) (volume.restrict (Ioo (0 : ℝ) 1)) := by
      have hm1 : Measurable (fun η : ℝ => 1 / (4 * Real.sqrt η)) := by fun_prop
      let Rset : Set (ℝ × ℝ) := {p : ℝ × ℝ | (0 : ℝ) < p.2} ∩ {p : ℝ × ℝ | p.2 < c / (1 + p.1)}
      have hR_meas : MeasurableSet Rset :=
        (measurableSet_lt measurable_const measurable_snd).inter
          (measurableSet_lt measurable_snd (measurable_const.div (measurable_const.add measurable_fst)))
      have hm_ind : StronglyMeasurable (fun p : ℝ × ℝ => Rset.indicator (fun q : ℝ × ℝ => D (q.2, q.2 * q.1)) p) :=
        ((hD_meas.comp (measurable_snd.prodMk (measurable_snd.mul measurable_fst))).indicator hR_meas).stronglyMeasurable
      have hm2 : StronglyMeasurable (fun η : ℝ => ∫ lam,
          Rset.indicator (fun q : ℝ × ℝ => D (q.2, q.2 * q.1)) (η, lam)) :=
        hm_ind.integral_prod_right
      have heq : (fun η : ℝ => ∫ lam in Ioo (0 : ℝ) (c / (1 + η)), D (lam, lam * η)) =
          fun η => ∫ lam, Rset.indicator (fun q : ℝ × ℝ => D (q.2, q.2 * q.1)) (η, lam) := by
        ext η; rw [← integral_indicator measurableSet_Ioo]
        refine integral_congr_ae (ae_of_all _ fun lam => ?_)
        dsimp only
        by_cases h : lam ∈ Ioo (0 : ℝ) (c / (1 + η))
        · have hR : (η, lam) ∈ Rset := ⟨h.1, h.2⟩
          rw [indicator_of_mem h, indicator_of_mem hR]
        · have hR : (η, lam) ∉ Rset := fun hr => h ⟨hr.1, hr.2⟩
          rw [indicator_of_notMem h, indicator_of_notMem hR]
      exact (hm1.aestronglyMeasurable).mul (by rw [heq]; exact hm2.aestronglyMeasurable)
    refine hdom.mono' hmeas ?_
    rw [ae_restrict_iff' measurableSet_Ioo]; filter_upwards with η hη
    have h1η : 0 < 1 + η := by linarith [hη.1]
    have hlam1_pos : 0 < c / (1 + η) := div_pos hc.1 h1η
    have hlam1_le1 : c / (1 + η) ≤ 1 := (div_le_one h1η).mpr (by linarith [hc1, hη.1])
    have hi_nn : 0 ≤ ∫ lam in Ioo (0 : ℝ) (c / (1 + η)), D (lam, lam * η) := by
      refine setIntegral_nonneg measurableSet_Ioo (fun lam hlam => ?_)
      have hsq : (lam, lam * η) ∈ unitSquare :=
        ⟨⟨hlam.1.le, hlam.2.le.trans hlam1_le1⟩, ⟨mul_nonneg hlam.1.le hη.1.le,
          (mul_le_of_le_one_right hlam.1.le hη.2.le).trans (hlam.2.le.trans hlam1_le1)⟩⟩
      exact (hD_bounds _ hsq).1
    have hi_le1 : ∫ lam in Ioo (0 : ℝ) (c / (1 + η)), D (lam, lam * η) ≤ 1 := by
      have hD_int_ray : IntegrableOn (fun lam => D (lam, lam * η)) (Ioo (0 : ℝ) (c / (1 + η))) volume := by
        refine (integrableOn_const (C := (1 : ℝ)) (hs := by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)).mono'
          (hD_meas.comp (measurable_id.prodMk (measurable_id.mul measurable_const))).aestronglyMeasurable ?_
        rw [ae_restrict_iff' measurableSet_Ioo]; filter_upwards with lam hlam
        have hsq : (lam, lam * η) ∈ unitSquare :=
          ⟨⟨hlam.1.le, hlam.2.le.trans hlam1_le1⟩, ⟨mul_nonneg hlam.1.le hη.1.le,
            (mul_le_of_le_one_right hlam.1.le hη.2.le).trans (hlam.2.le.trans hlam1_le1)⟩⟩
        rw [Real.norm_eq_abs, abs_of_nonneg (hD_bounds _ hsq).1]; exact (hD_bounds _ hsq).2
      calc ∫ lam in Ioo (0 : ℝ) (c / (1 + η)), D (lam, lam * η)
          ≤ ∫ _ in Ioo (0 : ℝ) (c / (1 + η)), (1 : ℝ) :=
            setIntegral_mono_on hD_int_ray
              (integrableOn_const (C := (1 : ℝ)) (hs := by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top))
              measurableSet_Ioo (fun lam hlam => (hD_bounds _
                ⟨⟨hlam.1.le, hlam.2.le.trans hlam1_le1⟩, ⟨mul_nonneg hlam.1.le hη.1.le,
                  (mul_le_of_le_one_right hlam.1.le hη.2.le).trans (hlam.2.le.trans hlam1_le1)⟩⟩).2)
        _ = c / (1 + η) := by rw [setIntegral_const, Real.volume_real_Ioo_of_le hlam1_pos.le, sub_zero, smul_eq_mul, mul_one]
        _ ≤ 1 := hlam1_le1
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) hi_nn)]
    calc 1 / (4 * Real.sqrt η) * ∫ lam in Ioo (0 : ℝ) (c / (1 + η)), D (lam, lam * η)
        ≤ 1 / (4 * Real.sqrt η) * 1 := mul_le_mul_of_nonneg_left hi_le1 (by positivity)
      _ = 1 / 2 * density1D η := by unfold density1D; ring
  have hTc_meas : MeasurableSet Tc :=
    measurableSet_openUnitSquare.inter ((measurableSet_lt measurable_snd measurable_fst).inter
      (measurableSet_lt (measurable_fst.add measurable_snd) measurable_const))
  have hGTc : ∀ ab ∈ Tc, 0 ≤ G ab ∧ G ab ≤ C := by
    intro ab hab
    have ha : 0 < ab.1 := hab.1.1.1
    have hη : ab.2 / ab.1 ∈ Ioo (0 : ℝ) 1 := ⟨div_pos hab.1.2.1 ha, (div_lt_one ha).mpr hab.2.1⟩
    have hG' := hG ab.1 ha _ hη
    have e : ab.1 * (ab.2 / ab.1) = ab.2 := by field_simp
    rw [e] at hG'
    have hG'' : G ab = gw (ab.2 / ab.1) := hG'
    rw [hG'']
    exact ⟨hg0 _ hη, hgC _ hη⟩
  have hDG_meas : Measurable (fun ab : Type2 => D ab * G ab) := hD_meas.mul hG_meas
  have hDG_int : IntegrableOn (fun ab : Type2 => D ab * G ab * rho ab.1 ab.2) Tc volume := by
    refine ((hD_int_S.mono_set hTc_sub).const_mul C).mono'
      (hDG_meas.mul (by unfold rho; fun_prop)).aestronglyMeasurable ?_
    rw [ae_restrict_iff' hTc_meas]; filter_upwards with ab hab
    have hsq : ab ∈ unitSquare := ⟨Ioo_subset_Icc_self hab.1.1, Ioo_subset_Icc_self hab.1.2⟩
    have hD0 := (hD_bounds ab hsq).1
    have hGb := hGTc ab hab
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg hD0 hGb.1) (rho_nonneg _ _))]
    calc D ab * G ab * rho ab.1 ab.2 = D ab * rho ab.1 ab.2 * G ab := by ring
      _ ≤ D ab * rho ab.1 ab.2 * C :=
          mul_le_mul_of_nonneg_left hGb.2 (mul_nonneg hD0 (rho_nonneg _ _))
      _ = C * (D ab * rho ab.1 ab.2) := by ring
  have hray := setIntegral_ray_triangle hc.1 hc1 hDG_meas hDG_int
  have hinner : ∀ η ∈ Ioo (0 : ℝ) 1,
      (1 / (4 * Real.sqrt η)) * ∫ lam in Ioo (0 : ℝ) (c / (1 + η)), (D (lam, lam * η) * G (lam, lam * η)) =
      gw η * ((1 / (4 * Real.sqrt η)) * ∫ lam in Ioo (0 : ℝ) (c / (1 + η)), D (lam, lam * η)) := by
    intro η hη
    have h1 : ∫ lam in Ioo (0 : ℝ) (c / (1 + η)), (D (lam, lam * η) * G (lam, lam * η)) =
        (∫ lam in Ioo (0 : ℝ) (c / (1 + η)), D (lam, lam * η)) * gw η := by
      rw [← integral_mul_const]
      refine setIntegral_congr_fun measurableSet_Ioo (fun lam hlam => ?_)
      show D (lam, lam * η) * G (lam, lam * η) = D (lam, lam * η) * gw η
      rw [hG lam hlam.1 η hη]
    rw [h1]; ring
  have hray' : ∫ ab in Tc, D ab * G ab * rho ab.1 ab.2 =
      ∫ η in Ioo (0 : ℝ) 1,
        gw η * ((1 / (4 * Real.sqrt η)) * ∫ lam in Ioo (0 : ℝ) (c / (1 + η)), D (lam, lam * η)) :=
    hray.trans (setIntegral_congr_fun measurableSet_Ioo hinner)
  have hgaw_int : IntegrableOn (fun η => gw η * arctanWeight η) (Ioo (0 : ℝ) 1) volume := by
    refine (integrableOn_arctanWeight.const_mul C).mono'
      (hgw_meas.mul (by unfold arctanWeight; fun_prop)).aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Ioo]; filter_upwards with η hη
    have haw := arctanWeight_nonneg hη.1
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hg0 η hη) haw)]
    exact mul_le_mul_of_nonneg_right (hgC η hη) haw
  have hlhs_int : IntegrableOn
      (fun η : ℝ => gw η * ((1 / (4 * Real.sqrt η)) * (2 / (1 + η) * w (c, 0))))
      (Ioo (0 : ℝ) 1) volume := by
    refine IntegrableOn.congr_fun (f := fun η => w (c, 0) * (gw η * arctanWeight η))
      (hgaw_int.const_mul _) (fun η hη => ?_) measurableSet_Ioo
    show w (c, 0) * (gw η * arctanWeight η) = _
    rw [← arctanWeight_eq hη.1]; ring
  have hrhs_int : IntegrableOn (fun η : ℝ => gw η * ((1 / (4 * Real.sqrt η)) *
      ∫ lam in Ioo (0 : ℝ) (c / (1 + η)), D (lam, lam * η))) (Ioo (0 : ℝ) 1) volume := by
    refine (hη_int_rhs.abs.const_mul C).mono'
      (hgw_meas.aestronglyMeasurable.mul hη_int_rhs.aestronglyMeasurable) ?_
    rw [ae_restrict_iff' measurableSet_Ioo]; filter_upwards with η hη
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hg0 η hη)]
    exact mul_le_mul_of_nonneg_right (hgC η hη) (abs_nonneg _)
  have hmono := setIntegral_mono_on hlhs_int hrhs_int measurableSet_Ioo (fun η hη =>
    mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (hray_pt η hη) (by positivity)) (hg0 η hη))
  have hval : ∫ η in Ioo (0 : ℝ) 1, gw η * ((1 / (4 * Real.sqrt η)) * (2 / (1 + η) * w (c, 0))) =
      (∫ η in Ioo (0 : ℝ) 1, gw η * arctanWeight η) * w (c, 0) := by
    rw [← integral_mul_const]
    refine setIntegral_congr_fun measurableSet_Ioo (fun η hη => ?_)
    show gw η * ((1 / (4 * Real.sqrt η)) * (2 / (1 + η) * w (c, 0))) =
      gw η * arctanWeight η * w (c, 0)
    rw [← arctanWeight_eq hη.1]; ring
  rw [hval, ← hray'] at hmono
  refine hmono.trans (le_of_eq ?_)
  exact setIntegral_congr_fun hTc_meas (fun ab _ => by ring)

/-! ### 7. The two angular weights -/

/-- `gw₁(η) = 4√η / (1 + η)`: the value of `G₁` along the ray of slope `η`. -/
def gw1 (η : ℝ) : ℝ := 4 * Real.sqrt η / (1 + η)

lemma measurable_gw1 : Measurable gw1 := by unfold gw1; fun_prop
lemma measurable_G1 : Measurable G1 := by unfold G1; fun_prop

lemma G1_ray {lam : ℝ} (hlam : 0 < lam) {η : ℝ} (hη : η ∈ Ioo (0 : ℝ) 1) :
    G1 (lam, lam * η) = gw1 η := by
  unfold G1 gw1
  have h1 : lam * (lam * η) = lam ^ 2 * η := by ring
  have hden : lam + lam * η ≠ 0 := ne_of_gt (by nlinarith [mul_pos hlam hη.1])
  have h1η : (1 + η) ≠ 0 := by linarith [hη.1]
  show 4 * Real.sqrt (lam * (lam * η)) / (lam + lam * η) = 4 * Real.sqrt η / (1 + η)
  rw [h1, Real.sqrt_mul (sq_nonneg lam), Real.sqrt_sq hlam.le, div_eq_div_iff hden h1η]
  ring

lemma gw1_bounds {η : ℝ} (hη : η ∈ Ioo (0 : ℝ) 1) : 0 ≤ gw1 η ∧ gw1 η ≤ 2 := by
  unfold gw1
  have h1η : 0 < 1 + η := by linarith [hη.1]
  have hs := Real.sqrt_nonneg η
  have hsq : Real.sqrt η ^ 2 = η := Real.sq_sqrt hη.1.le
  refine ⟨div_nonneg (by linarith) h1η.le, ?_⟩
  rw [div_le_iff₀ h1η]
  nlinarith [sq_nonneg (Real.sqrt η - 1)]

lemma G1_bounds {ab : Type2} (ha : 0 < ab.1) (hb : 0 < ab.2) : 0 ≤ G1 ab ∧ G1 ab ≤ 2 := by
  unfold G1
  have hsum : 0 < ab.1 + ab.2 := by linarith
  have hs := Real.sqrt_nonneg (ab.1 * ab.2)
  refine ⟨div_nonneg (by linarith) hsum.le, ?_⟩
  rw [div_le_iff₀ hsum]
  have hle : Real.sqrt (ab.1 * ab.2) ≤ (ab.1 + ab.2) / 2 := by
    rw [Real.sqrt_le_iff]
    exact ⟨by linarith, by nlinarith [sq_nonneg (ab.1 - ab.2)]⟩
  linarith

lemma gw1_mul_arctanWeight {η : ℝ} (hη : 0 < η) : gw1 η * arctanWeight η = 2 / (1 + η) ^ 2 := by
  unfold gw1 arctanWeight
  have hs : Real.sqrt η ≠ 0 := (Real.sqrt_pos.mpr hη).ne'
  have h1 : (1 + η) ≠ 0 := by linarith
  rw [div_mul_div_comm, div_eq_div_iff (mul_ne_zero h1 (mul_ne_zero (mul_ne_zero two_ne_zero hs) h1))
    (pow_ne_zero 2 h1)]
  ring

lemma integrableOn_gw1_arctanWeight :
    IntegrableOn (fun η => gw1 η * arctanWeight η) (Ioo (0 : ℝ) 1) volume := by
  refine (integrableOn_arctanWeight.const_mul 2).mono'
    (measurable_gw1.mul (by unfold arctanWeight; fun_prop)).aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ioo]; filter_upwards with η hη
  have haw := arctanWeight_nonneg hη.1
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (gw1_bounds hη).1 haw)]
  exact mul_le_mul_of_nonneg_right (gw1_bounds hη).2 haw

lemma integral_gw1_arctanWeight : ∫ η in Ioo (0 : ℝ) 1, gw1 η * arctanWeight η = 1 := by
  have hderiv' : ∀ x : ℝ, 0 ≤ x → HasDerivAt (fun y : ℝ => 2 * y / (1 + y)) (2 / (1 + x) ^ 2) x := by
    intro x hx
    have h1 : (1 + x) ≠ 0 := by linarith
    have hn : HasDerivAt (fun y : ℝ => 2 * y) 2 x := by
      simpa using (hasDerivAt_id x).const_mul (2 : ℝ)
    have hd : HasDerivAt (fun y : ℝ => 1 + y) 1 x := by
      simpa using (hasDerivAt_id x).const_add (1 : ℝ)
    have hq := hn.div hd h1
    have he : (2 * (1 + x) - 2 * x * 1) / (1 + x) ^ 2 = 2 / (1 + x) ^ 2 := by
      congr 1; ring
    exact hq.congr_deriv he
  have hderiv : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt (fun y : ℝ => 2 * y / (1 + y)) (2 / (1 + x) ^ 2) x :=
    fun x hx => hderiv' x hx.1.le
  have hcont : ContinuousOn (fun y : ℝ => 2 * y / (1 + y)) (Icc (0 : ℝ) 1) :=
    fun y hy => (hderiv' y hy.1).continuousAt.continuousWithinAt
  have hint : IntervalIntegrable (fun η : ℝ => 2 / (1 + η) ^ 2) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one]
    exact integrableOn_gw1_arctanWeight.congr_fun (fun η hη => gw1_mul_arctanWeight hη.1)
      measurableSet_Ioo
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hcont hderiv hint
  rw [intervalIntegral.integral_of_le zero_le_one, ← setIntegral_congr_set Ioo_ae_eq_Ioc] at h
  rw [setIntegral_congr_fun measurableSet_Ioo (fun η hη => gw1_mul_arctanWeight hη.1), h]
  norm_num

lemma eight_inv_pi_ge : (2 : ℝ) ≤ 8 * (1 / Real.pi) := by
  have h := one_div_le_one_div_of_le Real.pi_pos (by linarith [Real.pi_lt_d4] : Real.pi ≤ 22 / 7)
  linarith

lemma integral_gw2_arctanWeight :
    ∫ η in Ioo (0 : ℝ) 1, (8 * (1 / Real.pi) - gw1 η) * arctanWeight η = 1 := by
  have hsplit : ∀ η ∈ Ioo (0 : ℝ) 1, (8 * (1 / Real.pi) - gw1 η) * arctanWeight η =
      8 * (1 / Real.pi) * arctanWeight η - gw1 η * arctanWeight η := fun η _ => by ring
  rw [setIntegral_congr_fun measurableSet_Ioo hsplit,
    integral_sub (integrableOn_arctanWeight.const_mul _) integrableOn_gw1_arctanWeight,
    integral_const_mul, integral_arctanWeight, integral_gw1_arctanWeight]
  field_simp
  ring

lemma WA2_bounds {ab : Type2} (ha : 0 < ab.1) (hb : 0 < ab.2) :
    0 ≤ WA2 ab ∧ WA2 ab ≤ 1 / 2 + 2 * (1 / Real.pi) := by
  unfold WA2
  have hG := G1_bounds ha hb
  have h8 := eight_inv_pi_ge
  have hJ0 := Jtail_nonneg (ab.1 + ab.2)
  have hJ1 := Jtail_le_half (ab.1 + ab.2)
  have hJ1' : Jtail (ab.1 + ab.2) ^ 2 ≤ 1 / 4 := by nlinarith
  have hJ2' : Jtail (ab.1 + ab.2) * (1 - Jtail (ab.1 + ab.2)) ≤ 1 / 4 := by
    nlinarith [sq_nonneg (Jtail (ab.1 + ab.2) - 1 / 2)]
  constructor
  · exact add_nonneg (mul_nonneg (sq_nonneg _) hG.1)
      (mul_nonneg (mul_nonneg hJ0 (by linarith)) (by linarith))
  · nlinarith [mul_le_mul hJ1' hG.2 hG.1 (by norm_num : (0 : ℝ) ≤ 1 / 4),
      mul_le_mul_of_nonneg_right hJ2' (by linarith : (0 : ℝ) ≤ 8 * (1 / Real.pi) - G1 ab),
      mul_nonneg (mul_nonneg hJ0 (by linarith)) hG.1]

lemma measurable_WA2 : Measurable WA2 := by
  unfold WA2
  have hJ : Measurable (fun ab : Type2 => Jtail (ab.1 + ab.2)) :=
    antitone_Jtail.measurable.comp (measurable_fst.add measurable_snd)
  exact ((hJ.pow_const 2).mul measurable_G1).add
    ((hJ.mul (measurable_const.sub hJ)).mul (measurable_const.sub measurable_G1))

/-! ### 8. Term A as an integral against `D ρ W_A` -/

lemma lemma5_termA_sharp (Q : InterimProfile)
    (hQ_sym_u : ∀ a b, Q.u (b, a) = Q.u (a, b))
    (hQ_u0 : Q.u (0, 0) = 0) :
    let w : Type2 → ℝ := fun ab => (ab.1 + ab.2) / 2 - Q.u ab
    let D : Type2 → ℝ := fun ab => 1 - (Q.g1 ab + Q.g2 ab)
    ∫ t in Ioo (0 : ℝ) t0, K t * w (t, 0) ≤
      ∫ t in Ioo (0 : ℝ) t0, ∫ s in Ioo (0 : ℝ) (1 - t),
        D (s + t, s) * rho (s + t) s * WA2 (s + t, s) := by
  intro w D
  have hD_meas : Measurable D := measurable_const.sub (Q.g1_meas.add Q.g2_meas)
  have hD_bounds : ∀ ab ∈ unitSquare, 0 ≤ D ab ∧ D ab ≤ 1 := fun ab hab =>
    ⟨by dsimp only [D]; linarith [Q.g_sum_le ab hab],
     by dsimp only [D]; linarith [Q.g1_nonneg ab hab, Q.g2_nonneg ab hab]⟩
  have hD_int_S : IntegrableOn (fun ab : Type2 => D ab * rho ab.1 ab.2) stripPos volume :=
    integrableOn_deficit_stripPos Q
  have hKw0_int : IntegrableOn (fun t => K t * w (t, 0)) (Ioo (0 : ℝ) t0) volume := by
    have hdom := integrableOn_K_Ioo_t0.abs.const_mul 2
    have hc : ContinuousOn (fun t => w (t, 0)) (Ioo (0 : ℝ) t0) :=
      ((continuousOn_id.add continuousOn_const).div_const 2).sub
        (Q.u_continuousOn.comp (f := fun t : ℝ => (t, (0 : ℝ))) (continuous_id.prodMk continuous_const).continuousOn
          (fun t ht => ⟨⟨ht.1.le, ht.2.le.trans t0_lt_one.le⟩, ⟨le_rfl, zero_le_one⟩⟩))
    have hmK : Measurable K := by unfold K gT artanh; fun_prop
    refine hdom.mono' (hmK.aestronglyMeasurable.mul (hc.aestronglyMeasurable measurableSet_Ioo)) ?_
    rw [ae_restrict_iff' measurableSet_Ioo]; filter_upwards with t ht
    have hsq : (t, (0 : ℝ)) ∈ unitSquare := ⟨⟨ht.1.le, ht.2.le.trans t0_lt_one.le⟩, ⟨le_rfl, zero_le_one⟩⟩
    have hu_nn := Q.u_nonneg _ hsq; have hu_le : Q.u (t, 0) ≤ 1 := by linarith [Q.u_le_bound hsq, hQ_u0]
    have hw_abs : |w (t, 0)| ≤ 2 := by dsimp only [w]; rw [abs_le]; constructor <;> linarith [ht.1, ht.2, t0_lt_one]
    rw [Real.norm_eq_abs, abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right hw_abs (abs_nonneg _)
  let S' : Set Type2 := {ab : Type2 | ab ∈ openUnitSquare ∧ ab.2 < ab.1}
  have hS' : MeasurableSet S' :=
    measurableSet_openUnitSquare.inter (measurableSet_lt measurable_snd measurable_fst)
  let F : Type2 → ℝ := fun ab => D ab * rho ab.1 ab.2
  have hF_meas : Measurable F := hD_meas.mul (by unfold rho; fun_prop)
  have hF_nn : ∀ ab ∈ S', 0 ≤ F ab := fun ab hab =>
    mul_nonneg (hD_bounds ab ⟨Ioo_subset_Icc_self hab.1.1, Ioo_subset_Icc_self hab.1.2⟩).1 (rho_nonneg _ _)
  have hF_int : IntegrableOn F S' volume := by
    refine (integrableOn_rho_openUnitSquare.mono_set (fun ab (hab : ab ∈ S') => hab.1)).mono'
      hF_meas.aestronglyMeasurable ?_
    rw [ae_restrict_iff' hS']; filter_upwards with ab hab
    have hsq : ab ∈ unitSquare := ⟨Ioo_subset_Icc_self hab.1.1, Ioo_subset_Icc_self hab.1.2⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (hF_nn ab hab)]
    calc D ab * rho ab.1 ab.2 ≤ 1 * rho ab.1 ab.2 :=
          mul_le_mul_of_nonneg_right (hD_bounds ab hsq).2 (rho_nonneg _ _)
      _ = rho ab.1 ab.2 := one_mul _
  have h8 := eight_inv_pi_ge
  have hGS : ∀ ab ∈ S', 0 ≤ G1 ab ∧ G1 ab ≤ 2 := fun ab hab => G1_bounds hab.1.1.1 hab.1.2.1
  -- the two weighted integrands
  have hF1_int : IntegrableOn (fun ab => F ab * G1 ab) S' volume :=
    integrableOn_mul_bdd_on hS' hF_int measurable_G1 (fun ab hab => (hGS ab hab).1)
      (fun ab hab => (hGS ab hab).2)
  have hF2_int : IntegrableOn (fun ab => F ab * (8 * (1 / Real.pi) - G1 ab)) S' volume :=
    integrableOn_mul_bdd_on (C := 8 * (1 / Real.pi)) hS' hF_int (measurable_const.sub measurable_G1)
      (fun ab hab => by linarith [(hGS ab hab).2]) (fun ab hab => by linarith [(hGS ab hab).1])
  have hsum_meas : Measurable (fun ab : Type2 => ab.1 + ab.2) := measurable_fst.add measurable_snd
  have hmc : ∀ c : ℝ, MeasurableSet (S' ∩ {ab : Type2 | ab.1 + ab.2 < c}) := fun c =>
    hS'.inter (measurableSet_lt hsum_meas measurable_const)
  let J1 : ℝ → ℝ := fun c => ∫ ab in S' ∩ {ab : Type2 | ab.1 + ab.2 < c}, F ab * G1 ab
  let J2 : ℝ → ℝ := fun c =>
    ∫ ab in S' ∩ {ab : Type2 | ab.1 + ab.2 < c}, F ab * (8 * (1 / Real.pi) - G1 ab)
  have hF1_nn : ∀ ab ∈ S', 0 ≤ F ab * G1 ab := fun ab hab => mul_nonneg (hF_nn ab hab) (hGS ab hab).1
  have hF2_nn : ∀ ab ∈ S', 0 ≤ F ab * (8 * (1 / Real.pi) - G1 ab) := fun ab hab =>
    mul_nonneg (hF_nn ab hab) (by linarith [(hGS ab hab).2])
  have hJ1_mono : Monotone J1 := fun c1' c2' h12 =>
    setIntegral_mono_set (hF1_int.mono_set inter_subset_left)
      (ae_restrict_of_forall_mem (hmc c2') (fun ab hab => hF1_nn ab hab.1))
      (Filter.Eventually.of_forall (inter_subset_inter_right _ (fun ab hab => lt_of_lt_of_le hab h12)))
  have hJ2_mono : Monotone J2 := fun c1' c2' h12 =>
    setIntegral_mono_set (hF2_int.mono_set inter_subset_left)
      (ae_restrict_of_forall_mem (hmc c2') (fun ab hab => hF2_nn ab hab.1))
      (Filter.Eventually.of_forall (inter_subset_inter_right _ (fun ab hab => lt_of_lt_of_le hab h12)))
  have hJ1_nn : ∀ c, 0 ≤ J1 c := fun c => setIntegral_nonneg (hmc c) (fun ab hab => hF1_nn ab hab.1)
  have hJ2_nn : ∀ c, 0 ≤ J2 c := fun c => setIntegral_nonneg (hmc c) (fun ab hab => hF2_nn ab hab.1)
  have hJ1_le : ∀ c, J1 c ≤ ∫ ab in S', F ab * G1 ab := fun c =>
    setIntegral_mono_set hF1_int (ae_restrict_of_forall_mem hS' hF1_nn)
      (Filter.Eventually.of_forall inter_subset_left)
  have hJ2_le : ∀ c, J2 c ≤ ∫ ab in S', F ab * (8 * (1 / Real.pi) - G1 ab) := fun c =>
    setIntegral_mono_set hF2_int (ae_restrict_of_forall_mem hS' hF2_nn)
      (Filter.Eventually.of_forall inter_subset_left)
  have hset : ∀ c : ℝ, {ab : Type2 | ab ∈ openUnitSquare ∧ ab.2 < ab.1 ∧ ab.1 + ab.2 < c} =
      S' ∩ {ab : Type2 | ab.1 + ab.2 < c} := by
    intro c; ext ab; simp only [S', mem_inter_iff, mem_ofPred_eq]; tauto
  have hray1 : ∀ c ∈ Ioo (0 : ℝ) t0, w (c, 0) ≤ J1 c := by
    intro c hc
    have h := lemma5_ray_bound Q hQ_sym_u hQ_u0 hc measurable_G1 measurable_gw1
      (fun lam hlam η hη => G1_ray hlam hη) (fun η hη => (gw1_bounds hη).1)
      (fun η hη => (gw1_bounds hη).2)
    dsimp only at h
    rw [integral_gw1_arctanWeight, one_mul, hset c] at h
    exact h
  have hray2 : ∀ c ∈ Ioo (0 : ℝ) t0, w (c, 0) ≤ J2 c := by
    intro c hc
    have h := lemma5_ray_bound (C := 8 * (1 / Real.pi)) Q hQ_sym_u hQ_u0 hc
      (G := fun ab => 8 * (1 / Real.pi) - G1 ab) (gw := fun η => 8 * (1 / Real.pi) - gw1 η)
      (measurable_const.sub measurable_G1) (measurable_const.sub measurable_gw1)
      (fun lam hlam η hη => by show 8 * (1 / Real.pi) - G1 (lam, lam * η) = _; rw [G1_ray hlam hη])
      (fun η hη => by linarith [(gw1_bounds hη).2]) (fun η hη => by linarith [(gw1_bounds hη).1])
    dsimp only at h
    rw [integral_gw2_arctanWeight, one_mul, hset c] at h
    exact h
  have hmK : Measurable K := by unfold K gT artanh; fun_prop
  have hmJ : Measurable Jtail := antitone_Jtail.measurable
  let k1 : ℝ → ℝ := fun c => K c * (2 * Jtail c)
  let k2 : ℝ → ℝ := fun c => K c * (1 - 2 * Jtail c)
  have hk1_int : IntegrableOn k1 (Ioo (0 : ℝ) t0) volume := by
    refine integrableOn_K_Ioo_t0.abs.mono'
      (hmK.mul (measurable_const.mul hmJ)).aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Ioo]; filter_upwards with c _
    dsimp only [k1]
    rw [Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (by linarith [Jtail_nonneg c] : 0 ≤ 2 * Jtail c)]
    exact mul_le_of_le_one_right (abs_nonneg _) (by linarith [Jtail_le_half c])
  have hk2_int : IntegrableOn k2 (Ioo (0 : ℝ) t0) volume := by
    refine integrableOn_K_Ioo_t0.abs.mono'
      (hmK.mul (measurable_const.sub (measurable_const.mul hmJ))).aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Ioo]; filter_upwards with c _
    dsimp only [k2]
    rw [Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (by linarith [Jtail_le_half c] : 0 ≤ 1 - 2 * Jtail c)]
    exact mul_le_of_le_one_right (abs_nonneg _) (by linarith [Jtail_nonneg c])
  have hkJ_int : ∀ (k J : ℝ → ℝ) (Cb : ℝ), IntegrableOn k (Ioo (0 : ℝ) t0) volume →
      Monotone J → (∀ c, 0 ≤ J c) → (∀ c, J c ≤ Cb) →
      IntegrableOn (fun c => k c * J c) (Ioo (0 : ℝ) t0) volume := by
    intro k J Cb hk hJm hJ0 hJC
    refine (hk.abs.const_mul Cb).mono'
      (hk.aestronglyMeasurable.mul hJm.measurable.aestronglyMeasurable) ?_
    filter_upwards with c
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hJ0 c), mul_comm]
    exact mul_le_mul_of_nonneg_right (hJC c) (abs_nonneg _)
  have hk1J1 := hkJ_int k1 J1 _ hk1_int hJ1_mono hJ1_nn hJ1_le
  have hk2J2 := hkJ_int k2 J2 _ hk2_int hJ2_mono hJ2_nn hJ2_le
  have hstep1 : ∫ t in Ioo (0 : ℝ) t0, K t * w (t, 0) ≤
      (∫ c in Ioo (0 : ℝ) t0, k1 c * J1 c) + ∫ c in Ioo (0 : ℝ) t0, k2 c * J2 c := by
    rw [← integral_add hk1J1 hk2J2]
    refine setIntegral_mono_on hKw0_int (hk1J1.add hk2J2) measurableSet_Ioo (fun c hc => ?_)
    have hK0 : 0 ≤ K c := (K_pos hc.1 hc.2.le).le
    have hk1_nn : 0 ≤ k1 c := mul_nonneg hK0 (by linarith [Jtail_nonneg c])
    have hk2_nn : 0 ≤ k2 c := mul_nonneg hK0 (by linarith [Jtail_le_half c])
    have h1 := mul_le_mul_of_nonneg_left (hray1 c hc) hk1_nn
    have h2 := mul_le_mul_of_nonneg_left (hray2 c hc) hk2_nn
    have hsum_k : K c * w (c, 0) = k1 c * w (c, 0) + k2 c * w (c, 0) := by dsimp [k1, k2]; ring
    linarith
  have hswap1 : ∫ c in Ioo (0 : ℝ) t0, k1 c * J1 c =
      ∫ ab in S', F ab * G1 ab * Jtail (ab.1 + ab.2) ^ 2 := by
    rw [integral_swap_sublevel (ν := (volume : Measure Type2)) hS'
      (h := fun ab : Type2 => ab.1 + ab.2) hsum_meas hk1_int hF1_int]
    refine setIntegral_congr_fun hS' (fun ab hab => ?_)
    dsimp only [k1]; rw [integral_K_mul_two_Jtail (by linarith [hab.1.1.1, hab.1.2.1])]
  have hswap2 : ∫ c in Ioo (0 : ℝ) t0, k2 c * J2 c =
      ∫ ab in S', F ab * (8 * (1 / Real.pi) - G1 ab) *
        (Jtail (ab.1 + ab.2) * (1 - Jtail (ab.1 + ab.2))) := by
    rw [integral_swap_sublevel (ν := (volume : Measure Type2)) hS'
      (h := fun ab : Type2 => ab.1 + ab.2) hsum_meas hk2_int hF2_int]
    refine setIntegral_congr_fun hS' (fun ab hab => ?_)
    dsimp only [k2]; rw [integral_K_mul_one_sub_two_Jtail (by linarith [hab.1.1.1, hab.1.2.1])]
  have hJm_sum : Measurable (fun ab : Type2 => Jtail (ab.1 + ab.2)) := hmJ.comp hsum_meas
  have hI1 : IntegrableOn (fun ab : Type2 => F ab * G1 ab * Jtail (ab.1 + ab.2) ^ 2) S' volume :=
    integrableOn_mul_bdd_on (C := 1 / 4) hS' hF1_int (hJm_sum.pow_const 2)
      (fun _ _ => sq_nonneg _)
      (fun ab _ => by nlinarith [Jtail_nonneg (ab.1 + ab.2), Jtail_le_half (ab.1 + ab.2)])
  have hI2 : IntegrableOn
      (fun ab : Type2 => F ab * (8 * (1 / Real.pi) - G1 ab) *
        (Jtail (ab.1 + ab.2) * (1 - Jtail (ab.1 + ab.2)))) S' volume :=
    integrableOn_mul_bdd_on (C := 1 / 4) hS' hF2_int (hJm_sum.mul (measurable_const.sub hJm_sum))
      (fun ab _ => mul_nonneg (Jtail_nonneg _) (by linarith [Jtail_le_half (ab.1 + ab.2)]))
      (fun ab _ => by nlinarith [sq_nonneg (Jtail (ab.1 + ab.2) - 1 / 2)])
  have hcomb : (∫ ab in S', F ab * G1 ab * Jtail (ab.1 + ab.2) ^ 2) +
      (∫ ab in S', F ab * (8 * (1 / Real.pi) - G1 ab) *
        (Jtail (ab.1 + ab.2) * (1 - Jtail (ab.1 + ab.2)))) =
      ∫ ab in S', F ab * WA2 ab := by
    rw [← integral_add hI1 hI2]
    refine setIntegral_congr_fun hS' (fun ab _ => ?_)
    unfold WA2; ring
  have hsub : stripPos ⊆ S' := fun ab hab =>
    ⟨hab.1, by have h : (0 : ℝ) < ab.1 - ab.2 := hab.2.1; linarith⟩
  have hstep3 : ∫ ab in S', F ab * WA2 ab = ∫ ab in stripPos, F ab * WA2 ab := by
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hS' hsub (fun ab hab => ?_)
    have hnot : ¬ (ab.1 - ab.2 < t0) := fun hlt =>
      hab.2 ⟨hab.1.1, (by have h : ab.2 < ab.1 := hab.1.2; linarith : (0 : ℝ) < ab.1 - ab.2), hlt⟩
    have hge : t0 ≤ ab.1 + ab.2 := by
      by_contra hlt
      exact hnot (by linarith [hab.1.1.2.1, not_le.mp hlt])
    unfold WA2; rw [Jtail_of_ge_t0 hge]; ring
  have hFW_int : IntegrableOn (fun ab : Type2 => F ab * WA2 ab) stripPos volume :=
    integrableOn_mul_bdd_on measurableSet_stripPos (hF_int.mono_set hsub) measurable_WA2
      (fun ab hab => (WA2_bounds hab.1.1.1 hab.1.2.1).1) (fun ab hab => (WA2_bounds hab.1.1.1 hab.1.2.1).2)
  have hstep4 : ∫ ab in stripPos, F ab * WA2 ab =
      ∫ t in Ioo (0 : ℝ) t0, ∫ s in Ioo (0 : ℝ) (1 - t),
        D (s + t, s) * rho (s + t) s * WA2 (s + t, s) := by
    rw [stripPos_eq_setOf]
    exact setIntegral_shear_upper le_rfl t0_pos.le t0_lt_one.le (by rwa [← stripPos_eq_setOf])
  rw [← hstep4, ← hstep3, ← hcomb, ← hswap1, ← hswap2]
  exact hstep1
/-! ### 9. Term B: exact diagonal identity -/

lemma Iwing_bounds {t x : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (hx : x ∈ Icc (0 : ℝ) (1 - t)) :
    0 ≤ Iwing x t ∧ Iwing x t ≤ gT t := by
  have hnn : ∀ r ∈ Ioo (0 : ℝ) (1 - t), 0 ≤ rho (r + t) r := fun r _ => rho_nonneg _ _
  rw [← integral_rho_eq_Iwing hx.1 ht0, ← integral_rho_eq_gT ht0 ht1]
  refine ⟨setIntegral_nonneg measurableSet_Ioo (fun r _ => rho_nonneg _ _), ?_⟩
  exact setIntegral_mono_set (integrableOn_rho_diag (by linarith) ht0)
    (ae_restrict_of_forall_mem measurableSet_Ioo hnn)
    (Filter.Eventually.of_forall (Ioo_subset_Ioo_right hx.2))

lemma integrableOn_deficit_psiB (Q : InterimProfile) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) t0) :
    IntegrableOn (fun r => (1 - (Q.g1 (r + t, r) + Q.g2 (r + t, r))) * psiB t r)
      (Ioo (0 : ℝ) (1 - t)) volume := by
  have ht1 : t < 1 := ht.2.trans t0_lt_one
  have hmeas : Measurable (fun r : ℝ => (1 - (Q.g1 (r + t, r) + Q.g2 (r + t, r))) * psiB t r) := by
    have hm : Measurable (fun r : ℝ => ((r + t, r) : Type2)) :=
      (measurable_id.add measurable_const).prodMk measurable_id
    have hpsi : Measurable (fun r : ℝ => psiB t r) := by unfold psiB Iwing; fun_prop
    exact (measurable_const.sub ((Q.g1_meas.comp hm).add (Q.g2_meas.comp hm))).mul hpsi
  refine (integrableOn_const (C := 2 * gT t + rho 1 (1 - t))
    (hs := by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)).mono' hmeas.aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ioo]; filter_upwards with r hr
  have hsq : (r + t, r) ∈ unitSquare :=
    ⟨⟨by linarith [hr.1, ht.1], by linarith [hr.2]⟩, ⟨hr.1.le, by linarith [hr.2, ht.1]⟩⟩
  have hD0 : 0 ≤ 1 - (Q.g1 (r + t, r) + Q.g2 (r + t, r)) := by linarith [Q.g_sum_le _ hsq]
  have hD1 : 1 - (Q.g1 (r + t, r) + Q.g2 (r + t, r)) ≤ 1 := by
    linarith [Q.g1_nonneg _ hsq, Q.g2_nonneg _ hsq]
  have hI := Iwing_bounds ht.1 ht1 ⟨hr.1.le, hr.2.le⟩
  have hrho := rho_nonneg 1 (1 - t)
  have hpsi : |psiB t r| ≤ 2 * gT t + rho 1 (1 - t) := by
    unfold psiB; rw [abs_le]; constructor <;> linarith [hI.1, hI.2]
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hD0]
  calc (1 - (Q.g1 (r + t, r) + Q.g2 (r + t, r))) * |psiB t r|
      ≤ 1 * (2 * gT t + rho 1 (1 - t)) :=
        mul_le_mul hD1 hpsi (abs_nonneg _) zero_le_one
    _ = 2 * gT t + rho 1 (1 - t) := one_mul _

lemma lemma5_diag_identity (Q : InterimProfile) (hQ_u0 : Q.u (0, 0) = 0)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) t0) :
    let w : Type2 → ℝ := fun ab => (ab.1 + ab.2) / 2 - Q.u ab
    let D : Type2 → ℝ := fun ab => 1 - (Q.g1 ab + Q.g2 ab)
    2 * (∫ s in Ioo (0 : ℝ) (1 - t), w (s + t, s) * rho (s + t) s) - w (1, 1 - t) * rho 1 (1 - t) =
      K t * w (t, 0) + ∫ r in Ioo (0 : ℝ) (1 - t), D (r + t, r) * psiB t r := by
  intro w D
  have hD_meas : Measurable D := measurable_const.sub (Q.g1_meas.add Q.g2_meas)
  have hD_bounds : ∀ ab ∈ unitSquare, 0 ≤ D ab ∧ D ab ≤ 1 := fun ab hab =>
    ⟨by dsimp only [D]; linarith [Q.g_sum_le ab hab],
     by dsimp only [D]; linarith [Q.g1_nonneg ab hab, Q.g2_nonneg ab hab]⟩
  have ht1 : t < 1 := ht.2.trans t0_lt_one
  have hb : 0 < 1 - t := by linarith
  have hfwd : ∀ s ∈ Icc (0 : ℝ) (1 - t),
      w (s + t, s) - w (t, 0) = ∫ r in Ioo (0 : ℝ) s, D (r + t, r) := by
    intro s hs
    have hftc := subgrad_integral_eq hs.1 (Q.diagSubgrad ht.1.le le_rfl hs.2)
    rw [intervalIntegral.integral_of_le hs.1, ← setIntegral_congr_set Ioo_ae_eq_Ioc] at hftc
    have h0 : (0 : ℝ) + t = t := zero_add t
    rw [h0] at hftc
    have hconst : ∫ _ in Ioo (0 : ℝ) s, (1 : ℝ) = s := by
      rw [setIntegral_const, Real.volume_real_Ioo_of_le hs.1, sub_zero, smul_eq_mul, mul_one]
    have hg_int : IntegrableOn (fun r => Q.g1 (r + t, r) + Q.g2 (r + t, r)) (Ioo (0 : ℝ) s) volume :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le hs.1).mp
        ((Q.diagSubgrad ht.1.le le_rfl hs.2).intervalIntegrable hs.1)
    have hD_eq : ∫ r in Ioo (0 : ℝ) s, D (r + t, r) =
        s - ∫ r in Ioo (0 : ℝ) s, (Q.g1 (r + t, r) + Q.g2 (r + t, r)) := by
      dsimp only [D]
      rw [integral_sub (integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)) hg_int,
        hconst]
    rw [hD_eq, hftc]
    dsimp only [w]; ring
  have hrho_d := integrableOn_rho_diag (s := 1 - t) hb.le ht.1
  have hw_d : IntegrableOn (fun s => w (s + t, s) * rho (s + t) s) (Ioo (0 : ℝ) (1 - t)) volume := by
    have hc : ContinuousOn (fun s => w (s + t, s)) (Ioo (0 : ℝ) (1 - t)) :=
      ((continuousOn_id.add continuousOn_const |>.add continuousOn_id).div_const 2).sub
        (Q.u_continuousOn.comp (f := fun s : ℝ => (s + t, s))
          ((continuous_id.add continuous_const).prodMk continuous_id).continuousOn
          (fun s hs => ⟨⟨by linarith [hs.1, ht.1], by linarith [hs.2]⟩, ⟨hs.1.le, by linarith [hs.2, ht.1]⟩⟩))
    have hm_rho : Measurable (fun s : ℝ => rho (s + t) s) := by unfold rho; fun_prop
    refine (hrho_d.const_mul 2).mono' ((hc.aestronglyMeasurable measurableSet_Ioo).mul
      hm_rho.aestronglyMeasurable) ?_
    rw [ae_restrict_iff' measurableSet_Ioo]; filter_upwards with s hs
    have hsq : (s + t, s) ∈ unitSquare := ⟨⟨by linarith [hs.1, ht.1], by linarith [hs.2]⟩, ⟨hs.1.le, by linarith [hs.2, ht.1]⟩⟩
    have hw_abs : |w (s + t, s)| ≤ 2 := by
      dsimp only [w]; rw [abs_le]; constructor <;> linarith [Q.u_nonneg _ hsq, Q.u_le_bound hsq, hQ_u0, hsq.1.1, hsq.1.2, hsq.2.1, hsq.2.2]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (rho_nonneg _ _)]
    exact mul_le_mul_of_nonneg_right hw_abs (rho_nonneg _ _)
  have hD_int : IntegrableOn (fun r => D (r + t, r)) (Ioo (0 : ℝ) (1 - t)) volume := by
    refine (integrableOn_const (C := (1 : ℝ)) (hs := by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)).mono'
      (hD_meas.comp ((measurable_id.add measurable_const).prodMk measurable_id)).aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Ioo]; filter_upwards with r hr
    have hsq : (r + t, r) ∈ unitSquare :=
      ⟨⟨by linarith [hr.1, ht.1], by linarith [hr.2]⟩, ⟨hr.1.le, by linarith [hr.2, ht.1]⟩⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (hD_bounds _ hsq).1]; exact (hD_bounds _ hsq).2
  have hswap := integral_swap_sublevel (ν := (volume : Measure ℝ)) (S := Ioo (0 : ℝ) (1 - t))
    measurableSet_Ioo (h := fun r : ℝ => r) measurable_id
    (k := fun s => rho (s + t) s) (F := fun r => D (r + t, r)) hrho_d hD_int
  have hL1 : ∫ c in Ioo (0 : ℝ) (1 - t),
      rho (c + t) c * (∫ x in Ioo (0 : ℝ) (1 - t) ∩ {x : ℝ | x < c}, D (x + t, x)) =
      (∫ s in Ioo (0 : ℝ) (1 - t), w (s + t, s) * rho (s + t) s) - w (t, 0) * gT t := by
    have hcongr : ∀ c ∈ Ioo (0 : ℝ) (1 - t),
        rho (c + t) c * (∫ x in Ioo (0 : ℝ) (1 - t) ∩ {x : ℝ | x < c}, D (x + t, x)) =
        w (c + t, c) * rho (c + t) c - w (t, 0) * rho (c + t) c := by
      intro c hc
      have hset : Ioo (0 : ℝ) (1 - t) ∩ {x : ℝ | x < c} = Ioo (0 : ℝ) c := by
        ext x
        exact ⟨fun hx => ⟨hx.1.1, hx.2⟩, fun hx => ⟨⟨hx.1, hx.2.trans hc.2⟩, hx.2⟩⟩
      rw [hset, ← hfwd c (Ioo_subset_Icc_self hc)]; ring
    rw [setIntegral_congr_fun measurableSet_Ioo hcongr, integral_sub hw_d (hrho_d.const_mul _),
      integral_const_mul, integral_rho_eq_gT ht.1 ht1]
  have hR1 : ∫ x in Ioo (0 : ℝ) (1 - t), D (x + t, x) * (∫ c in Ioo (max x 0) (1 - t), rho (c + t) c) =
      ∫ x in Ioo (0 : ℝ) (1 - t), D (x + t, x) * (gT t - Iwing x t) := by
    refine setIntegral_congr_fun measurableSet_Ioo (fun x hx => ?_)
    have hcont : ContinuousOn (fun r => Iwing r t) (Icc x (1 - t)) :=
      fun c hc => (hasDerivAt_Iwing_s (hx.1.trans_le hc.1) ht.1).continuousAt.continuousWithinAt
    have hint : IntervalIntegrable (fun r => rho (r + t) r) volume x (1 - t) :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le hx.2.le).mpr
        (hrho_d.mono_set (Ioo_subset_Ioo_left hx.1.le))
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx.2.le hcont
      (fun c hc => hasDerivAt_Iwing_s (hx.1.trans hc.1) ht.1) hint
    rw [intervalIntegral.integral_of_le hx.2.le, ← setIntegral_congr_set Ioo_ae_eq_Ioc] at h
    show D (x + t, x) * (∫ c in Ioo (max x 0) (1 - t), rho (c + t) c) =
      D (x + t, x) * (gT t - Iwing x t)
    rw [max_eq_left hx.1.le, h, Iwing_one_sub ht.1 ht1]
  have hstar : (∫ s in Ioo (0 : ℝ) (1 - t), w (s + t, s) * rho (s + t) s) - w (t, 0) * gT t =
      ∫ x in Ioo (0 : ℝ) (1 - t), D (x + t, x) * (gT t - Iwing x t) := by
    rw [← hL1, ← hR1]; exact hswap
  have hbar : w (1, 1 - t) = w (t, 0) + ∫ r in Ioo (0 : ℝ) (1 - t), D (r + t, r) := by
    have h := hfwd (1 - t) ⟨hb.le, le_rfl⟩
    have h1 : 1 - t + t = 1 := by ring
    rw [h1] at h
    linarith
  have hDG_int : IntegrableOn (fun x => D (x + t, x) * (gT t - Iwing x t)) (Ioo (0 : ℝ) (1 - t)) volume := by
    have h1 := (integrableOn_deficit_psiB Q ht).add (hD_int.const_mul (rho 1 (1 - t)))
    have h2 : IntegrableOn (fun x => 1 / 2 * ((1 - (Q.g1 (x + t, x) + Q.g2 (x + t, x))) * psiB t x +
        rho 1 (1 - t) * D (x + t, x))) (Ioo (0 : ℝ) (1 - t)) volume := h1.const_mul (1 / 2)
    refine IntegrableOn.congr_fun h2 (fun x _ => ?_) measurableSet_Ioo
    show 1 / 2 * ((1 - (Q.g1 (x + t, x) + Q.g2 (x + t, x))) * psiB t x +
        rho 1 (1 - t) * (1 - (Q.g1 (x + t, x) + Q.g2 (x + t, x)))) =
      (1 - (Q.g1 (x + t, x) + Q.g2 (x + t, x))) * (gT t - Iwing x t)
    unfold psiB; ring
  have hpsi : ∫ r in Ioo (0 : ℝ) (1 - t), D (r + t, r) * psiB t r =
      2 * (∫ x in Ioo (0 : ℝ) (1 - t), D (x + t, x) * (gT t - Iwing x t)) -
        rho 1 (1 - t) * ∫ r in Ioo (0 : ℝ) (1 - t), D (r + t, r) := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_sub (hDG_int.const_mul 2) (hD_int.const_mul _)]
    refine setIntegral_congr_fun measurableSet_Ioo (fun r _ => ?_)
    show D (r + t, r) * psiB t r =
      2 * (D (r + t, r) * (gT t - Iwing r t)) - rho 1 (1 - t) * D (r + t, r)
    unfold psiB; ring
  have hK : K t = 2 * gT t - rho 1 (1 - t) := by unfold K rho; rw [one_mul]
  rw [hpsi, hbar, hK]
  linear_combination 2 * hstar

/-! ### 10. Sharp strip dominance -/

lemma integrableOn_deficit_WA_stripPos (Q : InterimProfile) :
    IntegrableOn (fun ab : Type2 => (1 - (Q.g1 ab + Q.g2 ab)) * rho ab.1 ab.2 * WA2 ab)
      stripPos volume :=
  integrableOn_mul_bdd_on measurableSet_stripPos (integrableOn_deficit_stripPos Q) measurable_WA2
    (fun ab hab => (WA2_bounds hab.1.1.1 hab.1.2.1).1) (fun ab hab => (WA2_bounds hab.1.1.1 hab.1.2.1).2)

/-- Integrated form of `sharp_pointwise` along one diagonal. -/
lemma lemma5_diag_bound (Q : InterimProfile) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) t0) :
    let D : Type2 → ℝ := fun ab => 1 - (Q.g1 ab + Q.g2 ab)
    (∫ s in Ioo (0 : ℝ) (1 - t), D (s + t, s) * rho (s + t) s * WA2 (s + t, s)) +
        (∫ r in Ioo (0 : ℝ) (1 - t), D (r + t, r) * psiB t r) ≤
      2 * (1 / Real.pi) * ∫ s in Ioo (0 : ℝ) (1 - t), D (s + t, s) * rho (s + t) s := by
  intro D
  have hD_meas : Measurable D := measurable_const.sub (Q.g1_meas.add Q.g2_meas)
  have hD_bounds : ∀ ab ∈ unitSquare, 0 ≤ D ab ∧ D ab ≤ 1 := fun ab hab =>
    ⟨by dsimp only [D]; linarith [Q.g_sum_le ab hab],
     by dsimp only [D]; linarith [Q.g1_nonneg ab hab, Q.g2_nonneg ab hab]⟩
  have hrho_d := integrableOn_rho_diag (s := 1 - t) (by linarith [ht.2, t0_lt_one]) ht.1
  have hm : Measurable (fun s : ℝ => ((s + t, s) : Type2)) :=
    (measurable_id.add measurable_const).prodMk measurable_id
  have hm_rho : Measurable (fun s : ℝ => rho (s + t) s) := by unfold rho; fun_prop
  have hsqs : ∀ s ∈ Ioo (0 : ℝ) (1 - t), (s + t, s) ∈ unitSquare := fun s hs =>
    ⟨⟨by linarith [hs.1, ht.1], by linarith [hs.2]⟩, ⟨hs.1.le, by linarith [hs.2, ht.1]⟩⟩
  have hIt : IntegrableOn (fun s => D (s + t, s) * rho (s + t) s) (Ioo (0 : ℝ) (1 - t)) volume := by
    refine hrho_d.mono' ((hD_meas.comp hm).mul hm_rho).aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Ioo]; filter_upwards with s hs
    have hb := hD_bounds _ (hsqs s hs)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hb.1 (rho_nonneg _ _))]
    calc D (s + t, s) * rho (s + t) s ≤ 1 * rho (s + t) s :=
          mul_le_mul_of_nonneg_right hb.2 (rho_nonneg _ _)
      _ = rho (s + t) s := one_mul _
  have hAt : IntegrableOn (fun s => D (s + t, s) * rho (s + t) s * WA2 (s + t, s))
      (Ioo (0 : ℝ) (1 - t)) volume :=
    integrableOn_mul_bdd_on measurableSet_Ioo hIt (measurable_WA2.comp hm)
      (fun s hs => (WA2_bounds (ab := (s + t, s))
        (by show (0 : ℝ) < s + t; linarith [hs.1, ht.1]) hs.1).1)
      (fun s hs => (WA2_bounds (ab := (s + t, s))
        (by show (0 : ℝ) < s + t; linarith [hs.1, ht.1]) hs.1).2)
  have hBt := integrableOn_deficit_psiB Q ht
  rw [← integral_add hAt hBt, ← integral_const_mul]
  refine setIntegral_mono_on (hAt.add hBt) (hIt.const_mul _) measurableSet_Ioo (fun s hs => ?_)
  have hp := sharp_pointwise ht hs.1
  have hD0 := (hD_bounds _ (hsqs s hs)).1
  have hmul := mul_le_mul_of_nonneg_left hp hD0
  dsimp only [D] at hmul ⊢
  linarith

/-- Strip dominance for a symmetric profile with `u(0, 0) = 0`. -/
lemma lemma5_strip_dominance_sym {L : ℝ} (hL : 2 / Real.pi ≤ L) (Q : InterimProfile)
    (hQ_sym_u : ∀ a b, Q.u (b, a) = Q.u (a, b))
    (hQ_sym_g : ∀ a b, Q.g1 (b, a) = Q.g2 (a, b))
    (hQ_u0 : Q.u (0, 0) = 0) :
    stripFunctional L Q ≤ M1 L := by
  let w : Type2 → ℝ := fun ab => (ab.1 + ab.2) / 2 - Q.u ab
  let D : Type2 → ℝ := fun ab => 1 - (Q.g1 ab + Q.g2 ab)
  have hD_bounds : ∀ ab ∈ unitSquare, 0 ≤ D ab ∧ D ab ≤ 1 := fun ab hab =>
    ⟨by dsimp only [D]; linarith [Q.g_sum_le ab hab],
     by dsimp only [D]; linarith [Q.g1_nonneg ab hab, Q.g2_nonneg ab hab]⟩
  have hhalf_eq := lemma5_half_strip_eq L Q hQ_sym_u hQ_sym_g
  have hD_meas : Measurable D := measurable_const.sub (Q.g1_meas.add Q.g2_meas)
  have hD_int_S : IntegrableOn (fun ab : Type2 => D ab * rho ab.1 ab.2) stripPos volume :=
    integrableOn_deficit_stripPos Q
  have hw_int_S : IntegrableOn (fun ab : Type2 => w ab * rho ab.1 ab.2) stripPos volume := by
    have hdom := integrableOn_rho_stripPos.const_mul 2
    have hmu : AEStronglyMeasurable Q.u (volume.restrict stripPos) :=
      Q.u_aestronglyMeasurable.mono_measure (Measure.restrict_mono Set.inter_subset_left le_rfl)
    have hmw : AEStronglyMeasurable w (volume.restrict stripPos) :=
      (((measurable_fst.add measurable_snd).div_const 2).aestronglyMeasurable).sub hmu
    refine hdom.mono' (hmw.mul (by unfold rho; fun_prop : Measurable _).aestronglyMeasurable) ?_
    rw [ae_restrict_iff' measurableSet_stripPos]; filter_upwards with ab hab
    have hsq : ab ∈ unitSquare := ⟨Ioo_subset_Icc_self hab.1.1, Ioo_subset_Icc_self hab.1.2⟩
    have hu_nn := Q.u_nonneg ab hsq; have hu_le : Q.u ab ≤ 1 := by linarith [Q.u_le_bound hsq, hQ_u0]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (rho_nonneg _ _)]
    have hw_abs : |w ab| ≤ 2 := by
      dsimp only [w]; rw [abs_le]; constructor <;> linarith [hsq.1.1, hsq.1.2, hsq.2.1, hsq.2.2]
    exact mul_le_mul_of_nonneg_right hw_abs (rho_nonneg _ _)
  have hKw0_int : IntegrableOn (fun t => K t * w (t, 0)) (Ioo (0 : ℝ) t0) volume := by
    have hdom := integrableOn_K_Ioo_t0.abs.const_mul 2
    have hc : ContinuousOn (fun t => w (t, 0)) (Ioo (0 : ℝ) t0) :=
      ((continuousOn_id.add continuousOn_const).div_const 2).sub
        (Q.u_continuousOn.comp (f := fun t : ℝ => (t, (0 : ℝ))) (continuous_id.prodMk continuous_const).continuousOn
          (fun t ht => ⟨⟨ht.1.le, ht.2.le.trans t0_lt_one.le⟩, ⟨le_rfl, zero_le_one⟩⟩))
    have hmK : Measurable K := by unfold K gT artanh; fun_prop
    refine hdom.mono' (hmK.aestronglyMeasurable.mul (hc.aestronglyMeasurable measurableSet_Ioo)) ?_
    rw [ae_restrict_iff' measurableSet_Ioo]; filter_upwards with t ht
    have hsq : (t, (0 : ℝ)) ∈ unitSquare := ⟨⟨ht.1.le, ht.2.le.trans t0_lt_one.le⟩, ⟨le_rfl, zero_le_one⟩⟩
    have hu_nn := Q.u_nonneg _ hsq; have hu_le : Q.u (t, 0) ≤ 1 := by linarith [Q.u_le_bound hsq, hQ_u0]
    have hw_abs : |w (t, 0)| ≤ 2 := by dsimp only [w]; rw [abs_le]; constructor <;> linarith [ht.1, ht.2, t0_lt_one]
    rw [Real.norm_eq_abs, abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right hw_abs (abs_nonneg _)
  have hi2 : IntegrableOn (fun t => w (1, 1 - t) * rho 1 (1 - t)) (Ioo (0 : ℝ) t0) volume := by
    have hc_rho : ContinuousOn (fun t : ℝ => rho 1 (1 - t)) (Icc (0 : ℝ) t0) := by
      unfold rho
      refine continuousOn_const.div (continuousOn_const.mul
        (Real.continuous_sqrt.comp (continuous_const.mul (continuous_const.sub continuous_id))).continuousOn) ?_
      intro t ht
      have hsq : 0 < Real.sqrt (1 * (1 - t)) := Real.sqrt_pos.mpr (by linarith [ht.2, t0_lt_one])
      exact mul_ne_zero (by norm_num : (4 : ℝ) ≠ 0) hsq.ne'
    have hc_w : ContinuousOn (fun t => w (1, 1 - t)) (Icc (0 : ℝ) t0) :=
      ((continuousOn_const.add (continuousOn_const.sub continuousOn_id)).div_const 2).sub
        (Q.u_continuousOn.comp (f := fun t : ℝ => ((1 : ℝ), 1 - t))
          (continuous_const.prodMk (continuous_const.sub continuous_id)).continuousOn
          (fun t ht => ⟨⟨zero_le_one, le_rfl⟩, ⟨by linarith [ht.2, t0_lt_one], by linarith [ht.1]⟩⟩))
    exact (hc_w.mul hc_rho).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hshear_w : ∫ ab in stripPos, w ab * rho ab.1 ab.2 =
      ∫ t in Ioo (0 : ℝ) t0, ∫ s in Ioo (0 : ℝ) (1 - t), w (s + t, s) * rho (s + t) s := by
    rw [stripPos_eq_setOf]
    exact setIntegral_shear_upper le_rfl t0_pos.le t0_lt_one.le (by rwa [← stripPos_eq_setOf])
  have hshear_D : ∫ ab in stripPos, D ab * rho ab.1 ab.2 =
      ∫ t in Ioo (0 : ℝ) t0, ∫ s in Ioo (0 : ℝ) (1 - t), D (s + t, s) * rho (s + t) s := by
    rw [stripPos_eq_setOf]
    exact setIntegral_shear_upper le_rfl t0_pos.le t0_lt_one.le (by rwa [← stripPos_eq_setOf])
  have hlo_int : IntegrableOn (fun t => 2 * ∫ s in Ioo (0 : ℝ) (1 - t), w (s + t, s) * rho (s + t) s)
      (Ioo (0 : ℝ) t0) volume := (integrableOn_shear_stripPos hw_int_S).const_mul 2
  have hI_int : IntegrableOn (fun t => ∫ s in Ioo (0 : ℝ) (1 - t), D (s + t, s) * rho (s + t) s)
      (Ioo (0 : ℝ) t0) volume := integrableOn_shear_stripPos hD_int_S
  have hA_int : IntegrableOn (fun t => ∫ s in Ioo (0 : ℝ) (1 - t),
      D (s + t, s) * rho (s + t) s * WA2 (s + t, s)) (Ioo (0 : ℝ) t0) volume :=
    integrableOn_shear_stripPos (integrableOn_deficit_WA_stripPos Q)
  have hid : ∀ t ∈ Ioo (0 : ℝ) t0,
      2 * (∫ s in Ioo (0 : ℝ) (1 - t), w (s + t, s) * rho (s + t) s) - w (1, 1 - t) * rho 1 (1 - t) =
      K t * w (t, 0) + ∫ r in Ioo (0 : ℝ) (1 - t), D (r + t, r) * psiB t r :=
    fun t ht => lemma5_diag_identity Q hQ_u0 ht
  have hB_int : IntegrableOn (fun t => ∫ r in Ioo (0 : ℝ) (1 - t), D (r + t, r) * psiB t r)
      (Ioo (0 : ℝ) t0) volume := by
    refine ((hlo_int.sub hi2).sub hKw0_int).congr_fun (fun t ht => ?_) measurableSet_Ioo
    have h := hid t ht
    show 2 * (∫ s in Ioo (0 : ℝ) (1 - t), w (s + t, s) * rho (s + t) s) - w (1, 1 - t) * rho 1 (1 - t) -
      K t * w (t, 0) = _
    linarith
  have hsum : 2 * (∫ ab in stripPos, w ab * rho ab.1 ab.2) -
      (∫ t in Ioo (0 : ℝ) t0, w (1, 1 - t) * rho 1 (1 - t)) =
      (∫ t in Ioo (0 : ℝ) t0, K t * w (t, 0)) +
      ∫ t in Ioo (0 : ℝ) t0, ∫ r in Ioo (0 : ℝ) (1 - t), D (r + t, r) * psiB t r := by
    rw [hshear_w, ← integral_const_mul, ← integral_sub hlo_int hi2, ← integral_add hKw0_int hB_int]
    exact setIntegral_congr_fun measurableSet_Ioo (fun t ht => hid t ht)
  have htermA := lemma5_termA_sharp Q hQ_sym_u hQ_u0
  have hpt : ∀ t ∈ Ioo (0 : ℝ) t0,
      (∫ s in Ioo (0 : ℝ) (1 - t), D (s + t, s) * rho (s + t) s * WA2 (s + t, s)) +
        (∫ r in Ioo (0 : ℝ) (1 - t), D (r + t, r) * psiB t r) ≤
      2 * (1 / Real.pi) * ∫ s in Ioo (0 : ℝ) (1 - t), D (s + t, s) * rho (s + t) s :=
    fun t ht => lemma5_diag_bound Q ht
  have hAB : (∫ t in Ioo (0 : ℝ) t0, ∫ s in Ioo (0 : ℝ) (1 - t),
        D (s + t, s) * rho (s + t) s * WA2 (s + t, s)) +
      (∫ t in Ioo (0 : ℝ) t0, ∫ r in Ioo (0 : ℝ) (1 - t), D (r + t, r) * psiB t r) ≤
      2 * (1 / Real.pi) * ∫ ab in stripPos, D ab * rho ab.1 ab.2 := by
    rw [hshear_D, ← integral_add hA_int hB_int, ← integral_const_mul]
    exact setIntegral_mono_on (hA_int.add hB_int) (hI_int.const_mul _) measurableSet_Ioo hpt
  have hD_S_nn : 0 ≤ ∫ ab in stripPos, D ab * rho ab.1 ab.2 := by
    refine setIntegral_nonneg measurableSet_stripPos (fun ab hab => ?_)
    have hsq : ab ∈ unitSquare := ⟨Ioo_subset_Icc_self hab.1.1, Ioo_subset_Icc_self hab.1.2⟩
    exact mul_nonneg (hD_bounds _ hsq).1 (rho_nonneg _ _)
  have hfinal : (stripFunctional L Q - M1 L) / 2 ≤
      (2 * (1 / Real.pi) - L) * ∫ ab in stripPos, D ab * rho ab.1 ab.2 := by
    have fin : ∀ X ID IW IB TA TB TAs : ℝ, X = -L * ID + 2 * IW - IB → 2 * IW - IB = TA + TB →
        TA ≤ TAs → TAs + TB ≤ 2 * (1 / Real.pi) * ID → X ≤ (2 * (1 / Real.pi) - L) * ID := by
      intro X ID IW IB TA TB TAs h1 h2 h3 h4; linarith
    exact fin _ _ _ _ _ _ _ hhalf_eq hsum htermA hAB
  have hL' : 2 * (1 / Real.pi) ≤ L := by
    rw [show 2 * (1 / Real.pi) = 2 / Real.pi by ring]; exact hL
  have hle0 : (2 * (1 / Real.pi) - L) * ∫ ab in stripPos, D ab * rho ab.1 ab.2 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) hD_S_nn
  linarith


/-- **Lemma 5 (sharp strip dominance):** for every `L ≥ 2/π` and every interim profile,
`stripFunctional L P ≤ M₁(L)`. -/
theorem lemma5_strip_dominance {L : ℝ} (hL : 2 / Real.pi ≤ L) (P : InterimProfile) :
    stripFunctional L P ≤ M1 L := by
  let Q : InterimProfile := P.symm.shiftZero
  have hQ_sym_u : ∀ a b, Q.u (b, a) = Q.u (a, b) := by
    intro a b; dsimp only [Q, InterimProfile.shiftZero, InterimProfile.symm]; ring
  have hQ_sym_g : ∀ a b, Q.g1 (b, a) = Q.g2 (a, b) := by
    intro a b; dsimp only [Q, InterimProfile.shiftZero, InterimProfile.symm]; ring
  have hQ_u0 : Q.u (0, 0) = 0 := by
    dsimp only [Q, InterimProfile.shiftZero]; ring
  calc stripFunctional L P = stripFunctional L P.symm := (stripFunctional_symm L P).symm
    _ ≤ stripFunctional L Q := stripFunctional_le_shiftZero L P.symm
    _ ≤ M1 L := lemma5_strip_dominance_sym hL Q hQ_sym_u hQ_sym_g hQ_u0

end

end EconCSAuction
