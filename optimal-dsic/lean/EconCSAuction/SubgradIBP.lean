import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Exact 1D Fundamental Theorem of Calculus & Integration by Parts for Arbitrary Subgradients

Proves WITHOUT Rademacher's theorem or 2D Sobolev theory:
1. `subgrad_integral_eq`: If `f, d : ℝ → ℝ` satisfy the convex subgradient sandwich
   `(y - x) * d x ≤ f y - f x ≤ (y - x) * d y` for all `a ≤ x ≤ y ≤ b`, then `d` is monotone on
   `[a, b]`, interval-integrable, and `∫ x in a..b, d x = f b - f a`.
2. `subgrad_ibp`: For any such `(f, d)` and any `C¹` weight `φ` on `[a, b]`,
   `∫ x in Ioo a b, (d x * φ x + f x * φ' x) = f b * φ b - f a * φ a`.

This single 1D tool powers every integration by parts in Lemma 4 and Lemma 5
for arbitrary non-smooth convex interim utility functions.
-/

open MeasureTheory Set

namespace EconCSAuction

noncomputable section

/-- Convex subgradient sandwich on `[a, b]`. -/
def IsSubgradOn (f d : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, x ≤ y →
    (y - x) * d x ≤ f y - f x ∧ f y - f x ≤ (y - x) * d y

lemma IsSubgradOn.mono_set {f d : ℝ → ℝ} {a b a' b' : ℝ}
    (h : IsSubgradOn f d a b) (ha : a ≤ a') (hb : b' ≤ b) :
    IsSubgradOn f d a' b' :=
  fun x hx y hy hxy => h x ⟨ha.trans hx.1, hx.2.trans hb⟩ y ⟨ha.trans hy.1, hy.2.trans hb⟩ hxy

lemma IsSubgradOn.monotoneOn {f d : ℝ → ℝ} {a b : ℝ} (h : IsSubgradOn f d a b) :
    MonotoneOn d (Icc a b) := by
  intro x hx y hy hxy
  rcases eq_or_lt_of_le hxy with rfl | hlt
  · exact le_rfl
  · have ⟨h1, h2⟩ := h x hx y hy hxy
    have hpos : 0 < y - x := sub_pos.mpr hlt
    nlinarith

lemma IsSubgradOn.intervalIntegrable {f d : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (h : IsSubgradOn f d a b) :
    IntervalIntegrable d volume a b := by
  have hm : MonotoneOn d (uIcc a b) := by rw [uIcc_of_le hab]; exact h.monotoneOn
  exact hm.intervalIntegrable

lemma IsSubgradOn.continuousOn {f d : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (h : IsSubgradOn f d a b) :
    ContinuousOn f (Icc a b) := by
  have hmono := h.monotoneOn
  let M : ℝ := max (|d a|) (|d b|) + 1
  have hM : 0 ≤ M := by positivity
  have hlip : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, |f y - f x| ≤ M * |y - x| := by
    intro x hx y hy
    have hd_bdd : ∀ z ∈ Icc a b, |d z| ≤ M := by
      intro z hz
      have h1 : d a ≤ d z := hmono ⟨le_rfl, hab⟩ hz hz.1
      have h2 : d z ≤ d b := hmono hz ⟨hab, le_rfl⟩ hz.2
      rw [abs_le]
      have ha1 : -|d a| ≤ d a := neg_abs_le _
      have hb1 : d b ≤ |d b| := le_abs_self _
      have hm1 : |d a| ≤ M := by linarith [le_max_left (|d a|) (|d b|)]
      have hm2 : |d b| ≤ M := by linarith [le_max_right (|d a|) (|d b|)]
      exact ⟨by linarith, by linarith⟩
    rcases le_total x y with hxy | hyx
    · have ⟨h1, h2⟩ := h x hx y hy hxy
      have hdx := abs_le.mp (hd_bdd x hx)
      have hdy := abs_le.mp (hd_bdd y hy)
      rw [abs_of_nonneg (sub_nonneg.mpr hxy), abs_le]
      exact ⟨by nlinarith, by nlinarith⟩
    · have ⟨h1, h2⟩ := h y hy x hx hyx
      have hdx := abs_le.mp (hd_bdd x hx)
      have hdy := abs_le.mp (hd_bdd y hy)
      have habs : |y - x| = x - y := by rw [abs_of_nonpos (sub_nonpos.mpr hyx)]; ring
      rw [habs, abs_le]
      exact ⟨by nlinarith, by nlinarith⟩
  rw [Metric.continuousOn_iff]
  intro x hx ε hε
  refine ⟨ε / (M + 1), div_pos hε (by linarith), fun y hy hdist => ?_⟩
  rw [Real.dist_eq] at hdist ⊢
  calc |f y - f x| ≤ M * |y - x| := hlip x hx y hy
    _ ≤ M * (ε / (M + 1)) := mul_le_mul_of_nonneg_left hdist.le hM
    _ < (M + 1) * (ε / (M + 1)) := by
        have hpos : 0 < ε / (M + 1) := div_pos hε (by linarith)
        nlinarith
    _ = ε := mul_div_cancel₀ ε (by linarith)

/-- Exact 1D FTC for arbitrary convex subgradients via uniform Riemann sandwich:
`∫ x in a..b, d x = f b - f a`. -/
lemma subgrad_integral_eq {f d : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (h : IsSubgradOn f d a b) :
    ∫ x in a..b, d x = f b - f a := by
  rcases eq_or_lt_of_le hab with rfl | hlt
  · simp
  · have hmono := h.monotoneOn
    have hint := h.intervalIntegrable hab
    have hd_diff : 0 ≤ d b - d a := sub_nonneg.mpr (hmono ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab)
    -- Show `|(∫ x in a..b, d x) - (f b - f a)| ≤ ε` for every `ε > 0`.
    suffices hle : ∀ ε > 0, |(∫ x in a..b, d x) - (f b - f a)| ≤ ε by
      by_contra hne
      have hpos : 0 < |(∫ x in a..b, d x) - (f b - f a)| := abs_pos.mpr (sub_ne_zero.mpr hne)
      have := hle (|(∫ x in a..b, d x) - (f b - f a)| / 2) (by linarith)
      linarith
    intro ε hε
    obtain ⟨n, hn⟩ := exists_nat_gt ((b - a) * (d b - d a) / ε)
    have hn_pos : 0 < n := by
      by_contra h0
      have hn0 : n = 0 := Nat.eq_zero_of_not_pos h0
      subst hn0
      have : 0 ≤ (b - a) * (d b - d a) / ε := by positivity
      simp at hn
      linarith
    have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn_pos
    let step : ℝ := (b - a) / (n : ℝ)
    have hstep_pos : 0 < step := div_pos (sub_pos.mpr hlt) hnR
    let pt : ℕ → ℝ := fun k => a + (k : ℝ) * step
    have hpt0 : pt 0 = a := by simp [pt]
    have hptn : pt n = b := by
      simp only [pt, step]
      field_simp [hnR.ne']
      ring
    have hpt_mem : ∀ k ≤ n, pt k ∈ Icc a b := by
      intro k hk
      have hkR : (k : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hk
      refine ⟨by dsimp [pt]; nlinarith [Nat.cast_nonneg (α := ℝ) k], ?_⟩
      dsimp [pt, step]
      have : (k : ℝ) * ((b - a) / (n : ℝ)) ≤ (n : ℝ) * ((b - a) / (n : ℝ)) :=
        mul_le_mul_of_nonneg_right hkR hstep_pos.le
      rw [mul_div_cancel₀ _ hnR.ne'] at this
      linarith
    have hpt_step : ∀ k : ℕ, pt (k + 1) - pt k = step := by
      intro k; dsimp [pt]; push_cast; ring
    -- Telescoping lower & upper bounds for `f b - f a`
    have hf_tele : f b - f a = ∑ k ∈ Finset.range n, (f (pt (k + 1)) - f (pt k)) := by
      rw [Finset.sum_range_sub (fun k => f (pt k)) n, hpt0, hptn]
    have hf_lower : (∑ k ∈ Finset.range n, step * d (pt k)) ≤ f b - f a := by
      rw [hf_tele]
      refine Finset.sum_le_sum (fun k hk => ?_)
      have hk' : k < n := Finset.mem_range.mp hk
      have hsand := h (pt k) (hpt_mem k hk'.le) (pt (k + 1)) (hpt_mem (k + 1) hk')
        (by linarith [hpt_step k])
      rw [hpt_step k] at hsand
      exact hsand.1
    have hf_upper : f b - f a ≤ ∑ k ∈ Finset.range n, step * d (pt (k + 1)) := by
      rw [hf_tele]
      refine Finset.sum_le_sum (fun k hk => ?_)
      have hk' : k < n := Finset.mem_range.mp hk
      have hsand := h (pt k) (hpt_mem k hk'.le) (pt (k + 1)) (hpt_mem (k + 1) hk')
        (by linarith [hpt_step k])
      rw [hpt_step k] at hsand
      exact hsand.2
    -- Same lower & upper bounds for `∫ x in a..b, d x`
    have hint_k : ∀ k ∈ Finset.range n, IntervalIntegrable d volume (pt k) (pt (k + 1)) := by
      intro k hk
      have hk' : k < n := Finset.mem_range.mp hk
      exact (h.mono_set (hpt_mem k hk'.le).1 (hpt_mem (k + 1) hk').2).intervalIntegrable
        (by linarith [hpt_step k])
    have hi_tele : ∫ x in a..b, d x = ∑ k ∈ Finset.range n, ∫ x in pt k..pt (k + 1), d x := by
      rw [← hpt0, ← hptn]
      exact (intervalIntegral.sum_integral_adjacent_intervals
        (fun k hk => hint_k k (Finset.mem_range.mpr hk))).symm
    have hi_lower : (∑ k ∈ Finset.range n, step * d (pt k)) ≤ ∫ x in a..b, d x := by
      rw [hi_tele]
      refine Finset.sum_le_sum (fun k hk => ?_)
      have hk' : k < n := Finset.mem_range.mp hk
      have hle_pt : pt k ≤ pt (k + 1) := by linarith [hpt_step k]
      have hconst : ∫ _ in pt k..pt (k + 1), d (pt k) = step * d (pt k) := by
        rw [intervalIntegral.integral_const, smul_eq_mul, hpt_step k]
      rw [← hconst]
      refine intervalIntegral.integral_mono_on hle_pt intervalIntegrable_const (hint_k k hk) ?_
      intro x hx
      exact hmono (hpt_mem k hk'.le)
        ⟨(hpt_mem k hk'.le).1.trans hx.1, hx.2.trans (hpt_mem (k + 1) hk').2⟩ hx.1
    have hi_upper : (∫ x in a..b, d x) ≤ ∑ k ∈ Finset.range n, step * d (pt (k + 1)) := by
      rw [hi_tele]
      refine Finset.sum_le_sum (fun k hk => ?_)
      have hk' : k < n := Finset.mem_range.mp hk
      have hle_pt : pt k ≤ pt (k + 1) := by linarith [hpt_step k]
      have hconst : ∫ _ in pt k..pt (k + 1), d (pt (k + 1)) = step * d (pt (k + 1)) := by
        rw [intervalIntegral.integral_const, smul_eq_mul, hpt_step k]
      rw [← hconst]
      refine intervalIntegral.integral_mono_on hle_pt (hint_k k hk) intervalIntegrable_const ?_
      intro x hx
      exact hmono ⟨(hpt_mem k hk'.le).1.trans hx.1, hx.2.trans (hpt_mem (k + 1) hk').2⟩
        (hpt_mem (k + 1) hk') hx.2
    -- Gap `U_n - L_n = step * (d b - d a) ≤ ε`
    have hgap : (∑ k ∈ Finset.range n, step * d (pt (k + 1))) -
        (∑ k ∈ Finset.range n, step * d (pt k)) = step * (d b - d a) := by
      rw [← Finset.sum_sub_distrib]
      have hterm : ∀ k ∈ Finset.range n,
          step * d (pt (k + 1)) - step * d (pt k) = step * (d (pt (k + 1)) - d (pt k)) :=
        fun k _ => by ring
      rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum,
          Finset.sum_range_sub (fun k => d (pt k)) n, hpt0, hptn]
    have hgap_le : step * (d b - d a) ≤ ε := by
      have hmul : (b - a) * (d b - d a) < (n : ℝ) * ε := by
        have := (div_lt_iff₀ hε).mp hn
        linarith
      dsimp [step]
      have : (b - a) / (n : ℝ) * (d b - d a) = (b - a) * (d b - d a) / (n : ℝ) := by ring
      rw [this, div_le_iff₀ hnR]
      linarith
    rw [abs_le]
    exact ⟨by linarith, by linarith⟩

/-- Exact 1D integration by parts for arbitrary non-smooth subgradient pairs `(f, d)` against any
`C¹` weight `φ` on `[a, b]`:
`∫ x in Ioo a b, (d x * φ x + f x * φ' x) = f b * φ b - f a * φ a`. -/
lemma subgrad_ibp_of_integrable {f d φ φ' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hsub : IsSubgradOn f d a b)
    (hφ_cont : ContinuousOn φ (Icc a b))
    (hφ'_int : IntegrableOn φ' (Ioo a b) volume)
    (hφ_deriv : ∀ x ∈ Ioo a b, HasDerivAt φ (φ' x) x) :
    ∫ x in Ioo a b, (d x * φ x + f x * φ' x) = f b * φ b - f a * φ a := by
  rcases eq_or_lt_of_le hab with rfl | hlt
  · simp
  · have hd_int : IntegrableOn d (Ioo a b) volume :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le hab).mp (hsub.intervalIntegrable hab)
    have hf_cont : ContinuousOn f (Icc a b) := hsub.continuousOn hab
    have hφ_int : IntegrableOn φ (Ioo a b) volume :=
      hφ_cont.integrableOn_Icc.mono_set Ioo_subset_Icc_self
    have hf_int : IntegrableOn f (Ioo a b) volume :=
      hf_cont.integrableOn_Icc.mono_set Ioo_subset_Icc_self
    have hfφ'_int : IntegrableOn (fun x => f x * φ' x) (Ioo a b) volume := by
      obtain ⟨Cf, hCf⟩ := isCompact_Icc.exists_bound_of_continuousOn hf_cont
      have hmeas : AEStronglyMeasurable (fun x => f x * φ' x) (volume.restrict (Ioo a b)) :=
        hf_int.aestronglyMeasurable.mul hφ'_int.aestronglyMeasurable
      refine (hφ'_int.norm.const_mul (max Cf 0)).mono' hmeas ?_
      rw [ae_restrict_iff' measurableSet_Ioo]
      filter_upwards with x hx
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right ((hCf x (Ioo_subset_Icc_self hx)).trans (le_max_left _ _))
        (norm_nonneg _)
    have hdφ_int : IntegrableOn (fun x => d x * φ x) (Ioo a b) volume := by
      obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hφ_cont
      have hmeas : AEStronglyMeasurable (fun x => d x * φ x) (volume.restrict (Ioo a b)) :=
        hd_int.aestronglyMeasurable.mul hφ_int.aestronglyMeasurable
      refine (hd_int.norm.const_mul (max C 0)).mono' hmeas ?_
      rw [ae_restrict_iff' measurableSet_Ioo]
      filter_upwards with x hx
      rw [norm_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right ((hC x (Ioo_subset_Icc_self hx)).trans (le_max_left _ _))
        (norm_nonneg _)
    -- Triangle Fubini for `∫ x in (a, b), (f x - f a) * φ' x`
    let T : Set (ℝ × ℝ) := (Ioo a b ×ˢ Ioo a b) ∩ {xr : ℝ × ℝ | xr.2 < xr.1}
    have hT_meas : MeasurableSet T :=
      (measurableSet_Ioo.prod measurableSet_Ioo).inter (measurableSet_lt measurable_snd measurable_fst)
    have hprod_int : IntegrableOn (fun xr : ℝ × ℝ => d xr.2 * φ' xr.1) (Ioo a b ×ˢ Ioo a b) volume := by
      unfold IntegrableOn
      rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
      have h1 : Integrable (fun xr : ℝ × ℝ => φ' xr.1 * d xr.2)
          ((volume.restrict (Ioo a b)).prod (volume.restrict (Ioo a b))) :=
        hφ'_int.mul_prod hd_int
      exact h1.congr (ae_of_all _ (fun xr => mul_comm _ _))
    have hT_int : Integrable (T.indicator (fun xr : ℝ × ℝ => d xr.2 * φ' xr.1)) (volume.prod volume) := by
      rw [← Measure.volume_eq_prod]
      exact (integrable_indicator_iff hT_meas).mpr (hprod_int.mono_set Set.inter_subset_left)
    -- Step 1: LHS of Fubini = `∫ x in Ioo a b, (f x - f a) * φ' x`
    have hLHS : ∫ xr, T.indicator (fun xr : ℝ × ℝ => d xr.2 * φ' xr.1) xr ∂(volume.prod volume) =
        ∫ x in Ioo a b, (f x - f a) * φ' x := by
      rw [integral_prod _ hT_int, ← integral_indicator measurableSet_Ioo]
      congr 1; ext x
      by_cases hx : x ∈ Ioo a b
      · simp only [indicator_of_mem hx]
        have hfx : f x - f a = ∫ r in Ioo a x, d r := by
          rw [setIntegral_congr_set Ioo_ae_eq_Ioc, ← intervalIntegral.integral_of_le hx.1.le]
          exact (subgrad_integral_eq hx.1.le (hsub.mono_set le_rfl hx.2.le)).symm
        rw [hfx, ← integral_mul_const, ← integral_indicator measurableSet_Ioo]
        congr 1; ext r
        by_cases hr : r ∈ Ioo a x
        · have hmem : (x, r) ∈ T := ⟨⟨hx, hr.1, hr.2.trans hx.2⟩, hr.2⟩
          simp [hmem, hr]
        · have hnot : (x, r) ∉ T := fun h => hr ⟨h.1.2.1, h.2⟩
          simp [hnot, hr]
      · simp only [indicator_of_notMem hx]
        have hzero : ∀ r, T.indicator (fun xr : ℝ × ℝ => d xr.2 * φ' xr.1) (x, r) = 0 := by
          intro r; have hnot : (x, r) ∉ T := fun h => hx h.1.1; simp [hnot]
        simp [hzero]
    -- Step 2: RHS of Fubini = `∫ r in Ioo a b, d r * (φ b - φ r)`
    have hRHS : ∫ xr, T.indicator (fun xr : ℝ × ℝ => d xr.2 * φ' xr.1) xr ∂(volume.prod volume) =
        ∫ r in Ioo a b, d r * (φ b - φ r) := by
      rw [integral_prod_symm _ hT_int, ← integral_indicator measurableSet_Ioo]
      congr 1; ext r
      by_cases hr : r ∈ Ioo a b
      · simp only [indicator_of_mem hr]
        have hφr : φ b - φ r = ∫ x in Ioo r b, φ' x := by
          rw [setIntegral_congr_set Ioo_ae_eq_Ioc, ← intervalIntegral.integral_of_le hr.2.le]
          symm
          exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hr.2.le
            (hφ_cont.mono (Icc_subset_Icc_left hr.1.le))
            (fun x hx => hφ_deriv x ⟨hr.1.trans hx.1, hx.2⟩)
            ((intervalIntegrable_iff_integrableOn_Ioo_of_le hr.2.le).mpr
              (hφ'_int.mono_set (Ioo_subset_Ioo_left hr.1.le)))
        rw [hφr, ← integral_const_mul, ← integral_indicator measurableSet_Ioo]
        congr 1; ext x
        by_cases hx : x ∈ Ioo r b
        · have hmem : (x, r) ∈ T := ⟨⟨⟨hr.1.trans hx.1, hx.2⟩, hr⟩, hx.1⟩
          simp [hmem, hx]
        · have hnot : (x, r) ∉ T := fun h => hx ⟨h.2, h.1.1.2⟩
          simp [hnot, hx]
      · simp only [indicator_of_notMem hr]
        have hzero : ∀ x, T.indicator (fun xr : ℝ × ℝ => d xr.2 * φ' xr.1) (x, r) = 0 := by
          intro x; have hnot : (x, r) ∉ T := fun h => hr h.1.2; simp [hnot]
        simp [hzero]
    -- Combine:
    have hFub : ∫ x in Ioo a b, (f x - f a) * φ' x = ∫ r in Ioo a b, d r * (φ b - φ r) :=
      hLHS.symm.trans hRHS
    have h1 : ∫ x in Ioo a b, (f x - f a) * φ' x =
        (∫ x in Ioo a b, f x * φ' x) - f a * (φ b - φ a) := by
      have hsub_eq : (fun x => (f x - f a) * φ' x) = fun x => f x * φ' x - f a * φ' x := by
        ext x; ring
      rw [hsub_eq, integral_sub hfφ'_int (hφ'_int.const_mul (f a)), integral_const_mul]
      have hφ_tot : ∫ x in Ioo a b, φ' x = φ b - φ a := by
        rw [setIntegral_congr_set Ioo_ae_eq_Ioc, ← intervalIntegral.integral_of_le hab]
        exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hφ_cont hφ_deriv
          ((intervalIntegrable_iff_integrableOn_Ioo_of_le hab).mpr hφ'_int)
      rw [hφ_tot]
    have h2 : ∫ r in Ioo a b, d r * (φ b - φ r) =
        (f b - f a) * φ b - ∫ r in Ioo a b, d r * φ r := by
      have hsub_eq : (fun r => d r * (φ b - φ r)) = fun r => d r * φ b - d r * φ r := by
        ext r; ring
      rw [hsub_eq, integral_sub (hd_int.mul_const (φ b)) hdφ_int, integral_mul_const]
      have hd_tot : ∫ r in Ioo a b, d r = f b - f a := by
        rw [setIntegral_congr_set Ioo_ae_eq_Ioc, ← intervalIntegral.integral_of_le hab]
        exact subgrad_integral_eq hab hsub
      rw [hd_tot]
    rw [integral_add hdφ_int hfφ'_int]
    linarith

/-- `subgrad_ibp_of_integrable` for a `C¹` weight. -/
lemma subgrad_ibp {f d φ φ' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hsub : IsSubgradOn f d a b)
    (hφ_cont : ContinuousOn φ (Icc a b))
    (hφ'_cont : ContinuousOn φ' (Icc a b))
    (hφ_deriv : ∀ x ∈ Ioo a b, HasDerivAt φ (φ' x) x) :
    ∫ x in Ioo a b, (d x * φ x + f x * φ' x) = f b * φ b - f a * φ a :=
  subgrad_ibp_of_integrable hab hsub hφ_cont
    (hφ'_cont.integrableOn_Icc.mono_set Ioo_subset_Icc_self) hφ_deriv

end

end EconCSAuction
