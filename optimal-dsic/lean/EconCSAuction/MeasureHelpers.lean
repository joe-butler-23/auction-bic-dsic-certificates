import EconCSAuction.Spec
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-!
# Measure-Theoretic & Change-of-Variables Helpers for `v_ij = L + U_ij²`

Proves that `singleValMeasure L`, `bidderMeasure L`, and `jointMeasure L` are probability measures,
that `singleValMeasure L` has exact continuous CDF `F(v) = √(v - L)` and `L¹` density
`1 / (2 √(v - L))` on `(L, L + 1)`, and establishes the 2D density formula with
`ρ(a, b) = 1 / (4 √(a b))` plus the shear `(s + t, s)` and ray `(λ, λ η)` change-of-variables
identities using only 1D translation/scaling and Fubini.
-/

open MeasureTheory Set

namespace EconCSAuction

noncomputable section

/-- Shifted unit square `[0, 1]²`. -/
def unitSquare : Set Type2 := Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1

/-- Open unit square `(0, 1)²`. -/
def openUnitSquare : Set Type2 := Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1

/-- Joint density `ρ(a, b) = 1 / (4 √(a b))` on `(0, 1)²`. -/
def rho (a b : ℝ) : ℝ := 1 / (4 * Real.sqrt (a * b))

/-- 1D shifted density `f₁(a) = 1 / (2 √a)` on `(0, 1)`. -/
def density1D (a : ℝ) : ℝ := 1 / (2 * Real.sqrt a)

lemma measurableSet_valInterval (L : ℝ) : MeasurableSet (valInterval L) :=
  measurableSet_Icc

lemma measurableSet_openUnitSquare : MeasurableSet openUnitSquare :=
  measurableSet_Ioo.prod measurableSet_Ioo

lemma rho_nonneg (a b : ℝ) : 0 ≤ rho a b := by
  unfold rho
  positivity

lemma rho_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : 0 < rho a b := by
  unfold rho
  positivity

lemma rho_eq_mul_density1D {a b : ℝ} (ha : 0 ≤ a) (_hb : 0 ≤ b) :
    rho a b = density1D a * density1D b := by
  unfold rho density1D
  rw [Real.sqrt_mul ha]
  ring

lemma density1D_nonneg (a : ℝ) : 0 ≤ density1D a := by
  unfold density1D
  positivity

lemma volume_Icc_zero_one : volume (Icc (0 : ℝ) 1) = 1 := by
  rw [Real.volume_Icc]
  norm_num

instance isProbabilityMeasure_volume_Icc : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) :=
  ⟨by rw [Measure.restrict_apply_univ, volume_Icc_zero_one]⟩

instance isProbabilityMeasure_singleValMeasure (L : ℝ) :
    IsProbabilityMeasure (singleValMeasure L) := by
  unfold singleValMeasure
  have hm : Measurable (fun u : ℝ => L + u ^ 2) := measurable_const.add (measurable_id.pow_const 2)
  exact ⟨by rw [Measure.map_apply hm MeasurableSet.univ, preimage_univ, measure_univ]⟩

instance isProbabilityMeasure_bidderMeasure (L : ℝ) :
    IsProbabilityMeasure (bidderMeasure L) := by
  unfold bidderMeasure
  infer_instance

instance isProbabilityMeasure_jointMeasure (L : ℝ) :
    IsProbabilityMeasure (jointMeasure L) := by
  unfold jointMeasure
  infer_instance

lemma singleValMeasure_apply_valInterval (L : ℝ) :
    singleValMeasure L (valInterval L) = 1 := by
  unfold singleValMeasure
  have hm : Measurable (fun u : ℝ => L + u ^ 2) := measurable_const.add (measurable_id.pow_const 2)
  rw [Measure.map_apply hm (measurableSet_valInterval L),
      Measure.restrict_apply (hm (measurableSet_valInterval L))]
  have hsub : Icc (0 : ℝ) 1 ⊆ (fun u : ℝ => L + u ^ 2) ⁻¹' valInterval L := by
    intro u hu
    refine ⟨?_, ?_⟩
    · nlinarith [hu.1]
    · nlinarith [hu.1, hu.2]
  rw [inter_eq_right.mpr hsub, volume_Icc_zero_one]

lemma ae_mem_valInterval (L : ℝ) : ∀ᵐ v ∂(singleValMeasure L), v ∈ valInterval L := by
  rw [ae_iff]
  have h1 := measure_compl (measurableSet_valInterval L) (measure_ne_top (singleValMeasure L) _)
  rw [measure_univ, singleValMeasure_apply_valInterval] at h1
  simpa [Set.compl_def] using h1

lemma ae_mem_bidderDomain (L : ℝ) : ∀ᵐ v ∂(bidderMeasure L), v ∈ bidderDomain L := by
  unfold bidderMeasure bidderDomain
  have h1 : ∀ᵐ v : Type2 ∂((singleValMeasure L).prod (singleValMeasure L)), v.1 ∈ valInterval L :=
    QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_fst (ae_mem_valInterval L)
  have h2 : ∀ᵐ v : Type2 ∂((singleValMeasure L).prod (singleValMeasure L)), v.2 ∈ valInterval L :=
    QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_snd (ae_mem_valInterval L)
  filter_upwards [h1, h2] with v hv1 hv2
  exact ⟨hv1, hv2⟩

lemma ae_mem_profileDomain (L : ℝ) : ∀ᵐ x ∂(jointMeasure L), x ∈ profileDomain L := by
  unfold jointMeasure profileDomain
  have h1 : ∀ᵐ x : Type2 × Type2 ∂((bidderMeasure L).prod (bidderMeasure L)), x.1 ∈ bidderDomain L :=
    QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_fst (ae_mem_bidderDomain L)
  have h2 : ∀ᵐ x : Type2 × Type2 ∂((bidderMeasure L).prod (bidderMeasure L)), x.2 ∈ bidderDomain L :=
    QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_snd (ae_mem_bidderDomain L)
  filter_upwards [h1, h2] with x hx1 hx2
  exact ⟨hx1, hx2⟩

/-- Exact continuous CDF of `singleValMeasure L`: `F(v) = √(v - L)` on `[L, L + 1]`. -/
lemma singleValMeasure_Iic (L v : ℝ) (hv : v ∈ valInterval L) :
    singleValMeasure L (Iic v) = ENNReal.ofReal (Real.sqrt (v - L)) := by
  unfold singleValMeasure
  have hm : Measurable (fun u : ℝ => L + u ^ 2) := measurable_const.add (measurable_id.pow_const 2)
  rw [Measure.map_apply hm measurableSet_Iic, Measure.restrict_apply (hm measurableSet_Iic)]
  have hv0 : 0 ≤ v - L := sub_nonneg.mpr hv.1
  have hv1 : v - L ≤ 1 := by linarith [hv.2]
  have hsq1 : Real.sqrt (v - L) ≤ 1 := by
    calc Real.sqrt (v - L) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hv1
      _ = 1 := Real.sqrt_one
  have heq : (fun u : ℝ => L + u ^ 2) ⁻¹' Iic v ∩ Icc (0 : ℝ) 1 = Icc 0 (Real.sqrt (v - L)) := by
    ext u
    simp only [mem_inter_iff, mem_preimage, mem_Iic, mem_Icc]
    constructor
    · rintro ⟨hle, hu0, _⟩
      refine ⟨hu0, ?_⟩
      rw [← Real.sqrt_sq hu0]
      exact Real.sqrt_le_sqrt (by linarith)
    · rintro ⟨hu0, hule⟩
      refine ⟨?_, hu0, hule.trans hsq1⟩
      have hsq : u ^ 2 ≤ (Real.sqrt (v - L)) ^ 2 := by nlinarith [Real.sqrt_nonneg (v - L)]
      rw [Real.sq_sqrt hv0] at hsq
      linarith
  rw [heq, Real.volume_Icc, sub_zero]

/-- Integral of `1 / (2 √a)` on `(0, x)` equals `√x` for `0 ≤ x`. -/
lemma integral_density1D_Ioc {x : ℝ} (hx : 0 ≤ x) :
    ∫ a in Ioc (0 : ℝ) x, density1D a = Real.sqrt x := by
  have h1 : ∀ a ∈ Ioo (0 : ℝ) x, density1D a = (1 / 2 : ℝ) * a ^ (-(1 / 2 : ℝ)) := by
    intro a ha
    unfold density1D
    rw [Real.sqrt_eq_rpow, Real.rpow_neg ha.1.le]
    ring
  rw [← intervalIntegral.integral_of_le hx]
  have hcongr : ∫ a in (0 : ℝ)..x, density1D a = ∫ a in (0 : ℝ)..x, (1 / 2 : ℝ) * a ^ (-(1 / 2 : ℝ)) := by
    apply intervalIntegral.integral_congr_ae
    rw [ae_iff]
    have hsub : {a : ℝ | ¬ (a ∈ uIoc 0 x → density1D a = (1 / 2 : ℝ) * a ^ (-(1 / 2 : ℝ)))} ⊆ {x} := by
      intro a ha
      simp only [mem_setOf_eq, not_imp, uIoc_of_le hx] at ha
      rcases ha with ⟨⟨ha0, hax⟩, hne⟩
      by_contra hax'
      exact hne (h1 a ⟨ha0, lt_of_le_of_ne hax hax'⟩)
    exact measure_mono_null hsub (measure_singleton x)
  rw [hcongr, intervalIntegral.integral_const_mul]
  have hrp := integral_rpow (a := (0 : ℝ)) (b := x) (r := -(1 / 2 : ℝ)) (Or.inl (by norm_num))
  rw [hrp]
  have h0 : (0 : ℝ) ^ (-(1 / 2 : ℝ) + 1) = 0 := by
    rw [Real.zero_rpow (by norm_num)]
  rw [h0, sub_zero]
  have hhalf : -(1 / 2 : ℝ) + 1 = 1 / 2 := by norm_num
  rw [hhalf, ← Real.sqrt_eq_rpow]
  ring

lemma integrableOn_density1D_Ioo : IntegrableOn density1D (Ioo (0 : ℝ) 1) volume := by
  have h1 : IntegrableOn (fun a : ℝ => (1 / 2 : ℝ) * a ^ (-(1 / 2 : ℝ))) (Ioc 0 1) volume := by
    have hr := intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ)) (b := 1) (r := -(1 / 2 : ℝ)) (by norm_num)
    exact (hr.const_mul (1 / 2)).1
  have heq : IntegrableOn density1D (Ioc (0 : ℝ) 1) volume := by
    refine h1.congr_fun (fun a ha => ?_) measurableSet_Ioc
    dsimp only
    unfold density1D
    rw [Real.rpow_neg ha.1.le, ← Real.sqrt_eq_rpow]
    ring
  exact heq.mono_set Ioo_subset_Ioc_self

lemma integrableOn_rho_openUnitSquare : IntegrableOn (fun ab : Type2 => rho ab.1 ab.2) openUnitSquare volume := by
  have hprod : IntegrableOn (fun ab : Type2 => density1D ab.1 * density1D ab.2) openUnitSquare volume := by
    unfold IntegrableOn openUnitSquare
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
    exact integrableOn_density1D_Ioo.mul_prod integrableOn_density1D_Ioo
  refine hprod.congr_fun (fun ab hab => ?_) measurableSet_openUnitSquare
  exact (rho_eq_mul_density1D hab.1.1.le hab.2.1.le).symm

/-- Exact measure representation of `singleValMeasure L` via density `1 / (2 √a)` on `(0, 1)`. -/
lemma singleValMeasure_eq_map_withDensity (L : ℝ) :
    singleValMeasure L =
      Measure.map (fun a : ℝ => L + a)
        ((volume.restrict (Ioo (0 : ℝ) 1)).withDensity (fun a => ENNReal.ofReal (density1D a))) := by
  have hshift : singleValMeasure L =
      Measure.map (fun a : ℝ => L + a)
        (Measure.map (fun u : ℝ => u ^ 2) (volume.restrict (Icc (0 : ℝ) 1))) := by
    unfold singleValMeasure
    have hm1 : Measurable (fun a : ℝ => L + a) := measurable_const.add measurable_id
    have hm2 : Measurable (fun u : ℝ => u ^ 2) := measurable_id.pow_const 2
    rw [Measure.map_map hm1 hm2]
    rfl
  rw [hshift]
  congr 1
  -- Show both probability measures on `ℝ` agree on all `Iic x`.
  have hfin1 : IsFiniteMeasure (Measure.map (fun u : ℝ => u ^ 2) (volume.restrict (Icc (0 : ℝ) 1))) := by
    have : singleValMeasure 0 = Measure.map (fun u : ℝ => u ^ 2) (volume.restrict (Icc (0 : ℝ) 1)) := by
      unfold singleValMeasure; simp
    rw [← this]; infer_instance
  have hlint_Iic (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
      ∫⁻ a in Ioo (0 : ℝ) x, ENNReal.ofReal (density1D a) = ENNReal.ofReal (Real.sqrt x) := by
    have hint : IntegrableOn density1D (Ioo (0 : ℝ) x) volume :=
      integrableOn_density1D_Ioo.mono_set (Ioo_subset_Ioo_right hx1)
    rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ (fun a => density1D_nonneg a)),
        setIntegral_congr_set Ioo_ae_eq_Ioc, integral_density1D_Ioc hx0]
  have hfin2 : IsFiniteMeasure
      ((volume.restrict (Ioo (0 : ℝ) 1)).withDensity (fun a => ENNReal.ofReal (density1D a))) := by
    refine ⟨?_⟩
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hlint_Iic 1 zero_le_one le_rfl]
    simp
  apply Measure.ext_of_Iic
  intro x
  have hm0 : singleValMeasure 0 (Iic x) =
      (Measure.map (fun u : ℝ => u ^ 2) (volume.restrict (Icc (0 : ℝ) 1))) (Iic x) := by
    unfold singleValMeasure; simp
  rw [← hm0, withDensity_apply _ measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic]
  by_cases hx0 : x < 0
  · have hL : singleValMeasure 0 (Iic x) = 0 := by
      have hdisj : Disjoint (Iic x) (valInterval 0) :=
        Set.disjoint_left.mpr (fun y hy1 hy2 => by linarith [mem_Iic.mp hy1, hy2.1])
      have hle : singleValMeasure 0 (Iic x) ≤ singleValMeasure 0 (valInterval 0)ᶜ :=
        measure_mono hdisj.subset_compl_right
      have hcompl : singleValMeasure 0 (valInterval 0)ᶜ = 0 := by
        rw [measure_compl (measurableSet_valInterval 0) (measure_ne_top _ _),
            measure_univ, singleValMeasure_apply_valInterval]; simp
      exact le_antisymm (hle.trans hcompl.le) bot_le
    have hR : Iic x ∩ Ioo (0 : ℝ) 1 = ∅ := by
      ext y; simp only [mem_inter_iff, mem_Iic, mem_Ioo, mem_empty_iff_false, iff_false]
      rintro ⟨h1, h2, _⟩; linarith
    rw [hL, hR, setLIntegral_empty]
  · push Not at hx0
    by_cases hx1 : x ≤ 1
    · rw [singleValMeasure_Iic 0 x ⟨hx0, by linarith⟩, sub_zero]
      have hset_ae : (Iic x ∩ Ioo (0 : ℝ) 1 : Set ℝ) =ᵐ[volume] Ioo 0 x := by
        apply MeasureTheory.ae_eq_set.mpr
        constructor
        · have hsub : (Iic x ∩ Ioo (0 : ℝ) 1) \ Ioo 0 x ⊆ {x} := by
            intro y hy
            simp only [mem_diff, mem_inter_iff, mem_Iic, mem_Ioo, not_and, not_lt] at hy
            exact le_antisymm hy.1.1 (hy.2 hy.1.2.1)
          exact measure_mono_null hsub (measure_singleton x)
        · have hsub : Ioo (0 : ℝ) x \ (Iic x ∩ Ioo (0 : ℝ) 1) = ∅ := by
            ext y; simp only [mem_diff, mem_Ioo, mem_inter_iff, mem_Iic, mem_empty_iff_false, iff_false]
            rintro ⟨⟨hy0, hyx⟩, hnot⟩
            exact hnot ⟨hyx.le, hy0, hyx.trans_le hx1⟩
          rw [hsub]; simp
      rw [setLIntegral_congr hset_ae, hlint_Iic x hx0 hx1]
    · push Not at hx1
      have hL : singleValMeasure 0 (Iic x) = 1 := by
        have hsub : valInterval 0 ⊆ Iic x := fun y hy => by
          simp only [valInterval, mem_Icc, zero_add] at hy
          exact hy.2.trans hx1.le
        have hle := measure_mono (μ := singleValMeasure 0) hsub
        rw [singleValMeasure_apply_valInterval] at hle
        exact le_antisymm prob_le_one hle
      have hset : Iic x ∩ Ioo (0 : ℝ) 1 = Ioo 0 1 := by
        ext y; simp only [mem_inter_iff, mem_Iic, mem_Ioo]
        exact ⟨fun h => h.2, fun h => ⟨h.2.le.trans hx1.le, h⟩⟩
      rw [hL, hset, hlint_Iic 1 zero_le_one le_rfl]
      simp

/-- Exact measure representation of `bidderMeasure L` via `ρ(a, b) = 1 / (4 √(a b))` on `(0, 1)²`. -/
lemma bidderMeasure_eq_map_withDensity (L : ℝ) :
    bidderMeasure L =
      Measure.map (fun ab : Type2 => (L + ab.1, L + ab.2))
        ((volume.restrict openUnitSquare).withDensity (fun ab => ENNReal.ofReal (rho ab.1 ab.2))) := by
  unfold bidderMeasure
  rw [singleValMeasure_eq_map_withDensity L]
  have hm1 : Measurable (fun a : ℝ => L + a) := measurable_const.add measurable_id
  let μ1 : Measure ℝ := (volume.restrict (Ioo (0 : ℝ) 1)).withDensity (fun a => ENNReal.ofReal (density1D a))
  have hfin : IsFiniteMeasure μ1 := by
    refine ⟨?_⟩
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
        ← ofReal_integral_eq_lintegral_ofReal integrableOn_density1D_Ioo
          (ae_of_all _ (fun a => density1D_nonneg a)),
        setIntegral_congr_set Ioo_ae_eq_Ioc, integral_density1D_Ioc zero_le_one]
    simp
  have hprod_map : (Measure.map (fun a : ℝ => L + a) μ1).prod (Measure.map (fun a : ℝ => L + a) μ1) =
      Measure.map (Prod.map (fun a : ℝ => L + a) (fun a : ℝ => L + a)) (μ1.prod μ1) :=
    Measure.map_prod_map μ1 μ1 hm1 hm1
  change (Measure.map (fun a : ℝ => L + a) μ1).prod (Measure.map (fun a : ℝ => L + a) μ1) = _
  rw [hprod_map]
  have hpm : Prod.map (fun a : ℝ => L + a) (fun a : ℝ => L + a) = fun ab : Type2 => (L + ab.1, L + ab.2) := rfl
  rw [hpm]
  congr 1
  have hd_meas : Measurable (fun a : ℝ => ENNReal.ofReal (density1D a)) :=
    (measurable_const.div (measurable_const.mul Real.continuous_sqrt.measurable)).ennreal_ofReal
  apply Measure.prod_eq
  intro s t hs ht
  rw [withDensity_apply _ (hs.prod ht), withDensity_apply _ hs, withDensity_apply _ ht]
  unfold openUnitSquare
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.prod_restrict,
      Measure.restrict_restrict (hs.prod ht)]
  have hinter : (s ×ˢ t) ∩ (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) = (s ∩ Ioo 0 1) ×ˢ (t ∩ Ioo 0 1) :=
    Set.prod_inter_prod
  rw [hinter, ← Measure.prod_restrict]
  have hcongr : ∀ᵐ ab ∂((volume.restrict (s ∩ Ioo (0 : ℝ) 1)).prod (volume.restrict (t ∩ Ioo (0 : ℝ) 1))),
      ENNReal.ofReal (rho ab.1 ab.2) = ENNReal.ofReal (density1D ab.1) * ENNReal.ofReal (density1D ab.2) := by
    rw [Measure.prod_restrict, ae_restrict_iff' ((hs.inter measurableSet_Ioo).prod (ht.inter measurableSet_Ioo))]
    filter_upwards with ab hab
    rw [rho_eq_mul_density1D hab.1.2.1.le hab.2.2.1.le, ENNReal.ofReal_mul (density1D_nonneg ab.1)]
  rw [lintegral_congr_ae hcongr, lintegral_prod_mul hd_meas.aemeasurable hd_meas.aemeasurable]
  rw [Measure.restrict_restrict hs, Measure.restrict_restrict ht]

/-- Integrability equivalence for `bidderMeasure L` in shifted `(a, b) ∈ (0, 1)²` coordinates. -/
lemma integrable_bidderMeasure_iff {L : ℝ} {f : Type2 → ℝ}
    (hf : AEStronglyMeasurable f (bidderMeasure L)) :
    Integrable f (bidderMeasure L) ↔
      IntegrableOn (fun ab : Type2 => f (L + ab.1, L + ab.2) * rho ab.1 ab.2) openUnitSquare volume := by
  have hm : Measurable (fun ab : Type2 => (L + ab.1, L + ab.2)) :=
    (measurable_const.add measurable_fst).prodMk (measurable_const.add measurable_snd)
  have hrho_meas : Measurable (fun ab : Type2 => ENNReal.ofReal (rho ab.1 ab.2)) :=
    (measurable_const.div (measurable_const.mul
      (Real.continuous_sqrt.measurable.comp (measurable_fst.mul measurable_snd)))).ennreal_ofReal
  have hrho_lt_top : ∀ᵐ ab ∂(volume.restrict openUnitSquare),
      ENNReal.ofReal (rho ab.1 ab.2) < ⊤ :=
    ae_of_all _ (fun _ => ENNReal.ofReal_lt_top)
  rw [bidderMeasure_eq_map_withDensity L] at hf ⊢
  rw [integrable_map_measure hf hm.aemeasurable,
      integrable_withDensity_iff_integrable_smul₀' hrho_meas.aemeasurable hrho_lt_top]
  unfold IntegrableOn
  refine integrable_congr (ae_of_all _ (fun ab => ?_))
  simp only [Function.comp_apply, ENNReal.toReal_ofReal (rho_nonneg ab.1 ab.2), smul_eq_mul, mul_comm]

/-- Integral formula for `bidderMeasure L` in shifted `(a, b) ∈ (0, 1)²` coordinates. -/
lemma integral_bidderMeasure_eq {L : ℝ} {f : Type2 → ℝ}
    (hf : AEStronglyMeasurable f (bidderMeasure L)) :
    ∫ v, f v ∂(bidderMeasure L) =
      ∫ ab in openUnitSquare, f (L + ab.1, L + ab.2) * rho ab.1 ab.2 := by
  have hm : Measurable (fun ab : Type2 => (L + ab.1, L + ab.2)) :=
    (measurable_const.add measurable_fst).prodMk (measurable_const.add measurable_snd)
  have hrho_meas : Measurable (fun ab : Type2 => ENNReal.ofReal (rho ab.1 ab.2)) :=
    (measurable_const.div (measurable_const.mul
      (Real.continuous_sqrt.measurable.comp (measurable_fst.mul measurable_snd)))).ennreal_ofReal
  have hrho_lt_top : ∀ᵐ ab ∂(volume.restrict openUnitSquare),
      ENNReal.ofReal (rho ab.1 ab.2) < ⊤ :=
    ae_of_all _ (fun _ => ENNReal.ofReal_lt_top)
  rw [bidderMeasure_eq_map_withDensity L] at hf ⊢
  rw [integral_map hm.aemeasurable hf,
      integral_withDensity_eq_integral_toReal_smul₀ hrho_meas.aemeasurable hrho_lt_top]
  refine setIntegral_congr_fun measurableSet_openUnitSquare (fun ab _ => ?_)
  simp only [ENNReal.toReal_ofReal (rho_nonneg ab.1 ab.2), smul_eq_mul, mul_comm]

/-- Bounded measurable functions on `bidderDomain L` are integrable under `bidderMeasure L`. -/
lemma integrable_of_bounded_bidderMeasure {L C : ℝ} {f : Type2 → ℝ}
    (hm : AEStronglyMeasurable f (bidderMeasure L))
    (hb : ∀ v ∈ bidderDomain L, |f v| ≤ C) :
    Integrable f (bidderMeasure L) := by
  refine Integrable.of_bound hm C ?_
  filter_upwards [ae_mem_bidderDomain L] with v hv
  simpa [Real.norm_eq_abs] using hb v hv

/-- Bounded measurable functions on `profileDomain L` are integrable under `jointMeasure L`. -/
lemma integrable_of_bounded_jointMeasure {L C : ℝ} {f : Type2 × Type2 → ℝ}
    (hm : AEStronglyMeasurable f (jointMeasure L))
    (hb : ∀ x ∈ profileDomain L, |f x| ≤ C) :
    Integrable f (jointMeasure L) := by
  refine Integrable.of_bound hm C ?_
  filter_upwards [ae_mem_profileDomain L] with x hx
  simpa [Real.norm_eq_abs] using hb x hx

/-- Measurable equivalence `(t, s) ↦ (s + t, s)` (linear shear with Jacobian determinant `1`). -/
def shearEquiv : (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) where
  toFun ts := (ts.2 + ts.1, ts.2)
  invFun ab := (ab.1 - ab.2, ab.2)
  left_inv ts := by ext <;> dsimp <;> ring
  right_inv ab := by ext <;> dsimp <;> ring
  measurable_toFun := (measurable_snd.add measurable_fst).prodMk measurable_snd
  measurable_invFun := (measurable_fst.sub measurable_snd).prodMk measurable_snd

lemma measurePreserving_shearEquiv :
    MeasurePreserving shearEquiv (volume.prod volume) (volume.prod volume) := by
  have h1 : MeasurePreserving (fun st : ℝ × ℝ => (st.1, st.1 + st.2))
      (volume.prod volume) (volume.prod volume) := by
    have hmeas_s : Measurable (fun st : ℝ × ℝ => (st.1, st.1 + st.2)) :=
      measurable_fst.prodMk (measurable_fst.add measurable_snd)
    constructor
    · exact hmeas_s
    · symm
      apply Measure.prod_eq
      intro s t hs ht
      rw [Measure.map_apply hmeas_s (hs.prod ht)]
      rw [Measure.prod_apply (hmeas_s (hs.prod ht))]
      have hslice : ∀ x : ℝ,
          volume (Prod.mk x ⁻¹' ((fun st : ℝ × ℝ => (st.1, st.1 + st.2)) ⁻¹' (s ×ˢ t))) =
            s.indicator (fun _ => volume t) x := by
        intro x
        by_cases hx : x ∈ s
        · rw [indicator_of_mem hx]
          have heq : Prod.mk x ⁻¹' ((fun st : ℝ × ℝ => (st.1, st.1 + st.2)) ⁻¹' (s ×ˢ t)) =
              (fun y => x + y) ⁻¹' t := by
            ext y; simp [hx]
          rw [heq, measure_preimage_add]
        · rw [indicator_of_notMem hx]
          have heq : Prod.mk x ⁻¹' ((fun st : ℝ × ℝ => (st.1, st.1 + st.2)) ⁻¹' (s ×ˢ t)) = ∅ := by
            ext y; simp [hx]
          rw [heq, measure_empty]
      simp_rw [hslice]
      rw [lintegral_indicator_const hs, mul_comm]
  have hcomp := (Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))).comp
    (h1.comp (Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))))
  simpa [shearEquiv, Function.comp_def, add_comm] using hcomp

/-- Shear change of variables on a trapezoid `{(a, b) ∈ (0, 1)² | t₁ < a - b < t₂}`:
`∫_{(a,b)} f(a, b) = ∫ t ∈ (t₁, t₂), ∫ s ∈ (0, 1 - t), f(s + t, s)` (using only 1D translation + Fubini). -/
lemma setIntegral_shear_upper {t1 t2 : ℝ} (ht1 : 0 ≤ t1) (_ht12 : t1 ≤ t2) (_ht2 : t2 ≤ 1)
    {f : Type2 → ℝ}
    (hf : IntegrableOn f {ab : Type2 | ab ∈ openUnitSquare ∧ t1 < ab.1 - ab.2 ∧ ab.1 - ab.2 < t2} volume) :
    ∫ ab in {ab : Type2 | ab ∈ openUnitSquare ∧ t1 < ab.1 - ab.2 ∧ ab.1 - ab.2 < t2}, f ab =
      ∫ t in Ioo t1 t2, ∫ s in Ioo (0 : ℝ) (1 - t), f (s + t, s) := by
  let A : Set Type2 := openUnitSquare ∩ ({ab : Type2 | t1 < ab.1 - ab.2} ∩ {ab : Type2 | ab.1 - ab.2 < t2})
  have hA_eq : {ab : Type2 | ab ∈ openUnitSquare ∧ t1 < ab.1 - ab.2 ∧ ab.1 - ab.2 < t2} = A := rfl
  have hA_meas : MeasurableSet A :=
    measurableSet_openUnitSquare.inter
      ((measurableSet_lt measurable_const (measurable_fst.sub measurable_snd)).inter
       (measurableSet_lt (measurable_fst.sub measurable_snd) measurable_const))
  rw [hA_eq] at hf ⊢
  have hInd_int : Integrable (A.indicator f) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact (integrable_indicator_iff hA_meas).mpr hf
  let B : Set (ℝ × ℝ) := {ts : ℝ × ℝ | ts.1 ∈ Ioo t1 t2} ∩
    ({ts : ℝ × ℝ | (0 : ℝ) < ts.2} ∩ {ts : ℝ × ℝ | ts.2 < 1 - ts.1})
  have hpre : (shearEquiv : ℝ × ℝ → ℝ × ℝ) ⁻¹' A = B := by
    ext ⟨t, s⟩
    simp only [A, B, shearEquiv, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk, openUnitSquare,
      mem_preimage, mem_inter_iff, mem_ofPred_eq, mem_prod, mem_Ioo]
    constructor
    · rintro ⟨⟨⟨ha0, ha1⟩, ⟨hb0, hb1⟩⟩, h1, h2⟩
      refine ⟨⟨by linarith, by linarith⟩, ⟨hb0, by linarith⟩⟩
    · rintro ⟨⟨ht1', ht2'⟩, ⟨hs0, hs1⟩⟩
      refine ⟨⟨⟨by linarith, by linarith⟩, ⟨hs0, by linarith⟩⟩, by linarith, by linarith⟩
  have hInd_comp : (fun ts : ℝ × ℝ => A.indicator f (shearEquiv ts)) =
      B.indicator (fun ts : ℝ × ℝ => f (ts.2 + ts.1, ts.2)) := by
    ext ts
    by_cases h : ts ∈ B
    · have ha : shearEquiv ts ∈ A := by rwa [← mem_preimage, hpre]
      rw [indicator_of_mem ha, indicator_of_mem h]; rfl
    · have ha : shearEquiv ts ∉ A := by rwa [← mem_preimage, hpre]
      rw [indicator_of_notMem ha, indicator_of_notMem h]
  have hB_int : Integrable (B.indicator (fun ts : ℝ × ℝ => f (ts.2 + ts.1, ts.2))) (volume.prod volume) := by
    rw [← hInd_comp]
    exact measurePreserving_shearEquiv.integrable_comp_of_integrable hInd_int
  have hEq : ∫ ab in A, f ab =
      ∫ ts, B.indicator (fun ts : ℝ × ℝ => f (ts.2 + ts.1, ts.2)) ts ∂(volume.prod volume) := by
    rw [← integral_indicator hA_meas, Measure.volume_eq_prod,
        ← measurePreserving_shearEquiv.integral_comp' (g := A.indicator f)]
    congr 1
  rw [hEq, integral_prod _ hB_int, ← integral_indicator measurableSet_Ioo]
  congr 1
  ext t
  by_cases ht : t ∈ Ioo t1 t2
  · simp only [indicator_of_mem ht]
    rw [← integral_indicator measurableSet_Ioo]
    congr 1
    ext s
    by_cases hs : s ∈ Ioo (0 : ℝ) (1 - t)
    · have hts : (t, s) ∈ B := ⟨ht, hs.1, hs.2⟩
      simp [hts, hs]
    · have hts : (t, s) ∉ B := fun h => hs ⟨h.2.1, h.2.2⟩
      simp [hts, hs]
  · simp only [indicator_of_notMem ht]
    have hzero : ∀ s : ℝ, B.indicator (fun ts : ℝ × ℝ => f (ts.2 + ts.1, ts.2)) (t, s) = 0 := by
      intro s
      have hts : (t, s) ∉ B := fun h => ht h.1
      simp [hts]
    simp [hzero]

/-- Ray change of variables `(a, b) = (λ, λ η)` on a region below the diagonal that is star-shaped
about the origin, `{(a, b) ∈ (0, 1)² | b < a ∧ a < Λ(b / a)}` with `Λ ≤ 1`, using only 1D scaling
and Fubini:
`∫ D(a, b) ρ(a, b) = ∫ η ∈ (0, 1), (1 / (4 √η)) * ∫ λ ∈ (0, Λ η), D(λ, λ η)`. -/
lemma setIntegral_ray_region {Λ : ℝ → ℝ} (hΛm : Measurable Λ)
    (hΛ1 : ∀ η ∈ Ioo (0 : ℝ) 1, Λ η ≤ 1)
    {D : Type2 → ℝ} (hDm : Measurable D)
    (hD : IntegrableOn (fun ab : Type2 => D ab * rho ab.1 ab.2)
      {ab : Type2 | ab ∈ openUnitSquare ∧ ab.2 < ab.1 ∧ ab.1 < Λ (ab.2 / ab.1)} volume) :
    ∫ ab in {ab : Type2 | ab ∈ openUnitSquare ∧ ab.2 < ab.1 ∧ ab.1 < Λ (ab.2 / ab.1)},
        D ab * rho ab.1 ab.2 =
      ∫ η in Ioo (0 : ℝ) 1, (1 / (4 * Real.sqrt η)) *
        ∫ lam in Ioo (0 : ℝ) (Λ η), D (lam, lam * η) := by
  let Tc : Set Type2 := openUnitSquare ∩ ({ab : Type2 | ab.2 < ab.1} ∩ {ab : Type2 | ab.1 < Λ (ab.2 / ab.1)})
  have hTc_eq : {ab : Type2 | ab ∈ openUnitSquare ∧ ab.2 < ab.1 ∧ ab.1 < Λ (ab.2 / ab.1)} = Tc := rfl
  have hTc_meas : MeasurableSet Tc :=
    measurableSet_openUnitSquare.inter
      ((measurableSet_lt measurable_snd measurable_fst).inter
       (measurableSet_lt measurable_fst (hΛm.comp (measurable_snd.div measurable_fst))))
  rw [hTc_eq] at hD ⊢
  have hInd_int : Integrable (Tc.indicator (fun ab : Type2 => D ab * rho ab.1 ab.2)) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact (integrable_indicator_iff hTc_meas).mpr hD
  let R : Set (ℝ × ℝ) :=
    ({p : ℝ × ℝ | (0 : ℝ) < p.2} ∩ {p : ℝ × ℝ | p.2 < 1}) ∩
    ({p : ℝ × ℝ | (0 : ℝ) < p.1} ∩ {p : ℝ × ℝ | p.1 < Λ p.2})
  have hR_meas : MeasurableSet R :=
    ((measurableSet_lt measurable_const measurable_snd).inter (measurableSet_lt measurable_snd measurable_const)).inter
      ((measurableSet_lt measurable_const measurable_fst).inter
       (measurableSet_lt measurable_fst (hΛm.comp measurable_snd)))
  have hmem_iff : ∀ lam η : ℝ, (lam, η) ∈ R ↔ (lam, lam * η) ∈ Tc := by
    intro lam η
    simp only [R, Tc, openUnitSquare, mem_inter_iff, mem_ofPred_eq, mem_prod, mem_Ioo]
    constructor
    · rintro ⟨⟨hη0, hη1⟩, ⟨hlam0, hlamc⟩⟩
      have hlam1 : lam < 1 := lt_of_lt_of_le hlamc (hΛ1 η ⟨hη0, hη1⟩)
      have hb0 : 0 < lam * η := mul_pos hlam0 hη0
      have hba : lam * η < lam := by nlinarith
      have hb1 : lam * η < 1 := by linarith
      have hq : lam * η / lam = η := by field_simp
      exact ⟨⟨⟨hlam0, hlam1⟩, ⟨hb0, hb1⟩⟩, hba, by rw [hq]; exact hlamc⟩
    · rintro ⟨⟨⟨hlam0, _⟩, ⟨hb0, _⟩⟩, hba, hlamc⟩
      have hη0 : 0 < η := by nlinarith
      have hη1 : η < 1 := by nlinarith
      have hq : lam * η / lam = η := by field_simp
      rw [hq] at hlamc
      exact ⟨⟨hη0, hη1⟩, hlam0, hlamc⟩
  have hF_meas : Measurable
      (R.indicator (fun p : ℝ × ℝ => D (p.1, p.1 * p.2) * (1 / (4 * Real.sqrt p.2)))) :=
    ((hDm.comp (measurable_fst.prodMk (measurable_fst.mul measurable_snd))).mul
      (measurable_const.div (measurable_const.mul (Real.continuous_sqrt.measurable.comp measurable_snd)))).indicator
      hR_meas
  have hF_int : Integrable
      (R.indicator (fun p : ℝ × ℝ => D (p.1, p.1 * p.2) * (1 / (4 * Real.sqrt p.2))))
      (volume.prod volume) := by
    refine ⟨hF_meas.aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral, lintegral_prod _ hF_meas.eNorm.aemeasurable]
    have hTc_fin : ∫⁻ ab, ‖Tc.indicator (fun ab : Type2 => D ab * rho ab.1 ab.2) ab‖ₑ ∂(volume.prod volume) < ⊤ :=
      hInd_int.2
    rw [lintegral_prod _ hInd_int.aestronglyMeasurable.enorm] at hTc_fin
    refine lt_of_le_of_lt (le_of_eq ?_) hTc_fin
    refine lintegral_congr (fun lam => ?_)
    by_cases hlam : 0 < lam ∧ lam < 1
    · have hm_mul : Measurable (fun η : ℝ => lam * η) := measurable_const.mul measurable_id
      have h1 : ENNReal.ofReal lam *
          ∫⁻ η, ‖Tc.indicator (fun ab : Type2 => D ab * rho ab.1 ab.2) (lam, lam * η)‖ₑ =
          ∫⁻ b, ‖Tc.indicator (fun ab : Type2 => D ab * rho ab.1 ab.2) (lam, b)‖ₑ := by
        have hmap : Measure.map (fun η : ℝ => lam * η) volume = ENNReal.ofReal lam⁻¹ • (volume : Measure ℝ) := by
          ext s hs
          rw [Measure.map_apply hm_mul hs, Measure.smul_apply, smul_eq_mul,
              Real.volume_preimage_mul_left hlam.1.ne', abs_of_pos (inv_pos.mpr hlam.1)]
        have hmeas_b : Measurable (fun b : ℝ => ‖Tc.indicator (fun ab : Type2 => D ab * rho ab.1 ab.2) (lam, b)‖ₑ) :=
          (((hDm.mul (measurable_const.div (measurable_const.mul
            (Real.continuous_sqrt.measurable.comp (measurable_fst.mul measurable_snd))))).indicator hTc_meas).comp
            (measurable_const.prodMk measurable_id)).eNorm
        have hlm := lintegral_map (μ := (volume : Measure ℝ)) hmeas_b hm_mul
        rw [hmap, lintegral_smul_measure, smul_eq_mul] at hlm
        rw [← hlm, ← mul_assoc, ← ENNReal.ofReal_mul hlam.1.le, mul_inv_cancel₀ hlam.1.ne',
            ENNReal.ofReal_one, one_mul]
      rw [← h1, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_congr (fun η => ?_)
      by_cases hη : (lam, η) ∈ R
      · have hTc_mem : (lam, lam * η) ∈ Tc := (hmem_iff lam η).mp hη
        simp only [indicator_of_mem hη, indicator_of_mem hTc_mem]
        have hlam0 := hlam.1
        have hη0 : 0 < η := hη.1.1
        have hrho_eq : lam * rho lam (lam * η) = 1 / (4 * Real.sqrt η) := by
          unfold rho
          have hsq : Real.sqrt (lam * (lam * η)) = lam * Real.sqrt η := by
            rw [← mul_assoc, Real.sqrt_mul (mul_nonneg hlam0.le hlam0.le), Real.sqrt_mul_self hlam0.le]
          rw [hsq]; field_simp [hlam0.ne', (Real.sqrt_pos.mpr hη0).ne']
        rw [← Real.eNorm_of_nonneg hlam0.le, ← eNorm_mul]
        congr 1
        calc D (lam, lam * η) * (1 / (4 * Real.sqrt η))
            = D (lam, lam * η) * (lam * rho lam (lam * η)) := by rw [hrho_eq]
          _ = lam * (D (lam, lam * η) * rho lam (lam * η)) := by ring
      · have hTc_not : (lam, lam * η) ∉ Tc := fun hm => hη ((hmem_iff lam η).mpr hm)
        simp [hη, hTc_not]
    · have hzero1 : ∀ η, R.indicator (fun p : ℝ × ℝ => D (p.1, p.1 * p.2) * (1 / (4 * Real.sqrt p.2))) (lam, η) = 0 := by
        intro η
        have hnot : (lam, η) ∉ R := by
          intro hR
          simp only [R, mem_inter_iff, mem_ofPred_eq] at hR
          apply hlam
          exact ⟨hR.2.1, lt_of_lt_of_le hR.2.2 (hΛ1 η ⟨hR.1.1, hR.1.2⟩)⟩
        simp [hnot]
      have hzero2 : ∀ b, Tc.indicator (fun ab : Type2 => D ab * rho ab.1 ab.2) (lam, b) = 0 := by
        intro b
        have hnot : (lam, b) ∉ Tc := by
          intro hT
          simp only [Tc, openUnitSquare, mem_inter_iff, mem_ofPred_eq, mem_prod, mem_Ioo] at hT
          apply hlam
          exact ⟨hT.1.1.1, hT.1.1.2⟩
        simp [hnot]
      simp_rw [hzero1, hzero2]
  rw [← integral_indicator hTc_meas, Measure.volume_eq_prod, integral_prod _ hInd_int]
  have hstep : (∫ lam, ∫ b, Tc.indicator (fun ab : Type2 => D ab * rho ab.1 ab.2) (lam, b)) =
      ∫ lam, ∫ η, R.indicator (fun p : ℝ × ℝ => D (p.1, p.1 * p.2) * (1 / (4 * Real.sqrt p.2))) (lam, η) := by
    refine integral_congr_ae (ae_of_all _ (fun lam => ?_))
    dsimp only
    by_cases hlam : 0 < lam ∧ lam < 1
    · have hcomp := Measure.integral_comp_mul_left
        (fun b : ℝ => Tc.indicator (fun ab : Type2 => D ab * rho ab.1 ab.2) (lam, b)) lam
      have h1 : ∫ b, Tc.indicator (fun ab : Type2 => D ab * rho ab.1 ab.2) (lam, b) =
          lam * ∫ η, Tc.indicator (fun ab : Type2 => D ab * rho ab.1 ab.2) (lam, lam * η) := by
        rw [hcomp, abs_of_pos (inv_pos.mpr hlam.1), smul_eq_mul, ← mul_assoc,
            mul_inv_cancel₀ hlam.1.ne', one_mul]
      rw [h1, ← integral_const_mul]
      refine integral_congr_ae (ae_of_all _ (fun η => ?_))
      dsimp only
      by_cases hη : (lam, η) ∈ R
      · have hTc_mem : (lam, lam * η) ∈ Tc := (hmem_iff lam η).mp hη
        simp only [indicator_of_mem hη, indicator_of_mem hTc_mem]
        have hlam0 := hlam.1
        have hη0 : 0 < η := hη.1.1
        have hrho_eq : lam * rho lam (lam * η) = 1 / (4 * Real.sqrt η) := by
          unfold rho
          have hsq : Real.sqrt (lam * (lam * η)) = lam * Real.sqrt η := by
            rw [← mul_assoc, Real.sqrt_mul (mul_nonneg hlam0.le hlam0.le), Real.sqrt_mul_self hlam0.le]
          rw [hsq]; field_simp [hlam0.ne', (Real.sqrt_pos.mpr hη0).ne']
        calc lam * (D (lam, lam * η) * rho lam (lam * η))
            = D (lam, lam * η) * (lam * rho lam (lam * η)) := by ring
          _ = D (lam, lam * η) * (1 / (4 * Real.sqrt η)) := by rw [hrho_eq]
      · have hTc_not : (lam, lam * η) ∉ Tc := fun hm => hη ((hmem_iff lam η).mpr hm)
        simp [hη, hTc_not]
    · have hzero1 : ∀ η, R.indicator (fun p : ℝ × ℝ => D (p.1, p.1 * p.2) * (1 / (4 * Real.sqrt p.2))) (lam, η) = 0 := by
        intro η
        have hnot : (lam, η) ∉ R := by
          intro hR
          simp only [R, mem_inter_iff, mem_ofPred_eq] at hR
          apply hlam
          exact ⟨hR.2.1, lt_of_lt_of_le hR.2.2 (hΛ1 η ⟨hR.1.1, hR.1.2⟩)⟩
        simp [hnot]
      have hzero2 : ∀ b, Tc.indicator (fun ab : Type2 => D ab * rho ab.1 ab.2) (lam, b) = 0 := by
        intro b
        have hnot : (lam, b) ∉ Tc := by
          intro hT
          simp only [Tc, openUnitSquare, mem_inter_iff, mem_ofPred_eq, mem_prod, mem_Ioo] at hT
          apply hlam
          exact ⟨hT.1.1.1, hT.1.1.2⟩
        simp [hnot]
      simp_rw [hzero1, hzero2]
  rw [hstep, ← integral_prod _ hF_int, integral_prod_symm _ hF_int, ← integral_indicator measurableSet_Ioo]
  congr 1
  ext η
  by_cases hη : η ∈ Ioo (0 : ℝ) 1
  · simp only [indicator_of_mem hη]
    rw [← integral_const_mul, ← integral_indicator measurableSet_Ioo]
    congr 1
    ext lam
    by_cases hlam : lam ∈ Ioo (0 : ℝ) (Λ η)
    · have hp : (lam, η) ∈ R := ⟨⟨hη.1, hη.2⟩, ⟨hlam.1, hlam.2⟩⟩
      simp only [indicator_of_mem hp, indicator_of_mem hlam, mul_comm]
    · have hp : (lam, η) ∉ R := fun h => hlam ⟨h.2.1, h.2.2⟩
      simp [hp, hlam]
  · simp only [indicator_of_notMem hη]
    have hzero : ∀ lam, R.indicator (fun p : ℝ × ℝ => D (p.1, p.1 * p.2) * (1 / (4 * Real.sqrt p.2))) (lam, η) = 0 := by
      intro lam
      have hp : (lam, η) ∉ R := fun h => hη ⟨h.1.1, h.1.2⟩
      simp [hp]
    simp_rw [hzero]; simp


/-- The corner triangle `T_c = {(a, b) ∈ (0, 1)² | b < a ∧ a + b < c}`, `c ∈ (0, 1]`, as a special
case of `setIntegral_ray_region` with `Λ η = c / (1 + η)`. -/
lemma setIntegral_ray_triangle {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1)
    {D : Type2 → ℝ} (hDm : Measurable D)
    (hD : IntegrableOn (fun ab : Type2 => D ab * rho ab.1 ab.2)
      {ab : Type2 | ab ∈ openUnitSquare ∧ ab.2 < ab.1 ∧ ab.1 + ab.2 < c} volume) :
    ∫ ab in {ab : Type2 | ab ∈ openUnitSquare ∧ ab.2 < ab.1 ∧ ab.1 + ab.2 < c},
        D ab * rho ab.1 ab.2 =
      ∫ η in Ioo (0 : ℝ) 1, (1 / (4 * Real.sqrt η)) *
        ∫ lam in Ioo (0 : ℝ) (c / (1 + η)), D (lam, lam * η) := by
  have hset : {ab : Type2 | ab ∈ openUnitSquare ∧ ab.2 < ab.1 ∧ ab.1 + ab.2 < c} =
      {ab : Type2 | ab ∈ openUnitSquare ∧ ab.2 < ab.1 ∧ ab.1 < c / (1 + ab.2 / ab.1)} := by
    ext ab
    have key : ab ∈ openUnitSquare → (ab.1 + ab.2 < c ↔ ab.1 < c / (1 + ab.2 / ab.1)) := by
      intro hsq
      have ha : 0 < ab.1 := hsq.1.1
      have h1 : 0 < 1 + ab.2 / ab.1 := by have := div_pos hsq.2.1 ha; linarith
      have he : ab.1 * (1 + ab.2 / ab.1) = ab.1 + ab.2 := by field_simp
      rw [lt_div_iff₀ h1, he]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, (key h1).mp h3⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, (key h1).mpr h3⟩
  rw [hset] at hD ⊢
  exact setIntegral_ray_region (Λ := fun η => c / (1 + η))
    (measurable_const.div (measurable_const.add measurable_id))
    (fun η hη => (div_le_one (by linarith [hη.1])).mpr (by linarith [hη.1])) hDm hD

/-- Any diagonal line `{ab | ab.1 - ab.2 = c}` has 2D Lebesgue measure zero. -/
lemma volume_diff_eq_const_zero (c : ℝ) : volume {ab : Type2 | ab.1 - ab.2 = c} = 0 := by
  have hm : MeasurableSet {ab : Type2 | ab.1 - ab.2 = c} :=
    measurableSet_eq_fun (measurable_fst.sub measurable_snd) measurable_const
  rw [Measure.volume_eq_prod, Measure.prod_apply hm]
  have h0 : ∀ x : ℝ, volume (Prod.mk x ⁻¹' {ab : Type2 | ab.1 - ab.2 = c}) = 0 := by
    intro x
    have : Prod.mk x ⁻¹' {ab : Type2 | ab.1 - ab.2 = c} = {x - c} := by
      ext y; simp; constructor <;> intro h <;> linarith
    rw [this, measure_singleton]
  simp_rw [h0]; simp

/-- Item swap `(v₁, v₂) ↦ (v₂, v₁)` preserves `bidderMeasure L`. -/
lemma measurePreserving_swap_bidderMeasure (L : ℝ) :
    MeasurePreserving Prod.swap (bidderMeasure L) (bidderMeasure L) :=
  Measure.measurePreserving_swap

/-- Profile involution `σ(b₁, b₂) = ((b₂.2, b₂.1), (b₁.2, b₁.1))` swapping bidders and items. -/
def swapProfileEquiv : (Type2 × Type2) ≃ᵐ (Type2 × Type2) :=
  MeasurableEquiv.prodComm.trans
    (MeasurableEquiv.prodCongr MeasurableEquiv.prodComm MeasurableEquiv.prodComm)

lemma measurePreserving_swapProfile (L : ℝ) :
    MeasurePreserving swapProfileEquiv (jointMeasure L) (jointMeasure L) := by
  unfold swapProfileEquiv jointMeasure
  have h1 : MeasurePreserving (MeasurableEquiv.prodComm : Type2 × Type2 → Type2 × Type2)
      ((bidderMeasure L).prod (bidderMeasure L)) ((bidderMeasure L).prod (bidderMeasure L)) :=
    Measure.measurePreserving_swap
  have h2 : MeasurePreserving (Prod.map Prod.swap Prod.swap : Type2 × Type2 → Type2 × Type2)
      ((bidderMeasure L).prod (bidderMeasure L)) ((bidderMeasure L).prod (bidderMeasure L)) :=
    (measurePreserving_swap_bidderMeasure L).prod (measurePreserving_swap_bidderMeasure L)
  exact h2.comp h1

lemma integral_swapProfile (L : ℝ) (f : Type2 × Type2 → ℝ) :
    ∫ x, f ((x.2.2, x.2.1), (x.1.2, x.1.1)) ∂(jointMeasure L) = ∫ x, f x ∂(jointMeasure L) :=
  (measurePreserving_swapProfile L).integral_comp swapProfileEquiv.measurableEmbedding f

end

end EconCSAuction
