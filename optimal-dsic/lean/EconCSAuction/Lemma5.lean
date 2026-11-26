import EconCSAuction.Lemma4

/-!
# Lemma 5 (part 1): exact reduction of the strip functional

For an arbitrary `P : InterimProfile` (non-smooth convex interim utility `(u, g₁, g₂)` on `[0, 1]²`
with `u ≥ 0`, `g₁, g₂ ≥ 0`, `g₁ + g₂ ≤ 1` and BIC subgradients) this file proves:
1. exact equality `stripFunctional L P = M1 L` for linear `u(a, b) = c a + (1 - c) b`;
2. symmetrization `P.symm` and the `u(0, 0) = 0` shift `P.shiftZero`;
3. the radial identity on `S_+`, by an exact 1D identity along each ray through the origin
   (`subgrad_ibp` + the ray change of variables `setIntegral_ray_region`); no truncation or limit;
4. the exact half-strip identity `lemma5_half_strip_eq` for `w = (a + b)/2 - u` and the deficit
   `D = 1 - (g₁ + g₂)`.

The bound `stripFunctional L P ≤ M1 L` for every `L ≥ 2/π` is proved in `Lemma5Sharp.lean`.
-/

open MeasureTheory Set Filter Topology

namespace EconCSAuction

noncomputable section

/-- Optimal strip functional benchmark `M₁(L) = L ∫_S ρ - ∫_0^{1-t₀} (2s + t₀) t₀ ρ(s + t₀, s) ds`. -/
def M1 (L : ℝ) : ℝ :=
  L * (∫ ab in stripSet, rho ab.1 ab.2) -
    ∫ s in Ioo (0 : ℝ) (1 - t0), (2 * s + t0) * (t0 * rho (s + t0) s)

/-- Canonical linear half-profile `u⋆(a, b) = (a + b) / 2`, `g₁ = g₂ = 1/2`. -/
def linearHalfProfile : InterimProfile where
  u ab := (ab.1 + ab.2) / 2
  g1 _ := 1 / 2
  g2 _ := 1 / 2
  u_nonneg ab hab := by linarith [hab.1.1, hab.2.1]
  g1_nonneg _ _ := by norm_num
  g2_nonneg _ _ := by norm_num
  g_sum_le _ _ := by norm_num
  bic ab _ ab' _ := by linarith
  g1_meas := measurable_const
  g2_meas := measurable_const

/-! ### Step 1: Exact Equality for Any Linear Profile `u_c(a, b) = c a + (1 - c) b` on `S` -/

lemma stripFunctional_eq_M1_of_linear (L c : ℝ) (P : InterimProfile)
    (hu : ∀ ab ∈ stripSet, P.u ab = c * ab.1 + (1 - c) * ab.2)
    (hg1 : ∀ ab ∈ stripSet, P.g1 ab = c)
    (hg2 : ∀ ab ∈ stripSet, P.g2 ab = 1 - c)
    (hbdy : ∀ s ∈ Ioo (0 : ℝ) (1 - t0), P.u (s + t0, s) + P.u (s, s + t0) = 2 * s + t0) :
    stripFunctional L P = M1 L := by
  unfold stripFunctional M1
  congr 1
  · rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_stripSet (fun ab hab => ?_)
    rw [hu ab hab, hg1 ab hab, hg2 ab hab]
    ring
  · refine setIntegral_congr_fun measurableSet_Ioo (fun s hs => ?_)
    rw [hbdy s hs]

lemma stripFunctional_linearHalf (L : ℝ) : stripFunctional L linearHalfProfile = M1 L :=
  stripFunctional_eq_M1_of_linear L (1 / 2) linearHalfProfile
    (fun _ _ => by dsimp [linearHalfProfile]; ring)
    (fun _ _ => rfl)
    (fun _ _ => by dsimp [linearHalfProfile]; ring)
    (fun _ _ => by dsimp [linearHalfProfile]; ring)

/-! ### Step 2: Symmetrization and `u(0, 0) = 0` Shift Reduction -/

lemma integrableOn_rho_stripSet :
    IntegrableOn (fun ab : Type2 => rho ab.1 ab.2) stripSet volume :=
  integrableOn_rho_openUnitSquare.mono_set Set.inter_subset_left

lemma integrableOn_rho_stripPos :
    IntegrableOn (fun ab : Type2 => rho ab.1 ab.2) stripPos volume :=
  integrableOn_rho_openUnitSquare.mono_set Set.inter_subset_left

lemma integrableOn_shear_stripPos {f : Type2 → ℝ} (hf : IntegrableOn f stripPos volume) :
    IntegrableOn (fun t : ℝ => ∫ s in Ioo (0 : ℝ) (1 - t), f (s + t, s)) (Ioo (0 : ℝ) t0) volume := by
  let B : Set (ℝ × ℝ) := {ts : ℝ × ℝ | ts.1 ∈ Ioo (0 : ℝ) t0} ∩
    ({ts : ℝ × ℝ | (0 : ℝ) < ts.2} ∩ {ts : ℝ × ℝ | ts.2 < 1 - ts.1})
  have hpre : (shearEquiv : ℝ × ℝ → ℝ × ℝ) ⁻¹' stripPos = B := by
    ext ⟨t, s⟩
    simp only [stripPos, B, shearEquiv, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk,
      openUnitSquare, mem_preimage, mem_inter_iff, mem_ofPred_eq, mem_prod, mem_Ioo]
    constructor
    · rintro ⟨⟨⟨ha0, ha1⟩, ⟨hb0, hb1⟩⟩, h1, h2⟩; exact ⟨⟨by linarith, by linarith⟩, ⟨hb0, by linarith⟩⟩
    · rintro ⟨⟨ht1, ht2⟩, ⟨hs0, hs1⟩⟩; exact ⟨⟨⟨by linarith, by linarith⟩, ⟨hs0, by linarith⟩⟩, by linarith, by linarith⟩
  have hB_int : Integrable (B.indicator (fun ts : ℝ × ℝ => f (ts.2 + ts.1, ts.2)))
      (volume.prod volume) := by
    have hi := (integrable_indicator_iff measurableSet_stripPos).mpr hf
    rw [Measure.volume_eq_prod] at hi
    refine ((measurePreserving_shearEquiv.integrable_comp_emb shearEquiv.measurableEmbedding).mpr hi).congr
      (ae_of_all _ (fun ⟨t, s⟩ => ?_))
    have hmem : (t, s) ∈ B ↔ (s + t, s) ∈ stripPos := by
      have := Set.ext_iff.mp hpre (t, s)
      simpa [shearEquiv] using this.symm
    dsimp only [Function.comp_apply, shearEquiv, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk]
    by_cases h : (t, s) ∈ B
    · rw [indicator_of_mem (hmem.mp h), indicator_of_mem h]
    · rw [indicator_of_notMem (fun ha => h (hmem.mpr ha)), indicator_of_notMem h]
  have hmarg : IntegrableOn (fun t : ℝ => ∫ s, B.indicator (fun ts : ℝ × ℝ => f (ts.2 + ts.1, ts.2)) (t, s))
      (Ioo (0 : ℝ) t0) volume :=
    hB_int.integral_prod_left.integrableOn (s := Ioo (0 : ℝ) t0)
  refine hmarg.congr_fun (fun t ht => ?_) measurableSet_Ioo
  rw [← integral_indicator measurableSet_Ioo]
  refine integral_congr_ae (ae_of_all _ fun s => ?_)
  dsimp only
  by_cases hs : s ∈ Ioo (0 : ℝ) (1 - t)
  · have hts : (t, s) ∈ B := ⟨ht, hs.1, hs.2⟩
    rw [indicator_of_mem hts, indicator_of_mem hs]
  · have hts : (t, s) ∉ B := fun h => hs ⟨h.2.1, h.2.2⟩
    rw [indicator_of_notMem hts, indicator_of_notMem hs]

lemma integrableOn_strip_integrand (L : ℝ) (P : InterimProfile) :
    IntegrableOn (fun ab : Type2 => ((L + ab.1) * P.g1 ab + (L + ab.2) * P.g2 ab - P.u ab) * rho ab.1 ab.2)
      stripSet volume := by
  let Umax : ℝ := P.u (0, 0) + 1
  have hdom : IntegrableOn (fun ab : Type2 => (|L| + 1 + Umax) * rho ab.1 ab.2) stripSet volume :=
    integrableOn_rho_stripSet.const_mul (|L| + 1 + Umax)
  have hmeas : AEStronglyMeasurable
      (fun ab : Type2 => ((L + ab.1) * P.g1 ab + (L + ab.2) * P.g2 ab - P.u ab) * rho ab.1 ab.2)
      (volume.restrict stripSet) := by
    have hm1 : Measurable (fun ab : Type2 => (L + ab.1) * P.g1 ab + (L + ab.2) * P.g2 ab) :=
      ((measurable_const.add measurable_fst).mul P.g1_meas).add
        ((measurable_const.add measurable_snd).mul P.g2_meas)
    have hmu : AEStronglyMeasurable P.u (volume.restrict stripSet) :=
      P.u_aestronglyMeasurable.mono_measure (Measure.restrict_mono Set.inter_subset_left le_rfl)
    exact (hm1.aestronglyMeasurable.sub hmu).mul (by unfold rho; fun_prop : Measurable _).aestronglyMeasurable
  refine hdom.mono' hmeas ?_
  rw [ae_restrict_iff' measurableSet_stripSet]
  filter_upwards with ab hab
  have hsq : ab ∈ unitSquare := ⟨Ioo_subset_Icc_self hab.1.1, Ioo_subset_Icc_self hab.1.2⟩
  have hg1 := P.g1_nonneg ab hsq; have hg2 := P.g2_nonneg ab hsq; have hgs := P.g_sum_le ab hsq
  have hu_nn := P.u_nonneg ab hsq; have hu_le : P.u ab ≤ Umax := P.u_le_bound hsq
  have hval : |(L + ab.1) * P.g1 ab + (L + ab.2) * P.g2 ab| ≤ |L| + 1 := by
    calc _ ≤ |L + ab.1| * P.g1 ab + |L + ab.2| * P.g2 ab := by
          have := abs_add_le ((L + ab.1) * P.g1 ab) ((L + ab.2) * P.g2 ab)
          rwa [abs_mul, abs_mul, abs_of_nonneg hg1, abs_of_nonneg hg2] at this
      _ ≤ (|L| + 1) * P.g1 ab + (|L| + 1) * P.g2 ab := by
          have h1 : |L + ab.1| ≤ |L| + 1 := (abs_add_le _ _).trans (by rw [abs_of_nonneg hsq.1.1]; linarith [hsq.1.2])
          have h2 : |L + ab.2| ≤ |L| + 1 := (abs_add_le _ _).trans (by rw [abs_of_nonneg hsq.2.1]; linarith [hsq.2.2])
          exact add_le_add (mul_le_mul_of_nonneg_right h1 hg1) (mul_le_mul_of_nonneg_right h2 hg2)
      _ ≤ (|L| + 1) * 1 := by nlinarith [abs_nonneg L]
      _ = |L| + 1 := mul_one _
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (rho_nonneg _ _)]
  have hsub : |(L + ab.1) * P.g1 ab + (L + ab.2) * P.g2 ab - P.u ab| ≤ |L| + 1 + Umax := by
    calc _ ≤ |(L + ab.1) * P.g1 ab + (L + ab.2) * P.g2 ab| + |P.u ab| := abs_sub _ _
      _ = |(L + ab.1) * P.g1 ab + (L + ab.2) * P.g2 ab| + P.u ab := by rw [abs_of_nonneg hu_nn]
      _ ≤ |L| + 1 + Umax := by linarith
  exact mul_le_mul_of_nonneg_right hsub (rho_nonneg _ _)

lemma stripFunctional_symm (L : ℝ) (P : InterimProfile) :
    stripFunctional L P.symm = stripFunctional L P := by
  have hswap_mem : ∀ a b : ℝ, (a, b) ∈ stripSet ↔ (b, a) ∈ stripSet := by
    intro a b
    simp only [stripSet, openUnitSquare, mem_inter_iff, mem_ofPred_eq, mem_prod, mem_Ioo]
    constructor <;> rintro ⟨⟨h1, h2⟩, h3, h4⟩ <;> exact ⟨⟨h2, h1⟩, by linarith, by linarith⟩
  have hmp := Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
  let F : Type2 → ℝ := fun ab => ((L + ab.1) * P.g1 ab + (L + ab.2) * P.g2 ab - P.u ab) * rho ab.1 ab.2
  have hswap_eq : ∫ ab in stripSet, F (ab.2, ab.1) = ∫ ab in stripSet, F ab := by
    rw [← integral_indicator measurableSet_stripSet, ← integral_indicator measurableSet_stripSet,
        Measure.volume_eq_prod,
        ← hmp.integral_comp MeasurableEquiv.prodComm.measurableEmbedding (stripSet.indicator F)]
    congr 1; ext ⟨a, b⟩
    by_cases h : (a, b) ∈ stripSet
    · have hs : (b, a) ∈ stripSet := (hswap_mem a b).mp h
      simp only [Function.comp_apply, Prod.swap_prod_mk, indicator_of_mem hs, indicator_of_mem h]
    · have hs : (b, a) ∉ stripSet := mt (hswap_mem a b).mpr h
      simp only [Function.comp_apply, Prod.swap_prod_mk, indicator_of_notMem hs, indicator_of_notMem h]
  have hF_int : IntegrableOn F stripSet volume := integrableOn_strip_integrand L P
  have hFswap_int : IntegrableOn (fun ab : Type2 => F (ab.2, ab.1)) stripSet volume := by
    rw [← integrable_indicator_iff measurableSet_stripSet, Measure.volume_eq_prod]
    have hi := (integrable_indicator_iff measurableSet_stripSet).mpr hF_int
    rw [Measure.volume_eq_prod] at hi
    refine ((hmp.integrable_comp_emb MeasurableEquiv.prodComm.measurableEmbedding).mpr hi).congr
      (ae_of_all _ (fun ⟨a, b⟩ => ?_))
    by_cases h : (a, b) ∈ stripSet
    · have hs : (b, a) ∈ stripSet := (hswap_mem a b).mp h
      simp only [Function.comp_apply, Prod.swap_prod_mk, indicator_of_mem hs, indicator_of_mem h]
    · have hs : (b, a) ∉ stripSet := mt (hswap_mem a b).mpr h
      simp only [Function.comp_apply, Prod.swap_prod_mk, indicator_of_notMem hs, indicator_of_notMem h]
  unfold stripFunctional
  congr 1
  · have hpt : ∀ ab ∈ stripSet,
        ((L + ab.1) * P.symm.g1 ab + (L + ab.2) * P.symm.g2 ab - P.symm.u ab) * rho ab.1 ab.2 =
        (F ab + F (ab.2, ab.1)) / 2 := by
      intro ab _
      dsimp only [F, InterimProfile.symm]
      have hrc : rho ab.2 ab.1 = rho ab.1 ab.2 := by unfold rho; rw [mul_comm ab.2 ab.1]
      rw [hrc]; ring
    rw [setIntegral_congr_fun measurableSet_stripSet hpt,
        integral_div, integral_add hF_int hFswap_int, hswap_eq]
    ring
  · refine setIntegral_congr_fun measurableSet_Ioo (fun s _ => ?_)
    dsimp only [InterimProfile.symm]; ring

lemma stripFunctional_le_shiftZero (L : ℝ) (P : InterimProfile) :
    stripFunctional L P ≤ stripFunctional L P.shiftZero := by
  have h0 : ((0 : ℝ), (0 : ℝ)) ∈ unitSquare := ⟨⟨le_rfl, zero_le_one⟩, ⟨le_rfl, zero_le_one⟩⟩
  have hc0 : 0 ≤ P.u (0, 0) := P.u_nonneg (0, 0) h0
  have h1 : IntegrableOn (fun ab : Type2 => ((L + ab.1) * P.g1 ab + (L + ab.2) * P.g2 ab - P.u ab) * rho ab.1 ab.2)
      stripSet volume := integrableOn_strip_integrand L P
  have h2 : IntegrableOn (fun ab : Type2 => P.u (0, 0) * rho ab.1 ab.2) stripSet volume :=
    integrableOn_rho_stripSet.const_mul (P.u (0, 0))
  have hstrip_diff :
      (∫ ab in stripSet, ((L + ab.1) * P.shiftZero.g1 ab + (L + ab.2) * P.shiftZero.g2 ab - P.shiftZero.u ab) * rho ab.1 ab.2) =
      (∫ ab in stripSet, ((L + ab.1) * P.g1 ab + (L + ab.2) * P.g2 ab - P.u ab) * rho ab.1 ab.2) +
      P.u (0, 0) * (∫ ab in stripSet, rho ab.1 ab.2) := by
    have hpt : ∀ ab ∈ stripSet,
        ((L + ab.1) * P.shiftZero.g1 ab + (L + ab.2) * P.shiftZero.g2 ab - P.shiftZero.u ab) * rho ab.1 ab.2 =
        ((L + ab.1) * P.g1 ab + (L + ab.2) * P.g2 ab - P.u ab) * rho ab.1 ab.2 + P.u (0, 0) * rho ab.1 ab.2 := by
      intro ab _; dsimp only [InterimProfile.shiftZero]; ring
    rw [setIntegral_congr_fun measurableSet_stripSet hpt, integral_add h1 h2, integral_const_mul]
  have hbdy_int1 : IntegrableOn (fun s => (P.u (s + t0, s) + P.u (s, s + t0)) * (t0 * rho (s + t0) s))
      (Ioo (0 : ℝ) (1 - t0)) volume :=
    ((integrableOn_bdy_t0 P).add (integrableOn_bdy_t0 P.swap)).congr_fun
      (fun s _ => by dsimp only [Pi.add_apply, InterimProfile.swap]; ring) measurableSet_Ioo
  have hbdy_int2 : IntegrableOn (fun s => 2 * P.u (0, 0) * (t0 * rho (s + t0) s))
      (Ioo (0 : ℝ) (1 - t0)) volume := by
    have h : IntegrableOn (fun s => 2 * P.u (0, 0) * t0 * rho (s + t0) s) (Ioo (0 : ℝ) (1 - t0)) volume :=
      (integrableOn_rho_diag (s := 1 - t0) (by linarith [t0_lt_one]) t0_pos).const_mul (2 * P.u (0, 0) * t0)
    exact h.congr_fun (fun s _ => by ring) measurableSet_Ioo
  have hbdy_diff :
      (∫ s in Ioo (0 : ℝ) (1 - t0), (P.shiftZero.u (s + t0, s) + P.shiftZero.u (s, s + t0)) * (t0 * rho (s + t0) s)) =
      (∫ s in Ioo (0 : ℝ) (1 - t0), (P.u (s + t0, s) + P.u (s, s + t0)) * (t0 * rho (s + t0) s)) -
      2 * P.u (0, 0) * (∫ s in Ioo (0 : ℝ) (1 - t0), t0 * rho (s + t0) s) := by
    have hpt : ∀ s ∈ Ioo (0 : ℝ) (1 - t0),
        (P.shiftZero.u (s + t0, s) + P.shiftZero.u (s, s + t0)) * (t0 * rho (s + t0) s) =
        (P.u (s + t0, s) + P.u (s, s + t0)) * (t0 * rho (s + t0) s) -
          2 * P.u (0, 0) * (t0 * rho (s + t0) s) := by
      intro s _; dsimp only [InterimProfile.shiftZero]; ring
    rw [setIntegral_congr_fun measurableSet_Ioo hpt, integral_sub hbdy_int1 hbdy_int2, integral_const_mul]
  unfold stripFunctional
  rw [hstrip_diff, hbdy_diff]
  have hnn1 : 0 ≤ ∫ ab in stripSet, rho ab.1 ab.2 :=
    setIntegral_nonneg measurableSet_stripSet (fun ab _ => rho_nonneg _ _)
  have hnn2 : 0 ≤ ∫ s in Ioo (0 : ℝ) (1 - t0), t0 * rho (s + t0) s :=
    setIntegral_nonneg measurableSet_Ioo (fun s _ => mul_nonneg t0_pos.le (rho_nonneg _ _))
  nlinarith

/-! ### Step 3: Radial identity on `S_+`, by integrating along rays through the origin

Along the ray `λ ↦ (λ, λ η)` one has `a g₁ + b g₂ = λ · d/dλ u(λ, λ η)`, and `ρ da db` is
`(1 / (4 √η)) dλ dη`, which has no singularity in `λ`. So the radial integral is an exact
one-dimensional identity on each ray, and the boundary terms come from two substitutions in `η`. -/

lemma radial_green_stripPos (P : InterimProfile) :
    (∫ ab in stripPos, (ab.1 * P.g1 ab + ab.2 * P.g2 ab + P.u ab) * rho ab.1 ab.2) =
    (∫ t in Ioo (0 : ℝ) t0, P.u (1, 1 - t) * rho 1 (1 - t)) +
    (∫ s in Ioo (0 : ℝ) (1 - t0), P.u (s + t0, s) * (t0 * rho (s + t0) s)) := by
  have ht0 := t0_pos
  have ht1 := t0_lt_one
  let Umax : ℝ := P.u (0, 0) + 1
  -- a measurable modification of `u` that agrees with it on the unit square
  let clamp : Type2 → Type2 := fun ab => (max 0 (min 1 ab.1), max 0 (min 1 ab.2))
  have hclamp_cont : Continuous clamp :=
    (continuous_const.max (continuous_const.min continuous_fst)).prodMk
      (continuous_const.max (continuous_const.min continuous_snd))
  have hclamp_mem : ∀ ab, clamp ab ∈ unitSquare := fun ab =>
    ⟨⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩,
     ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩⟩
  have hclamp_id : ∀ ab ∈ unitSquare, clamp ab = ab := by
    intro ab hab
    show (max 0 (min 1 ab.1), max 0 (min 1 ab.2)) = ab
    rw [min_eq_right hab.1.2, min_eq_right hab.2.2, max_eq_right hab.1.1, max_eq_right hab.2.1]
  let ut : Type2 → ℝ := fun ab => P.u (clamp ab)
  have hut_meas : Measurable ut :=
    (P.u_continuousOn.comp_continuous hclamp_cont hclamp_mem).measurable
  have hut_eq : ∀ ab ∈ unitSquare, ut ab = P.u ab := fun ab hab => by
    show P.u (clamp ab) = P.u ab; rw [hclamp_id ab hab]
  have hut_bd : ∀ ab, 0 ≤ ut ab ∧ ut ab ≤ Umax := fun ab =>
    ⟨P.u_nonneg _ (hclamp_mem ab), P.u_le_bound (hclamp_mem ab)⟩
  have hUmax : 0 ≤ Umax := (hut_bd (0, 0)).1.trans (hut_bd (0, 0)).2
  let F : Type2 → ℝ := fun ab => ab.1 * P.g1 ab + ab.2 * P.g2 ab + ut ab
  have hF_meas : Measurable F :=
    ((measurable_fst.mul P.g1_meas).add (measurable_snd.mul P.g2_meas)).add hut_meas
  have hF_int : IntegrableOn (fun ab : Type2 => F ab * rho ab.1 ab.2) stripPos volume := by
    refine (integrableOn_rho_stripPos.const_mul (1 + Umax)).mono'
      (hF_meas.mul (by unfold rho; fun_prop)).aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_stripPos]; filter_upwards with ab hab
    have hsq : ab ∈ unitSquare := ⟨Ioo_subset_Icc_self hab.1.1, Ioo_subset_Icc_self hab.1.2⟩
    have hg1 := P.g1_nonneg ab hsq; have hg2 := P.g2_nonneg ab hsq; have hgs := P.g_sum_le ab hsq
    have hb := hut_bd ab
    have hnn : 0 ≤ F ab := by dsimp only [F]; nlinarith [hsq.1.1, hsq.2.1]
    have hle : F ab ≤ 1 + Umax := by dsimp only [F]; nlinarith [hsq.1.2, hsq.2.2]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hnn (rho_nonneg _ _))]
    exact mul_le_mul_of_nonneg_right hle (rho_nonneg _ _)
  -- the strip as a region star-shaped about the origin
  let Λ : ℝ → ℝ := fun η => min 1 (t0 / (1 - η))
  have hΛm : Measurable Λ :=
    measurable_const.min (measurable_const.div (measurable_const.sub measurable_id))
  have hset : stripPos =
      {ab : Type2 | ab ∈ openUnitSquare ∧ ab.2 < ab.1 ∧ ab.1 < Λ (ab.2 / ab.1)} := by
    ext ab
    have key : ab ∈ openUnitSquare → ab.2 < ab.1 →
        (ab.1 - ab.2 < t0 ↔ ab.1 < Λ (ab.2 / ab.1)) := by
      intro hsq hba
      have ha : 0 < ab.1 := hsq.1.1
      have h1 : 0 < 1 - ab.2 / ab.1 := by rw [sub_pos, div_lt_one ha]; exact hba
      have he : ab.1 * (1 - ab.2 / ab.1) = ab.1 - ab.2 := by field_simp
      show _ ↔ ab.1 < min 1 (t0 / (1 - ab.2 / ab.1))
      rw [lt_min_iff, lt_div_iff₀ h1, he]
      exact ⟨fun h => ⟨hsq.1.2, h⟩, fun h => h.2⟩
    constructor
    · rintro ⟨hsq, h0, hlt⟩
      have hba : ab.2 < ab.1 := by have h : (0 : ℝ) < ab.1 - ab.2 := h0; linarith
      exact ⟨hsq, hba, (key hsq hba).mp hlt⟩
    · rintro ⟨hsq, hba, hlt⟩
      exact ⟨hsq, (by show (0 : ℝ) < ab.1 - ab.2; linarith), (key hsq hba).mpr hlt⟩
  have hLHS : (∫ ab in stripPos, (ab.1 * P.g1 ab + ab.2 * P.g2 ab + P.u ab) * rho ab.1 ab.2) =
      ∫ ab in stripPos, F ab * rho ab.1 ab.2 := by
    refine setIntegral_congr_fun measurableSet_stripPos (fun ab hab => ?_)
    show _ = (ab.1 * P.g1 ab + ab.2 * P.g2 ab + ut ab) * rho ab.1 ab.2
    rw [hut_eq ab ⟨Ioo_subset_Icc_self hab.1.1, Ioo_subset_Icc_self hab.1.2⟩]
  have hF_int' : IntegrableOn (fun ab : Type2 => F ab * rho ab.1 ab.2)
      {ab : Type2 | ab ∈ openUnitSquare ∧ ab.2 < ab.1 ∧ ab.1 < Λ (ab.2 / ab.1)} volume := by
    rw [← hset]; exact hF_int
  have hray := setIntegral_ray_region hΛm (fun η _ => min_le_left _ _) hF_meas hF_int'
  have hΛpos : ∀ η ∈ Ioo (0 : ℝ) 1, 0 < Λ η := fun η hη =>
    lt_min one_pos (div_pos ht0 (by linarith [hη.2]))
  have hΛ1 : ∀ η, Λ η ≤ 1 := fun η => min_le_left _ _
  have hray_mem : ∀ η ∈ Ioo (0 : ℝ) 1, ∀ lam ∈ Icc (0 : ℝ) (Λ η), (lam, lam * η) ∈ unitSquare :=
    fun η hη lam hlam => ⟨⟨hlam.1, hlam.2.trans (hΛ1 η)⟩, ⟨mul_nonneg hlam.1 hη.1.le,
      (mul_le_of_le_one_right hlam.1 hη.2.le).trans (hlam.2.trans (hΛ1 η))⟩⟩
  -- exact identity on each ray
  let H : ℝ → ℝ := fun η => (1 / (4 * Real.sqrt η)) * (Λ η * ut (Λ η, Λ η * η))
  have hinner : ∀ η ∈ Ioo (0 : ℝ) 1,
      (1 / (4 * Real.sqrt η)) * ∫ lam in Ioo (0 : ℝ) (Λ η), F (lam, lam * η) = H η := by
    intro η hη
    have hibp := subgrad_ibp (hΛpos η hη).le (P.raySubgrad hη.1.le hη.2.le (hΛ1 η))
      (φ := fun x => x) (φ' := fun _ => 1) continuousOn_id continuousOn_const
      (fun x _ => hasDerivAt_id x)
    rw [mul_zero, sub_zero] at hibp
    have hcongr : ∫ lam in Ioo (0 : ℝ) (Λ η), F (lam, lam * η) =
        ∫ lam in Ioo (0 : ℝ) (Λ η),
          ((P.g1 (lam, lam * η) + η * P.g2 (lam, lam * η)) * lam + P.u (lam, lam * η) * 1) := by
      refine setIntegral_congr_fun measurableSet_Ioo (fun lam hlam => ?_)
      show lam * P.g1 (lam, lam * η) + lam * η * P.g2 (lam, lam * η) + ut (lam, lam * η) = _
      rw [hut_eq _ (hray_mem η hη lam (Ioo_subset_Icc_self hlam))]; ring
    show _ = (1 / (4 * Real.sqrt η)) * (Λ η * ut (Λ η, Λ η * η))
    rw [hcongr, hibp, hut_eq _ (hray_mem η hη _ ⟨(hΛpos η hη).le, le_rfl⟩), mul_comm (P.u _)]
  have hH_meas : Measurable H := by
    have hpt : Measurable (fun η : ℝ => ((Λ η, Λ η * η) : Type2)) :=
      hΛm.prodMk (hΛm.mul measurable_id)
    exact (by fun_prop : Measurable fun η : ℝ => 1 / (4 * Real.sqrt η)).mul
      (hΛm.mul (hut_meas.comp hpt))
  have hH_int : IntegrableOn H (Ioo (0 : ℝ) 1) volume := by
    refine (integrableOn_density1D_Ioo.const_mul (Umax / 2)).mono' hH_meas.aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Ioo]; filter_upwards with η hη
    have hs : 0 < Real.sqrt η := Real.sqrt_pos.mpr hη.1
    have hb := hut_bd (Λ η, Λ η * η)
    have hc : 0 ≤ 1 / (4 * Real.sqrt η) := by positivity
    have hprod : Λ η * ut (Λ η, Λ η * η) ≤ Umax := by
      nlinarith [(hΛpos η hη).le, hΛ1 η, hb.1, hb.2]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hc (mul_nonneg (hΛpos η hη).le hb.1))]
    calc (1 / (4 * Real.sqrt η)) * (Λ η * ut (Λ η, Λ η * η))
        ≤ (1 / (4 * Real.sqrt η)) * Umax := mul_le_mul_of_nonneg_left hprod hc
      _ = Umax / 2 * density1D η := by unfold density1D; ring
  have hb0 : 0 < 1 - t0 := by linarith
  have hb1 : 1 - t0 < 1 := by linarith
  have hH_ii : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 → IntervalIntegrable H volume a b := fun a b ha hab hb =>
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hab).mpr (hH_int.mono_set (Ioo_subset_Ioo ha hb))
  have hsplit : ∫ η in Ioo (0 : ℝ) 1, H η =
      (∫ η in (0 : ℝ)..(1 - t0), H η) + ∫ η in (1 - t0)..1, H η := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hH_ii 0 (1 - t0) le_rfl hb0.le hb1.le)
      (hH_ii (1 - t0) 1 hb0.le hb1.le le_rfl), intervalIntegral.integral_of_le zero_le_one,
      setIntegral_congr_set Ioo_ae_eq_Ioc]
  -- the edge `a = 1`: substitute `η = 1 - t`
  have hedge : ∫ η in (1 - t0)..1, H η = ∫ t in Ioo (0 : ℝ) t0, P.u (1, 1 - t) * rho 1 (1 - t) := by
    have hsub := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := t0) H 1
    rw [sub_zero] at hsub
    rw [← hsub, intervalIntegral.integral_of_le ht0.le, ← setIntegral_congr_set Ioo_ae_eq_Ioc]
    refine setIntegral_congr_fun measurableSet_Ioo (fun t ht => ?_)
    have hη : 1 - t ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have hΛe : Λ (1 - t) = 1 := by
      show min 1 (t0 / (1 - (1 - t))) = 1
      rw [min_eq_left]
      rw [show 1 - (1 - t) = t by ring, le_div_iff₀ ht.1]; linarith [ht.2]
    show (1 / (4 * Real.sqrt (1 - t))) * (Λ (1 - t) * ut (Λ (1 - t), Λ (1 - t) * (1 - t))) =
      P.u (1, 1 - t) * rho 1 (1 - t)
    rw [hΛe, one_mul, one_mul,
      hut_eq _ ⟨⟨zero_le_one, le_rfl⟩, ⟨hη.1.le, hη.2.le⟩⟩]
    unfold rho; rw [one_mul]; ring
  -- the edge `a - b = t₀`: substitute `s = t₀ η / (1 - η)`
  have hstrip : ∫ η in (0 : ℝ)..(1 - t0), H η =
      ∫ s in Ioo (0 : ℝ) (1 - t0), P.u (s + t0, s) * (t0 * rho (s + t0) s) := by
    let f : ℝ → ℝ := fun η => t0 * η / (1 - η)
    let f' : ℝ → ℝ := fun η => t0 / (1 - η) ^ 2
    let g : ℝ → ℝ := fun s => P.u (s + t0, s) * (t0 * rho (s + t0) s)
    have hden : ∀ η ∈ Icc (0 : ℝ) (1 - t0), 0 < 1 - η := fun η hη => by linarith [hη.2]
    have hf_deriv : ∀ η ∈ Icc (0 : ℝ) (1 - t0), HasDerivAt f (f' η) η := by
      intro η hη
      have h1 : (1 - η) ≠ 0 := (hden η hη).ne'
      have hn : HasDerivAt (fun y : ℝ => t0 * y) t0 η := by
        simpa using (hasDerivAt_id η).const_mul t0
      have hd : HasDerivAt (fun y : ℝ => 1 - y) (-1) η := by
        simpa using (hasDerivAt_id η).const_sub (1 : ℝ)
      have hq := hn.div hd h1
      have he : (t0 * (1 - η) - t0 * η * (-1)) / (1 - η) ^ 2 = t0 / (1 - η) ^ 2 := by
        congr 1; ring
      exact hq.congr_deriv he
    have hf_cont : ContinuousOn f (uIcc (0 : ℝ) (1 - t0)) := by
      rw [uIcc_of_le hb0.le]
      exact fun η hη => (hf_deriv η hη).continuousAt.continuousWithinAt
    have hmm : min (0 : ℝ) (1 - t0) = 0 := min_eq_left hb0.le
    have hMM : max (0 : ℝ) (1 - t0) = 1 - t0 := max_eq_right hb0.le
    have hf_range : ∀ η ∈ Icc (0 : ℝ) (1 - t0), f η ∈ Icc (0 : ℝ) (1 - t0) := by
      intro η hη
      have h1 := hden η hη
      refine ⟨div_nonneg (mul_nonneg ht0.le hη.1) h1.le, ?_⟩
      show t0 * η / (1 - η) ≤ 1 - t0
      rw [div_le_iff₀ h1]; nlinarith [hη.2]
    have hf_range' : ∀ η ∈ Ioo (0 : ℝ) (1 - t0), f η ∈ Ioo (0 : ℝ) (1 - t0) := by
      intro η hη
      have h1 := hden η (Ioo_subset_Icc_self hη)
      refine ⟨div_pos (mul_pos ht0 hη.1) h1, ?_⟩
      show t0 * η / (1 - η) < 1 - t0
      rw [div_lt_iff₀ h1]; nlinarith [hη.2]
    have hg_int : IntegrableOn g (Ioo (0 : ℝ) (1 - t0)) volume := integrableOn_bdy_t0 P
    have hg_cont : ContinuousOn g (Ioo (0 : ℝ) (1 - t0)) := by
      have hu : ContinuousOn (fun s : ℝ => P.u (s + t0, s)) (Ioo (0 : ℝ) (1 - t0)) :=
        P.u_continuousOn.comp ((continuous_id.add continuous_const).prodMk continuous_id).continuousOn
          (fun s hs => ⟨⟨by linarith [hs.1], by linarith [hs.2]⟩, ⟨hs.1.le, by linarith [hs.2]⟩⟩)
      have hr : ContinuousOn (fun s : ℝ => rho (s + t0) s) (Ioo (0 : ℝ) (1 - t0)) := by
        unfold rho
        refine continuousOn_const.div (continuousOn_const.mul
          (Real.continuous_sqrt.comp ((continuous_id.add continuous_const).mul continuous_id)).continuousOn) ?_
        intro s hs
        exact mul_ne_zero four_ne_zero (Real.sqrt_pos.mpr (mul_pos (by linarith [hs.1]) hs.1)).ne'
      exact hu.mul (continuousOn_const.mul hr)
    have hpt : ∀ η ∈ Ioo (0 : ℝ) (1 - t0), (g ∘ f) η * f' η = H η := by
      intro η hη
      have h1 : 0 < 1 - η := by linarith [hη.2]
      have hη01 : η ∈ Ioo (0 : ℝ) 1 := ⟨hη.1, by linarith [hη.2]⟩
      obtain ⟨lam, hlam⟩ : ∃ lam, lam = t0 / (1 - η) := ⟨_, rfl⟩
      have hlam0 : 0 < lam := by rw [hlam]; exact div_pos ht0 h1
      have hΛe : Λ η = lam := by
        show min 1 (t0 / (1 - η)) = lam
        rw [← hlam, min_eq_right]
        rw [hlam, div_le_one h1]; linarith [hη.2]
      have hf1 : f η + t0 = lam := by
        show t0 * η / (1 - η) + t0 = lam
        rw [hlam]; field_simp; ring
      have hf2 : f η = lam * η := by
        show t0 * η / (1 - η) = lam * η
        rw [hlam]; ring
      have hf'e : t0 * f' η = lam ^ 2 := by
        show t0 * (t0 / (1 - η) ^ 2) = lam ^ 2
        rw [hlam]; field_simp
      have hrho_eq : lam * rho lam (lam * η) = 1 / (4 * Real.sqrt η) := by
        unfold rho
        have hsq : Real.sqrt (lam * (lam * η)) = lam * Real.sqrt η := by
          rw [← mul_assoc, Real.sqrt_mul (mul_nonneg hlam0.le hlam0.le), Real.sqrt_mul_self hlam0.le]
        rw [hsq]; field_simp [hlam0.ne', (Real.sqrt_pos.mpr hη.1).ne']
      have hmem : (lam, lam * η) ∈ unitSquare := by
        have := hray_mem η hη01 (Λ η) ⟨(hΛpos η hη01).le, le_rfl⟩
        rwa [hΛe] at this
      show P.u (f η + t0, f η) * (t0 * rho (f η + t0) (f η)) * f' η =
        (1 / (4 * Real.sqrt η)) * (Λ η * ut (Λ η, Λ η * η))
      rw [hf1, hf2, hΛe, hut_eq _ hmem, ← hrho_eq]
      calc P.u (lam, lam * η) * (t0 * rho lam (lam * η)) * f' η
          = P.u (lam, lam * η) * rho lam (lam * η) * (t0 * f' η) := by ring
        _ = P.u (lam, lam * η) * rho lam (lam * η) * lam ^ 2 := by rw [hf'e]
        _ = lam * rho lam (lam * η) * (lam * P.u (lam, lam * η)) := by ring
    have hsubst := intervalIntegral.integral_comp_mul_deriv''' (a := (0 : ℝ)) (b := 1 - t0)
      (f := f) (f' := f') (g := g) hf_cont
      (by rw [hmm, hMM]
          exact fun η hη => (hf_deriv η (Ioo_subset_Icc_self hη)).hasDerivWithinAt)
      (by rw [hmm, hMM]
          exact hg_cont.mono (by rintro _ ⟨η, hη, rfl⟩; exact hf_range' η hη))
      (by rw [uIcc_of_le hb0.le]
          exact ((integrableOn_Icc_iff_integrableOn_Ioo).mpr hg_int).mono_set
            (by rintro _ ⟨η, hη, rfl⟩; exact hf_range η hη))
      (by rw [uIcc_of_le hb0.le, integrableOn_Icc_iff_integrableOn_Ioo]
          exact (hH_int.mono_set (Ioo_subset_Ioo le_rfl hb1.le)).congr_fun
            (fun η hη => (hpt η hη).symm) measurableSet_Ioo)
    have hf0 : f 0 = 0 := by show t0 * 0 / (1 - 0) = 0; simp
    have hfb : f (1 - t0) = 1 - t0 := by
      show t0 * (1 - t0) / (1 - (1 - t0)) = 1 - t0
      rw [show 1 - (1 - t0) = t0 by ring]; field_simp
    rw [hf0, hfb, intervalIntegral.integral_of_le hb0.le, intervalIntegral.integral_of_le hb0.le,
      ← setIntegral_congr_set Ioo_ae_eq_Ioc, ← setIntegral_congr_set Ioo_ae_eq_Ioc] at hsubst
    rw [intervalIntegral.integral_of_le hb0.le, ← setIntegral_congr_set Ioo_ae_eq_Ioc, ← hsubst]
    exact setIntegral_congr_fun measurableSet_Ioo (fun η hη => (hpt η hη).symm)
  rw [hLHS, hset, hray, setIntegral_congr_fun measurableSet_Ioo hinner, hsplit, hedge, hstrip, add_comm]


lemma stripPos_eq_setOf :
    stripPos = {ab : Type2 | ab ∈ openUnitSquare ∧ (0 : ℝ) < ab.1 - ab.2 ∧ ab.1 - ab.2 < t0} := by
  ext ab; simp only [stripPos, mem_inter_iff, mem_ofPred_eq]

lemma integrableOn_deficit_stripPos (Q : InterimProfile) :
    IntegrableOn (fun ab : Type2 => (1 - (Q.g1 ab + Q.g2 ab)) * rho ab.1 ab.2) stripPos volume := by
  refine integrableOn_rho_stripPos.mono'
    ((measurable_const.sub (Q.g1_meas.add Q.g2_meas)).mul (by unfold rho; fun_prop)).aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_stripPos]; filter_upwards with ab hab
  have hsq : ab ∈ unitSquare := ⟨Ioo_subset_Icc_self hab.1.1, Ioo_subset_Icc_self hab.1.2⟩
  have hD0 : 0 ≤ 1 - (Q.g1 ab + Q.g2 ab) := by linarith [Q.g_sum_le ab hsq]
  have hD1 : 1 - (Q.g1 ab + Q.g2 ab) ≤ 1 := by linarith [Q.g1_nonneg ab hsq, Q.g2_nonneg ab hsq]
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hD0 (rho_nonneg _ _))]
  calc (1 - (Q.g1 ab + Q.g2 ab)) * rho ab.1 ab.2 ≤ 1 * rho ab.1 ab.2 := mul_le_mul_of_nonneg_right hD1 (rho_nonneg _ _)
    _ = rho ab.1 ab.2 := one_mul _

/-- Step 3B: Exact half-strip reduction of `(stripFunctional L Q - M1 L) / 2` for symmetric `Q`. -/
lemma lemma5_half_strip_eq (L : ℝ) (Q : InterimProfile)
    (hQ_sym_u : ∀ a b, Q.u (b, a) = Q.u (a, b))
    (hQ_sym_g : ∀ a b, Q.g1 (b, a) = Q.g2 (a, b)) :
    let w : Type2 → ℝ := fun ab => (ab.1 + ab.2) / 2 - Q.u ab
    let D : Type2 → ℝ := fun ab => 1 - (Q.g1 ab + Q.g2 ab)
    (stripFunctional L Q - M1 L) / 2 =
      -L * (∫ ab in stripPos, D ab * rho ab.1 ab.2) +
      2 * (∫ ab in stripPos, w ab * rho ab.1 ab.2) -
      (∫ t in Ioo (0 : ℝ) t0, w (1, 1 - t) * rho 1 (1 - t)) := by
  intro w D
  have hsym_strip : ∀ R : InterimProfile,
      (∀ a b, R.u (b, a) = R.u (a, b)) → (∀ a b, R.g1 (b, a) = R.g2 (a, b)) →
      stripFunctional L R =
        2 * ((∫ ab in stripPos, ((L + ab.1) * R.g1 ab + (L + ab.2) * R.g2 ab - R.u ab) * rho ab.1 ab.2) -
             (∫ s in Ioo (0 : ℝ) (1 - t0), R.u (s + t0, s) * (t0 * rho (s + t0) s))) := by
    intro R hRu hRg
    let stripNeg : Set Type2 :=
      openUnitSquare ∩ ({ab : Type2 | (0 : ℝ) < ab.2 - ab.1} ∩ {ab : Type2 | ab.2 - ab.1 < t0})
    have hSn_meas : MeasurableSet stripNeg :=
      measurableSet_openUnitSquare.inter
        ((measurableSet_lt measurable_const (measurable_snd.sub measurable_fst)).inter
         (measurableSet_lt (measurable_snd.sub measurable_fst) measurable_const))
    have hae_S : (stripSet : Set Type2) =ᵐ[volume] (stripPos ∪ stripNeg) := by
      apply MeasureTheory.ae_eq_set.mpr
      constructor
      · have hsub : stripSet \ (stripPos ∪ stripNeg) ⊆ {ab : Type2 | ab.1 = ab.2} := by
          intro ab hab
          simp only [Set.mem_sdiff, mem_union, stripSet, stripPos, stripNeg, mem_inter_iff, mem_ofPred_eq, not_or] at hab ⊢
          by_contra hne
          have hsq := hab.1.1
          rcases lt_or_gt_of_ne hne with hlt | hgt
          · exact hab.2.2 ⟨hsq, by linarith, by linarith [hab.1.2.1]⟩
          · exact hab.2.1 ⟨hsq, by linarith, hab.1.2.2⟩
        refine measure_mono_null hsub ?_
        have hdiag : {ab : Type2 | ab.1 = ab.2} = {ab : Type2 | ab.1 - ab.2 = 0} := by
          ext ab; simp [sub_eq_zero]
        rw [hdiag]; exact volume_diff_eq_const_zero 0
      · have : (stripPos ∪ stripNeg) \ stripSet = ∅ := by
          ext ab
          simp only [Set.mem_sdiff, mem_union, stripSet, stripPos, stripNeg, mem_inter_iff,
            mem_ofPred_eq, mem_empty_iff_false, iff_false]
          rintro ⟨⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩, hnot⟩
          · exact hnot ⟨h1, by linarith [t0_pos], h3⟩
          · exact hnot ⟨h1, by linarith, by linarith [t0_pos]⟩
        rw [this]; simp
    have hdisj : Disjoint stripPos stripNeg :=
      Set.disjoint_left.mpr (fun ab h1 h2 => by
        simp only [stripPos, stripNeg, mem_inter_iff, mem_ofPred_eq] at h1 h2; linarith [h1.2.1, h2.2.1])
    let F : Type2 → ℝ := fun ab => ((L + ab.1) * R.g1 ab + (L + ab.2) * R.g2 ab - R.u ab) * rho ab.1 ab.2
    have hF_int : IntegrableOn F stripSet volume := integrableOn_strip_integrand L R
    have hswap_mem : ∀ a b : ℝ, (a, b) ∈ stripPos ↔ (b, a) ∈ stripNeg := by
      intro a b
      simp only [stripPos, stripNeg, openUnitSquare, mem_inter_iff, mem_ofPred_eq, mem_prod, mem_Ioo]
      tauto
    have hmp := Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    have hSn_eq : ∫ ab in stripNeg, F ab = ∫ ab in stripPos, F ab := by
      rw [← integral_indicator hSn_meas, ← integral_indicator measurableSet_stripPos,
          Measure.volume_eq_prod,
          ← hmp.integral_comp MeasurableEquiv.prodComm.measurableEmbedding (stripNeg.indicator F)]
      congr 1; ext ⟨a, b⟩
      by_cases h : (a, b) ∈ stripPos
      · have hs : (b, a) ∈ stripNeg := (hswap_mem a b).mp h
        simp only [Function.comp_apply, Prod.swap_prod_mk, indicator_of_mem hs, indicator_of_mem h]
        dsimp only [F]; rw [hRu a b, hRg a b, show R.g2 (b, a) = R.g1 (a, b) by rw [← hRg b a]]
        have hrc : rho b a = rho a b := by unfold rho; rw [mul_comm b a]
        rw [hrc]; ring
      · have hs : (b, a) ∉ stripNeg := mt (hswap_mem a b).mpr h
        simp only [Function.comp_apply, Prod.swap_prod_mk, indicator_of_notMem hs, indicator_of_notMem h]
    have hSp_sub : stripPos ⊆ stripSet := by
      intro ab hab; simp only [stripPos, stripSet, mem_inter_iff, mem_ofPred_eq] at hab ⊢
      exact ⟨hab.1, by linarith [hab.2.1, t0_pos], hab.2.2⟩
    have hSn_sub : stripNeg ⊆ stripSet := by
      intro ab hab; simp only [stripNeg, stripSet, mem_inter_iff, mem_ofPred_eq] at hab ⊢
      exact ⟨hab.1, by linarith [hab.2.2], by linarith [hab.2.1, t0_pos]⟩
    unfold stripFunctional
    rw [setIntegral_congr_set hae_S, setIntegral_union hdisj hSn_meas
        (hF_int.mono_set hSp_sub) (hF_int.mono_set hSn_sub), hSn_eq]
    have hbdy_eq : (∫ s in Ioo (0 : ℝ) (1 - t0), (R.u (s + t0, s) + R.u (s, s + t0)) * (t0 * rho (s + t0) s)) =
        2 * ∫ s in Ioo (0 : ℝ) (1 - t0), R.u (s + t0, s) * (t0 * rho (s + t0) s) := by
      rw [← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioo (fun s _ => ?_)
      rw [hRu (s + t0) s]; ring
    rw [hbdy_eq]; ring
  have hR_green : ∀ R : InterimProfile,
      (∀ a b, R.u (b, a) = R.u (a, b)) → (∀ a b, R.g1 (b, a) = R.g2 (a, b)) →
      (stripFunctional L R) / 2 =
        L * (∫ ab in stripPos, (R.g1 ab + R.g2 ab) * rho ab.1 ab.2) +
        (∫ t in Ioo (0 : ℝ) t0, R.u (1, 1 - t) * rho 1 (1 - t)) -
        2 * (∫ ab in stripPos, R.u ab * rho ab.1 ab.2) := by
    intro R hRu hRg
    rw [hsym_strip R hRu hRg]
    have hrg := radial_green_stripPos R
    have h1_int : IntegrableOn (fun ab : Type2 => L * (R.g1 ab + R.g2 ab) * rho ab.1 ab.2) stripPos volume := by
      refine (integrableOn_rho_stripPos.const_mul |L|).mono'
        ((measurable_const.mul (R.g1_meas.add R.g2_meas)).mul (by unfold rho; fun_prop)).aestronglyMeasurable ?_
      rw [ae_restrict_iff' measurableSet_stripPos]; filter_upwards with ab hab
      have hsq : ab ∈ unitSquare := ⟨Ioo_subset_Icc_self hab.1.1, Ioo_subset_Icc_self hab.1.2⟩
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (add_nonneg (R.g1_nonneg _ hsq) (R.g2_nonneg _ hsq)),
          abs_of_nonneg (rho_nonneg _ _)]
      calc |L| * (R.g1 ab + R.g2 ab) * rho ab.1 ab.2 ≤ |L| * 1 * rho ab.1 ab.2 :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (R.g_sum_le _ hsq) (abs_nonneg L)) (rho_nonneg _ _)
        _ = |L| * rho ab.1 ab.2 := by ring
    have h2_int : IntegrableOn (fun ab : Type2 => (ab.1 * R.g1 ab + ab.2 * R.g2 ab + R.u ab) * rho ab.1 ab.2)
        stripPos volume := by
      refine (integrableOn_rho_stripPos.const_mul (1 + (R.u (0, 0) + 1))).mono'
        (((measurable_fst.mul R.g1_meas).add (measurable_snd.mul R.g2_meas) |>.aestronglyMeasurable.add
          (R.u_aestronglyMeasurable.mono_measure (Measure.restrict_mono Set.inter_subset_left le_rfl))).mul
          (by unfold rho; fun_prop : Measurable _).aestronglyMeasurable) ?_
      rw [ae_restrict_iff' measurableSet_stripPos]; filter_upwards with ab hab
      have hsq : ab ∈ unitSquare := ⟨Ioo_subset_Icc_self hab.1.1, Ioo_subset_Icc_self hab.1.2⟩
      have hnn : 0 ≤ ab.1 * R.g1 ab + ab.2 * R.g2 ab + R.u ab := by
        nlinarith [hsq.1.1, hsq.2.1, R.g1_nonneg _ hsq, R.g2_nonneg _ hsq, R.u_nonneg _ hsq]
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hnn (rho_nonneg _ _))]
      have hle : ab.1 * R.g1 ab + ab.2 * R.g2 ab + R.u ab ≤ 1 + (R.u (0, 0) + 1) := by
        nlinarith [hsq.1.2, hsq.2.2, R.g1_nonneg _ hsq, R.g2_nonneg _ hsq, R.g_sum_le _ hsq, R.u_le_bound hsq]
      exact mul_le_mul_of_nonneg_right hle (rho_nonneg _ _)
    have h12_int : IntegrableOn (fun ab : Type2 => L * (R.g1 ab + R.g2 ab) * rho ab.1 ab.2 +
        (ab.1 * R.g1 ab + ab.2 * R.g2 ab + R.u ab) * rho ab.1 ab.2) stripPos volume := h1_int.add h2_int
    have h3_int : IntegrableOn (fun ab : Type2 => 2 * (R.u ab * rho ab.1 ab.2)) stripPos volume := by
      refine (integrableOn_rho_stripPos.const_mul (2 * (R.u (0, 0) + 1))).mono'
        ((R.u_aestronglyMeasurable.mono_measure (Measure.restrict_mono Set.inter_subset_left le_rfl)).mul
          (by unfold rho; fun_prop : Measurable _).aestronglyMeasurable |>.const_mul 2) ?_
      rw [ae_restrict_iff' measurableSet_stripPos]; filter_upwards with ab hab
      have hsq : ab ∈ unitSquare := ⟨Ioo_subset_Icc_self hab.1.1, Ioo_subset_Icc_self hab.1.2⟩
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by norm_num) (mul_nonneg (R.u_nonneg _ hsq) (rho_nonneg _ _)))]
      have := R.u_le_bound hsq
      nlinarith [rho_nonneg ab.1 ab.2]
    have hsplit : (∫ ab in stripPos, ((L + ab.1) * R.g1 ab + (L + ab.2) * R.g2 ab - R.u ab) * rho ab.1 ab.2) =
        L * (∫ ab in stripPos, (R.g1 ab + R.g2 ab) * rho ab.1 ab.2) +
        (∫ ab in stripPos, (ab.1 * R.g1 ab + ab.2 * R.g2 ab + R.u ab) * rho ab.1 ab.2) -
        2 * (∫ ab in stripPos, R.u ab * rho ab.1 ab.2) := by
      have hpt : ∀ ab ∈ stripPos,
          ((L + ab.1) * R.g1 ab + (L + ab.2) * R.g2 ab - R.u ab) * rho ab.1 ab.2 =
          L * (R.g1 ab + R.g2 ab) * rho ab.1 ab.2 +
          (ab.1 * R.g1 ab + ab.2 * R.g2 ab + R.u ab) * rho ab.1 ab.2 -
          2 * (R.u ab * rho ab.1 ab.2) := fun ab _ => by ring
      rw [setIntegral_congr_fun measurableSet_stripPos hpt, integral_sub h12_int h3_int,
          integral_add h1_int h2_int, integral_const_mul]
      have hLmul : ∫ ab in stripPos, L * (R.g1 ab + R.g2 ab) * rho ab.1 ab.2 =
          L * ∫ ab in stripPos, (R.g1 ab + R.g2 ab) * rho ab.1 ab.2 := by
        rw [← integral_const_mul]; refine setIntegral_congr_fun measurableSet_stripPos (fun _ _ => by ring)
      rw [hLmul]
    rw [hsplit, hrg]; ring
  have h1 := hR_green Q hQ_sym_u hQ_sym_g
  have h2 := hR_green linearHalfProfile
    (fun a b => by dsimp [linearHalfProfile]; ring)
    (fun a b => rfl)
  rw [stripFunctional_linearHalf] at h2
  have hDg_sub :
      (∫ ab in stripPos, (Q.g1 ab + Q.g2 ab) * rho ab.1 ab.2) -
      (∫ ab in stripPos, (linearHalfProfile.g1 ab + linearHalfProfile.g2 ab) * rho ab.1 ab.2) =
      -(∫ ab in stripPos, D ab * rho ab.1 ab.2) := by
    have hi1 : IntegrableOn (fun ab : Type2 => (Q.g1 ab + Q.g2 ab) * rho ab.1 ab.2) stripPos volume := by
      refine integrableOn_rho_stripPos.mono'
        ((Q.g1_meas.add Q.g2_meas).mul (by unfold rho; fun_prop)).aestronglyMeasurable ?_
      rw [ae_restrict_iff' measurableSet_stripPos]; filter_upwards with ab hab
      have hsq : ab ∈ unitSquare := ⟨Ioo_subset_Icc_self hab.1.1, Ioo_subset_Icc_self hab.1.2⟩
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (add_nonneg (Q.g1_nonneg _ hsq) (Q.g2_nonneg _ hsq)) (rho_nonneg _ _))]
      nlinarith [Q.g_sum_le _ hsq, rho_nonneg ab.1 ab.2]
    have hi2 : IntegrableOn (fun ab : Type2 => (linearHalfProfile.g1 ab + linearHalfProfile.g2 ab) * rho ab.1 ab.2)
        stripPos volume :=
      integrableOn_rho_stripPos.congr_fun
        (fun _ _ => by dsimp [linearHalfProfile]; ring) measurableSet_stripPos
    rw [← integral_sub hi1 hi2, ← integral_neg]
    refine setIntegral_congr_fun measurableSet_stripPos (fun ab _ => ?_)
    dsimp only [D, linearHalfProfile]; ring
  have hw_sub :
      (∫ ab in stripPos, linearHalfProfile.u ab * rho ab.1 ab.2) -
      (∫ ab in stripPos, Q.u ab * rho ab.1 ab.2) =
      ∫ ab in stripPos, w ab * rho ab.1 ab.2 := by
    have hi1 : IntegrableOn (fun ab : Type2 => linearHalfProfile.u ab * rho ab.1 ab.2) stripPos volume := by
      refine integrableOn_rho_stripPos.mono'
        ((linearHalfProfile.u_aestronglyMeasurable.mono_measure (Measure.restrict_mono Set.inter_subset_left le_rfl)).mul
          (by unfold rho; fun_prop : Measurable _).aestronglyMeasurable) ?_
      rw [ae_restrict_iff' measurableSet_stripPos]; filter_upwards with ab hab
      dsimp only [linearHalfProfile]
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by linarith [hab.1.1.1, hab.1.2.1]) (rho_nonneg _ _))]
      nlinarith [hab.1.1.2, hab.1.2.2, rho_nonneg ab.1 ab.2]
    have hi2 : IntegrableOn (fun ab : Type2 => Q.u ab * rho ab.1 ab.2) stripPos volume := by
      refine (integrableOn_rho_stripPos.const_mul (Q.u (0, 0) + 1)).mono'
        ((Q.u_aestronglyMeasurable.mono_measure (Measure.restrict_mono Set.inter_subset_left le_rfl)).mul
          (by unfold rho; fun_prop : Measurable _).aestronglyMeasurable) ?_
      rw [ae_restrict_iff' measurableSet_stripPos]; filter_upwards with ab hab
      have hsq : ab ∈ unitSquare := ⟨Ioo_subset_Icc_self hab.1.1, Ioo_subset_Icc_self hab.1.2⟩
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Q.u_nonneg _ hsq) (rho_nonneg _ _))]
      exact mul_le_mul_of_nonneg_right (Q.u_le_bound hsq) (rho_nonneg _ _)
    rw [← integral_sub hi1 hi2]
    refine setIntegral_congr_fun measurableSet_stripPos (fun ab _ => by dsimp only [w, linearHalfProfile]; ring)
  have hwbdy_sub :
      (∫ t in Ioo (0 : ℝ) t0, Q.u (1, 1 - t) * rho 1 (1 - t)) -
      (∫ t in Ioo (0 : ℝ) t0, linearHalfProfile.u (1, 1 - t) * rho 1 (1 - t)) =
      -(∫ t in Ioo (0 : ℝ) t0, w (1, 1 - t) * rho 1 (1 - t)) := by
    have hc_rho : ContinuousOn (fun t : ℝ => rho 1 (1 - t)) (Icc (0 : ℝ) t0) := by
      unfold rho
      refine continuousOn_const.div (continuousOn_const.mul
        (Real.continuous_sqrt.comp (continuous_const.mul (continuous_const.sub continuous_id))).continuousOn) ?_
      intro t ht
      have hsq : 0 < Real.sqrt (1 * (1 - t)) := Real.sqrt_pos.mpr (by linarith [ht.2, t0_lt_one])
      exact mul_ne_zero (by norm_num : (4 : ℝ) ≠ 0) hsq.ne'
    have hi1 : IntegrableOn (fun t => Q.u (1, 1 - t) * rho 1 (1 - t)) (Ioo (0 : ℝ) t0) volume :=
      ((Q.u_continuousOn.comp (f := fun t : ℝ => ((1 : ℝ), 1 - t))
        (continuous_const.prodMk (continuous_const.sub continuous_id)).continuousOn
        (fun t ht => ⟨⟨zero_le_one, le_rfl⟩, ⟨by linarith [ht.2, t0_lt_one], by linarith [ht.1]⟩⟩)).mul
        hc_rho).integrableOn_Icc.mono_set Ioo_subset_Icc_self
    have hi2 : IntegrableOn (fun t => linearHalfProfile.u (1, 1 - t) * rho 1 (1 - t)) (Ioo (0 : ℝ) t0) volume :=
      ((linearHalfProfile.u_continuousOn.comp (f := fun t : ℝ => ((1 : ℝ), 1 - t))
        (continuous_const.prodMk (continuous_const.sub continuous_id)).continuousOn
        (fun t ht => ⟨⟨zero_le_one, le_rfl⟩, ⟨by linarith [ht.2, t0_lt_one], by linarith [ht.1]⟩⟩)).mul
        hc_rho).integrableOn_Icc.mono_set Ioo_subset_Icc_self
    rw [← integral_sub hi1 hi2, ← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioo (fun t _ => by dsimp only [w, linearHalfProfile]; ring)
  linear_combination h1 - h2 + L * hDg_sub + 2 * hw_sub + hwbdy_sub

end

end EconCSAuction
