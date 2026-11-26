import AuctionSep.Solution

/-!
# Symmetric Ex-Post IR & No-Subsidy (NPT) BIC–DSIC Separation

Replaces the flat interim tariff of `BICWitness.M_bic` by the standard nonnegative ratio payment
rule `t1(x, y) = (T1(x) / ev(x)) * (x₁ q₁₁(x, y) + x₂ q₁₂(x, y))` (using Lean's `a / 0 = 0`
convention when `ev(x) = 0`), where `ev(x) = ∫ y in unitSquare, (x₁ q₁₁(x, y) + x₂ q₁₂(x, y))`.

Because every raw interim payment in `CertData.t1Int` is nonnegative and `M_bic` satisfies
`IsInterimIR`, the ratio `λ(x) = T1(x) / ev(x)` satisfies `0 ≤ λ(x) ≤ 1` for all `x ∈ [0, 1]²`.
Consequently the adjusted mechanism `M_bic_exPostIR` preserves interim payments, BIC, feasibility,
and expected revenue `62105 / 69984`, while simultaneously satisfying:
- symmetric `IsExPostIR` (in expectation over internal randomization), and
- pointwise No Positive Transfers (`0 ≤ t1 x y ∧ 0 ≤ t2 x y`, zero cash subsidies).
-/

open MeasureTheory Set AuctionSep AuctionSep.CertData AuctionSep.BICWitness AuctionSep.MeasureLemmas

namespace AuctionSep

noncomputable section

private def t1NonnegCheck : Bool :=
  range6All fun i => range6All fun j => range2All fun k => decide (0 ≤ t1Int i j k)

private theorem t1NonnegCheck_true : t1NonnegCheck = true := by decide

private lemma t1Int_nonneg {i j k : ℕ} (hi : i < 6) (hj : j < 6) (hk : k < 2) :
    (0 : Int) ≤ t1Int i j k := by
  have h := of_range2All (of_range6All (of_range6All t1NonnegCheck_true hi) hj) hk
  simpa [decide_eq_true_eq] using h

private lemma T1_W_nonneg (x : Type2) : 0 ≤ T1 M_bic x := by
  rw [T1_M_bic]
  unfold t1Val
  have h : (0 : ℝ) ≤ (t1Int (cell6 x.1) (cell6 x.2) (kind6 x) : ℝ) := by
    exact_mod_cast t1Int_nonneg (cell6_lt x.1) (cell6_lt x.2) (kind6_lt x)
  linarith

private abbrev W := M_bic

private def v (x y : Type2) : ℝ :=
  x.1 * W.q11 x y + x.2 * W.q12 x y

private def ev (x : Type2) : ℝ :=
  ∫ y in unitSquare, v x y

/-- Ratio payment factor `λ(x) = T1(x) / ev(x)` (equals `0` when `ev(x) = 0` in Lean's `ℝ`). -/
private def lam (x : Type2) : ℝ :=
  T1 W x / ev x

private def transfer (x y : Type2) : ℝ :=
  lam x * v x y

private lemma v_nonneg {x y : Type2} (hx : x ∈ unitSquare) (hy : y ∈ unitSquare) :
    0 ≤ v x y := by
  have hf := M_bic_feasible.1 x hx y hy
  unfold v
  exact add_nonneg (mul_nonneg hx.1.1 hf.1) (mul_nonneg hx.2.1 hf.2.2.2.1)

private lemma v_le_two {x y : Type2} (hx : x ∈ unitSquare) (hy : y ∈ unitSquare) :
    v x y ≤ 2 := by
  have hf := M_bic_feasible.1 x hx y hy
  have hb₁ : W.q11 x y ≤ 1 := by linarith [hf.2.1, hf.2.2.1]
  have hb₂ : W.q12 x y ≤ 1 := by linarith [hf.2.2.2.2.1, hf.2.2.2.2.2]
  have h₁ := mul_le_mul hx.1.2 hb₁ hf.1 (by norm_num : 0 ≤ (1 : ℝ))
  have h₂ := mul_le_mul hx.2.2 hb₂ hf.2.2.2.1 (by norm_num : 0 ≤ (1 : ℝ))
  unfold v
  linarith

private lemma sliceV {x : Type2} (hx : x ∈ unitSquare) :
    IntegrableOn (v x) unitSquare volume := by
  have h := M_bic_isBIC.1 x hx
  exact (h.1.const_mul _).add (h.2.1.const_mul _)

private lemma ev_eq {x : Type2} (hx : x ∈ unitSquare) :
    ev x = x.1 * Q11 W x + x.2 * Q12 W x := by
  have h := M_bic_isBIC.1 x hx
  unfold ev v Q11 Q12
  rw [integral_add (h.1.const_mul _) (h.2.1.const_mul _), integral_const_mul, integral_const_mul]

private lemma ev_nonneg {x : Type2} (hx : x ∈ unitSquare) : 0 ≤ ev x := by
  unfold ev
  exact setIntegral_nonneg measurableSet_unitSquare (fun y hy => v_nonneg hx hy)

private lemma T1_le_ev {x : Type2} (hx : x ∈ unitSquare) : T1 W x ≤ ev x := by
  have hi := M_bic_isInterimIR.1 x hx
  rw [← ev_eq hx] at hi
  linarith

private lemma lam_nonneg {x : Type2} (hx : x ∈ unitSquare) : 0 ≤ lam x :=
  div_nonneg (T1_W_nonneg x) (ev_nonneg hx)

private lemma lam_le_one {x : Type2} (hx : x ∈ unitSquare) : lam x ≤ 1 := by
  unfold lam
  by_cases h0 : ev x = 0
  · simp [h0]
  · exact (div_le_one (lt_of_le_of_ne (ev_nonneg hx) (Ne.symm h0))).mpr (T1_le_ev hx)

private lemma jointV :
    IntegrableOn (fun p : Type2 × Type2 => v p.1 p.2) profileDomain volume := by
  apply DSICBound.integrableOn_bdd_profileDomain (C := 2)
  · have hm₁ : Measurable (fun p : Type2 × Type2 => p.1.1) := measurable_fst.comp measurable_fst
    have hm₂ : Measurable (fun p : Type2 × Type2 => p.1.2) := measurable_snd.comp measurable_fst
    exact (hm₁.aestronglyMeasurable.mul M_bic_feasible.2.1.aestronglyMeasurable).add
      (hm₂.aestronglyMeasurable.mul M_bic_feasible.2.2.1.aestronglyMeasurable)
  · intro p hp
    rw [abs_of_nonneg (v_nonneg hp.1 hp.2)]
    exact v_le_two hp.1 hp.2

private lemma lam_integrableOn_unitSquare :
    IntegrableOn lam unitSquare volume := by
  have hv := jointV
  unfold IntegrableOn profileDomain at hv
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at hv
  have hev : IntegrableOn ev unitSquare volume := hv.integral_prod_left
  have ht1 : IntegrableOn (fun p : Type2 × Type2 => W.t1 p.1 p.2) profileDomain volume :=
    M_bic_feasible.2.2.2.2.2.1
  unfold IntegrableOn profileDomain at ht1
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at ht1
  have hT1 : IntegrableOn (T1 W) unitSquare volume := ht1.integral_prod_left
  have hmeas : AEStronglyMeasurable lam (volume.restrict unitSquare) :=
    (hT1.aestronglyMeasurable.aemeasurable.div hev.aestronglyMeasurable.aemeasurable).aestronglyMeasurable
  have hbound : ∀ᵐ x ∂(volume.restrict unitSquare), ‖lam x‖ ≤ (1 : ℝ) := by
    rw [ae_restrict_iff' measurableSet_unitSquare]
    filter_upwards with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (lam_nonneg hx)]
    exact lam_le_one hx
  have hfin : IsFiniteMeasure (volume.restrict unitSquare) :=
    ⟨by rw [Measure.restrict_apply_univ, volume_unitSquare]; exact ENNReal.one_lt_top⟩
  exact Integrable.of_bound hmeas 1 hbound

private lemma jointT :
    IntegrableOn (fun p : Type2 × Type2 => transfer p.1 p.2) profileDomain volume := by
  have hlam_prod : IntegrableOn (fun p : Type2 × Type2 => lam p.1) profileDomain volume :=
    integrableOn_fst_of_prod lam_integrableOn_unitSquare (by simp [volume_unitSquare])
  apply DSICBound.integrableOn_bdd_profileDomain (C := 2)
  · exact hlam_prod.aestronglyMeasurable.mul jointV.aestronglyMeasurable
  · intro p hp
    have hnn : 0 ≤ transfer p.1 p.2 := mul_nonneg (lam_nonneg hp.1) (v_nonneg hp.1 hp.2)
    have hle : transfer p.1 p.2 ≤ v p.1 p.2 := by
      calc transfer p.1 p.2 = lam p.1 * v p.1 p.2 := rfl
        _ ≤ 1 * v p.1 p.2 := mul_le_mul_of_nonneg_right (lam_le_one hp.1) (v_nonneg hp.1 hp.2)
        _ = v p.1 p.2 := one_mul _
    rw [abs_of_nonneg hnn]
    exact hle.trans (v_le_two hp.1 hp.2)

private lemma sliceT {x : Type2} (hx : x ∈ unitSquare) :
    IntegrableOn (transfer x) unitSquare volume :=
  (sliceV hx).const_mul (lam x)

private lemma interim {x : Type2} (hx : x ∈ unitSquare) :
    (∫ y in unitSquare, transfer x y) = T1 W x := by
  unfold transfer
  rw [integral_const_mul]
  change lam x * ev x = T1 W x
  unfold lam
  by_cases h0 : ev x = 0
  · have hT0 : T1 W x = 0 := le_antisymm (h0 ▸ T1_le_ev hx) (T1_W_nonneg x)
    simp [h0, hT0]
  · exact div_mul_cancel₀ (T1 W x) h0

/-- No-subsidy, symmetric ex-post IR BIC witness with the same allocations and revenue as `M_bic`. -/
def M_bic_exPostIR : Mechanism :=
  { W with t1 := transfer, t2 := fun x y => transfer y x }

private lemma M_bic_exPostIR_feasible : IsFeasible M_bic_exPostIR := by
  have ht := jointT
  unfold IntegrableOn profileDomain at ht
  have hs : IntegrableOn (fun p : Type2 × Type2 => transfer p.2 p.1) profileDomain volume := by
    unfold IntegrableOn profileDomain
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at ht ⊢
    exact Measure.measurePreserving_swap.integrable_comp_of_integrable ht
  exact ⟨M_bic_feasible.1, M_bic_feasible.2.1, M_bic_feasible.2.2.1, M_bic_feasible.2.2.2.1,
    M_bic_feasible.2.2.2.2.1, jointT, hs⟩

private lemma M_bic_exPostIR_isBIC : IsBIC M_bic_exPostIR := by
  refine ⟨fun x hx => ⟨(M_bic_isBIC.1 x hx).1, (M_bic_isBIC.1 x hx).2.1, sliceT hx⟩,
    fun y hy => ⟨(M_bic_isBIC.2.1 y hy).1, (M_bic_isBIC.2.1 y hy).2.1, sliceT hy⟩, ?_, ?_⟩
  · intro x hx r hr
    change _ - (∫ y in unitSquare, transfer r y) ≤ _ - (∫ y in unitSquare, transfer x y)
    rw [interim hr, interim hx]
    exact M_bic_isBIC.2.2.1 x hx r hr
  · intro y hy r hr
    change _ - (∫ x in unitSquare, transfer r x) ≤ _ - (∫ x in unitSquare, transfer y x)
    rw [interim hr, interim hy]
    exact M_bic_isBIC.2.2.2 y hy r hr

private lemma M_bic_exPostIR_isExPostIR : IsExPostIR M_bic_exPostIR := by
  intro x hx y hy
  have h (r s : Type2) (hr : r ∈ unitSquare) (hs : s ∈ unitSquare) :
      0 ≤ v r s - transfer r s := by
    have hle : transfer r s ≤ v r s := by
      calc transfer r s = lam r * v r s := rfl
        _ ≤ 1 * v r s := mul_le_mul_of_nonneg_right (lam_le_one hr) (v_nonneg hr hs)
        _ = v r s := one_mul _
    linarith
  exact ⟨h x y hx hy, h y x hy hx⟩

private lemma M_bic_exPostIR_noSubsidy :
    ∀ x ∈ unitSquare, ∀ y ∈ unitSquare,
      0 ≤ M_bic_exPostIR.t1 x y ∧ 0 ≤ M_bic_exPostIR.t2 x y := by
  intro x hx y hy
  exact ⟨mul_nonneg (lam_nonneg hx) (v_nonneg hx hy),
         mul_nonneg (lam_nonneg hy) (v_nonneg hy hx)⟩

private lemma M_bic_exPostIR_revenue : ExpectedRevenue M_bic_exPostIR = ExpectedRevenue W := by
  unfold ExpectedRevenue
  rw [integral_add M_bic_exPostIR_feasible.2.2.2.2.2.1 M_bic_exPostIR_feasible.2.2.2.2.2.2,
      integral_add M_bic_feasible.2.2.2.2.2.1 M_bic_feasible.2.2.2.2.2.2]
  unfold profileDomain
  apply congrArg₂ (· + ·)
  · rw [setIntegral_prod_eq M_bic_exPostIR_feasible.2.2.2.2.2.1,
        setIntegral_prod_eq M_bic_feasible.2.2.2.2.2.1]
    exact setIntegral_congr_fun measurableSet_unitSquare (fun _ hx => interim hx)
  · rw [setIntegral_prod_symm_eq M_bic_exPostIR_feasible.2.2.2.2.2.2,
        setIntegral_prod_symm_eq M_bic_feasible.2.2.2.2.2.2]
    exact setIntegral_congr_fun measurableSet_unitSquare (fun _ hy => interim hy)

/--
Any feasible, DSIC, interim-IR mechanism satisfies `ExpectedRevenue M ≤ 2324277 / 2621440`.

Proof: For any `δ > 0`, set `ε = min (δ / 4) 1 ∈ (0, 1]`. On the positive-measure corner
`S = [0, ε]² ⊆ [0, 1]²`, Fubini yields types `x₀, y₀ ∈ S` whose allocation and payment slices are
integrable on `unitSquare`. Shifting transfers by `-M.t1 x₀ y` and `-M.t2 x y₀` preserves
feasibility and DSIC, enforces `IsExPostIR` via `u1Report M x x₀ y ≤ u1Report M x x y`, and shifts
expected revenue by `T1 M x₀ + T2 M y₀ ≤ 4 * ε ≤ δ`. Applying `DSICBound.dsic_expectedRevenue_le`
and letting `δ → 0⁺` yields the bound.
-/
theorem dsic_interimIR_expectedRevenue_le (M : Mechanism)
    (hF : IsFeasible M) (hD : IsDSIC M) (hIR : IsInterimIR M) :
    ExpectedRevenue M ≤ 2324277 / 2621440 := by
  apply le_of_forall_pos_le_add
  intro δ hδ
  set ε : ℝ := min (δ / 4) 1
  have hε_pos : 0 < ε := lt_min (by linarith) zero_lt_one
  have hε_le1 : ε ≤ 1 := min_le_right _ _
  have h4ε : 4 * ε ≤ δ := by
    have : ε ≤ δ / 4 := min_le_left _ _
    linarith
  let S : Set Type2 := Icc (0 : ℝ) ε ×ˢ Icc (0 : ℝ) ε
  have hS_sub : S ⊆ unitSquare := Set.prod_mono (Icc_subset_Icc_right hε_le1) (Icc_subset_Icc_right hε_le1)
  have hS_vol : volume S ≠ 0 := by
    have hI : volume (Icc (0 : ℝ) ε) ≠ 0 := by
      rw [Real.volume_Icc, sub_zero]
      exact (ENNReal.ofReal_pos.mpr hε_pos).ne'
    dsimp [S]
    rw [Measure.volume_eq_prod, Measure.prod_prod]
    exact mul_ne_zero hI hI
  have hS_restrict_ne : (volume.restrict unitSquare) S ≠ 0 := by
    rw [Measure.restrict_apply' measurableSet_unitSquare, inter_eq_left.mpr hS_sub]
    exact hS_vol
  have exists_in_S {P : Type2 → Prop}
      (hP : ∀ᵐ z ∂(volume.restrict unitSquare), P z) : ∃ z ∈ S, P z := by
    by_contra hno
    push Not at hno
    have hsub : S ⊆ {z | ¬ P z} := fun z hz => hno z hz
    have hle : (volume.restrict unitSquare) S ≤ (volume.restrict unitSquare) {z | ¬ P z} :=
      measure_mono hsub
    have hzero : (volume.restrict unitSquare) {z | ¬ P z} = 0 := by
      simpa [ae_iff] using hP
    exact hS_restrict_ne (le_antisymm (hle.trans hzero.le) bot_le)
  have hae1 : ∀ᵐ x ∂(volume.restrict unitSquare),
      IntegrableOn (fun y => M.t1 x y) unitSquare volume ∧
      IntegrableOn (fun y => M.q11 x y) unitSquare volume ∧
      IntegrableOn (fun y => M.q12 x y) unitSquare volume :=
    (ae_integrableOn_prod_right hF.2.2.2.2.2.1).and
      ((ae_integrableOn_prod_right hF.2.1).and (ae_integrableOn_prod_right hF.2.2.1))
  have hae2 : ∀ᵐ y ∂(volume.restrict unitSquare),
      IntegrableOn (fun x => M.t2 x y) unitSquare volume ∧
      IntegrableOn (fun x => M.q21 x y) unitSquare volume ∧
      IntegrableOn (fun x => M.q22 x y) unitSquare volume :=
    (ae_integrableOn_prod_left hF.2.2.2.2.2.2).and
      ((ae_integrableOn_prod_left hF.2.2.2.1).and (ae_integrableOn_prod_left hF.2.2.2.2.1))
  obtain ⟨x₀, hx₀S, ht1_x₀, hq11_x₀, hq12_x₀⟩ := exists_in_S hae1
  obtain ⟨y₀, hy₀S, ht2_y₀, hq21_y₀, hq22_y₀⟩ := exists_in_S hae2
  have hx₀ : x₀ ∈ unitSquare := hS_sub hx₀S
  have hy₀ : y₀ ∈ unitSquare := hS_sub hy₀S
  let M' : Mechanism :=
    { M with
      t1 := fun x y => M.t1 x y - M.t1 x₀ y
      t2 := fun x y => M.t2 x y - M.t2 x y₀ }
  have hshift1_int : IntegrableOn (fun p : Type2 × Type2 => M.t1 x₀ p.2) profileDomain volume :=
    integrableOn_snd_of_prod (by simp [volume_unitSquare]) ht1_x₀
  have hshift2_int : IntegrableOn (fun p : Type2 × Type2 => M.t2 p.1 y₀) profileDomain volume :=
    integrableOn_fst_of_prod ht2_y₀ (by simp [volume_unitSquare])
  have hF' : IsFeasible M' :=
    ⟨hF.1, hF.2.1, hF.2.2.1, hF.2.2.2.1, hF.2.2.2.2.1,
     hF.2.2.2.2.2.1.sub hshift1_int, hF.2.2.2.2.2.2.sub hshift2_int⟩
  have hD' : IsDSIC M' := by
    refine ⟨?_, ?_⟩
    · intro x hx x' hx' y hy
      have h := hD.1 x hx x' hx' y hy
      unfold u1Report at h ⊢
      dsimp only [M']
      linarith
    · intro x hx y hy y' hy'
      have h := hD.2 x hx y hy y' hy'
      unfold u2Report at h ⊢
      dsimp only [M']
      linarith
  have hIR' : IsExPostIR M' := by
    intro x hx y hy
    refine ⟨?_, ?_⟩
    · have hd := hD.1 x hx x₀ hx₀ y hy
      have hf := hF.1 x₀ hx₀ y hy
      have hv : 0 ≤ x.1 * M.q11 x₀ y + x.2 * M.q12 x₀ y :=
        add_nonneg (mul_nonneg hx.1.1 hf.1) (mul_nonneg hx.2.1 hf.2.2.2.1)
      unfold u1Report at hd ⊢
      dsimp only [M']
      linarith
    · have hd := hD.2 x hx y hy y₀ hy₀
      have hf := hF.1 x hx y₀ hy₀
      have hv : 0 ≤ y.1 * M.q21 x y₀ + y.2 * M.q22 x y₀ :=
        add_nonneg (mul_nonneg hy.1.1 hf.2.1) (mul_nonneg hy.2.1 hf.2.2.2.2.1)
      unfold u2Report at hd ⊢
      dsimp only [M']
      linarith
  have hrev' : ExpectedRevenue M' ≤ 2324277 / 2621440 :=
    DSICBound.dsic_expectedRevenue_le M' hF' hD' hIR'
  have hI1 : (∫ p in profileDomain, M.t1 x₀ p.2) = T1 M x₀ := by
    unfold profileDomain T1
    rw [setIntegral_prod_eq hshift1_int]
    dsimp only
    rw [setIntegral_const, volume_real_unitSquare, one_smul]
  have hI2 : (∫ p in profileDomain, M.t2 p.1 y₀) = T2 M y₀ := by
    unfold profileDomain T2
    rw [setIntegral_prod_symm_eq hshift2_int]
    dsimp only
    rw [setIntegral_const, volume_real_unitSquare, one_smul]
  have hrev_eq : ExpectedRevenue M' = ExpectedRevenue M - T1 M x₀ - T2 M y₀ := by
    unfold ExpectedRevenue M'
    dsimp only
    rw [integral_add hF'.2.2.2.2.2.1 hF'.2.2.2.2.2.2,
        integral_sub hF.2.2.2.2.2.1 hshift1_int,
        integral_sub hF.2.2.2.2.2.2 hshift2_int,
        hI1, hI2,
        integral_add hF.2.2.2.2.2.1 hF.2.2.2.2.2.2]
    ring
  have hconst1 : IntegrableOn (fun _ : Type2 => (1 : ℝ)) unitSquare volume :=
    integrableOn_const_of_subset_unitSquare Subset.rfl 1
  have hQ11 : Q11 M x₀ ≤ 1 := by
    unfold Q11
    calc ∫ y in unitSquare, M.q11 x₀ y
        ≤ ∫ _ in unitSquare, (1 : ℝ) := by
          apply setIntegral_mono_on hq11_x₀ hconst1 measurableSet_unitSquare
          intro y hy
          have hf := hF.1 x₀ hx₀ y hy
          linarith [hf.2.1, hf.2.2.1]
      _ = 1 := by simp [volume_real_unitSquare]
  have hQ12 : Q12 M x₀ ≤ 1 := by
    unfold Q12
    calc ∫ y in unitSquare, M.q12 x₀ y
        ≤ ∫ _ in unitSquare, (1 : ℝ) := by
          apply setIntegral_mono_on hq12_x₀ hconst1 measurableSet_unitSquare
          intro y hy
          have hf := hF.1 x₀ hx₀ y hy
          linarith [hf.2.2.2.2.1, hf.2.2.2.2.2]
      _ = 1 := by simp [volume_real_unitSquare]
  have hQ21 : Q21 M y₀ ≤ 1 := by
    unfold Q21
    calc ∫ x in unitSquare, M.q21 x y₀
        ≤ ∫ _ in unitSquare, (1 : ℝ) := by
          apply setIntegral_mono_on hq21_y₀ hconst1 measurableSet_unitSquare
          intro x hx
          have hf := hF.1 x hx y₀ hy₀
          linarith [hf.1, hf.2.2.1]
      _ = 1 := by simp [volume_real_unitSquare]
  have hQ22 : Q22 M y₀ ≤ 1 := by
    unfold Q22
    calc ∫ x in unitSquare, M.q22 x y₀
        ≤ ∫ _ in unitSquare, (1 : ℝ) := by
          apply setIntegral_mono_on hq22_y₀ hconst1 measurableSet_unitSquare
          intro x hx
          have hf := hF.1 x hx y₀ hy₀
          linarith [hf.2.2.2.1, hf.2.2.2.2.2]
      _ = 1 := by simp [volume_real_unitSquare]
  have hT1_le : T1 M x₀ ≤ 2 * ε := by
    have h0 := hIR.1 x₀ hx₀
    have h1 : x₀.1 * Q11 M x₀ ≤ ε := by
      calc x₀.1 * Q11 M x₀ ≤ x₀.1 * 1 := mul_le_mul_of_nonneg_left hQ11 hx₀S.1.1
        _ = x₀.1 := mul_one _
        _ ≤ ε := hx₀S.1.2
    have h2 : x₀.2 * Q12 M x₀ ≤ ε := by
      calc x₀.2 * Q12 M x₀ ≤ x₀.2 * 1 := mul_le_mul_of_nonneg_left hQ12 hx₀S.2.1
        _ = x₀.2 := mul_one _
        _ ≤ ε := hx₀S.2.2
    linarith
  have hT2_le : T2 M y₀ ≤ 2 * ε := by
    have h0 := hIR.2 y₀ hy₀
    have h1 : y₀.1 * Q21 M y₀ ≤ ε := by
      calc y₀.1 * Q21 M y₀ ≤ y₀.1 * 1 := mul_le_mul_of_nonneg_left hQ21 hy₀S.1.1
        _ = y₀.1 := mul_one _
        _ ≤ ε := hy₀S.1.2
    have h2 : y₀.2 * Q22 M y₀ ≤ ε := by
      calc y₀.2 * Q22 M y₀ ≤ y₀.2 * 1 := mul_le_mul_of_nonneg_left hQ22 hy₀S.2.1
        _ = y₀.2 := mul_one _
        _ ≤ ε := hy₀S.2.2
    linarith
  linarith

/--
Full Zero-Asterisk BIC–DSIC Separation Theorem for `2×2` i.i.d. `U[0,1]`:
There exists a feasible, BIC, ex-post-IR mechanism `M_bic` with nonnegative transfers everywhere
(`0 ≤ t1 ∧ 0 ≤ t2`), a ratio payment factor `lam : Type2 → ℝ` in `[0, 1]` supporting nonnegative
ex-post-IR payments on every realized deterministic bundle `(b1, b2) ≥ 0`, and expected revenue
`62105 / 69984`, strictly exceeding `c = 2324277 / 2621440`, such that EVERY feasible DSIC mechanism
`M_dsic` satisfying EITHER `IsExPostIR M_dsic` OR `IsInterimIR M_dsic` has `ExpectedRevenue M_dsic ≤ c`.
-/
theorem main_theorem_equal_ex_post_ir :
    ∃ (M_bic : Mechanism) (lam : Type2 → ℝ) (c : ℝ),
      IsFeasible M_bic ∧ IsBIC M_bic ∧ IsExPostIR M_bic ∧
      (∀ x ∈ unitSquare, ∀ y ∈ unitSquare, 0 ≤ M_bic.t1 x y ∧ 0 ≤ M_bic.t2 x y) ∧
      (∀ x ∈ unitSquare, 0 ≤ lam x ∧ lam x ≤ 1) ∧
      (∀ x ∈ unitSquare, ∀ y ∈ unitSquare,
        M_bic.t1 x y = lam x * (x.1 * M_bic.q11 x y + x.2 * M_bic.q12 x y) ∧
        M_bic.t2 x y = lam y * (y.1 * M_bic.q21 x y + y.2 * M_bic.q22 x y)) ∧
      (∀ x ∈ unitSquare, ∀ b1 b2 : ℝ, 0 ≤ b1 → 0 ≤ b2 →
        0 ≤ lam x * (x.1 * b1 + x.2 * b2) ∧
        lam x * (x.1 * b1 + x.2 * b2) ≤ x.1 * b1 + x.2 * b2) ∧
      ExpectedRevenue M_bic = 62105 / 69984 ∧
      c = 2324277 / 2621440 ∧
      c < ExpectedRevenue M_bic ∧
      ∀ M_dsic : Mechanism,
        IsFeasible M_dsic → IsDSIC M_dsic → (IsExPostIR M_dsic ∨ IsInterimIR M_dsic) →
          ExpectedRevenue M_dsic ≤ c := by
  refine ⟨M_bic_exPostIR, lam, 2324277 / 2621440, M_bic_exPostIR_feasible, M_bic_exPostIR_isBIC,
    M_bic_exPostIR_isExPostIR, M_bic_exPostIR_noSubsidy,
    fun x hx => ⟨lam_nonneg hx, lam_le_one hx⟩,
    fun _ _ _ _ => ⟨rfl, rfl⟩,
    ?_,
    M_bic_exPostIR_revenue.trans M_bic_expectedRevenue, rfl, ?_, ?_⟩
  · intro x hx b1 b2 hb1 hb2
    have hval : 0 ≤ x.1 * b1 + x.2 * b2 :=
      add_nonneg (mul_nonneg hx.1.1 hb1) (mul_nonneg hx.2.1 hb2)
    refine ⟨mul_nonneg (lam_nonneg hx) hval, ?_⟩
    calc lam x * (x.1 * b1 + x.2 * b2) ≤ 1 * (x.1 * b1 + x.2 * b2) :=
          mul_le_mul_of_nonneg_right (lam_le_one hx) hval
      _ = x.1 * b1 + x.2 * b2 := one_mul _
  · rw [M_bic_exPostIR_revenue.trans M_bic_expectedRevenue]
    norm_num
  · intro D hF hD hIR
    rcases hIR with hEx | hInt
    · exact DSICBound.dsic_expectedRevenue_le D hF hD hEx
    · exact dsic_interimIR_expectedRevenue_le D hF hD hInt

end

end AuctionSep
