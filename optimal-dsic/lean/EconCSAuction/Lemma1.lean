import EconCSAuction.MeasureHelpers

/-!
# Lemma 1: WLOG Single-Item Reduction & DSIC ⊆ BIC

Proves that any measurable randomized 4-bundle unit-demand mechanism `(g, p)` can be reduced
to a feasible single-item mechanism `(g̃, p)` (`q1_12 = q2_12 = 0`, so allocations lie in the
`2 × 2` doubly substochastic `K_{2,2}` matching polytope) preserving exact expected revenue,
feasibility, DSIC, ex-post IR, BIC, and interim IR. Also proves unconditionally that every
feasible DSIC + ex-post IR mechanism (for `L ≥ 0`) is BIC + interim IR.
-/

open MeasureTheory Set

namespace EconCSAuction

noncomputable section

/-- Single-item reduction of an arbitrary randomized 4-bundle unit-demand mechanism:
whenever bundle `{1, 2}` is allocated at bid `b_i`, assign only `argmax_{j} b_{ij}`
(breaking ties toward item 1) and keep transfers unchanged. -/
def reduceSingleItem (M : Mechanism) : Mechanism where
  q1_1  b1 b2 := M.q1_1  b1 b2 + if b1.2 ≤ b1.1 then M.q1_12 b1 b2 else 0
  q1_2  b1 b2 := M.q1_2  b1 b2 + if b1.2 ≤ b1.1 then 0 else M.q1_12 b1 b2
  q1_12 _  _  := 0
  q2_1  b1 b2 := M.q2_1  b1 b2 + if b2.2 ≤ b2.1 then M.q2_12 b1 b2 else 0
  q2_2  b1 b2 := M.q2_2  b1 b2 + if b2.2 ≤ b2.1 then 0 else M.q2_12 b1 b2
  q2_12 _  _  := 0
  p1    := M.p1
  p2    := M.p2

lemma reduceSingleItem_isSingleItem (M : Mechanism) : IsSingleItem (reduceSingleItem M) :=
  ⟨fun _ _ => rfl, fun _ _ => rfl⟩

lemma reduceSingleItem_expectedRevenue (L : ℝ) (M : Mechanism) :
    ExpectedRevenue L (reduceSingleItem M) = ExpectedRevenue L M :=
  rfl

lemma unitDemandVal_reduce_eq (v : Type2) (q1 q2 q12 : ℝ) :
    UnitDemandVal v (q1 + if v.2 ≤ v.1 then q12 else 0) (q2 + if v.2 ≤ v.1 then 0 else q12) 0 =
      UnitDemandVal v q1 q2 q12 := by
  unfold UnitDemandVal
  split_ifs with h
  · rw [max_eq_left h]; ring
  · rw [max_eq_right (le_of_not_ge h)]; ring

lemma unitDemandVal_reduce_le (v b : Type2) (q1 q2 q12 : ℝ) (hq12 : 0 ≤ q12) :
    UnitDemandVal v (q1 + if b.2 ≤ b.1 then q12 else 0) (q2 + if b.2 ≤ b.1 then 0 else q12) 0 ≤
      UnitDemandVal v q1 q2 q12 := by
  unfold UnitDemandVal
  split_ifs with h
  · have h1 : v.1 ≤ max v.1 v.2 := le_max_left v.1 v.2
    nlinarith
  · have h2 : v.2 ≤ max v.1 v.2 := le_max_right v.1 v.2
    nlinarith

lemma reduceSingleItem_isFeasible {L : ℝ} {M : Mechanism} (hF : IsFeasible L M) :
    IsFeasible L (reduceSingleItem M) := by
  rcases hF with ⟨hpt, hm11, hm12, hm112, hm21, hm22, hm212, hmp1, hmp2, hip1, hip2⟩
  refine ⟨?_, ?_, ?_, measurable_const, ?_, ?_, measurable_const, hmp1, hmp2, hip1, hip2⟩
  · intro v1 hv1 v2 hv2
    rcases hpt v1 hv1 v2 hv2 with ⟨h11, h12, h112, h21, h22, h212, hs1, hs2, hi1, hi2⟩
    dsimp only [reduceSingleItem]
    have ha1 : 0 ≤ (if v1.2 ≤ v1.1 then M.q1_12 v1 v2 else 0) := by split_ifs <;> linarith
    have ha2 : 0 ≤ (if v1.2 ≤ v1.1 then 0 else M.q1_12 v1 v2) := by split_ifs <;> linarith
    have hb1 : 0 ≤ (if v2.2 ≤ v2.1 then M.q2_12 v1 v2 else 0) := by split_ifs <;> linarith
    have hb2 : 0 ≤ (if v2.2 ≤ v2.1 then 0 else M.q2_12 v1 v2) := by split_ifs <;> linarith
    have ha1_le : (if v1.2 ≤ v1.1 then M.q1_12 v1 v2 else 0) ≤ M.q1_12 v1 v2 := by split_ifs <;> linarith
    have ha2_le : (if v1.2 ≤ v1.1 then 0 else M.q1_12 v1 v2) ≤ M.q1_12 v1 v2 := by split_ifs <;> linarith
    have hb1_le : (if v2.2 ≤ v2.1 then M.q2_12 v1 v2 else 0) ≤ M.q2_12 v1 v2 := by split_ifs <;> linarith
    have hb2_le : (if v2.2 ≤ v2.1 then 0 else M.q2_12 v1 v2) ≤ M.q2_12 v1 v2 := by split_ifs <;> linarith
    have hasum : (if v1.2 ≤ v1.1 then M.q1_12 v1 v2 else 0) +
        (if v1.2 ≤ v1.1 then 0 else M.q1_12 v1 v2) = M.q1_12 v1 v2 := by split_ifs <;> ring
    have hbsum : (if v2.2 ≤ v2.1 then M.q2_12 v1 v2 else 0) +
        (if v2.2 ≤ v2.1 then 0 else M.q2_12 v1 v2) = M.q2_12 v1 v2 := by split_ifs <;> ring
    refine ⟨by linarith, by linarith, le_rfl, by linarith, by linarith, le_rfl,
      by linarith, by linarith, by linarith, by linarith⟩
  · have hpred : MeasurableSet {p : Type2 × Type2 | p.1.2 ≤ p.1.1} :=
      measurableSet_le (measurable_snd.comp measurable_fst) (measurable_fst.comp measurable_fst)
    exact hm11.add (Measurable.ite hpred hm112 measurable_const)
  · have hpred : MeasurableSet {p : Type2 × Type2 | p.1.2 ≤ p.1.1} :=
      measurableSet_le (measurable_snd.comp measurable_fst) (measurable_fst.comp measurable_fst)
    exact hm12.add (Measurable.ite hpred measurable_const hm112)
  · have hpred : MeasurableSet {p : Type2 × Type2 | p.2.2 ≤ p.2.1} :=
      measurableSet_le (measurable_snd.comp measurable_snd) (measurable_fst.comp measurable_snd)
    exact hm21.add (Measurable.ite hpred hm212 measurable_const)
  · have hpred : MeasurableSet {p : Type2 × Type2 | p.2.2 ≤ p.2.1} :=
      measurableSet_le (measurable_snd.comp measurable_snd) (measurable_fst.comp measurable_snd)
    exact hm22.add (Measurable.ite hpred measurable_const hm212)

/-- Every allocation slice of a feasible mechanism is integrable under `bidderMeasure L`. -/
lemma slice_q_integrable {L : ℝ} {M : Mechanism} (hF : IsFeasible L M) :
    (∀ b1 ∈ bidderDomain L,
      Integrable (fun b2 => M.q1_1 b1 b2) (bidderMeasure L) ∧
      Integrable (fun b2 => M.q1_2 b1 b2) (bidderMeasure L) ∧
      Integrable (fun b2 => M.q1_12 b1 b2) (bidderMeasure L)) ∧
    (∀ b2 ∈ bidderDomain L,
      Integrable (fun b1 => M.q2_1 b1 b2) (bidderMeasure L) ∧
      Integrable (fun b1 => M.q2_2 b1 b2) (bidderMeasure L) ∧
      Integrable (fun b1 => M.q2_12 b1 b2) (bidderMeasure L)) := by
  rcases hF with ⟨hpt, hm11, hm12, hm112, hm21, hm22, hm212, _, _, _, _⟩
  refine ⟨fun b1 hb1 => ⟨?_, ?_, ?_⟩, fun b2 hb2 => ⟨?_, ?_, ?_⟩⟩
  · refine integrable_of_bounded_bidderMeasure (C := 1)
      (hm11.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable ?_
    intro b2 hb2
    rcases hpt b1 hb1 b2 hb2 with ⟨h11, h12, h112, _, _, _, hs1, _, _, _⟩
    rw [abs_of_nonneg h11]; linarith
  · refine integrable_of_bounded_bidderMeasure (C := 1)
      (hm12.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable ?_
    intro b2 hb2
    rcases hpt b1 hb1 b2 hb2 with ⟨h11, h12, h112, _, _, _, hs1, _, _, _⟩
    rw [abs_of_nonneg h12]; linarith
  · refine integrable_of_bounded_bidderMeasure (C := 1)
      (hm112.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable ?_
    intro b2 hb2
    rcases hpt b1 hb1 b2 hb2 with ⟨h11, h12, h112, _, _, _, hs1, _, _, _⟩
    rw [abs_of_nonneg h112]; linarith
  · refine integrable_of_bounded_bidderMeasure (C := 1)
      (hm21.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable ?_
    intro b1 hb1
    rcases hpt b1 hb1 b2 hb2 with ⟨_, _, _, h21, h22, h212, _, hs2, _, _⟩
    rw [abs_of_nonneg h21]; linarith
  · refine integrable_of_bounded_bidderMeasure (C := 1)
      (hm22.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable ?_
    intro b1 hb1
    rcases hpt b1 hb1 b2 hb2 with ⟨_, _, _, h21, h22, h212, _, hs2, _, _⟩
    rw [abs_of_nonneg h22]; linarith
  · refine integrable_of_bounded_bidderMeasure (C := 1)
      (hm212.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable ?_
    intro b1 hb1
    rcases hpt b1 hb1 b2 hb2 with ⟨_, _, _, h21, h22, h212, _, hs2, _, _⟩
    rw [abs_of_nonneg h212]; linarith

lemma reduceSingleItem_Q1 {L : ℝ} {M : Mechanism} (hF : IsFeasible L M) {b1 : Type2} (hb1 : b1 ∈ bidderDomain L) :
    Q1_1 L (reduceSingleItem M) b1 = Q1_1 L M b1 + (if b1.2 ≤ b1.1 then Q1_12 L M b1 else 0) ∧
    Q1_2 L (reduceSingleItem M) b1 = Q1_2 L M b1 + (if b1.2 ≤ b1.1 then 0 else Q1_12 L M b1) ∧
    Q1_12 L (reduceSingleItem M) b1 = 0 := by
  rcases (slice_q_integrable hF).1 b1 hb1 with ⟨hi11, hi12, hi112⟩
  refine ⟨?_, ?_, ?_⟩
  · unfold Q1_1 Q1_12 reduceSingleItem; dsimp only
    split_ifs <;> [exact integral_add hi11 hi112; simp]
  · unfold Q1_2 Q1_12 reduceSingleItem; dsimp only
    split_ifs <;> [simp; exact integral_add hi12 hi112]
  · unfold Q1_12 reduceSingleItem; simp

lemma reduceSingleItem_Q2 {L : ℝ} {M : Mechanism} (hF : IsFeasible L M) {b2 : Type2} (hb2 : b2 ∈ bidderDomain L) :
    Q2_1 L (reduceSingleItem M) b2 = Q2_1 L M b2 + (if b2.2 ≤ b2.1 then Q2_12 L M b2 else 0) ∧
    Q2_2 L (reduceSingleItem M) b2 = Q2_2 L M b2 + (if b2.2 ≤ b2.1 then 0 else Q2_12 L M b2) ∧
    Q2_12 L (reduceSingleItem M) b2 = 0 := by
  rcases (slice_q_integrable hF).2 b2 hb2 with ⟨hi21, hi22, hi212⟩
  refine ⟨?_, ?_, ?_⟩
  · unfold Q2_1 Q2_12 reduceSingleItem; dsimp only
    split_ifs <;> [exact integral_add hi21 hi212; simp]
  · unfold Q2_2 Q2_12 reduceSingleItem; dsimp only
    split_ifs <;> [simp; exact integral_add hi22 hi212]
  · unfold Q2_12 reduceSingleItem; simp

lemma reduceSingleItem_isBIC {L : ℝ} {M : Mechanism} (hF : IsFeasible L M) (hB : IsBIC L M) :
    IsBIC L (reduceSingleItem M) := by
  refine ⟨hB.1, hB.2.1, ?_, ?_⟩
  · intro v1 hv1 b1 hb1
    rcases reduceSingleItem_Q1 hF hb1 with ⟨h1, h2, h3⟩
    rcases reduceSingleItem_Q1 hF hv1 with ⟨h1', h2', h3'⟩
    have hq12 : 0 ≤ Q1_12 L M b1 := by
      unfold Q1_12
      refine integral_nonneg_of_ae ?_
      filter_upwards [ae_mem_bidderDomain L] with b2 hb2
      exact (hF.1 b1 hb1 b2 hb2).2.2.1
    rw [h1, h2, h3, h1', h2', h3']
    have hle := unitDemandVal_reduce_le v1 b1 (Q1_1 L M b1) (Q1_2 L M b1) (Q1_12 L M b1) hq12
    have heq := unitDemandVal_reduce_eq v1 (Q1_1 L M v1) (Q1_2 L M v1) (Q1_12 L M v1)
    have hb := hB.2.2.1 v1 hv1 b1 hb1
    change _ - P1 L M b1 ≤ _ - P1 L M v1
    linarith
  · intro v2 hv2 b2 hb2
    rcases reduceSingleItem_Q2 hF hb2 with ⟨h1, h2, h3⟩
    rcases reduceSingleItem_Q2 hF hv2 with ⟨h1', h2', h3'⟩
    have hq212 : 0 ≤ Q2_12 L M b2 := by
      unfold Q2_12
      refine integral_nonneg_of_ae ?_
      filter_upwards [ae_mem_bidderDomain L] with b1 hb1
      exact (hF.1 b1 hb1 b2 hb2).2.2.2.2.2.1
    rw [h1, h2, h3, h1', h2', h3']
    have hle := unitDemandVal_reduce_le v2 b2 (Q2_1 L M b2) (Q2_2 L M b2) (Q2_12 L M b2) hq212
    have heq := unitDemandVal_reduce_eq v2 (Q2_1 L M v2) (Q2_2 L M v2) (Q2_12 L M v2)
    have hb := hB.2.2.2 v2 hv2 b2 hb2
    change _ - P2 L M b2 ≤ _ - P2 L M v2
    linarith

lemma reduceSingleItem_isInterimIR {L : ℝ} {M : Mechanism} (hF : IsFeasible L M) (hIR : IsInterimIR L M) :
    IsInterimIR L (reduceSingleItem M) := by
  refine ⟨?_, ?_⟩
  · intro v1 hv1
    rcases reduceSingleItem_Q1 hF hv1 with ⟨h1, h2, h3⟩
    rw [h1, h2, h3, unitDemandVal_reduce_eq]
    exact hIR.1 v1 hv1
  · intro v2 hv2
    rcases reduceSingleItem_Q2 hF hv2 with ⟨h1, h2, h3⟩
    rw [h1, h2, h3, unitDemandVal_reduce_eq]
    exact hIR.2 v2 hv2

/-- Every feasible DSIC + ex-post IR mechanism (for `L ≥ 0`) is unconditionally BIC + interim IR
(every payment slice is automatically integrable via the DSIC + ex-post IR sandwich). -/
lemma dsic_exPostIR_implies_bic_interimIR {L : ℝ} (hL : 0 ≤ L) {M : Mechanism}
    (hF : IsFeasible L M) (hD : IsDSIC L M) (hIR : IsExPostIR L M) :
    IsBIC L M ∧ IsInterimIR L M := by
  have hval_bounds : ∀ v ∈ bidderDomain L, ∀ q1 q2 q12 : ℝ,
      0 ≤ q1 → 0 ≤ q2 → 0 ≤ q12 → q1 + q2 + q12 ≤ 1 →
      0 ≤ UnitDemandVal v q1 q2 q12 ∧ UnitDemandVal v q1 q2 q12 ≤ L + 1 := by
    intro v hv q1 q2 q12 h1 h2 h12 hs
    unfold UnitDemandVal
    have hv10 : 0 ≤ v.1 := by linarith [hv.1.1]
    have hv20 : 0 ≤ v.2 := by linarith [hv.2.1]
    have hmax0 : 0 ≤ max v.1 v.2 := le_trans hv10 (le_max_left _ _)
    have hmax1 : max v.1 v.2 ≤ L + 1 := max_le hv.1.2 hv.2.2
    refine ⟨by positivity, ?_⟩
    nlinarith [hv.1.2, hv.2.2]
  -- Pick one slice v1₀ ∈ bidderDomain L with integrable `p1 v1₀ ·` via Fubini
  have hae1 : ∀ᵐ v1 ∂(bidderMeasure L),
      v1 ∈ bidderDomain L ∧ Integrable (fun v2 => M.p1 v1 v2) (bidderMeasure L) := by
    have h1 := ae_mem_bidderDomain L
    have h2 : ∀ᵐ v1 ∂(bidderMeasure L), Integrable (fun v2 => M.p1 v1 v2) (bidderMeasure L) :=
      Integrable.prod_right_ae hF.2.2.2.2.2.2.2.2.2.1
    exact h1.and h2
  obtain ⟨v1₀, hv1₀, hp1₀⟩ := hae1.exists
  have hae2 : ∀ᵐ v2 ∂(bidderMeasure L),
      v2 ∈ bidderDomain L ∧ Integrable (fun v1 => M.p2 v1 v2) (bidderMeasure L) := by
    have h1 := ae_mem_bidderDomain L
    have h2 : ∀ᵐ v2 ∂(bidderMeasure L), Integrable (fun v1 => M.p2 v1 v2) (bidderMeasure L) :=
      Integrable.prod_left_ae hF.2.2.2.2.2.2.2.2.2.2
    exact h1.and h2
  obtain ⟨v2₀, hv2₀, hp2₀⟩ := hae2.exists
  have hslice_p1 : ∀ b1 ∈ bidderDomain L, Integrable (fun b2 => M.p1 b1 b2) (bidderMeasure L) := by
    intro b1 hb1
    have hmeas : AEStronglyMeasurable (fun b2 => M.p1 b1 b2) (bidderMeasure L) :=
      (hF.2.2.2.2.2.2.2.1.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    have hdom : Integrable (fun b2 => |M.p1 v1₀ b2| + (L + 1)) (bidderMeasure L) :=
      hp1₀.abs.add (integrable_const (L + 1))
    refine hdom.mono' hmeas ?_
    filter_upwards [ae_mem_bidderDomain L] with b2 hb2
    rcases hF.1 b1 hb1 b2 hb2 with ⟨h11, h12, h112, _, _, _, hs1, _, _, _⟩
    rcases hF.1 v1₀ hv1₀ b2 hb2 with ⟨h11', h12', h112', _, _, _, hs1', _, _, _⟩
    have hvb := hval_bounds b1 hb1 _ _ _ h11 h12 h112 hs1
    have hvb0 := hval_bounds v1₀ hv1₀ _ _ _ h11 h12 h112 hs1
    have hv00 := hval_bounds v1₀ hv1₀ _ _ _ h11' h12' h112' hs1'
    have hir := (hIR b1 hb1 b2 hb2).1
    have hd := hD.1 v1₀ hv1₀ b1 hb1 b2 hb2
    unfold u1Report at hir hd
    rw [Real.norm_eq_abs, abs_le]
    have hupper : M.p1 b1 b2 ≤ L + 1 := by linarith
    have hlower : M.p1 v1₀ b2 - (L + 1) ≤ M.p1 b1 b2 := by linarith
    have habs : -|M.p1 v1₀ b2| ≤ M.p1 v1₀ b2 := neg_abs_le _
    have habs2 : 0 ≤ |M.p1 v1₀ b2| := abs_nonneg _
    exact ⟨by linarith, by linarith⟩
  have hslice_p2 : ∀ b2 ∈ bidderDomain L, Integrable (fun b1 => M.p2 b1 b2) (bidderMeasure L) := by
    intro b2 hb2
    have hmeas : AEStronglyMeasurable (fun b1 => M.p2 b1 b2) (bidderMeasure L) :=
      (hF.2.2.2.2.2.2.2.2.1.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
    have hdom : Integrable (fun b1 => |M.p2 b1 v2₀| + (L + 1)) (bidderMeasure L) :=
      hp2₀.abs.add (integrable_const (L + 1))
    refine hdom.mono' hmeas ?_
    filter_upwards [ae_mem_bidderDomain L] with b1 hb1
    rcases hF.1 b1 hb1 b2 hb2 with ⟨_, _, _, h21, h22, h212, _, hs2, _, _⟩
    rcases hF.1 b1 hb1 v2₀ hv2₀ with ⟨_, _, _, h21', h22', h212', _, hs2', _, _⟩
    have hvb := hval_bounds b2 hb2 _ _ _ h21 h22 h212 hs2
    have hvb0 := hval_bounds v2₀ hv2₀ _ _ _ h21 h22 h212 hs2
    have hv00 := hval_bounds v2₀ hv2₀ _ _ _ h21' h22' h212' hs2'
    have hir := (hIR b1 hb1 b2 hb2).2
    have hd := hD.2 b1 hb1 v2₀ hv2₀ b2 hb2
    unfold u2Report at hir hd
    rw [Real.norm_eq_abs, abs_le]
    have hupper : M.p2 b1 b2 ≤ L + 1 := by linarith
    have hlower : M.p2 b1 v2₀ - (L + 1) ≤ M.p2 b1 b2 := by linarith
    have habs : -|M.p2 b1 v2₀| ≤ M.p2 b1 v2₀ := neg_abs_le _
    have habs2 : 0 ≤ |M.p2 b1 v2₀| := abs_nonneg _
    exact ⟨by linarith, by linarith⟩
  have hq_int := slice_q_integrable hF
  have hint_u1 : ∀ v1 b1, b1 ∈ bidderDomain L →
      ∫ b2, u1Report M v1 b1 b2 ∂(bidderMeasure L) =
        UnitDemandVal v1 (Q1_1 L M b1) (Q1_2 L M b1) (Q1_12 L M b1) - P1 L M b1 := by
    intro v1 b1 hb1
    rcases hq_int.1 b1 hb1 with ⟨h1, h2, h12⟩
    have hp := hslice_p1 b1 hb1
    have hi1 : Integrable (fun b2 => v1.1 * M.q1_1 b1 b2) (bidderMeasure L) := h1.const_mul v1.1
    have hi2 : Integrable (fun b2 => v1.2 * M.q1_2 b1 b2) (bidderMeasure L) := h2.const_mul v1.2
    have hi12 : Integrable (fun b2 => max v1.1 v1.2 * M.q1_12 b1 b2) (bidderMeasure L) := h12.const_mul _
    have hi12s : Integrable (fun b2 => v1.1 * M.q1_1 b1 b2 + v1.2 * M.q1_2 b1 b2) (bidderMeasure L) := hi1.add hi2
    have hiall : Integrable (fun b2 => v1.1 * M.q1_1 b1 b2 + v1.2 * M.q1_2 b1 b2 + max v1.1 v1.2 * M.q1_12 b1 b2)
        (bidderMeasure L) := hi12s.add hi12
    unfold u1Report UnitDemandVal Q1_1 Q1_2 Q1_12 P1
    rw [integral_sub hiall hp, integral_add hi12s hi12, integral_add hi1 hi2,
        integral_const_mul, integral_const_mul, integral_const_mul]
  have hint_u2 : ∀ v2 b2, b2 ∈ bidderDomain L →
      ∫ b1, u2Report M b1 v2 b2 ∂(bidderMeasure L) =
        UnitDemandVal v2 (Q2_1 L M b2) (Q2_2 L M b2) (Q2_12 L M b2) - P2 L M b2 := by
    intro v2 b2 hb2
    rcases hq_int.2 b2 hb2 with ⟨h1, h2, h12⟩
    have hp := hslice_p2 b2 hb2
    have hi1 : Integrable (fun b1 => v2.1 * M.q2_1 b1 b2) (bidderMeasure L) := h1.const_mul v2.1
    have hi2 : Integrable (fun b1 => v2.2 * M.q2_2 b1 b2) (bidderMeasure L) := h2.const_mul v2.2
    have hi12 : Integrable (fun b1 => max v2.1 v2.2 * M.q2_12 b1 b2) (bidderMeasure L) := h12.const_mul _
    have hi12s : Integrable (fun b1 => v2.1 * M.q2_1 b1 b2 + v2.2 * M.q2_2 b1 b2) (bidderMeasure L) := hi1.add hi2
    have hiall : Integrable (fun b1 => v2.1 * M.q2_1 b1 b2 + v2.2 * M.q2_2 b1 b2 + max v2.1 v2.2 * M.q2_12 b1 b2)
        (bidderMeasure L) := hi12s.add hi12
    unfold u2Report UnitDemandVal Q2_1 Q2_2 Q2_12 P2
    rw [integral_sub hiall hp, integral_add hi12s hi12, integral_add hi1 hi2,
        integral_const_mul, integral_const_mul, integral_const_mul]
  refine ⟨⟨hslice_p1, hslice_p2, ?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro v1 hv1 b1 hb1
    rw [← hint_u1 v1 b1 hb1, ← hint_u1 v1 v1 hv1]
    rcases hq_int.1 b1 hb1 with ⟨a1, a2, a12⟩
    rcases hq_int.1 v1 hv1 with ⟨b1i, b2i, b12i⟩
    refine integral_mono_ae
      ((((a1.const_mul _).add (a2.const_mul _)).add (a12.const_mul _)).sub (hslice_p1 b1 hb1))
      ((((b1i.const_mul _).add (b2i.const_mul _)).add (b12i.const_mul _)).sub (hslice_p1 v1 hv1)) ?_
    filter_upwards [ae_mem_bidderDomain L] with b2 hb2
    exact hD.1 v1 hv1 b1 hb1 b2 hb2
  · intro v2 hv2 b2 hb2
    rw [← hint_u2 v2 b2 hb2, ← hint_u2 v2 v2 hv2]
    rcases hq_int.2 b2 hb2 with ⟨a1, a2, a12⟩
    rcases hq_int.2 v2 hv2 with ⟨b1i, b2i, b12i⟩
    refine integral_mono_ae
      ((((a1.const_mul _).add (a2.const_mul _)).add (a12.const_mul _)).sub (hslice_p2 b2 hb2))
      ((((b1i.const_mul _).add (b2i.const_mul _)).add (b12i.const_mul _)).sub (hslice_p2 v2 hv2)) ?_
    filter_upwards [ae_mem_bidderDomain L] with b1 hb1
    exact hD.2 b1 hb1 v2 hv2 b2 hb2
  · intro v1 hv1
    rw [← hint_u1 v1 v1 hv1]
    refine integral_nonneg_of_ae ?_
    filter_upwards [ae_mem_bidderDomain L] with b2 hb2
    exact (hIR v1 hv1 b2 hb2).1
  · intro v2 hv2
    rw [← hint_u2 v2 v2 hv2]
    refine integral_nonneg_of_ae ?_
    filter_upwards [ae_mem_bidderDomain L] with b1 hb1
    exact (hIR b1 hb1 v2 hv2).2

end

end EconCSAuction
