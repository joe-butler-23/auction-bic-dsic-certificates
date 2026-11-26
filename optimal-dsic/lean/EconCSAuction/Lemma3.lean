import EconCSAuction.Lemma1
import EconCSAuction.Lemma2

/-!
# Lemma 3: Feasibility, DSIC, Ex-Post IR, Exact Revenue, and Swap Symmetry

Proves for every `L ≥ 0` (and in particular every `L ≥ 2/π`):
1. `flagshipMechanism L` is feasible (`IsFeasible`), DSIC (`IsDSIC`), ex-post IR (`IsExPostIR`),
   has nonnegative payments (`NonNegPayment`) bounded in `[L, L + 1]` (`BoundedPayment`), and is
   strictly complementary (`b2_decision_iff_not_b1`; on `(-1, 1)²`, `q1_1 = 1 ↔ PhiBar t1 > PhiBar t2`).
2. Exact bidder+item swap symmetry under `σ(b₁, b₂) = ((b₂.2, b₂.1), (b₁.2, b₁.1))` for both
   `flagshipMechanism L` and `symTwinMechanism L`.
3. Exact expected revenue identity:
   `ExpectedRevenue L (flagshipMechanism L) = optimalRevenueFormula L`
   `= 2 * L + 2 * ∫ t in Ioo t0 1, PhiPlus t * gT t * (2 * GT t - 1)`.
4. Symmetric twin mechanism (`symTwinMechanism L`, 50/50 strip lottery at base price `L` and
   wing price `L + t₀/2` on `|t_{-i}| ≤ t₀`): pointwise feasible, DSIC, and ex-post IR.
-/

open MeasureTheory Set

namespace EconCSAuction

noncomputable section

/-! ### 1. Properties of `PhiBar` and Exact Complementarity of `flagshipMechanism` -/

lemma PhiBar_neg (t : ℝ) : PhiBar (-t) = -PhiBar t := by
  unfold PhiBar
  by_cases h1 : t0 < t
  · have h2 : ¬ t0 < -t := by linarith [t0_pos]
    have h3 : -t < -t0 := by linarith
    simp [h1, h2, h3]
  · by_cases h2 : t < -t0
    · have h3 : t0 < -t := by linarith
      simp [h1, h2, h3]
    · have h3 : ¬ t0 < -t := by linarith
      have h4 : ¬ -t < -t0 := by linarith
      simp [h1, h2, h3, h4]

lemma PhiBar_zero_of_abs_le {t : ℝ} (h1 : -t0 ≤ t) (h2 : t ≤ t0) : PhiBar t = 0 := by
  unfold PhiBar
  have ha : ¬ t0 < t := not_lt.mpr h2
  have hb : ¬ t < -t0 := not_lt.mpr h1
  simp [ha, hb]

lemma PhiBar_pos_of_gt {t : ℝ} (ht : t0 < t) (ht1 : t < 1) : 0 < PhiBar t := by
  unfold PhiBar
  rw [if_pos ht]
  exact PhiPlus_pos_of_gt_t0 ht ht1

lemma PhiBar_neg_of_lt {t : ℝ} (ht : t < -t0) (ht1 : -1 < t) : PhiBar t < 0 := by
  have h1 : t0 < -t := by linarith
  have h2 : -t < 1 := by linarith
  have hpos := PhiBar_pos_of_gt h1 h2
  rw [PhiBar_neg] at hpos
  linarith

/-- Bidder 1's posted-price decision rule is equivalent to `t1 > max t0 t2` (for `t2 ≥ -t0`)
or `t1 > t2` (for `t2 < -t0`). -/
lemma b1_decision_iff (L : ℝ) (b1 b2 : Type2) :
    (b1.1 - p1Item1 L (b2.1 - b2.2) > b1.2 - p1Item2 L (b2.1 - b2.2)) ↔
      (if -t0 ≤ b2.1 - b2.2 then max t0 (b2.1 - b2.2) < b1.1 - b1.2
       else b2.1 - b2.2 < b1.1 - b1.2) := by
  unfold p1Item1 p1Item2
  split_ifs <;> constructor <;> intro h <;> linarith

/-- Bidder 2's posted-price decision rule is the exact logical negation of Bidder 1's! -/
lemma b2_decision_iff_not_b1 (L : ℝ) (b1 b2 : Type2) :
    (b2.1 - p2Item1 L (b1.1 - b1.2) ≥ b2.2 - p2Item2 L (b1.1 - b1.2)) ↔
      ¬ (b1.1 - p1Item1 L (b2.1 - b2.2) > b1.2 - p1Item2 L (b2.1 - b2.2)) := by
  unfold p1Item1 p1Item2 p2Item1 p2Item2
  set t1 := b1.1 - b1.2
  set t2 := b2.1 - b2.2
  have ht0 := t0_pos
  by_cases h1 : t1 ≤ t0 <;> by_cases h2 : -t0 ≤ t2
  · simp only [h1, h2, ite_true, gt_iff_lt, ge_iff_le]
    constructor <;> intro h
    · push Not
      have hle : t1 ≤ max t0 t2 := h1.trans (le_max_left t0 t2)
      linarith
    · push Not at h
      have hge : -t0 ≤ t2 := h2
      have hmax : max t0 (-t1) ≥ -t2 := by
        rcases le_total t0 (-t1) with hle | hle
        · rw [max_eq_right hle]; linarith
        · rw [max_eq_left hle]; linarith
      linarith
  · simp only [h1, h2, ite_true, ite_false, gt_iff_lt, ge_iff_le]
    push Not at h2
    rcases le_total t0 (-t1) with hm | hm
    · rw [max_eq_right hm]
      constructor <;> intro h <;> linarith
    · rw [max_eq_left hm]
      constructor <;> intro h <;> linarith
  · simp only [h1, h2, ite_false, ite_true, gt_iff_lt, ge_iff_le]
    push Not at h1
    have hmax : max t0 t2 = max t0 t2 := rfl
    constructor <;> intro h
    · push Not
      have hge : t2 ≥ t1 := by linarith
      have : max t0 t2 = t2 := max_eq_right (by linarith)
      rw [this]; linarith
    · push Not at h
      have hle : t1 ≤ max t0 t2 := by linarith
      have : max t0 t2 = t2 := by
        rcases le_total t0 t2 with hle2 | hle2
        · exact max_eq_right hle2
        · rw [max_eq_left hle2] at hle; linarith
      rw [this] at hle; linarith
  · simp only [h1, h2, ite_false, gt_iff_lt, ge_iff_le]
    push Not at h1 h2
    constructor <;> intro h <;> linarith

/-- On `(-1, 1)²`, Bidder 1 receives Item 1 iff `PhiBar t1 > PhiBar t2`. -/
lemma b1_decision_iff_PhiBar {L : ℝ} {b1 b2 : Type2}
    (hb1 : b1.1 - b1.2 ∈ Ioo (-1 : ℝ) 1) (hb2 : b2.1 - b2.2 ∈ Ioo (-1 : ℝ) 1) :
    (b1.1 - p1Item1 L (b2.1 - b2.2) > b1.2 - p1Item2 L (b2.1 - b2.2)) ↔
      PhiBar (b2.1 - b2.2) < PhiBar (b1.1 - b1.2) := by
  rw [b1_decision_iff]
  set t1 := b1.1 - b1.2
  set t2 := b2.1 - b2.2
  have ht0 := t0_pos
  have hmono : StrictMonoOn PhiPlus (Ico t0 1) := strictMonoOn_PhiPlus
  by_cases h2_ge : -t0 ≤ t2
  · rw [if_pos h2_ge]
    by_cases h2_gt : t0 < t2
    · rw [max_eq_right h2_gt.le]
      have hP2 : PhiBar t2 = PhiPlus t2 := by unfold PhiBar; rw [if_pos h2_gt]
      have hP2_pos : 0 < PhiBar t2 := PhiBar_pos_of_gt h2_gt hb2.2
      rw [hP2]
      constructor
      · intro h12
        have h1_gt : t0 < t1 := h2_gt.trans h12
        unfold PhiBar; rw [if_pos h1_gt]
        exact hmono ⟨h2_gt.le, hb2.2⟩ ⟨h1_gt.le, hb1.2⟩ h12
      · intro hlt
        have h1_gt : t0 < t1 := by
          by_contra hle; push Not at hle
          have hP1_le : PhiBar t1 ≤ 0 := by
            by_cases hm : t1 < -t0
            · exact (PhiBar_neg_of_lt hm hb1.1).le
            · push Not at hm; rw [PhiBar_zero_of_abs_le hm hle]
          linarith
        unfold PhiBar at hlt; rw [if_pos h1_gt] at hlt
        by_contra hle; push Not at hle
        rcases eq_or_lt_of_le hle with heq | h21
        · rw [heq] at hlt; exact lt_irrefl _ hlt
        · have := hmono ⟨h1_gt.le, hb1.2⟩ ⟨h2_gt.le, hb2.2⟩ h21
          linarith
    · push Not at h2_gt
      rw [max_eq_left h2_gt, PhiBar_zero_of_abs_le h2_ge h2_gt]
      constructor
      · intro h1; exact PhiBar_pos_of_gt h1 hb1.2
      · intro hpos
        by_contra hle; push Not at hle
        by_cases hm : t1 < -t0
        · linarith [PhiBar_neg_of_lt hm hb1.1]
        · push Not at hm; rw [PhiBar_zero_of_abs_le hm hle] at hpos; linarith
  · rw [if_neg h2_ge]
    push Not at h2_ge
    have hP2_neg : PhiBar t2 < 0 := PhiBar_neg_of_lt h2_ge hb2.1
    have hP2_eq : PhiBar t2 = -PhiPlus (-t2) := by
      unfold PhiBar; rw [if_neg (by linarith), if_pos h2_ge]
    constructor
    · intro h21
      by_cases h1_lt : t1 < -t0
      · have hP1_eq : PhiBar t1 = -PhiPlus (-t1) := by
          unfold PhiBar; rw [if_neg (by linarith), if_pos h1_lt]
        rw [hP2_eq, hP1_eq]
        have := hmono (a := -t1) (b := -t2) ⟨by linarith, by linarith [hb1.1]⟩
          ⟨by linarith, by linarith [hb2.1]⟩ (by linarith)
        linarith
      · push Not at h1_lt
        by_cases h1_gt : t0 < t1
        · exact hP2_neg.trans (PhiBar_pos_of_gt h1_gt hb1.2)
        · push Not at h1_gt
          rwa [PhiBar_zero_of_abs_le h1_lt h1_gt]
    · intro hlt
      by_contra hle; push Not at hle
      have h1_lt : t1 < -t0 := hle.trans_lt h2_ge
      have hP1_eq : PhiBar t1 = -PhiPlus (-t1) := by
        unfold PhiBar; rw [if_neg (by linarith), if_pos h1_lt]
      rw [hP2_eq, hP1_eq] at hlt
      rcases eq_or_lt_of_le hle with heq | h12
      · rw [heq] at hlt; linarith
      · have := hmono (a := -t2) (b := -t1) ⟨by linarith, by linarith [hb2.1]⟩
          ⟨by linarith, by linarith [hb1.1]⟩ (by linarith)
        linarith

/-! ### 2. Feasibility, DSIC, Ex-Post IR, and Payment Bounds for `flagshipMechanism` -/

lemma flagshipMechanism_boundedPayment (L : ℝ) : BoundedPayment L (flagshipMechanism L) := by
  intro v1 hv1 v2 hv2
  have ht1_le : v1.1 - v1.2 ≤ 1 := by linarith [hv1.1.2, hv1.2.1]
  have ht1_ge : -1 ≤ v1.1 - v1.2 := by linarith [hv1.1.1, hv1.2.2]
  have ht2_le : v2.1 - v2.2 ≤ 1 := by linarith [hv2.1.2, hv2.2.1]
  have ht2_ge : -1 ≤ v2.1 - v2.2 := by linarith [hv2.1.1, hv2.2.2]
  have ht0 := t0_pos
  have ht01 := t0_lt_one
  refine ⟨?_, ?_⟩
  · unfold flagshipMechanism p1Item1 p1Item2 valInterval; dsimp only
    split_ifs <;> refine ⟨?_, ?_⟩
    · linarith [le_max_left t0 (v2.1 - v2.2)]
    · linarith [max_le ht01.le ht2_le]
    · linarith
    · linarith
    · linarith
    · linarith
    · linarith
    · linarith
  · unfold flagshipMechanism p2Item1 p2Item2 valInterval; dsimp only
    split_ifs <;> refine ⟨?_, ?_⟩
    · linarith
    · linarith
    · linarith [le_max_left t0 (-(v1.1 - v1.2))]
    · linarith [max_le ht01.le (by linarith : -(v1.1 - v1.2) ≤ 1)]
    · linarith
    · linarith
    · linarith
    · linarith

lemma flagshipMechanism_nonNegPayment {L : ℝ} (hL : 0 ≤ L) : NonNegPayment L (flagshipMechanism L) := by
  intro v1 hv1 v2 hv2
  have hb := flagshipMechanism_boundedPayment L v1 hv1 v2 hv2
  exact ⟨hL.trans hb.1.1, hL.trans hb.2.1⟩

lemma flagshipMechanism_isFeasible (L : ℝ) : IsFeasible L (flagshipMechanism L) := by
  have hmeas_p11 : Measurable (fun p : Type2 × Type2 => p1Item1 L (p.2.1 - p.2.2)) := by
    unfold p1Item1
    have hpred : MeasurableSet {p : Type2 × Type2 | -t0 ≤ p.2.1 - p.2.2} :=
      measurableSet_le measurable_const ((measurable_fst.comp measurable_snd).sub (measurable_snd.comp measurable_snd))
    exact Measurable.ite hpred
      (measurable_const.add (measurable_const.max ((measurable_fst.comp measurable_snd).sub (measurable_snd.comp measurable_snd))))
      measurable_const
  have hmeas_p12 : Measurable (fun p : Type2 × Type2 => p1Item2 L (p.2.1 - p.2.2)) := by
    unfold p1Item2
    have hpred : MeasurableSet {p : Type2 × Type2 | -t0 ≤ p.2.1 - p.2.2} :=
      measurableSet_le measurable_const ((measurable_fst.comp measurable_snd).sub (measurable_snd.comp measurable_snd))
    exact Measurable.ite hpred measurable_const
      (measurable_const.add ((measurable_fst.comp measurable_snd).sub (measurable_snd.comp measurable_snd)).neg)
  have hmeas_p21 : Measurable (fun p : Type2 × Type2 => p2Item1 L (p.1.1 - p.1.2)) := by
    unfold p2Item1
    have hpred : MeasurableSet {p : Type2 × Type2 | p.1.1 - p.1.2 ≤ t0} :=
      measurableSet_le ((measurable_fst.comp measurable_fst).sub (measurable_snd.comp measurable_fst)) measurable_const
    exact Measurable.ite hpred measurable_const
      (measurable_const.add ((measurable_fst.comp measurable_fst).sub (measurable_snd.comp measurable_fst)))
  have hmeas_p22 : Measurable (fun p : Type2 × Type2 => p2Item2 L (p.1.1 - p.1.2)) := by
    unfold p2Item2
    have hpred : MeasurableSet {p : Type2 × Type2 | p.1.1 - p.1.2 ≤ t0} :=
      measurableSet_le ((measurable_fst.comp measurable_fst).sub (measurable_snd.comp measurable_fst)) measurable_const
    exact Measurable.ite hpred
      (measurable_const.add (measurable_const.max ((measurable_fst.comp measurable_fst).sub (measurable_snd.comp measurable_fst)).neg))
      measurable_const
  have hpred1 : MeasurableSet {p : Type2 × Type2 |
      p.1.2 - p1Item2 L (p.2.1 - p.2.2) < p.1.1 - p1Item1 L (p.2.1 - p.2.2)} :=
    measurableSet_lt ((measurable_snd.comp measurable_fst).sub hmeas_p12)
      ((measurable_fst.comp measurable_fst).sub hmeas_p11)
  have hpred2 : MeasurableSet {p : Type2 × Type2 |
      p.2.2 - p2Item2 L (p.1.1 - p.1.2) ≤ p.2.1 - p2Item1 L (p.1.1 - p.1.2)} :=
    measurableSet_le ((measurable_snd.comp measurable_snd).sub hmeas_p22)
      ((measurable_fst.comp measurable_snd).sub hmeas_p21)
  have hmp1 : Measurable (Function.uncurry (flagshipMechanism L).p1) :=
    Measurable.ite hpred1 hmeas_p11 hmeas_p12
  have hmp2 : Measurable (Function.uncurry (flagshipMechanism L).p2) :=
    Measurable.ite hpred2 hmeas_p21 hmeas_p22
  refine ⟨?_, Measurable.ite hpred1 measurable_const measurable_const,
    Measurable.ite hpred1 measurable_const measurable_const, measurable_const,
    Measurable.ite hpred2 measurable_const measurable_const,
    Measurable.ite hpred2 measurable_const measurable_const, measurable_const,
    hmp1, hmp2, ?_, ?_⟩
  · intro v1 _ v2 _
    have hcomp := b2_decision_iff_not_b1 L v1 v2
    unfold flagshipMechanism; dsimp only
    by_cases h1 : v1.1 - p1Item1 L (v2.1 - v2.2) > v1.2 - p1Item2 L (v2.1 - v2.2)
    · have h2 : ¬ (v2.1 - p2Item1 L (v1.1 - v1.2) ≥ v2.2 - p2Item2 L (v1.1 - v1.2)) :=
        fun h => (hcomp.mp h) h1
      simp [h1, h2]
    · have h2 : v2.1 - p2Item1 L (v1.1 - v1.2) ≥ v2.2 - p2Item2 L (v1.1 - v1.2) :=
        hcomp.mpr h1
      simp [h1, h2]
  · refine integrable_of_bounded_jointMeasure (C := |L| + 1) hmp1.aestronglyMeasurable ?_
    intro x hx
    have hb := (flagshipMechanism_boundedPayment L x.1 hx.1 x.2 hx.2).1
    dsimp only [Function.uncurry]
    rw [abs_le]
    exact ⟨by linarith [neg_abs_le L, hb.1], by linarith [le_abs_self L, hb.2]⟩
  · refine integrable_of_bounded_jointMeasure (C := |L| + 1) hmp2.aestronglyMeasurable ?_
    intro x hx
    have hb := (flagshipMechanism_boundedPayment L x.1 hx.1 x.2 hx.2).2
    dsimp only [Function.uncurry]
    rw [abs_le]
    exact ⟨by linarith [neg_abs_le L, hb.1], by linarith [le_abs_self L, hb.2]⟩

lemma flagshipMechanism_isDSIC (L : ℝ) : IsDSIC L (flagshipMechanism L) := by
  refine ⟨?_, ?_⟩
  · intro v1 _ b1 _ b2 _
    unfold u1Report UnitDemandVal flagshipMechanism; dsimp only
    split_ifs with h1 h2 <;> linarith
  · intro b1 _ v2 _ b2 _
    unfold u2Report UnitDemandVal flagshipMechanism; dsimp only
    split_ifs with h1 h2 <;> linarith

lemma flagshipMechanism_isExPostIR (L : ℝ) : IsExPostIR L (flagshipMechanism L) := by
  intro v1 hv1 v2 hv2
  refine ⟨?_, ?_⟩
  · unfold u1Report UnitDemandVal flagshipMechanism p1Item1 p1Item2; dsimp only
    have h1 : L ≤ v1.1 := hv1.1.1
    have h2 : L ≤ v1.2 := hv1.2.1
    split_ifs <;> linarith
  · unfold u2Report UnitDemandVal flagshipMechanism p2Item1 p2Item2; dsimp only
    have h1 : L ≤ v2.1 := hv2.1.1
    have h2 : L ≤ v2.2 := hv2.2.1
    split_ifs <;> linarith

/-! ### 3. Exact Bidder+Item Swap Symmetry and Symmetric Twin Mechanism -/

/-- Exact bidder+item swap symmetry of `flagshipMechanism L` under
`σ(b₁, b₂) = ((b₂.2, b₂.1), (b₁.2, b₁.1))`. -/
lemma flagshipMechanism_swap (L : ℝ) (b1 b2 : Type2) :
    (flagshipMechanism L).q2_1 (b2.2, b2.1) (b1.2, b1.1) = (flagshipMechanism L).q1_2 b1 b2 ∧
    (flagshipMechanism L).q2_2 (b2.2, b2.1) (b1.2, b1.1) = (flagshipMechanism L).q1_1 b1 b2 ∧
    (flagshipMechanism L).p2 (b2.2, b2.1) (b1.2, b1.1) = (flagshipMechanism L).p1 b1 b2 := by
  have hp1 : p2Item1 L (b2.2 - b2.1) = p1Item2 L (b2.1 - b2.2) := by
    unfold p2Item1 p1Item2
    by_cases h : -t0 ≤ b2.1 - b2.2
    · rw [if_pos (by linarith), if_pos h]
    · rw [if_neg (by linarith), if_neg h]; ring
  have hp2 : p2Item2 L (b2.2 - b2.1) = p1Item1 L (b2.1 - b2.2) := by
    unfold p2Item2 p1Item1
    by_cases h : -t0 ≤ b2.1 - b2.2
    · rw [if_pos (by linarith), if_pos h]; congr 2; ring
    · rw [if_neg (by linarith), if_neg h]
  unfold flagshipMechanism; dsimp only
  rw [hp1, hp2]
  by_cases hc : b1.1 - p1Item1 L (b2.1 - b2.2) > b1.2 - p1Item2 L (b2.1 - b2.2)
  · have hnot : ¬ b1.2 - p1Item2 L (b2.1 - b2.2) ≥ b1.1 - p1Item1 L (b2.1 - b2.2) := by linarith
    simp [hc, hnot]
  · have hge : b1.2 - p1Item2 L (b2.1 - b2.2) ≥ b1.1 - p1Item1 L (b2.1 - b2.2) := by linarith
    simp [hc, hge]

/-- Symmetric twin mechanism: on `|t_{-i}| ≤ t₀`, offers each bidder the 3-option menu
`{(1/2, 1/2; L), (1, 0; L + t₀/2), (0, 1; L + t₀/2)}`; outside, matches `flagshipMechanism`. -/
def symTwinMechanism (L : ℝ) : Mechanism where
  q1_1 b1 b2 :=
    let t1 := b1.1 - b1.2; let t2 := b2.1 - b2.2
    if -t0 ≤ t2 ∧ t2 ≤ t0 then
      if t0 < t1 then 1 else if t1 < -t0 then 0 else 1 / 2
    else if t2 < t1 then 1 else 0
  q1_2 b1 b2 :=
    let t1 := b1.1 - b1.2; let t2 := b2.1 - b2.2
    if -t0 ≤ t2 ∧ t2 ≤ t0 then
      if t0 < t1 then 0 else if t1 < -t0 then 1 else 1 / 2
    else if t2 < t1 then 0 else 1
  q1_12 _ _ := 0
  q2_1 b1 b2 :=
    let t1 := b1.1 - b1.2; let t2 := b2.1 - b2.2
    if -t0 ≤ t1 ∧ t1 ≤ t0 then
      if t0 < t2 then 1 else if t2 < -t0 then 0 else 1 / 2
    else if t1 ≤ t2 then 1 else 0
  q2_2 b1 b2 :=
    let t1 := b1.1 - b1.2; let t2 := b2.1 - b2.2
    if -t0 ≤ t1 ∧ t1 ≤ t0 then
      if t0 < t2 then 0 else if t2 < -t0 then 1 else 1 / 2
    else if t1 ≤ t2 then 0 else 1
  q2_12 _ _ := 0
  p1 b1 b2 :=
    let t1 := b1.1 - b1.2; let t2 := b2.1 - b2.2
    if -t0 ≤ t2 ∧ t2 ≤ t0 then
      if t0 < t1 then L + t0 / 2 else if t1 < -t0 then L + t0 / 2 else L
    else if t0 < t2 then
      if t2 < t1 then L + t2 else L
    else
      if t2 < t1 then L else L + (-t2)
  p2 b1 b2 :=
    let t1 := b1.1 - b1.2; let t2 := b2.1 - b2.2
    if -t0 ≤ t1 ∧ t1 ≤ t0 then
      if t0 < t2 then L + t0 / 2 else if t2 < -t0 then L + t0 / 2 else L
    else if t0 < t1 then
      if t1 ≤ t2 then L + t1 else L
    else
      if t1 ≤ t2 then L else L + (-t1)

lemma symTwinMechanism_isPointwiseFeasible (L : ℝ) : IsPointwiseFeasible L (symTwinMechanism L) := by
  intro v1 _ v2 _
  unfold symTwinMechanism; dsimp only
  have ht0 := t0_pos
  have htrich : ∀ x : ℝ, x < -t0 ∨ (-t0 ≤ x ∧ x ≤ t0) ∨ t0 < x := by
    intro x
    by_cases h1 : x < -t0
    · exact Or.inl h1
    · by_cases h2 : x ≤ t0
      · exact Or.inr (Or.inl ⟨not_lt.mp h1, h2⟩)
      · exact Or.inr (Or.inr (not_le.mp h2))
  rcases htrich (v1.1 - v1.2) with h1 | ⟨h1a, h1b⟩ | h1 <;>
    rcases htrich (v2.1 - v2.2) with h2 | ⟨h2a, h2b⟩ | h2 <;>
    split_ifs <;> (try simp only [not_and_or, not_le, not_lt] at *) <;>
    norm_num <;> repeat (first | linarith | cases ‹_ ∨ _›)

lemma symTwinMechanism_isDSIC (L : ℝ) : IsDSIC L (symTwinMechanism L) := by
  have ht0 := t0_pos
  refine ⟨?_, ?_⟩
  · intro v1 _ b1 _ b2 _
    unfold u1Report UnitDemandVal symTwinMechanism; dsimp only
    split_ifs <;> linarith
  · intro b1 _ v2 _ b2 _
    unfold u2Report UnitDemandVal symTwinMechanism; dsimp only
    split_ifs <;> linarith

lemma symTwinMechanism_isExPostIR (L : ℝ) : IsExPostIR L (symTwinMechanism L) := by
  have ht0 := t0_pos
  intro v1 hv1 v2 hv2
  refine ⟨?_, ?_⟩
  · unfold u1Report UnitDemandVal symTwinMechanism; dsimp only
    have h1 := hv1.1.1; have h2 := hv1.2.1
    split_ifs <;> linarith
  · unfold u2Report UnitDemandVal symTwinMechanism; dsimp only
    have h1 := hv2.1.1; have h2 := hv2.2.1
    split_ifs <;> linarith

/-- Exact payment swap symmetry of `symTwinMechanism L` under `σ(b₁, b₂) = ((b₂.2, b₂.1), (b₁.2, b₁.1))`. -/
lemma symTwinMechanism_swap_p (L : ℝ) (b1 b2 : Type2) :
    (symTwinMechanism L).p2 (b2.2, b2.1) (b1.2, b1.1) = (symTwinMechanism L).p1 b1 b2 := by
  unfold symTwinMechanism; dsimp only
  by_cases h2 : -t0 ≤ b2.1 - b2.2 ∧ b2.1 - b2.2 ≤ t0
  · have h2' : -t0 ≤ b2.2 - b2.1 ∧ b2.2 - b2.1 ≤ t0 := ⟨by linarith [h2.2], by linarith [h2.1]⟩
    rw [if_pos h2', if_pos h2]
    split_ifs <;> first | rfl | (exfalso; linarith [t0_pos])
  · have h2' : ¬ (-t0 ≤ b2.2 - b2.1 ∧ b2.2 - b2.1 ≤ t0) := fun ⟨a, b⟩ => h2 ⟨by linarith, by linarith⟩
    rw [if_neg h2', if_neg h2]
    simp only [not_and_or, not_le] at h2
    rcases h2 with hlt | hgt
    · rw [if_pos (by linarith : t0 < b2.2 - b2.1), if_neg (by linarith [t0_pos] : ¬ t0 < b2.1 - b2.2)]
      split_ifs <;> first | rfl | (exfalso; linarith) | ring
    · rw [if_neg (by linarith [t0_pos] : ¬ t0 < b2.2 - b2.1), if_pos hgt]
      split_ifs <;> first | rfl | (exfalso; linarith) | ring

/-! ### 4. Exact Distribution of `t = v₁ - v₂` and Exact Expected Revenue of `flagshipMechanism` -/

/-- Exact 1D expectation of any bounded measurable function of `t = v₁ - v₂` under `bidderMeasure L`:
`∫ v, h (v.1 - v.2) ∂(bidderMeasure L) = ∫ t in (0, 1), (h t + h (-t)) * g_T(t)`. -/
lemma integral_bidderMeasure_diff {L : ℝ} {h : ℝ → ℝ}
    (hm : Measurable h) (hb : ∃ C, ∀ t ∈ Icc (-1 : ℝ) 1, |h t| ≤ C) :
    ∫ v, h (v.1 - v.2) ∂(bidderMeasure L) =
      ∫ t in Ioo (0 : ℝ) 1, (h t + h (-t)) * gT t := by
  obtain ⟨C, hC⟩ := hb
  have hmeas_v : Measurable (fun v : Type2 => h (v.1 - v.2)) :=
    hm.comp (measurable_fst.sub measurable_snd)
  rw [integral_bidderMeasure_eq hmeas_v.aestronglyMeasurable]
  have hsimp : ∀ ab : Type2, h ((L + ab.1) - (L + ab.2)) * rho ab.1 ab.2 =
      h (ab.1 - ab.2) * rho ab.1 ab.2 := by
    intro ab; congr 2; ring
  simp_rw [hsimp]
  -- Split `openUnitSquare` into `U_+ = {a > b}` and `U_- = {b > a}` (diagonal `{a = b}` has measure 0!)
  let Up : Set Type2 := openUnitSquare ∩ ({ab : Type2 | (0 : ℝ) < ab.1 - ab.2} ∩ {ab : Type2 | ab.1 - ab.2 < 1})
  let Um : Set Type2 := openUnitSquare ∩ ({ab : Type2 | (0 : ℝ) < ab.2 - ab.1} ∩ {ab : Type2 | ab.2 - ab.1 < 1})
  have hUp_meas : MeasurableSet Up :=
    measurableSet_openUnitSquare.inter
      ((measurableSet_lt measurable_const (measurable_fst.sub measurable_snd)).inter
       (measurableSet_lt (measurable_fst.sub measurable_snd) measurable_const))
  have hUm_meas : MeasurableSet Um :=
    measurableSet_openUnitSquare.inter
      ((measurableSet_lt measurable_const (measurable_snd.sub measurable_fst)).inter
       (measurableSet_lt (measurable_snd.sub measurable_fst) measurable_const))
  have hint_all : IntegrableOn (fun ab : Type2 => h (ab.1 - ab.2) * rho ab.1 ab.2) openUnitSquare volume := by
    have hdom : IntegrableOn (fun ab : Type2 => max C 0 * rho ab.1 ab.2) openUnitSquare volume :=
      integrableOn_rho_openUnitSquare.const_mul _
    refine hdom.mono' ((hm.comp (measurable_fst.sub measurable_snd)).mul
      (measurable_const.div (measurable_const.mul
        (Real.continuous_sqrt.measurable.comp (measurable_fst.mul measurable_snd))))).aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_openUnitSquare]
    filter_upwards with ab hab
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (rho_nonneg _ _)]
    have hdiff : ab.1 - ab.2 ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hab.1.1, hab.2.2], by linarith [hab.1.2, hab.2.1]⟩
    exact mul_le_mul_of_nonneg_right ((hC _ hdiff).trans (le_max_left _ _)) (rho_nonneg _ _)
  have hae_union : (openUnitSquare : Set Type2) =ᵐ[volume] (Up ∪ Um) := by
    apply MeasureTheory.ae_eq_set.mpr
    constructor
    · have hsub : openUnitSquare \ (Up ∪ Um) ⊆ {ab : Type2 | ab.1 = ab.2} := by
        intro ab hab
        simp only [mem_sdiff, mem_union, Up, Um, mem_inter_iff, mem_ofPred_eq, not_or] at hab
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · exact hab.2.2 ⟨hab.1, by linarith, by linarith [hab.1.1.1, hab.1.2.2]⟩
        · exact hab.2.1 ⟨hab.1, by linarith, by linarith [hab.1.1.2, hab.1.2.1]⟩
      refine measure_mono_null hsub ?_
      have hdiag : {ab : Type2 | ab.1 = ab.2} = {ab : Type2 | ab.1 - ab.2 = 0} := by
        ext ab; simp [sub_eq_zero]
      rw [hdiag]; exact volume_diff_eq_const_zero 0
    · have : (Up ∪ Um) \ openUnitSquare = ∅ := by
        ext ab; simp [Up, Um]; tauto
      rw [this]; simp
  have hdisj : Disjoint Up Um := Set.disjoint_left.mpr (fun ab h1 h2 => by
    simp only [Up, Um, mem_inter_iff, mem_ofPred_eq] at h1 h2; linarith)
  rw [setIntegral_congr_set hae_union, setIntegral_union hdisj hUm_meas
      (hint_all.mono_set Set.inter_subset_left) (hint_all.mono_set Set.inter_subset_left)]
  have hUp_eq : Up = {ab : Type2 | ab ∈ openUnitSquare ∧ (0 : ℝ) < ab.1 - ab.2 ∧ ab.1 - ab.2 < 1} := rfl
  -- Evaluate `Up` via `setIntegral_shear_upper`
  have hUp_val : ∫ ab in Up, h (ab.1 - ab.2) * rho ab.1 ab.2 = ∫ t in Ioo (0 : ℝ) 1, h t * gT t := by
    rw [hUp_eq, setIntegral_shear_upper le_rfl zero_le_one le_rfl (hint_all.mono_set (fun _ h => h.1))]
    refine setIntegral_congr_fun measurableSet_Ioo (fun t ht => ?_)
    have hsub : ∀ s : ℝ, h (s + t - s) * rho (s + t) s = h t * rho (s + t) s := by
      intro s; congr 2; ring
    simp_rw [hsub]
    rw [integral_const_mul, integral_rho_eq_gT ht.1 ht.2]
  -- Evaluate `Um` by swapping `(a, b) ↦ (b, a)` then `setIntegral_shear_upper`!
  have hUm_val : ∫ ab in Um, h (ab.1 - ab.2) * rho ab.1 ab.2 = ∫ t in Ioo (0 : ℝ) 1, h (-t) * gT t := by
    have hswap_pre : (Prod.swap : Type2 → Type2) ⁻¹' Um = Up := by
      ext ⟨a, b⟩; simp [Up, Um, openUnitSquare]
    have hmp := Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    have hInd_swap : ∫ ab in Um, h (ab.1 - ab.2) * rho ab.1 ab.2 =
        ∫ ab in Up, h (ab.2 - ab.1) * rho ab.1 ab.2 := by
      rw [← integral_indicator hUm_meas, ← integral_indicator hUp_meas, Measure.volume_eq_prod]
      rw [← hmp.integral_comp MeasurableEquiv.prodComm.measurableEmbedding
        (Um.indicator (fun ab : Type2 => h (ab.1 - ab.2) * rho ab.1 ab.2))]
      congr 1; ext ⟨a, b⟩
      by_cases hmem : (a, b) ∈ Up
      · have hsm : (b, a) ∈ Um := by
          simp only [Up, Um, openUnitSquare, mem_inter_iff, mem_ofPred_eq, mem_Ioo] at hmem ⊢
          exact ⟨⟨hmem.1.2, hmem.1.1⟩, by linarith [hmem.2.1], by linarith [hmem.2.2]⟩
        simp only [Function.comp_apply, Prod.swap_prod_mk, indicator_of_mem hsm,
          indicator_of_mem hmem]
        unfold rho; rw [mul_comm b a]
      · have hsm : (b, a) ∉ Um := fun h => hmem (by
          simp only [Up, Um, openUnitSquare, mem_inter_iff, mem_ofPred_eq, mem_Ioo] at h ⊢
          exact ⟨⟨h.1.2, h.1.1⟩, by linarith [h.2.1], by linarith [h.2.2]⟩)
        simp only [Function.comp_apply, Prod.swap_prod_mk, indicator_of_notMem hsm,
          indicator_of_notMem hmem]
    rw [hInd_swap]
    have hint_neg : IntegrableOn (fun ab : Type2 => h (ab.2 - ab.1) * rho ab.1 ab.2) Up volume := by
      have hdom : IntegrableOn (fun ab : Type2 => max C 0 * rho ab.1 ab.2) Up volume :=
        (integrableOn_rho_openUnitSquare.mono_set Set.inter_subset_left).const_mul _
      refine hdom.mono' ((hm.comp (measurable_snd.sub measurable_fst)).mul
        (measurable_const.div (measurable_const.mul
          (Real.continuous_sqrt.measurable.comp (measurable_fst.mul measurable_snd))))).aestronglyMeasurable ?_
      rw [ae_restrict_iff' hUp_meas]
      filter_upwards with ab hab
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (rho_nonneg _ _)]
      have hdiff : ab.2 - ab.1 ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hab.1.1.2, hab.1.2.1], by linarith [hab.1.1.1, hab.1.2.2]⟩
      exact mul_le_mul_of_nonneg_right ((hC _ hdiff).trans (le_max_left _ _)) (rho_nonneg _ _)
    rw [hUp_eq, setIntegral_shear_upper le_rfl zero_le_one le_rfl hint_neg]
    refine setIntegral_congr_fun measurableSet_Ioo (fun t ht => ?_)
    have hsub : ∀ s : ℝ, h (s - (s + t)) * rho (s + t) s = h (-t) * rho (s + t) s := by
      intro s; congr 2; ring
    simp_rw [hsub]
    rw [integral_const_mul, integral_rho_eq_gT ht.1 ht.2]
  rw [hUp_val, hUm_val]
  have hint_pos : IntegrableOn (fun t => h t * gT t) (Ioo (0 : ℝ) 1) volume := by
    refine (integrableOn_gT_Ioo_zero_one.const_mul (max C 0)).mono'
      (hm.mul measurable_gT).aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Ioo]
    filter_upwards with t ht
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (gT_pos ht.1 ht.2).le]
    exact mul_le_mul_of_nonneg_right ((hC t ⟨by linarith [ht.1], ht.2.le⟩).trans (le_max_left _ _))
      (gT_pos ht.1 ht.2).le
  have hint_neg2 : IntegrableOn (fun t => h (-t) * gT t) (Ioo (0 : ℝ) 1) volume := by
    refine (integrableOn_gT_Ioo_zero_one.const_mul (max C 0)).mono'
      ((hm.comp measurable_neg).mul measurable_gT).aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Ioo]
    filter_upwards with t ht
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (gT_pos ht.1 ht.2).le]
    exact mul_le_mul_of_nonneg_right ((hC (-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩).trans (le_max_left _ _))
      (gT_pos ht.1 ht.2).le
  rw [← integral_add hint_pos hint_neg2]
  refine setIntegral_congr_fun measurableSet_Ioo (fun t _ => by ring)

/-- Tail probability `P(v₁ - v₂ > c) = 1 - G_T(c)` for `c ∈ (0, 1]`. -/
lemma prob_diff_gt (L : ℝ) {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) :
    ∫ v, (if c < v.1 - v.2 then (1 : ℝ) else 0) ∂(bidderMeasure L) = tailGT c := by
  have hm : Measurable (fun t : ℝ => if c < t then (1 : ℝ) else 0) :=
    Measurable.ite (measurableSet_lt measurable_const measurable_id) measurable_const measurable_const
  rw [integral_bidderMeasure_diff hm ⟨1, fun t _ => by split_ifs <;> norm_num⟩]
  have hcongr : ∀ t ∈ Ioo (0 : ℝ) 1,
      ((if c < t then (1 : ℝ) else 0) + (if c < -t then 1 else 0)) * gT t =
        (Ioo c 1).indicator gT t := by
    intro t ht
    have hneg : ¬ c < -t := by linarith [ht.1]
    rw [ite_eq_right hneg, add_zero]
    by_cases hct : c < t
    · rw [ite_eq_left hct, one_mul, indicator_of_mem (show t ∈ Ioo c 1 from ⟨hct, ht.2⟩)]
    · rw [ite_eq_right hct, zero_mul, indicator_of_notMem (show t ∉ Ioo c 1 from fun h => hct h.1)]
  rw [setIntegral_congr_fun measurableSet_Ioo hcongr,
      setIntegral_indicator measurableSet_Ioo,
      inter_eq_right.mpr (Ioo_subset_Ioo_left hc0.le),
      integral_gT_Ioo hc0 hc1]

/-- Symmetric lower tail probability `P(v₁ - v₂ < -c) = 1 - G_T(c)` for `c ∈ (0, 1]`. -/
lemma prob_diff_lt_neg (L : ℝ) {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) :
    ∫ v, (if v.1 - v.2 < -c then (1 : ℝ) else 0) ∂(bidderMeasure L) = tailGT c := by
  rw [← (measurePreserving_swap_bidderMeasure L).integral_comp
    MeasurableEquiv.prodComm.measurableEmbedding (fun v : Type2 => if v.1 - v.2 < -c then (1 : ℝ) else 0)]
  have heq : ∀ v : Type2, (if v.2 - v.1 < -c then (1 : ℝ) else 0) = if c < v.1 - v.2 then 1 else 0 := by
    intro v; by_cases h : c < v.1 - v.2
    · rw [ite_eq_left (by linarith), ite_eq_left h]
    · rw [ite_eq_right (by linarith), ite_eq_right h]
  simp only [Prod.fst_swap, Prod.snd_swap, heq]
  exact prob_diff_gt L hc0 hc1

/-- Closed lower tail probability `P(v₁ - v₂ ≤ -c) = 1 - G_T(c)` for `c ∈ (0, 1]`. -/
lemma prob_diff_le_neg (L : ℝ) {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) :
    ∫ v, (if v.1 - v.2 ≤ -c then (1 : ℝ) else 0) ∂(bidderMeasure L) = tailGT c := by
  have hm : Measurable (fun t : ℝ => if t ≤ -c then (1 : ℝ) else 0) :=
    Measurable.ite (measurableSet_le measurable_id measurable_const) measurable_const measurable_const
  rw [integral_bidderMeasure_diff hm ⟨1, fun t _ => by split_ifs <;> norm_num⟩]
  have hcongr : ∀ t ∈ Ioo (0 : ℝ) 1,
      ((if t ≤ -c then (1 : ℝ) else 0) + (if -t ≤ -c then 1 else 0)) * gT t =
        (Ico c 1).indicator gT t := by
    intro t ht
    have hpos : ¬ t ≤ -c := by linarith [ht.1]
    rw [ite_eq_right hpos, zero_add]
    by_cases hct : c ≤ t
    · rw [ite_eq_left (by linarith : -t ≤ -c), one_mul, indicator_of_mem (show t ∈ Ico c 1 from ⟨hct, ht.2⟩)]
    · rw [ite_eq_right (by linarith : ¬ -t ≤ -c), zero_mul,
        indicator_of_notMem (show t ∉ Ico c 1 from fun h => hct h.1)]
  rw [setIntegral_congr_fun measurableSet_Ioo hcongr,
      setIntegral_indicator measurableSet_Ico,
      inter_eq_right.mpr (Ico_subset_Ioo_left hc0),
      setIntegral_congr_set Ioo_ae_eq_Ico.symm,
      integral_gT_Ioo hc0 hc1]

/-- Exact expected revenue of `flagshipMechanism L`:
`ExpectedRevenue L (flagshipMechanism L) = 2L + 2 ∫_{t₀}^1 Φ_+(t) g_T(t) (2 G_T(t) - 1) dt`. -/
theorem flagshipMechanism_expectedRevenue (L : ℝ) :
    ExpectedRevenue L (flagshipMechanism L) = optimalRevenueFormula L := by
  have hF := flagshipMechanism_isFeasible L
  have hp1_int : Integrable (fun x : Type2 × Type2 => (flagshipMechanism L).p1 x.1 x.2) (jointMeasure L) :=
    hF.2.2.2.2.2.2.2.2.2.1
  have hp2_int : Integrable (fun x : Type2 × Type2 => (flagshipMechanism L).p2 x.1 x.2) (jointMeasure L) :=
    hF.2.2.2.2.2.2.2.2.2.2
  unfold ExpectedRevenue optimalRevenueFormula
  rw [integral_add hp1_int hp2_int]
  -- Common 1D integral target `R1`:
  let R1 : ℝ := t0 * tailGT t0 * (2 * GT t0 - 1) + 2 * ∫ t in Ioo t0 1, t * tailGT t * gT t
  have hR1_eq : R1 = ∫ t in Ioo t0 1, PhiPlus t * gT t * (2 * GT t - 1) := by
    -- Exact antiderivative `A(t) = t * tailGT(t) * (2 * tailGT(t) - 1)` on `[t0, 1]`!
    let A : ℝ → ℝ := fun t => t * tailGT t * (2 * tailGT t - 1)
    have hA_cont : ContinuousOn A (Icc t0 1) :=
      (continuousOn_id.mul (continuousOn_tailGT t0_pos)).mul
        ((continuousOn_const.mul (continuousOn_tailGT t0_pos)).sub continuousOn_const)
    have hA_deriv : ∀ t ∈ Ioo t0 1,
        HasDerivAt A (PhiPlus t * gT t * (2 * GT t - 1) - 2 * (t * tailGT t * gT t)) t := by
      intro t ht
      have ht0' : 0 < t := t0_pos.trans ht.1
      have hd_tail := hasDerivAt_tailGT ht0' ht.2
      have hd1 : HasDerivAt (fun x => x * tailGT x) (1 * tailGT t + t * (-gT t)) t :=
        (hasDerivAt_id t).mul hd_tail
      have hd2 : HasDerivAt (fun x => 2 * tailGT x - 1) (2 * (-gT t)) t :=
        (hd_tail.const_mul (2 : ℝ)).sub_const (1 : ℝ)
      have hdA := hd1.mul hd2
      refine hdA.congr_deriv ?_
      -- Use `PhiPlus t * gT t = t * gT t - tailGT t` and `2 * GT t - 1 = 1 - 2 * tailGT t`!
      have hPhi_gT : PhiPlus t * gT t = t * gT t - tailGT t := by
        unfold PhiPlus tailGT gT
        have hs0 : 0 < Real.sqrt (1 - t) := Real.sqrt_pos.mpr (by linarith [ht.2])
        have hs1 : Real.sqrt (1 - t) < 1 := by rw [Real.sqrt_lt' zero_lt_one]; linarith
        have hA0 : artanh (Real.sqrt (1 - t)) ≠ 0 := (artanh_pos hs0 hs1).ne'
        field_simp [hA0]
        ring
      have hGT : 2 * GT t - 1 = 1 - 2 * tailGT t := by unfold GT; ring
      rw [hPhi_gT, hGT]
      ring
    -- Prove `IntervalIntegrable` on `Ioo t0 1` directly via `Ioo` congruence!
    have hint1 : IntegrableOn (fun t => PhiPlus t * gT t * (2 * GT t - 1)) (Ioo t0 1) volume := by
      have hcg := continuousOn_gT_Ioc t0_pos
      have hct := continuousOn_tailGT t0_pos
      have hbase : ContinuousOn (fun t => (t * gT t - tailGT t) * (1 - 2 * tailGT t)) (Icc t0 1) :=
        ((continuousOn_id.mul hcg).sub hct).mul (continuousOn_const.sub (continuousOn_const.mul hct))
      refine (hbase.integrableOn_Icc.mono_set Ioo_subset_Icc_self).congr_fun (fun t ht => ?_) measurableSet_Ioo
      have hs0 : 0 < Real.sqrt (1 - t) := Real.sqrt_pos.mpr (by linarith [ht.2])
      have hs1 : Real.sqrt (1 - t) < 1 := by rw [Real.sqrt_lt' zero_lt_one]; linarith [t0_pos.trans ht.1]
      have hA0 : artanh (Real.sqrt (1 - t)) ≠ 0 := (artanh_pos hs0 hs1).ne'
      unfold GT
      unfold PhiPlus tailGT gT
      field_simp [hA0]; ring
    have hint2 : IntegrableOn (fun t => t * tailGT t * gT t) (Ioo t0 1) volume := by
      have hcg := continuousOn_gT_Ioc t0_pos
      have hct := continuousOn_tailGT t0_pos
      exact (((continuousOn_id.mul hct).mul hcg).integrableOn_Icc).mono_set Ioo_subset_Icc_self
    have hint_diff : IntervalIntegrable
        (fun t => PhiPlus t * gT t * (2 * GT t - 1) - 2 * (t * tailGT t * gT t)) volume t0 1 := by
      rw [intervalIntegrable_iff_integrableOn_Ioo_of_le t0_lt_one.le]
      exact hint1.sub (hint2.const_mul 2)
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le t0_lt_one.le hA_cont hA_deriv hint_diff
    rw [intervalIntegral.integral_of_le t0_lt_one.le, ← setIntegral_congr_set Ioo_ae_eq_Ioc,
        integral_sub hint1 (hint2.const_mul 2), integral_const_mul] at hftc
    dsimp only [A, R1] at hftc ⊢
    rw [tailGT_one] at hftc
    have hGT0 : 2 * GT t0 - 1 = 1 - 2 * tailGT t0 := by unfold GT; ring
    rw [hGT0]
    linarith
  -- Now evaluate `∫ x, p1 x.1 x.2 = L + R1` and `∫ x, p2 x.1 x.2 = L + R1`!
  have hp1_eq : ∫ x, (flagshipMechanism L).p1 x.1 x.2 ∂(jointMeasure L) = L + R1 := by
    unfold jointMeasure
    rw [integral_prod_symm (fun x : Type2 × Type2 => (flagshipMechanism L).p1 x.1 x.2) hp1_int]
    -- Evaluate inner integral over `b1` for each `b2 ∈ bidderDomain L`
    let g1 : ℝ → ℝ := fun t2 =>
      if -t0 ≤ t2 then L + max t0 t2 * tailGT (max t0 t2)
      else L + (-t2) * tailGT (-t2)
    have hinner : ∀ᵐ b2 ∂(bidderMeasure L),
        (∫ b1, (flagshipMechanism L).p1 b1 b2 ∂(bidderMeasure L)) = g1 (b2.1 - b2.2) := by
      filter_upwards [ae_mem_bidderDomain L] with b2 hb2
      have ht2_le : b2.1 - b2.2 ≤ 1 := by linarith [hb2.1.2, hb2.2.1]
      have ht2_ge : -1 ≤ b2.1 - b2.2 := by linarith [hb2.1.1, hb2.2.2]
      dsimp only [g1]
      by_cases h2 : -t0 ≤ b2.1 - b2.2
      · rw [if_pos h2]
        have hrew : ∀ b1 : Type2, (flagshipMechanism L).p1 b1 b2 =
            L + max t0 (b2.1 - b2.2) * (if max t0 (b2.1 - b2.2) < b1.1 - b1.2 then 1 else 0) := by
          intro b1
          unfold flagshipMechanism
          dsimp only
          simp only [b1_decision_iff, h2, ite_true]
          unfold p1Item1 p1Item2
          simp only [h2, ite_true]
          split_ifs <;> ring
        simp_rw [hrew]
        have hind_int : Integrable (fun b1 : Type2 =>
            if max t0 (b2.1 - b2.2) < b1.1 - b1.2 then (1 : ℝ) else 0) (bidderMeasure L) :=
          integrable_of_bounded_bidderMeasure (C := 1)
            (Measurable.ite (measurableSet_lt measurable_const (measurable_fst.sub measurable_snd))
              measurable_const measurable_const).aestronglyMeasurable
            (fun _ _ => by split_ifs <;> norm_num)
        rw [integral_add (integrable_const L) (hind_int.const_mul _),
            integral_const, probReal_univ, one_smul, integral_const_mul,
            prob_diff_gt L (lt_of_lt_of_le t0_pos (le_max_left _ _)) (max_le t0_lt_one.le ht2_le)]
      · rw [ite_eq_right h2]
        push Not at h2
        have hrew : ∀ b1 : Type2, (flagshipMechanism L).p1 b1 b2 =
            L + (-(b2.1 - b2.2)) * (if b1.1 - b1.2 ≤ b2.1 - b2.2 then 1 else 0) := by
          intro b1
          unfold flagshipMechanism; dsimp only
          simp only [b1_decision_iff, not_le.mpr h2, ite_false]
          unfold p1Item1 p1Item2
          simp only [not_le.mpr h2, ite_false]
          split_ifs with hlt hle
          · exfalso; linarith
          · ring
          · ring
          · exfalso; linarith
        simp_rw [hrew]
        have hind_int : Integrable (fun b1 : Type2 =>
            if b1.1 - b1.2 ≤ b2.1 - b2.2 then (1 : ℝ) else 0) (bidderMeasure L) :=
          integrable_of_bounded_bidderMeasure (C := 1)
            (Measurable.ite (measurableSet_le (measurable_fst.sub measurable_snd) measurable_const)
              measurable_const measurable_const).aestronglyMeasurable
            (fun _ _ => by split_ifs <;> norm_num)
        rw [integral_add (integrable_const L) (hind_int.const_mul _),
            integral_const, probReal_univ, one_smul, integral_const_mul]
        have hneg_eq : ∀ b1 : Type2, (b1.1 - b1.2 ≤ b2.1 - b2.2) ↔ (b1.1 - b1.2 ≤ -(-(b2.1 - b2.2))) := by
          intro b1; simp
        simp_rw [hneg_eq]
        rw [prob_diff_le_neg L (by linarith [t0_pos]) (by linarith)]
    rw [integral_congr_ae hinner]
    have hg1_meas : Measurable g1 := by
      unfold g1 tailGT gT artanh
      have hpred : MeasurableSet {t : ℝ | -t0 ≤ t} := measurableSet_le measurable_const measurable_id
      exact Measurable.ite hpred (by fun_prop) (by fun_prop)
    have hg1_bdd : ∃ C, ∀ t ∈ Icc (-1 : ℝ) 1, |g1 t| ≤ C := by
      refine ⟨|L| + 2, fun t ht => ?_⟩
      dsimp only [g1]
      have htail_bdd : ∀ u ∈ Icc t0 1, |tailGT u| ≤ 1 := by
        intro u hu
        have hu0 : 0 < u := t0_pos.trans_le hu.1
        have hnn : 0 ≤ tailGT u := by
          rw [← integral_gT_Ioo hu0 hu.2]
          exact setIntegral_nonneg measurableSet_Ioo (fun x hx => (gT_pos (hu0.trans hx.1) hx.2).le)
        have hle1 : tailGT u ≤ 1 / 2 := by
          rw [← integral_gT_Ioo hu0 hu.2, ← integral_gT_zero_one]
          exact setIntegral_mono_set integrableOn_gT_Ioo_zero_one
            (ae_restrict_of_forall_mem measurableSet_Ioo (fun x hx => (gT_pos hx.1 hx.2).le))
            (Filter.Eventually.of_forall (Ioo_subset_Ioo_left hu0.le))
        rw [abs_of_nonneg hnn]; linarith
      split_ifs with h
      · have hm : max t0 t ∈ Icc t0 1 := ⟨le_max_left _ _, max_le t0_lt_one.le ht.2⟩
        have h1 : |max t0 t * tailGT (max t0 t)| ≤ 1 := by
          rw [abs_mul, abs_of_nonneg (t0_pos.le.trans hm.1)]
          exact (mul_le_mul hm.2 (htail_bdd _ hm) (abs_nonneg _) zero_le_one).trans (by norm_num)
        calc |L + max t0 t * tailGT (max t0 t)| ≤ |L| + |max t0 t * tailGT (max t0 t)| := abs_add_le _ _
          _ ≤ |L| + 2 := by linarith
      · have hm : -t ∈ Icc t0 1 := ⟨by linarith, by linarith [ht.1]⟩
        have h1 : |(-t) * tailGT (-t)| ≤ 1 := by
          rw [abs_mul, abs_of_nonneg (t0_pos.le.trans hm.1)]
          exact (mul_le_mul hm.2 (htail_bdd _ hm) (abs_nonneg _) zero_le_one).trans (by norm_num)
        calc |L + (-t) * tailGT (-t)| ≤ |L| + |(-t) * tailGT (-t)| := abs_add_le _ _
          _ ≤ |L| + 2 := by linarith
    rw [integral_bidderMeasure_diff hg1_meas hg1_bdd]
    -- Use `ae` congruence on `Ioo 0 1` avoiding the single point `{t0}`!
    have hsplit_ae : ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) 1)),
        (g1 t + g1 (-t)) * gT t =
          2 * L * gT t +
          (Ioo (0 : ℝ) t0).indicator (fun x => 2 * (t0 * tailGT t0) * gT x) t +
          (Ioo t0 1).indicator (fun x => 2 * (x * tailGT x * gT x)) t := by
      have hne_t0 : ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) 1)), t ≠ t0 := by
        rw [ae_restrict_iff' measurableSet_Ioo]
        have hnull : volume ({t0} : Set ℝ) = 0 := measure_singleton t0
        filter_upwards [compl_mem_ae_iff.mpr hnull] with t ht _
        exact ht
      rw [ae_restrict_iff' measurableSet_Ioo] at hne_t0 ⊢
      filter_upwards [hne_t0] with t ht_ne ht
      rcases lt_or_gt_of_ne (ht_ne ht) with hlt | hgt
      · have h1 : -t0 ≤ t := by linarith [ht.1, t0_pos]
        have h2 : -t0 ≤ -t := by linarith
        have hm1 : max t0 t = t0 := max_eq_left hlt.le
        have hm2 : max t0 (-t) = t0 := max_eq_left (by linarith [ht.1, t0_pos])
        dsimp only [g1]
        rw [ite_eq_left h1, ite_eq_left h2, hm1, hm2,
            indicator_of_mem (show t ∈ Ioo (0 : ℝ) t0 from ⟨ht.1, hlt⟩),
            indicator_of_notMem (show t ∉ Ioo t0 1 from fun h => not_lt_of_gt hlt h.1)]
        ring
      · have h1 : -t0 ≤ t := by linarith [ht.1, t0_pos]
        have h2 : ¬ -t0 ≤ -t := by linarith
        have hm1 : max t0 t = t := max_eq_right hgt.le
        dsimp only [g1]
        rw [ite_eq_left h1, ite_eq_right h2, hm1, neg_neg,
            indicator_of_notMem (show t ∉ Ioo (0 : ℝ) t0 from fun h => not_lt_of_gt hgt h.2),
            indicator_of_mem (show t ∈ Ioo t0 1 from ⟨hgt, ht.2⟩)]
        ring
    rw [setIntegral_congr_ae measurableSet_Ioo (by
      rw [ae_restrict_iff' measurableSet_Ioo] at hsplit_ae
      exact hsplit_ae)]
    have hiA : IntegrableOn (fun t => 2 * L * gT t) (Ioo (0 : ℝ) 1) volume :=
      integrableOn_gT_Ioo_zero_one.const_mul (2 * L)
    have hiB : IntegrableOn (fun t => (Ioo (0 : ℝ) t0).indicator (fun x => 2 * (t0 * tailGT t0) * gT x) t)
        (Ioo (0 : ℝ) 1) volume :=
      (integrableOn_gT_Ioo_zero_one.const_mul _).indicator measurableSet_Ioo
    have hiAB : IntegrableOn (fun t => 2 * L * gT t +
        (Ioo (0 : ℝ) t0).indicator (fun x => 2 * (t0 * tailGT t0) * gT x) t) (Ioo (0 : ℝ) 1) volume :=
      hiA.add hiB
    have hiC : IntegrableOn (fun t => (Ioo t0 1).indicator (fun x => 2 * (x * tailGT x * gT x)) t)
        (Ioo (0 : ℝ) 1) volume := by
      have hint2 : IntegrableOn (fun t => 2 * (t * tailGT t * gT t)) (Ioo t0 1) volume :=
        ((((continuousOn_id.mul (continuousOn_tailGT t0_pos)).mul (continuousOn_gT_Ioc t0_pos)).integrableOn_Icc).mono_set
          Ioo_subset_Icc_self).const_mul 2
      exact (integrable_indicator_iff measurableSet_Ioo).mpr hint2 |>.integrableOn
    rw [integral_add hiAB hiC, integral_add hiA hiB,
        integral_const_mul, integral_gT_zero_one,
        setIntegral_indicator measurableSet_Ioo, setIntegral_indicator measurableSet_Ioo,
        inter_eq_right.mpr (Ioo_subset_Ioo_right t0_lt_one.le),
        inter_eq_right.mpr (Ioo_subset_Ioo_left t0_pos.le),
        integral_const_mul, integral_const_mul]
    have hmass_t0 : ∫ x in Ioo (0 : ℝ) t0, gT x = 1 / 2 - tailGT t0 := by
      have hunion : Ioc (0 : ℝ) 1 = Ioc 0 t0 ∪ Ioc t0 1 := (Ioc_union_Ioc_eq_Ioc t0_pos.le t0_lt_one.le).symm
      have htot := integral_gT_zero_one
      rw [setIntegral_congr_set Ioo_ae_eq_Ioc, hunion,
          setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
            (integrableOn_gT_Ioo_zero_one.mono_set (Ioo_subset_Ioo_right t0_lt_one.le) |>.congr_set_ae Ioo_ae_eq_Ioc.symm)
            (integrableOn_gT_Ioo_zero_one.mono_set (Ioo_subset_Ioo_left t0_pos.le) |>.congr_set_ae Ioo_ae_eq_Ioc.symm),
          ← setIntegral_congr_set Ioo_ae_eq_Ioc, ← setIntegral_congr_set Ioo_ae_eq_Ioc,
          integral_gT_Ioo t0_pos t0_lt_one.le] at htot
      linarith
    rw [hmass_t0]
    dsimp only [R1]; unfold GT; ring
  have hp2_eq : ∫ x, (flagshipMechanism L).p2 x.1 x.2 ∂(jointMeasure L) = L + R1 := by
    rw [← integral_swapProfile L (fun x => (flagshipMechanism L).p2 x.1 x.2)]
    have hrew : (fun x : Type2 × Type2 => (flagshipMechanism L).p2 (x.2.2, x.2.1) (x.1.2, x.1.1)) =
        (fun x : Type2 × Type2 => (flagshipMechanism L).p1 x.1 x.2) := by
      ext x; exact (flagshipMechanism_swap L x.1 x.2).2.2
    rw [hrew]; exact hp1_eq
  rw [hp1_eq, hp2_eq, hR1_eq]
  ring

end

end EconCSAuction
