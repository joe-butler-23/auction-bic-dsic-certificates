import AuctionSep.Problem
import AuctionSep.CertData
import AuctionSep.MeasureLemmas

open MeasureTheory Set AuctionSep.CertData AuctionSep.MeasureLemmas

namespace AuctionSep.BICWitness

/-! ### Unpacking Certificate Booleans -/

lemma of_range2All {f : Nat → Bool} (h : range2All f = true) {k : Nat} (hk : k < 2) :
    f k = true := by
  unfold range2All at h
  simp only [Bool.and_eq_true] at h
  interval_cases k <;> tauto

lemma of_range6All {f : Nat → Bool} (h : range6All f = true) {i : Nat} (hi : i < 6) :
    f i = true := by
  unfold range6All at h
  simp only [Bool.and_eq_true] at h
  interval_cases i <;> tauto

lemma of_range7All {f : Nat → Bool} (h : range7All f = true) {i : Nat} (hi : i < 7) :
    f i = true := by
  unfold range7All at h
  simp only [Bool.and_eq_true] at h
  interval_cases i <;> tauto

lemma q11Int_feas {i1 j1 k1 i2 j2 k2 : Nat}
    (hi1 : i1 < 6) (hj1 : j1 < 6) (hk1 : k1 < 2)
    (hi2 : i2 < 6) (hj2 : j2 < 6) (hk2 : k2 < 2) :
    0 ≤ q11Int i1 j1 k1 i2 j2 k2 ∧
    q11Int i1 j1 k1 i2 j2 k2 + q11Int i2 j2 k2 i1 j1 k1 ≤ 18 := by
  have h := bicFeasCheck_true
  unfold bicFeasCheck at h
  have h6 := of_range2All (of_range6All (of_range6All
    (of_range2All (of_range6All (of_range6All h hi1) hj1) hk1) hi2) hj2) hk2
  simpa [Bool.and_eq_true, decide_eq_true_eq] using h6

lemma q11Int_rowSum {i1 j1 k1 : Nat} (hi1 : i1 < 6) (hj1 : j1 < 6) (hk1 : k1 < 2) :
    (∑ i2 ∈ Finset.range 6, ∑ j2 ∈ Finset.range 6, ∑ k2 ∈ Finset.range 2,
      q11Int i1 j1 k1 i2 j2 k2) = qSum1Int i1 j1 k1 := by
  have ha := of_range2All (of_range6All (of_range6All bicRowSumCheck_true hi1) hj1) hk1
  simp only [decide_eq_true_eq] at ha
  rw [← ha]
  unfold t72Sum range6Sum P2.sum q11Int t72Get
  have hget : ∀ (p : P2 Int), p.a0 + p.a1 = P2.get p 0 + P2.get p 1 := fun _ => rfl
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, hget]

lemma uVert_grad {i j : Nat} (hi : i < 6) (hj : j < 6) :
    qSum1Int i j 0 = uVertInt (i + 1) j - uVertInt i j ∧
    qSum2Int i j 0 = uVertInt i (j + 1) - uVertInt i j ∧
    qSum1Int i j 1 = uVertInt (i + 1) (j + 1) - uVertInt i (j + 1) ∧
    qSum2Int i j 1 = uVertInt (i + 1) (j + 1) - uVertInt (i + 1) j := by
  have h := of_range6All (of_range6All bicGradCheck_true hi) hj
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

lemma uVert_nonneg {vi vj : Nat} (hvi : vi < 7) (hvj : vj < 7) :
    0 ≤ uVertInt vi vj := by
  have h := of_range7All (of_range7All bicVertIRCheck_true hvi) hvj
  simpa [decide_eq_true_eq] using h

lemma uVert_ic {vi vj i j k : Nat}
    (hvi : vi < 7) (hvj : vj < 7) (hi : i < 6) (hj : j < 6) (hk : k < 2) :
    Int.ofNat vi * qSum1Int i j k + Int.ofNat vj * qSum2Int i j k - t1Int i j k ≤
      uVertInt vi vj := by
  have h1 := of_range7All (of_range7All bicVertICCheck_true hvi) hvj
  have h2 := of_range2All (of_range6All (of_range6All h1 hi) hj) hk
  simpa [decide_eq_true_eq] using h2

/-! ### Continuous Triangulation Partition of `[0, 1]²` -/

noncomputable def cell6 (t : ℝ) : ℕ :=
  if t < 1 / 6 then 0
  else if t < 2 / 6 then 1
  else if t < 3 / 6 then 2
  else if t < 4 / 6 then 3
  else if t < 5 / 6 then 4
  else 5

lemma cell6_lt (t : ℝ) : cell6 t < 6 := by
  unfold cell6
  split_ifs <;> omega

lemma cell6_bounds {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ((cell6 t : ℕ) : ℝ) / 6 ≤ t ∧ t ≤ ((cell6 t + 1 : ℕ) : ℝ) / 6 := by
  rcases ht with ⟨ht0, ht1⟩
  unfold cell6
  split_ifs <;> push_cast <;> constructor <;> linarith

lemma cell6_eq_of_Ioo {i : ℕ} (hi : i < 6) {t : ℝ}
    (ht1 : (i : ℝ) / 6 < t) (ht2 : t < ((i + 1 : ℕ) : ℝ) / 6) :
    cell6 t = i := by
  interval_cases i <;> unfold cell6 <;> push_cast at ht1 ht2 <;> split_ifs <;> linarith

lemma measurable_cell6 : Measurable cell6 := by
  unfold cell6
  refine Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const ?_
  refine Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const ?_
  refine Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const ?_
  refine Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const ?_
  exact Measurable.ite (measurableSet_lt measurable_id measurable_const)
    measurable_const measurable_const

noncomputable def kind6 (x : Type2) : ℕ :=
  if (6 * x.1 - (cell6 x.1 : ℝ)) + (6 * x.2 - (cell6 x.2 : ℝ)) ≤ 1 then 0 else 1

lemma kind6_lt (x : Type2) : kind6 x < 2 := by
  unfold kind6
  split_ifs <;> omega

lemma measurable_kind6 : Measurable kind6 := by
  unfold kind6
  have hc1 : Measurable (fun x : Type2 => (cell6 x.1 : ℝ)) :=
    (Measurable.of_discrete (f := fun n : ℕ => (n : ℝ))).comp (measurable_cell6.comp measurable_fst)
  have hc2 : Measurable (fun x : Type2 => (cell6 x.2 : ℝ)) :=
    (Measurable.of_discrete (f := fun n : ℕ => (n : ℝ))).comp (measurable_cell6.comp measurable_snd)
  have hsum : Measurable (fun x : Type2 => (6 * x.1 - (cell6 x.1 : ℝ)) + (6 * x.2 - (cell6 x.2 : ℝ))) :=
    ((measurable_const.mul measurable_fst).sub hc1).add ((measurable_const.mul measurable_snd).sub hc2)
  exact Measurable.ite (measurableSet_le hsum measurable_const) measurable_const measurable_const

def triSet (i j k : ℕ) : Set Type2 :=
  { x ∈ unitSquare | cell6 x.1 = i ∧ cell6 x.2 = j ∧ kind6 x = k }

lemma measurableSet_triSet (i j k : ℕ) : MeasurableSet (triSet i j k) := by
  have h1 : MeasurableSet { x : Type2 | cell6 x.1 = i } :=
    (measurable_cell6.comp measurable_fst) (MeasurableSingletonClass.measurableSet_singleton i)
  have h2 : MeasurableSet { x : Type2 | cell6 x.2 = j } :=
    (measurable_cell6.comp measurable_snd) (MeasurableSingletonClass.measurableSet_singleton j)
  have h3 : MeasurableSet { x : Type2 | kind6 x = k } :=
    measurable_kind6 (MeasurableSingletonClass.measurableSet_singleton k)
  exact measurableSet_unitSquare.inter (h1.inter (h2.inter h3))

lemma triSet_subset (i j k : ℕ) : triSet i j k ⊆ unitSquare := fun _ hx => hx.1

lemma stepFunc_eq_sum_indicator (g : ℕ → ℕ → ℕ → ℝ) {x : Type2} (hx : x ∈ unitSquare) :
    g (cell6 x.1) (cell6 x.2) (kind6 x) =
      ∑ i ∈ Finset.range 6, ∑ j ∈ Finset.range 6, ∑ k ∈ Finset.range 2,
        (triSet i j k).indicator (fun _ => g i j k) x := by
  have hi : cell6 x.1 ∈ Finset.range 6 := Finset.mem_range.mpr (cell6_lt x.1)
  have hj : cell6 x.2 ∈ Finset.range 6 := Finset.mem_range.mpr (cell6_lt x.2)
  have hk : kind6 x ∈ Finset.range 2 := Finset.mem_range.mpr (kind6_lt x)
  rw [Finset.sum_eq_single (cell6 x.1)]
  · rw [Finset.sum_eq_single (cell6 x.2)]
    · rw [Finset.sum_eq_single (kind6 x)]
      · have hmem : x ∈ triSet (cell6 x.1) (cell6 x.2) (kind6 x) := ⟨hx, rfl, rfl, rfl⟩
        simp [hmem]
      · intro k' _ hk'
        have hnot : x ∉ triSet (cell6 x.1) (cell6 x.2) k' := fun h => hk' h.2.2.2.symm
        simp [hnot]
      · intro habs; exact absurd hk habs
    · intro j' _ hj'
      apply Finset.sum_eq_zero
      intro k' _
      have hnot : x ∉ triSet (cell6 x.1) j' k' := fun h => hj' h.2.2.1.symm
      simp [hnot]
    · intro habs; exact absurd hj habs
  · intro i' _ hi'
    apply Finset.sum_eq_zero
    intro j' _
    apply Finset.sum_eq_zero
    intro k' _
    have hnot : x ∉ triSet i' j' k' := fun h => hi' h.2.1.symm
    simp [hnot]
  · intro habs; exact absurd hi habs

lemma integrableOn_step1D (g : ℕ → ℕ → ℕ → ℝ) :
    IntegrableOn (fun x : Type2 => g (cell6 x.1) (cell6 x.2) (kind6 x)) unitSquare volume := by
  have hsum : IntegrableOn
      (fun x : Type2 => ∑ i ∈ Finset.range 6, ∑ j ∈ Finset.range 6, ∑ k ∈ Finset.range 2,
        (triSet i j k).indicator (fun _ => g i j k) x) unitSquare volume := by
    apply integrableOn_finset_sum'; intro i _
    apply integrableOn_finset_sum'; intro j _
    apply integrableOn_finset_sum'; intro k _
    have hc : IntegrableOn (fun _ : Type2 => g i j k) (triSet i j k) volume :=
      integrableOn_const_of_subset_unitSquare (triSet_subset i j k) (g i j k)
    exact (hc.integrable_indicator (measurableSet_triSet i j k)).integrableOn
  exact hsum.congr_fun (fun x hx => (stepFunc_eq_sum_indicator g hx).symm) measurableSet_unitSquare

lemma integrableOn_step2D (G : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℝ) :
    IntegrableOn
      (fun p : Type2 × Type2 =>
        G (cell6 p.1.1) (cell6 p.1.2) (kind6 p.1) (cell6 p.2.1) (cell6 p.2.2) (kind6 p.2))
      profileDomain volume := by
  let S (i1 j1 k1 i2 j2 k2 : ℕ) : Set (Type2 × Type2) := triSet i1 j1 k1 ×ˢ triSet i2 j2 k2
  have hmeasS : ∀ i1 j1 k1 i2 j2 k2, MeasurableSet (S i1 j1 k1 i2 j2 k2) :=
    fun i1 j1 k1 i2 j2 k2 => (measurableSet_triSet i1 j1 k1).prod (measurableSet_triSet i2 j2 k2)
  have hsubS : ∀ i1 j1 k1 i2 j2 k2, S i1 j1 k1 i2 j2 k2 ⊆ profileDomain :=
    fun i1 j1 k1 i2 j2 k2 _ hp => ⟨hp.1.1, hp.2.1⟩
  have hsum : IntegrableOn
      (fun p : Type2 × Type2 =>
        ∑ i1 ∈ Finset.range 6, ∑ j1 ∈ Finset.range 6, ∑ k1 ∈ Finset.range 2,
          ∑ i2 ∈ Finset.range 6, ∑ j2 ∈ Finset.range 6, ∑ k2 ∈ Finset.range 2,
            (S i1 j1 k1 i2 j2 k2).indicator (fun _ => G i1 j1 k1 i2 j2 k2) p)
      profileDomain volume := by
    apply integrableOn_finset_sum'; intro i1 _
    apply integrableOn_finset_sum'; intro j1 _
    apply integrableOn_finset_sum'; intro k1 _
    apply integrableOn_finset_sum'; intro i2 _
    apply integrableOn_finset_sum'; intro j2 _
    apply integrableOn_finset_sum'; intro k2 _
    have hc := integrableOn_const_of_subset_profileDomain (hsubS i1 j1 k1 i2 j2 k2) (G i1 j1 k1 i2 j2 k2)
    exact (hc.integrable_indicator (hmeasS i1 j1 k1 i2 j2 k2)).integrableOn
  refine hsum.congr_fun (fun p hp => ?_) measurableSet_profileDomain
  rcases hp with ⟨hp1, hp2⟩
  rw [stepFunc_eq_sum_indicator (fun i1 j1 k1 => G i1 j1 k1 (cell6 p.2.1) (cell6 p.2.2) (kind6 p.2)) hp1]
  symm
  apply Finset.sum_congr rfl; intro i1 _
  apply Finset.sum_congr rfl; intro j1 _
  apply Finset.sum_congr rfl; intro k1 _
  by_cases h1 : p.1 ∈ triSet i1 j1 k1
  · simp only [h1, Set.indicator_of_mem]
    rw [stepFunc_eq_sum_indicator (G i1 j1 k1) hp2]
    apply Finset.sum_congr rfl; intro i2 _
    apply Finset.sum_congr rfl; intro j2 _
    apply Finset.sum_congr rfl; intro k2 _
    by_cases h2 : p.2 ∈ triSet i2 j2 k2
    · have hpS : p ∈ S i1 j1 k1 i2 j2 k2 := ⟨h1, h2⟩
      simp [hpS, h2]
    · have hpS : p ∉ S i1 j1 k1 i2 j2 k2 := fun h => h2 h.2
      simp [hpS, h2]
  · simp only [h1, not_false_eq_true, Set.indicator_of_notMem]
    symm
    apply Finset.sum_eq_zero; intro i2 _
    apply Finset.sum_eq_zero; intro j2 _
    apply Finset.sum_eq_zero; intro k2 _
    have hpS : p ∉ S i1 j1 k1 i2 j2 k2 := fun h => h1 h.1
    simp [hpS]

/-! ### Exact Integration of Step Functions on `unitSquare` -/

lemma setIntegral_step1D (g : ℕ → ℕ → ℕ → ℝ) :
    ∫ x in unitSquare, g (cell6 x.1) (cell6 x.2) (kind6 x) =
      (1 / 72 : ℝ) * ∑ i ∈ Finset.range 6, ∑ j ∈ Finset.range 6, (g i j 0 + g i j 1) := by
  have hint : IntegrableOn (fun x : Type2 => g (cell6 x.1) (cell6 x.2) (kind6 x)) unitSquare volume :=
    integrableOn_step1D g
  have hslice : ∀ x1 : ℝ, IntegrableOn (fun x2 : ℝ => g (cell6 x1) (cell6 x2) (kind6 (x1, x2))) (Icc 0 1) volume := by
    intro x1
    let Sj (j k : ℕ) : Set ℝ := { x2 ∈ Icc (0 : ℝ) 1 | cell6 x2 = j ∧ kind6 (x1, x2) = k }
    have hmSj : ∀ j k, MeasurableSet (Sj j k) := by
      intro j k
      have h1 : MeasurableSet { x2 : ℝ | cell6 x2 = j } :=
        measurable_cell6 (MeasurableSingletonClass.measurableSet_singleton j)
      have h2 : MeasurableSet { x2 : ℝ | kind6 (x1, x2) = k } :=
        (measurable_kind6.comp (measurable_const.prodMk measurable_id))
          (MeasurableSingletonClass.measurableSet_singleton k)
      exact measurableSet_Icc.inter (h1.inter h2)
    have hsum : IntegrableOn
        (fun x2 : ℝ => ∑ j ∈ Finset.range 6, ∑ k ∈ Finset.range 2,
          (Sj j k).indicator (fun _ => g (cell6 x1) j k) x2) (Icc 0 1) volume := by
      apply integrableOn_finset_sum'; intro j _
      apply integrableOn_finset_sum'; intro k _
      have hc : IntegrableOn (fun _ : ℝ => g (cell6 x1) j k) (Sj j k) volume :=
        integrableOn_const (ne_of_lt (lt_of_le_of_lt (measure_mono (fun _ h => h.1))
          (by rw [volume_Icc_zero_one]; exact ENNReal.one_lt_top)))
      exact (hc.integrable_indicator (hmSj j k)).integrableOn
    refine hsum.congr_fun (fun x2 hx2 => ?_) measurableSet_Icc
    dsimp only
    rw [Finset.sum_eq_single (cell6 x2)]
    · rw [Finset.sum_eq_single (kind6 (x1, x2))]
      · have hm : x2 ∈ Sj (cell6 x2) (kind6 (x1, x2)) := ⟨hx2, rfl, rfl⟩
        simp [hm]
      · intro k' _ hk'; have hn : x2 ∉ Sj (cell6 x2) k' := fun h => hk' h.2.2.symm; simp [hn]
      · intro habs; exact absurd (Finset.mem_range.mpr (kind6_lt (x1, x2))) habs
    · intro j' _ hj'; apply Finset.sum_eq_zero; intro k' _
      have hn : x2 ∉ Sj j' k' := fun h => hj' h.2.1.symm; simp [hn]
    · intro habs; exact absurd (Finset.mem_range.mpr (cell6_lt x2)) habs
  unfold unitSquare at hint ⊢
  rw [setIntegral_prod_eq hint]
  let p6 : ℕ → ℝ := fun m => (m : ℝ) / 6
  have hp6_0 : p6 0 = 0 := by simp [p6]
  have hp6_6 : p6 6 = 1 := by norm_num [p6]
  have hp6_mono : ∀ m < 6, p6 m ≤ p6 (m + 1) := by intro m _; simp only [p6]; push_cast; linarith
  have houter_int : IntegrableOn (fun x1 => ∫ x2 in Icc (0 : ℝ) 1, g (cell6 x1) (cell6 x2) (kind6 (x1, x2)))
      (Icc (0 : ℝ) 1) volume := by
    unfold IntegrableOn at hint ⊢
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at hint
    exact hint.integral_prod_left
  have hpart_out := setIntegral_Icc_partition 6 p6
    (fun x1 => ∫ x2 in Icc (0 : ℝ) 1, g (cell6 x1) (cell6 x2) (kind6 (x1, x2)))
    hp6_mono (by simpa [hp6_0, hp6_6] using houter_int)
  simp only [hp6_0, hp6_6] at hpart_out
  rw [hpart_out]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hi6 : i < 6 := Finset.mem_range.mp hi
  have hinner_eq : ∀ x1 ∈ Ioo (p6 i) (p6 (i + 1)),
      (∫ x2 in Icc (0 : ℝ) 1, g (cell6 x1) (cell6 x2) (kind6 (x1, x2))) =
        ∑ j ∈ Finset.range 6,
          (((1 / 6 - (x1 - p6 i)) * g i j 0) + ((x1 - p6 i) * g i j 1)) := by
    intro x1 hx1
    have hci : cell6 x1 = i := cell6_eq_of_Ioo hi6 hx1.1 hx1.2
    have hsl := hslice x1
    have hpart_in := setIntegral_Icc_partition 6 p6
      (fun x2 => g (cell6 x1) (cell6 x2) (kind6 (x1, x2)))
      hp6_mono (by simpa [hp6_0, hp6_6] using hsl)
    simp only [hp6_0, hp6_6] at hpart_in
    rw [hpart_in]
    apply Finset.sum_congr rfl
    intro j hj
    have hj6 : j < 6 := Finset.mem_range.mp hj
    let mid : ℝ := p6 (j + 1) - (x1 - p6 i)
    have hx1_lt : x1 < ((i + 1 : ℕ) : ℝ) / 6 := hx1.2
    have hx1_gt : (i : ℝ) / 6 < x1 := hx1.1
    push_cast at hx1_lt
    have hmid1 : p6 j ≤ mid := by
      simp only [mid, p6]; push_cast; linarith
    have hmid2 : mid ≤ p6 (j + 1) := by
      simp only [mid, p6]; push_cast; linarith
    have hj_end : p6 (j + 1) ≤ 1 := by
      have hle : (j + 1 : ℕ) ≤ 6 := by omega
      have hle' : ((j + 1 : ℕ) : ℝ) ≤ 6 := by exact_mod_cast hle
      simp only [p6]; linarith
    have hj_int : IntegrableOn (fun x2 => g (cell6 x1) (cell6 x2) (kind6 (x1, x2)))
        (Icc (p6 j) (p6 (j + 1))) volume :=
      hsl.mono_set (Icc_subset_Icc (by simp [p6]; positivity) hj_end)
    rw [setIntegral_Icc_split hmid1 hmid2 hj_int]
    have hL : ∫ x2 in Icc (p6 j) mid, g (cell6 x1) (cell6 x2) (kind6 (x1, x2)) =
        (1 / 6 - (x1 - p6 i)) * g i j 0 := by
      rw [integral_Icc_eq_integral_Ioc, integral_Ioc_eq_integral_Ioo]
      have hcongr : EqOn (fun x2 => g (cell6 x1) (cell6 x2) (kind6 (x1, x2)))
          (fun _ => g i j 0) (Ioo (p6 j) mid) := by
        intro x2 hx2
        have hcj : cell6 x2 = j := cell6_eq_of_Ioo hj6 hx2.1 (lt_of_lt_of_le hx2.2 hmid2)
        have hk0 : kind6 (x1, x2) = 0 := by
          unfold kind6
          rw [hci, hcj]
          split_ifs with hcond
          · rfl
          · exfalso; simp only [mid, p6] at hx2; push_cast at hx2; linarith [hx2.2]
        simp [hci, hcj, hk0]
      rw [setIntegral_congr_fun measurableSet_Ioo hcongr, ← integral_Ioc_eq_integral_Ioo,
        ← integral_Icc_eq_integral_Ioc, setIntegral_Icc_const hmid1]
      simp only [mid, p6]; push_cast; ring
    have hR : ∫ x2 in Icc mid (p6 (j + 1)), g (cell6 x1) (cell6 x2) (kind6 (x1, x2)) =
        (x1 - p6 i) * g i j 1 := by
      rw [integral_Icc_eq_integral_Ioc, integral_Ioc_eq_integral_Ioo]
      have hcongr : EqOn (fun x2 => g (cell6 x1) (cell6 x2) (kind6 (x1, x2)))
          (fun _ => g i j 1) (Ioo mid (p6 (j + 1))) := by
        intro x2 hx2
        have hcj : cell6 x2 = j := cell6_eq_of_Ioo hj6 (lt_of_le_of_lt hmid1 hx2.1) hx2.2
        have hk1 : kind6 (x1, x2) = 1 := by
          unfold kind6
          rw [hci, hcj]
          split_ifs with hcond
          · exfalso; simp only [mid, p6] at hx2; push_cast at hx2; linarith [hx2.1]
          · rfl
        simp [hci, hcj, hk1]
      rw [setIntegral_congr_fun measurableSet_Ioo hcongr, ← integral_Ioc_eq_integral_Ioo,
        ← integral_Icc_eq_integral_Ioc, setIntegral_Icc_const hmid2]
      simp only [mid, p6]; push_cast; ring
    rw [hL, hR]
  rw [integral_Icc_eq_integral_Ioc, integral_Ioc_eq_integral_Ioo,
    setIntegral_congr_fun measurableSet_Ioo hinner_eq,
    ← integral_Ioc_eq_integral_Ioo, ← integral_Icc_eq_integral_Ioc]
  rw [setIntegral_finset_sum' (Finset.range 6) (fun j _ => by
    apply ContinuousOn.integrableOn_Icc; fun_prop)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hip : p6 i ≤ p6 (i + 1) := hp6_mono i hi6
  have hlin : (fun x1 : ℝ => (1 / 6 - (x1 - p6 i)) * g i j 0 + (x1 - p6 i) * g i j 1) =
      (fun x1 : ℝ => ((1 / 6 + p6 i) * g i j 0 - p6 i * g i j 1) + (g i j 1 - g i j 0) * x1) := by
    ext x1; ring
  rw [hlin, setIntegral_Icc_affine hip]
  simp only [p6]; push_cast; ring

/-! ### Definition of `M_bic` and Proof of Feasibility, BIC, IR, and Expected Revenue -/

noncomputable def q11Val (i1 j1 k1 i2 j2 k2 : ℕ) : ℝ :=
  (q11Int i1 j1 k1 i2 j2 k2 : ℝ) / 18

noncomputable def q12Val (i1 j1 k1 i2 j2 k2 : ℕ) : ℝ :=
  (q12Int i1 j1 k1 i2 j2 k2 : ℝ) / 18

noncomputable def t1Val (i j k : ℕ) : ℝ :=
  (t1Int i j k : ℝ) / 7776

noncomputable def M_bic : Mechanism where
  q11 x y := q11Val (cell6 x.1) (cell6 x.2) (kind6 x) (cell6 y.1) (cell6 y.2) (kind6 y)
  q12 x y := q12Val (cell6 x.1) (cell6 x.2) (kind6 x) (cell6 y.1) (cell6 y.2) (kind6 y)
  q21 x y := q11Val (cell6 y.1) (cell6 y.2) (kind6 y) (cell6 x.1) (cell6 x.2) (kind6 x)
  q22 x y := q12Val (cell6 y.1) (cell6 y.2) (kind6 y) (cell6 x.1) (cell6 x.2) (kind6 x)
  t1 x _ := t1Val (cell6 x.1) (cell6 x.2) (kind6 x)
  t2 _ y := t1Val (cell6 y.1) (cell6 y.2) (kind6 y)

lemma M_bic_feasible : IsFeasible M_bic := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x _ y _
    have hx1 := cell6_lt x.1; have hx2 := cell6_lt x.2; have hxk := kind6_lt x
    have hy1 := cell6_lt y.1; have hy2 := cell6_lt y.2; have hyk := kind6_lt y
    have hf1 := q11Int_feas hx1 hx2 hxk hy1 hy2 hyk
    have hf1' := q11Int_feas hy1 hy2 hyk hx1 hx2 hxk
    have hf2 := q11Int_feas hx2 hx1 hxk hy2 hy1 hyk
    have hf2' := q11Int_feas hy2 hy1 hyk hx2 hx1 hxk
    have h1a : (0 : ℝ) ≤ (q11Int (cell6 x.1) (cell6 x.2) (kind6 x) (cell6 y.1) (cell6 y.2) (kind6 y) : ℝ) := by exact_mod_cast hf1.1
    have h1b : (0 : ℝ) ≤ (q11Int (cell6 y.1) (cell6 y.2) (kind6 y) (cell6 x.1) (cell6 x.2) (kind6 x) : ℝ) := by exact_mod_cast hf1'.1
    have h1c : (q11Int (cell6 x.1) (cell6 x.2) (kind6 x) (cell6 y.1) (cell6 y.2) (kind6 y) : ℝ) +
        (q11Int (cell6 y.1) (cell6 y.2) (kind6 y) (cell6 x.1) (cell6 x.2) (kind6 x) : ℝ) ≤ 18 := by exact_mod_cast hf1.2
    have h2a : (0 : ℝ) ≤ (q11Int (cell6 x.2) (cell6 x.1) (kind6 x) (cell6 y.2) (cell6 y.1) (kind6 y) : ℝ) := by exact_mod_cast hf2.1
    have h2b : (0 : ℝ) ≤ (q11Int (cell6 y.2) (cell6 y.1) (kind6 y) (cell6 x.2) (cell6 x.1) (kind6 x) : ℝ) := by exact_mod_cast hf2'.1
    have h2c : (q11Int (cell6 x.2) (cell6 x.1) (kind6 x) (cell6 y.2) (cell6 y.1) (kind6 y) : ℝ) +
        (q11Int (cell6 y.2) (cell6 y.1) (kind6 y) (cell6 x.2) (cell6 x.1) (kind6 x) : ℝ) ≤ 18 := by exact_mod_cast hf2.2
    dsimp [M_bic, q11Val, q12Val, q12Int, q11Int] at *
    refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩
  · exact integrableOn_step2D q11Val
  · exact integrableOn_step2D q12Val
  · exact integrableOn_step2D (fun i1 j1 k1 i2 j2 k2 => q11Val i2 j2 k2 i1 j1 k1)
  · exact integrableOn_step2D (fun i1 j1 k1 i2 j2 k2 => q12Val i2 j2 k2 i1 j1 k1)
  · exact integrableOn_step2D (fun i1 j1 k1 _ _ _ => t1Val i1 j1 k1)
  · exact integrableOn_step2D (fun _ _ _ i2 j2 k2 => t1Val i2 j2 k2)

lemma Q11_M_bic (x : Type2) :
    Q11 M_bic x = (qSum1Int (cell6 x.1) (cell6 x.2) (kind6 x) : ℝ) / 1296 := by
  unfold Q11 M_bic
  dsimp only
  rw [setIntegral_step1D (fun i2 j2 k2 => q11Val (cell6 x.1) (cell6 x.2) (kind6 x) i2 j2 k2)]
  have hrow := q11Int_rowSum (cell6_lt x.1) (cell6_lt x.2) (kind6_lt x)
  have hcast : (∑ i2 ∈ Finset.range 6, ∑ j2 ∈ Finset.range 6,
      (q11Val (cell6 x.1) (cell6 x.2) (kind6 x) i2 j2 0 +
       q11Val (cell6 x.1) (cell6 x.2) (kind6 x) i2 j2 1)) =
      (qSum1Int (cell6 x.1) (cell6 x.2) (kind6 x) : ℝ) / 18 := by
    rw [← hrow]
    unfold q11Val
    push_cast
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl; intro i2 _
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl; intro j2 _
    simp [Finset.sum_range_succ]
    ring
  rw [hcast]
  ring

lemma Q12_M_bic (x : Type2) :
    Q12 M_bic x = (qSum2Int (cell6 x.1) (cell6 x.2) (kind6 x) : ℝ) / 1296 := by
  unfold Q12 M_bic
  dsimp only
  rw [setIntegral_step1D (fun i2 j2 k2 => q12Val (cell6 x.1) (cell6 x.2) (kind6 x) i2 j2 k2)]
  have hswap : (∑ i2 ∈ Finset.range 6, ∑ j2 ∈ Finset.range 6,
      (q12Val (cell6 x.1) (cell6 x.2) (kind6 x) i2 j2 0 +
       q12Val (cell6 x.1) (cell6 x.2) (kind6 x) i2 j2 1)) =
      ∑ j2 ∈ Finset.range 6, ∑ i2 ∈ Finset.range 6,
      (q11Val (cell6 x.2) (cell6 x.1) (kind6 x) j2 i2 0 +
       q11Val (cell6 x.2) (cell6 x.1) (kind6 x) j2 i2 1) := by
    rw [Finset.sum_comm]
    rfl
  rw [hswap]
  have hrow := q11Int_rowSum (cell6_lt x.2) (cell6_lt x.1) (kind6_lt x)
  have hcast : (∑ j2 ∈ Finset.range 6, ∑ i2 ∈ Finset.range 6,
      (q11Val (cell6 x.2) (cell6 x.1) (kind6 x) j2 i2 0 +
       q11Val (cell6 x.2) (cell6 x.1) (kind6 x) j2 i2 1)) =
      (qSum2Int (cell6 x.1) (cell6 x.2) (kind6 x) : ℝ) / 18 := by
    unfold qSum2Int
    change _ = (qSum1Int (cell6 x.2) (cell6 x.1) (kind6 x) : ℝ) / 18
    rw [← hrow]
    unfold q11Val
    push_cast
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl; intro j2 _
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl; intro i2 _
    simp [Finset.sum_range_succ]
    ring
  rw [hcast]
  ring

lemma T1_M_bic (x : Type2) :
    T1 M_bic x = t1Val (cell6 x.1) (cell6 x.2) (kind6 x) := by
  unfold T1 M_bic
  dsimp only
  rw [setIntegral_const, volume_real_unitSquare, one_smul]

lemma Q21_M_bic (y : Type2) : Q21 M_bic y = Q11 M_bic y := rfl
lemma Q22_M_bic (y : Type2) : Q22 M_bic y = Q12 M_bic y := rfl
lemma T2_M_bic (y : Type2) : T2 M_bic y = T1 M_bic y := rfl

/-! ### Barycentric Convex Combination Proof of Pointwise BIC and Interim IR -/

lemma vert_ic_real {vi vj ip jp kp : ℕ}
    (hvi : vi < 7) (hvj : vj < 7) (hip : ip < 6) (hjp : jp < 6) (hkp : kp < 2) :
    (vi : ℝ) * (qSum1Int ip jp kp : ℝ) + (vj : ℝ) * (qSum2Int ip jp kp : ℝ) -
      (t1Int ip jp kp : ℝ) ≤ (uVertInt vi vj : ℝ) := by
  have h := uVert_ic hvi hvj hip hjp hkp
  exact_mod_cast h

lemma vert_nonneg_real {vi vj : ℕ} (hvi : vi < 7) (hvj : vj < 7) :
    (0 : ℝ) ≤ (uVertInt vi vj : ℝ) := by
  exact_mod_cast uVert_nonneg hvi hvj

lemma interim_report_le_and_ir {x : Type2} (hx : x ∈ unitSquare)
    {ip jp kp : ℕ} (hip : ip < 6) (hjp : jp < 6) (hkp : kp < 2) :
    (0 ≤ x.1 * Q11 M_bic x + x.2 * Q12 M_bic x - T1 M_bic x) ∧
    (x.1 * ((qSum1Int ip jp kp : ℝ) / 1296) + x.2 * ((qSum2Int ip jp kp : ℝ) / 1296) -
      t1Val ip jp kp ≤ x.1 * Q11 M_bic x + x.2 * Q12 M_bic x - T1 M_bic x) := by
  rw [Q11_M_bic, Q12_M_bic, T1_M_bic]
  set i := cell6 x.1 with hi_def
  set j := cell6 x.2 with hj_def
  have hi : i < 6 := cell6_lt x.1
  have hj : j < 6 := cell6_lt x.2
  have hb1 := cell6_bounds hx.1
  have hb2 := cell6_bounds hx.2
  rw [← hi_def] at hb1
  rw [← hj_def] at hb2
  have hgrad := uVert_grad hi hj
  have hg10 : (qSum1Int i j 0 : ℝ) = (uVertInt (i + 1) j : ℝ) - (uVertInt i j : ℝ) := by exact_mod_cast hgrad.1
  have hg20 : (qSum2Int i j 0 : ℝ) = (uVertInt i (j + 1) : ℝ) - (uVertInt i j : ℝ) := by exact_mod_cast hgrad.2.1
  have hg11 : (qSum1Int i j 1 : ℝ) = (uVertInt (i + 1) (j + 1) : ℝ) - (uVertInt i (j + 1) : ℝ) := by exact_mod_cast hgrad.2.2.1
  have hg21 : (qSum2Int i j 1 : ℝ) = (uVertInt (i + 1) (j + 1) : ℝ) - (uVertInt (i + 1) j : ℝ) := by exact_mod_cast hgrad.2.2.2
  set u := 6 * x.1 - (i : ℝ)
  set v := 6 * x.2 - (j : ℝ)
  have hu0 : 0 ≤ u := by simp only [u]; linarith [hb1.1]
  have hu1 : u ≤ 1 := by simp only [u]; push_cast at hb1; linarith [hb1.2]
  have hv0 : 0 ≤ v := by simp only [v]; linarith [hb2.1]
  have hv1 : v ≤ 1 := by simp only [v]; push_cast at hb2; linarith [hb2.2]
  have hx1_eq : x.1 = ((i : ℝ) + u) / 6 := by simp only [u]; ring
  have hx2_eq : x.2 = ((j : ℝ) + v) / 6 := by simp only [v]; ring
  have hi7 : i < 7 := by omega
  have hj7 : j < 7 := by omega
  have hi17 : i + 1 < 7 := by omega
  have hj17 : j + 1 < 7 := by omega
  have hic00 := vert_ic_real hi7 hj7 hip hjp hkp
  have hic10 := vert_ic_real hi17 hj7 hip hjp hkp
  have hic01 := vert_ic_real hi7 hj17 hip hjp hkp
  have hic11 := vert_ic_real hi17 hj17 hip hjp hkp
  have hir00 := vert_nonneg_real hi7 hj7
  have hir10 := vert_nonneg_real hi17 hj7
  have hir01 := vert_nonneg_real hi7 hj17
  have hir11 := vert_nonneg_real hi17 hj17
  by_cases huv : u + v ≤ 1
  · have hk0 : kind6 x = 0 := by unfold kind6; rw [← hi_def, ← hj_def]; exact ite_eq_left_of_eq_true _ _ (eq_true huv)
    rw [hk0]
    have ht0 : t1Val i j 0 =
        ((i : ℝ) * (qSum1Int i j 0 : ℝ) + (j : ℝ) * (qSum2Int i j 0 : ℝ) - (uVertInt i j : ℝ)) / 7776 := by
      unfold t1Val t1Int; simp only [Int.ofNat_eq_natCast]; push_cast; ring
    rw [ht0, hx1_eq, hx2_eq]
    unfold t1Val
    have hw0 : 0 ≤ 1 - u - v := by linarith
    have htrue_eq :
        ((i : ℝ) + u) / 6 * ((qSum1Int i j 0 : ℝ) / 1296) +
        ((j : ℝ) + v) / 6 * ((qSum2Int i j 0 : ℝ) / 1296) -
        ((i : ℝ) * (qSum1Int i j 0 : ℝ) + (j : ℝ) * (qSum2Int i j 0 : ℝ) - (uVertInt i j : ℝ)) / 7776 =
        ((1 - u - v) * (uVertInt i j : ℝ) + u * (uVertInt (i + 1) j : ℝ) + v * (uVertInt i (j + 1) : ℝ)) / 7776 := by
      rw [hg10, hg20]; ring
    have hrep_eq :
        ((i : ℝ) + u) / 6 * ((qSum1Int ip jp kp : ℝ) / 1296) +
        ((j : ℝ) + v) / 6 * ((qSum2Int ip jp kp : ℝ) / 1296) -
        (t1Int ip jp kp : ℝ) / 7776 =
        ((1 - u - v) * ((i : ℝ) * (qSum1Int ip jp kp : ℝ) + (j : ℝ) * (qSum2Int ip jp kp : ℝ) - (t1Int ip jp kp : ℝ)) +
         u * (((i + 1 : ℕ) : ℝ) * (qSum1Int ip jp kp : ℝ) + (j : ℝ) * (qSum2Int ip jp kp : ℝ) - (t1Int ip jp kp : ℝ)) +
         v * ((i : ℝ) * (qSum1Int ip jp kp : ℝ) + ((j + 1 : ℕ) : ℝ) * (qSum2Int ip jp kp : ℝ) - (t1Int ip jp kp : ℝ))) / 7776 := by
      push_cast; ring
    rw [htrue_eq, hrep_eq]
    constructor
    · have h0 := mul_nonneg hw0 hir00
      have h1 := mul_nonneg hu0 hir10
      have h2 := mul_nonneg hv0 hir01
      linarith
    · have h0 := mul_le_mul_of_nonneg_left hic00 hw0
      have h1 := mul_le_mul_of_nonneg_left hic10 hu0
      have h2 := mul_le_mul_of_nonneg_left hic01 hv0
      linarith
  · have hk1 : kind6 x = 1 := by unfold kind6; rw [← hi_def, ← hj_def]; exact ite_eq_right_of_eq_false _ _ (eq_false huv)
    rw [hk1]
    have ht1 : t1Val i j 1 =
        (((i + 1 : ℕ) : ℝ) * (qSum1Int i j 1 : ℝ) + ((j + 1 : ℕ) : ℝ) * (qSum2Int i j 1 : ℝ) -
          (uVertInt (i + 1) (j + 1) : ℝ)) / 7776 := by
      unfold t1Val t1Int; simp only [Int.ofNat_eq_natCast]; push_cast; ring
    rw [ht1, hx1_eq, hx2_eq]
    unfold t1Val
    have hw0 : 0 ≤ u + v - 1 := by linarith
    have hw1 : 0 ≤ 1 - u := by linarith
    have hw2 : 0 ≤ 1 - v := by linarith
    have htrue_eq :
        ((i : ℝ) + u) / 6 * ((qSum1Int i j 1 : ℝ) / 1296) +
        ((j : ℝ) + v) / 6 * ((qSum2Int i j 1 : ℝ) / 1296) -
        (((i + 1 : ℕ) : ℝ) * (qSum1Int i j 1 : ℝ) + ((j + 1 : ℕ) : ℝ) * (qSum2Int i j 1 : ℝ) -
          (uVertInt (i + 1) (j + 1) : ℝ)) / 7776 =
        ((u + v - 1) * (uVertInt (i + 1) (j + 1) : ℝ) +
         (1 - u) * (uVertInt i (j + 1) : ℝ) +
         (1 - v) * (uVertInt (i + 1) j : ℝ)) / 7776 := by
      rw [hg11, hg21]; push_cast; ring
    have hrep_eq :
        ((i : ℝ) + u) / 6 * ((qSum1Int ip jp kp : ℝ) / 1296) +
        ((j : ℝ) + v) / 6 * ((qSum2Int ip jp kp : ℝ) / 1296) -
        (t1Int ip jp kp : ℝ) / 7776 =
        ((u + v - 1) * (((i + 1 : ℕ) : ℝ) * (qSum1Int ip jp kp : ℝ) + ((j + 1 : ℕ) : ℝ) * (qSum2Int ip jp kp : ℝ) - (t1Int ip jp kp : ℝ)) +
         (1 - u) * ((i : ℝ) * (qSum1Int ip jp kp : ℝ) + ((j + 1 : ℕ) : ℝ) * (qSum2Int ip jp kp : ℝ) - (t1Int ip jp kp : ℝ)) +
         (1 - v) * (((i + 1 : ℕ) : ℝ) * (qSum1Int ip jp kp : ℝ) + (j : ℝ) * (qSum2Int ip jp kp : ℝ) - (t1Int ip jp kp : ℝ))) / 7776 := by
      push_cast; ring
    rw [htrue_eq, hrep_eq]
    constructor
    · have h0 := mul_nonneg hw0 hir11
      have h1 := mul_nonneg hw1 hir01
      have h2 := mul_nonneg hw2 hir10
      linarith
    · have h0 := mul_le_mul_of_nonneg_left hic11 hw0
      have h1 := mul_le_mul_of_nonneg_left hic01 hw1
      have h2 := mul_le_mul_of_nonneg_left hic10 hw2
      linarith

lemma M_bic_isBIC : IsBIC M_bic := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x _
    refine ⟨?_, ?_, ?_⟩
    · exact integrableOn_step1D (fun i2 j2 k2 => q11Val (cell6 x.1) (cell6 x.2) (kind6 x) i2 j2 k2)
    · exact integrableOn_step1D (fun i2 j2 k2 => q12Val (cell6 x.1) (cell6 x.2) (kind6 x) i2 j2 k2)
    · exact integrableOn_const_of_subset_unitSquare Subset.rfl _
  · intro y _
    refine ⟨?_, ?_, ?_⟩
    · exact integrableOn_step1D (fun i1 j1 k1 => q11Val (cell6 y.1) (cell6 y.2) (kind6 y) i1 j1 k1)
    · exact integrableOn_step1D (fun i1 j1 k1 => q12Val (cell6 y.1) (cell6 y.2) (kind6 y) i1 j1 k1)
    · exact integrableOn_const_of_subset_unitSquare Subset.rfl _
  · intro x hx x' _
    have h := (interim_report_le_and_ir hx (cell6_lt x'.1) (cell6_lt x'.2) (kind6_lt x')).2
    rw [← Q11_M_bic x', ← Q12_M_bic x', ← T1_M_bic x'] at h
    exact h
  · intro y hy y' _
    rw [Q21_M_bic, Q22_M_bic, T2_M_bic, Q21_M_bic, Q22_M_bic, T2_M_bic]
    have h := (interim_report_le_and_ir hy (cell6_lt y'.1) (cell6_lt y'.2) (kind6_lt y')).2
    rw [← Q11_M_bic y', ← Q12_M_bic y', ← T1_M_bic y'] at h
    exact h

lemma M_bic_isInterimIR : IsInterimIR M_bic := by
  constructor
  · intro x hx
    exact (interim_report_le_and_ir (ip := 0) (jp := 0) (kp := 0) hx (by omega) (by omega) (by omega)).1
  · intro y hy
    rw [Q21_M_bic, Q22_M_bic, T2_M_bic]
    exact (interim_report_le_and_ir (ip := 0) (jp := 0) (kp := 0) hy (by omega) (by omega) (by omega)).1

lemma M_bic_expectedRevenue : ExpectedRevenue M_bic = 62105 / 69984 := by
  unfold ExpectedRevenue
  have hf := M_bic_feasible
  have ht1 : IntegrableOn (fun p : Type2 × Type2 => M_bic.t1 p.1 p.2) profileDomain volume := hf.2.2.2.2.2.1
  have ht2 : IntegrableOn (fun p : Type2 × Type2 => M_bic.t2 p.1 p.2) profileDomain volume := hf.2.2.2.2.2.2
  rw [integral_add ht1 ht2]
  have h1 : (∫ p in profileDomain, M_bic.t1 p.1 p.2) =
      ∫ x in unitSquare, t1Val (cell6 x.1) (cell6 x.2) (kind6 x) := by
    unfold profileDomain at ht1 ⊢
    rw [setIntegral_prod_eq ht1]
    apply setIntegral_congr_fun measurableSet_unitSquare
    intro x _
    exact T1_M_bic x
  have h2 : (∫ p in profileDomain, M_bic.t2 p.1 p.2) =
      ∫ y in unitSquare, t1Val (cell6 y.1) (cell6 y.2) (kind6 y) := by
    unfold profileDomain at ht2 ⊢
    rw [setIntegral_prod_symm_eq ht2]
    apply setIntegral_congr_fun measurableSet_unitSquare
    intro y _
    exact (T2_M_bic y).trans (T1_M_bic y)
  rw [h1, h2, setIntegral_step1D t1Val]
  have hsum : (∑ i ∈ Finset.range 6, ∑ j ∈ Finset.range 6, (t1Val i j 0 + t1Val i j 1)) =
      (bicRevSum : ℝ) / 7776 := by
    unfold bicRevSum range6Sum range2Sum t1Val
    push_cast
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    ring
  rw [hsum, bicRevSum_eq]
  norm_num

end AuctionSep.BICWitness
