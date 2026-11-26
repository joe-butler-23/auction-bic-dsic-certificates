import AuctionSep.Problem
import AuctionSep.CertData
import AuctionSep.MeasureLemmas

open MeasureTheory Set AuctionSep.CertData AuctionSep.MeasureLemmas

namespace AuctionSep.DSICBound

/-! ### Section 1: Unpacking Dual Certificate Data (`K = 4, m = 4`) -/

lemma of_range4All {f : Nat → Bool} (h : range4All f = true) {i : Nat} (hi : i < 4) :
    f i = true := by
  unfold range4All at h
  simp only [Bool.and_eq_true] at h
  interval_cases i <;> tauto

lemma a1Ext_nonneg {si sj i j : ℕ} (hsi : si < 4) (hsj : sj < 4) (hj : j < 4) :
    (0 : ℝ) ≤ (a1Ext si sj i j : ℝ) := by
  unfold a1Ext
  by_cases hi : i < 4
  · simp only [hi, ↓reduceIte]
    have h := of_range4All (of_range4All (of_range4All (of_range4All dualNonnegCheck_true hsi) hsj) hi) hj
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact_mod_cast h.1
  · simp only [hi, ↓reduceIte]; norm_num

lemma a2Ext_nonneg {si sj i j : ℕ} (hsi : si < 4) (hsj : sj < 4) (hi : i < 4) :
    (0 : ℝ) ≤ (a2Ext si sj i j : ℝ) := by
  unfold a2Ext
  by_cases hj : j < 4
  · simp only [hj, ↓reduceIte]
    have h := of_range4All (of_range4All (of_range4All (of_range4All dualNonnegCheck_true hsi) hsj) hi) hj
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact_mod_cast h.2
  · simp only [hj, ↓reduceIte]; norm_num

lemma a1Ext_four (si sj j : ℕ) : (a1Ext si sj 4 j : ℝ) = 0 := by
  unfold a1Ext; simp

lemma a2Ext_four (si sj i : ℕ) : (a2Ext si sj i 4 : ℝ) = 0 := by
  unfold a2Ext; simp

lemma dualDiv_le_one {si sj i j : ℕ} (hsi : si < 4) (hsj : sj < 4) (hi : i < 4) (hj : j < 4) :
    4 * ((a1Ext si sj i j : ℝ) / 1920 - (a1Ext si sj (i + 1) j : ℝ) / 1920) +
    4 * ((a2Ext si sj i j : ℝ) / 1920 - (a2Ext si sj i (j + 1) : ℝ) / 1920) ≤ 1 := by
  have h := of_range4All (of_range4All (of_range4All (of_range4All dualDivCheck_true hsi) hsj) hi) hj
  simp only [decide_eq_true_eq] at h
  have hr : (4 * ((a1Ext si sj i j : ℝ) - (a1Ext si sj (i + 1) j : ℝ)) +
      4 * ((a2Ext si sj i j : ℝ) - (a2Ext si sj i (j + 1) : ℝ))) ≤ 1920 := by
    exact_mod_cast h
  linarith

@[irreducible] noncomputable def a1Real (si sj i j : ℕ) : ℝ := (a1Ext si sj i j : ℝ) / 1920
@[irreducible] noncomputable def a2Real (si sj i j : ℕ) : ℝ := (a2Ext si sj i j : ℝ) / 1920

lemma a1Real_nonneg {si sj i j : ℕ} (hsi : si < 4) (hsj : sj < 4) (hj : j < 4) :
    0 ≤ a1Real si sj i j := by
  unfold a1Real; exact div_nonneg (a1Ext_nonneg hsi hsj hj) (by norm_num)

lemma a2Real_nonneg {si sj i j : ℕ} (hsi : si < 4) (hsj : sj < 4) (hi : i < 4) :
    0 ≤ a2Real si sj i j := by
  unfold a2Real; exact div_nonneg (a2Ext_nonneg hsi hsj hi) (by norm_num)

lemma a1Real_four (si sj j : ℕ) : a1Real si sj 4 j = 0 := by
  unfold a1Real; simp [a1Ext_four]

lemma a2Real_four (si sj i : ℕ) : a2Real si sj i 4 = 0 := by
  unfold a2Real; simp [a2Ext_four]

lemma a12Real_div_le_one {si sj i j : ℕ} (hsi : si < 4) (hsj : sj < 4) (hi : i < 4) (hj : j < 4) :
    4 * (a1Real si sj i j - a1Real si sj (i + 1) j) +
    4 * (a2Real si sj i j - a2Real si sj i (j + 1)) ≤ 1 := by
  unfold a1Real a2Real
  exact dualDiv_le_one hsi hsj hi hj

/-! ### Section 2: 4-Grid Partition & Piecewise-Affine Dual Potentials -/

noncomputable def cell4 (t : ℝ) : ℕ :=
  if t < 1 / 4 then 0
  else if t < 2 / 4 then 1
  else if t < 3 / 4 then 2
  else 3

lemma cell4_lt (t : ℝ) : cell4 t < 4 := by
  unfold cell4; split_ifs <;> omega

lemma cell4_bounds {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ((cell4 t : ℕ) : ℝ) / 4 ≤ t ∧ t ≤ ((cell4 t + 1 : ℕ) : ℝ) / 4 := by
  rcases ht with ⟨ht0, ht1⟩
  unfold cell4
  split_ifs <;> push_cast <;> constructor <;> linarith

lemma cell4_eq_of_Ioo {i : ℕ} (hi : i < 4) {t : ℝ}
    (ht1 : (i : ℝ) / 4 < t) (ht2 : t < ((i + 1 : ℕ) : ℝ) / 4) :
    cell4 t = i := by
  interval_cases i <;> unfold cell4 <;> push_cast at ht1 ht2 <;> split_ifs <;> linarith

lemma measurable_cell4 : Measurable cell4 := by
  unfold cell4
  refine Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const ?_
  refine Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const ?_
  exact Measurable.ite (measurableSet_lt measurable_id measurable_const)
    measurable_const measurable_const

noncomputable def alpha1 (si sj : ℕ) (x : Type2) : ℝ :=
  let i := cell4 x.1
  let j := cell4 x.2
  let u := 4 * x.1 - (i : ℝ)
  (1 - u) * a1Real si sj i j + u * a1Real si sj (i + 1) j

noncomputable def alpha2 (si sj : ℕ) (x : Type2) : ℝ :=
  let i := cell4 x.1
  let j := cell4 x.2
  let v := 4 * x.2 - (j : ℝ)
  (1 - v) * a2Real si sj i j + v * a2Real si sj i (j + 1)

lemma measurable_alpha1 (si sj : ℕ) : Measurable (alpha1 si sj) := by
  unfold alpha1
  have hc1 : Measurable (fun x : Type2 => cell4 x.1) := measurable_cell4.comp measurable_fst
  have hc2 : Measurable (fun x : Type2 => cell4 x.2) := measurable_cell4.comp measurable_snd
  have hcr : Measurable (fun x : Type2 => ((cell4 x.1 : ℕ) : ℝ)) :=
    (Measurable.of_discrete (f := fun n : ℕ => (n : ℝ))).comp hc1
  have hu : Measurable (fun x : Type2 => 4 * x.1 - ((cell4 x.1 : ℕ) : ℝ)) :=
    (measurable_const.mul measurable_fst).sub hcr
  have haL : Measurable (fun x : Type2 => a1Real si sj (cell4 x.1) (cell4 x.2)) :=
    (Measurable.of_discrete (f := fun p : ℕ × ℕ => a1Real si sj p.1 p.2)).comp (hc1.prodMk hc2)
  have haR : Measurable (fun x : Type2 => a1Real si sj (cell4 x.1 + 1) (cell4 x.2)) :=
    (Measurable.of_discrete (f := fun p : ℕ × ℕ => a1Real si sj (p.1 + 1) p.2)).comp (hc1.prodMk hc2)
  exact ((measurable_const.sub hu).mul haL).add (hu.mul haR)

lemma measurable_alpha2 (si sj : ℕ) : Measurable (alpha2 si sj) := by
  unfold alpha2
  have hc1 : Measurable (fun x : Type2 => cell4 x.1) := measurable_cell4.comp measurable_fst
  have hc2 : Measurable (fun x : Type2 => cell4 x.2) := measurable_cell4.comp measurable_snd
  have hcr : Measurable (fun x : Type2 => ((cell4 x.2 : ℕ) : ℝ)) :=
    (Measurable.of_discrete (f := fun n : ℕ => (n : ℝ))).comp hc2
  have hv : Measurable (fun x : Type2 => 4 * x.2 - ((cell4 x.2 : ℕ) : ℝ)) :=
    (measurable_const.mul measurable_snd).sub hcr
  have haL : Measurable (fun x : Type2 => a2Real si sj (cell4 x.1) (cell4 x.2)) :=
    (Measurable.of_discrete (f := fun p : ℕ × ℕ => a2Real si sj p.1 p.2)).comp (hc1.prodMk hc2)
  have haR : Measurable (fun x : Type2 => a2Real si sj (cell4 x.1) (cell4 x.2 + 1)) :=
    (Measurable.of_discrete (f := fun p : ℕ × ℕ => a2Real si sj p.1 (p.2 + 1))).comp (hc1.prodMk hc2)
  exact ((measurable_const.sub hv).mul haL).add (hv.mul haR)

lemma exists_bound_alpha1 (si sj : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ unitSquare, |alpha1 si sj x| ≤ C := by
  let C : ℝ := ∑ i ∈ Finset.range 4, ∑ j ∈ Finset.range 4,
    (|a1Real si sj i j| + |a1Real si sj (i + 1) j|)
  refine ⟨C, by positivity, fun x hx => ?_⟩
  unfold alpha1
  set i := cell4 x.1 with hi_def
  set j := cell4 x.2 with hj_def
  have hb := cell4_bounds hx.1
  rw [← hi_def] at hb
  set u := 4 * x.1 - (i : ℝ)
  have hu0 : 0 ≤ u := by simp only [u]; linarith [hb.1]
  have hu1 : u ≤ 1 := by simp only [u]; push_cast at hb; linarith [hb.2]
  have hterm : |(1 - u) * a1Real si sj i j + u * a1Real si sj (i + 1) j| ≤
      |a1Real si sj i j| + |a1Real si sj (i + 1) j| := by
    calc |(1 - u) * a1Real si sj i j + u * a1Real si sj (i + 1) j|
        ≤ |(1 - u) * a1Real si sj i j| + |u * a1Real si sj (i + 1) j| := abs_add_le _ _
      _ = (1 - u) * |a1Real si sj i j| + u * |a1Real si sj (i + 1) j| := by
          rw [abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr hu1), abs_of_nonneg hu0]
      _ ≤ 1 * |a1Real si sj i j| + 1 * |a1Real si sj (i + 1) j| :=
          add_le_add (mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _))
            (mul_le_mul_of_nonneg_right hu1 (abs_nonneg _))
      _ = _ := by ring
  have hi_mem : i ∈ Finset.range 4 := Finset.mem_range.mpr (cell4_lt x.1)
  have hj_mem : j ∈ Finset.range 4 := Finset.mem_range.mpr (cell4_lt x.2)
  let fj : ℕ → ℝ := fun j' => |a1Real si sj i j'| + |a1Real si sj (i + 1) j'|
  let fi : ℕ → ℝ := fun i' => ∑ j' ∈ Finset.range 4, (|a1Real si sj i' j'| + |a1Real si sj (i' + 1) j'|)
  have hle_j : fj j ≤ ∑ j' ∈ Finset.range 4, fj j' :=
    Finset.single_le_sum (f := fj) (fun j' _ => by dsimp only [fj]; positivity) hj_mem
  have hle_i : fi i ≤ C :=
    Finset.single_le_sum (f := fi) (fun i' _ => Finset.sum_nonneg (fun _ _ => by positivity)) hi_mem
  dsimp only [fj, fi] at hle_j hle_i
  linarith

lemma exists_bound_alpha2 (si sj : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ unitSquare, |alpha2 si sj x| ≤ C := by
  let C : ℝ := ∑ i ∈ Finset.range 4, ∑ j ∈ Finset.range 4,
    (|a2Real si sj i j| + |a2Real si sj i (j + 1)|)
  refine ⟨C, by positivity, fun x hx => ?_⟩
  unfold alpha2
  set i := cell4 x.1 with hi_def
  set j := cell4 x.2 with hj_def
  have hb := cell4_bounds hx.2
  rw [← hj_def] at hb
  set v := 4 * x.2 - (j : ℝ)
  have hv0 : 0 ≤ v := by simp only [v]; linarith [hb.1]
  have hv1 : v ≤ 1 := by simp only [v]; push_cast at hb; linarith [hb.2]
  have hterm : |(1 - v) * a2Real si sj i j + v * a2Real si sj i (j + 1)| ≤
      |a2Real si sj i j| + |a2Real si sj i (j + 1)| := by
    calc |(1 - v) * a2Real si sj i j + v * a2Real si sj i (j + 1)|
        ≤ |(1 - v) * a2Real si sj i j| + |v * a2Real si sj i (j + 1)| := abs_add_le _ _
      _ = (1 - v) * |a2Real si sj i j| + v * |a2Real si sj i (j + 1)| := by
          rw [abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr hv1), abs_of_nonneg hv0]
      _ ≤ 1 * |a2Real si sj i j| + 1 * |a2Real si sj i (j + 1)| :=
          add_le_add (mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _))
            (mul_le_mul_of_nonneg_right hv1 (abs_nonneg _))
      _ = _ := by ring
  have hi_mem : i ∈ Finset.range 4 := Finset.mem_range.mpr (cell4_lt x.1)
  have hj_mem : j ∈ Finset.range 4 := Finset.mem_range.mpr (cell4_lt x.2)
  let fj : ℕ → ℝ := fun j' => |a2Real si sj i j'| + |a2Real si sj i (j' + 1)|
  let fi : ℕ → ℝ := fun i' => ∑ j' ∈ Finset.range 4, (|a2Real si sj i' j'| + |a2Real si sj i' (j' + 1)|)
  have hle_j : fj j ≤ ∑ j' ∈ Finset.range 4, fj j' :=
    Finset.single_le_sum (f := fj) (fun j' _ => by dsimp only [fj]; positivity) hj_mem
  have hle_i : fi i ≤ C :=
    Finset.single_le_sum (f := fi) (fun i' _ => Finset.sum_nonneg (fun _ _ => by positivity)) hi_mem
  dsimp only [fj, fi] at hle_j hle_i
  linarith

lemma integrableOn_bdd_mul_unitSquare {f g : Type2 → ℝ} {C : ℝ}
    (hf_meas : Measurable f) (hf_bdd : ∀ x ∈ unitSquare, |f x| ≤ C)
    (hg_int : IntegrableOn g unitSquare volume) (hg_bdd : ∀ x ∈ unitSquare, 0 ≤ g x ∧ g x ≤ 1) :
    IntegrableOn (fun x => f x * g x) unitSquare volume := by
  have hdom : IntegrableOn (fun _ : Type2 => max C 0) unitSquare volume :=
    integrableOn_const_of_subset_unitSquare Subset.rfl (max C 0)
  have haesm : AEStronglyMeasurable (fun x => f x * g x) (volume.restrict unitSquare) :=
    (hf_meas.aestronglyMeasurable).mul hg_int.aestronglyMeasurable
  refine Integrable.mono' hdom haesm ?_
  rw [ae_restrict_iff' measurableSet_unitSquare]
  refine Filter.Eventually.of_forall (fun x hx => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hg_bdd x hx).1]
  have h1 := hf_bdd x hx
  have h2 := (hg_bdd x hx).2
  have hC0 : C ≤ max C 0 := le_max_left C 0
  nlinarith [abs_nonneg (f x), (hg_bdd x hx).1]

lemma integrableOn_bdd_profileDomain {F : Type2 × Type2 → ℝ} {C : ℝ}
    (hF_aesm : AEStronglyMeasurable F (volume.restrict profileDomain))
    (hF_bdd : ∀ p ∈ profileDomain, |F p| ≤ C) :
    IntegrableOn F profileDomain volume := by
  have hdom : IntegrableOn (fun _ : Type2 × Type2 => max C 0) profileDomain volume :=
    integrableOn_const_of_subset_profileDomain Subset.rfl (max C 0)
  refine Integrable.mono' hdom hF_aesm ?_
  rw [ae_restrict_iff' measurableSet_profileDomain]
  refine Filter.Eventually.of_forall (fun p hp => ?_)
  rw [Real.norm_eq_abs]
  exact le_trans (hF_bdd p hp) (le_max_left C 0)

/-! ### Section 3: 1D DSIC Envelope & Piecewise-Affine Integration-by-Parts -/

lemma sum_range_sub (g : ℕ → ℝ) :
    ∀ m : ℕ, (∑ k ∈ Finset.range m, (g (k + 1) - g k)) = g m - g 0
  | 0 => by simp
  | m + 1 => by rw [Finset.sum_range_succ, sum_range_sub g m]; ring

lemma dsic_1d_mono {q u : ℝ → ℝ}
    (hic : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, (t - s) * q s ≤ u t - u s) :
    MonotoneOn q (Icc (0 : ℝ) 1) := by
  intro s hs t ht hst
  rcases eq_or_lt_of_le hst with rfl | hlt
  · exact le_rfl
  · have h1 := hic s hs t ht
    have h2 := hic t ht s hs
    have h3 : (t - s) * (q s - q t) ≤ 0 := by nlinarith
    nlinarith

lemma dsic_1d_continuousOn {q u : ℝ → ℝ}
    (hq01 : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ q s ∧ q s ≤ 1)
    (hic : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, (t - s) * q s ≤ u t - u s) :
    ContinuousOn u (Icc (0 : ℝ) 1) := by
  rw [Metric.continuousOn_iff]
  intro x hx ε hε
  refine ⟨ε, hε, fun y hy hdist => ?_⟩
  rw [Real.dist_eq] at hdist ⊢
  have h1 := hic x hx y hy
  have h2 := hic y hy x hx
  rcases le_total x y with hxy | hyx
  · have hqx := hq01 x hx
    have hqy := hq01 y hy
    have hlo : -(y - x) ≤ u y - u x := by nlinarith
    have hhi : u y - u x ≤ y - x := by nlinarith
    rw [abs_of_nonneg (sub_nonneg.mpr hxy)] at hdist
    rw [abs_lt]; constructor <;> linarith
  · have hqx := hq01 x hx
    have hqy := hq01 y hy
    have hlo : -(x - y) ≤ u y - u x := by nlinarith
    have hhi : u y - u x ≤ x - y := by nlinarith
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hyx)] at hdist
    rw [abs_lt]; constructor <;> linarith

lemma dsic_1d_q_integral_le {q u : ℝ → ℝ}
    (hq_int : IntegrableOn q (Icc (0 : ℝ) 1) volume)
    (hq01 : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ q s ∧ q s ≤ 1)
    (hic : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, (t - s) * q s ≤ u t - u s)
    {a b : ℝ} (ha0 : 0 ≤ a) (hab : a ≤ b) (hb1 : b ≤ 1) :
    ∫ s in Icc a b, q s ≤ u b - u a := by
  have hmono := dsic_1d_mono hic
  have hstep : ∀ m : ℕ, ∫ s in Icc a b, q s ≤ (u b - u a) + (b - a) / ((m : ℝ) + 1) := by
    intro m
    let n : ℕ := m + 1
    have hn_pos : (0 : ℝ) < (n : ℝ) := by simp only [n]; positivity
    let h : ℝ := (b - a) / (n : ℝ)
    have hh_nn : 0 ≤ h := div_nonneg (sub_nonneg.mpr hab) (le_of_lt hn_pos)
    let p : ℕ → ℝ := fun k => a + (k : ℝ) * h
    have hp0 : p 0 = a := by simp [p]
    have hpn : p n = b := by
      simp only [p, h]
      rw [mul_div_cancel₀ _ (ne_of_gt hn_pos)]
      ring
    have hp_mono : ∀ k < n, p k ≤ p (k + 1) := by
      intro k _; simp only [p]; push_cast; linarith
    have hp_mem : ∀ k ≤ n, p k ∈ Icc (0 : ℝ) 1 := by
      intro k hk
      have hk_nn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      have hk_le : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hk
      have hkh1 : 0 ≤ (k : ℝ) * h := mul_nonneg hk_nn hh_nn
      have hkh2 : (k : ℝ) * h ≤ b - a := by
        calc (k : ℝ) * h ≤ (n : ℝ) * h := mul_le_mul_of_nonneg_right hk_le hh_nn
          _ = b - a := mul_div_cancel₀ _ (ne_of_gt hn_pos)
      exact ⟨by simp only [p]; linarith, by simp only [p]; linarith⟩
    have hq_ab : IntegrableOn q (Icc a b) volume := hq_int.mono_set (Icc_subset_Icc ha0 hb1)
    have hpart := setIntegral_Icc_partition n p q hp_mono (by simpa [hp0, hpn] using hq_ab)
    simp only [hp0, hpn] at hpart
    rw [hpart]
    have hsum_le : (∑ k ∈ Finset.range n, ∫ s in Icc (p k) (p (k + 1)), q s) ≤
        ∑ k ∈ Finset.range n, h * q (p (k + 1)) := by
      apply Finset.sum_le_sum
      intro k hk
      have hkn : k < n := Finset.mem_range.mp hk
      have hpk_le : p k ≤ p (k + 1) := hp_mono k hkn
      have hsub : Icc (p k) (p (k + 1)) ⊆ Icc (0 : ℝ) 1 :=
        Icc_subset_Icc (hp_mem k (by omega)).1 (hp_mem (k + 1) (by omega)).2
      have hmono_k : ∀ s ∈ Icc (p k) (p (k + 1)), q s ≤ q (p (k + 1)) :=
        fun s hs => hmono (hsub hs) (hp_mem (k + 1) (by omega)) hs.2
      calc ∫ s in Icc (p k) (p (k + 1)), q s
          ≤ ∫ _ in Icc (p k) (p (k + 1)), q (p (k + 1)) :=
            setIntegral_mono_on (hq_int.mono_set hsub)
              (ContinuousOn.integrableOn_Icc continuousOn_const) measurableSet_Icc hmono_k
        _ = (p (k + 1) - p k) * q (p (k + 1)) := setIntegral_Icc_const hpk_le _
        _ = h * q (p (k + 1)) := by simp only [p]; push_cast; ring
    have hrhs_le : (∑ k ∈ Finset.range n, h * q (p (k + 1))) ≤ (u b - u a) + h := by
      simp only [n, Finset.sum_range_succ]
      have hmid : (∑ k ∈ Finset.range m, h * q (p (k + 1))) ≤
          ∑ k ∈ Finset.range m, (u (p (k + 2)) - u (p (k + 1))) := by
        apply Finset.sum_le_sum
        intro k hk
        have hkm : k < m := Finset.mem_range.mp hk
        have hd : h = p (k + 2) - p (k + 1) := by simp only [p]; push_cast; ring
        rw [hd]
        exact hic (p (k + 1)) (hp_mem (k + 1) (by omega)) (p (k + 2)) (hp_mem (k + 2) (by omega))
      rw [sum_range_sub (fun k => u (p (k + 1))) m] at hmid
      have hp_end : p (m + 1) = b := hpn
      rw [hp_end] at hmid
      have hfirst : 0 ≤ u (p 1) - u a := by
        have h01 := hic a ⟨ha0, le_trans hab hb1⟩ (p 1) (hp_mem 1 (by omega))
        have hd : p 1 - a = h := by simp only [p]; push_cast; ring
        rw [hd] at h01
        have hqa := (hq01 a ⟨ha0, le_trans hab hb1⟩).1
        nlinarith
      have hlast : h * q (p (m + 1)) ≤ h := by
        rw [hp_end]
        have hqb := (hq01 b ⟨le_trans ha0 hab, hb1⟩).2
        nlinarith
      linarith
    have hh_eq : h = (b - a) / ((m : ℝ) + 1) := by simp only [h, n]; push_cast; rfl
    linarith
  by_contra hlt
  push Not at hlt
  set ε := (∫ s in Icc a b, q s) - (u b - u a)
  have hε : 0 < ε := sub_pos.mpr hlt
  obtain ⟨m, hm⟩ := exists_nat_gt ((b - a) / ε)
  have hm1 : (b - a) / ε < (m : ℝ) + 1 := by linarith
  have hm_pos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hmul : b - a < ((m : ℝ) + 1) * ε := (div_lt_iff₀ hε).mp hm1
  have hdiv : (b - a) / ((m : ℝ) + 1) < ε := (div_lt_iff₀ hm_pos).mpr (by linarith)
  have hst := hstep m
  linarith

lemma dsic_1d_affine_ibp {q u : ℝ → ℝ}
    (hq_int : IntegrableOn q (Icc (0 : ℝ) 1) volume)
    (hq01 : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ q s ∧ q s ≤ 1)
    (hic : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, (t - s) * q s ≤ u t - u s)
    {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a + 1 / 4 ≤ 1)
    {aL aR : ℝ} (haL : 0 ≤ aL) (haR : 0 ≤ aR) :
    ∫ s in Icc a (a + 1 / 4),
      ((1 - 4 * (s - a)) * aL + (4 * (s - a)) * aR) * q s ≤
      aR * u (a + 1 / 4) - aL * u a + 4 * (aL - aR) * ∫ t in Icc a (a + 1 / 4), u t := by
  set b := a + 1 / 4
  have hab : a ≤ b := by simp only [b]; linarith
  have hsub : Icc a b ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc ha0 ha1
  have hq_ab : IntegrableOn q (Icc a b) volume := hq_int.mono_set hsub
  have hu_cont : ContinuousOn u (Icc (0 : ℝ) 1) := dsic_1d_continuousOn hq01 hic
  have hu_ab : IntegrableOn u (Icc a b) volume := (ContinuousOn.integrableOn_Icc hu_cont).mono_set hsub
  have hvol_ab : volume (Icc a b) ≠ ⊤ := by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  -- Term 1: ∫ s in Icc a b, (b - s) * q s ≤ ∫ t in Icc a b, (u t - u a)
  let F : ℝ × ℝ → ℝ := { p : ℝ × ℝ | p.1 ≤ p.2 }.indicator (fun p => q p.1)
  have hF_int : IntegrableOn F (Icc a b ×ˢ Icc a b) volume :=
    (integrableOn_fst_of_prod hq_ab hvol_ab).indicator (measurableSet_le measurable_fst measurable_snd)
  have hF1 : ∫ p in Icc a b ×ˢ Icc a b, F p = ∫ s in Icc a b, (b - s) * q s := by
    rw [setIntegral_prod_eq hF_int]
    apply setIntegral_congr_fun measurableSet_Icc
    intro s hs; dsimp only
    have hslice_F : IntegrableOn (fun t => F (s, t)) (Icc a b) volume :=
      (integrableOn_const hvol_ab (C := q s)).indicator measurableSet_Ici
    rw [setIntegral_Icc_split hs.1 hs.2 hslice_F]
    have hL0 : ∫ t in Icc a s, F (s, t) = 0 := by
      rw [integral_Icc_eq_integral_Ioc, integral_Ioc_eq_integral_Ioo]
      have hc0 : EqOn (fun t => F (s, t)) (fun _ => 0) (Ioo a s) := by
        intro t ht; simp only [F]
        exact Set.indicator_of_notMem (by simp; exact ht.2) _
      rw [setIntegral_congr_fun measurableSet_Ioo hc0]; simp
    have hR1 : ∫ t in Icc s b, F (s, t) = (b - s) * q s := by
      rw [integral_Icc_eq_integral_Ioc, integral_Ioc_eq_integral_Ioo]
      have hc1 : EqOn (fun t => F (s, t)) (fun _ => q s) (Ioo s b) := by
        intro t ht; simp only [F]
        exact Set.indicator_of_mem (by simp; exact le_of_lt ht.1) _
      rw [setIntegral_congr_fun measurableSet_Ioo hc1, ← integral_Ioc_eq_integral_Ioo,
        ← integral_Icc_eq_integral_Ioc, setIntegral_Icc_const hs.2]
    rw [hL0, hR1, zero_add]
  have hF2 : ∫ p in Icc a b ×ˢ Icc a b, F p ≤ (∫ t in Icc a b, u t) - (b - a) * u a := by
    rw [setIntegral_prod_symm_eq hF_int]
    have hF_swap_int : IntegrableOn (fun t => ∫ s in Icc a b, F (s, t)) (Icc a b) volume := by
      let Fswap : ℝ × ℝ → ℝ := { p : ℝ × ℝ | p.2 ≤ p.1 }.indicator (fun p => q p.2)
      have hFs : IntegrableOn Fswap (Icc a b ×ˢ Icc a b) volume :=
        (integrableOn_snd_of_prod hvol_ab hq_ab).indicator (measurableSet_le measurable_snd measurable_fst)
      unfold IntegrableOn at hFs ⊢
      rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at hFs
      exact hFs.integral_prod_left
    have hpt : ∀ t ∈ Icc a b, (∫ s in Icc a b, F (s, t)) ≤ u t - u a := by
      intro t ht
      have hsl : IntegrableOn (fun s => F (s, t)) (Icc a b) volume :=
        hq_ab.indicator measurableSet_Iic
      rw [setIntegral_Icc_split ht.1 ht.2 hsl]
      have hL1 : ∫ s in Icc a t, F (s, t) = ∫ s in Icc a t, q s := by
        rw [integral_Icc_eq_integral_Ioc, integral_Ioc_eq_integral_Ioo,
          integral_Icc_eq_integral_Ioc (f := q), integral_Ioc_eq_integral_Ioo (f := q)]
        apply setIntegral_congr_fun measurableSet_Ioo
        intro s hs; simp only [F]
        exact Set.indicator_of_mem (by simp; exact le_of_lt hs.2) _
      have hR0 : ∫ s in Icc t b, F (s, t) = 0 := by
        rw [integral_Icc_eq_integral_Ioc, integral_Ioc_eq_integral_Ioo]
        have hc0 : EqOn (fun s => F (s, t)) (fun _ => 0) (Ioo t b) := by
          intro s hs; simp only [F]
          exact Set.indicator_of_notMem (by simp; exact hs.1) _
        rw [setIntegral_congr_fun measurableSet_Ioo hc0]; simp
      rw [hL1, hR0, add_zero]
      exact dsic_1d_q_integral_le hq_int hq01 hic ha0 ht.1 (le_trans ht.2 ha1)
    have hdiff_int1 : IntegrableOn (fun t => u t - u a) (Icc a b) volume :=
      Integrable.sub hu_ab (integrableOn_const hvol_ab)
    have hmono := setIntegral_mono_on hF_swap_int hdiff_int1 measurableSet_Icc hpt
    rw [integral_sub hu_ab (integrableOn_const hvol_ab), setIntegral_Icc_const hab] at hmono
    exact hmono
  -- Term 2: ∫ s in Icc a b, (s - a) * q s ≤ (b - a) * u b - ∫ t in Icc a b, u t
  let G : ℝ × ℝ → ℝ := { p : ℝ × ℝ | p.2 ≤ p.1 }.indicator (fun p => q p.1)
  have hG_int : IntegrableOn G (Icc a b ×ˢ Icc a b) volume :=
    (integrableOn_fst_of_prod hq_ab hvol_ab).indicator (measurableSet_le measurable_snd measurable_fst)
  have hG1 : ∫ p in Icc a b ×ˢ Icc a b, G p = ∫ s in Icc a b, (s - a) * q s := by
    rw [setIntegral_prod_eq hG_int]
    apply setIntegral_congr_fun measurableSet_Icc
    intro s hs; dsimp only
    have hslice_G : IntegrableOn (fun t => G (s, t)) (Icc a b) volume :=
      (integrableOn_const hvol_ab (C := q s)).indicator measurableSet_Iic
    rw [setIntegral_Icc_split hs.1 hs.2 hslice_G]
    have hL1 : ∫ t in Icc a s, G (s, t) = (s - a) * q s := by
      rw [integral_Icc_eq_integral_Ioc, integral_Ioc_eq_integral_Ioo]
      have hc1 : EqOn (fun t => G (s, t)) (fun _ => q s) (Ioo a s) := by
        intro t ht; simp only [G]
        exact Set.indicator_of_mem (by simp; exact le_of_lt ht.2) _
      rw [setIntegral_congr_fun measurableSet_Ioo hc1, ← integral_Ioc_eq_integral_Ioo,
        ← integral_Icc_eq_integral_Ioc, setIntegral_Icc_const hs.1]
    have hR0 : ∫ t in Icc s b, G (s, t) = 0 := by
      rw [integral_Icc_eq_integral_Ioc, integral_Ioc_eq_integral_Ioo]
      have hc0 : EqOn (fun t => G (s, t)) (fun _ => 0) (Ioo s b) := by
        intro t ht; simp only [G]
        exact Set.indicator_of_notMem (by simp; exact ht.1) _
      rw [setIntegral_congr_fun measurableSet_Ioo hc0]; simp
    rw [hL1, hR0, add_zero]
  have hG2 : ∫ p in Icc a b ×ˢ Icc a b, G p ≤ (b - a) * u b - (∫ t in Icc a b, u t) := by
    rw [setIntegral_prod_symm_eq hG_int]
    have hG_swap_int : IntegrableOn (fun t => ∫ s in Icc a b, G (s, t)) (Icc a b) volume := by
      let Gswap : ℝ × ℝ → ℝ := { p : ℝ × ℝ | p.1 ≤ p.2 }.indicator (fun p => q p.2)
      have hGs : IntegrableOn Gswap (Icc a b ×ˢ Icc a b) volume :=
        (integrableOn_snd_of_prod hvol_ab hq_ab).indicator (measurableSet_le measurable_fst measurable_snd)
      unfold IntegrableOn at hGs ⊢
      rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at hGs
      exact hGs.integral_prod_left
    have hpt : ∀ t ∈ Icc a b, (∫ s in Icc a b, G (s, t)) ≤ u b - u t := by
      intro t ht
      have hsl : IntegrableOn (fun s => G (s, t)) (Icc a b) volume :=
        hq_ab.indicator measurableSet_Ici
      rw [setIntegral_Icc_split ht.1 ht.2 hsl]
      have hL0 : ∫ s in Icc a t, G (s, t) = 0 := by
        rw [integral_Icc_eq_integral_Ioc, integral_Ioc_eq_integral_Ioo]
        have hc0 : EqOn (fun s => G (s, t)) (fun _ => 0) (Ioo a t) := by
          intro s hs; simp only [G]
          exact Set.indicator_of_notMem (by simp; exact hs.2) _
        rw [setIntegral_congr_fun measurableSet_Ioo hc0]; simp
      have hR1 : ∫ s in Icc t b, G (s, t) = ∫ s in Icc t b, q s := by
        rw [integral_Icc_eq_integral_Ioc, integral_Ioc_eq_integral_Ioo,
          integral_Icc_eq_integral_Ioc (f := q), integral_Ioc_eq_integral_Ioo (f := q)]
        apply setIntegral_congr_fun measurableSet_Ioo
        intro s hs; simp only [G]
        exact Set.indicator_of_mem (by simp; exact le_of_lt hs.1) _
      rw [hL0, hR1, zero_add]
      exact dsic_1d_q_integral_le hq_int hq01 hic (le_trans ha0 ht.1) ht.2 ha1
    have hdiff_int2 : IntegrableOn (fun t => u b - u t) (Icc a b) volume :=
      Integrable.sub (integrableOn_const hvol_ab) hu_ab
    have hmono := setIntegral_mono_on hG_swap_int hdiff_int2 measurableSet_Icc hpt
    rw [integral_sub (integrableOn_const hvol_ab) hu_ab, setIntegral_Icc_const hab] at hmono
    exact hmono
  -- Combine 4 * aL * Term1 + 4 * aR * Term2!
  have h1_int : IntegrableOn (fun s => (b - s) * q s) (Icc a b) volume := by
    have hF_left : IntegrableOn (fun s => ∫ t in Icc a b, F (s, t)) (Icc a b) volume := by
      unfold IntegrableOn at hF_int ⊢
      rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at hF_int
      exact hF_int.integral_prod_left
    refine hF_left.congr_fun (fun s hs => ?_) measurableSet_Icc
    -- We already proved ∫ t in Icc a b, F (s, t) = (b - s) * q s!
    have hslice_F : IntegrableOn (fun t => F (s, t)) (Icc a b) volume :=
      (integrableOn_const hvol_ab (C := q s)).indicator measurableSet_Ici
    dsimp only
    rw [setIntegral_Icc_split hs.1 hs.2 hslice_F]
    have hL0 : ∫ t in Icc a s, F (s, t) = 0 := by
      rw [integral_Icc_eq_integral_Ioc, integral_Ioc_eq_integral_Ioo]
      rw [setIntegral_congr_fun measurableSet_Ioo (fun t ht => Set.indicator_of_notMem (by simp; exact ht.2) _)]
      simp
    have hR1 : ∫ t in Icc s b, F (s, t) = (b - s) * q s := by
      rw [integral_Icc_eq_integral_Ioc, integral_Ioc_eq_integral_Ioo]
      have hc1 : EqOn (fun t => F (s, t)) (fun _ => q s) (Ioo s b) :=
        fun t ht => Set.indicator_of_mem (by simp; exact le_of_lt ht.1) _
      rw [setIntegral_congr_fun measurableSet_Ioo hc1,
        ← integral_Ioc_eq_integral_Ioo, ← integral_Icc_eq_integral_Ioc, setIntegral_Icc_const hs.2]
    rw [hL0, hR1, zero_add]
  have h2_int : IntegrableOn (fun s => (s - a) * q s) (Icc a b) volume := by
    have hsub_eq : (fun s => (s - a) * q s) = (fun s => (b - a) * q s - (b - s) * q s) := by
      ext s; ring
    rw [hsub_eq]
    exact (hq_ab.const_mul (b - a)).sub h1_int
  have hlin_eq : (fun s => ((1 - 4 * (s - a)) * aL + 4 * (s - a) * aR) * q s) =
      (fun s => (4 * aL) * ((b - s) * q s) + (4 * aR) * ((s - a) * q s)) := by
    ext s; simp only [b]; ring
  rw [hlin_eq, integral_add (h1_int.const_mul _) (h2_int.const_mul _),
    integral_const_mul, integral_const_mul]
  rw [hF1] at hF2
  rw [hG1] at hG2
  have hb_sub : b - a = 1 / 4 := by simp only [b]; ring
  rw [hb_sub] at hF2 hG2
  have hm1 := mul_le_mul_of_nonneg_left hF2 (show 0 ≤ 4 * aL by positivity)
  have hm2 := mul_le_mul_of_nonneg_left hG2 (show 0 ≤ 4 * aR by positivity)
  linarith

lemma dsic_1d_grid4_ibp {q u : ℝ → ℝ} (A : ℕ → ℝ)
    (hA_nn : ∀ i < 4, 0 ≤ A i) (hA4 : A 4 = 0)
    (hq_int : IntegrableOn q (Icc (0 : ℝ) 1) volume)
    (hq01 : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ q s ∧ q s ≤ 1)
    (hu0 : 0 ≤ u 0)
    (hic : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, (t - s) * q s ≤ u t - u s) :
    let α1d := fun s : ℝ =>
      let i := cell4 s
      let w := 4 * s - (i : ℝ)
      (1 - w) * A i + w * A (i + 1)
    IntegrableOn (fun s => α1d s * q s) (Icc (0 : ℝ) 1) volume →
    ∫ s in Icc (0 : ℝ) 1, α1d s * q s ≤
      ∑ i ∈ Finset.range 4, 4 * (A i - A (i + 1)) *
        ∫ t in Icc ((i : ℝ) / 4) (((i + 1 : ℕ) : ℝ) / 4), u t := by
  intro α1d hαq_int
  let p4 : ℕ → ℝ := fun i => (i : ℝ) / 4
  have hp4_0 : p4 0 = 0 := by simp [p4]
  have hp4_4 : p4 4 = 1 := by norm_num [p4]
  have hp4_mono : ∀ i < 4, p4 i ≤ p4 (i + 1) := by intro i _; simp only [p4]; push_cast; linarith
  have hpart := setIntegral_Icc_partition 4 p4 (fun s => α1d s * q s) hp4_mono
    (by simpa [hp4_0, hp4_4] using hαq_int)
  simp only [hp4_0, hp4_4] at hpart
  rw [hpart]
  have hcell : ∀ i < 4,
      ∫ s in Icc (p4 i) (p4 (i + 1)), α1d s * q s ≤
        A (i + 1) * u (p4 (i + 1)) - A i * u (p4 i) +
          4 * (A i - A (i + 1)) * ∫ t in Icc (p4 i) (p4 (i + 1)), u t := by
    intro i hi
    have hp_step : p4 (i + 1) = p4 i + 1 / 4 := by simp only [p4]; push_cast; ring
    rw [integral_Icc_eq_integral_Ioc, integral_Ioc_eq_integral_Ioo]
    have hcongr : EqOn (fun s => α1d s * q s)
        (fun s => ((1 - 4 * (s - p4 i)) * A i + (4 * (s - p4 i)) * A (i + 1)) * q s)
        (Ioo (p4 i) (p4 (i + 1))) := by
      intro s hs
      have hci : cell4 s = i := cell4_eq_of_Ioo hi hs.1 hs.2
      dsimp only [α1d]
      rw [hci]
      simp only [p4]; ring
    rw [setIntegral_congr_fun measurableSet_Ioo hcongr,
      ← integral_Ioc_eq_integral_Ioo, ← integral_Icc_eq_integral_Ioc, hp_step]
    have ha0 : 0 ≤ p4 i := by simp [p4]; positivity
    have ha1 : p4 i + 1 / 4 ≤ 1 := by
      rw [← hp_step]
      have hle : (i + 1 : ℕ) ≤ 4 := by omega
      have hle' : ((i + 1 : ℕ) : ℝ) ≤ 4 := by exact_mod_cast hle
      simp only [p4]; linarith
    have hA_R : 0 ≤ A (i + 1) := by
      by_cases hi3 : i + 1 < 4
      · exact hA_nn (i + 1) hi3
      · have heq : i + 1 = 4 := by omega
        rw [heq, hA4]
    exact dsic_1d_affine_ibp hq_int hq01 hic ha0 ha1 (hA_nn i hi) hA_R
  have hc0 := hcell 0 (by omega)
  have hc1 := hcell 1 (by omega)
  have hc2 := hcell 2 (by omega)
  have hc3 := hcell 3 (by omega)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  simp only [p4] at hc0 hc1 hc2 hc3
  norm_num at hc0 hc1 hc2 hc3 ⊢
  rw [hA4] at hc3 ⊢
  have hA0 := hA_nn 0 (by omega)
  have hu0' : 0 ≤ A 0 * u 0 := mul_nonneg hA0 hu0
  linarith

/-! ### Section 4: 2D Slice Bound on `unitSquare` -/

lemma u1_slice_bound {M : Mechanism}
    (hFeas : IsFeasible M) (hDSIC : IsDSIC M) (hIR : IsExPostIR M)
    {y : Type2} (hy : y ∈ unitSquare)
    (hq11_int : IntegrableOn (fun x => M.q11 x y) unitSquare volume)
    (hq12_int : IntegrableOn (fun x => M.q12 x y) unitSquare volume)
    (ht1_int : IntegrableOn (fun x => M.t1 x y) unitSquare volume) :
    ∫ x in unitSquare, M.t1 x y ≤
      ∫ x in unitSquare,
        ((x.1 - alpha1 (cell4 y.1) (cell4 y.2) x) * M.q11 x y +
         (x.2 - alpha2 (cell4 y.1) (cell4 y.2) x) * M.q12 x y) := by
  set si := cell4 y.1
  set sj := cell4 y.2
  have hsi : si < 4 := cell4_lt y.1
  have hsj : sj < 4 := cell4_lt y.2
  have hq11_bdd : ∀ x ∈ unitSquare, 0 ≤ M.q11 x y ∧ M.q11 x y ≤ 1 := by
    intro x hx; have hf := hFeas.1 x hx y hy; exact ⟨hf.1, by linarith [hf.2.1, hf.2.2.1]⟩
  have hq12_bdd : ∀ x ∈ unitSquare, 0 ≤ M.q12 x y ∧ M.q12 x y ≤ 1 := by
    intro x hx; have hf := hFeas.1 x hx y hy; exact ⟨hf.2.2.2.1, by linarith [hf.2.2.2.2.1, hf.2.2.2.2.2]⟩
  have hxq11_int : IntegrableOn (fun x : Type2 => x.1 * M.q11 x y) unitSquare volume :=
    integrableOn_bdd_mul_unitSquare measurable_fst (C := 1)
      (fun x hx => by rw [abs_of_nonneg hx.1.1]; exact hx.1.2) hq11_int hq11_bdd
  have hxq12_int : IntegrableOn (fun x : Type2 => x.2 * M.q12 x y) unitSquare volume :=
    integrableOn_bdd_mul_unitSquare measurable_snd (C := 1)
      (fun x hx => by rw [abs_of_nonneg hx.2.1]; exact hx.2.2) hq12_int hq12_bdd
  obtain ⟨C1, _, hC1⟩ := exists_bound_alpha1 si sj
  obtain ⟨C2, _, hC2⟩ := exists_bound_alpha2 si sj
  have ha1q_int : IntegrableOn (fun x : Type2 => alpha1 si sj x * M.q11 x y) unitSquare volume :=
    integrableOn_bdd_mul_unitSquare (measurable_alpha1 si sj) hC1 hq11_int hq11_bdd
  have ha2q_int : IntegrableOn (fun x : Type2 => alpha2 si sj x * M.q12 x y) unitSquare volume :=
    integrableOn_bdd_mul_unitSquare (measurable_alpha2 si sj) hC2 hq12_int hq12_bdd
  let u : Type2 → ℝ := fun x => u1Report M x x y
  have hu_int : IntegrableOn u unitSquare volume :=
    (hxq11_int.add hxq12_int).sub ht1_int
  have hu_nn : ∀ x ∈ unitSquare, 0 ≤ u x := fun x hx => (hIR x hx y hy).1
  let p4 : ℕ → ℝ := fun i => (i : ℝ) / 4
  have hp4_0 : p4 0 = 0 := by simp [p4]
  have hp4_4 : p4 4 = 1 := by norm_num [p4]
  have hp4_mono : ∀ i < 4, p4 i ≤ p4 (i + 1) := by intro i _; simp only [p4]; push_cast; linarith
  -- Bound 1: ∫ x in unitSquare, alpha1 si sj x * M.q11 x y
  have hbnd1 : ∫ x in unitSquare, alpha1 si sj x * M.q11 x y ≤
      ∑ i ∈ Finset.range 4, ∑ j ∈ Finset.range 4,
        4 * (a1Real si sj i j - a1Real si sj (i + 1) j) *
          ∫ x in Icc (p4 i) (p4 (i + 1)) ×ˢ Icc (p4 j) (p4 (j + 1)), u x := by
    unfold unitSquare at ha1q_int hq11_int hu_int ⊢
    rw [setIntegral_prod_symm_eq ha1q_int]
    have hae_q : ∀ᵐ x2 ∂(volume.restrict (Icc (0 : ℝ) 1)),
        IntegrableOn (fun s => M.q11 (s, x2) y) (Icc (0 : ℝ) 1) volume :=
      ae_integrableOn_prod_left hq11_int
    have hae_a1q : ∀ᵐ x2 ∂(volume.restrict (Icc (0 : ℝ) 1)),
        IntegrableOn (fun s => alpha1 si sj (s, x2) * M.q11 (s, x2) y) (Icc (0 : ℝ) 1) volume :=
      ae_integrableOn_prod_left ha1q_int
    have houter_lhs : IntegrableOn (fun x2 => ∫ s in Icc (0 : ℝ) 1, alpha1 si sj (s, x2) * M.q11 (s, x2) y)
        (Icc (0 : ℝ) 1) volume := by
      let Gswap : ℝ × ℝ → ℝ := fun z => alpha1 si sj (z.2, z.1) * M.q11 (z.2, z.1) y
      -- Simpler: use integral_prod_symm integrability directly via Measure.prod_swap or Fswap!
      have hmeas_swap : MeasurePreserving Prod.swap
          ((volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict (Icc (0 : ℝ) 1)))
          ((volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict (Icc (0 : ℝ) 1))) :=
        Measure.measurePreserving_swap
      unfold IntegrableOn at ha1q_int ⊢
      rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at ha1q_int
      have hG : Integrable (fun z : ℝ × ℝ => alpha1 si sj (z.2, z.1) * M.q11 (z.2, z.1) y)
          ((volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict (Icc (0 : ℝ) 1))) :=
        hmeas_swap.integrable_comp_of_integrable ha1q_int
      exact hG.integral_prod_left
    have hpart_j := setIntegral_Icc_partition 4 p4
      (fun x2 => ∫ s in Icc (0 : ℝ) 1, alpha1 si sj (s, x2) * M.q11 (s, x2) y)
      hp4_mono (by simpa [hp4_0, hp4_4] using houter_lhs)
    simp only [hp4_0, hp4_4] at hpart_j
    rw [hpart_j, Finset.sum_comm]
    apply Finset.sum_le_sum
    intro j hj
    have hj4 : j < 4 := Finset.mem_range.mp hj
    have hsub_j : Icc (p4 j) (p4 (j + 1)) ⊆ Icc (0 : ℝ) 1 := by
      refine Icc_subset_Icc (by simp [p4]; positivity) ?_
      have hle : ((j + 1 : ℕ) : ℝ) ≤ 4 := by exact_mod_cast (show j + 1 ≤ 4 by omega)
      simp only [p4]; linarith
    -- Switch Icc (p4 j) (p4 (j+1)) to Ioo (p4 j) (p4 (j+1)) for a.e. bound:
    have hu_outer_int : ∀ i < 4, IntegrableOn
        (fun x2 => ∫ t in Icc (p4 i) (p4 (i + 1)), u (t, x2))
        (Icc (p4 j) (p4 (j + 1))) volume := by
      intro i hi
      have hsub_i : Icc (p4 i) (p4 (i + 1)) ⊆ Icc (0 : ℝ) 1 := by
        refine Icc_subset_Icc (by simp [p4]; positivity) ?_
        have hle : ((i + 1 : ℕ) : ℝ) ≤ 4 := by exact_mod_cast (show i + 1 ≤ 4 by omega)
        simp only [p4]; linarith
      have hu_box : IntegrableOn u (Icc (p4 i) (p4 (i + 1)) ×ˢ Icc (p4 j) (p4 (j + 1))) volume :=
        hu_int.mono_set (prod_mono hsub_i hsub_j)
      unfold IntegrableOn at hu_box ⊢
      rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at hu_box
      have hG : Integrable (fun z : ℝ × ℝ => u (z.2, z.1))
          ((volume.restrict (Icc (p4 j) (p4 (j + 1)))).prod (volume.restrict (Icc (p4 i) (p4 (i + 1))))) :=
        Measure.measurePreserving_swap.integrable_comp_of_integrable hu_box
      exact hG.integral_prod_left
    -- Notice: for a.e. x2 in Ioo (p4 j) (p4 (j+1)), cell4 x2 = j!
    rw [integral_Icc_eq_integral_Ioc, integral_Ioc_eq_integral_Ioo]
    have hae_j1 : ∀ᵐ x2 ∂(volume.restrict (Ioo (p4 j) (p4 (j + 1)))),
        IntegrableOn (fun s => M.q11 (s, x2) y) (Icc (0 : ℝ) 1) volume :=
      ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Icc_self.trans hsub_j) hae_q
    have hae_j2 : ∀ᵐ x2 ∂(volume.restrict (Ioo (p4 j) (p4 (j + 1)))),
        IntegrableOn (fun s => alpha1 si sj (s, x2) * M.q11 (s, x2) y) (Icc (0 : ℝ) 1) volume :=
      ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Icc_self.trans hsub_j) hae_a1q
    have hae_mem : ∀ᵐ x2 ∂(volume.restrict (Ioo (p4 j) (p4 (j + 1)))),
        x2 ∈ Ioo (p4 j) (p4 (j + 1)) := ae_restrict_mem measurableSet_Ioo
    have hae_le : (fun x2 => ∫ s in Icc (0 : ℝ) 1, alpha1 si sj (s, x2) * M.q11 (s, x2) y) ≤ᵐ[volume.restrict (Ioo (p4 j) (p4 (j + 1)))]
        (fun x2 => ∑ i ∈ Finset.range 4,
          4 * (a1Real si sj i j - a1Real si sj (i + 1) j) *
            ∫ t in Icc (p4 i) (p4 (i + 1)), u (t, x2)) := by
      filter_upwards [hae_j1, hae_j2, hae_mem] with x2 hq_s ha1q_s hx2
      have hcj : cell4 x2 = j := cell4_eq_of_Ioo hj4 hx2.1 hx2.2
      have hx2_01 : x2 ∈ Icc (0 : ℝ) 1 := hsub_j (Ioo_subset_Icc_self hx2)
      let A : ℕ → ℝ := fun i => a1Real si sj i j
      have hA_nn : ∀ i < 4, 0 ≤ A i := fun i _ => a1Real_nonneg hsi hsj hj4
      have hA4 : A 4 = 0 := by simp [A, a1Real_four]
      have hic_1d : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
          (t - s) * M.q11 (s, x2) y ≤ u (t, x2) - u (s, x2) := by
        intro s hs t ht
        have hd := hDSIC.1 (t, x2) ⟨ht, hx2_01⟩ (s, x2) ⟨hs, hx2_01⟩ y hy
        dsimp only [u, u1Report] at hd ⊢
        linarith
      have halpha_eq : (fun s => alpha1 si sj (s, x2) * M.q11 (s, x2) y) =
          (fun s => (let i := cell4 s; let w := 4 * s - (i : ℝ); (1 - w) * A i + w * A (i + 1)) * M.q11 (s, x2) y) := by
        ext s; unfold alpha1; simp only [hcj, A]
      rw [halpha_eq]
      rw [halpha_eq] at ha1q_s
      exact dsic_1d_grid4_ibp A hA_nn hA4 hq_s (fun s hs => hq11_bdd (s, x2) ⟨hs, hx2_01⟩)
        (hu_nn (0, x2) ⟨⟨le_rfl, zero_le_one⟩, hx2_01⟩) hic_1d ha1q_s
    have hrhs_int_oo : IntegrableOn
        (fun x2 => ∑ i ∈ Finset.range 4,
          4 * (a1Real si sj i j - a1Real si sj (i + 1) j) *
            ∫ t in Icc (p4 i) (p4 (i + 1)), u (t, x2))
        (Ioo (p4 j) (p4 (j + 1))) volume := by
      refine (integrableOn_finset_sum' (Finset.range 4) (fun i hi => ?_)).mono_set Ioo_subset_Icc_self
      exact (hu_outer_int i (Finset.mem_range.mp hi)).const_mul _
    calc ∫ x2 in Ioo (p4 j) (p4 (j + 1)), ∫ s in Icc (0 : ℝ) 1, alpha1 si sj (s, x2) * M.q11 (s, x2) y
        ≤ ∫ x2 in Ioo (p4 j) (p4 (j + 1)), ∑ i ∈ Finset.range 4,
            4 * (a1Real si sj i j - a1Real si sj (i + 1) j) *
              ∫ t in Icc (p4 i) (p4 (i + 1)), u (t, x2) :=
          integral_mono_ae (houter_lhs.mono_set (Ioo_subset_Icc_self.trans hsub_j)) hrhs_int_oo hae_le
      _ = ∫ x2 in Icc (p4 j) (p4 (j + 1)), ∑ i ∈ Finset.range 4,
            4 * (a1Real si sj i j - a1Real si sj (i + 1) j) *
              ∫ t in Icc (p4 i) (p4 (i + 1)), u (t, x2) := by
          rw [← integral_Ioc_eq_integral_Ioo, ← integral_Icc_eq_integral_Ioc]
      _ = ∑ i ∈ Finset.range 4,
            4 * (a1Real si sj i j - a1Real si sj (i + 1) j) *
              ∫ x in Icc (p4 i) (p4 (i + 1)) ×ˢ Icc (p4 j) (p4 (j + 1)), u x := by
          rw [setIntegral_finset_sum' (Finset.range 4) (fun i hi =>
            (hu_outer_int i (Finset.mem_range.mp hi)).const_mul _)]
          apply Finset.sum_congr rfl
          intro i hi
          have hi4 : i < 4 := Finset.mem_range.mp hi
          have hsub_i : Icc (p4 i) (p4 (i + 1)) ⊆ Icc (0 : ℝ) 1 := by
            refine Icc_subset_Icc (by simp [p4]; positivity) ?_
            have hle : ((i + 1 : ℕ) : ℝ) ≤ 4 := by exact_mod_cast (show i + 1 ≤ 4 by omega)
            simp only [p4]; linarith
          rw [integral_const_mul, setIntegral_prod_symm_eq (hu_int.mono_set (prod_mono hsub_i hsub_j))]
  -- Bound 2: ∫ x in unitSquare, alpha2 si sj x * M.q12 x y (symmetric, no swap needed!)
  have hbnd2 : ∫ x in unitSquare, alpha2 si sj x * M.q12 x y ≤
      ∑ i ∈ Finset.range 4, ∑ j ∈ Finset.range 4,
        4 * (a2Real si sj i j - a2Real si sj i (j + 1)) *
          ∫ x in Icc (p4 i) (p4 (i + 1)) ×ˢ Icc (p4 j) (p4 (j + 1)), u x := by
    unfold unitSquare at ha2q_int hq12_int hu_int ⊢
    rw [setIntegral_prod_eq ha2q_int]
    have hae_q : ∀ᵐ x1 ∂(volume.restrict (Icc (0 : ℝ) 1)),
        IntegrableOn (fun s => M.q12 (x1, s) y) (Icc (0 : ℝ) 1) volume :=
      ae_integrableOn_prod_right hq12_int
    have hae_a2q : ∀ᵐ x1 ∂(volume.restrict (Icc (0 : ℝ) 1)),
        IntegrableOn (fun s => alpha2 si sj (x1, s) * M.q12 (x1, s) y) (Icc (0 : ℝ) 1) volume :=
      ae_integrableOn_prod_right ha2q_int
    have houter_lhs : IntegrableOn (fun x1 => ∫ s in Icc (0 : ℝ) 1, alpha2 si sj (x1, s) * M.q12 (x1, s) y)
        (Icc (0 : ℝ) 1) volume := by
      unfold IntegrableOn at ha2q_int ⊢
      rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at ha2q_int
      exact ha2q_int.integral_prod_left
    have hpart_i := setIntegral_Icc_partition 4 p4
      (fun x1 => ∫ s in Icc (0 : ℝ) 1, alpha2 si sj (x1, s) * M.q12 (x1, s) y)
      hp4_mono (by simpa [hp4_0, hp4_4] using houter_lhs)
    simp only [hp4_0, hp4_4] at hpart_i
    rw [hpart_i]
    apply Finset.sum_le_sum
    intro i hi
    have hi4 : i < 4 := Finset.mem_range.mp hi
    have hsub_i : Icc (p4 i) (p4 (i + 1)) ⊆ Icc (0 : ℝ) 1 := by
      refine Icc_subset_Icc (by simp [p4]; positivity) ?_
      have hle : ((i + 1 : ℕ) : ℝ) ≤ 4 := by exact_mod_cast (show i + 1 ≤ 4 by omega)
      simp only [p4]; linarith
    have hu_outer_int : ∀ j < 4, IntegrableOn
        (fun x1 => ∫ t in Icc (p4 j) (p4 (j + 1)), u (x1, t))
        (Icc (p4 i) (p4 (i + 1))) volume := by
      intro j hj
      have hj4 : j < 4 := hj
      have hsub_j : Icc (p4 j) (p4 (j + 1)) ⊆ Icc (0 : ℝ) 1 := by
        refine Icc_subset_Icc (by simp [p4]; positivity) ?_
        have hle : ((j + 1 : ℕ) : ℝ) ≤ 4 := by exact_mod_cast (show j + 1 ≤ 4 by omega)
        simp only [p4]; linarith
      have hu_box : IntegrableOn u (Icc (p4 i) (p4 (i + 1)) ×ˢ Icc (p4 j) (p4 (j + 1))) volume :=
        hu_int.mono_set (prod_mono hsub_i hsub_j)
      unfold IntegrableOn at hu_box ⊢
      rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at hu_box
      exact hu_box.integral_prod_left
    rw [integral_Icc_eq_integral_Ioc, integral_Ioc_eq_integral_Ioo]
    have hae_i1 := ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Icc_self.trans hsub_i) hae_q
    have hae_i2 := ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Icc_self.trans hsub_i) hae_a2q
    have hae_mem : ∀ᵐ x1 ∂(volume.restrict (Ioo (p4 i) (p4 (i + 1)))),
        x1 ∈ Ioo (p4 i) (p4 (i + 1)) := ae_restrict_mem measurableSet_Ioo
    have hae_le : (fun x1 => ∫ s in Icc (0 : ℝ) 1, alpha2 si sj (x1, s) * M.q12 (x1, s) y) ≤ᵐ[volume.restrict (Ioo (p4 i) (p4 (i + 1)))]
        (fun x1 => ∑ j ∈ Finset.range 4,
          4 * (a2Real si sj i j - a2Real si sj i (j + 1)) *
            ∫ t in Icc (p4 j) (p4 (j + 1)), u (x1, t)) := by
      filter_upwards [hae_i1, hae_i2, hae_mem] with x1 hq_s ha2q_s hx1
      have hci : cell4 x1 = i := cell4_eq_of_Ioo hi4 hx1.1 hx1.2
      have hx1_01 : x1 ∈ Icc (0 : ℝ) 1 := hsub_i (Ioo_subset_Icc_self hx1)
      let A : ℕ → ℝ := fun j => a2Real si sj i j
      have hA_nn : ∀ j < 4, 0 ≤ A j := fun j _ => a2Real_nonneg hsi hsj hi4
      have hA4 : A 4 = 0 := by simp [A, a2Real_four]
      have hic_1d : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
          (t - s) * M.q12 (x1, s) y ≤ u (x1, t) - u (x1, s) := by
        intro s hs t ht
        have hd := hDSIC.1 (x1, t) ⟨hx1_01, ht⟩ (x1, s) ⟨hx1_01, hs⟩ y hy
        dsimp only [u, u1Report] at hd ⊢
        linarith
      have halpha_eq : (fun s => alpha2 si sj (x1, s) * M.q12 (x1, s) y) =
          (fun s => (let j := cell4 s; let w := 4 * s - (j : ℝ); (1 - w) * A j + w * A (j + 1)) * M.q12 (x1, s) y) := by
        ext s; unfold alpha2; simp only [hci, A]
      rw [halpha_eq]
      rw [halpha_eq] at ha2q_s
      exact dsic_1d_grid4_ibp A hA_nn hA4 hq_s (fun s hs => hq12_bdd (x1, s) ⟨hx1_01, hs⟩)
        (hu_nn (x1, 0) ⟨hx1_01, ⟨le_rfl, zero_le_one⟩⟩) hic_1d ha2q_s
    have hrhs_int_oo : IntegrableOn
        (fun x1 => ∑ j ∈ Finset.range 4,
          4 * (a2Real si sj i j - a2Real si sj i (j + 1)) *
            ∫ t in Icc (p4 j) (p4 (j + 1)), u (x1, t))
        (Ioo (p4 i) (p4 (i + 1))) volume := by
      refine (integrableOn_finset_sum' (Finset.range 4) (fun j hj => ?_)).mono_set Ioo_subset_Icc_self
      exact (hu_outer_int j (Finset.mem_range.mp hj)).const_mul _
    calc ∫ x1 in Ioo (p4 i) (p4 (i + 1)), ∫ s in Icc (0 : ℝ) 1, alpha2 si sj (x1, s) * M.q12 (x1, s) y
        ≤ ∫ x1 in Ioo (p4 i) (p4 (i + 1)), ∑ j ∈ Finset.range 4,
            4 * (a2Real si sj i j - a2Real si sj i (j + 1)) *
              ∫ t in Icc (p4 j) (p4 (j + 1)), u (x1, t) :=
          integral_mono_ae (houter_lhs.mono_set (Ioo_subset_Icc_self.trans hsub_i)) hrhs_int_oo hae_le
      _ = ∫ x1 in Icc (p4 i) (p4 (i + 1)), ∑ j ∈ Finset.range 4,
            4 * (a2Real si sj i j - a2Real si sj i (j + 1)) *
              ∫ t in Icc (p4 j) (p4 (j + 1)), u (x1, t) := by
          rw [← integral_Ioc_eq_integral_Ioo, ← integral_Icc_eq_integral_Ioc]
      _ = ∑ j ∈ Finset.range 4,
            4 * (a2Real si sj i j - a2Real si sj i (j + 1)) *
              ∫ x in Icc (p4 i) (p4 (i + 1)) ×ˢ Icc (p4 j) (p4 (j + 1)), u x := by
          rw [setIntegral_finset_sum' (Finset.range 4) (fun j hj =>
            (hu_outer_int j (Finset.mem_range.mp hj)).const_mul _)]
          apply Finset.sum_congr rfl
          intro j hj
          have hj4 : j < 4 := Finset.mem_range.mp hj
          have hsub_j : Icc (p4 j) (p4 (j + 1)) ⊆ Icc (0 : ℝ) 1 := by
            refine Icc_subset_Icc (by simp [p4]; positivity) ?_
            have hle : ((j + 1 : ℕ) : ℝ) ≤ 4 := by exact_mod_cast (show j + 1 ≤ 4 by omega)
            simp only [p4]; linarith
          rw [integral_const_mul, setIntegral_prod_eq (hu_int.mono_set (prod_mono hsub_i hsub_j))]
  -- Sum of u integrals over the 4x4 boxes equals ∫ x in unitSquare, u x:
  have hu_partition : (∑ i ∈ Finset.range 4, ∑ j ∈ Finset.range 4,
      ∫ x in Icc (p4 i) (p4 (i + 1)) ×ˢ Icc (p4 j) (p4 (j + 1)), u x) =
      ∫ x in unitSquare, u x := by
    symm
    unfold unitSquare at hu_int ⊢
    rw [setIntegral_prod_eq hu_int]
    have hu_out : IntegrableOn (fun x1 => ∫ x2 in Icc (0 : ℝ) 1, u (x1, x2)) (Icc (0 : ℝ) 1) volume := by
      unfold IntegrableOn at hu_int ⊢
      rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at hu_int
      exact hu_int.integral_prod_left
    have hp_out := setIntegral_Icc_partition 4 p4 (fun x1 => ∫ x2 in Icc (0 : ℝ) 1, u (x1, x2))
      hp4_mono (by simpa [hp4_0, hp4_4] using hu_out)
    simp only [hp4_0, hp4_4] at hp_out
    rw [hp_out]
    -- Wait: for a.e. x1, x2 -> u (x1, x2) is IntegrableOn Icc 0 1!
    have hae_u : ∀ᵐ x1 ∂(volume.restrict (Icc (0 : ℝ) 1)),
        IntegrableOn (fun x2 => u (x1, x2)) (Icc (0 : ℝ) 1) volume :=
      ae_integrableOn_prod_right hu_int
    apply Finset.sum_congr rfl
    intro i hi
    have hi4 : i < 4 := Finset.mem_range.mp hi
    have hsub_i : Icc (p4 i) (p4 (i + 1)) ⊆ Icc (0 : ℝ) 1 := by
      refine Icc_subset_Icc (by simp [p4]; positivity) ?_
      have hle : ((i + 1 : ℕ) : ℝ) ≤ 4 := by exact_mod_cast (show i + 1 ≤ 4 by omega)
      simp only [p4]; linarith
    have hae_ui := ae_restrict_of_ae_restrict_of_subset hsub_i hae_u
    have hae_eq : (fun x1 => ∫ x2 in Icc (0 : ℝ) 1, u (x1, x2)) =ᵐ[volume.restrict (Icc (p4 i) (p4 (i + 1)))]
        (fun x1 => ∑ j ∈ Finset.range 4, ∫ x2 in Icc (p4 j) (p4 (j + 1)), u (x1, x2)) := by
      filter_upwards [hae_ui] with x1 hx1_int
      have hp_in := setIntegral_Icc_partition 4 p4 (fun x2 => u (x1, x2))
        hp4_mono (by simpa [hp4_0, hp4_4] using hx1_int)
      simpa [hp4_0, hp4_4] using hp_in
    rw [integral_congr_ae hae_eq]
    have hj_int : ∀ j ∈ Finset.range 4, IntegrableOn
        (fun x1 => ∫ x2 in Icc (p4 j) (p4 (j + 1)), u (x1, x2))
        (Icc (p4 i) (p4 (i + 1))) volume := by
      intro j hj
      have hj4 : j < 4 := Finset.mem_range.mp hj
      have hsub_j : Icc (p4 j) (p4 (j + 1)) ⊆ Icc (0 : ℝ) 1 := by
        refine Icc_subset_Icc (by simp [p4]; positivity) ?_
        have hle : ((j + 1 : ℕ) : ℝ) ≤ 4 := by exact_mod_cast (show j + 1 ≤ 4 by omega)
        simp only [p4]; linarith
      have hu_box := hu_int.mono_set (prod_mono hsub_i hsub_j)
      unfold IntegrableOn at hu_box ⊢
      rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at hu_box
      exact hu_box.integral_prod_left
    rw [setIntegral_finset_sum' (Finset.range 4) hj_int]
    apply Finset.sum_congr rfl
    intro j hj
    have hj4 : j < 4 := Finset.mem_range.mp hj
    have hsub_j : Icc (p4 j) (p4 (j + 1)) ⊆ Icc (0 : ℝ) 1 := by
      refine Icc_subset_Icc (by simp [p4]; positivity) ?_
      have hle : ((j + 1 : ℕ) : ℝ) ≤ 4 := by exact_mod_cast (show j + 1 ≤ 4 by omega)
      simp only [p4]; linarith
    rw [setIntegral_prod_eq (hu_int.mono_set (prod_mono hsub_i hsub_j))]
  -- Combine hbnd1 + hbnd2 <= ∫ u:
  have hsum_u_le : (∫ x in unitSquare, alpha1 si sj x * M.q11 x y) +
      (∫ x in unitSquare, alpha2 si sj x * M.q12 x y) ≤ ∫ x in unitSquare, u x := by
    calc (∫ x in unitSquare, alpha1 si sj x * M.q11 x y) +
          (∫ x in unitSquare, alpha2 si sj x * M.q12 x y)
        ≤ (∑ i ∈ Finset.range 4, ∑ j ∈ Finset.range 4,
            4 * (a1Real si sj i j - a1Real si sj (i + 1) j) *
              ∫ x in Icc (p4 i) (p4 (i + 1)) ×ˢ Icc (p4 j) (p4 (j + 1)), u x) +
          (∑ i ∈ Finset.range 4, ∑ j ∈ Finset.range 4,
            4 * (a2Real si sj i j - a2Real si sj i (j + 1)) *
              ∫ x in Icc (p4 i) (p4 (i + 1)) ×ˢ Icc (p4 j) (p4 (j + 1)), u x) := add_le_add hbnd1 hbnd2
      _ = ∑ i ∈ Finset.range 4, ∑ j ∈ Finset.range 4,
            (4 * (a1Real si sj i j - a1Real si sj (i + 1) j) +
             4 * (a2Real si sj i j - a2Real si sj i (j + 1))) *
              ∫ x in Icc (p4 i) (p4 (i + 1)) ×ˢ Icc (p4 j) (p4 (j + 1)), u x := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro i _
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro j _
          ring
      _ ≤ ∑ i ∈ Finset.range 4, ∑ j ∈ Finset.range 4,
            ∫ x in Icc (p4 i) (p4 (i + 1)) ×ˢ Icc (p4 j) (p4 (j + 1)), u x := by
          apply Finset.sum_le_sum; intro i hi
          apply Finset.sum_le_sum; intro j hj
          have hi4 : i < 4 := Finset.mem_range.mp hi
          have hj4 : j < 4 := Finset.mem_range.mp hj
          have hdiv := a12Real_div_le_one hsi hsj hi4 hj4
          have hbox_sub : Icc (p4 i) (p4 (i + 1)) ×ˢ Icc (p4 j) (p4 (j + 1)) ⊆ unitSquare := by
            refine prod_mono (Icc_subset_Icc (by simp [p4]; positivity) ?_) (Icc_subset_Icc (by simp [p4]; positivity) ?_)
            · have hle : ((i + 1 : ℕ) : ℝ) ≤ 4 := by exact_mod_cast (show i + 1 ≤ 4 by omega)
              simp only [p4]; linarith
            · have hle : ((j + 1 : ℕ) : ℝ) ≤ 4 := by exact_mod_cast (show j + 1 ≤ 4 by omega)
              simp only [p4]; linarith
          have hu_box_nn : 0 ≤ ∫ x in Icc (p4 i) (p4 (i + 1)) ×ˢ Icc (p4 j) (p4 (j + 1)), u x :=
            setIntegral_nonneg (measurableSet_Icc.prod measurableSet_Icc) (fun x hx => hu_nn x (hbox_sub hx))
          nlinarith
      _ = ∫ x in unitSquare, u x := hu_partition
  -- Rearrange t1 = x.1 * q11 + x.2 * q12 - u:
  have ht1_eq : (∫ x in unitSquare, M.t1 x y) =
      (∫ x in unitSquare, x.1 * M.q11 x y) + (∫ x in unitSquare, x.2 * M.q12 x y) -
      (∫ x in unitSquare, u x) := by
    have hfun : (fun x => M.t1 x y) = (fun x => (x.1 * M.q11 x y + x.2 * M.q12 x y) - u x) := by
      ext x; simp [u, u1Report]
    have hsum12 : IntegrableOn (fun x : Type2 => x.1 * M.q11 x y + x.2 * M.q12 x y) unitSquare volume :=
      Integrable.add hxq11_int hxq12_int
    rw [hfun, integral_sub hsum12 hu_int, integral_add hxq11_int hxq12_int]
  have hrhs_eq : (∫ x in unitSquare, ((x.1 - alpha1 si sj x) * M.q11 x y + (x.2 - alpha2 si sj x) * M.q12 x y)) =
      (∫ x in unitSquare, x.1 * M.q11 x y) - (∫ x in unitSquare, alpha1 si sj x * M.q11 x y) +
      ((∫ x in unitSquare, x.2 * M.q12 x y) - (∫ x in unitSquare, alpha2 si sj x * M.q12 x y)) := by
    have h1 : (fun x => (x.1 - alpha1 si sj x) * M.q11 x y) = (fun x => x.1 * M.q11 x y - alpha1 si sj x * M.q11 x y) := by ext x; ring
    have h2 : (fun x => (x.2 - alpha2 si sj x) * M.q12 x y) = (fun x => x.2 * M.q12 x y - alpha2 si sj x * M.q12 x y) := by ext x; ring
    have hi1 : IntegrableOn (fun x => (x.1 - alpha1 si sj x) * M.q11 x y) unitSquare volume := by
      rw [h1]; exact hxq11_int.sub ha1q_int
    have hi2 : IntegrableOn (fun x => (x.2 - alpha2 si sj x) * M.q12 x y) unitSquare volume := by
      rw [h2]; exact hxq12_int.sub ha2q_int
    rw [integral_add hi1 hi2, h1, h2, integral_sub hxq11_int ha1q_int, integral_sub hxq12_int ha2q_int]
  linarith

-- Bidder 2 slice bound by bidder-swap symmetry of Mechanism!
def swapMech (M : Mechanism) : Mechanism where
  q11 x y := M.q21 y x
  q12 x y := M.q22 y x
  q21 x y := M.q11 y x
  q22 x y := M.q12 y x
  t1 x y := M.t2 y x
  t2 x y := M.t1 y x



/-! ### Section 5: Bilinear Convexity Bound on 2D Subsquares & Final Revenue Theorem -/

def max3 (a b c : ℝ) : ℝ := max a (max b c)

lemma max3_cast (a b c : Int) :
    ((max3Int a b c : Int) : ℝ) = max3 (a : ℝ) (b : ℝ) (c : ℝ) := by
  unfold max3Int max3
  simp only [Int.cast_max]

lemma max3_div (a b c : ℝ) :
    max3 (a / 7680) (b / 7680) (c / 7680) = (max3 a b c) / 7680 := by
  unfold max3
  simp only [max_def]
  split_ifs <;> first | rfl | linarith

lemma sum_range4_cast (f : ℕ → Int) :
    (∑ i ∈ Finset.range 4, (f i : ℝ)) = ((range4Sum f : Int) : ℝ) := by
  unfold range4Sum
  push_cast
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]

lemma max3_affine_bilinear_le (c0 c1 d0 d1 a b : ℝ)
    {t s : ℝ} (ht : t ∈ Icc a (a + 1 / 16)) (hs : s ∈ Icc b (b + 1 / 16)) :
    let φ := fun x y => max3 0 (c0 + c1 * x) (d0 + d1 * y)
    let lam := 16 * (t - a)
    let mu := 16 * (s - b)
    φ t s ≤
      (1 - lam) * ((1 - mu) * φ a b + mu * φ a (b + 1 / 16)) +
      lam * ((1 - mu) * φ (a + 1 / 16) b + mu * φ (a + 1 / 16) (b + 1 / 16)) := by
  intro φ lam mu
  have hlam0 : 0 ≤ lam := by simp only [lam]; linarith [ht.1]
  have hlam1 : 0 ≤ 1 - lam := by simp only [lam]; linarith [ht.2]
  have hmu0 : 0 ≤ mu := by simp only [mu]; linarith [hs.1]
  have hmu1 : 0 ≤ 1 - mu := by simp only [mu]; linarith [hs.2]
  have ht_eq : c0 + c1 * t = (1 - lam) * (c0 + c1 * a) + lam * (c0 + c1 * (a + 1 / 16)) := by
    simp only [lam]; ring
  have hs_eq : d0 + d1 * s = (1 - mu) * (d0 + d1 * b) + mu * (d0 + d1 * (b + 1 / 16)) := by
    simp only [mu]; ring
  have hstep_x : φ t s ≤ (1 - lam) * φ a s + lam * φ (a + 1 / 16) s := by
    unfold φ max3
    refine max_le ?_ (max_le ?_ ?_)
    · have h0a : 0 ≤ max (0 : ℝ) (max (c0 + c1 * a) (d0 + d1 * s)) := le_max_left _ _
      have h0b : 0 ≤ max (0 : ℝ) (max (c0 + c1 * (a + 1 / 16)) (d0 + d1 * s)) := le_max_left _ _
      nlinarith
    · rw [ht_eq]
      have hfa : c0 + c1 * a ≤ max (0 : ℝ) (max (c0 + c1 * a) (d0 + d1 * s)) :=
        le_max_of_le_right (le_max_left _ _)
      have hfb : c0 + c1 * (a + 1 / 16) ≤ max (0 : ℝ) (max (c0 + c1 * (a + 1 / 16)) (d0 + d1 * s)) :=
        le_max_of_le_right (le_max_left _ _)
      nlinarith
    · have hga : d0 + d1 * s ≤ max (0 : ℝ) (max (c0 + c1 * a) (d0 + d1 * s)) :=
        le_max_of_le_right (le_max_right _ _)
      have hgb : d0 + d1 * s ≤ max (0 : ℝ) (max (c0 + c1 * (a + 1 / 16)) (d0 + d1 * s)) :=
        le_max_of_le_right (le_max_right _ _)
      nlinarith
  have hstep_y : ∀ x : ℝ, φ x s ≤ (1 - mu) * φ x b + mu * φ x (b + 1 / 16) := by
    intro x; unfold φ max3
    refine max_le ?_ (max_le ?_ ?_)
    · have h0a : 0 ≤ max (0 : ℝ) (max (c0 + c1 * x) (d0 + d1 * b)) := le_max_left _ _
      have h0b : 0 ≤ max (0 : ℝ) (max (c0 + c1 * x) (d0 + d1 * (b + 1 / 16))) := le_max_left _ _
      nlinarith
    · have hfa : c0 + c1 * x ≤ max (0 : ℝ) (max (c0 + c1 * x) (d0 + d1 * b)) :=
        le_max_of_le_right (le_max_left _ _)
      have hfb : c0 + c1 * x ≤ max (0 : ℝ) (max (c0 + c1 * x) (d0 + d1 * (b + 1 / 16))) :=
        le_max_of_le_right (le_max_left _ _)
      nlinarith
    · rw [hs_eq]
      have hga : d0 + d1 * b ≤ max (0 : ℝ) (max (c0 + c1 * x) (d0 + d1 * b)) :=
        le_max_of_le_right (le_max_right _ _)
      have hgb : d0 + d1 * (b + 1 / 16) ≤ max (0 : ℝ) (max (c0 + c1 * x) (d0 + d1 * (b + 1 / 16))) :=
        le_max_of_le_right (le_max_right _ _)
      nlinarith
  have hy1 := mul_le_mul_of_nonneg_left (hstep_y a) hlam1
  have hy2 := mul_le_mul_of_nonneg_left (hstep_y (a + 1 / 16)) hlam0
  linarith

lemma setIntegral_subsquare_max3_le (c0 c1 d0 d1 a b : ℝ) :
    let φ := fun p : ℝ × ℝ => max3 0 (c0 + c1 * p.1) (d0 + d1 * p.2)
    ∫ p in Icc a (a + 1 / 16) ×ˢ Icc b (b + 1 / 16), φ p ≤
      (1 / 1024 : ℝ) *
        (φ (a, b) + φ (a, b + 1 / 16) + φ (a + 1 / 16, b) + φ (a + 1 / 16, b + 1 / 16)) := by
  intro φ
  let B : ℝ × ℝ → ℝ := fun p =>
    let lam := 16 * (p.1 - a)
    let mu := 16 * (p.2 - b)
    (1 - lam) * ((1 - mu) * φ (a, b) + mu * φ (a, b + 1 / 16)) +
    lam * ((1 - mu) * φ (a + 1 / 16, b) + mu * φ (a + 1 / 16, b + 1 / 16))
  have hcomp : IsCompact (Icc a (a + 1 / 16) ×ˢ Icc b (b + 1 / 16)) := isCompact_Icc.prod isCompact_Icc
  have hφ_cont : Continuous φ := by
    unfold φ max3; fun_prop
  have hB_cont : Continuous B := by
    unfold B; fun_prop
  have hφ_int : IntegrableOn φ (Icc a (a + 1 / 16) ×ˢ Icc b (b + 1 / 16)) volume :=
    hφ_cont.continuousOn.integrableOn_compact hcomp
  have hB_int : IntegrableOn B (Icc a (a + 1 / 16) ×ˢ Icc b (b + 1 / 16)) volume :=
    hB_cont.continuousOn.integrableOn_compact hcomp
  have hle := setIntegral_mono_on hφ_int hB_int (measurableSet_Icc.prod measurableSet_Icc)
    (fun p hp => max3_affine_bilinear_le c0 c1 d0 d1 a b hp.1 hp.2)
  have hB_eval : ∫ p in Icc a (a + 1 / 16) ×ˢ Icc b (b + 1 / 16), B p =
      (1 / 1024 : ℝ) *
        (φ (a, b) + φ (a, b + 1 / 16) + φ (a + 1 / 16, b) + φ (a + 1 / 16, b + 1 / 16)) := by
    rw [setIntegral_prod_eq hB_int]
    have hb_le : b ≤ b + 1 / 16 := by linarith
    have ha_le : a ≤ a + 1 / 16 := by linarith
    have hinner : ∀ t : ℝ, ∫ s in Icc b (b + 1 / 16), B (t, s) =
        (1 / 32 : ℝ) * ((1 - 16 * (t - a)) * (φ (a, b) + φ (a, b + 1 / 16)) +
          (16 * (t - a)) * (φ (a + 1 / 16, b) + φ (a + 1 / 16, b + 1 / 16))) := by
      intro t
      have hlin : (fun s => B (t, s)) = (fun s =>
          ((1 - 16 * (t - a)) * ((1 + 16 * b) * φ (a, b) - 16 * b * φ (a, b + 1 / 16)) +
           (16 * (t - a)) * ((1 + 16 * b) * φ (a + 1 / 16, b) - 16 * b * φ (a + 1 / 16, b + 1 / 16))) +
          ((1 - 16 * (t - a)) * (16 * (φ (a, b + 1 / 16) - φ (a, b))) +
           (16 * (t - a)) * (16 * (φ (a + 1 / 16, b + 1 / 16) - φ (a + 1 / 16, b)))) * s) := by
        ext s; unfold B; ring
      rw [hlin, setIntegral_Icc_affine hb_le]
      ring
    simp_rw [hinner]
    have hlin2 : (fun t => (1 / 32 : ℝ) * ((1 - 16 * (t - a)) * (φ (a, b) + φ (a, b + 1 / 16)) +
          (16 * (t - a)) * (φ (a + 1 / 16, b) + φ (a + 1 / 16, b + 1 / 16)))) =
        (fun t => ((1 / 32) * ((1 + 16 * a) * (φ (a, b) + φ (a, b + 1 / 16)) -
            16 * a * (φ (a + 1 / 16, b) + φ (a + 1 / 16, b + 1 / 16)))) +
          ((1 / 2) * ((φ (a + 1 / 16, b) + φ (a + 1 / 16, b + 1 / 16)) -
            (φ (a, b) + φ (a, b + 1 / 16)))) * t) := by
      ext t; ring
    rw [hlin2, setIntegral_Icc_affine ha_le]
    ring
  linarith

noncomputable def Phi1 (x y : Type2) : ℝ :=
  x.1 - alpha1 (cell4 y.1) (cell4 y.2) x

noncomputable def Phi2 (x y : Type2) : ℝ :=
  x.2 - alpha2 (cell4 y.1) (cell4 y.2) x

lemma measurable_max_real {α : Type*} [MeasurableSpace α] {f g : α → ℝ}
    (hf : Measurable f) (hg : Measurable g) : Measurable (fun x => max (f x) (g x)) := by
  have heq : (fun x => max (f x) (g x)) = (fun x => if f x ≤ g x then g x else f x) := by
    ext x; exact max_def (α := ℝ) (f x) (g x)
  rw [heq]
  exact Measurable.ite (measurableSet_le hf hg) hg hf

lemma measurable_max3_real {α : Type*} [MeasurableSpace α] {f g h : α → ℝ}
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h) :
    Measurable (fun x => max3 (f x) (g x) (h x)) := by
  unfold max3
  exact measurable_max_real hf (measurable_max_real hg hh)

lemma measurable_Phi1 : Measurable (fun p : Type2 × Type2 => Phi1 p.1 p.2) := by
  unfold Phi1 alpha1
  have hx1 : Measurable (fun p : Type2 × Type2 => p.1.1) := measurable_fst.comp measurable_fst
  have hx2 : Measurable (fun p : Type2 × Type2 => p.1.2) := measurable_snd.comp measurable_fst
  have hy1 : Measurable (fun p : Type2 × Type2 => p.2.1) := measurable_fst.comp measurable_snd
  have hy2 : Measurable (fun p : Type2 × Type2 => p.2.2) := measurable_snd.comp measurable_snd
  have hcx1 : Measurable (fun p : Type2 × Type2 => cell4 p.1.1) := measurable_cell4.comp hx1
  have hcx2 : Measurable (fun p : Type2 × Type2 => cell4 p.1.2) := measurable_cell4.comp hx2
  have hcy1 : Measurable (fun p : Type2 × Type2 => cell4 p.2.1) := measurable_cell4.comp hy1
  have hcy2 : Measurable (fun p : Type2 × Type2 => cell4 p.2.2) := measurable_cell4.comp hy2
  have hcr : Measurable (fun p : Type2 × Type2 => ((cell4 p.1.1 : ℕ) : ℝ)) :=
    (Measurable.of_discrete (f := fun n : ℕ => (n : ℝ))).comp hcx1
  have hu : Measurable (fun p : Type2 × Type2 => 4 * p.1.1 - ((cell4 p.1.1 : ℕ) : ℝ)) :=
    (measurable_const.mul hx1).sub hcr
  have haL : Measurable (fun p : Type2 × Type2 => a1Real (cell4 p.2.1) (cell4 p.2.2) (cell4 p.1.1) (cell4 p.1.2)) :=
    (Measurable.of_discrete (f := fun q : (ℕ × ℕ) × (ℕ × ℕ) => a1Real q.1.1 q.1.2 q.2.1 q.2.2)).comp
      ((hcy1.prodMk hcy2).prodMk (hcx1.prodMk hcx2))
  have haR : Measurable (fun p : Type2 × Type2 => a1Real (cell4 p.2.1) (cell4 p.2.2) (cell4 p.1.1 + 1) (cell4 p.1.2)) :=
    (Measurable.of_discrete (f := fun q : (ℕ × ℕ) × (ℕ × ℕ) => a1Real q.1.1 q.1.2 (q.2.1 + 1) q.2.2)).comp
      ((hcy1.prodMk hcy2).prodMk (hcx1.prodMk hcx2))
  exact hx1.sub (((measurable_const.sub hu).mul haL).add (hu.mul haR))

lemma measurable_Phi2 : Measurable (fun p : Type2 × Type2 => Phi2 p.1 p.2) := by
  unfold Phi2 alpha2
  have hx1 : Measurable (fun p : Type2 × Type2 => p.1.1) := measurable_fst.comp measurable_fst
  have hx2 : Measurable (fun p : Type2 × Type2 => p.1.2) := measurable_snd.comp measurable_fst
  have hy1 : Measurable (fun p : Type2 × Type2 => p.2.1) := measurable_fst.comp measurable_snd
  have hy2 : Measurable (fun p : Type2 × Type2 => p.2.2) := measurable_snd.comp measurable_snd
  have hcx1 : Measurable (fun p : Type2 × Type2 => cell4 p.1.1) := measurable_cell4.comp hx1
  have hcx2 : Measurable (fun p : Type2 × Type2 => cell4 p.1.2) := measurable_cell4.comp hx2
  have hcy1 : Measurable (fun p : Type2 × Type2 => cell4 p.2.1) := measurable_cell4.comp hy1
  have hcy2 : Measurable (fun p : Type2 × Type2 => cell4 p.2.2) := measurable_cell4.comp hy2
  have hcr : Measurable (fun p : Type2 × Type2 => ((cell4 p.1.2 : ℕ) : ℝ)) :=
    (Measurable.of_discrete (f := fun n : ℕ => (n : ℝ))).comp hcx2
  have hv : Measurable (fun p : Type2 × Type2 => 4 * p.1.2 - ((cell4 p.1.2 : ℕ) : ℝ)) :=
    (measurable_const.mul hx2).sub hcr
  have haL : Measurable (fun p : Type2 × Type2 => a2Real (cell4 p.2.1) (cell4 p.2.2) (cell4 p.1.1) (cell4 p.1.2)) :=
    (Measurable.of_discrete (f := fun q : (ℕ × ℕ) × (ℕ × ℕ) => a2Real q.1.1 q.1.2 q.2.1 q.2.2)).comp
      ((hcy1.prodMk hcy2).prodMk (hcx1.prodMk hcx2))
  have haR : Measurable (fun p : Type2 × Type2 => a2Real (cell4 p.2.1) (cell4 p.2.2) (cell4 p.1.1) (cell4 p.1.2 + 1)) :=
    (Measurable.of_discrete (f := fun q : (ℕ × ℕ) × (ℕ × ℕ) => a2Real q.1.1 q.1.2 q.2.1 (q.2.2 + 1))).comp
      ((hcy1.prodMk hcy2).prodMk (hcx1.prodMk hcx2))
  exact hx2.sub (((measurable_const.sub hv).mul haL).add (hv.mul haR))

lemma measurable_Phi1_swap : Measurable (fun p : Type2 × Type2 => Phi1 p.2 p.1) := by
  unfold Phi1 alpha1
  have hx1 : Measurable (fun p : Type2 × Type2 => p.1.1) := measurable_fst.comp measurable_fst
  have hx2 : Measurable (fun p : Type2 × Type2 => p.1.2) := measurable_snd.comp measurable_fst
  have hy1 : Measurable (fun p : Type2 × Type2 => p.2.1) := measurable_fst.comp measurable_snd
  have hy2 : Measurable (fun p : Type2 × Type2 => p.2.2) := measurable_snd.comp measurable_snd
  have hcx1 : Measurable (fun p : Type2 × Type2 => cell4 p.1.1) := measurable_cell4.comp hx1
  have hcx2 : Measurable (fun p : Type2 × Type2 => cell4 p.1.2) := measurable_cell4.comp hx2
  have hcy1 : Measurable (fun p : Type2 × Type2 => cell4 p.2.1) := measurable_cell4.comp hy1
  have hcy2 : Measurable (fun p : Type2 × Type2 => cell4 p.2.2) := measurable_cell4.comp hy2
  have hcr : Measurable (fun p : Type2 × Type2 => ((cell4 p.2.1 : ℕ) : ℝ)) :=
    (Measurable.of_discrete (f := fun n : ℕ => (n : ℝ))).comp hcy1
  have hu : Measurable (fun p : Type2 × Type2 => 4 * p.2.1 - ((cell4 p.2.1 : ℕ) : ℝ)) :=
    (measurable_const.mul hy1).sub hcr
  have haL : Measurable (fun p : Type2 × Type2 => a1Real (cell4 p.1.1) (cell4 p.1.2) (cell4 p.2.1) (cell4 p.2.2)) :=
    (Measurable.of_discrete (f := fun q : (ℕ × ℕ) × (ℕ × ℕ) => a1Real q.1.1 q.1.2 q.2.1 q.2.2)).comp
      ((hcx1.prodMk hcx2).prodMk (hcy1.prodMk hcy2))
  have haR : Measurable (fun p : Type2 × Type2 => a1Real (cell4 p.1.1) (cell4 p.1.2) (cell4 p.2.1 + 1) (cell4 p.2.2)) :=
    (Measurable.of_discrete (f := fun q : (ℕ × ℕ) × (ℕ × ℕ) => a1Real q.1.1 q.1.2 (q.2.1 + 1) q.2.2)).comp
      ((hcx1.prodMk hcx2).prodMk (hcy1.prodMk hcy2))
  exact hy1.sub (((measurable_const.sub hu).mul haL).add (hu.mul haR))

lemma measurable_Phi2_swap : Measurable (fun p : Type2 × Type2 => Phi2 p.2 p.1) := by
  unfold Phi2 alpha2
  have hx1 : Measurable (fun p : Type2 × Type2 => p.1.1) := measurable_fst.comp measurable_fst
  have hx2 : Measurable (fun p : Type2 × Type2 => p.1.2) := measurable_snd.comp measurable_fst
  have hy1 : Measurable (fun p : Type2 × Type2 => p.2.1) := measurable_fst.comp measurable_snd
  have hy2 : Measurable (fun p : Type2 × Type2 => p.2.2) := measurable_snd.comp measurable_snd
  have hcx1 : Measurable (fun p : Type2 × Type2 => cell4 p.1.1) := measurable_cell4.comp hx1
  have hcx2 : Measurable (fun p : Type2 × Type2 => cell4 p.1.2) := measurable_cell4.comp hx2
  have hcy1 : Measurable (fun p : Type2 × Type2 => cell4 p.2.1) := measurable_cell4.comp hy1
  have hcy2 : Measurable (fun p : Type2 × Type2 => cell4 p.2.2) := measurable_cell4.comp hy2
  have hcr : Measurable (fun p : Type2 × Type2 => ((cell4 p.2.2 : ℕ) : ℝ)) :=
    (Measurable.of_discrete (f := fun n : ℕ => (n : ℝ))).comp hcy2
  have hv : Measurable (fun p : Type2 × Type2 => 4 * p.2.2 - ((cell4 p.2.2 : ℕ) : ℝ)) :=
    (measurable_const.mul hy2).sub hcr
  have haL : Measurable (fun p : Type2 × Type2 => a2Real (cell4 p.1.1) (cell4 p.1.2) (cell4 p.2.1) (cell4 p.2.2)) :=
    (Measurable.of_discrete (f := fun q : (ℕ × ℕ) × (ℕ × ℕ) => a2Real q.1.1 q.1.2 q.2.1 q.2.2)).comp
      ((hcx1.prodMk hcx2).prodMk (hcy1.prodMk hcy2))
  have haR : Measurable (fun p : Type2 × Type2 => a2Real (cell4 p.1.1) (cell4 p.1.2) (cell4 p.2.1) (cell4 p.2.2 + 1)) :=
    (Measurable.of_discrete (f := fun q : (ℕ × ℕ) × (ℕ × ℕ) => a2Real q.1.1 q.1.2 q.2.1 (q.2.2 + 1))).comp
      ((hcx1.prodMk hcx2).prodMk (hcy1.prodMk hcy2))
  exact hy2.sub (((measurable_const.sub hv).mul haL).add (hv.mul haR))

lemma exists_bound_Phi :
    ∃ C : ℝ, ∀ p ∈ profileDomain, |Phi1 p.1 p.2| ≤ C ∧ |Phi2 p.1 p.2| ≤ C := by
  let B : ℝ := 1 + ∑ si ∈ Finset.range 4, ∑ sj ∈ Finset.range 4,
    (Exists.choose (exists_bound_alpha1 si sj) + Exists.choose (exists_bound_alpha2 si sj))
  refine ⟨B, fun p hp => ?_⟩
  have h1 := (Exists.choose_spec (exists_bound_alpha1 (cell4 p.2.1) (cell4 p.2.2)))
  have h2 := (Exists.choose_spec (exists_bound_alpha2 (cell4 p.2.1) (cell4 p.2.2)))
  have hsi : cell4 p.2.1 ∈ Finset.range 4 := Finset.mem_range.mpr (cell4_lt p.2.1)
  have hsj : cell4 p.2.2 ∈ Finset.range 4 := Finset.mem_range.mpr (cell4_lt p.2.2)
  let gsj : ℕ → ℝ := fun sj' => Exists.choose (exists_bound_alpha1 (cell4 p.2.1) sj') +
      Exists.choose (exists_bound_alpha2 (cell4 p.2.1) sj')
  let gsi : ℕ → ℝ := fun si' => ∑ sj' ∈ Finset.range 4,
      (Exists.choose (exists_bound_alpha1 si' sj') + Exists.choose (exists_bound_alpha2 si' sj'))
  have hle_j : gsj (cell4 p.2.2) ≤ gsi (cell4 p.2.1) :=
    Finset.single_le_sum (f := gsj) (fun sj' _ => add_nonneg
      (Exists.choose_spec (exists_bound_alpha1 (cell4 p.2.1) sj')).1
      (Exists.choose_spec (exists_bound_alpha2 (cell4 p.2.1) sj')).1) hsj
  have hle_i : gsi (cell4 p.2.1) ≤ B - 1 := by
    simp only [B, add_sub_cancel_left]
    exact Finset.single_le_sum (f := gsi) (fun si' _ => Finset.sum_nonneg (fun sj' _ => add_nonneg
      (Exists.choose_spec (exists_bound_alpha1 si' sj')).1
      (Exists.choose_spec (exists_bound_alpha2 si' sj')).1)) hsi
  dsimp only [gsj, gsi] at hle_j hle_i
  have hx1 : |p.1.1| ≤ 1 := by rw [abs_of_nonneg hp.1.1.1]; exact hp.1.1.2
  have hx2 : |p.1.2| ≤ 1 := by rw [abs_of_nonneg hp.1.2.1]; exact hp.1.2.2
  have hb1 := h1.2 p.1 hp.1
  have hb2 := h2.2 p.1 hp.1
  have htri1 := abs_sub p.1.1 (alpha1 (cell4 p.2.1) (cell4 p.2.2) p.1)
  have htri2 := abs_sub p.1.2 (alpha2 (cell4 p.2.1) (cell4 p.2.2) p.1)
  unfold Phi1 Phi2
  constructor <;> linarith [h1.1, h2.1]

noncomputable def H_env (p : Type2 × Type2) : ℝ :=
  max3 0 (Phi1 p.1 p.2) (Phi1 p.2 p.1) + max3 0 (Phi2 p.1 p.2) (Phi2 p.2 p.1)

lemma integrableOn_H_env : IntegrableOn H_env profileDomain volume := by
  obtain ⟨CP, hCP⟩ := exists_bound_Phi
  have hH_m : Measurable H_env :=
    (measurable_max3_real measurable_const measurable_Phi1 measurable_Phi1_swap).add
      (measurable_max3_real measurable_const measurable_Phi2 measurable_Phi2_swap)
  refine integrableOn_bdd_profileDomain (C := 2 * CP) hH_m.aestronglyMeasurable (fun p hp => ?_)
  have hsw : (p.2, p.1) ∈ profileDomain := ⟨hp.2, hp.1⟩
  have b1 := (hCP p hp).1; have b2 := (hCP p hp).2
  have b3 := (hCP (p.2, p.1) hsw).1; have b4 := (hCP (p.2, p.1) hsw).2
  have hCP0 : 0 ≤ CP := le_trans (abs_nonneg _) b1
  unfold H_env max3
  have hm1 : |max (0 : ℝ) (max (Phi1 p.1 p.2) (Phi1 p.2 p.1))| ≤ CP := by
    rw [abs_of_nonneg (le_max_left _ _)]
    exact max_le hCP0 (max_le (le_trans (le_abs_self _) b1) (le_trans (le_abs_self _) b3))
  have hm2 : |max (0 : ℝ) (max (Phi2 p.1 p.2) (Phi2 p.2 p.1))| ≤ CP := by
    rw [abs_of_nonneg (le_max_left _ _)]
    exact max_le hCP0 (max_le (le_trans (le_abs_self _) b2) (le_trans (le_abs_self _) b4))
  linarith [abs_add_le (max (0 : ℝ) (max (Phi1 p.1 p.2) (Phi1 p.2 p.1)))
    (max (0 : ℝ) (max (Phi2 p.1 p.2) (Phi2 p.2 p.1)))]

lemma integrableOn_Phi_q1 {M : Mechanism} (hFeas : IsFeasible M) :
    IntegrableOn (fun p : Type2 × Type2 => Phi1 p.1 p.2 * M.q11 p.1 p.2) profileDomain volume ∧
    IntegrableOn (fun p : Type2 × Type2 => Phi2 p.1 p.2 * M.q12 p.1 p.2) profileDomain volume := by
  obtain ⟨CP, hCP⟩ := exists_bound_Phi
  constructor
  · exact integrableOn_bdd_profileDomain (measurable_Phi1.aestronglyMeasurable.mul hFeas.2.1.aestronglyMeasurable)
      (fun p hp => by
        rw [abs_mul, abs_of_nonneg (hFeas.1 p.1 hp.1 p.2 hp.2).1]
        have hq1 : M.q11 p.1 p.2 ≤ 1 := by linarith [(hFeas.1 p.1 hp.1 p.2 hp.2).2.1, (hFeas.1 p.1 hp.1 p.2 hp.2).2.2.1]
        nlinarith [(hCP p hp).1, abs_nonneg (Phi1 p.1 p.2), (hFeas.1 p.1 hp.1 p.2 hp.2).1])
  · exact integrableOn_bdd_profileDomain (measurable_Phi2.aestronglyMeasurable.mul hFeas.2.2.1.aestronglyMeasurable)
      (fun p hp => by
        rw [abs_mul, abs_of_nonneg (hFeas.1 p.1 hp.1 p.2 hp.2).2.2.2.1]
        have hq1 : M.q12 p.1 p.2 ≤ 1 := by linarith [(hFeas.1 p.1 hp.1 p.2 hp.2).2.2.2.2.1, (hFeas.1 p.1 hp.1 p.2 hp.2).2.2.2.2.2]
        nlinarith [(hCP p hp).2, abs_nonneg (Phi2 p.1 p.2), (hFeas.1 p.1 hp.1 p.2 hp.2).2.2.2.1])

lemma integrableOn_Phi_q2 {M : Mechanism} (hFeas : IsFeasible M) :
    IntegrableOn (fun p : Type2 × Type2 => Phi1 p.2 p.1 * M.q21 p.1 p.2) profileDomain volume ∧
    IntegrableOn (fun p : Type2 × Type2 => Phi2 p.2 p.1 * M.q22 p.1 p.2) profileDomain volume := by
  obtain ⟨CP, hCP⟩ := exists_bound_Phi
  have hm1 : Measurable (fun p : Type2 × Type2 => Phi1 p.2 p.1) := measurable_Phi1_swap
  have hm2 : Measurable (fun p : Type2 × Type2 => Phi2 p.2 p.1) := measurable_Phi2_swap
  constructor
  · exact integrableOn_bdd_profileDomain (hm1.aestronglyMeasurable.mul hFeas.2.2.2.1.aestronglyMeasurable)
      (fun p hp => by
        have hswap : (p.2, p.1) ∈ profileDomain := ⟨hp.2, hp.1⟩
        rw [abs_mul, abs_of_nonneg (hFeas.1 p.1 hp.1 p.2 hp.2).2.1]
        have hq1 : M.q21 p.1 p.2 ≤ 1 := by linarith [(hFeas.1 p.1 hp.1 p.2 hp.2).1, (hFeas.1 p.1 hp.1 p.2 hp.2).2.2.1]
        nlinarith [(hCP (p.2, p.1) hswap).1, abs_nonneg (Phi1 p.2 p.1), (hFeas.1 p.1 hp.1 p.2 hp.2).2.1])
  · exact integrableOn_bdd_profileDomain (hm2.aestronglyMeasurable.mul hFeas.2.2.2.2.1.aestronglyMeasurable)
      (fun p hp => by
        have hswap : (p.2, p.1) ∈ profileDomain := ⟨hp.2, hp.1⟩
        rw [abs_mul, abs_of_nonneg (hFeas.1 p.1 hp.1 p.2 hp.2).2.2.2.2.1]
        have hq1 : M.q22 p.1 p.2 ≤ 1 := by linarith [(hFeas.1 p.1 hp.1 p.2 hp.2).2.2.2.1, (hFeas.1 p.1 hp.1 p.2 hp.2).2.2.2.2.2]
        nlinarith [(hCP (p.2, p.1) hswap).2, abs_nonneg (Phi2 p.2 p.1), (hFeas.1 p.1 hp.1 p.2 hp.2).2.2.2.2.1])

lemma dsic_t1_integral_le {M : Mechanism}
    (hFeas : IsFeasible M) (hDSIC : IsDSIC M) (hIR : IsExPostIR M) :
    ∫ p in profileDomain, M.t1 p.1 p.2 ≤
      ∫ p in profileDomain, (Phi1 p.1 p.2 * M.q11 p.1 p.2 + Phi2 p.1 p.2 * M.q12 p.1 p.2) := by
  obtain ⟨hP1q11_int, hP2q12_int⟩ := integrableOn_Phi_q1 hFeas
  have hrhs_p : IntegrableOn (fun p : Type2 × Type2 => Phi1 p.1 p.2 * M.q11 p.1 p.2 + Phi2 p.1 p.2 * M.q12 p.1 p.2)
      profileDomain volume := Integrable.add hP1q11_int hP2q12_int
  have ht1_p := hFeas.2.2.2.2.2.1
  have hq11_p := hFeas.2.1
  have hq12_p := hFeas.2.2.1
  unfold profileDomain at ht1_p hrhs_p hq11_p hq12_p ⊢
  rw [setIntegral_prod_symm_eq ht1_p, setIntegral_prod_symm_eq hrhs_p]
  have hae1 := ae_integrableOn_prod_left hq11_p
  have hae2 := ae_integrableOn_prod_left hq12_p
  have hae3 := ae_integrableOn_prod_left ht1_p
  have hae_y : ∀ᵐ y ∂(volume.restrict unitSquare), y ∈ unitSquare := ae_restrict_mem measurableSet_unitSquare
  have hlhs_out : IntegrableOn (fun y => ∫ x in unitSquare, M.t1 x y) unitSquare volume := by
    unfold IntegrableOn at ht1_p ⊢
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at ht1_p
    exact (Measure.measurePreserving_swap.integrable_comp_of_integrable ht1_p).integral_prod_left
  have hrhs_out : IntegrableOn (fun y => ∫ x in unitSquare, (Phi1 x y * M.q11 x y + Phi2 x y * M.q12 x y))
      unitSquare volume := by
    unfold IntegrableOn at hrhs_p ⊢
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at hrhs_p
    exact (Measure.measurePreserving_swap.integrable_comp_of_integrable hrhs_p).integral_prod_left
  apply integral_mono_ae hlhs_out hrhs_out
  filter_upwards [hae1, hae2, hae3, hae_y] with y h1 h2 h3 hy
  exact u1_slice_bound hFeas hDSIC hIR hy h1 h2 h3

lemma dsic_t2_integral_le {M : Mechanism}
    (hFeas : IsFeasible M) (hDSIC : IsDSIC M) (hIR : IsExPostIR M) :
    ∫ p in profileDomain, M.t2 p.1 p.2 ≤
      ∫ p in profileDomain, (Phi1 p.2 p.1 * M.q21 p.1 p.2 + Phi2 p.2 p.1 * M.q22 p.1 p.2) := by
  obtain ⟨hP1q21_int, hP2q22_int⟩ := integrableOn_Phi_q2 hFeas
  have hrhs_p : IntegrableOn (fun p : Type2 × Type2 => Phi1 p.2 p.1 * M.q21 p.1 p.2 + Phi2 p.2 p.1 * M.q22 p.1 p.2)
      profileDomain volume := Integrable.add hP1q21_int hP2q22_int
  have hq11_p := hFeas.2.1
  have hq12_p := hFeas.2.2.1
  have hq21_p := hFeas.2.2.2.1
  have hq22_p := hFeas.2.2.2.2.1
  have ht1_p := hFeas.2.2.2.2.2.1
  have ht2_p := hFeas.2.2.2.2.2.2
  let Ms := swapMech M
  have hFs : IsFeasible Ms := by
    have hsw : ∀ (f : Type2 × Type2 → ℝ), IntegrableOn f profileDomain volume →
        IntegrableOn (fun p => f (p.2, p.1)) profileDomain volume := by
      intro f hf; unfold IntegrableOn profileDomain at hf ⊢
      rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at hf ⊢
      exact Measure.measurePreserving_swap.integrable_comp_of_integrable hf
    refine ⟨?_, hsw _ hq21_p, hsw _ hq22_p, hsw _ hq11_p, hsw _ hq12_p, hsw _ ht2_p, hsw _ ht1_p⟩
    intro x hx y hy; have hf := hFeas.1 y hy x hx
    dsimp only [Ms, swapMech]
    exact ⟨hf.2.1, hf.1, by linarith [hf.2.2.1], hf.2.2.2.2.1, hf.2.2.2.1, by linarith [hf.2.2.2.2.2]⟩
  have hDs : IsDSIC Ms :=
    ⟨fun x hx x' hx' y hy => hDSIC.2 y hy x hx x' hx',
     fun x hx y hy y' hy' => hDSIC.1 y hy y' hy' x hx⟩
  have hIRs : IsExPostIR Ms := fun x hx y hy => ⟨(hIR y hy x hx).2, (hIR y hy x hx).1⟩
  unfold profileDomain at ht2_p hrhs_p hq21_p hq22_p ⊢
  rw [setIntegral_prod_eq ht2_p, setIntegral_prod_eq hrhs_p]
  have hae1 := ae_integrableOn_prod_right hq21_p
  have hae2 := ae_integrableOn_prod_right hq22_p
  have hae3 := ae_integrableOn_prod_right ht2_p
  have hae_x : ∀ᵐ x ∂(volume.restrict unitSquare), x ∈ unitSquare := ae_restrict_mem measurableSet_unitSquare
  have hlhs_out : IntegrableOn (fun x => ∫ y in unitSquare, M.t2 x y) unitSquare volume := by
    unfold IntegrableOn at ht2_p ⊢
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at ht2_p
    exact ht2_p.integral_prod_left
  have hrhs_out : IntegrableOn (fun x => ∫ y in unitSquare, (Phi1 y x * M.q21 x y + Phi2 y x * M.q22 x y))
      unitSquare volume := by
    unfold IntegrableOn at hrhs_p ⊢
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at hrhs_p
    exact hrhs_p.integral_prod_left
  apply integral_mono_ae hlhs_out hrhs_out
  filter_upwards [hae1, hae2, hae3, hae_x] with x h1 h2 h3 hx
  exact u1_slice_bound hFs hDs hIRs hx h1 h2 h3

lemma dsic_revenue_le_envelope {M : Mechanism}
    (hFeas : IsFeasible M) (hDSIC : IsDSIC M) (hIR : IsExPostIR M) :
    ExpectedRevenue M ≤ ∫ p in profileDomain, H_env p := by
  obtain ⟨hP1q11_int, hP2q12_int⟩ := integrableOn_Phi_q1 hFeas
  obtain ⟨hP1q21_int, hP2q22_int⟩ := integrableOn_Phi_q2 hFeas
  have h1_int : IntegrableOn (fun p : Type2 × Type2 => Phi1 p.1 p.2 * M.q11 p.1 p.2 + Phi2 p.1 p.2 * M.q12 p.1 p.2)
      profileDomain volume := Integrable.add hP1q11_int hP2q12_int
  have h2_int : IntegrableOn (fun p : Type2 × Type2 => Phi1 p.2 p.1 * M.q21 p.1 p.2 + Phi2 p.2 p.1 * M.q22 p.1 p.2)
      profileDomain volume := Integrable.add hP1q21_int hP2q22_int
  have hsum_p : IntegrableOn
      (fun p : Type2 × Type2 => (Phi1 p.1 p.2 * M.q11 p.1 p.2 + Phi2 p.1 p.2 * M.q12 p.1 p.2) +
        (Phi1 p.2 p.1 * M.q21 p.1 p.2 + Phi2 p.2 p.1 * M.q22 p.1 p.2))
      profileDomain volume := Integrable.add h1_int h2_int
  unfold ExpectedRevenue
  rw [integral_add hFeas.2.2.2.2.2.1 hFeas.2.2.2.2.2.2]
  calc (∫ p in profileDomain, M.t1 p.1 p.2) + (∫ p in profileDomain, M.t2 p.1 p.2)
      ≤ (∫ p in profileDomain, (Phi1 p.1 p.2 * M.q11 p.1 p.2 + Phi2 p.1 p.2 * M.q12 p.1 p.2)) +
        (∫ p in profileDomain, (Phi1 p.2 p.1 * M.q21 p.1 p.2 + Phi2 p.2 p.1 * M.q22 p.1 p.2)) :=
        add_le_add (dsic_t1_integral_le hFeas hDSIC hIR) (dsic_t2_integral_le hFeas hDSIC hIR)
    _ = ∫ p in profileDomain,
          ((Phi1 p.1 p.2 * M.q11 p.1 p.2 + Phi2 p.1 p.2 * M.q12 p.1 p.2) +
           (Phi1 p.2 p.1 * M.q21 p.1 p.2 + Phi2 p.2 p.1 * M.q22 p.1 p.2)) :=
        (integral_add h1_int h2_int).symm
    _ ≤ ∫ p in profileDomain, H_env p := by
        apply setIntegral_mono_on hsum_p integrableOn_H_env measurableSet_profileDomain
        intro p hp
        have hf := hFeas.1 p.1 hp.1 p.2 hp.2
        unfold H_env max3
        have hm10 : (0 : ℝ) ≤ max (0 : ℝ) (max (Phi1 p.1 p.2) (Phi1 p.2 p.1)) := le_max_left _ _
        have hm1a : Phi1 p.1 p.2 ≤ max (0 : ℝ) (max (Phi1 p.1 p.2) (Phi1 p.2 p.1)) := le_max_of_le_right (le_max_left _ _)
        have hm1b : Phi1 p.2 p.1 ≤ max (0 : ℝ) (max (Phi1 p.1 p.2) (Phi1 p.2 p.1)) := le_max_of_le_right (le_max_right _ _)
        have hm20 : (0 : ℝ) ≤ max (0 : ℝ) (max (Phi2 p.1 p.2) (Phi2 p.2 p.1)) := le_max_left _ _
        have hm2a : Phi2 p.1 p.2 ≤ max (0 : ℝ) (max (Phi2 p.1 p.2) (Phi2 p.2 p.1)) := le_max_of_le_right (le_max_left _ _)
        have hm2b : Phi2 p.2 p.1 ≤ max (0 : ℝ) (max (Phi2 p.1 p.2) (Phi2 p.2 p.1)) := le_max_of_le_right (le_max_right _ _)
        have hq1_rem : 0 ≤ 1 - M.q11 p.1 p.2 - M.q21 p.1 p.2 := by linarith [hf.2.2.1]
        have hq2_rem : 0 ≤ 1 - M.q12 p.1 p.2 - M.q22 p.1 p.2 := by linarith [hf.2.2.2.2.2]
        have hi1 : Phi1 p.1 p.2 * M.q11 p.1 p.2 + Phi1 p.2 p.1 * M.q21 p.1 p.2 ≤
            max (0 : ℝ) (max (Phi1 p.1 p.2) (Phi1 p.2 p.1)) := by
          have c1 := mul_le_mul_of_nonneg_right hm1a hf.1
          have c2 := mul_le_mul_of_nonneg_right hm1b hf.2.1
          have c3 := mul_nonneg hm10 hq1_rem
          nlinarith
        have hi2 : Phi2 p.1 p.2 * M.q12 p.1 p.2 + Phi2 p.2 p.1 * M.q22 p.1 p.2 ≤
            max (0 : ℝ) (max (Phi2 p.1 p.2) (Phi2 p.2 p.1)) := by
          have c1 := mul_le_mul_of_nonneg_right hm2a hf.2.2.2.1
          have c2 := mul_le_mul_of_nonneg_right hm2b hf.2.2.2.2.1
          have c3 := mul_nonneg hm20 hq2_rem
          nlinarith
        linarith

/-! ### Section 6: Evaluating the 4D Bilinear Trapezoidal Bound to `2324277 / 2621440` -/

lemma sub4_partition_2d {F : ℝ × ℝ → ℝ} (i1 i2 : ℕ)
    (hF : Continuous F) :
    ∫ z in Icc ((i1 : ℝ) / 4) (((i1 + 1 : ℕ) : ℝ) / 4) ×ˢ
           Icc ((i2 : ℝ) / 4) (((i2 + 1 : ℕ) : ℝ) / 4), F z =
      ∑ u1 ∈ Finset.range 4, ∑ u2 ∈ Finset.range 4,
        ∫ z in Icc ((i1 : ℝ) / 4 + (u1 : ℝ) / 16) ((i1 : ℝ) / 4 + (u1 : ℝ) / 16 + 1 / 16) ×ˢ
               Icc ((i2 : ℝ) / 4 + (u2 : ℝ) / 16) ((i2 : ℝ) / 4 + (u2 : ℝ) / 16 + 1 / 16), F z := by
  let q1 : ℕ → ℝ := fun u => (i1 : ℝ) / 4 + (u : ℝ) / 16
  let q2 : ℕ → ℝ := fun u => (i2 : ℝ) / 4 + (u : ℝ) / 16
  have hq1_0 : q1 0 = (i1 : ℝ) / 4 := by simp [q1]
  have hq1_4 : q1 4 = ((i1 + 1 : ℕ) : ℝ) / 4 := by simp only [q1]; push_cast; ring
  have hq2_0 : q2 0 = (i2 : ℝ) / 4 := by simp [q2]
  have hq2_4 : q2 4 = ((i2 + 1 : ℕ) : ℝ) / 4 := by simp only [q2]; push_cast; ring
  have hq1_m : ∀ u < 4, q1 u ≤ q1 (u + 1) := by intro u _; simp [q1]; linarith
  have hq2_m : ∀ u < 4, q2 u ≤ q2 (u + 1) := by intro u _; simp [q2]; linarith
  have hF_box : IntegrableOn F (Icc (q1 0) (q1 4) ×ˢ Icc (q2 0) (q2 4)) volume :=
    hF.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  rw [← hq1_0, ← hq1_4, ← hq2_0, ← hq2_4, setIntegral_prod_eq hF_box]
  have hout : IntegrableOn (fun t => ∫ s in Icc (q2 0) (q2 4), F (t, s)) (Icc (q1 0) (q1 4)) volume := by
    unfold IntegrableOn at hF_box ⊢
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at hF_box
    exact hF_box.integral_prod_left
  rw [setIntegral_Icc_partition 4 q1 _ hq1_m hout]
  apply Finset.sum_congr rfl; intro u1 hu1
  have hinner_eq : ∀ t : ℝ, ∫ s in Icc (q2 0) (q2 4), F (t, s) =
      ∑ u2 ∈ Finset.range 4, ∫ s in Icc (q2 u2) (q2 (u2 + 1)), F (t, s) := by
    intro t
    have ht_int : IntegrableOn (fun s => F (t, s)) (Icc (q2 0) (q2 4)) volume :=
      (hF.comp (continuous_const.prodMk continuous_id)).continuousOn.integrableOn_Icc
    exact setIntegral_Icc_partition 4 q2 (fun s => F (t, s)) hq2_m ht_int
  simp_rw [hinner_eq]
  have hu2_int : ∀ u2 ∈ Finset.range 4, IntegrableOn
      (fun t => ∫ s in Icc (q2 u2) (q2 (u2 + 1)), F (t, s)) (Icc (q1 u1) (q1 (u1 + 1))) volume := by
    intro u2 _
    have hsub_box : IntegrableOn F (Icc (q1 u1) (q1 (u1 + 1)) ×ˢ Icc (q2 u2) (q2 (u2 + 1))) volume :=
      hF.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
    unfold IntegrableOn at hsub_box ⊢
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at hsub_box
    exact hsub_box.integral_prod_left
  rw [setIntegral_finset_sum' (Finset.range 4) hu2_int]
  apply Finset.sum_congr rfl; intro u2 _
  have hsub_box : IntegrableOn F (Icc (q1 u1) (q1 (u1 + 1)) ×ˢ Icc (q2 u2) (q2 (u2 + 1))) volume :=
    hF.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  rw [← setIntegral_prod_eq hsub_box]
  have hs1 : q1 (u1 + 1) = q1 u1 + 1 / 16 := by simp only [q1]; push_cast; ring
  have hs2 : q2 (u2 + 1) = q2 u2 + 1 / 16 := by simp only [q2]; push_cast; ring
  rw [hs1, hs2]
  simp only [q1, q2, Nat.cast_zero, zero_div, add_zero]

lemma envelope_cell_bound {i1 j1 i2 j2 : ℕ}
    (hi1 : i1 ∈ Finset.range 4) (hj1 : j1 ∈ Finset.range 4)
    (hi2 : i2 ∈ Finset.range 4) (hj2 : j2 ∈ Finset.range 4) :
    let p4 : ℕ → ℝ := fun i => (i : ℝ) / 4
    (∫ x1 in Ioo (p4 i1) (p4 (i1 + 1)), ∫ x2 in Ioo (p4 j1) (p4 (j1 + 1)),
      ∫ y1 in Ioo (p4 i2) (p4 (i2 + 1)), ∫ y2 in Ioo (p4 j2) (p4 (j2 + 1)),
        H_env ((x1, x2), (y1, y2))) ≤
      (dualCellSum i1 j1 i2 j2 : ℝ) / 125829120 := by
  intro p4
  have hi1_4 : i1 < 4 := Finset.mem_range.mp hi1
  have hj1_4 : j1 < 4 := Finset.mem_range.mp hj1
  have hi2_4 : i2 < 4 := Finset.mem_range.mp hi2
  have hj2_4 : j2 < 4 := Finset.mem_range.mp hj2
  -- Affine formulas on cell (i1, j1, i2, j2):
  let a1L_x : ℝ := a1Real i2 j2 i1 j1
  let a1R_x : ℝ := a1Real i2 j2 (i1 + 1) j1
  let c0_1 : ℝ := (((i1 : ℝ) + 1) * a1L_x - (i1 : ℝ) * a1R_x) - a1L_x - (i1 : ℝ) * a1L_x + (i1 : ℝ) * a1L_x
  -- Let's define f1(x1), g1(y1), f2(x2), g2(y2) cleanly as c0 + c1 * x1!
  let c1_x : ℝ := 1 + 4 * (a1L_x - a1R_x)
  let c0_x : ℝ := -((1 + (i1 : ℝ) * 4) * a1L_x - (i1 : ℝ) * 4 * a1R_x) -- wait: check!
  -- Even cleaner: write (1 - (4 * x1 - i1)) * a1L_x + (4 * x1 - i1) * a1R_x = ((1 + i1) * a1L_x - i1 * a1R_x) + 4 * (a1R_x - a1L_x) * x1!
  let C0_1 : ℝ := -(((1 + (i1 : ℝ)) * a1L_x - (i1 : ℝ) * a1R_x))
  let C1_1 : ℝ := 1 - 4 * (a1R_x - a1L_x)
  let a1L_y : ℝ := a1Real i1 j1 i2 j2
  let a1R_y : ℝ := a1Real i1 j1 (i2 + 1) j2
  let D0_1 : ℝ := -(((1 + (i2 : ℝ)) * a1L_y - (i2 : ℝ) * a1R_y))
  let D1_1 : ℝ := 1 - 4 * (a1R_y - a1L_y)

  let a2L_x : ℝ := a2Real i2 j2 i1 j1
  let a2R_x : ℝ := a2Real i2 j2 i1 (j1 + 1)
  let C0_2 : ℝ := -(((1 + (j1 : ℝ)) * a2L_x - (j1 : ℝ) * a2R_x))
  let C1_2 : ℝ := 1 - 4 * (a2R_x - a2L_x)
  let a2L_y : ℝ := a2Real i1 j1 i2 j2
  let a2R_y : ℝ := a2Real i1 j1 i2 (j2 + 1)
  let D0_2 : ℝ := -(((1 + (j2 : ℝ)) * a2L_y - (j2 : ℝ) * a2R_y))
  let D1_2 : ℝ := 1 - 4 * (a2R_y - a2L_y)

  let φ1 : ℝ × ℝ → ℝ := fun z => max3 0 (C0_1 + C1_1 * z.1) (D0_1 + D1_1 * z.2)
  let φ2 : ℝ × ℝ → ℝ := fun z => max3 0 (C0_2 + C1_2 * z.1) (D0_2 + D1_2 * z.2)
  have hφ1_cont : Continuous φ1 := by unfold φ1 max3; fun_prop
  have hφ2_cont : Continuous φ2 := by unfold φ2 max3; fun_prop

  -- On the 4 open intervals, H((x1, x2), (y1, y2)) = φ1 (x1, y1) + φ2 (x2, y2) IDENTICALLY!
  have hH_cell : ∀ x1 ∈ Ioo (p4 i1) (p4 (i1 + 1)), ∀ x2 ∈ Ioo (p4 j1) (p4 (j1 + 1)),
      ∀ y1 ∈ Ioo (p4 i2) (p4 (i2 + 1)), ∀ y2 ∈ Ioo (p4 j2) (p4 (j2 + 1)),
        H_env ((x1, x2), (y1, y2)) = φ1 (x1, y1) + φ2 (x2, y2) := by
    intro x1 hx1 x2 hx2 y1 hy1 y2 hy2
    have cx1 := cell4_eq_of_Ioo hi1_4 hx1.1 hx1.2
    have cx2 := cell4_eq_of_Ioo hj1_4 hx2.1 hx2.2
    have cy1 := cell4_eq_of_Ioo hi2_4 hy1.1 hy1.2
    have cy2 := cell4_eq_of_Ioo hj2_4 hy2.1 hy2.2
    dsimp only [H_env, Phi1, Phi2, alpha1, alpha2, φ1, φ2]
    rw [cx1, cx2, cy1, cy2]
    congr 1
    · congr 1
      · simp only [C0_1, C1_1, a1L_x, a1R_x]; ring
      · simp only [D0_1, D1_1, a1L_y, a1R_y]; ring
    · congr 1
      · simp only [C0_2, C1_2, a2L_x, a2R_x]; ring
      · simp only [D0_2, D1_2, a2L_y, a2R_y]; ring
  -- Evaluate the 4 iterated open integrals of φ1 (x1, y1) + φ2 (x2, y2) explicitly!
  have hlen : ∀ k : ℕ, p4 k ≤ p4 (k + 1) ∧ p4 (k + 1) - p4 k = 1 / 4 := by
    intro k; simp only [p4]; push_cast; constructor <;> linarith
  have heval_4d :
      (∫ x1 in Ioo (p4 i1) (p4 (i1 + 1)), ∫ x2 in Ioo (p4 j1) (p4 (j1 + 1)),
        ∫ y1 in Ioo (p4 i2) (p4 (i2 + 1)), ∫ y2 in Ioo (p4 j2) (p4 (j2 + 1)),
          H_env ((x1, x2), (y1, y2))) =
      (1 / 16 : ℝ) *
        ((∫ z in Icc (p4 i1) (p4 (i1 + 1)) ×ˢ Icc (p4 i2) (p4 (i2 + 1)), φ1 z) +
         (∫ z in Icc (p4 j1) (p4 (j1 + 1)) ×ˢ Icc (p4 j2) (p4 (j2 + 1)), φ2 z)) := by
    have step_y2 : ∀ x1 ∈ Ioo (p4 i1) (p4 (i1 + 1)), ∀ x2 ∈ Ioo (p4 j1) (p4 (j1 + 1)),
        ∀ y1 ∈ Ioo (p4 i2) (p4 (i2 + 1)),
        (∫ y2 in Ioo (p4 j2) (p4 (j2 + 1)), H_env ((x1, x2), (y1, y2))) =
          (1 / 4 : ℝ) * φ1 (x1, y1) + ∫ y2 in Icc (p4 j2) (p4 (j2 + 1)), φ2 (x2, y2) := by
      intro x1 hx1 x2 hx2 y1 hy1
      rw [setIntegral_congr_fun measurableSet_Ioo (fun y2 hy2 => hH_cell x1 hx1 x2 hx2 y1 hy1 y2 hy2),
        ← integral_Ioc_eq_integral_Ioo, ← integral_Icc_eq_integral_Ioc]
      have h1i : IntegrableOn (fun _ : ℝ => φ1 (x1, y1)) (Icc (p4 j2) (p4 (j2 + 1))) volume :=
        ContinuousOn.integrableOn_Icc continuousOn_const
      have h2i : IntegrableOn (fun y2 : ℝ => φ2 (x2, y2)) (Icc (p4 j2) (p4 (j2 + 1))) volume :=
        (hφ2_cont.comp (continuous_const.prodMk continuous_id)).continuousOn.integrableOn_Icc
      rw [integral_add h1i h2i, setIntegral_Icc_const (hlen j2).1, (hlen j2).2]
    have step_y1 : ∀ x1 ∈ Ioo (p4 i1) (p4 (i1 + 1)), ∀ x2 ∈ Ioo (p4 j1) (p4 (j1 + 1)),
        (∫ y1 in Ioo (p4 i2) (p4 (i2 + 1)), ∫ y2 in Ioo (p4 j2) (p4 (j2 + 1)), H_env ((x1, x2), (y1, y2))) =
          (1 / 4 : ℝ) * (∫ y1 in Icc (p4 i2) (p4 (i2 + 1)), φ1 (x1, y1)) +
          (1 / 4 : ℝ) * (∫ y2 in Icc (p4 j2) (p4 (j2 + 1)), φ2 (x2, y2)) := by
      intro x1 hx1 x2 hx2
      rw [setIntegral_congr_fun measurableSet_Ioo (fun y1 hy1 => step_y2 x1 hx1 x2 hx2 y1 hy1),
        ← integral_Ioc_eq_integral_Ioo, ← integral_Icc_eq_integral_Ioc]
      have h1i : IntegrableOn (fun y1 : ℝ => (1 / 4 : ℝ) * φ1 (x1, y1)) (Icc (p4 i2) (p4 (i2 + 1))) volume :=
        ((hφ1_cont.comp (continuous_const.prodMk continuous_id)).continuousOn.integrableOn_Icc).const_mul _
      have h2i : IntegrableOn (fun _ : ℝ => ∫ y2 in Icc (p4 j2) (p4 (j2 + 1)), φ2 (x2, y2))
          (Icc (p4 i2) (p4 (i2 + 1))) volume :=
        ContinuousOn.integrableOn_Icc continuousOn_const
      rw [integral_add h1i h2i, integral_const_mul, setIntegral_Icc_const (hlen i2).1, (hlen i2).2]
    have step_x2 : ∀ x1 ∈ Ioo (p4 i1) (p4 (i1 + 1)),
        (∫ x2 in Ioo (p4 j1) (p4 (j1 + 1)), ∫ y1 in Ioo (p4 i2) (p4 (i2 + 1)),
          ∫ y2 in Ioo (p4 j2) (p4 (j2 + 1)), H_env ((x1, x2), (y1, y2))) =
          (1 / 16 : ℝ) * (∫ y1 in Icc (p4 i2) (p4 (i2 + 1)), φ1 (x1, y1)) +
          (1 / 4 : ℝ) * (∫ z in Icc (p4 j1) (p4 (j1 + 1)) ×ˢ Icc (p4 j2) (p4 (j2 + 1)), φ2 z) := by
      intro x1 hx1
      rw [setIntegral_congr_fun measurableSet_Ioo (fun x2 hx2 => step_y1 x1 hx1 x2 hx2),
        ← integral_Ioc_eq_integral_Ioo, ← integral_Icc_eq_integral_Ioc]
      have hφ2_box : IntegrableOn φ2 (Icc (p4 j1) (p4 (j1 + 1)) ×ˢ Icc (p4 j2) (p4 (j2 + 1))) volume :=
        hφ2_cont.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
      have hφ2_out : IntegrableOn (fun x2 => ∫ y2 in Icc (p4 j2) (p4 (j2 + 1)), φ2 (x2, y2))
          (Icc (p4 j1) (p4 (j1 + 1))) volume := by
        unfold IntegrableOn at hφ2_box ⊢
        rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at hφ2_box
        exact hφ2_box.integral_prod_left
      have h1i : IntegrableOn (fun _ : ℝ => (1 / 4 : ℝ) * ∫ y1 in Icc (p4 i2) (p4 (i2 + 1)), φ1 (x1, y1))
          (Icc (p4 j1) (p4 (j1 + 1))) volume := ContinuousOn.integrableOn_Icc continuousOn_const
      rw [integral_add h1i (hφ2_out.const_mul _), setIntegral_Icc_const (hlen j1).1, (hlen j1).2,
        integral_const_mul, ← setIntegral_prod_eq hφ2_box]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioo step_x2,
      ← integral_Ioc_eq_integral_Ioo, ← integral_Icc_eq_integral_Ioc]
    have hφ1_box : IntegrableOn φ1 (Icc (p4 i1) (p4 (i1 + 1)) ×ˢ Icc (p4 i2) (p4 (i2 + 1))) volume :=
      hφ1_cont.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
    have hφ1_out : IntegrableOn (fun x1 => ∫ y1 in Icc (p4 i2) (p4 (i2 + 1)), φ1 (x1, y1))
        (Icc (p4 i1) (p4 (i1 + 1))) volume := by
      unfold IntegrableOn at hφ1_box ⊢
      rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at hφ1_box
      exact hφ1_box.integral_prod_left
    have h2i : IntegrableOn
        (fun _ : ℝ => (1 / 4 : ℝ) * ∫ z in Icc (p4 j1) (p4 (j1 + 1)) ×ˢ Icc (p4 j2) (p4 (j2 + 1)), φ2 z)
        (Icc (p4 i1) (p4 (i1 + 1))) volume := ContinuousOn.integrableOn_Icc continuousOn_const
    rw [integral_add (hφ1_out.const_mul _) h2i, integral_const_mul, ← setIntegral_prod_eq hφ1_box,
      setIntegral_Icc_const (hlen i1).1, (hlen i1).2]
    ring
  rw [heval_4d]
  simp only [p4]
  rw [sub4_partition_2d i1 i2 hφ1_cont, sub4_partition_2d j1 j2 hφ2_cont]
  -- Point evaluation identities matching phi1Scaled and phi2Scaled!
  let v1 := fun u1 u2 => max3Int 0 (phi1Scaled i1 j1 u1 i2 j2) (phi1Scaled i2 j2 u2 i1 j1)
  let v2 := fun u1 u2 => max3Int 0 (phi2Scaled i1 j1 u1 i2 j2) (phi2Scaled i2 j2 u2 i1 j1)
  have hv1_eq : ∀ u1 u2 : ℕ, u1 ≤ 4 → u2 ≤ 4 →
      φ1 ((i1 : ℝ) / 4 + (u1 : ℝ) / 16, (i2 : ℝ) / 4 + (u2 : ℝ) / 16) = (v1 u1 u2 : ℝ) / 7680 := by
    intro u1 u2 hu1 hu2
    have hsub1 : ((4 - u1 : ℕ) : ℝ) = 4 - (u1 : ℝ) := Nat.cast_sub hu1
    have hsub2 : ((4 - u2 : ℕ) : ℝ) = 4 - (u2 : ℝ) := Nat.cast_sub hu2
    dsimp only [v1]
    rw [max3_cast, ← max3_div]
    dsimp only [φ1]
    congr 1
    · norm_num
    · unfold phi1Scaled; simp only [Int.ofNat_eq_natCast]; push_cast; rw [hsub1]
      simp only [C0_1, C1_1, a1L_x, a1R_x]; unfold a1Real; ring
    · unfold phi1Scaled; simp only [Int.ofNat_eq_natCast]; push_cast; rw [hsub2]
      simp only [D0_1, D1_1, a1L_y, a1R_y]; unfold a1Real; ring
  have hv2_eq : ∀ u1 u2 : ℕ, u1 ≤ 4 → u2 ≤ 4 →
      φ2 ((j1 : ℝ) / 4 + (u1 : ℝ) / 16, (j2 : ℝ) / 4 + (u2 : ℝ) / 16) = (v2 u1 u2 : ℝ) / 7680 := by
    intro u1 u2 hu1 hu2
    have hsub1 : ((4 - u1 : ℕ) : ℝ) = 4 - (u1 : ℝ) := Nat.cast_sub hu1
    have hsub2 : ((4 - u2 : ℕ) : ℝ) = 4 - (u2 : ℝ) := Nat.cast_sub hu2
    dsimp only [v2]
    rw [max3_cast, ← max3_div]
    dsimp only [φ2]
    congr 1
    · norm_num
    · unfold phi2Scaled; simp only [Int.ofNat_eq_natCast]; push_cast; rw [hsub1]
      simp only [C0_2, C1_2, a2L_x, a2R_x]; unfold a2Real; ring
    · unfold phi2Scaled; simp only [Int.ofNat_eq_natCast]; push_cast; rw [hsub2]
      simp only [D0_2, D1_2, a2L_y, a2R_y]; unfold a2Real; ring
  have hb_φ1 : (∑ u1 ∈ Finset.range 4, ∑ u2 ∈ Finset.range 4,
      ∫ z in Icc ((i1 : ℝ) / 4 + (u1 : ℝ) / 16) ((i1 : ℝ) / 4 + (u1 : ℝ) / 16 + 1 / 16) ×ˢ
             Icc ((i2 : ℝ) / 4 + (u2 : ℝ) / 16) ((i2 : ℝ) / 4 + (u2 : ℝ) / 16 + 1 / 16), φ1 z) ≤
      ∑ u1 ∈ Finset.range 4, ∑ u2 ∈ Finset.range 4,
        (1 / 1024 : ℝ) * (((v1 u1 u2 : ℝ) + (v1 u1 (u2 + 1) : ℝ) +
          (v1 (u1 + 1) u2 : ℝ) + (v1 (u1 + 1) (u2 + 1) : ℝ)) / 7680) := by
    apply Finset.sum_le_sum; intro u1 hu1
    apply Finset.sum_le_sum; intro u2 hu2
    have hu1_4 : u1 < 4 := Finset.mem_range.mp hu1
    have hu2_4 : u2 < 4 := Finset.mem_range.mp hu2
    have hsq := setIntegral_subsquare_max3_le C0_1 C1_1 D0_1 D1_1
      ((i1 : ℝ) / 4 + (u1 : ℝ) / 16) ((i2 : ℝ) / 4 + (u2 : ℝ) / 16)
    have hs1 : (i1 : ℝ) / 4 + (u1 : ℝ) / 16 + 1 / 16 = (i1 : ℝ) / 4 + ((u1 + 1 : ℕ) : ℝ) / 16 := by push_cast; ring
    have hs2 : (i2 : ℝ) / 4 + (u2 : ℝ) / 16 + 1 / 16 = (i2 : ℝ) / 4 + ((u2 + 1 : ℕ) : ℝ) / 16 := by push_cast; ring
    change ∫ p in _, φ1 p ≤ _ at hsq
    calc _ ≤ (1 / 1024 : ℝ) *
          (φ1 ((i1 : ℝ) / 4 + (u1 : ℝ) / 16, (i2 : ℝ) / 4 + (u2 : ℝ) / 16) +
           φ1 ((i1 : ℝ) / 4 + (u1 : ℝ) / 16, (i2 : ℝ) / 4 + (u2 : ℝ) / 16 + 1 / 16) +
           φ1 ((i1 : ℝ) / 4 + (u1 : ℝ) / 16 + 1 / 16, (i2 : ℝ) / 4 + (u2 : ℝ) / 16) +
           φ1 ((i1 : ℝ) / 4 + (u1 : ℝ) / 16 + 1 / 16, (i2 : ℝ) / 4 + (u2 : ℝ) / 16 + 1 / 16)) := hsq
      _ = _ := by
        rw [hs1, hs2, hv1_eq u1 u2 (by omega) (by omega), hv1_eq u1 (u2 + 1) (by omega) (by omega),
          hv1_eq (u1 + 1) u2 (by omega) (by omega), hv1_eq (u1 + 1) (u2 + 1) (by omega) (by omega)]
        ring
  have hb_φ2 : (∑ u1 ∈ Finset.range 4, ∑ u2 ∈ Finset.range 4,
      ∫ z in Icc ((j1 : ℝ) / 4 + (u1 : ℝ) / 16) ((j1 : ℝ) / 4 + (u1 : ℝ) / 16 + 1 / 16) ×ˢ
             Icc ((j2 : ℝ) / 4 + (u2 : ℝ) / 16) ((j2 : ℝ) / 4 + (u2 : ℝ) / 16 + 1 / 16), φ2 z) ≤
      ∑ u1 ∈ Finset.range 4, ∑ u2 ∈ Finset.range 4,
        (1 / 1024 : ℝ) * (((v2 u1 u2 : ℝ) + (v2 u1 (u2 + 1) : ℝ) +
          (v2 (u1 + 1) u2 : ℝ) + (v2 (u1 + 1) (u2 + 1) : ℝ)) / 7680) := by
    apply Finset.sum_le_sum; intro u1 hu1
    apply Finset.sum_le_sum; intro u2 hu2
    have hu1_4 : u1 < 4 := Finset.mem_range.mp hu1
    have hu2_4 : u2 < 4 := Finset.mem_range.mp hu2
    have hsq := setIntegral_subsquare_max3_le C0_2 C1_2 D0_2 D1_2
      ((j1 : ℝ) / 4 + (u1 : ℝ) / 16) ((j2 : ℝ) / 4 + (u2 : ℝ) / 16)
    have hs1 : (j1 : ℝ) / 4 + (u1 : ℝ) / 16 + 1 / 16 = (j1 : ℝ) / 4 + ((u1 + 1 : ℕ) : ℝ) / 16 := by push_cast; ring
    have hs2 : (j2 : ℝ) / 4 + (u2 : ℝ) / 16 + 1 / 16 = (j2 : ℝ) / 4 + ((u2 + 1 : ℕ) : ℝ) / 16 := by push_cast; ring
    change ∫ p in _, φ2 p ≤ _ at hsq
    calc _ ≤ (1 / 1024 : ℝ) *
          (φ2 ((j1 : ℝ) / 4 + (u1 : ℝ) / 16, (j2 : ℝ) / 4 + (u2 : ℝ) / 16) +
           φ2 ((j1 : ℝ) / 4 + (u1 : ℝ) / 16, (j2 : ℝ) / 4 + (u2 : ℝ) / 16 + 1 / 16) +
           φ2 ((j1 : ℝ) / 4 + (u1 : ℝ) / 16 + 1 / 16, (j2 : ℝ) / 4 + (u2 : ℝ) / 16) +
           φ2 ((j1 : ℝ) / 4 + (u1 : ℝ) / 16 + 1 / 16, (j2 : ℝ) / 4 + (u2 : ℝ) / 16 + 1 / 16)) := hsq
      _ = _ := by
        rw [hs1, hs2, hv2_eq u1 u2 (by omega) (by omega), hv2_eq u1 (u2 + 1) (by omega) (by omega),
          hv2_eq (u1 + 1) u2 (by omega) (by omega), hv2_eq (u1 + 1) (u2 + 1) (by omega) (by omega)]
        ring
  have hcell_eq : (1 / 16 : ℝ) *
      ((∑ u1 ∈ Finset.range 4, ∑ u2 ∈ Finset.range 4,
          (1 / 1024 : ℝ) * (((v1 u1 u2 : ℝ) + (v1 u1 (u2 + 1) : ℝ) +
            (v1 (u1 + 1) u2 : ℝ) + (v1 (u1 + 1) (u2 + 1) : ℝ)) / 7680)) +
       (∑ u1 ∈ Finset.range 4, ∑ u2 ∈ Finset.range 4,
          (1 / 1024 : ℝ) * (((v2 u1 u2 : ℝ) + (v2 u1 (u2 + 1) : ℝ) +
            (v2 (u1 + 1) u2 : ℝ) + (v2 (u1 + 1) (u2 + 1) : ℝ)) / 7680))) =
      (dualCellSum i1 j1 i2 j2 : ℝ) / 125829120 := by
    rw [← Finset.sum_add_distrib]
    have hcomb : ∀ u1 ∈ Finset.range 4,
        (∑ u2 ∈ Finset.range 4,
          (1 / 1024 : ℝ) * (((v1 u1 u2 : ℝ) + (v1 u1 (u2 + 1) : ℝ) +
            (v1 (u1 + 1) u2 : ℝ) + (v1 (u1 + 1) (u2 + 1) : ℝ)) / 7680)) +
        (∑ u2 ∈ Finset.range 4,
          (1 / 1024 : ℝ) * (((v2 u1 u2 : ℝ) + (v2 u1 (u2 + 1) : ℝ) +
            (v2 (u1 + 1) u2 : ℝ) + (v2 (u1 + 1) (u2 + 1) : ℝ)) / 7680)) =
        ((range4Sum fun u2 =>
          (v1 u1 u2 + v1 u1 (u2 + 1) + v1 (u1 + 1) u2 + v1 (u1 + 1) (u2 + 1)) +
          (v2 u1 u2 + v2 u1 (u2 + 1) + v2 (u1 + 1) u2 + v2 (u1 + 1) (u2 + 1)) : Int) : ℝ) / 7864320 := by
      intro u1 _
      rw [← Finset.sum_add_distrib, ← sum_range4_cast, Finset.sum_div]
      apply Finset.sum_congr rfl; intro u2 _
      push_cast; ring
    rw [Finset.sum_congr rfl hcomb, ← Finset.sum_div, sum_range4_cast]
    change (1 / 16 : ℝ) * ((dualCellSum i1 j1 i2 j2 : ℝ) / 7864320) = _
    ring
  linarith

lemma envelope_integral_le :
    ∫ p in profileDomain, H_env p ≤ 2324277 / 2621440 := by
  let H := H_env
  have hH_int : IntegrableOn H profileDomain volume := integrableOn_H_env
  let p4 : ℕ → ℝ := fun i => (i : ℝ) / 4
  have hp4_0 : p4 0 = 0 := by simp [p4]
  have hp4_4 : p4 4 = 1 := by norm_num [p4]
  have hp4_m : ∀ i < 4, p4 i ≤ p4 (i + 1) := by intro i _; simp only [p4]; push_cast; linarith
  have hsub4 : ∀ i < 4, Icc (p4 i) (p4 (i + 1)) ⊆ Icc (0 : ℝ) 1 := by
    intro i hi; refine Icc_subset_Icc (by simp [p4]; positivity) ?_
    have hle : ((i + 1 : ℕ) : ℝ) ≤ 4 := by exact_mod_cast (show i + 1 ≤ 4 by omega)
    simp only [p4]; linarith
  -- Helper: partition any integrable 2D function on unitSquare into 4x4 open squares!
  have hpart_unit : ∀ (G : Type2 → ℝ), IntegrableOn G unitSquare volume →
      ∫ z in unitSquare, G z = ∑ i ∈ Finset.range 4, ∑ j ∈ Finset.range 4,
        ∫ z1 in Ioo (p4 i) (p4 (i + 1)), ∫ z2 in Ioo (p4 j) (p4 (j + 1)), G (z1, z2) := by
    intro G hG
    unfold unitSquare at hG ⊢
    rw [setIntegral_prod_eq hG]
    have hG_out : IntegrableOn (fun z1 => ∫ z2 in Icc (0 : ℝ) 1, G (z1, z2)) (Icc (0 : ℝ) 1) volume := by
      unfold IntegrableOn at hG ⊢
      rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at hG
      exact hG.integral_prod_left
    have hp_out := setIntegral_Icc_partition 4 p4 (fun z1 => ∫ z2 in Icc (0 : ℝ) 1, G (z1, z2))
      hp4_m (by simpa [hp4_0, hp4_4] using hG_out)
    simp only [hp4_0, hp4_4] at hp_out
    rw [hp_out]
    have hae_G := ae_integrableOn_prod_right hG
    apply Finset.sum_congr rfl; intro i hi
    have hi4 : i < 4 := Finset.mem_range.mp hi
    rw [integral_Icc_eq_integral_Ioc, integral_Ioc_eq_integral_Ioo]
    have hae_Gi := ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Icc_self.trans (hsub4 i hi4)) hae_G
    have hae_eq : (fun z1 => ∫ z2 in Icc (0 : ℝ) 1, G (z1, z2)) =ᵐ[volume.restrict (Ioo (p4 i) (p4 (i + 1)))]
        (fun z1 => ∑ j ∈ Finset.range 4, ∫ z2 in Ioo (p4 j) (p4 (j + 1)), G (z1, z2)) := by
      filter_upwards [hae_Gi] with z1 hz1
      have hp_in := setIntegral_Icc_partition 4 p4 (fun z2 => G (z1, z2))
        hp4_m (by simpa [hp4_0, hp4_4] using hz1)
      simp only [hp4_0, hp4_4] at hp_in
      rw [hp_in]
      apply Finset.sum_congr rfl; intro j _
      rw [integral_Icc_eq_integral_Ioc, integral_Ioc_eq_integral_Ioo]
    rw [integral_congr_ae hae_eq]
    have hj_int : ∀ j ∈ Finset.range 4, IntegrableOn
        (fun z1 => ∫ z2 in Ioo (p4 j) (p4 (j + 1)), G (z1, z2))
        (Ioo (p4 i) (p4 (i + 1))) volume := by
      intro j hj
      have hj4 : j < 4 := Finset.mem_range.mp hj
      have hG_box := (hG.mono_set (prod_mono (hsub4 i hi4) (hsub4 j hj4))).mono_set
        (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
      unfold IntegrableOn at hG_box ⊢
      rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at hG_box
      exact hG_box.integral_prod_left
    exact setIntegral_finset_sum' (Finset.range 4) hj_int
  -- Decompose 4D integral into 16 x 16 cells (i1, j1, i2, j2):
  change ∫ p in profileDomain, H p ≤ _
  have h4d : ∫ p in profileDomain, H p =
      ∑ i1 ∈ Finset.range 4, ∑ j1 ∈ Finset.range 4,
        ∑ i2 ∈ Finset.range 4, ∑ j2 ∈ Finset.range 4,
          ∫ x1 in Ioo (p4 i1) (p4 (i1 + 1)), ∫ x2 in Ioo (p4 j1) (p4 (j1 + 1)),
            ∫ y1 in Ioo (p4 i2) (p4 (i2 + 1)), ∫ y2 in Ioo (p4 j2) (p4 (j2 + 1)),
              H ((x1, x2), (y1, y2)) := by
    unfold profileDomain at hH_int ⊢
    rw [setIntegral_prod_eq hH_int]
    have hH_out : IntegrableOn (fun x => ∫ y in unitSquare, H (x, y)) unitSquare volume := by
      unfold IntegrableOn at hH_int ⊢
      rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at hH_int
      exact hH_int.integral_prod_left
    rw [hpart_unit _ hH_out]
    have hae_H := ae_integrableOn_prod_right hH_int
    apply Finset.sum_congr rfl; intro i1 hi1
    apply Finset.sum_congr rfl; intro j1 hj1
    have hi1_4 : i1 < 4 := Finset.mem_range.mp hi1
    have hj1_4 : j1 < 4 := Finset.mem_range.mp hj1
    -- Convert double x1, x2 integral via prod on Ioo x Ioo to apply hae_H!
    have hbox1_sub : Ioo (p4 i1) (p4 (i1 + 1)) ×ˢ Ioo (p4 j1) (p4 (j1 + 1)) ⊆ unitSquare :=
      prod_mono (Ioo_subset_Icc_self.trans (hsub4 i1 hi1_4)) (Ioo_subset_Icc_self.trans (hsub4 j1 hj1_4))
    have hH_box1 := hH_out.mono_set hbox1_sub
    rw [← setIntegral_prod_eq hH_box1]
    have hae_H1 := ae_restrict_of_ae_restrict_of_subset hbox1_sub hae_H
    have hae_eq1 : (fun x => ∫ y in unitSquare, H (x, y)) =ᵐ[volume.restrict (Ioo (p4 i1) (p4 (i1 + 1)) ×ˢ Ioo (p4 j1) (p4 (j1 + 1)))]
        (fun x => ∑ i2 ∈ Finset.range 4, ∑ j2 ∈ Finset.range 4,
          ∫ y1 in Ioo (p4 i2) (p4 (i2 + 1)), ∫ y2 in Ioo (p4 j2) (p4 (j2 + 1)), H (x, (y1, y2))) := by
      filter_upwards [hae_H1] with x hx_int
      exact hpart_unit (fun y => H (x, y)) hx_int
    rw [integral_congr_ae hae_eq1]
    have hcell2_int : ∀ (i2 j2 : ℕ), i2 < 4 → j2 < 4 → IntegrableOn
        (fun x => ∫ y1 in Ioo (p4 i2) (p4 (i2 + 1)), ∫ y2 in Ioo (p4 j2) (p4 (j2 + 1)), H (x, (y1, y2)))
        (Ioo (p4 i1) (p4 (i1 + 1)) ×ˢ Ioo (p4 j1) (p4 (j1 + 1))) volume := by
      intro i2 j2 hi2_4 hj2_4
      have hbox2_sub : Ioo (p4 i2) (p4 (i2 + 1)) ×ˢ Ioo (p4 j2) (p4 (j2 + 1)) ⊆ unitSquare :=
        prod_mono (Ioo_subset_Icc_self.trans (hsub4 i2 hi2_4)) (Ioo_subset_Icc_self.trans (hsub4 j2 hj2_4))
      have h4sub : (Ioo (p4 i1) (p4 (i1 + 1)) ×ˢ Ioo (p4 j1) (p4 (j1 + 1))) ×ˢ
          (Ioo (p4 i2) (p4 (i2 + 1)) ×ˢ Ioo (p4 j2) (p4 (j2 + 1))) ⊆ profileDomain :=
        prod_mono hbox1_sub hbox2_sub
      have hH4 := hH_int.mono_set h4sub
      have hH4_out : IntegrableOn
          (fun x => ∫ y in Ioo (p4 i2) (p4 (i2 + 1)) ×ˢ Ioo (p4 j2) (p4 (j2 + 1)), H (x, y))
          (Ioo (p4 i1) (p4 (i1 + 1)) ×ˢ Ioo (p4 j1) (p4 (j1 + 1))) volume := by
        unfold IntegrableOn at hH4 ⊢
        rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at hH4
        exact hH4.integral_prod_left
      have hae_4 := ae_integrableOn_prod_right hH4
      refine hH4_out.congr ?_
      filter_upwards [hae_4] with x hx_4
      exact setIntegral_prod_eq hx_4
    rw [setIntegral_finset_sum' (Finset.range 4) (fun i2 hi2 =>
      integrableOn_finset_sum' (Finset.range 4) (fun j2 hj2 =>
        hcell2_int i2 j2 (Finset.mem_range.mp hi2) (Finset.mem_range.mp hj2)))]
    apply Finset.sum_congr rfl; intro i2 hi2
    rw [setIntegral_finset_sum' (Finset.range 4) (fun j2 hj2 =>
      hcell2_int i2 j2 (Finset.mem_range.mp hi2) (Finset.mem_range.mp hj2))]
    apply Finset.sum_congr rfl; intro j2 hj2
    exact setIntegral_prod_eq (hcell2_int i2 j2 (Finset.mem_range.mp hi2) (Finset.mem_range.mp hj2))
  rw [h4d]
  calc (∑ i1 ∈ Finset.range 4, ∑ j1 ∈ Finset.range 4,
          ∑ i2 ∈ Finset.range 4, ∑ j2 ∈ Finset.range 4,
            ∫ x1 in Ioo (p4 i1) (p4 (i1 + 1)), ∫ x2 in Ioo (p4 j1) (p4 (j1 + 1)),
              ∫ y1 in Ioo (p4 i2) (p4 (i2 + 1)), ∫ y2 in Ioo (p4 j2) (p4 (j2 + 1)),
                H ((x1, x2), (y1, y2)))
      ≤ ∑ i1 ∈ Finset.range 4, ∑ j1 ∈ Finset.range 4,
          ∑ i2 ∈ Finset.range 4, ∑ j2 ∈ Finset.range 4,
            (dualCellSum i1 j1 i2 j2 : ℝ) / 125829120 := by
        apply Finset.sum_le_sum; intro i1 hi1
        apply Finset.sum_le_sum; intro j1 hj1
        apply Finset.sum_le_sum; intro i2 hi2
        apply Finset.sum_le_sum; intro j2 hj2
        exact envelope_cell_bound hi1 hj1 hi2 hj2
    _ = (dualTotalSum : ℝ) / 125829120 := by
        unfold dualTotalSum
        simp_rw [← Finset.sum_div, sum_range4_cast]
    _ = 2324277 / 2621440 := by
        rw [dualTotalSum_eq]
        norm_num

theorem dsic_expectedRevenue_le (M : Mechanism)
    (hFeas : IsFeasible M) (hDSIC : IsDSIC M) (hIR : IsExPostIR M) :
    ExpectedRevenue M ≤ 2324277 / 2621440 :=
  le_trans (dsic_revenue_le_envelope hFeas hDSIC hIR) envelope_integral_le

end AuctionSep.DSICBound
