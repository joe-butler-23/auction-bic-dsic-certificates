import AuctionSep.Problem
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open MeasureTheory Set

namespace AuctionSep.MeasureLemmas

lemma measurableSet_unitSquare : MeasurableSet unitSquare :=
  measurableSet_Icc.prod measurableSet_Icc

lemma measurableSet_profileDomain : MeasurableSet profileDomain :=
  measurableSet_unitSquare.prod measurableSet_unitSquare

lemma volume_Icc_zero_one : volume (Icc (0 : ℝ) 1) = 1 := by
  rw [Real.volume_Icc]
  norm_num

lemma volume_unitSquare : volume unitSquare = 1 := by
  unfold unitSquare
  rw [Measure.volume_eq_prod, Measure.prod_prod, volume_Icc_zero_one, one_mul]

lemma volume_real_unitSquare : volume.real unitSquare = 1 := by
  simp [Measure.real, volume_unitSquare]

lemma volume_profileDomain : volume profileDomain = 1 := by
  unfold profileDomain
  rw [Measure.volume_eq_prod, Measure.prod_prod, volume_unitSquare, one_mul]

lemma volume_real_profileDomain : volume.real profileDomain = 1 := by
  simp [Measure.real, volume_profileDomain]

lemma integrableOn_const_of_subset_unitSquare {s : Set Type2} (hs : s ⊆ unitSquare) (c : ℝ) :
    IntegrableOn (fun _ => c) s volume :=
  integrableOn_const (ne_of_lt (lt_of_le_of_lt (measure_mono hs)
    (by rw [volume_unitSquare]; exact ENNReal.one_lt_top)))

lemma integrableOn_const_of_subset_profileDomain {s : Set (Type2 × Type2)}
    (hs : s ⊆ profileDomain) (c : ℝ) :
    IntegrableOn (fun _ => c) s volume :=
  integrableOn_const (ne_of_lt (lt_of_le_of_lt (measure_mono hs)
    (by rw [volume_profileDomain]; exact ENNReal.one_lt_top)))

lemma integrableOn_finset_sum' {α ι : Type*} [MeasurableSpace α] [DecidableEq ι]
    {μ : Measure α} {s : Set α} (I : Finset ι) {f : ι → α → ℝ}
    (hf : ∀ i ∈ I, IntegrableOn (f i) s μ) :
    IntegrableOn (fun x => ∑ i ∈ I, f i x) s μ := by
  induction I using Finset.induction_on with
  | empty => simp
  | @insert a J ha ih =>
      have ha_int : IntegrableOn (f a) s μ := hf a (Finset.mem_insert_self a J)
      have hJ_int : IntegrableOn (fun x => ∑ i ∈ J, f i x) s μ :=
        ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
      simp only [Finset.sum_insert ha]
      exact Integrable.add ha_int hJ_int

lemma setIntegral_finset_sum' {α ι : Type*} [MeasurableSpace α] [DecidableEq ι]
    {μ : Measure α} {s : Set α} (I : Finset ι) {f : ι → α → ℝ}
    (hf : ∀ i ∈ I, IntegrableOn (f i) s μ) :
    ∫ x in s, (∑ i ∈ I, f i x) ∂μ = ∑ i ∈ I, ∫ x in s, f i x ∂μ := by
  induction I using Finset.induction_on with
  | empty => simp
  | @insert a J ha ih =>
      have ha_int : IntegrableOn (f a) s μ := hf a (Finset.mem_insert_self a J)
      have hJ : ∀ i ∈ J, IntegrableOn (f i) s μ := fun i hi => hf i (Finset.mem_insert_of_mem hi)
      have hJ_int : IntegrableOn (fun x => ∑ i ∈ J, f i x) s μ := integrableOn_finset_sum' J hJ
      simp only [Finset.sum_insert ha]
      rw [integral_add ha_int hJ_int, ih hJ]

lemma setIntegral_Icc_const {a b : ℝ} (hab : a ≤ b) (c : ℝ) :
    ∫ _ in Icc a b, c = (b - a) * c := by
  rw [setIntegral_const, Real.volume_real_Icc, max_eq_left (sub_nonneg.mpr hab), smul_eq_mul]

lemma setIntegral_Icc_id {a b : ℝ} (hab : a ≤ b) :
    ∫ x in Icc a b, x = (b ^ 2 - a ^ 2) / 2 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab, integral_id]

lemma integrableOn_Icc_affine (a b c0 c1 : ℝ) :
    IntegrableOn (fun x : ℝ => c0 + c1 * x) (Icc a b) volume := by
  apply ContinuousOn.integrableOn_Icc
  fun_prop

lemma setIntegral_Icc_affine {a b : ℝ} (hab : a ≤ b) (c0 c1 : ℝ) :
    ∫ x in Icc a b, (c0 + c1 * x) = c0 * (b - a) + c1 * ((b ^ 2 - a ^ 2) / 2) := by
  have h0 : IntegrableOn (fun _ : ℝ => c0) (Icc a b) volume :=
    ContinuousOn.integrableOn_Icc continuousOn_const
  have h1 : IntegrableOn (fun x : ℝ => c1 * x) (Icc a b) volume :=
    ContinuousOn.integrableOn_Icc (continuousOn_const.mul continuousOn_id)
  rw [integral_add h0 h1, setIntegral_Icc_const hab, mul_comm c0, integral_const_mul,
    setIntegral_Icc_id hab]

lemma setIntegral_Icc_split {a b c : ℝ} {f : ℝ → ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (hf : IntegrableOn f (Icc a c) volume) :
    ∫ x in Icc a c, f x = (∫ x in Icc a b, f x) + (∫ x in Icc b c, f x) := by
  rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc]
  rw [← Ioc_union_Ioc_eq_Ioc hab hbc]
  apply setIntegral_union
  · exact Ioc_disjoint_Ioc_of_le le_rfl
  · exact measurableSet_Ioc
  · exact hf.mono_set (Ioc_subset_Icc_self.trans (Icc_subset_Icc_right hbc))
  · exact hf.mono_set (Ioc_subset_Icc_self.trans (Icc_subset_Icc_left hab))

lemma mono_step_le (p : ℕ → ℝ) :
    ∀ m : ℕ, (∀ k < m, p k ≤ p (k + 1)) → p 0 ≤ p m
  | 0, _ => le_rfl
  | m + 1, hm =>
      le_trans (mono_step_le p m (fun k hk => hm k (Nat.lt_succ_of_lt hk)))
        (hm m (Nat.lt_succ_self m))

lemma setIntegral_Icc_partition :
    ∀ (n : ℕ) (p : ℕ → ℝ) (f : ℝ → ℝ),
      (∀ k < n, p k ≤ p (k + 1)) →
      IntegrableOn f (Icc (p 0) (p n)) volume →
      ∫ x in Icc (p 0) (p n), f x =
        ∑ k ∈ Finset.range n, ∫ x in Icc (p k) (p (k + 1)), f x
  | 0, p, f, _, _ => by
      simp [integral_Icc_eq_integral_Ioc]
  | n + 1, p, f, hmono, hf => by
      have hsub : ∀ k < n, p k ≤ p (k + 1) := fun k hk => hmono k (Nat.lt_succ_of_lt hk)
      have h0n : p 0 ≤ p n := mono_step_le p n hsub
      have hnn1 : p n ≤ p (n + 1) := hmono n (Nat.lt_succ_self n)
      have hf_left : IntegrableOn f (Icc (p 0) (p n)) volume :=
        hf.mono_set (Icc_subset_Icc_right hnn1)
      rw [setIntegral_Icc_split h0n hnn1 hf, Finset.sum_range_succ,
        setIntegral_Icc_partition n p f hsub hf_left]

lemma setIntegral_prod_eq {α β : Type*} [MeasureSpace α] [MeasureSpace β]
    [SFinite (volume : Measure α)] [SFinite (volume : Measure β)]
    {s : Set α} {t : Set β} {f : α × β → ℝ}
    (hf : IntegrableOn f (s ×ˢ t) volume) :
    ∫ z in s ×ˢ t, f z = ∫ x in s, ∫ y in t, f (x, y) := by
  rw [Measure.volume_eq_prod] at hf ⊢
  exact setIntegral_prod f hf

lemma setIntegral_prod_symm_eq {α β : Type*} [MeasureSpace α] [MeasureSpace β]
    [SFinite (volume : Measure α)] [SFinite (volume : Measure β)]
    {s : Set α} {t : Set β} {f : α × β → ℝ}
    (hf : IntegrableOn f (s ×ˢ t) volume) :
    ∫ z in s ×ˢ t, f z = ∫ y in t, ∫ x in s, f (x, y) := by
  unfold IntegrableOn at hf
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at hf ⊢
  exact integral_prod_symm f hf

lemma ae_integrableOn_prod_left {α β : Type*} [MeasureSpace α] [MeasureSpace β]
    [SFinite (volume : Measure α)] [SFinite (volume : Measure β)]
    {s : Set α} {t : Set β} {f : α × β → ℝ}
    (hf : IntegrableOn f (s ×ˢ t) volume) :
    ∀ᵐ y ∂(volume.restrict t), IntegrableOn (fun x => f (x, y)) s volume := by
  unfold IntegrableOn at hf ⊢
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at hf
  exact Integrable.prod_left_ae hf

lemma ae_integrableOn_prod_right {α β : Type*} [MeasureSpace α] [MeasureSpace β]
    [SFinite (volume : Measure α)] [SFinite (volume : Measure β)]
    {s : Set α} {t : Set β} {f : α × β → ℝ}
    (hf : IntegrableOn f (s ×ˢ t) volume) :
    ∀ᵐ x ∂(volume.restrict s), IntegrableOn (fun y => f (x, y)) t volume := by
  unfold IntegrableOn at hf ⊢
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at hf
  exact Integrable.prod_right_ae hf

lemma integrableOn_fst_of_prod {α β : Type*} [MeasureSpace α] [MeasureSpace β]
    [SFinite (volume : Measure α)] [SFinite (volume : Measure β)]
    {s : Set α} {t : Set β} {f : α → ℝ}
    (hf : IntegrableOn f s volume) (ht : volume t ≠ ⊤) :
    IntegrableOn (fun z : α × β => f z.1) (s ×ˢ t) volume := by
  have hg : IntegrableOn (fun _ : β => (1 : ℝ)) t volume := integrableOn_const ht
  unfold IntegrableOn at hf hg ⊢
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
  simpa using hf.mul_prod hg

lemma integrableOn_snd_of_prod {α β : Type*} [MeasureSpace α] [MeasureSpace β]
    [SFinite (volume : Measure α)] [SFinite (volume : Measure β)]
    {s : Set α} {t : Set β} {g : β → ℝ}
    (hs : volume s ≠ ⊤) (hg : IntegrableOn g t volume) :
    IntegrableOn (fun z : α × β => g z.2) (s ×ˢ t) volume := by
  have hf : IntegrableOn (fun _ : α => (1 : ℝ)) s volume := integrableOn_const hs
  unfold IntegrableOn at hf hg ⊢
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
  simpa using hf.mul_prod hg

end AuctionSep.MeasureLemmas
