import EconCSAuction.MeasureHelpers
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Monotone
import Mathlib.Topology.Order.IntermediateValue

/-!
# Lemma 2: Closed-Form Difference Law, Unique Root `t₀ ∈ (9/25, 7/16)`, Monotonicity of `Φ_+`, and Positivity of `K`

Proves on `ℝ`:
1. `Iwing(s, t) = (1/2) ln((√(s + t) + √s) / √t)` satisfies `∂_s Iwing = ρ(s + t, s)`,
   `∂_t Iwing = -√s / (4 t √(s + t))`, `∫_0^s ρ(r + t, r) dr = Iwing(s, t)`, and
   `g_T(t) = ∫_0^{1-t} ρ(r + t, r) dr`, `g_T'(t) = -1 / (4 t √(1 - t))`,
   `1 - G_T(t) = ∫_t^1 g_T(x) dx = √(1 - t)/2 - t g_T(t)`.
2. `Φ_+(t) = 2t - √(1 - t) / artanh(√(1 - t))` has a unique root `t₀ ∈ (9/25, 7/16)`
   (equivalently `s₀ = √(1 - t₀) ∈ (3/4, 4/5)`), with `Φ_+ < 0` on `(0, t₀)` and `Φ_+ > 0` on `(t₀, 1)`.
3. `Φ_+'(t) > 0` strictly on `[t₀, 1)`, so `Φ_+` is strictly increasing on `[t₀, 1)`.
4. `K(t) = 2 g_T(t) - 1/(4√(1 - t)) > 0` on `(0, t₀]`, `K(t) < 2 g_T(t)`, and `∫_0^{t₀} K(t) dt = 1/2`.
-/

open MeasureTheory Set Filter Topology

namespace EconCSAuction

noncomputable section

/-- Wing auxiliary integral `I(s, t) = (1/2) ln((√(s + t) + √s) / √t) = (1/2) arsinh(√(s/t))`. -/
def Iwing (s t : ℝ) : ℝ :=
  (1 / 2) * Real.log ((Real.sqrt (s + t) + Real.sqrt s) / Real.sqrt t)

/-! ### 1. Calculus of `artanh` and elementary exponential/log bounds -/

lemma artanh_zero : artanh 0 = 0 := by
  unfold artanh; simp

lemma hasDerivAt_artanh {s : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt artanh (1 / (1 - s ^ 2)) s := by
  have h1 : 0 < 1 + s := by linarith [hs.1]
  have h2 : 0 < 1 - s := by linarith [hs.2]
  have hdiv : 0 < (1 + s) / (1 - s) := div_pos h1 h2
  have hd_num : HasDerivAt (fun x : ℝ => 1 + x) 1 s := by
    simpa using (hasDerivAt_id s).const_add (1 : ℝ)
  have hd_den : HasDerivAt (fun x : ℝ => 1 - x) (-1) s := by
    simpa using (hasDerivAt_id s).const_sub (1 : ℝ)
  have hd_q : HasDerivAt (fun x : ℝ => (1 + x) / (1 - x))
      ((1 * (1 - s) - (1 + s) * (-1)) / (1 - s) ^ 2) s :=
    hd_num.div hd_den h2.ne'
  have hd_log : HasDerivAt (fun x : ℝ => Real.log ((1 + x) / (1 - x)))
      (((1 * (1 - s) - (1 + s) * (-1)) / (1 - s) ^ 2) / ((1 + s) / (1 - s))) s :=
    hd_q.log hdiv.ne'
  have hd : HasDerivAt artanh
      ((1 / 2 : ℝ) * (((1 * (1 - s) - (1 + s) * (-1)) / (1 - s) ^ 2) / ((1 + s) / (1 - s)))) s :=
    hd_log.const_mul (1 / 2 : ℝ)
  refine hd.congr_deriv ?_
  have h1s : 1 - s ^ 2 ≠ 0 := by nlinarith [hs.1, hs.2]
  field_simp [h1.ne', h2.ne', h1s]
  ring

lemma strictMonoOn_artanh : StrictMonoOn artanh (Ioo (-1 : ℝ) 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioo (-1 : ℝ) 1)
  · intro s hs
    exact (hasDerivAt_artanh hs).continuousAt.continuousWithinAt
  · intro s hs
    rw [interior_Ioo] at hs
    rw [(hasDerivAt_artanh hs).deriv]
    have : 0 < 1 - s ^ 2 := by nlinarith [hs.1, hs.2]
    positivity

lemma artanh_gt_self {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) : s < artanh s := by
  let f : ℝ → ℝ := fun x => artanh x - x
  have hmono : StrictMonoOn f (Ico (0 : ℝ) 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Ico (0 : ℝ) 1)
    · intro x hx
      have hx' : x ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hx.1], hx.2⟩
      exact ((hasDerivAt_artanh hx').sub (hasDerivAt_id x)).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ico] at hx
      have hx' : x ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hx.1], hx.2⟩
      have hd : HasDerivAt f (1 / (1 - x ^ 2) - 1) x :=
        (hasDerivAt_artanh hx').sub (hasDerivAt_id x)
      rw [hd.deriv]
      have h1x : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
      have hx2 : 0 < x ^ 2 := sq_pos_of_pos hx.1
      have : 1 / (1 - x ^ 2) - 1 = x ^ 2 / (1 - x ^ 2) := by field_simp [h1x.ne']; ring
      rw [this]
      exact div_pos hx2 h1x
  have hlt := hmono ⟨le_rfl, zero_lt_one⟩ ⟨hs0.le, hs1⟩ hs0
  dsimp [f] at hlt
  rw [artanh_zero, sub_zero] at hlt
  linarith

lemma artanh_pos {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) : 0 < artanh s :=
  hs0.trans (artanh_gt_self hs0 hs1)

lemma artanh_three_fourths_gt : (6 / 7 : ℝ) < artanh (3 / 4) := by
  unfold artanh
  have h7 : (1 + (3 / 4 : ℝ)) / (1 - (3 / 4 : ℝ)) = 7 := by norm_num
  rw [h7]
  have hexp : Real.exp (12 / 7 : ℝ) < 7 := by
    have hpow : Real.exp (12 : ℝ) < (7 : ℝ) ^ 7 := by
      calc Real.exp (12 : ℝ) = (Real.exp 1) ^ 12 := by
            rw [← Real.exp_nat_mul]; norm_num
        _ < (2.72 : ℝ) ^ 12 := by
            gcongr
            linarith [Real.exp_one_lt_d9]
        _ < (7 : ℝ) ^ 7 := by norm_num
    have h7pow : (Real.exp (12 / 7 : ℝ)) ^ 7 < (7 : ℝ) ^ 7 := by
      calc (Real.exp (12 / 7 : ℝ)) ^ 7 = Real.exp (7 * (12 / 7 : ℝ)) := by
            rw [← Real.exp_nat_mul]; norm_num
        _ = Real.exp 12 := by norm_num
        _ < (7 : ℝ) ^ 7 := hpow
    by_contra hle
    push Not at hle
    have : (7 : ℝ) ^ 7 ≤ (Real.exp (12 / 7 : ℝ)) ^ 7 := pow_le_pow_left₀ (by norm_num) hle 7
    linarith
  have hlog : (12 / 7 : ℝ) < Real.log 7 := (Real.lt_log_iff_exp_lt (by norm_num)).mpr hexp
  linarith

lemma artanh_four_fifths_lt : artanh (4 / 5) < 10 / 9 := by
  unfold artanh
  have h9 : (1 + (4 / 5 : ℝ)) / (1 - (4 / 5 : ℝ)) = (3 : ℝ) ^ 2 := by norm_num
  rw [h9, Real.log_pow]
  have hexp : (3 : ℝ) < Real.exp (10 / 9 : ℝ) := by
    have hpow : (3 : ℝ) ^ 9 < Real.exp (10 : ℝ) := by
      calc (3 : ℝ) ^ 9 < (2.718 : ℝ) ^ 10 := by norm_num
        _ < (Real.exp 1) ^ 10 := by
            gcongr
            linarith [Real.exp_one_gt_d9]
        _ = Real.exp 10 := by
            rw [← Real.exp_nat_mul]; norm_num
    have h9pow : (3 : ℝ) ^ 9 < (Real.exp (10 / 9 : ℝ)) ^ 9 := by
      calc (3 : ℝ) ^ 9 < Real.exp 10 := hpow
        _ = Real.exp (9 * (10 / 9 : ℝ)) := by norm_num
        _ = (Real.exp (10 / 9 : ℝ)) ^ 9 := by rw [← Real.exp_nat_mul]; norm_num
    by_contra hle
    push Not at hle
    have : (Real.exp (10 / 9 : ℝ)) ^ 9 ≤ (3 : ℝ) ^ 9 :=
      pow_le_pow_left₀ (Real.exp_pos _).le hle 9
    linarith
  have hlog : Real.log 3 < (10 / 9 : ℝ) := (Real.log_lt_iff_lt_exp (by norm_num)).mpr hexp
  push_cast
  linarith

/-! ### 2. Auxiliary root function `ψ(s) = 2(1 - s²) artanh(s) - s` and unique root `s₀ ∈ (3/4, 4/5)` -/

/-- Auxiliary function `ψ(s) = 2(1 - s²) artanh(s) - s = artanh(s) · Φ_+(1 - s²)`. -/
def psi (s : ℝ) : ℝ := 2 * (1 - s ^ 2) * artanh s - s

lemma psi_zero : psi 0 = 0 := by
  unfold psi; simp [artanh_zero]

lemma hasDerivAt_psi {s : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt psi (1 - 4 * s * artanh s) s := by
  have h1 : 0 < 1 - s ^ 2 := by nlinarith [hs.1, hs.2]
  have hd_poly : HasDerivAt (fun x : ℝ => 2 * (1 - x ^ 2)) (-4 * s) s := by
    have hp : HasDerivAt (fun x : ℝ => 1 - x ^ 2) (-(2 * s)) s := by
      have := (hasDerivAt_pow 2 s).const_sub (1 : ℝ)
      simpa using this
    exact (hp.const_mul (2 : ℝ)).congr_deriv (by ring)
  have hd_prod : HasDerivAt (fun x : ℝ => 2 * (1 - x ^ 2) * artanh x)
      (-4 * s * artanh s + 2 * (1 - s ^ 2) * (1 / (1 - s ^ 2))) s :=
    hd_poly.mul (hasDerivAt_artanh hs)
  have hd : HasDerivAt psi
      ((-4 * s * artanh s + 2 * (1 - s ^ 2) * (1 / (1 - s ^ 2))) - 1) s :=
    hd_prod.sub (hasDerivAt_id s)
  refine hd.congr_deriv ?_
  field_simp [h1.ne']
  ring

lemma strictAntiOn_psiDeriv : StrictAntiOn (fun s => 1 - 4 * s * artanh s) (Ico (0 : ℝ) 1) := by
  intro a ha b hb hab
  have ha' : a ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [ha.1], ha.2⟩
  have hb' : b ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hb.1], hb.2⟩
  have hA : artanh a < artanh b := strictMonoOn_artanh ha' hb' hab
  have hA0 : 0 ≤ artanh a := by
    rcases eq_or_lt_of_le ha.1 with rfl | ha0
    · simp [artanh_zero]
    · exact (artanh_pos ha0 ha.2).le
  have hAb : 0 < artanh b := artanh_pos (ha.1.trans_lt hab) hb.2
  have hmul : a * artanh a < b * artanh b := by
    calc a * artanh a ≤ a * artanh b := mul_le_mul_of_nonneg_left hA.le ha.1
      _ < b * artanh b := mul_lt_mul_of_pos_right hab hAb
  linarith

lemma psi_three_fourths_pos : 0 < psi (3 / 4) := by
  unfold psi
  have h := artanh_three_fourths_gt
  nlinarith

lemma psi_four_fifths_neg : psi (4 / 5) < 0 := by
  unfold psi
  have h := artanh_four_fifths_lt
  nlinarith

lemma continuousOn_psi_Icc {a b : ℝ} (ha : -1 < a) (hb : b < 1) : ContinuousOn psi (Icc a b) := by
  intro s hs
  exact (hasDerivAt_psi ⟨ha.trans_le hs.1, hs.2.trans_lt hb⟩).continuousAt.continuousWithinAt

/-- Strict concavity of `ψ` on `[0, 1)`: if `ψ ≥ 0` at endpoints, `ψ > 0` strictly inside. -/
lemma psi_pos_between {a x b : ℝ} (ha : 0 ≤ a) (hax : a < x) (hxb : x < b) (hb : b < 1)
    (hpa : 0 ≤ psi a) (hpb : 0 ≤ psi b) : 0 < psi x := by
  by_contra hle
  push Not at hle
  obtain ⟨c1, ⟨hc1_a, hc1_x⟩, hfc1⟩ :=
    exists_hasDerivAt_eq_slope psi (fun y => 1 - 4 * y * artanh y) hax
      (continuousOn_psi_Icc (by linarith) (hxb.trans hb))
      (fun y hy => hasDerivAt_psi ⟨by linarith [hy.1], hy.2.trans (hxb.trans hb)⟩)
  obtain ⟨c2, ⟨hc2_x, hc2_b⟩, hfc2⟩ :=
    exists_hasDerivAt_eq_slope psi (fun y => 1 - 4 * y * artanh y) hxb
      (continuousOn_psi_Icc (by linarith) hb)
      (fun y hy => hasDerivAt_psi ⟨by linarith [hy.1], hy.2.trans hb⟩)
  have h1 : (psi x - psi a) / (x - a) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  have h2 : 0 ≤ (psi b - psi x) / (b - x) := div_nonneg (by linarith) (by linarith)
  have hlt := strictAntiOn_psiDeriv ⟨ha.trans hc1_a.le, hc1_x.trans (hxb.trans hb)⟩
    ⟨(ha.trans hax.le).trans hc2_x.le, hc2_b.trans hb⟩ (hc1_x.trans hc2_x)
  linarith

lemma exists_s0_in_bounds : ∃ s ∈ Ioo (3 / 4 : ℝ) (4 / 5), psi s = 0 := by
  obtain ⟨s, hsIcc, hseq⟩ := intermediate_value_Icc' (by norm_num : (3 / 4 : ℝ) ≤ 4 / 5)
    (continuousOn_psi_Icc (by norm_num) (by norm_num))
    ⟨psi_four_fifths_neg.le, psi_three_fourths_pos.le⟩
  refine ⟨s, ⟨lt_of_le_of_ne hsIcc.1 ?_, lt_of_le_of_ne hsIcc.2 ?_⟩, hseq⟩
  · intro h; rw [← h] at hseq; linarith [psi_three_fourths_pos]
  · intro h; rw [h] at hseq; linarith [psi_four_fifths_neg]

lemma existsUnique_s0 : ∃! s ∈ Ioo (0 : ℝ) 1, psi s = 0 := by
  obtain ⟨s, hs, hseq⟩ := exists_s0_in_bounds
  refine ⟨s, ⟨⟨by linarith [hs.1], by linarith [hs.2]⟩, hseq⟩, fun s' ⟨hs', hs'eq⟩ => ?_⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have := psi_pos_between le_rfl hs'.1 hlt (by linarith [hs.2]) psi_zero.ge hseq.ge
    linarith
  · have := psi_pos_between le_rfl (by linarith [hs.1]) hgt hs'.2 psi_zero.ge hs'eq.ge
    linarith

/-- Unique root `s₀ = √(1 - t₀) ∈ (3/4, 4/5)` of `ψ`. -/
def s0 : ℝ := Classical.choose existsUnique_s0

lemma s0_spec : s0 ∈ Ioo (0 : ℝ) 1 ∧ psi s0 = 0 :=
  (Classical.choose_spec existsUnique_s0).1

lemma s0_unique {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) (hpsi : psi s = 0) : s = s0 :=
  (Classical.choose_spec existsUnique_s0).2 s ⟨hs, hpsi⟩

lemma s0_mem_bounds : s0 ∈ Ioo (3 / 4 : ℝ) (4 / 5) := by
  obtain ⟨s, hs, hseq⟩ := exists_s0_in_bounds
  rwa [← s0_unique ⟨by linarith [hs.1], by linarith [hs.2]⟩ hseq]

lemma psi_pos_of_lt_s0 {s : ℝ} (hs0 : 0 < s) (hs : s < s0) : 0 < psi s :=
  psi_pos_between le_rfl hs0 hs s0_spec.1.2 psi_zero.ge s0_spec.2.ge

/-! ### 3. Transfer to `Φ_+(t)` and exact properties of `t₀` -/

lemma PhiPlus_eq_psi_div {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    PhiPlus t = psi (Real.sqrt (1 - t)) / artanh (Real.sqrt (1 - t)) := by
  unfold PhiPlus psi
  have hs0 : 0 < Real.sqrt (1 - t) := Real.sqrt_pos.mpr (by linarith)
  have hs1 : Real.sqrt (1 - t) < 1 := by rw [Real.sqrt_lt' zero_lt_one]; linarith
  have hA : artanh (Real.sqrt (1 - t)) ≠ 0 := (artanh_pos hs0 hs1).ne'
  rw [Real.sq_sqrt (by linarith : 0 ≤ 1 - t)]
  field_simp [hA]; ring

lemma PhiPlus_one_sub_s0_sq : (1 - s0 ^ 2) ∈ Ioo (0 : ℝ) 1 ∧ PhiPlus (1 - s0 ^ 2) = 0 := by
  have hs := s0_spec.1
  have ht0 : 0 < 1 - s0 ^ 2 := by nlinarith [hs.1, hs.2]
  have ht1 : 1 - s0 ^ 2 < 1 := by nlinarith [hs.1, hs.2]
  refine ⟨⟨ht0, ht1⟩, ?_⟩
  rw [PhiPlus_eq_psi_div ht0 ht1, show 1 - (1 - s0 ^ 2) = s0 ^ 2 by ring,
    Real.sqrt_sq hs.1.le, s0_spec.2, zero_div]

lemma existsUnique_t0 : ∃! t ∈ Ioo (0 : ℝ) 1, PhiPlus t = 0 := by
  refine ⟨1 - s0 ^ 2, PhiPlus_one_sub_s0_sq, fun t ⟨⟨ht0, ht1⟩, hphi⟩ => ?_⟩
  rw [PhiPlus_eq_psi_div ht0 ht1] at hphi
  have hs0 : 0 < Real.sqrt (1 - t) := Real.sqrt_pos.mpr (by linarith)
  have hs1 : Real.sqrt (1 - t) < 1 := by rw [Real.sqrt_lt' zero_lt_one]; linarith
  have hpsi0 : psi (Real.sqrt (1 - t)) = 0 :=
    (div_eq_zero_iff.mp hphi).resolve_right (artanh_pos hs0 hs1).ne'
  have hsq := congrArg (· ^ 2) (s0_unique ⟨hs0, hs1⟩ hpsi0)
  rw [Real.sq_sqrt (by linarith : 0 ≤ 1 - t)] at hsq
  linarith

lemma t0_eq_one_sub_s0_sq : t0 = 1 - s0 ^ 2 := by
  have hex : ∃ t : ℝ, t ∈ Ioo (0 : ℝ) 1 ∧ PhiPlus t = 0 := ⟨1 - s0 ^ 2, PhiPlus_one_sub_s0_sq⟩
  have hspec := Classical.epsilon_spec hex
  change t0 ∈ Ioo (0 : ℝ) 1 ∧ PhiPlus t0 = 0 at hspec
  exact existsUnique_t0.unique hspec PhiPlus_one_sub_s0_sq

lemma t0_mem_bounds : t0 ∈ Ioo (9 / 25 : ℝ) (7 / 16) := by
  rw [t0_eq_one_sub_s0_sq]
  have hb := s0_mem_bounds
  exact ⟨by nlinarith [hb.1, hb.2], by nlinarith [hb.1, hb.2]⟩

lemma t0_pos : 0 < t0 := by linarith [t0_mem_bounds.1]
lemma t0_lt_one : t0 < 1 := by linarith [t0_mem_bounds.2]

lemma PhiPlus_t0 : PhiPlus t0 = 0 := by
  rw [t0_eq_one_sub_s0_sq]; exact PhiPlus_one_sub_s0_sq.2

lemma sqrt_one_sub_t0 : Real.sqrt (1 - t0) = s0 := by
  rw [t0_eq_one_sub_s0_sq, show 1 - (1 - s0 ^ 2) = s0 ^ 2 by ring, Real.sqrt_sq s0_spec.1.1.le]

lemma PhiPlus_pos_of_gt_t0 {t : ℝ} (ht : t0 < t) (ht1 : t < 1) : 0 < PhiPlus t := by
  have ht0 : 0 < t := t0_pos.trans ht
  rw [PhiPlus_eq_psi_div ht0 ht1]
  have hs0 : 0 < Real.sqrt (1 - t) := Real.sqrt_pos.mpr (by linarith)
  have hs1 : Real.sqrt (1 - t) < 1 := by rw [Real.sqrt_lt' zero_lt_one]; linarith
  have hlt : Real.sqrt (1 - t) < s0 := by
    rw [← sqrt_one_sub_t0]
    exact Real.sqrt_lt_sqrt (by linarith) (by linarith)
  exact div_pos (psi_pos_of_lt_s0 hs0 hlt) (artanh_pos hs0 hs1)


/-! ### 4. Strict monotonicity of `Φ_+` on `[t₀, 1)` (Lemma 2(3)) -/

/-- Reparameterized virtual difference `h(s) = Φ_+(1 - s²) = 2(1 - s²) - s / artanh(s)`. -/
def hPhi (s : ℝ) : ℝ := 2 * (1 - s ^ 2) - s / artanh s

lemma hasDerivAt_hPhi {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    HasDerivAt hPhi
      ((s / (1 - s ^ 2) - artanh s - 4 * s * (artanh s) ^ 2) / (artanh s) ^ 2) s := by
  have hsIoo : s ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith, hs1⟩
  have hA : artanh s ≠ 0 := (artanh_pos hs0 hs1).ne'
  have h1s : 1 - s ^ 2 ≠ 0 := by nlinarith
  have hd1 : HasDerivAt (fun x : ℝ => 2 * (1 - x ^ 2)) (-4 * s) s := by
    have hp : HasDerivAt (fun x : ℝ => 1 - x ^ 2) (-(2 * s)) s := by
      simpa using (hasDerivAt_pow 2 s).const_sub (1 : ℝ)
    exact (hp.const_mul (2 : ℝ)).congr_deriv (by ring)
  have hd2 : HasDerivAt (fun x : ℝ => x / artanh x)
      ((1 * artanh s - s * (1 / (1 - s ^ 2))) / (artanh s) ^ 2) s :=
    (hasDerivAt_id s).div (hasDerivAt_artanh hsIoo) hA
  have hd : HasDerivAt hPhi
      (-4 * s - (1 * artanh s - s * (1 / (1 - s ^ 2))) / (artanh s) ^ 2) s :=
    hd1.sub hd2
  refine hd.congr_deriv ?_
  field_simp [hA, h1s]
  ring


/-- Zero-numerics derivative sign on `(0, s₀]`: `ψ(s) ≥ 0` gives `s / (1 - s²) ≤ 2 artanh s`,
and `s < artanh s` yields `s³ / (1 - s²) < 2 s (artanh s)² < 4 s (artanh s)²`. -/
lemma deriv_hPhi_neg {s : ℝ} (hs0 : 0 < s) (hs : s ≤ s0) :
    (s / (1 - s ^ 2) - artanh s - 4 * s * (artanh s) ^ 2) / (artanh s) ^ 2 < 0 := by
  have hs1 : s < 1 := hs.trans_lt s0_spec.1.2
  have h1s : 0 < 1 - s ^ 2 := by nlinarith
  have hA_gt : s < artanh s := artanh_gt_self hs0 hs1
  have hA_pos : 0 < artanh s := hs0.trans hA_gt
  have hpsi_nn : 0 ≤ psi s := by
    rcases eq_or_lt_of_le hs with rfl | hlt
    · exact s0_spec.2.ge
    · exact (psi_pos_of_lt_s0 hs0 hlt).le
  have hbound : s / (1 - s ^ 2) ≤ 2 * artanh s := by
    rw [div_le_iff₀ h1s]; unfold psi at hpsi_nn; linarith
  have hcube : s ^ 3 / (1 - s ^ 2) < 4 * s * (artanh s) ^ 2 := by
    have h1 : s ^ 2 * (s / (1 - s ^ 2)) ≤ s ^ 2 * (2 * artanh s) :=
      mul_le_mul_of_nonneg_left hbound (sq_nonneg s)
    have h2 : s ^ 2 * (2 * artanh s) < 2 * s * (artanh s) ^ 2 := by
      nlinarith [mul_pos (mul_pos hs0 hA_pos) (sub_pos.mpr hA_gt)]
    have h3 : s ^ 2 * (s / (1 - s ^ 2)) = s ^ 3 / (1 - s ^ 2) := by ring
    nlinarith [mul_pos hs0 (sq_pos_of_pos hA_pos)]
  have hid : s / (1 - s ^ 2) - s ^ 3 / (1 - s ^ 2) = s := by field_simp [h1s.ne']
  exact div_neg_of_neg_of_pos (by linarith) (sq_pos_of_pos hA_pos)

lemma strictAntiOn_hPhi : StrictAntiOn hPhi (Ioc (0 : ℝ) s0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioc (0 : ℝ) s0)
  · intro s hs
    exact (hasDerivAt_hPhi hs.1 (hs.2.trans_lt s0_spec.1.2)).continuousAt.continuousWithinAt
  · intro s hs
    rw [interior_Ioc] at hs
    rw [(hasDerivAt_hPhi hs.1 (hs.2.trans s0_spec.1.2)).deriv]
    exact deriv_hPhi_neg hs.1 hs.2.le

lemma strictMonoOn_PhiPlus : StrictMonoOn PhiPlus (Ico t0 1) := by
  intro t1 ht1 t2 ht2 h12
  have hPhi_eq : ∀ t ∈ Ico t0 1, PhiPlus t = hPhi (Real.sqrt (1 - t)) := fun t ht => by
    unfold PhiPlus hPhi; rw [Real.sq_sqrt (by linarith [ht.2] : 0 ≤ 1 - t)]; ring
  rw [hPhi_eq t1 ht1, hPhi_eq t2 ht2]
  have hs2_pos : 0 < Real.sqrt (1 - t2) := Real.sqrt_pos.mpr (by linarith [ht2.2])
  have hs1_le : Real.sqrt (1 - t1) ≤ s0 := by
    rw [← sqrt_one_sub_t0]; exact Real.sqrt_le_sqrt (by linarith [ht1.1])
  have hlt : Real.sqrt (1 - t2) < Real.sqrt (1 - t1) :=
    Real.sqrt_lt_sqrt (by linarith [ht2.2]) (by linarith)
  exact strictAntiOn_hPhi ⟨hs2_pos, hlt.le.trans hs1_le⟩ ⟨hs2_pos.trans hlt, hs1_le⟩ hlt


/-! ### 5. Exact formulas for `Iwing`, `g_T`, `tailGT`, and `K` (Lemma 2(1) & 2(4)) -/

lemma Iwing_zero {t : ℝ} (ht : 0 < t) : Iwing 0 t = 0 := by
  unfold Iwing
  have hst : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr ht).ne'
  simp [Real.sqrt_zero, div_self hst]

lemma Iwing_one_sub {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) : Iwing (1 - t) t = gT t := by
  unfold Iwing gT artanh
  have hsub : 1 - t + t = 1 := by ring
  rw [hsub, Real.sqrt_one]
  have hs0 : 0 < Real.sqrt (1 - t) := Real.sqrt_pos.mpr (by linarith)
  have hs1 : Real.sqrt (1 - t) < 1 := by rw [Real.sqrt_lt' zero_lt_one]; linarith
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have hsq : (1 + Real.sqrt (1 - t)) / (1 - Real.sqrt (1 - t)) =
      ((1 + Real.sqrt (1 - t)) / Real.sqrt t) ^ 2 := by
    have hden : 1 - Real.sqrt (1 - t) ≠ 0 := by linarith
    have hdiff : (1 - Real.sqrt (1 - t)) * (1 + Real.sqrt (1 - t)) = t := by
      have := Real.sq_sqrt (by linarith : 0 ≤ 1 - t)
      nlinarith
    rw [div_pow, Real.sq_sqrt ht0.le]
    field_simp [hden, ht0.ne']
    nlinarith
  rw [hsq, Real.log_pow]
  push_cast
  ring

lemma hasDerivAt_Iwing_s {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    HasDerivAt (fun r => Iwing r t) (rho (s + t) s) s := by
  have hst : 0 < s + t := by linarith
  have hsq_s : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have hsq_st : 0 < Real.sqrt (s + t) := Real.sqrt_pos.mpr hst
  have hsq_t : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hsum_pos : 0 < Real.sqrt (s + t) + Real.sqrt s := by linarith
  have hd1 : HasDerivAt (fun r : ℝ => Real.sqrt (r + t)) (1 / (2 * Real.sqrt (s + t))) s := by
    have hadd : HasDerivAt (fun r : ℝ => r + t) 1 s := by
      simpa using (hasDerivAt_id s).add_const t
    exact ((Real.hasDerivAt_sqrt hst.ne').comp s hadd).congr_deriv (by ring)
  have hd2 : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt s)) s := Real.hasDerivAt_sqrt hs.ne'
  have hd_num : HasDerivAt (fun r : ℝ => (Real.sqrt (r + t) + Real.sqrt r) / Real.sqrt t)
      ((1 / (2 * Real.sqrt (s + t)) + 1 / (2 * Real.sqrt s)) / Real.sqrt t) s :=
    (hd1.add hd2).div_const (Real.sqrt t)
  have harg : (Real.sqrt (s + t) + Real.sqrt s) / Real.sqrt t ≠ 0 :=
    (div_pos hsum_pos hsq_t).ne'
  have hd : HasDerivAt (fun r => Iwing r t)
      ((1 / 2 : ℝ) * (((1 / (2 * Real.sqrt (s + t)) + 1 / (2 * Real.sqrt s)) / Real.sqrt t) /
        ((Real.sqrt (s + t) + Real.sqrt s) / Real.sqrt t))) s :=
    (hd_num.log harg).const_mul (1 / 2 : ℝ)
  refine hd.congr_deriv ?_
  unfold rho
  rw [Real.sqrt_mul hst.le]
  field_simp [hsq_s.ne', hsq_st.ne', hsq_t.ne', hsum_pos.ne']
  ring

lemma hasDerivAt_gT {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    HasDerivAt gT (-(1 / (4 * t * Real.sqrt (1 - t)))) t := by
  have h1t : 0 < 1 - t := by linarith
  have hs0 : 0 < Real.sqrt (1 - t) := Real.sqrt_pos.mpr h1t
  have hs1 : Real.sqrt (1 - t) < 1 := by rw [Real.sqrt_lt' zero_lt_one]; linarith
  have hd_sqrt : HasDerivAt (fun x : ℝ => Real.sqrt (1 - x)) (-(1 / (2 * Real.sqrt (1 - t)))) t := by
    have h1 : HasDerivAt (fun x : ℝ => 1 - x) (-1) t := by
      simpa using (hasDerivAt_id t).const_sub (1 : ℝ)
    exact ((Real.hasDerivAt_sqrt h1t.ne').comp t h1).congr_deriv (by ring)
  have hd_A := (hasDerivAt_artanh (s := Real.sqrt (1 - t)) ⟨by linarith, hs1⟩).comp t hd_sqrt
  have hd : HasDerivAt gT _ t := hd_A.const_mul (1 / 2 : ℝ)
  refine hd.congr_deriv ?_
  rw [Real.sq_sqrt h1t.le]
  have hsub : 1 - (1 - t) = t := by ring
  rw [hsub]
  field_simp [ht0.ne', hs0.ne']
  ring

lemma hasDerivAt_tailGT {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    HasDerivAt tailGT (-gT t) t := by
  have h1t : 0 < 1 - t := by linarith
  have hs0 : 0 < Real.sqrt (1 - t) := Real.sqrt_pos.mpr h1t
  have hd1 : HasDerivAt (fun x : ℝ => Real.sqrt (1 - x) / 2)
      (-(1 / (4 * Real.sqrt (1 - t)))) t := by
    have h1 : HasDerivAt (fun x : ℝ => 1 - x) (-1) t := by
      simpa using (hasDerivAt_id t).const_sub (1 : ℝ)
    exact (((Real.hasDerivAt_sqrt h1t.ne').comp t h1).div_const (2 : ℝ)).congr_deriv (by ring)
  have hd2 : HasDerivAt (fun x : ℝ => x * gT x)
      (1 * gT t + t * (-(1 / (4 * t * Real.sqrt (1 - t))))) t :=
    (hasDerivAt_id t).mul (hasDerivAt_gT ht0 ht1)
  have hd : HasDerivAt tailGT _ t := hd1.sub hd2
  refine hd.congr_deriv ?_
  field_simp [ht0.ne', hs0.ne']
  ring

lemma gT_pos {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) : 0 < gT t := by
  unfold gT
  have hs0 : 0 < Real.sqrt (1 - t) := Real.sqrt_pos.mpr (by linarith)
  have hs1 : Real.sqrt (1 - t) < 1 := by rw [Real.sqrt_lt' zero_lt_one]; linarith
  exact mul_pos (by norm_num) (artanh_pos hs0 hs1)

lemma gT_one : gT 1 = 0 := by
  unfold gT; simp [artanh_zero]

lemma tailGT_one : tailGT 1 = 0 := by
  unfold tailGT; simp [gT_one]

lemma integrableOn_rho_diag {s t : ℝ} (hs : 0 ≤ s) (ht : 0 < t) :
    IntegrableOn (fun r => rho (r + t) r) (Ioo (0 : ℝ) s) volume := by
  have hdom : IntegrableOn (fun r : ℝ => (1 / (2 * Real.sqrt t)) * density1D r) (Ioo (0 : ℝ) s) volume := by
    have hd : IntegrableOn density1D (Ioo (0 : ℝ) s) volume := by
      have h1 : IntegrableOn (fun a : ℝ => (1 / 2 : ℝ) * a ^ (-(1 / 2 : ℝ))) (Ioc 0 s) volume :=
        ((intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ)) (b := s) (r := -(1 / 2 : ℝ))
          (by norm_num)).const_mul (1 / 2)).1
      exact (h1.congr_fun (fun a ha => by
        unfold density1D; rw [Real.rpow_neg ha.1.le, ← Real.sqrt_eq_rpow]; ring)
        measurableSet_Ioc).mono_set Ioo_subset_Ioc_self
    exact hd.const_mul _
  have hmeas : Measurable (fun r : ℝ => rho (r + t) r) :=
    measurable_const.div (measurable_const.mul
      (Real.continuous_sqrt.measurable.comp ((measurable_id.add measurable_const).mul measurable_id)))
  refine hdom.mono' hmeas.aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ioo]
  filter_upwards with r hr
  rw [Real.norm_eq_abs, abs_of_nonneg (rho_nonneg _ _)]
  unfold rho density1D
  have hrt : 0 < r + t := by linarith [hr.1]
  rw [Real.sqrt_mul hrt.le]
  have hle : Real.sqrt t ≤ Real.sqrt (r + t) := Real.sqrt_le_sqrt (by linarith [hr.1])
  have hsq_t : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hinv : (Real.sqrt (r + t))⁻¹ ≤ (Real.sqrt t)⁻¹ := inv_anti₀ hsq_t hle
  calc 1 / (4 * (Real.sqrt (r + t) * Real.sqrt r))
      = (1 / (4 * Real.sqrt r)) * (Real.sqrt (r + t))⁻¹ := by ring
    _ ≤ (1 / (4 * Real.sqrt r)) * (Real.sqrt t)⁻¹ :=
        mul_le_mul_of_nonneg_left hinv (by positivity)
    _ = 1 / (2 * Real.sqrt t) * (1 / (2 * Real.sqrt r)) := by ring

/-- Exact improper FTC: `∫ r in (0, s), ρ(r + t, r) = Iwing(s, t)` for `s ≥ 0, t > 0`. -/
lemma integral_rho_eq_Iwing {s t : ℝ} (hs : 0 ≤ s) (ht : 0 < t) :
    ∫ r in Ioo (0 : ℝ) s, rho (r + t) r = Iwing s t := by
  rcases eq_or_lt_of_le hs with rfl | hs0
  · simp [Iwing_zero ht]
  · have hcont : ContinuousOn (fun r => Iwing r t) (Icc (0 : ℝ) s) := by
      unfold Iwing
      refine ContinuousOn.mul continuousOn_const ?_
      refine ContinuousOn.log ?_ ?_
      · refine ContinuousOn.div ?_ continuousOn_const (fun _ _ => (Real.sqrt_pos.mpr ht).ne')
        exact (Real.continuous_sqrt.comp (continuous_id.add continuous_const)).continuousOn.add
          Real.continuous_sqrt.continuousOn
      · intro r hr
        have hpos : 0 < Real.sqrt (r + t) := Real.sqrt_pos.mpr (by linarith [hr.1])
        have hsq : 0 ≤ Real.sqrt r := Real.sqrt_nonneg r
        exact (div_pos (by linarith) (Real.sqrt_pos.mpr ht)).ne'
    have hint : IntervalIntegrable (fun r => rho (r + t) r) volume 0 s := by
      rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hs]
      exact integrableOn_rho_diag hs ht
    rw [setIntegral_congr_set Ioo_ae_eq_Ioc, ← intervalIntegral.integral_of_le hs]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hs hcont
        (fun r hr => hasDerivAt_Iwing_s hr.1 ht) hint,
        Iwing_zero ht, sub_zero]

/-- Exact difference density integral: `∫ r in (0, 1 - t), ρ(r + t, r) = g_T(t)` for `t ∈ (0, 1)`. -/
lemma integral_rho_eq_gT {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    ∫ r in Ioo (0 : ℝ) (1 - t), rho (r + t) r = gT t := by
  rw [integral_rho_eq_Iwing (by linarith) ht0, Iwing_one_sub ht0 ht1]

/-- Elementary upper bound `g_T(t) ≤ 1 / √t = 2 · density1D(t)` on `(0, 1)`. -/
lemma gT_le_inv_sqrt {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    gT t ≤ 1 / Real.sqrt t := by
  rw [← Iwing_one_sub ht0 ht1]
  unfold Iwing
  have hsub : 1 - t + t = 1 := by ring
  rw [hsub, Real.sqrt_one]
  have hsqt : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have hsq1t : Real.sqrt (1 - t) ≤ 1 := by
    calc Real.sqrt (1 - t) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt (by linarith)
      _ = 1 := Real.sqrt_one
  have hpos : 0 < (1 + Real.sqrt (1 - t)) / Real.sqrt t :=
    div_pos (by linarith [Real.sqrt_nonneg (1 - t)]) hsqt
  have hlog := Real.log_le_sub_one_of_pos hpos
  have hfrac : (1 + Real.sqrt (1 - t)) / Real.sqrt t ≤ 2 / Real.sqrt t :=
    div_le_div_of_nonneg_right (by linarith) hsqt.le
  have hhalf : (1 / 2 : ℝ) * (2 / Real.sqrt t) = 1 / Real.sqrt t := by ring
  linarith

lemma measurable_gT : Measurable gT := by
  unfold gT artanh
  fun_prop

lemma integrableOn_gT_Ioo_zero_one : IntegrableOn gT (Ioo (0 : ℝ) 1) volume := by
  have hdom : IntegrableOn (fun t : ℝ => 2 * density1D t) (Ioo (0 : ℝ) 1) volume :=
    integrableOn_density1D_Ioo.const_mul 2
  refine hdom.mono' measurable_gT.aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ioo]
  filter_upwards with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (gT_pos ht.1 ht.2).le]
  calc gT t ≤ 1 / Real.sqrt t := gT_le_inv_sqrt ht.1 ht.2
    _ = 2 * density1D t := by unfold density1D; ring

lemma continuousOn_gT_Ioc {t : ℝ} (ht0 : 0 < t) : ContinuousOn gT (Icc t 1) := by
  unfold gT artanh
  intro x hx
  have hsq_lt : Real.sqrt (1 - x) < 1 := by
    rw [Real.sqrt_lt' zero_lt_one]; linarith [hx.1]
  have hnum : 0 < 1 + Real.sqrt (1 - x) := by linarith [Real.sqrt_nonneg (1 - x)]
  have hden : 0 < 1 - Real.sqrt (1 - x) := by linarith
  have harg : (1 + Real.sqrt (1 - x)) / (1 - Real.sqrt (1 - x)) ≠ 0 := (div_pos hnum hden).ne'
  have hc_sq : ContinuousAt (fun y : ℝ => Real.sqrt (1 - y)) x :=
    Real.continuous_sqrt.continuousAt.comp (continuous_const.sub continuous_id).continuousAt
  have hc_q : ContinuousAt (fun y : ℝ => (1 + Real.sqrt (1 - y)) / (1 - Real.sqrt (1 - y))) x :=
    (continuousAt_const.add hc_sq).div (continuousAt_const.sub hc_sq) hden.ne'
  exact (continuousAt_const.mul (continuousAt_const.mul (hc_q.log harg))).continuousWithinAt

lemma continuousOn_tailGT {t : ℝ} (ht0 : 0 < t) : ContinuousOn tailGT (Icc t 1) := by
  unfold tailGT
  refine ContinuousOn.sub ?_ (continuousOn_id.mul (continuousOn_gT_Ioc ht0))
  exact (Real.continuous_sqrt.comp (continuous_const.sub continuous_id)).continuousOn.div_const 2

/-- Exact tail CDF formula: `∫ x in (t, 1), g_T(x) = tailGT(t) = √(1 - t)/2 - t g_T(t)`. -/
lemma integral_gT_Ioo {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    ∫ x in Ioo t 1, gT x = tailGT t := by
  have hcont : ContinuousOn (fun x => -tailGT x) (Icc t 1) := (continuousOn_tailGT ht0).neg
  have hint : IntervalIntegrable gT volume t 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le ht1]
    exact integrableOn_gT_Ioo_zero_one.mono_set (Ioo_subset_Ioo_left ht0.le)
  have hderiv : ∀ x ∈ Ioo t 1, HasDerivAt (fun y => -tailGT y) (gT x) x := by
    intro x hx
    exact (hasDerivAt_tailGT (ht0.trans hx.1) hx.2).fun_neg.congr_deriv (by ring)
  rw [setIntegral_congr_set Ioo_ae_eq_Ioc, ← intervalIntegral.integral_of_le ht1]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht1 hcont hderiv hint,
      tailGT_one]
  ring

lemma tendsto_mul_gT_zero : Tendsto (fun t : ℝ => t * gT t) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (Real.continuous_sqrt.tendsto 0 |>.mono_left nhdsWithin_le_nhds |>.trans (by rw [Real.sqrt_zero])) ?_ ?_
  · filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with t ht
    exact mul_nonneg ht.1.le (gT_pos ht.1 ht.2).le
  · filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with t ht
    calc t * gT t ≤ t * (1 / Real.sqrt t) := mul_le_mul_of_nonneg_left (gT_le_inv_sqrt ht.1 ht.2) ht.1.le
      _ = Real.sqrt t := by
          have hsq : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr ht.1).ne'
          field_simp [hsq]
          exact (Real.sq_sqrt ht.1.le).symm

lemma strictAntiOn_gT : StrictAntiOn gT (Ioo (0 : ℝ) 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioo (0 : ℝ) 1)
  · intro x hx; exact (hasDerivAt_gT hx.1 hx.2).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioo] at hx
    rw [(hasDerivAt_gT hx.1 hx.2).deriv]
    have hx0 : 0 < x := hx.1
    have hsq : 0 < Real.sqrt (1 - x) := Real.sqrt_pos.mpr (by linarith [hx.2])
    have : 0 < 1 / (4 * x * Real.sqrt (1 - x)) := by positivity
    linarith

lemma tendsto_tailGT_zero : Tendsto tailGT (𝓝[>] (0 : ℝ)) (𝓝 (1 / 2 : ℝ)) := by
  unfold tailGT
  have h1 : Tendsto (fun t : ℝ => Real.sqrt (1 - t) / 2) (𝓝[>] (0 : ℝ)) (𝓝 (1 / 2 : ℝ)) := by
    have hc : ContinuousAt (fun t : ℝ => Real.sqrt (1 - t) / 2) 0 :=
      (Real.continuous_sqrt.comp (continuous_const.sub continuous_id)).continuousAt.div_const 2
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  simpa using h1.sub tendsto_mul_gT_zero

/-- FTC on `(0, b)` when `F` has right limit `F0` at `0⁺` and is continuous on `[c, b]` for every `0 < c`. -/
lemma integral_Ioo_eq_sub_of_tendsto_zero {f F : ℝ → ℝ} {b F0 : ℝ} (hb : 0 < b)
    (hcont : ∀ {c : ℝ}, 0 < c → ContinuousOn F (Icc c b))
    (hlim : Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 F0))
    (hderiv : ∀ x ∈ Ioo (0 : ℝ) b, HasDerivAt F (f x) x)
    (hint : IntegrableOn f (Ioo (0 : ℝ) b) volume) :
    ∫ x in Ioo (0 : ℝ) b, f x = F b - F0 := by
  let G : ℝ → ℝ := fun t => if t = 0 then F0 else F t
  have hG_cont : ContinuousOn G (Icc (0 : ℝ) b) := by
    intro x hx
    by_cases hx0 : x = 0
    · subst hx0
      rw [ContinuousWithinAt, show G 0 = F0 by simp [G]]
      have hlimG : Tendsto G (𝓝[>] (0 : ℝ)) (𝓝 F0) := by
        refine hlim.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with t (ht : (0 : ℝ) < t)
        simp [G, ht.ne']
      rw [Metric.tendsto_nhdsWithin_nhds] at hlimG ⊢
      intro ε hε
      obtain ⟨δ, hδ, hball⟩ := hlimG ε hε
      refine ⟨δ, hδ, fun y hy hdist => ?_⟩
      rcases eq_or_lt_of_le hy.1 with rfl | hypos
      · simpa [G] using hε
      · exact hball hypos hdist
    · have hxpos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hx0)
      have hc : ContinuousWithinAt F (Icc (x / 2) b) x :=
        hcont (by linarith) x ⟨by linarith, hx.2⟩
      have hle_nhds : 𝓝[Icc (0 : ℝ) b] x ≤ 𝓝[Icc (x / 2) b] x := by
        rw [nhdsWithin_le_iff]
        filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds (by linarith : x / 2 < x)),
          self_mem_nhdsWithin] with t ht1 ht2
        exact ⟨ht1.le, ht2.2⟩
      have hev : F =ᶠ[𝓝[Icc (0 : ℝ) b] x] G := by
        filter_upwards [nhdsWithin_le_nhds (lt_mem_nhds hxpos)] with t ht
        simp [G, ht.ne']
      rw [ContinuousWithinAt, show G x = F x by simp [G, hx0]]
      exact (hc.mono_left hle_nhds).congr' hev
  have hG_deriv : ∀ x ∈ Ioo (0 : ℝ) b, HasDerivAt G (f x) x := by
    intro x hx
    refine (hderiv x hx).congr_of_eventuallyEq ?_
    filter_upwards [lt_mem_nhds hx.1] with t ht
    simp [G, ht.ne']
  have hint' : IntervalIntegrable f volume 0 b :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hb.le).mpr hint
  rw [setIntegral_congr_set Ioo_ae_eq_Ioc, ← intervalIntegral.integral_of_le hb.le,
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hb.le hG_cont hG_deriv hint']
  simp [G, hb.ne']

/-- Total mass of `g_T` on `(0, 1)` equals `1 / 2` (since `t = a - b` is symmetric around `0`). -/
lemma integral_gT_zero_one : ∫ x in Ioo (0 : ℝ) 1, gT x = 1 / 2 := by
  have h := integral_Ioo_eq_sub_of_tendsto_zero (F := fun t => -tailGT t) (F0 := -(1 / 2 : ℝ))
    zero_lt_one (fun hc => (continuousOn_tailGT hc).neg) tendsto_tailGT_zero.neg
    (fun x hx => (hasDerivAt_tailGT hx.1 hx.2).fun_neg.congr_deriv (by ring))
    integrableOn_gT_Ioo_zero_one
  rw [h, tailGT_one]; ring

/-- Lemma 2(4): `K(t) > 0` strictly on `(0, t₀]`. -/
lemma K_pos {t : ℝ} (ht0 : 0 < t) (ht : t ≤ t0) : 0 < K t := by
  unfold K gT
  have h1t : 0 < 1 - t := by linarith [t0_lt_one]
  have hs_ge : (3 / 4 : ℝ) < Real.sqrt (1 - t) := by
    have h1 : Real.sqrt (1 - t0) ≤ Real.sqrt (1 - t) := Real.sqrt_le_sqrt (by linarith)
    rw [sqrt_one_sub_t0] at h1
    exact s0_mem_bounds.1.trans_le h1
  have hs_lt : Real.sqrt (1 - t) < 1 := by rw [Real.sqrt_lt' zero_lt_one]; linarith
  have hA : artanh (3 / 4) < artanh (Real.sqrt (1 - t)) :=
    strictMonoOn_artanh ⟨by norm_num, by norm_num⟩ ⟨by linarith, hs_lt⟩ hs_ge
  have hA_gt : (6 / 7 : ℝ) < artanh (Real.sqrt (1 - t)) := artanh_three_fourths_gt.trans hA
  have hinv : 1 / (4 * Real.sqrt (1 - t)) < 1 / 3 := by
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    linarith
  linarith

lemma integrableOn_K_Ioo_t0 : IntegrableOn K (Ioo (0 : ℝ) t0) volume := by
  unfold K
  have h1 : IntegrableOn (fun t => 2 * gT t) (Ioo (0 : ℝ) t0) volume :=
    (integrableOn_gT_Ioo_zero_one.mono_set (Ioo_subset_Ioo_right t0_lt_one.le)).const_mul 2
  have h2 : IntegrableOn (fun t : ℝ => 1 / (4 * Real.sqrt (1 - t))) (Ioo (0 : ℝ) t0) volume := by
    refine ContinuousOn.integrableOn_Icc ?_ |>.mono_set Ioo_subset_Icc_self
    refine continuousOn_const.div (continuousOn_const.mul
      (Real.continuous_sqrt.comp (continuous_const.sub continuous_id)).continuousOn) ?_
    intro t ht
    have hpos : 0 < Real.sqrt (1 - t) := Real.sqrt_pos.mpr (by linarith [ht.2, t0_lt_one])
    exact (by positivity : 0 < 4 * Real.sqrt (1 - t)).ne'
  exact h1.sub h2

/-- Lemma 2(4): Exact integral identity `∫ t in (0, t₀), K(t) = 1 / 2`. -/
lemma integral_K_Ioo_t0 : ∫ t in Ioo (0 : ℝ) t0, K t = 1 / 2 := by
  let F0 : ℝ → ℝ := fun t => 2 * t * gT t - Real.sqrt (1 - t) / 2
  have hF0_t0 : F0 t0 = 0 := by
    dsimp only [F0]
    have hphi := PhiPlus_t0
    unfold PhiPlus at hphi
    have hs0 : 0 < Real.sqrt (1 - t0) := Real.sqrt_pos.mpr (by linarith [t0_lt_one])
    have hs1 : Real.sqrt (1 - t0) < 1 := by rw [Real.sqrt_lt' zero_lt_one]; linarith [t0_pos]
    have hA : artanh (Real.sqrt (1 - t0)) ≠ 0 := (artanh_pos hs0 hs1).ne'
    have hmul : 2 * t0 * artanh (Real.sqrt (1 - t0)) = Real.sqrt (1 - t0) := by
      have : Real.sqrt (1 - t0) / artanh (Real.sqrt (1 - t0)) = 2 * t0 := by linarith
      exact ((div_eq_iff hA).mp this).symm
    unfold gT; linarith
  have hlim : Tendsto F0 (𝓝[>] (0 : ℝ)) (𝓝 (-(1 / 2 : ℝ))) := by
    have h1 : Tendsto (fun t : ℝ => 2 * (t * gT t)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa using tendsto_mul_gT_zero.const_mul 2
    have h2 : Tendsto (fun t : ℝ => Real.sqrt (1 - t) / 2) (𝓝[>] (0 : ℝ)) (𝓝 (1 / 2 : ℝ)) := by
      have hc : ContinuousAt (fun t : ℝ => Real.sqrt (1 - t) / 2) 0 :=
        (Real.continuous_sqrt.comp (continuous_const.sub continuous_id)).continuousAt.div_const 2
      simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
    refine (by simpa using h1.sub h2 : Tendsto (fun t => 2 * (t * gT t) - Real.sqrt (1 - t) / 2)
      (𝓝[>] (0 : ℝ)) (𝓝 (-(1 / 2 : ℝ)))).congr (fun t => by dsimp [F0]; ring)
  have hcont : ∀ {c : ℝ}, 0 < c → ContinuousOn F0 (Icc c t0) := fun hc =>
    ((continuousOn_const.mul continuousOn_id).mul
      ((continuousOn_gT_Ioc hc).mono (Icc_subset_Icc_right t0_lt_one.le))).sub
      ((Real.continuous_sqrt.comp (continuous_const.sub continuous_id)).continuousOn.div_const 2)
  have hderiv : ∀ x ∈ Ioo (0 : ℝ) t0, HasDerivAt F0 (K x) x := by
    intro x hx
    have hx1 : x < 1 := hx.2.trans t0_lt_one
    have h1x : 0 < 1 - x := by linarith
    have hd1 := (by simpa using (hasDerivAt_id x).const_mul (2 : ℝ) :
      HasDerivAt (fun t : ℝ => 2 * t) 2 x).mul (hasDerivAt_gT hx.1 hx1)
    have hd2 : HasDerivAt (fun t : ℝ => Real.sqrt (1 - t) / 2) (-(1 / (4 * Real.sqrt (1 - x)))) x := by
      have h1 : HasDerivAt (fun t : ℝ => 1 - t) (-1) x := by
        simpa using (hasDerivAt_id x).const_sub (1 : ℝ)
      exact (((Real.hasDerivAt_sqrt h1x.ne').comp x h1).div_const (2 : ℝ)).congr_deriv (by ring)
    refine (hd1.sub hd2).congr_deriv ?_
    unfold K
    have hsq : Real.sqrt (1 - x) ≠ 0 := (Real.sqrt_pos.mpr h1x).ne'
    field_simp [hx.1.ne', hsq]; ring
  rw [integral_Ioo_eq_sub_of_tendsto_zero t0_pos hcont hlim hderiv integrableOn_K_Ioo_t0, hF0_t0]
  ring

end

end EconCSAuction
