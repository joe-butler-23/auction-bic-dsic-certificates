import Mathlib.MeasureTheory.Group.Integral
import EconCSAuction.Lemma3
import EconCSAuction.SubgradIBP

/-!
# Lemma 4: Explicit `H(div)` Wing Flux `z^{wing}` and Full Non-Smooth Wing Duality

Defines `InterimProfile` (any bidder's shifted convex interim utility `(u, g₁, g₂)` on `[0, 1]²`
with `u ≥ 0`, `g₁, g₂ ≥ 0`, `g₁ + g₂ ≤ 1`, and BIC subgradient inequality) and constructs the
explicit closed-form `H(div)` wing flux `(z₁^{wing}, z₂^{wing})` on `W_+ ∪ W_-`:
1. Exact PDE `∂_s z₂^{wing} + ∂_t (z₁^{wing} - z₂^{wing}) = -ρ` in `(t, s)` coordinates,
   `z₁^{wing}(1, b) = 0`, `z₂^{wing}(a, 0⁺) = 0`, and `(z₁^{wing} - z₂^{wing})(s + t₀, s) = t₀ ρ`.
2. `φ̃₁^{wing}(a, b) - φ̃₂^{wing}(a, b) = Φ̄(a - b)` everywhere on `W_+ ∪ W_-`.
3. For every `L ≥ 0`, `φ̃₁^{wing} > L` and `φ̃₂^{wing} > L` strictly everywhere on `W_+ ∪ W_-`.
4. The wing identity on `W_+ ∪ W_-` by two exact 1D integrations by parts
   (`subgrad_ibp_of_integrable` along diagonals and along horizontal lines) and Fubini; no
   truncation, no limit, and no 2D Sobolev or Rademacher assumptions.
-/

open MeasureTheory Set Filter Topology

namespace EconCSAuction

noncomputable section

/-! ### 1. Shifted Interim Profile `(u, g₁, g₂)` and Directional Subgradients -/

/-- Shifted interim utility and single-item allocation profile `(u, g₁, g₂)` on `[0, 1]²`. -/
structure InterimProfile where
  u  : Type2 → ℝ
  g1 : Type2 → ℝ
  g2 : Type2 → ℝ
  u_nonneg  : ∀ ab ∈ unitSquare, 0 ≤ u ab
  g1_nonneg : ∀ ab ∈ unitSquare, 0 ≤ g1 ab
  g2_nonneg : ∀ ab ∈ unitSquare, 0 ≤ g2 ab
  g_sum_le  : ∀ ab ∈ unitSquare, g1 ab + g2 ab ≤ 1
  bic       : ∀ ab ∈ unitSquare, ∀ ab' ∈ unitSquare,
    u ab' + (ab.1 - ab'.1) * g1 ab' + (ab.2 - ab'.2) * g2 ab' ≤ u ab
  g1_meas   : Measurable g1
  g2_meas   : Measurable g2

namespace InterimProfile

lemma u_lip (P : InterimProfile) {x y : Type2} (hx : x ∈ unitSquare) (hy : y ∈ unitSquare) :
    |P.u y - P.u x| ≤ |y.1 - x.1| + |y.2 - x.2| := by
  have h1 := P.bic y hy x hx
  have h2 := P.bic x hx y hy
  have hg1x := P.g1_nonneg x hx; have hg2x := P.g2_nonneg x hx; have hsx := P.g_sum_le x hx
  have hg1y := P.g1_nonneg y hy; have hg2y := P.g2_nonneg y hy; have hsy := P.g_sum_le y hy
  have hg1x_le : P.g1 x ≤ 1 := by linarith
  have hg2x_le : P.g2 x ≤ 1 := by linarith
  have hg1y_le : P.g1 y ≤ 1 := by linarith
  have hg2y_le : P.g2 y ≤ 1 := by linarith
  rw [abs_le]
  have ha1 : -|y.1 - x.1| ≤ y.1 - x.1 := neg_abs_le _
  have ha2 : y.1 - x.1 ≤ |y.1 - x.1| := le_abs_self _
  have hb1 : -|y.2 - x.2| ≤ y.2 - x.2 := neg_abs_le _
  have hb2 : y.2 - x.2 ≤ |y.2 - x.2| := le_abs_self _
  constructor
  · nlinarith
  · nlinarith

lemma u_le_bound (P : InterimProfile) {ab : Type2} (hab : ab ∈ unitSquare) :
    P.u ab ≤ P.u (0, 0) + 1 := by
  have h0 : ((0 : ℝ), (0 : ℝ)) ∈ unitSquare := ⟨⟨le_rfl, zero_le_one⟩, ⟨le_rfl, zero_le_one⟩⟩
  have h := P.bic (0, 0) h0 ab hab
  have hg1 := P.g1_nonneg ab hab; have hg2 := P.g2_nonneg ab hab; have hs := P.g_sum_le ab hab
  have h1 : ab.1 * P.g1 ab ≤ P.g1 ab := by nlinarith [hab.1.2]
  have h2 : ab.2 * P.g2 ab ≤ P.g2 ab := by nlinarith [hab.2.2]
  dsimp only at h
  linarith

lemma u_continuousOn (P : InterimProfile) : ContinuousOn P.u unitSquare := by
  rw [Metric.continuousOn_iff]
  intro x hx ε hε
  refine ⟨ε / 3, by linarith, fun y hy hdist => ?_⟩
  rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq] at hdist
  rw [Real.dist_eq]
  calc |P.u y - P.u x| ≤ |y.1 - x.1| + |y.2 - x.2| := P.u_lip hx hy
    _ < ε / 3 + ε / 3 := add_lt_add hdist.1 hdist.2
    _ < ε := by linarith

lemma u_aestronglyMeasurable (P : InterimProfile) :
    AEStronglyMeasurable P.u (volume.restrict openUnitSquare) :=
  (P.u_continuousOn.mono (Set.prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)).aestronglyMeasurable
    measurableSet_openUnitSquare

/-- Diagonal subgradient along `s ↦ (s + t, s)`: `IsSubgradOn` with derivative `g1 + g2`. -/
lemma diagSubgrad (P : InterimProfile) {t a b : ℝ}
    (ht0 : 0 ≤ t) (ha : 0 ≤ a) (hb : b ≤ 1 - t) :
    IsSubgradOn (fun s => P.u (s + t, s)) (fun s => P.g1 (s + t, s) + P.g2 (s + t, s)) a b := by
  intro x hx y hy hxy
  have hxm : (x + t, x) ∈ unitSquare := ⟨⟨by linarith [hx.1], by linarith [hx.2]⟩, ⟨by linarith [hx.1], by linarith [hx.2]⟩⟩
  have hym : (y + t, y) ∈ unitSquare := ⟨⟨by linarith [hy.1], by linarith [hy.2]⟩, ⟨by linarith [hy.1], by linarith [hy.2]⟩⟩
  have h1 := P.bic (y + t, y) hym (x + t, x) hxm
  have h2 := P.bic (x + t, x) hxm (y + t, y) hym
  dsimp only at h1 h2
  exact ⟨by linarith, by linarith⟩

/-- Horizontal subgradient along `t ↦ (s + t, s)`: `IsSubgradOn` with derivative `g1`. -/
lemma horizSubgrad (P : InterimProfile) {s a b : ℝ}
    (hs0 : 0 ≤ s) (ha : 0 ≤ a) (hb : b ≤ 1 - s) :
    IsSubgradOn (fun t => P.u (s + t, s)) (fun t => P.g1 (s + t, s)) a b := by
  intro x hx y hy hxy
  have hxm : (s + x, s) ∈ unitSquare := ⟨⟨by linarith [hx.1], by linarith [hx.2]⟩, ⟨hs0, by linarith [hx.1, hx.2]⟩⟩
  have hym : (s + y, s) ∈ unitSquare := ⟨⟨by linarith [hy.1], by linarith [hy.2]⟩, ⟨hs0, by linarith [hy.1, hy.2]⟩⟩
  have h1 := P.bic (s + y, s) hym (s + x, s) hxm
  have h2 := P.bic (s + x, s) hxm (s + y, s) hym
  dsimp only at h1 h2
  exact ⟨by linarith, by linarith⟩

/-- Ray subgradient along `λ ↦ (λ, λ η)`: `IsSubgradOn` with derivative `g1 + η * g2`. -/
lemma raySubgrad (P : InterimProfile) {η b : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hb : b ≤ 1) :
    IsSubgradOn (fun lam => P.u (lam, lam * η))
      (fun lam => P.g1 (lam, lam * η) + η * P.g2 (lam, lam * η)) 0 b := by
  intro x hx y hy hxy
  have hxm : (x, x * η) ∈ unitSquare := ⟨⟨hx.1, hx.2.trans hb⟩, ⟨by nlinarith [hx.1], by nlinarith [hx.1, hx.2]⟩⟩
  have hym : (y, y * η) ∈ unitSquare := ⟨⟨hy.1, hy.2.trans hb⟩, ⟨by nlinarith [hy.1], by nlinarith [hy.1, hy.2]⟩⟩
  have h1 := P.bic (y, y * η) hym (x, x * η) hxm
  have h2 := P.bic (x, x * η) hxm (y, y * η) hym
  dsimp only at h1 h2
  exact ⟨by nlinarith, by nlinarith⟩

/-- Coordinate swap `(a, b) ↔ (b, a)` preserves `InterimProfile`. -/
def swap (P : InterimProfile) : InterimProfile where
  u ab := P.u (ab.2, ab.1)
  g1 ab := P.g2 (ab.2, ab.1)
  g2 ab := P.g1 (ab.2, ab.1)
  u_nonneg ab hab := P.u_nonneg (ab.2, ab.1) ⟨hab.2, hab.1⟩
  g1_nonneg ab hab := P.g2_nonneg (ab.2, ab.1) ⟨hab.2, hab.1⟩
  g2_nonneg ab hab := P.g1_nonneg (ab.2, ab.1) ⟨hab.2, hab.1⟩
  g_sum_le ab hab := by linarith [P.g_sum_le (ab.2, ab.1) ⟨hab.2, hab.1⟩]
  bic ab hab ab' hab' := by
    have h := P.bic (ab.2, ab.1) ⟨hab.2, hab.1⟩ (ab'.2, ab'.1) ⟨hab'.2, hab'.1⟩
    dsimp only at h ⊢; linarith
  g1_meas := P.g2_meas.comp measurable_swap
  g2_meas := P.g1_meas.comp measurable_swap

/-- Symmetrization `(1/2) (P + P.swap)` preserves `InterimProfile`. -/
def symm (P : InterimProfile) : InterimProfile where
  u ab := (P.u ab + P.u (ab.2, ab.1)) / 2
  g1 ab := (P.g1 ab + P.g2 (ab.2, ab.1)) / 2
  g2 ab := (P.g2 ab + P.g1 (ab.2, ab.1)) / 2
  u_nonneg ab hab := by linarith [P.u_nonneg ab hab, P.u_nonneg (ab.2, ab.1) ⟨hab.2, hab.1⟩]
  g1_nonneg ab hab := by linarith [P.g1_nonneg ab hab, P.g2_nonneg (ab.2, ab.1) ⟨hab.2, hab.1⟩]
  g2_nonneg ab hab := by linarith [P.g2_nonneg ab hab, P.g1_nonneg (ab.2, ab.1) ⟨hab.2, hab.1⟩]
  g_sum_le ab hab := by linarith [P.g_sum_le ab hab, P.g_sum_le (ab.2, ab.1) ⟨hab.2, hab.1⟩]
  bic ab hab ab' hab' := by
    have h1 := P.bic ab hab ab' hab'
    have h2 := P.bic (ab.2, ab.1) ⟨hab.2, hab.1⟩ (ab'.2, ab'.1) ⟨hab'.2, hab'.1⟩
    dsimp only at h1 h2 ⊢; linarith
  g1_meas := (P.g1_meas.add (P.g2_meas.comp measurable_swap)).div_const 2
  g2_meas := (P.g2_meas.add (P.g1_meas.comp measurable_swap)).div_const 2

/-- Shifting `u` down by `u(0, 0)` preserves `InterimProfile` and forces `u(0, 0) = 0`. -/
def shiftZero (P : InterimProfile) : InterimProfile where
  u ab := P.u ab - P.u (0, 0)
  g1 := P.g1
  g2 := P.g2
  u_nonneg ab hab := by
    have h0 : ((0 : ℝ), (0 : ℝ)) ∈ unitSquare := ⟨⟨le_rfl, zero_le_one⟩, ⟨le_rfl, zero_le_one⟩⟩
    have h := P.bic ab hab (0, 0) h0
    dsimp only at h
    have hg1 := P.g1_nonneg (0, 0) h0
    have hg2 := P.g2_nonneg (0, 0) h0
    nlinarith [hab.1.1, hab.2.1]
  g1_nonneg := P.g1_nonneg
  g2_nonneg := P.g2_nonneg
  g_sum_le := P.g_sum_le
  bic ab hab ab' hab' := by linarith [P.bic ab hab ab' hab']
  g1_meas := P.g1_meas
  g2_meas := P.g2_meas

end InterimProfile

/-! ### 2. Domain Partition (`S`, `W_+`, `W_-`) and Explicit Wing Flux `z^{wing}` -/

/-- Open strip `S = {(a, b) ∈ (0, 1)² | |a - b| < t₀}`. -/
def stripSet : Set Type2 :=
  openUnitSquare ∩ ({ab : Type2 | -t0 < ab.1 - ab.2} ∩ {ab : Type2 | ab.1 - ab.2 < t0})

/-- Upper half-strip `S_+ = {(a, b) ∈ (0, 1)² | 0 < a - b < t₀}`. -/
def stripPos : Set Type2 :=
  openUnitSquare ∩ ({ab : Type2 | (0 : ℝ) < ab.1 - ab.2} ∩ {ab : Type2 | ab.1 - ab.2 < t0})

/-- Upper wing `W_+ = {(a, b) ∈ (0, 1)² | t₀ < a - b < 1}`. -/
def wingPos : Set Type2 :=
  openUnitSquare ∩ ({ab : Type2 | t0 < ab.1 - ab.2} ∩ {ab : Type2 | ab.1 - ab.2 < 1})

/-- Lower wing `W_- = {(a, b) ∈ (0, 1)² | t₀ < b - a < 1}`. -/
def wingNeg : Set Type2 :=
  openUnitSquare ∩ ({ab : Type2 | t0 < ab.2 - ab.1} ∩ {ab : Type2 | ab.2 - ab.1 < 1})

lemma measurableSet_stripSet : MeasurableSet stripSet :=
  measurableSet_openUnitSquare.inter
    ((measurableSet_lt measurable_const (measurable_fst.sub measurable_snd)).inter
     (measurableSet_lt (measurable_fst.sub measurable_snd) measurable_const))

lemma measurableSet_stripPos : MeasurableSet stripPos :=
  measurableSet_openUnitSquare.inter
    ((measurableSet_lt measurable_const (measurable_fst.sub measurable_snd)).inter
     (measurableSet_lt (measurable_fst.sub measurable_snd) measurable_const))

lemma measurableSet_wingPos : MeasurableSet wingPos :=
  measurableSet_openUnitSquare.inter
    ((measurableSet_lt measurable_const (measurable_fst.sub measurable_snd)).inter
     (measurableSet_lt (measurable_fst.sub measurable_snd) measurable_const))

lemma measurableSet_wingNeg : MeasurableSet wingNeg :=
  measurableSet_openUnitSquare.inter
    ((measurableSet_lt measurable_const (measurable_snd.sub measurable_fst)).inter
     (measurableSet_lt (measurable_snd.sub measurable_fst) measurable_const))

/-- Inverse hazard function `H(t) = (1 - G_T(t)) / g_T(t) = t - Φ_+(t)`. -/
def Hwing (t : ℝ) : ℝ := tailGT t / gT t

/-- Explicit closed-form `z₂^{wing}` in `(t, s)` coordinates (`a = s + t, b = s`). -/
def z2WingTS (t s : ℝ) : ℝ :=
  -(Hwing t / (4 * t * Real.sqrt (1 - t) * gT t)) * Iwing s t +
    Hwing t * (Real.sqrt s / (4 * t * Real.sqrt (s + t)))

/-- Difference `w^{wing}(t, s) = z₁^{wing} - z₂^{wing} = H(t) ρ(s + t, s)`. -/
def wWingTS (t s : ℝ) : ℝ := Hwing t * rho (s + t) s

/-- Explicit closed-form `z₁^{wing}` in `(t, s)` coordinates. -/
def z1WingTS (t s : ℝ) : ℝ := z2WingTS t s + wWingTS t s

/-- Dual virtual values `(φ̃₁^{wing}, φ̃₂^{wing})` on `W_+ ∪ W_-` (zero on `S`). -/
def phi1Wing (L : ℝ) (ab : Type2) : ℝ :=
  if t0 < ab.1 - ab.2 then
    L + ab.1 - z1WingTS (ab.1 - ab.2) ab.2 / rho ab.1 ab.2
  else if t0 < ab.2 - ab.1 then
    L + ab.1 - z2WingTS (ab.2 - ab.1) ab.1 / rho ab.2 ab.1
  else 0

def phi2Wing (L : ℝ) (ab : Type2) : ℝ :=
  if t0 < ab.1 - ab.2 then
    L + ab.2 - z2WingTS (ab.1 - ab.2) ab.2 / rho ab.1 ab.2
  else if t0 < ab.2 - ab.1 then
    L + ab.2 - z1WingTS (ab.2 - ab.1) ab.1 / rho ab.2 ab.1
  else 0

/-- Strip functional `L(u|_S)` from Lemma 4(4) and Lemma 5. -/
def stripFunctional (L : ℝ) (P : InterimProfile) : ℝ :=
  (∫ ab in stripSet, ((L + ab.1) * P.g1 ab + (L + ab.2) * P.g2 ab - P.u ab) * rho ab.1 ab.2) -
    ∫ s in Ioo (0 : ℝ) (1 - t0),
      (P.u (s + t0, s) + P.u (s, s + t0)) * (t0 * rho (s + t0) s)

/-! ### 3. Pointwise Properties of `H`, `z^{wing}`, and `φ̃^{wing}` (Lemma 4(1)–(3)) -/

lemma Hwing_eq_sub_PhiPlus {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    Hwing t = t - PhiPlus t := by
  unfold Hwing tailGT PhiPlus gT
  have hs0 : 0 < Real.sqrt (1 - t) := Real.sqrt_pos.mpr (by linarith)
  have hs1 : Real.sqrt (1 - t) < 1 := by rw [Real.sqrt_lt' zero_lt_one]; linarith
  have hA : artanh (Real.sqrt (1 - t)) ≠ 0 := (artanh_pos hs0 hs1).ne'
  field_simp [hA]
  ring

lemma Hwing_t0 : Hwing t0 = t0 := by
  rw [Hwing_eq_sub_PhiPlus t0_pos t0_lt_one, PhiPlus_t0, sub_zero]

lemma Hwing_pos {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) : 0 < Hwing t := by
  unfold Hwing
  have htail : 0 < tailGT t := by
    rw [← integral_gT_Ioo ht0 ht1.le]
    have hpos_m : 0 < gT ((t + 1) / 2) := gT_pos (by linarith) (by linarith)
    have hge : ∫ x in Ioo t ((t + 1) / 2), gT ((t + 1) / 2) ≤ ∫ x in Ioo t 1, gT x := by
      calc ∫ x in Ioo t ((t + 1) / 2), gT ((t + 1) / 2)
          ≤ ∫ x in Ioo t ((t + 1) / 2), gT x := by
            refine setIntegral_mono_on (integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top))
              (integrableOn_gT_Ioo_zero_one.mono_set (Ioo_subset_Ioo ht0.le (by linarith)))
              measurableSet_Ioo (fun x hx => (strictAntiOn_gT ⟨ht0.trans hx.1, by linarith [hx.2]⟩
                ⟨by linarith, by linarith⟩ hx.2).le)
        _ ≤ ∫ x in Ioo t 1, gT x :=
            setIntegral_mono_set (integrableOn_gT_Ioo_zero_one.mono_set (Ioo_subset_Ioo_left ht0.le))
              (ae_restrict_of_forall_mem measurableSet_Ioo (fun x hx => (gT_pos (ht0.trans hx.1) hx.2).le))
              (Eventually.of_forall (Ioo_subset_Ioo_right (by linarith)))
    have hval : ∫ _ in Ioo t ((t + 1) / 2), gT ((t + 1) / 2) = ((1 - t) / 2) * gT ((t + 1) / 2) := by
      rw [setIntegral_const, Real.volume_real_Ioo_of_le (by linarith), smul_eq_mul]; ring
    rw [hval] at hge
    have : 0 < ((1 - t) / 2) * gT ((t + 1) / 2) := mul_pos (by linarith) hpos_m
    linarith
  exact div_pos htail (gT_pos ht0 ht1)

/-- Key elementary bound `H(t) ≤ 1 - t` on `(0, 1)` (immediate from `g_T` decreasing). -/
lemma Hwing_le_one_sub {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) : Hwing t ≤ 1 - t := by
  unfold Hwing
  rw [div_le_iff₀ (gT_pos ht0 ht1), ← integral_gT_Ioo ht0 ht1.le]
  calc ∫ x in Ioo t 1, gT x
      ≤ ∫ _ in Ioo t 1, gT t := by
        refine setIntegral_mono_on (integrableOn_gT_Ioo_zero_one.mono_set (Ioo_subset_Ioo_left ht0.le))
          (integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top))
          measurableSet_Ioo (fun x hx => (strictAntiOn_gT ⟨ht0, ht1⟩ ⟨ht0.trans hx.1, hx.2⟩ hx.1).le)
    _ = (1 - t) * gT t := by
        rw [setIntegral_const, Real.volume_real_Ioo_of_le ht1.le, smul_eq_mul]

lemma hasDerivAt_Hwing {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    HasDerivAt Hwing (-1 + Hwing t / (4 * t * Real.sqrt (1 - t) * gT t)) t := by
  have hg : gT t ≠ 0 := (gT_pos ht0 ht1).ne'
  have hsq : Real.sqrt (1 - t) ≠ 0 := (Real.sqrt_pos.mpr (by linarith)).ne'
  have hd := (hasDerivAt_tailGT ht0 ht1).div (hasDerivAt_gT ht0 ht1) hg
  refine (hd.congr_of_eventuallyEq (Eventually.of_forall fun _ => rfl)).congr_deriv ?_
  unfold Hwing
  field_simp [hg, ht0.ne', hsq]
  ring

/-- Lemma 4(1): `∂_s z₂^{wing}(t, s)`. -/
lemma hasDerivAt_z2WingTS_s {t s : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (hs : 0 < s) :
    HasDerivAt (fun r => z2WingTS t r)
      (-(Hwing t / (4 * t * Real.sqrt (1 - t) * gT t)) * rho (s + t) s +
        Hwing t / (8 * Real.sqrt s * (s + t) * Real.sqrt (s + t))) s := by
  have hst : 0 < s + t := by linarith
  have hsq_s : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have hsq_st : 0 < Real.sqrt (s + t) := Real.sqrt_pos.mpr hst
  have hd1 := (hasDerivAt_Iwing_s hs ht0).const_mul (-(Hwing t / (4 * t * Real.sqrt (1 - t) * gT t)))
  have hd_num : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt s)) s := Real.hasDerivAt_sqrt hs.ne'
  have hd_den : HasDerivAt (fun r : ℝ => 4 * t * Real.sqrt (r + t))
      (4 * t * (1 / (2 * Real.sqrt (s + t)))) s := by
    have hadd : HasDerivAt (fun r : ℝ => r + t) 1 s := (hasDerivAt_id s).add_const t
    have hsq := (Real.hasDerivAt_sqrt hst.ne').comp s hadd
    exact (hsq.const_mul (4 * t)).congr_deriv (by ring)
  have hd2 := (hd_num.div hd_den (by positivity)).const_mul (Hwing t)
  refine ((hd1.add hd2).congr_of_eventuallyEq (Eventually.of_forall fun r => by
    unfold z2WingTS; dsimp only [Pi.add_apply, Pi.div_apply])).congr_deriv ?_
  unfold rho
  rw [Real.sqrt_mul hst.le]
  field_simp [ht0.ne', hsq_s.ne', hsq_st.ne', hst.ne']
  rw [Real.sq_sqrt hst.le, Real.sq_sqrt hs.le]
  ring

/-- Lemma 4(1): `∂_t w^{wing}(t, s)`. -/
lemma hasDerivAt_wWingTS_t {t s : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (hs : 0 < s) :
    HasDerivAt (fun x => wWingTS x s)
      ((-1 + Hwing t / (4 * t * Real.sqrt (1 - t) * gT t)) * rho (s + t) s -
        Hwing t / (8 * Real.sqrt s * (s + t) * Real.sqrt (s + t))) t := by
  have hst : 0 < s + t := by linarith
  have hsq_s : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have hsq_st : 0 < Real.sqrt (s + t) := Real.sqrt_pos.mpr hst
  have hsq_prod : 0 < Real.sqrt ((s + t) * s) := Real.sqrt_pos.mpr (mul_pos hst hs)
  have hd_rho : HasDerivAt (fun x : ℝ => rho (s + x) s)
      (-(1 / (8 * Real.sqrt s * (s + t) * Real.sqrt (s + t)))) t := by
    have hmul : HasDerivAt (fun x : ℝ => (s + x) * s) s t := by
      have h1 : HasDerivAt (fun x : ℝ => s + x) 1 t := (hasDerivAt_id t).const_add s
      exact (h1.mul_const s).congr_deriv (by ring)
    have hsq := (Real.hasDerivAt_sqrt (mul_pos hst hs).ne').comp t hmul
    have hden := hsq.const_mul (4 : ℝ)
    have hinv := (hasDerivAt_const t (1 : ℝ)).div hden (mul_ne_zero (by norm_num) hsq_prod.ne')
    refine (hinv.congr_of_eventuallyEq (Eventually.of_forall fun x => by
      unfold rho; rfl)).congr_deriv ?_
    dsimp only [Function.comp_apply]
    rw [Real.sqrt_mul hst.le]
    field_simp [hsq_s.ne', hsq_st.ne', hst.ne']
    rw [Real.sq_sqrt hst.le, Real.sq_sqrt hs.le]
    ring
  have hd := (hasDerivAt_Hwing ht0 ht1).mul hd_rho
  exact (hd.congr_of_eventuallyEq (Eventually.of_forall fun x => by unfold wWingTS; rfl)).congr_deriv (by ring)

/-- Lemma 4(1): Exact wing PDE `∂_s z₂^{wing}(t, s) + ∂_t w^{wing}(t, s) = -ρ(s + t, s)`. -/
lemma wing_pde_ts (t s : ℝ) :
    (-(Hwing t / (4 * t * Real.sqrt (1 - t) * gT t)) * rho (s + t) s +
      Hwing t / (8 * Real.sqrt s * (s + t) * Real.sqrt (s + t))) +
    ((-1 + Hwing t / (4 * t * Real.sqrt (1 - t) * gT t)) * rho (s + t) s -
      Hwing t / (8 * Real.sqrt s * (s + t) * Real.sqrt (s + t))) =
      -rho (s + t) s := by
  ring

/-- Lemma 4(1): Boundary condition `z₁^{wing}(1, 1 - t) = 0` identically for `t ∈ (0, 1)`. -/
lemma z1WingTS_boundary_a1 {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    z1WingTS t (1 - t) = 0 := by
  unfold z1WingTS z2WingTS wWingTS rho
  rw [Iwing_one_sub ht0 ht1]
  have hsum : 1 - t + t = 1 := by ring
  rw [hsum, Real.sqrt_one, one_mul]
  have h1t : 0 < 1 - t := by linarith
  have hsq : Real.sqrt (1 - t) ≠ 0 := (Real.sqrt_pos.mpr h1t).ne'
  have hg : gT t ≠ 0 := (gT_pos ht0 ht1).ne'
  field_simp [ht0.ne', hsq, hg]
  rw [Real.sq_sqrt h1t.le]
  ring

lemma wWingTS_t0 (s : ℝ) : wWingTS t0 s = t0 * rho (s + t0) s := by
  unfold wWingTS
  rw [Hwing_t0]

/-- Lemma 4(2): `φ̃₁^{wing}(a, b) - φ̃₂^{wing}(a, b) = Φ̄(a - b)` everywhere on `W_+ ∪ W_-`. -/
lemma phi1Wing_sub_phi2Wing (L : ℝ) {ab : Type2} (hab : ab ∈ wingPos ∪ wingNeg) :
    phi1Wing L ab - phi2Wing L ab = PhiBar (ab.1 - ab.2) := by
  rcases hab with hp | hm
  · have ht : t0 < ab.1 - ab.2 := hp.2.1
    have ht1 : ab.1 - ab.2 < 1 := hp.2.2
    have hrho : rho ab.1 ab.2 ≠ 0 := (rho_pos hp.1.1.1 hp.1.2.1).ne'
    unfold phi1Wing phi2Wing PhiBar
    rw [ite_eq_left ht, ite_eq_left ht, ite_eq_left ht]
    unfold z1WingTS wWingTS
    have hsum : ab.2 + (ab.1 - ab.2) = ab.1 := by ring
    rw [hsum]
    have hH := Hwing_eq_sub_PhiPlus (t0_pos.trans ht) ht1
    field_simp [hrho]
    rw [hH]; ring
  · have ht : t0 < ab.2 - ab.1 := hm.2.1
    have ht1 : ab.2 - ab.1 < 1 := hm.2.2
    have hnot : ¬ t0 < ab.1 - ab.2 := by linarith [t0_pos]
    have hlt : ab.1 - ab.2 < -t0 := by linarith
    have hrho : rho ab.2 ab.1 ≠ 0 := (rho_pos hm.1.2.1 hm.1.1.1).ne'
    unfold phi1Wing phi2Wing PhiBar
    rw [ite_eq_right hnot, ite_eq_left ht, ite_eq_right hnot, ite_eq_left ht, ite_eq_right hnot, ite_eq_left hlt]
    unfold z1WingTS wWingTS
    have hsum : ab.1 + (ab.2 - ab.1) = ab.2 := by ring
    rw [hsum]
    have hH := Hwing_eq_sub_PhiPlus (t0_pos.trans ht) ht1
    have hneg : -(ab.1 - ab.2) = ab.2 - ab.1 := by ring
    rw [hneg]
    field_simp [hrho]
    rw [hH]; ring

/-- Key pointwise inequality on `W_+`: `z₂^{wing}(t, s) / ρ(s + t, s) < s`. -/
lemma z2WingTS_div_rho_lt_s {t s : ℝ} (ht : t0 < t) (ht1 : t < 1) (hs0 : 0 < s) :
    z2WingTS t s / rho (s + t) s < s := by
  have ht0 : 0 < t := t0_pos.trans ht
  have hst : 0 < s + t := by linarith
  have hI_pos : 0 < Iwing s t := by
    have hgt : Real.sqrt t < Real.sqrt (s + t) + Real.sqrt s := by
      have h1 : Real.sqrt t < Real.sqrt (s + t) := Real.sqrt_lt_sqrt ht0.le (by linarith)
      linarith [Real.sqrt_nonneg s]
    unfold Iwing
    have h1 : 1 < (Real.sqrt (s + t) + Real.sqrt s) / Real.sqrt t :=
      (one_lt_div (Real.sqrt_pos.mpr ht0)).mpr hgt
    exact mul_pos (by norm_num) (Real.log_pos h1)
  have hH_pos : 0 < Hwing t := Hwing_pos ht0 ht1
  have hH_lt_t : Hwing t < t := by
    rw [Hwing_eq_sub_PhiPlus ht0 ht1]
    linarith [PhiPlus_pos_of_gt_t0 ht ht1]
  have hneg_term : 0 < Hwing t / (4 * t * Real.sqrt (1 - t) * gT t) * Iwing s t := by
    have : 0 < Real.sqrt (1 - t) := Real.sqrt_pos.mpr (by linarith)
    have : 0 < gT t := gT_pos ht0 ht1
    positivity
  have hlt1 : z2WingTS t s < Hwing t * (Real.sqrt s / (4 * t * Real.sqrt (s + t))) := by
    unfold z2WingTS; linarith
  have hrho_pos : 0 < rho (s + t) s := rho_pos hst hs0
  have hratio : Hwing t * (Real.sqrt s / (4 * t * Real.sqrt (s + t))) / rho (s + t) s =
      (Hwing t / t) * s := by
    unfold rho
    rw [Real.sqrt_mul hst.le]
    have hsq_s : (Real.sqrt s) ^ 2 = s := Real.sq_sqrt hs0.le
    have h1 : Real.sqrt s ≠ 0 := (Real.sqrt_pos.mpr hs0).ne'
    have h2 : Real.sqrt (s + t) ≠ 0 := (Real.sqrt_pos.mpr hst).ne'
    field_simp [ht0.ne', h1, h2]
    nlinarith
  have hlt2 : z2WingTS t s / rho (s + t) s < (Hwing t / t) * s := by
    rw [← hratio]
    exact div_lt_div_of_pos_right hlt1 hrho_pos
  have hfrac_lt : Hwing t / t < 1 := (div_lt_one ht0).mpr hH_lt_t
  nlinarith

/-- Lemma 4(3): Strictly positive dual virtual values `φ̃₁^{wing} > L` and `φ̃₂^{wing} > L` on `W_+ ∪ W_-`. -/
lemma phiWing_gt_L (L : ℝ) {ab : Type2} (hab : ab ∈ wingPos ∪ wingNeg) :
    L < phi1Wing L ab ∧ L < phi2Wing L ab := by
  rcases hab with hp | hm
  · have ht : t0 < ab.1 - ab.2 := hp.2.1
    have ht1 : ab.1 - ab.2 < 1 := hp.2.2
    have hphi2 : L < phi2Wing L ab := by
      unfold phi2Wing
      rw [if_pos ht]
      have hlt := z2WingTS_div_rho_lt_s ht ht1 hp.1.2.1
      have hsum : ab.2 + (ab.1 - ab.2) = ab.1 := by ring
      rw [hsum] at hlt
      linarith
    have hdiff := phi1Wing_sub_phi2Wing L (Or.inl hp)
    have hpos : 0 < PhiBar (ab.1 - ab.2) := PhiBar_pos_of_gt ht ht1
    exact ⟨by linarith, hphi2⟩
  · have ht : t0 < ab.2 - ab.1 := hm.2.1
    have ht1 : ab.2 - ab.1 < 1 := hm.2.2
    have hnot : ¬ t0 < ab.1 - ab.2 := by linarith [t0_pos]
    have hphi1 : L < phi1Wing L ab := by
      unfold phi1Wing
      rw [if_neg hnot, if_pos ht]
      have hlt := z2WingTS_div_rho_lt_s ht ht1 hm.1.1.1
      have hsum : ab.1 + (ab.2 - ab.1) = ab.2 := by ring
      rw [hsum] at hlt
      linarith
    have hdiff := phi1Wing_sub_phi2Wing L (Or.inr hm)
    have hneg : PhiBar (ab.1 - ab.2) < 0 := PhiBar_neg_of_lt (by linarith) (by linarith)
    exact ⟨hphi1, by linarith⟩

/-! ### 4. Uniform Bounds, Integrability, and Full Non-Smooth Lemma 4(4) Identity -/

/-- Uniform `L^∞` bound on `z₂^{wing}(t, s)` everywhere on `W_+`: `|z₂^{wing}(t, s)| ≤ C_z2`. -/
lemma z2WingTS_abs_le {t s : ℝ} (ht : t0 ≤ t) (ht1 : t < 1) (hs0 : 0 ≤ s) (hs1 : s ≤ 1 - t) :
    |z2WingTS t s| ≤ 1 / (4 * t0) + 1 / (4 * t0 * Real.sqrt t0) := by
  have ht0_pos := t0_pos
  have ht_pos : 0 < t := ht0_pos.trans_le ht
  have h1t : 0 < 1 - t := by linarith
  have hH_nn : 0 ≤ Hwing t := (Hwing_pos ht_pos ht1).le
  have hH_le : Hwing t ≤ 1 - t := Hwing_le_one_sub ht_pos ht1
  have hI_nn : 0 ≤ Iwing s t := by
    rw [← integral_rho_eq_Iwing hs0 ht_pos]
    exact setIntegral_nonneg measurableSet_Ioo (fun r _ => rho_nonneg _ _)
  have hI_le : Iwing s t ≤ gT t := by
    rw [← integral_rho_eq_Iwing hs0 ht_pos, ← integral_rho_eq_gT ht_pos ht1]
    exact setIntegral_mono_set (integrableOn_rho_diag (by linarith) ht_pos)
      (ae_restrict_of_forall_mem measurableSet_Ioo (fun r _ => rho_nonneg _ _))
      (Eventually.of_forall (Ioo_subset_Ioo_right hs1))
  have hT1_nn : 0 ≤ Hwing t / (4 * t * Real.sqrt (1 - t) * gT t) * Iwing s t := by
    have := Real.sqrt_pos.mpr h1t; have := gT_pos ht_pos ht1; positivity
  have hT1_le : Hwing t / (4 * t * Real.sqrt (1 - t) * gT t) * Iwing s t ≤ 1 / (4 * t0) := by
    have hg_pos : 0 < gT t := gT_pos ht_pos ht1
    have hsq1t : 0 < Real.sqrt (1 - t) := Real.sqrt_pos.mpr h1t
    calc Hwing t / (4 * t * Real.sqrt (1 - t) * gT t) * Iwing s t
        ≤ Hwing t / (4 * t * Real.sqrt (1 - t) * gT t) * gT t :=
          mul_le_mul_of_nonneg_left hI_le (by positivity)
      _ = Hwing t / (4 * t * Real.sqrt (1 - t)) := by field_simp [hg_pos.ne']
      _ ≤ (1 - t) / (4 * t * Real.sqrt (1 - t)) :=
          div_le_div_of_nonneg_right hH_le (by positivity)
      _ = Real.sqrt (1 - t) / (4 * t) := by
          have hsq2 : (Real.sqrt (1 - t)) ^ 2 = 1 - t := Real.sq_sqrt h1t.le
          field_simp [ht_pos.ne', hsq1t.ne']; linarith
      _ ≤ 1 / (4 * t0) := by
          have hsq_le1 : Real.sqrt (1 - t) ≤ 1 := by
            calc Real.sqrt (1 - t) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt (by linarith)
              _ = 1 := Real.sqrt_one
          exact div_le_div₀ zero_le_one hsq_le1 (by positivity) (by linarith)
  have hT2_nn : 0 ≤ Hwing t * (Real.sqrt s / (4 * t * Real.sqrt (s + t))) := by
    have : 0 < Real.sqrt (s + t) := Real.sqrt_pos.mpr (by linarith)
    positivity
  have hT2_le : Hwing t * (Real.sqrt s / (4 * t * Real.sqrt (s + t))) ≤ 1 / (4 * t0 * Real.sqrt t0) := by
    have hsq_s_le : Real.sqrt s ≤ 1 := by
      calc Real.sqrt s ≤ Real.sqrt 1 := Real.sqrt_le_sqrt (by linarith)
        _ = 1 := Real.sqrt_one
    have hden_ge : 4 * t0 * Real.sqrt t0 ≤ 4 * t * Real.sqrt (s + t) := by
      have h1 : Real.sqrt t0 ≤ Real.sqrt (s + t) := Real.sqrt_le_sqrt (by linarith)
      have h2 : 0 ≤ Real.sqrt t0 := Real.sqrt_nonneg t0
      nlinarith
    have hq_le : Real.sqrt s / (4 * t * Real.sqrt (s + t)) ≤ 1 / (4 * t0 * Real.sqrt t0) :=
      div_le_div₀ zero_le_one hsq_s_le (by positivity) hden_ge
    calc Hwing t * (Real.sqrt s / (4 * t * Real.sqrt (s + t)))
        ≤ 1 * (1 / (4 * t0 * Real.sqrt t0)) :=
          mul_le_mul (hH_le.trans (by linarith)) hq_le (by positivity) zero_le_one
      _ = 1 / (4 * t0 * Real.sqrt t0) := one_mul _
  unfold z2WingTS
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩

/-- Helper: `dz2(t, s) = ∂_s z₂^{wing}(t, s)`. -/
def dz2WingTS (t s : ℝ) : ℝ :=
  -(Hwing t / (4 * t * Real.sqrt (1 - t) * gT t)) * rho (s + t) s +
    Hwing t / (8 * Real.sqrt s * (s + t) * Real.sqrt (s + t))

/-- Helper: `dw(t, s) = ∂_t w^{wing}(t, s)`. -/
def dwWingTS (t s : ℝ) : ℝ :=
  (-1 + Hwing t / (4 * t * Real.sqrt (1 - t) * gT t)) * rho (s + t) s -
    Hwing t / (8 * Real.sqrt s * (s + t) * Real.sqrt (s + t))

/-! ### Zero-truncation ingredients for the wing identity -/

lemma z2WingTS_zero {t : ℝ} (ht : 0 < t) : z2WingTS t 0 = 0 := by
  unfold z2WingTS
  rw [Iwing_zero ht]; simp

lemma continuousOn_Iwing_s {t : ℝ} (ht : 0 < t) (b : ℝ) :
    ContinuousOn (fun s => Iwing s t) (Icc (0 : ℝ) b) := by
  unfold Iwing
  intro s hs
  have hst : 0 < Real.sqrt (s + t) := Real.sqrt_pos.mpr (by linarith [hs.1])
  have hsqt : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have harg : (Real.sqrt (s + t) + Real.sqrt s) / Real.sqrt t ≠ 0 :=
    (div_pos (by linarith [Real.sqrt_nonneg s]) hsqt).ne'
  have hc : ContinuousAt (fun r : ℝ => (Real.sqrt (r + t) + Real.sqrt r) / Real.sqrt t) s :=
    (((Real.continuous_sqrt.comp (continuous_id.add continuous_const)).add
      Real.continuous_sqrt).div_const _).continuousAt
  exact (continuousAt_const.mul (hc.log harg)).continuousWithinAt

lemma continuousOn_z2WingTS_s {t : ℝ} (ht : 0 < t) (b : ℝ) :
    ContinuousOn (fun s => z2WingTS t s) (Icc (0 : ℝ) b) := by
  unfold z2WingTS
  refine (continuousOn_const.mul (continuousOn_Iwing_s ht b)).add (continuousOn_const.mul ?_)
  refine Real.continuous_sqrt.continuousOn.div (continuousOn_const.mul
    (Real.continuous_sqrt.comp (continuous_id.add continuous_const)).continuousOn) ?_
  intro s hs
  exact mul_ne_zero (mul_ne_zero four_ne_zero ht.ne') (Real.sqrt_pos.mpr (by linarith [hs.1])).ne'

/-- Uniform bounds: `|∂_s z₂^{wing}| ≤ 4 ρ` and `|∂_t w^{wing}| ≤ 4 ρ` on the wing. -/
lemma dWing_abs_le {t s : ℝ} (ht : t0 ≤ t) (ht1 : t < 1) (hs : 0 < s) :
    |dz2WingTS t s| ≤ 4 * rho (s + t) s ∧ |dwWingTS t s| ≤ 4 * rho (s + t) s := by
  have ht0 : 0 < t := t0_pos.trans_le ht
  have ht925 : (9 : ℝ) / 25 ≤ t := t0_mem_bounds.1.le.trans ht
  have h1t : 0 < 1 - t := by linarith
  have hH0 := (Hwing_pos ht0 ht1).le
  have hH1 := Hwing_le_one_sub ht0 ht1
  have hσ0 : 0 < Real.sqrt (1 - t) := Real.sqrt_pos.mpr h1t
  have hσ1 : Real.sqrt (1 - t) < 1 := by rw [Real.sqrt_lt' zero_lt_one]; linarith
  have hσsq : Real.sqrt (1 - t) ^ 2 = 1 - t := Real.sq_sqrt h1t.le
  have hart := artanh_gt_self hσ0 hσ1
  have hgT : gT t = 1 / 2 * artanh (Real.sqrt (1 - t)) := rfl
  -- first coefficient
  have hden : 2 * t * (1 - t) ≤ 4 * t * Real.sqrt (1 - t) * gT t := by
    rw [hgT]; nlinarith [mul_pos ht0 hσ0, mul_pos (mul_pos ht0 hσ0) (sub_pos.mpr hart)]
  have hden0 : 0 < 4 * t * Real.sqrt (1 - t) * gT t := lt_of_lt_of_le (by positivity) hden
  have hc1_0 : 0 ≤ Hwing t / (4 * t * Real.sqrt (1 - t) * gT t) := div_nonneg hH0 hden0.le
  have hc1 : Hwing t / (4 * t * Real.sqrt (1 - t) * gT t) ≤ 25 / 18 := by
    rw [div_le_iff₀ hden0]; nlinarith
  -- second coefficient
  have hst : 0 < s + t := by linarith
  have hss : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have hsst : 0 < Real.sqrt (s + t) := Real.sqrt_pos.mpr hst
  have hrho : rho (s + t) s = 1 / (4 * (Real.sqrt (s + t) * Real.sqrt s)) := by
    unfold rho; rw [Real.sqrt_mul hst.le]
  have hrho0 : 0 < rho (s + t) s := by rw [hrho]; positivity
  have hc2_eq : Hwing t / (8 * Real.sqrt s * (s + t) * Real.sqrt (s + t)) =
      Hwing t / (2 * (s + t)) * rho (s + t) s := by
    rw [hrho]; field_simp; ring
  have hc2_0 : 0 ≤ Hwing t / (8 * Real.sqrt s * (s + t) * Real.sqrt (s + t)) := by
    rw [hc2_eq]; exact mul_nonneg (div_nonneg hH0 (by linarith)) hrho0.le
  have hc2 : Hwing t / (8 * Real.sqrt s * (s + t) * Real.sqrt (s + t)) ≤ 25 / 18 * rho (s + t) s := by
    rw [hc2_eq]
    refine mul_le_mul_of_nonneg_right ?_ hrho0.le
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < 2 * (s + t))]; nlinarith
  have hc1r := mul_le_mul_of_nonneg_right hc1 hrho0.le
  have hc1r0 := mul_nonneg hc1_0 hrho0.le
  unfold dz2WingTS dwWingTS
  constructor <;> rw [abs_le] <;> constructor <;> nlinarith

lemma measurable_dWing :
    Measurable (fun ab : Type2 => dz2WingTS (ab.1 - ab.2) ab.2) ∧
    Measurable (fun ab : Type2 => dwWingTS (ab.1 - ab.2) ab.2) ∧
    Measurable (fun ab : Type2 => wWingTS (ab.1 - ab.2) ab.2) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold dz2WingTS Hwing tailGT gT artanh rho; fun_prop
  · unfold dwWingTS Hwing tailGT gT artanh rho; fun_prop
  · unfold wWingTS Hwing tailGT gT artanh rho; fun_prop

/-- Fubini on the wing with the horizontal variable inside:
`∫_{W_+} F = ∫ s ∈ (0, 1 - t₀), ∫ t ∈ (t₀, 1 - s), F(s + t, s)`. -/
lemma setIntegral_wingPos_horiz {F : Type2 → ℝ} (hF : IntegrableOn F wingPos volume) :
    ∫ ab in wingPos, F ab =
      ∫ s in Ioo (0 : ℝ) (1 - t0), ∫ t in Ioo t0 (1 - s), F (s + t, s) := by
  have hInd : Integrable (wingPos.indicator F) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact (integrable_indicator_iff measurableSet_wingPos).mpr hF
  rw [← integral_indicator measurableSet_wingPos, Measure.volume_eq_prod,
    integral_prod_symm _ hInd, ← integral_indicator measurableSet_Ioo]
  refine integral_congr_ae (ae_of_all _ fun s => ?_)
  dsimp only
  have htrans : ∫ a, wingPos.indicator F (a, s) = ∫ t, wingPos.indicator F (s + t, s) :=
    (integral_add_left_eq_self (μ := volume) (fun a => wingPos.indicator F (a, s)) s).symm
  rw [htrans]
  by_cases hs : s ∈ Ioo (0 : ℝ) (1 - t0)
  · rw [indicator_of_mem hs, ← integral_indicator measurableSet_Ioo]
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    dsimp only
    by_cases ht : t ∈ Ioo t0 (1 - s)
    · have hm : ((s + t, s) : Type2) ∈ wingPos :=
        ⟨⟨⟨by linarith [hs.1, ht.1, t0_pos], by linarith [ht.2]⟩, ⟨hs.1, by linarith [hs.2, t0_pos]⟩⟩,
          (by show t0 < s + t - s; linarith [ht.1]), (by show s + t - s < 1; linarith [ht.2, hs.1])⟩
      rw [indicator_of_mem hm, indicator_of_mem ht]
    · have hm : ((s + t, s) : Type2) ∉ wingPos := fun h => ht
        ⟨by have h1 : t0 < s + t - s := h.2.1; linarith, by have h2 : s + t < 1 := h.1.1.2; linarith⟩
      rw [indicator_of_notMem hm, indicator_of_notMem ht]
  · rw [indicator_of_notMem hs]
    have hz : ∀ t, wingPos.indicator F (s + t, s) = 0 := fun t =>
      indicator_of_notMem (fun (h : ((s + t, s) : Type2) ∈ wingPos) => hs
        ⟨h.1.2.1, by have h1 : t0 < s + t - s := h.2.1; have h2 : s + t < 1 := h.1.1.2; linarith⟩) _
    simp_rw [hz]; simp


/-- Reusable integrability of the wing IBP integrand on `W_+`. -/
lemma integrableOn_wingPos_ibp (P : InterimProfile) :
    IntegrableOn (fun ab : Type2 =>
      P.g1 ab * z1WingTS (ab.1 - ab.2) ab.2 + P.g2 ab * z2WingTS (ab.1 - ab.2) ab.2 -
        P.u ab * rho ab.1 ab.2) wingPos volume := by
  let Cz : ℝ := 1 / (4 * t0) + 1 / (4 * t0 * Real.sqrt t0)
  let Umax : ℝ := P.u (0, 0) + 1
  have h0sq : ((0 : ℝ), (0 : ℝ)) ∈ unitSquare := ⟨⟨le_rfl, zero_le_one⟩, ⟨le_rfl, zero_le_one⟩⟩
  have hUmax : 0 ≤ Umax := by linarith [P.u_nonneg (0, 0) h0sq]
  have hCz : 0 ≤ Cz := by have := t0_pos; positivity
  have hdom : IntegrableOn (fun ab : Type2 => 2 * Cz + (1 + Umax) * rho ab.1 ab.2) wingPos volume := by
    have h1 : IntegrableOn (fun _ : Type2 => 2 * Cz) wingPos volume := by
      refine integrableOn_const (lt_of_le_of_lt (measure_mono Set.inter_subset_left) ?_).ne
      unfold openUnitSquare
      rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ioo]; norm_num
    have h2 : IntegrableOn (fun ab : Type2 => (1 + Umax) * rho ab.1 ab.2) wingPos volume :=
      (integrableOn_rho_openUnitSquare.mono_set Set.inter_subset_left).const_mul (1 + Umax)
    exact h1.add h2
  have hf_meas : AEStronglyMeasurable (fun ab : Type2 =>
      P.g1 ab * z1WingTS (ab.1 - ab.2) ab.2 + P.g2 ab * z2WingTS (ab.1 - ab.2) ab.2 -
        P.u ab * rho ab.1 ab.2) (volume.restrict wingPos) := by
    have hmu : AEStronglyMeasurable P.u (volume.restrict wingPos) :=
      P.u_aestronglyMeasurable.mono_measure (Measure.restrict_mono Set.inter_subset_left le_rfl)
    have hm_rho : Measurable (fun ab : Type2 => rho ab.1 ab.2) := by unfold rho; fun_prop
    have hm_H : Measurable (fun ab : Type2 => Hwing (ab.1 - ab.2)) := by
      unfold Hwing tailGT gT artanh; fun_prop
    have hm_z2 : Measurable (fun ab : Type2 => z2WingTS (ab.1 - ab.2) ab.2) := by
      unfold z2WingTS Hwing tailGT gT artanh Iwing; fun_prop
    have hm_z1 : Measurable (fun ab : Type2 => z1WingTS (ab.1 - ab.2) ab.2) := by
      unfold z1WingTS wWingTS; exact hm_z2.add (hm_H.mul (by unfold rho; fun_prop))
    exact ((P.g1_meas.mul hm_z1).add (P.g2_meas.mul hm_z2)).aestronglyMeasurable.sub
      (hmu.mul hm_rho.aestronglyMeasurable)
  refine hdom.mono' hf_meas ?_
  rw [ae_restrict_iff' measurableSet_wingPos]
  filter_upwards with ab hab
  simp only [wingPos, openUnitSquare, mem_inter_iff, mem_ofPred_eq, mem_prod, mem_Ioo] at hab
  have hsq : ab ∈ unitSquare := ⟨⟨hab.1.1.1.le, hab.1.1.2.le⟩, ⟨hab.1.2.1.le, hab.1.2.2.le⟩⟩
  have ht : t0 < ab.1 - ab.2 := hab.2.1
  have ht1 : ab.1 - ab.2 < 1 := hab.2.2
  have hz2 : |z2WingTS (ab.1 - ab.2) ab.2| ≤ Cz :=
    z2WingTS_abs_le ht.le ht1 hab.1.2.1.le (by linarith [hab.1.1.2])
  have hH_le : Hwing (ab.1 - ab.2) ≤ 1 := (Hwing_le_one_sub (t0_pos.trans ht) ht1).trans (by linarith [t0_pos])
  have hH_nn : 0 ≤ Hwing (ab.1 - ab.2) := (Hwing_pos (t0_pos.trans ht) ht1).le
  have hsum : ab.2 + (ab.1 - ab.2) = ab.1 := by ring
  have hz1 : |z1WingTS (ab.1 - ab.2) ab.2| ≤ Cz + rho ab.1 ab.2 := by
    unfold z1WingTS wWingTS
    rw [hsum]
    calc |z2WingTS (ab.1 - ab.2) ab.2 + Hwing (ab.1 - ab.2) * rho ab.1 ab.2|
        ≤ |z2WingTS (ab.1 - ab.2) ab.2| + Hwing (ab.1 - ab.2) * rho ab.1 ab.2 := by
          have := abs_add_le (z2WingTS (ab.1 - ab.2) ab.2) (Hwing (ab.1 - ab.2) * rho ab.1 ab.2)
          rwa [abs_of_nonneg (mul_nonneg hH_nn (rho_nonneg _ _))] at this
      _ ≤ Cz + 1 * rho ab.1 ab.2 :=
          add_le_add hz2 (mul_le_mul_of_nonneg_right hH_le (rho_nonneg _ _))
      _ = Cz + rho ab.1 ab.2 := by ring
  have hg1_nn := P.g1_nonneg ab hsq; have hg2_nn := P.g2_nonneg ab hsq
  have hg1_le : P.g1 ab ≤ 1 := by linarith [P.g_sum_le ab hsq]
  have hg2_le : P.g2 ab ≤ 1 := by linarith [P.g_sum_le ab hsq]
  have hu_nn := P.u_nonneg ab hsq; have hu_le : P.u ab ≤ Umax := P.u_le_bound hsq
  rw [Real.norm_eq_abs]
  calc |P.g1 ab * z1WingTS (ab.1 - ab.2) ab.2 + P.g2 ab * z2WingTS (ab.1 - ab.2) ab.2 - P.u ab * rho ab.1 ab.2|
      ≤ P.g1 ab * |z1WingTS (ab.1 - ab.2) ab.2| + P.g2 ab * |z2WingTS (ab.1 - ab.2) ab.2| + P.u ab * rho ab.1 ab.2 := by
        have h1 := abs_sub (P.g1 ab * z1WingTS (ab.1 - ab.2) ab.2 + P.g2 ab * z2WingTS (ab.1 - ab.2) ab.2)
          (P.u ab * rho ab.1 ab.2)
        have h2 := abs_add_le (P.g1 ab * z1WingTS (ab.1 - ab.2) ab.2) (P.g2 ab * z2WingTS (ab.1 - ab.2) ab.2)
        rw [abs_mul, abs_of_nonneg hu_nn, abs_of_nonneg (rho_nonneg _ _)] at h1
        rw [abs_mul, abs_mul, abs_of_nonneg hg1_nn, abs_of_nonneg hg2_nn] at h2
        linarith
    _ ≤ 1 * (Cz + rho ab.1 ab.2) + 1 * Cz + Umax * rho ab.1 ab.2 :=
        add_le_add
          (add_le_add (mul_le_mul hg1_le hz1 (abs_nonneg _) zero_le_one)
            (mul_le_mul hg2_le hz2 (abs_nonneg _) zero_le_one))
          (mul_le_mul_of_nonneg_right hu_le (rho_nonneg _ _))
    _ = 2 * Cz + (1 + Umax) * rho ab.1 ab.2 := by ring

/-- Reusable integrability of the `t = t₀` boundary integrand `s ↦ P.u (s + t0, s) * (t0 * rho (s + t0) s)`. -/
lemma integrableOn_bdy_t0 (P : InterimProfile) :
    IntegrableOn (fun s => P.u (s + t0, s) * (t0 * rho (s + t0) s)) (Ioo (0 : ℝ) (1 - t0)) volume := by
  let Umax : ℝ := P.u (0, 0) + 1
  have hdom : IntegrableOn (fun s => Umax * t0 * rho (s + t0) s) (Ioo (0 : ℝ) (1 - t0)) volume :=
    (integrableOn_rho_diag (s := 1 - t0) (by linarith [t0_lt_one]) t0_pos).const_mul (Umax * t0)
  have hmeas : AEStronglyMeasurable (fun s => P.u (s + t0, s) * (t0 * rho (s + t0) s))
      (volume.restrict (Ioo (0 : ℝ) (1 - t0))) := by
    have hc : ContinuousOn (fun s => P.u (s + t0, s)) (Ioo (0 : ℝ) (1 - t0)) :=
      P.u_continuousOn.comp ((continuous_id.add continuous_const).prodMk continuous_id).continuousOn
        (fun s hs => ⟨⟨by linarith [hs.1, t0_pos], by linarith [hs.2]⟩, ⟨hs.1.le, by linarith [hs.2, t0_pos]⟩⟩)
    have hm_rho : Measurable (fun s : ℝ => rho (s + t0) s) := by unfold rho; fun_prop
    exact hc.aestronglyMeasurable measurableSet_Ioo |>.mul
      (measurable_const.mul hm_rho).aestronglyMeasurable
  refine hdom.mono' hmeas ?_
  rw [ae_restrict_iff' measurableSet_Ioo]
  filter_upwards with s hs
  have hsq : (s + t0, s) ∈ unitSquare :=
    ⟨⟨by linarith [hs.1, t0_pos], by linarith [hs.2]⟩, ⟨hs.1.le, by linarith [hs.2, t0_pos]⟩⟩
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (P.u_nonneg _ hsq) (mul_nonneg t0_pos.le (rho_nonneg _ _)))]
  have hu_le : P.u (s + t0, s) ≤ Umax := P.u_le_bound hsq
  calc P.u (s + t0, s) * (t0 * rho (s + t0) s)
      ≤ Umax * (t0 * rho (s + t0) s) := mul_le_mul_of_nonneg_right hu_le (mul_nonneg t0_pos.le (rho_nonneg _ _))
    _ = Umax * t0 * rho (s + t0) s := by ring

/-- Lemma 4(4) identity on the upper wing `W_+`. Exact integration by parts along each diagonal
(for `z₂^{wing}`) and along each horizontal line (for `w^{wing}`), with no truncation and no
limit: `z₂^{wing}` vanishes on `s = 0`, the two contributions on the edge `a = 1` cancel under
`s = 1 - t`, and the derivatives are dominated by `4 ρ`. -/
lemma wingPos_ibp_identity (P : InterimProfile) :
    (∫ ab in wingPos, (P.g1 ab * z1WingTS (ab.1 - ab.2) ab.2 +
        P.g2 ab * z2WingTS (ab.1 - ab.2) ab.2 - P.u ab * rho ab.1 ab.2)) =
    -(∫ s in Ioo (0 : ℝ) (1 - t0), P.u (s + t0, s) * (t0 * rho (s + t0) s)) := by
  have ht0 := t0_pos
  have ht1 := t0_lt_one
  let Umax : ℝ := P.u (0, 0) + 1
  let Aab : Type2 → ℝ := fun ab =>
    (P.g1 ab + P.g2 ab) * z2WingTS (ab.1 - ab.2) ab.2 + P.u ab * dz2WingTS (ab.1 - ab.2) ab.2
  let Bab : Type2 → ℝ := fun ab =>
    P.g1 ab * wWingTS (ab.1 - ab.2) ab.2 + P.u ab * dwWingTS (ab.1 - ab.2) ab.2
  let E : ℝ → ℝ := fun s => P.u (1, s) * (Hwing (1 - s) * rho 1 s)
  have hsplit_pt : ∀ ab : Type2,
      P.g1 ab * z1WingTS (ab.1 - ab.2) ab.2 + P.g2 ab * z2WingTS (ab.1 - ab.2) ab.2 -
        P.u ab * rho ab.1 ab.2 = Aab ab + Bab ab := by
    intro ab
    have hpde := wing_pde_ts (ab.1 - ab.2) ab.2
    have hrho : rho (ab.2 + (ab.1 - ab.2)) ab.2 = rho ab.1 ab.2 := by
      rw [show ab.2 + (ab.1 - ab.2) = ab.1 by ring]
    show _ = ((P.g1 ab + P.g2 ab) * z2WingTS (ab.1 - ab.2) ab.2 +
        P.u ab * dz2WingTS (ab.1 - ab.2) ab.2) +
      (P.g1 ab * wWingTS (ab.1 - ab.2) ab.2 + P.u ab * dwWingTS (ab.1 - ab.2) ab.2)
    unfold z1WingTS dz2WingTS dwWingTS
    linear_combination (-P.u ab) * hpde + (P.u ab) * hrho
  have hsq_of : ∀ ab ∈ wingPos, ab ∈ unitSquare := fun ab hab =>
    ⟨Ioo_subset_Icc_self hab.1.1, Ioo_subset_Icc_self hab.1.2⟩
  have hf_int := integrableOn_wingPos_ibp P
  have hu_meas : AEStronglyMeasurable P.u (volume.restrict wingPos) :=
    P.u_aestronglyMeasurable.mono_measure (Measure.restrict_mono Set.inter_subset_left le_rfl)
  have hB_int : IntegrableOn Bab wingPos volume := by
    have hdom : IntegrableOn (fun ab : Type2 => (1 + 4 * Umax) * rho ab.1 ab.2) wingPos volume :=
      (integrableOn_rho_openUnitSquare.mono_set Set.inter_subset_left).const_mul _
    have hmeas : AEStronglyMeasurable Bab (volume.restrict wingPos) :=
      (P.g1_meas.mul measurable_dWing.2.2).aestronglyMeasurable.add
        (hu_meas.mul measurable_dWing.2.1.aestronglyMeasurable)
    refine hdom.mono' hmeas ?_
    rw [ae_restrict_iff' measurableSet_wingPos]; filter_upwards with ab hab
    have hsq := hsq_of ab hab
    have hT0 : t0 ≤ ab.1 - ab.2 := le_of_lt hab.2.1
    have hT1 : ab.1 - ab.2 < 1 := hab.2.2
    have hTp : 0 < ab.1 - ab.2 := ht0.trans_le hT0
    have hs0 : 0 < ab.2 := hab.1.2.1
    have hrr : rho (ab.2 + (ab.1 - ab.2)) ab.2 = rho ab.1 ab.2 := by
      rw [show ab.2 + (ab.1 - ab.2) = ab.1 by ring]
    have hdw := (dWing_abs_le hT0 hT1 hs0).2
    rw [hrr] at hdw
    have hr0 := rho_nonneg ab.1 ab.2
    have hw0 : 0 ≤ wWingTS (ab.1 - ab.2) ab.2 := by
      unfold wWingTS; rw [hrr]; exact mul_nonneg (Hwing_pos hTp hT1).le hr0
    have hw1 : wWingTS (ab.1 - ab.2) ab.2 ≤ rho ab.1 ab.2 := by
      unfold wWingTS; rw [hrr]
      have := Hwing_le_one_sub hTp hT1
      nlinarith
    have hg1 := P.g1_nonneg ab hsq; have hg2 := P.g2_nonneg ab hsq; have hgs := P.g_sum_le ab hsq
    have hu0 := P.u_nonneg ab hsq; have hu1 : P.u ab ≤ Umax := P.u_le_bound hsq
    have h1 : |P.g1 ab * wWingTS (ab.1 - ab.2) ab.2| ≤ rho ab.1 ab.2 := by
      rw [abs_of_nonneg (mul_nonneg hg1 hw0)]; nlinarith
    have h2 : |P.u ab * dwWingTS (ab.1 - ab.2) ab.2| ≤ 4 * Umax * rho ab.1 ab.2 := by
      rw [abs_mul, abs_of_nonneg hu0]; nlinarith [abs_nonneg (dwWingTS (ab.1 - ab.2) ab.2)]
    rw [Real.norm_eq_abs]
    calc |Bab ab| ≤ |P.g1 ab * wWingTS (ab.1 - ab.2) ab.2| +
          |P.u ab * dwWingTS (ab.1 - ab.2) ab.2| := abs_add_le _ _
      _ ≤ (1 + 4 * Umax) * rho ab.1 ab.2 := by linarith
  have hA_int : IntegrableOn Aab wingPos volume := by
    have h2 : IntegrableOn (fun ab : Type2 =>
        (P.g1 ab * z1WingTS (ab.1 - ab.2) ab.2 + P.g2 ab * z2WingTS (ab.1 - ab.2) ab.2 -
          P.u ab * rho ab.1 ab.2) - Bab ab) wingPos volume := hf_int.sub hB_int
    refine h2.congr_fun (fun ab _ => ?_) measurableSet_wingPos
    show _ - Bab ab = Aab ab
    rw [hsplit_pt ab]; ring
  have hI : (∫ ab in wingPos, (P.g1 ab * z1WingTS (ab.1 - ab.2) ab.2 +
        P.g2 ab * z2WingTS (ab.1 - ab.2) ab.2 - P.u ab * rho ab.1 ab.2)) =
      (∫ ab in wingPos, Aab ab) + ∫ ab in wingPos, Bab ab := by
    rw [← integral_add hA_int hB_int]
    exact setIntegral_congr_fun measurableSet_wingPos (fun ab _ => hsplit_pt ab)
  -- the diagonal part
  have hw_eq : wingPos =
      {ab : Type2 | ab ∈ openUnitSquare ∧ t0 < ab.1 - ab.2 ∧ ab.1 - ab.2 < 1} := by
    ext ab; simp only [wingPos, mem_inter_iff, mem_ofPred_eq]
  have hA_shear : ∫ ab in wingPos, Aab ab =
      ∫ t in Ioo t0 1, ∫ s in Ioo (0 : ℝ) (1 - t), Aab (s + t, s) := by
    rw [hw_eq]
    exact setIntegral_shear_upper ht0.le ht1.le le_rfl (by rwa [← hw_eq])
  have hA_t : ∀ t ∈ Ioo t0 1, ∫ s in Ioo (0 : ℝ) (1 - t), Aab (s + t, s) = -E (1 - t) := by
    intro t ht
    have htp : 0 < t := ht0.trans ht.1
    have hb : 0 ≤ 1 - t := by linarith [ht.2]
    have hdz_int : IntegrableOn (fun s => dz2WingTS t s) (Ioo (0 : ℝ) (1 - t)) volume := by
      refine ((integrableOn_rho_diag hb htp).const_mul 4).mono'
        (by unfold dz2WingTS Hwing tailGT gT artanh rho; fun_prop : Measurable fun s => dz2WingTS t s).aestronglyMeasurable ?_
      rw [ae_restrict_iff' measurableSet_Ioo]; filter_upwards with s hs
      rw [Real.norm_eq_abs]; exact (dWing_abs_le ht.1.le ht.2 hs.1).1
    have hibp := subgrad_ibp_of_integrable hb (P.diagSubgrad htp.le le_rfl le_rfl)
      (φ := fun s => z2WingTS t s) (φ' := fun s => dz2WingTS t s)
      (continuousOn_z2WingTS_s htp _) hdz_int
      (fun s hs => hasDerivAt_z2WingTS_s htp ht.2 hs.1)
    have h1 : 1 - t + t = 1 := by ring
    have hbd : z2WingTS t (1 - t) = -(Hwing t * rho 1 (1 - t)) := by
      have hz := z1WingTS_boundary_a1 htp ht.2
      unfold z1WingTS wWingTS at hz
      rw [h1] at hz
      linarith
    rw [z2WingTS_zero htp, mul_zero, sub_zero, h1, hbd] at hibp
    have hcongr : ∫ s in Ioo (0 : ℝ) (1 - t), Aab (s + t, s) =
        ∫ s in Ioo (0 : ℝ) (1 - t), ((P.g1 (s + t, s) + P.g2 (s + t, s)) * z2WingTS t s +
          P.u (s + t, s) * dz2WingTS t s) := by
      refine setIntegral_congr_fun measurableSet_Ioo (fun s _ => ?_)
      show (P.g1 (s + t, s) + P.g2 (s + t, s)) * z2WingTS (s + t - s) s +
        P.u (s + t, s) * dz2WingTS (s + t - s) s = _
      rw [add_sub_cancel_left]
    rw [hcongr, hibp]
    show _ = -(P.u (1, 1 - t) * (Hwing (1 - (1 - t)) * rho 1 (1 - t)))
    rw [sub_sub_cancel]; ring
  -- the horizontal part
  have hB_horiz := setIntegral_wingPos_horiz hB_int
  have hB_s : ∀ s ∈ Ioo (0 : ℝ) (1 - t0), ∫ t in Ioo t0 (1 - s), Bab (s + t, s) =
      E s - P.u (s + t0, s) * (t0 * rho (s + t0) s) := by
    intro s hs
    have hab : t0 ≤ 1 - s := by linarith [hs.2]
    have hdw_int : IntegrableOn (fun t => dwWingTS t s) (Ioo t0 (1 - s)) volume := by
      refine (integrableOn_const (C := 1 / s)
        (hs := by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)).mono'
        (by unfold dwWingTS Hwing tailGT gT artanh rho; fun_prop : Measurable fun t => dwWingTS t s).aestronglyMeasurable ?_
      rw [ae_restrict_iff' measurableSet_Ioo]; filter_upwards with t ht
      have hd := (dWing_abs_le ht.1.le (by linarith [ht.2, hs.1]) hs.1).2
      have hst : 0 < s + t := by linarith [hs.1, ht.1]
      have hrle : rho (s + t) s ≤ 1 / (4 * s) := by
        unfold rho
        apply one_div_le_one_div_of_le (by linarith [hs.1])
        have : s ≤ Real.sqrt ((s + t) * s) := by
          rw [Real.le_sqrt' hs.1]; nlinarith [hs.1, ht.1]
        linarith
      rw [Real.norm_eq_abs]
      calc |dwWingTS t s| ≤ 4 * rho (s + t) s := hd
        _ ≤ 4 * (1 / (4 * s)) := by linarith
        _ = 1 / s := by field_simp
    have hibp := subgrad_ibp_of_integrable hab (P.horizSubgrad hs.1.le ht0.le le_rfl)
      (φ := fun t => wWingTS t s) (φ' := fun t => dwWingTS t s)
      (fun t ht => (hasDerivAt_wWingTS_t (ht0.trans_le ht.1) (by linarith [ht.2, hs.1])
        hs.1).continuousAt.continuousWithinAt) hdw_int
      (fun t ht => hasDerivAt_wWingTS_t (ht0.trans ht.1) (by linarith [ht.2, hs.1]) hs.1)
    have h1 : s + (1 - s) = 1 := by ring
    have hw1 : wWingTS (1 - s) s = Hwing (1 - s) * rho 1 s := by unfold wWingTS; rw [h1]
    rw [wWingTS_t0, h1, hw1] at hibp
    have hcongr : ∫ t in Ioo t0 (1 - s), Bab (s + t, s) =
        ∫ t in Ioo t0 (1 - s), (P.g1 (s + t, s) * wWingTS t s + P.u (s + t, s) * dwWingTS t s) := by
      refine setIntegral_congr_fun measurableSet_Ioo (fun t _ => ?_)
      show P.g1 (s + t, s) * wWingTS (s + t - s) s + P.u (s + t, s) * dwWingTS (s + t - s) s = _
      rw [add_sub_cancel_left]
    rw [hcongr, hibp]
  -- the edge `a = 1`
  have hE_int : IntegrableOn E (Ioo (0 : ℝ) (1 - t0)) volume := by
    have hc : ContinuousOn (fun s : ℝ => P.u (1, s)) (Ioo (0 : ℝ) (1 - t0)) :=
      P.u_continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
        (fun s hs => ⟨⟨zero_le_one, le_rfl⟩, ⟨hs.1.le, by linarith [hs.2]⟩⟩)
    have hmH : Measurable (fun s : ℝ => Hwing (1 - s) * rho 1 s) := by
      unfold Hwing tailGT gT artanh rho; fun_prop
    refine (integrableOn_const (C := Umax)
      (hs := by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)).mono'
      ((hc.aestronglyMeasurable measurableSet_Ioo).mul hmH.aestronglyMeasurable) ?_
    rw [ae_restrict_iff' measurableSet_Ioo]; filter_upwards with s hs
    have hsq : ((1 : ℝ), s) ∈ unitSquare := ⟨⟨zero_le_one, le_rfl⟩, ⟨hs.1.le, by linarith [hs.2]⟩⟩
    have hu0 := P.u_nonneg _ hsq; have hu1 : P.u (1, s) ≤ Umax := P.u_le_bound hsq
    have hH0 := (Hwing_pos (by linarith [hs.2] : (0 : ℝ) < 1 - s) (by linarith [hs.1])).le
    have hH1 := Hwing_le_one_sub (by linarith [hs.2] : (0 : ℝ) < 1 - s) (by linarith [hs.1])
    have hss : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs.1
    have hsle : s ≤ Real.sqrt s := by rw [Real.le_sqrt' hs.1]; nlinarith [hs.1, hs.2]
    have hr : rho 1 s = 1 / (4 * Real.sqrt s) := by unfold rho; rw [one_mul]
    have hprod0 : 0 ≤ Hwing (1 - s) * rho 1 s := mul_nonneg hH0 (rho_nonneg _ _)
    have hprod1 : Hwing (1 - s) * rho 1 s ≤ 1 := by
      rw [hr, mul_one_div, div_le_one (by linarith)]; linarith
    show ‖P.u (1, s) * (Hwing (1 - s) * rho 1 s)‖ ≤ Umax
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hu0 hprod0)]
    nlinarith
  have hreflect : ∫ t in Ioo t0 1, E (1 - t) = ∫ s in Ioo (0 : ℝ) (1 - t0), E s := by
    have hsub := intervalIntegral.integral_comp_sub_left (a := t0) (b := 1) E 1
    rw [sub_self, intervalIntegral.integral_of_le ht1.le,
      intervalIntegral.integral_of_le (by linarith : (0 : ℝ) ≤ 1 - t0),
      ← setIntegral_congr_set Ioo_ae_eq_Ioc, ← setIntegral_congr_set Ioo_ae_eq_Ioc] at hsub
    exact hsub
  rw [hI, hA_shear, hB_horiz, setIntegral_congr_fun measurableSet_Ioo hA_t,
    setIntegral_congr_fun measurableSet_Ioo hB_s, integral_neg, hreflect,
    integral_sub hE_int (integrableOn_bdy_t0 P)]
  ring


/-- The open unit square agrees almost everywhere with `(wingPos ∪ wingNeg) ∪ stripSet`
(the two boundary lines `a - b = ±t₀` have measure zero). -/
lemma ae_eq_wing_union_strip :
    (openUnitSquare : Set Type2) =ᵐ[volume] ((wingPos ∪ wingNeg) ∪ stripSet) := by
  apply MeasureTheory.ae_eq_set.mpr
  constructor
  · have hsub : openUnitSquare \ ((wingPos ∪ wingNeg) ∪ stripSet) ⊆
        {ab : Type2 | ab.1 - ab.2 = t0} ∪ {ab : Type2 | ab.1 - ab.2 = -t0} := by
      intro ab hab
      simp only [Set.mem_diff, mem_union, wingPos, wingNeg, stripSet, mem_inter_iff, mem_ofPred_eq, not_or] at hab ⊢
      by_contra hne
      push Not at hne
      have hsq : ab ∈ openUnitSquare := hab.1
      rcases lt_or_gt_of_ne hne.1 with hlt | hgt
      · rcases lt_or_gt_of_ne hne.2 with hlt2 | hgt2
        · exact hab.2.1.2 ⟨hsq, by linarith, by linarith [hsq.1.1, hsq.2.2]⟩
        · exact hab.2.2 ⟨hsq, hgt2, hlt⟩
      · exact hab.2.1.1 ⟨hsq, hgt, by linarith [hsq.1.2, hsq.2.1]⟩
    exact measure_mono_null hsub
      (measure_union_null (volume_diff_eq_const_zero t0) (volume_diff_eq_const_zero (-t0)))
  · have : ((wingPos ∪ wingNeg) ∪ stripSet) \ openUnitSquare = ∅ := by
      ext ab; simp [wingPos, wingNeg, stripSet]; tauto
    rw [this]; simp

/-- Full Lemma 4(4) Decomposition over `[0, 1]² = S ∪ W_+ ∪ W_-` for EVERY `InterimProfile` `P`! -/
theorem lemma4_wing_decomposition (L : ℝ) (P : InterimProfile) :
    (∫ ab in openUnitSquare, ((L + ab.1) * P.g1 ab + (L + ab.2) * P.g2 ab - P.u ab) * rho ab.1 ab.2) =
    (∫ ab in (wingPos ∪ wingNeg), (phi1Wing L ab * P.g1 ab + phi2Wing L ab * P.g2 ab) * rho ab.1 ab.2) +
    stripFunctional L P := by
  let revInt : Type2 → ℝ := fun ab => ((L + ab.1) * P.g1 ab + (L + ab.2) * P.g2 ab - P.u ab) * rho ab.1 ab.2
  have hrev_int : IntegrableOn revInt openUnitSquare volume := by
    have hdom := integrableOn_rho_openUnitSquare.const_mul (|L| + 1 + (P.u (0, 0) + 1))
    have hmeas : AEStronglyMeasurable revInt (volume.restrict openUnitSquare) := by
      have hm1 : Measurable (fun ab : Type2 => (L + ab.1) * P.g1 ab + (L + ab.2) * P.g2 ab) :=
        ((measurable_const.add measurable_fst).mul P.g1_meas).add
          ((measurable_const.add measurable_snd).mul P.g2_meas)
      have hm_rho : Measurable (fun ab : Type2 => rho ab.1 ab.2) := by unfold rho; fun_prop
      exact (hm1.aestronglyMeasurable.sub P.u_aestronglyMeasurable).mul hm_rho.aestronglyMeasurable
    refine hdom.mono' hmeas ?_
    rw [ae_restrict_iff' measurableSet_openUnitSquare]
    filter_upwards with ab hab
    have hsq : ab ∈ unitSquare := ⟨Ioo_subset_Icc_self hab.1, Ioo_subset_Icc_self hab.2⟩
    have hg1 := P.g1_nonneg ab hsq; have hg2 := P.g2_nonneg ab hsq; have hgs := P.g_sum_le ab hsq
    have hu_nn := P.u_nonneg ab hsq; have hu_le := P.u_le_bound hsq
    have hval : |(L + ab.1) * P.g1 ab + (L + ab.2) * P.g2 ab| ≤ |L| + 1 := by
      calc |(L + ab.1) * P.g1 ab + (L + ab.2) * P.g2 ab|
          ≤ |(L + ab.1) * P.g1 ab| + |(L + ab.2) * P.g2 ab| := abs_add_le _ _
        _ = |L + ab.1| * P.g1 ab + |L + ab.2| * P.g2 ab := by
            rw [abs_mul, abs_mul, abs_of_nonneg hg1, abs_of_nonneg hg2]
        _ ≤ (|L| + 1) * P.g1 ab + (|L| + 1) * P.g2 ab := by
            have h1 : |L + ab.1| ≤ |L| + 1 := by
              calc |L + ab.1| ≤ |L| + |ab.1| := abs_add_le _ _
                _ = |L| + ab.1 := by rw [abs_of_nonneg hsq.1.1]
                _ ≤ |L| + 1 := by linarith [hsq.1.2]
            have h2 : |L + ab.2| ≤ |L| + 1 := by
              calc |L + ab.2| ≤ |L| + |ab.2| := abs_add_le _ _
                _ = |L| + ab.2 := by rw [abs_of_nonneg hsq.2.1]
                _ ≤ |L| + 1 := by linarith [hsq.2.2]
            gcongr
        _ ≤ (|L| + 1) * 1 := by nlinarith [abs_nonneg L]
        _ = |L| + 1 := mul_one _
    rw [Real.norm_eq_abs]
    dsimp only [revInt]
    rw [abs_mul, abs_of_nonneg (rho_nonneg _ _)]
    have hsub : |(L + ab.1) * P.g1 ab + (L + ab.2) * P.g2 ab - P.u ab| ≤ |L| + 1 + (P.u (0, 0) + 1) := by
      calc _ ≤ |(L + ab.1) * P.g1 ab + (L + ab.2) * P.g2 ab| + |P.u ab| := abs_sub _ _
        _ = |(L + ab.1) * P.g1 ab + (L + ab.2) * P.g2 ab| + P.u ab := by rw [abs_of_nonneg hu_nn]
        _ ≤ |L| + 1 + (P.u (0, 0) + 1) := by linarith
    exact mul_le_mul_of_nonneg_right hsub (rho_nonneg _ _)
  have hae_part := ae_eq_wing_union_strip
  have hdisj_ws : Disjoint (wingPos ∪ wingNeg) stripSet :=
    Set.disjoint_left.mpr (fun ab h1 h2 => by
      simp only [mem_union, wingPos, wingNeg, stripSet, mem_inter_iff, mem_ofPred_eq] at h1 h2
      rcases h1 with hp | hm
      · linarith [hp.2.1, h2.2.2]
      · linarith [hm.2.1, h2.2.1])
  have hdisj_pm : Disjoint wingPos wingNeg :=
    Set.disjoint_left.mpr (fun ab h1 h2 => by
      simp only [wingPos, wingNeg, mem_inter_iff, mem_ofPred_eq] at h1 h2
      linarith [h1.2.1, h2.2.1, t0_pos])
  rw [setIntegral_congr_set hae_part,
      setIntegral_union hdisj_ws measurableSet_stripSet
        (hrev_int.mono_set (union_subset Set.inter_subset_left Set.inter_subset_left))
        (hrev_int.mono_set Set.inter_subset_left),
      setIntegral_union hdisj_pm measurableSet_wingNeg
        (hrev_int.mono_set Set.inter_subset_left) (hrev_int.mono_set Set.inter_subset_left)]
  have hdiff_int : IntegrableOn (fun ab : Type2 =>
      P.g1 ab * z1WingTS (ab.1 - ab.2) ab.2 + P.g2 ab * z2WingTS (ab.1 - ab.2) ab.2 - P.u ab * rho ab.1 ab.2)
      wingPos volume := integrableOn_wingPos_ibp P
  have hpt_wp : ∀ ab ∈ wingPos,
      revInt ab - (P.g1 ab * z1WingTS (ab.1 - ab.2) ab.2 + P.g2 ab * z2WingTS (ab.1 - ab.2) ab.2 - P.u ab * rho ab.1 ab.2) =
      (phi1Wing L ab * P.g1 ab + phi2Wing L ab * P.g2 ab) * rho ab.1 ab.2 := by
    intro ab hab
    have ht : t0 < ab.1 - ab.2 := hab.2.1
    have hrho : rho ab.1 ab.2 ≠ 0 := (rho_pos hab.1.1.1 hab.1.2.1).ne'
    dsimp only [revInt]; unfold phi1Wing phi2Wing
    rw [ite_eq_left ht, ite_eq_left ht]
    field_simp [hrho]
    ring
  have hWp_eq : ∫ ab in wingPos, revInt ab =
      (∫ ab in wingPos, (phi1Wing L ab * P.g1 ab + phi2Wing L ab * P.g2 ab) * rho ab.1 ab.2) -
      (∫ s in Ioo (0 : ℝ) (1 - t0), P.u (s + t0, s) * (t0 * rho (s + t0) s)) := by
    have hibp := wingPos_ibp_identity P
    have hrev_wp : IntegrableOn revInt wingPos volume := hrev_int.mono_set Set.inter_subset_left
    have hEq := setIntegral_congr_fun (μ := volume) measurableSet_wingPos hpt_wp
    rw [integral_sub hrev_wp hdiff_int, hibp] at hEq
    linarith
  have hmp := Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
  have hswap_mem : ∀ a b : ℝ, (a, b) ∈ wingPos ↔ (b, a) ∈ wingNeg := by
    intro a b
    simp only [wingPos, wingNeg, openUnitSquare, mem_inter_iff, mem_ofPred_eq, mem_prod, mem_Ioo]
    tauto
  have hswap_int : ∀ F : Type2 → ℝ,
      (∫ ab in wingNeg, F ab) = ∫ ab in wingPos, F (ab.2, ab.1) := by
    intro F
    rw [← integral_indicator measurableSet_wingNeg, ← integral_indicator measurableSet_wingPos,
        Measure.volume_eq_prod,
        ← hmp.integral_comp MeasurableEquiv.prodComm.measurableEmbedding (wingNeg.indicator F)]
    congr 1; ext ⟨a, b⟩
    by_cases h : (a, b) ∈ wingPos
    · have hs : (b, a) ∈ wingNeg := (hswap_mem a b).mp h
      simp only [Function.comp_apply, Prod.swap_prod_mk, indicator_of_mem hs, indicator_of_mem h]
    · have hs : (b, a) ∉ wingNeg := mt (hswap_mem a b).mpr h
      simp only [Function.comp_apply, Prod.swap_prod_mk, indicator_of_notMem hs, indicator_of_notMem h]
  have hWm_eq : ∫ ab in wingNeg, revInt ab =
      (∫ ab in wingNeg, (phi1Wing L ab * P.g1 ab + phi2Wing L ab * P.g2 ab) * rho ab.1 ab.2) -
      (∫ s in Ioo (0 : ℝ) (1 - t0), P.u (s, s + t0) * (t0 * rho (s + t0) s)) := by
    rw [hswap_int revInt, hswap_int (fun ab => (phi1Wing L ab * P.g1 ab + phi2Wing L ab * P.g2 ab) * rho ab.1 ab.2)]
    have hibp_swap := wingPos_ibp_identity P.swap
    have hrev_swap : ∀ ab ∈ wingPos,
        revInt (ab.2, ab.1) -
          (P.swap.g1 ab * z1WingTS (ab.1 - ab.2) ab.2 + P.swap.g2 ab * z2WingTS (ab.1 - ab.2) ab.2 -
            P.swap.u ab * rho ab.1 ab.2) =
        (phi1Wing L (ab.2, ab.1) * P.g1 (ab.2, ab.1) + phi2Wing L (ab.2, ab.1) * P.g2 (ab.2, ab.1)) *
          rho ab.2 ab.1 := by
      intro ab hab
      have ht : t0 < ab.1 - ab.2 := hab.2.1
      have hnot : ¬ t0 < ab.2 - ab.1 := by linarith [t0_pos]
      have hrho : rho ab.1 ab.2 ≠ 0 := (rho_pos hab.1.1.1 hab.1.2.1).ne'
      have hrho_comm : rho ab.2 ab.1 = rho ab.1 ab.2 := by unfold rho; rw [mul_comm ab.2 ab.1]
      dsimp only [revInt, InterimProfile.swap]; unfold phi1Wing phi2Wing
      rw [ite_eq_right hnot, ite_eq_left ht, ite_eq_right hnot, ite_eq_left ht, hrho_comm]
      field_simp [hrho]
      ring
    have hrev_swap_int : IntegrableOn (fun ab : Type2 => revInt (ab.2, ab.1)) wingPos volume := by
      rw [← integrable_indicator_iff measurableSet_wingPos, Measure.volume_eq_prod]
      have hi := (integrable_indicator_iff measurableSet_wingNeg).mpr (hrev_int.mono_set Set.inter_subset_left)
      rw [Measure.volume_eq_prod] at hi
      have hc := (hmp.integrable_comp_emb MeasurableEquiv.prodComm.measurableEmbedding).mpr hi
      refine hc.congr (ae_of_all _ (fun ⟨a, b⟩ => ?_))
      by_cases h : (a, b) ∈ wingPos
      · have hs : (b, a) ∈ wingNeg := (hswap_mem a b).mp h
        simp only [Function.comp_apply, Prod.swap_prod_mk, indicator_of_mem hs, indicator_of_mem h]
      · have hs : (b, a) ∉ wingNeg := mt (hswap_mem a b).mpr h
        simp only [Function.comp_apply, Prod.swap_prod_mk, indicator_of_notMem hs, indicator_of_notMem h]
    have hdiff_swap_int := integrableOn_wingPos_ibp P.swap
    have hEq := setIntegral_congr_fun (μ := volume) measurableSet_wingPos hrev_swap
    rw [integral_sub hrev_swap_int hdiff_swap_int, hibp_swap] at hEq
    dsimp only [InterimProfile.swap] at hEq
    linarith
  have hphi_int_p : IntegrableOn (fun ab => (phi1Wing L ab * P.g1 ab + phi2Wing L ab * P.g2 ab) * rho ab.1 ab.2)
      wingPos volume :=
    ((hrev_int.mono_set Set.inter_subset_left).sub hdiff_int).congr_fun hpt_wp measurableSet_wingPos
  have hphi_int_m : IntegrableOn (fun ab => (phi1Wing L ab * P.g1 ab + phi2Wing L ab * P.g2 ab) * rho ab.1 ab.2)
      wingNeg volume := by
    have hphi_swap_wp : IntegrableOn
        (fun ab : Type2 => (phi1Wing L (ab.2, ab.1) * P.g1 (ab.2, ab.1) + phi2Wing L (ab.2, ab.1) * P.g2 (ab.2, ab.1)) *
          rho ab.2 ab.1) wingPos volume := by
      have hrev_sw_int : IntegrableOn (fun ab : Type2 => revInt (ab.2, ab.1)) wingPos volume := by
        rw [← integrable_indicator_iff measurableSet_wingPos, Measure.volume_eq_prod]
        have hi := (integrable_indicator_iff measurableSet_wingNeg).mpr (hrev_int.mono_set Set.inter_subset_left)
        rw [Measure.volume_eq_prod] at hi
        refine ((hmp.integrable_comp_emb MeasurableEquiv.prodComm.measurableEmbedding).mpr hi).congr
          (ae_of_all _ (fun ⟨a, b⟩ => ?_))
        by_cases h : (a, b) ∈ wingPos
        · simp only [Function.comp_apply, Prod.swap_prod_mk, indicator_of_mem ((hswap_mem a b).mp h), indicator_of_mem h]
        · simp only [Function.comp_apply, Prod.swap_prod_mk, indicator_of_notMem (mt (hswap_mem a b).mpr h), indicator_of_notMem h]
      refine (hrev_sw_int.sub (integrableOn_wingPos_ibp P.swap)).congr_fun (fun ab hab => ?_) measurableSet_wingPos
      have ht : t0 < ab.1 - ab.2 := hab.2.1
      have hnot : ¬ t0 < ab.2 - ab.1 := by linarith [t0_pos]
      have hrho : rho ab.1 ab.2 ≠ 0 := (rho_pos hab.1.1.1 hab.1.2.1).ne'
      have hrho_comm : rho ab.2 ab.1 = rho ab.1 ab.2 := by unfold rho; rw [mul_comm ab.2 ab.1]
      simp only [Pi.sub_apply, revInt, InterimProfile.swap, phi1Wing, phi2Wing,
        ite_eq_right hnot, ite_eq_left ht, hrho_comm]
      field_simp [hrho]; ring
    rw [← integrable_indicator_iff measurableSet_wingNeg, Measure.volume_eq_prod]
    have hi := (integrable_indicator_iff measurableSet_wingPos).mpr hphi_swap_wp
    rw [Measure.volume_eq_prod] at hi
    refine ((hmp.integrable_comp_emb MeasurableEquiv.prodComm.measurableEmbedding).mpr hi).congr
      (ae_of_all _ (fun ⟨a, b⟩ => ?_))
    by_cases h : (a, b) ∈ wingNeg
    · simp only [Function.comp_apply, Prod.swap_prod_mk, indicator_of_mem ((hswap_mem b a).mpr h), indicator_of_mem h]
    · simp only [Function.comp_apply, Prod.swap_prod_mk, indicator_of_notMem (mt (hswap_mem b a).mp h), indicator_of_notMem h]
  have hbdy_int_p := integrableOn_bdy_t0 P
  have hbdy_int_m : IntegrableOn (fun s => P.u (s, s + t0) * (t0 * rho (s + t0) s)) (Ioo (0 : ℝ) (1 - t0)) volume :=
    integrableOn_bdy_t0 P.swap
  rw [hWp_eq, hWm_eq, setIntegral_union hdisj_pm measurableSet_wingNeg hphi_int_p hphi_int_m]
  unfold stripFunctional
  have hbdy_add : (∫ s in Ioo (0 : ℝ) (1 - t0), P.u (s + t0, s) * (t0 * rho (s + t0) s)) +
      (∫ s in Ioo (0 : ℝ) (1 - t0), P.u (s, s + t0) * (t0 * rho (s + t0) s)) =
      ∫ s in Ioo (0 : ℝ) (1 - t0), (P.u (s + t0, s) + P.u (s, s + t0)) * (t0 * rho (s + t0) s) := by
    rw [← integral_add hbdy_int_p hbdy_int_m]
    refine setIntegral_congr_fun measurableSet_Ioo (fun s _ => by ring)
  dsimp only [revInt]
  linarith

end

end EconCSAuction
