import OrtegaCerdaMultipliers.Foundations.Basic
import OrtegaCerdaMultipliers.Foundations.Pompeiu
import OrtegaCerdaMultipliers.Foundations.Polar
import OrtegaCerdaMultipliers.Foundations.DiscGeometry

/-!
# M10 (ModelKernels) — Lemmas 7 and 8, the Schur test, Forelli–Rudin integrals

See `blueprint/M10_ModelKernels.md`.  Scaffold: statements, proofs `sorry`; definitions are real.

Reconciliation: the Forelli–Rudin bound `integral_one_sub_conj_mul_rpow_neg_three_le` that M08
uses for the far field in the disc is stated here (M08 imports M10).
-/

open MeasureTheory Metric Set Complex
open scoped ENNReal NNReal ComplexConjugate Topology

noncomputable section

namespace OC

/-! ## §1 Schur test -/

theorem schur_test_of_measurable {X : Type*} [MeasurableSpace X] {ν : Measure X} [SFinite ν]
    {k : X → X → ℝ≥0∞} (hk : Measurable (Function.uncurry k)) {A B : ℝ≥0∞}
    (hA : ∀ᵐ x ∂ν, ∫⁻ y, k x y ∂ν ≤ A) (hB : ∀ᵐ y ∂ν, ∫⁻ x, k x y ∂ν ≤ B)
    {F : X → ℝ≥0∞} (hF : Measurable F) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    eLpNorm (fun x ↦ ∫⁻ y, k x y * F y ∂ν) p ν ≤
      A ^ (1 - p⁻¹.toReal) * B ^ p⁻¹.toReal * eLpNorm F p ν := by
  have hky : ∀ x, Measurable (k x) := fun x => hk.of_uncurry_left
  have hkx : ∀ y, Measurable fun x => k x y := fun y => hk.of_uncurry_right
  have hkF : Measurable fun q : X × X => k q.1 q.2 * F q.2 := hk.mul (hF.comp measurable_snd)
  have hTF : Measurable (fun x ↦ ∫⁻ y, k x y * F y ∂ν) := hkF.lintegral_prod_right'
  have hTFs : AEStronglyMeasurable (fun x ↦ ∫⁻ y, k x y * F y ∂ν) ν :=
    hTF.aestronglyMeasurable
  have hFs : AEStronglyMeasurable F ν := hF.aestronglyMeasurable
  rcases eq_or_ne p ∞ with rfl | hp_top
  · simp only [ENNReal.inv_top, ENNReal.toReal_zero, sub_zero, ENNReal.rpow_one,
      ENNReal.rpow_zero, mul_one]
    rw [eLpNorm_exponent_top hTFs, eLpNorm_exponent_top hFs]
    simp only [eLpNormEssSup, enorm_eq_self]
    refine essSup_le_of_ae_le _ ?_
    have hFle : ∀ᵐ y ∂ν, F y ≤ essSup F ν := ENNReal.ae_le_essSup F
    filter_upwards [hA] with x hx
    calc ∫⁻ y, k x y * F y ∂ν ≤ ∫⁻ y, k x y * essSup F ν ∂ν :=
          lintegral_mono_ae (hFle.mono fun y hy => by gcongr)
      _ = (∫⁻ y, k x y ∂ν) * essSup F ν := lintegral_mul_const _ (hky x)
      _ ≤ A * essSup F ν := by gcongr
  rcases eq_or_lt_of_le hp with rfl | hp1
  · simp only [inv_one, ENNReal.toReal_one, sub_self, ENNReal.rpow_zero, ENNReal.rpow_one,
      one_mul]
    rw [eLpNorm_one_eq_lintegral_enorm hTFs, eLpNorm_one_eq_lintegral_enorm hFs]
    simp only [enorm_eq_self]
    rw [lintegral_lintegral_swap hkF.aemeasurable]
    calc ∫⁻ y, ∫⁻ x, k x y * F y ∂ν ∂ν = ∫⁻ y, (∫⁻ x, k x y ∂ν) * F y ∂ν := by
          refine lintegral_congr fun y => ?_
          exact lintegral_mul_const _ (hkx y)
      _ ≤ ∫⁻ y, B * F y ∂ν := lintegral_mono_ae (hB.mono fun y hy => by gcongr)
      _ = B * ∫⁻ y, F y ∂ν := lintegral_const_mul _ hF
  -- the case `1 < p < ∞`
  set r := p.toReal with hr_def
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp).ne'
  have hr1 : 1 < r := by
    rw [hr_def, ← ENNReal.toReal_one]
    exact ENNReal.toReal_strict_mono hp_top hp1
  have hr0 : 0 < r := zero_lt_one.trans hr1
  set q := r.conjExponent with hq_def
  have hrq : r.HolderConjugate q := Real.HolderConjugate.conjExponent hr1
  have hq0 : 0 < q := hrq.symm.pos
  have hinv : q⁻¹ + r⁻¹ = 1 := hrq.symm.inv_add_inv_eq_one
  have hpinv : p⁻¹.toReal = r⁻¹ := by rw [ENNReal.toReal_inv]
  rw [hpinv, show 1 - r⁻¹ = q⁻¹ by linarith]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp_top hTFs,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp_top hFs]
  simp only [enorm_eq_self, ← hr_def]
  -- pointwise Hölder
  have hpt : ∀ x, ∫⁻ y, k x y ∂ν ≤ A →
      (∫⁻ y, k x y * F y ∂ν) ^ r ≤ A ^ (r / q) * ∫⁻ y, k x y * F y ^ r ∂ν := by
    intro x hx
    have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq ν hrq.symm
      (f := fun y => k x y ^ q⁻¹) (g := fun y => k x y ^ r⁻¹ * F y)
      ((hky x).pow_const _).aemeasurable (((hky x).pow_const _).mul hF).aemeasurable
    have e1 : (fun y => k x y ^ q⁻¹) * (fun y => k x y ^ r⁻¹ * F y) = fun y => k x y * F y := by
      funext y
      simp only [Pi.mul_apply]
      rw [← mul_assoc, ← ENNReal.rpow_add_of_nonneg _ _ (inv_nonneg.2 hq0.le)
        (inv_nonneg.2 hr0.le), hinv, ENNReal.rpow_one]
    have e2 : ∀ y, (k x y ^ q⁻¹) ^ q = k x y := fun y => by
      rw [← ENNReal.rpow_mul, inv_mul_cancel₀ hq0.ne', ENNReal.rpow_one]
    have e3 : ∀ y, (k x y ^ r⁻¹ * F y) ^ r = k x y * F y ^ r := fun y => by
      rw [ENNReal.mul_rpow_of_nonneg _ _ hr0.le, ← ENNReal.rpow_mul, inv_mul_cancel₀ hr0.ne',
        ENNReal.rpow_one]
    rw [e1] at hH
    simp only [e2, e3] at hH
    calc (∫⁻ y, k x y * F y ∂ν) ^ r
        ≤ ((∫⁻ y, k x y ∂ν) ^ (1 / q) * (∫⁻ y, k x y * F y ^ r ∂ν) ^ (1 / r)) ^ r :=
          ENNReal.rpow_le_rpow hH hr0.le
      _ = (∫⁻ y, k x y ∂ν) ^ (r / q) * ∫⁻ y, k x y * F y ^ r ∂ν := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hr0.le, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
            one_div_mul_eq_div, one_div_mul_eq_div, div_self hr0.ne', ENNReal.rpow_one]
      _ ≤ A ^ (r / q) * ∫⁻ y, k x y * F y ^ r ∂ν := by
          gcongr
  have hint : ∫⁻ x, (∫⁻ y, k x y * F y ∂ν) ^ r ∂ν ≤
      A ^ (r / q) * B * ∫⁻ y, F y ^ r ∂ν := by
    have hkFr : Measurable fun q : X × X => k q.1 q.2 * F q.2 ^ r :=
      hk.mul ((hF.comp measurable_snd).pow_const _)
    calc ∫⁻ x, (∫⁻ y, k x y * F y ∂ν) ^ r ∂ν
        ≤ ∫⁻ x, A ^ (r / q) * ∫⁻ y, k x y * F y ^ r ∂ν ∂ν :=
          lintegral_mono_ae (hA.mono fun x hx => hpt x hx)
      _ = A ^ (r / q) * ∫⁻ x, ∫⁻ y, k x y * F y ^ r ∂ν ∂ν :=
          lintegral_const_mul _ hkFr.lintegral_prod_right'
      _ = A ^ (r / q) * ∫⁻ y, (∫⁻ x, k x y ∂ν) * F y ^ r ∂ν := by
          rw [lintegral_lintegral_swap hkFr.aemeasurable]
          congr 1
          refine lintegral_congr fun y => ?_
          exact lintegral_mul_const _ (hkx y)
      _ ≤ A ^ (r / q) * ∫⁻ y, B * F y ^ r ∂ν := by
          exact mul_le_mul_right (lintegral_mono_ae (hB.mono fun y hy => by gcongr)) _
      _ = A ^ (r / q) * B * ∫⁻ y, F y ^ r ∂ν := by
          rw [lintegral_const_mul _ (hF.pow_const _), mul_assoc]
  calc (∫⁻ x, (∫⁻ y, k x y * F y ∂ν) ^ r ∂ν) ^ (1 / r)
      ≤ (A ^ (r / q) * B * ∫⁻ y, F y ^ r ∂ν) ^ (1 / r) :=
        ENNReal.rpow_le_rpow hint (by positivity)
    _ = A ^ q⁻¹ * B ^ r⁻¹ * (∫⁻ y, F y ^ r ∂ν) ^ (1 / r) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
          ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul, one_div]
        congr 3
        field_simp

theorem schur_test {X : Type*} [MeasurableSpace X] {ν : Measure X} [SFinite ν]
    {k : X → X → ℝ≥0∞} (hk : Measurable (Function.uncurry k)) {A B : ℝ≥0∞}
    (hA : ∀ᵐ x ∂ν, ∫⁻ y, k x y ∂ν ≤ A) (hB : ∀ᵐ y ∂ν, ∫⁻ x, k x y ∂ν ≤ B)
    {F : X → ℝ≥0∞} (hF : AEMeasurable F ν) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    eLpNorm (fun x ↦ ∫⁻ y, k x y * F y ∂ν) p ν ≤
      A ^ (1 - p⁻¹.toReal) * B ^ p⁻¹.toReal * eLpNorm F p ν := by
  have hT : (fun x ↦ ∫⁻ y, k x y * F y ∂ν) = fun x ↦ ∫⁻ y, k x y * hF.mk F y ∂ν := by
    funext x
    exact lintegral_congr_ae (hF.ae_eq_mk.mono fun y hy => by simp only [hy])
  rw [hT, eLpNorm_congr_ae hF.ae_eq_mk]
  exact schur_test_of_measurable hk hA hB hF.measurable_mk hp

theorem schur_test_le_max {X : Type*} [MeasurableSpace X] {ν : Measure X} [SFinite ν]
    {k : X → X → ℝ≥0∞} (hk : Measurable (Function.uncurry k)) {A : ℝ≥0∞}
    (hA : ∀ᵐ x ∂ν, ∫⁻ y, k x y ∂ν ≤ A) (hB : ∀ᵐ y ∂ν, ∫⁻ x, k x y ∂ν ≤ A)
    {F : X → ℝ≥0∞} (hF : AEMeasurable F ν) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    eLpNorm (fun x ↦ ∫⁻ y, k x y * F y ∂ν) p ν ≤ A * eLpNorm F p ν := by
  have h := schur_test hk hA hB hF hp
  have h1 : p⁻¹.toReal ≤ 1 := by
    rw [ENNReal.toReal_inv]
    rcases eq_or_ne p ∞ with rfl | hpt
    · simp
    · exact inv_le_one_of_one_le₀ (by
        rw [← ENNReal.toReal_one]; exact ENNReal.toReal_mono hpt hp)
  rwa [← ENNReal.rpow_add_of_nonneg _ _ (by linarith) ENNReal.toReal_nonneg, sub_add_cancel,
    ENNReal.rpow_one] at h

/-! ## §2 Forelli–Rudin estimate -/

theorem norm_one_sub_conj_mul_le_five_mul {a w : ℂ} (ha : a ∈ 𝔻) (hw : w ∈ 𝔻)
    (h : (1 - ‖a‖) / 2 ≤ ‖a - w‖) : ‖1 - conj a * w‖ ≤ 5 * ‖a - w‖ := sorry

theorem lintegral_FR_near {s : ℝ} (hs0 : 0 < s) {a : ℂ} (ha : a ∈ 𝔻) :
    ∫⁻ w in ball a ((1 - ‖a‖) / 2),
        ENNReal.ofReal ((1 - ‖w‖ ^ 2) ^ (-s) / (‖1 - conj a * w‖ * ‖a - w‖)) ≤
      ENNReal.ofReal (2 * Real.pi * (1 - ‖a‖) ^ (-s)) := sorry

theorem fr_poisson_integral {w : ℂ} (hw : ‖w‖ < 1) :
    ∫ θ in (0 : ℝ)..2 * Real.pi, (1 - ‖w‖ ^ 2) / ‖circleMap 0 1 θ - w‖ ^ 2 = 2 * Real.pi := by
  have hw' : w ∈ ball (0 : ℂ) 1 := by simpa using hw
  have := DiffContOnCl.circleAverage_poissonKernel_smul' (E := ℂ) (f := fun _ ↦ (1 : ℂ))
    (c := 0) (R := 1) (w := w) diffContOnCl_const hw'
  simp [Real.circleAverage_def] at this
  rw [← Complex.ofReal_inj, ← intervalIntegral.integral_ofReal]
  push_cast
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  generalize (∫ θ in (0 : ℝ)..2 * Real.pi, (1 - (‖w‖ : ℂ) ^ 2) / (‖circleMap 0 1 θ - w‖ : ℂ) ^ 2) = I at this ⊢
  field_simp at this
  linear_combination this

theorem fr_norm_one_sub_conj_mul_circleMap (a : ℂ) (ρ θ : ℝ) :
    ‖1 - conj a * circleMap 0 ρ θ‖ = ‖circleMap 0 1 θ - (ρ : ℂ) * a‖ := by
  have he : circleMap 0 1 θ * conj (circleMap 0 1 θ) = 1 := by
    rw [Complex.mul_conj']; simp
  have : 1 - conj a * circleMap 0 ρ θ =
      circleMap 0 1 θ * conj (circleMap 0 1 θ - (ρ : ℂ) * a) := by
    rw [map_sub, map_mul, Complex.conj_ofReal, mul_sub, he]
    simp only [circleMap, zero_add, one_mul, ofReal_one]
    ring
  rw [this, norm_mul, Complex.norm_conj]
  simp

theorem lintegral_circle_inv_normSq_one_sub {a : ℂ} {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (h : ‖a‖ * ρ < 1) :
    ∫⁻ θ in Ioc 0 (2 * Real.pi),
        ENNReal.ofReal (‖1 - conj a * circleMap 0 ρ θ‖⁻¹ ^ 2) =
      ENNReal.ofReal (2 * Real.pi / (1 - ‖a‖ ^ 2 * ρ ^ 2)) := by
  set w : ℂ := (ρ : ℂ) * a with hw_def
  have hwn : ‖w‖ = ‖a‖ * ρ := by
    rw [hw_def, norm_mul, Complex.norm_real, Real.norm_of_nonneg hρ0, mul_comm]
  have hw1 : ‖w‖ < 1 := by rw [hwn]; exact h
  have hpos : 0 < 1 - ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
  have hne : ∀ θ, ‖circleMap 0 1 θ - w‖ ≠ 0 := by
    intro θ h0
    have : ‖circleMap 0 1 θ‖ ≤ ‖circleMap 0 1 θ - w‖ + ‖w‖ := norm_le_norm_sub_add _ _
    rw [h0] at this
    simp at this
    linarith
  have hcont : Continuous fun θ : ℝ ↦ ‖1 - conj a * circleMap 0 ρ θ‖⁻¹ ^ 2 := by
    simp_rw [fr_norm_one_sub_conj_mul_circleMap]
    exact ((((continuous_circleMap 0 1).sub continuous_const).norm).inv₀ hne).pow 2
  rw [← ofReal_integral_eq_lintegral_ofReal (hcont.integrableOn_Ioc)
    (Filter.Eventually.of_forall fun θ ↦ by positivity),
    ← intervalIntegral.integral_of_le Real.two_pi_pos.le]
  congr 1
  have hI := fr_poisson_integral hw1
  have heq : ∀ θ : ℝ, ‖1 - conj a * circleMap 0 ρ θ‖⁻¹ ^ 2 =
      (1 - ‖w‖ ^ 2)⁻¹ * ((1 - ‖w‖ ^ 2) / ‖circleMap 0 1 θ - w‖ ^ 2) := by
    intro θ
    rw [fr_norm_one_sub_conj_mul_circleMap, ← hw_def]
    field_simp
  simp_rw [heq]
  rw [intervalIntegral.integral_const_mul, hI, hwn]
  field_simp

theorem lintegral_Ioo_rpow_div_le {s b : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hb0 : 0 ≤ b)
    (hb1 : b < 1) :
    ∫⁻ ρ in Ioo (0 : ℝ) 1, ENNReal.ofReal ((1 - ρ) ^ (-s) / (1 - b * ρ)) ≤
      ENNReal.ofReal ((1 - b) ^ (-s) / (s * (1 - s))) := sorry

theorem lintegral_disc_rpow_div_normSq {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {a : ℂ}
    (ha : a ∈ 𝔻) :
    ∫⁻ w in 𝔻, ENNReal.ofReal ((1 - ‖w‖) ^ (-s) / ‖1 - conj a * w‖ ^ 2) ≤
      ENNReal.ofReal (2 * Real.pi / (s * (1 - s)) * (1 - ‖a‖) ^ (-s)) := sorry

theorem lintegral_FR {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {a : ℂ} (ha : a ∈ 𝔻) :
    ∫⁻ w in 𝔻, ENNReal.ofReal ((1 - ‖w‖ ^ 2) ^ (-s) / (‖1 - conj a * w‖ * ‖a - w‖)) ≤
      ENNReal.ofReal (24 * Real.pi / (s * (1 - s)) * (1 - ‖a‖ ^ 2) ^ (-s)) := sorry

/-- Forelli–Rudin, the case `∫_𝔻 dm(w)/|1 − z̄w|³ ≲ (1 − |z|²)⁻¹` used by M08 (far field in the
disc, `farField_sum_le_disc`). -/
theorem integral_one_sub_conj_mul_rpow_neg_three_le :
    ∃ C : ℝ, ∀ z ∈ 𝔻,
      ∫⁻ w in 𝔻, ENNReal.ofReal (1 / ‖1 - conj z * w‖ ^ 3) ≤ ENNReal.ofReal (C / (1 - ‖z‖ ^ 2)) :=
  sorry

/-! ## §3 Positive model kernels and their Schur bounds -/

/-- The positive model kernel of the disc, `(1-|z|²)^c (1-|ζ|²)^{1-c} / (|1-ζ̄z| |z-ζ|)`. -/
def discModel (c : ℝ) (z ζ : ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal ((1 - ‖z‖ ^ 2) ^ c * (1 - ‖ζ‖ ^ 2) ^ (1 - c) /
    (‖1 - conj ζ * z‖ * ‖z - ζ‖))

theorem measurable_discModel (c : ℝ) : Measurable (Function.uncurry (discModel c)) := sorry

theorem lintegral_discModel_left {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) {z : ℂ} (hz : z ∈ 𝔻) :
    ∫⁻ ζ, discModel c z ζ ∂discMeasure ≤ ENNReal.ofReal (24 * Real.pi / (c * (1 - c))) := sorry

theorem lintegral_discModel_right {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) {ζ : ℂ} (hζ : ζ ∈ 𝔻) :
    ∫⁻ z, discModel c z ζ ∂discMeasure ≤ ENNReal.ofReal (24 * Real.pi / (c * (1 - c))) := sorry

instance sigmaFinite_discMeasure : SigmaFinite discMeasure := by
  unfold discMeasure; infer_instance

theorem eLpNorm_discModel_le {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) {F : ℂ → ℝ≥0∞}
    (hF : AEMeasurable F discMeasure) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    eLpNorm (fun z ↦ ∫⁻ ζ, discModel c z ζ * F ζ ∂discMeasure) p discMeasure ≤
      ENNReal.ofReal (24 * Real.pi / (c * (1 - c))) * eLpNorm F p discMeasure := sorry

/-- The Gaussian model kernel of the plane, `e^{-c|z-ζ|²} / |z-ζ|`. -/
def planeModel (c : ℝ) (z ζ : ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-c * ‖z - ζ‖ ^ 2) / ‖z - ζ‖)

theorem measurable_planeModel (c : ℝ) : Measurable (Function.uncurry (planeModel c)) := sorry

theorem lintegral_planeModel_left {c : ℝ} (hc : 0 < c) (z : ℂ) :
    ∫⁻ ζ, planeModel c z ζ = ENNReal.ofReal (Real.pi * Real.sqrt (Real.pi / c)) := sorry

theorem lintegral_planeModel_right {c : ℝ} (hc : 0 < c) (ζ : ℂ) :
    ∫⁻ z, planeModel c z ζ = ENNReal.ofReal (Real.pi * Real.sqrt (Real.pi / c)) := sorry

theorem eLpNorm_planeModel_le {c : ℝ} (hc : 0 < c) {F : ℂ → ℝ≥0∞} (hF : AEMeasurable F)
    {p : ℝ≥0∞} (hp : 1 ≤ p) :
    eLpNorm (fun z ↦ ∫⁻ ζ, planeModel c z ζ * F ζ) p volume ≤
      ENNReal.ofReal (Real.pi * Real.sqrt (Real.pi / c)) * eLpNorm F p volume := sorry

/-! ## §4 The weak equation for holomorphic perturbations of the Cauchy kernel -/

/-- A holomorphic function on an open set times a test function supported in it is `C¹`. -/
theorem weak_contDiff_holo_mul {Ω : Set ℂ} (hΩ : IsOpen Ω) {H : ℂ → ℂ}
    (hH : DifferentiableOn ℂ H Ω) {α : ℂ → ℂ} (hα : ContDiff ℝ (⊤ : ℕ∞) α)
    (hαs : tsupport α ⊆ Ω) : ContDiff ℝ 1 (fun z ↦ H z * α z) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ Ω
  · have h1 : ContDiffAt ℂ 1 H x :=
      (hH.contDiffOn hΩ).contDiffAt (hΩ.mem_nhds hx)
    exact (h1.restrict_scalars ℝ).mul (hα.contDiffAt.of_le (by exact_mod_cast le_top))
  · have hx' : x ∉ tsupport α := fun h ↦ hx (hαs h)
    have h0 : (fun z ↦ H z * α z) =ᶠ[𝓝 x] fun _ ↦ (0 : ℂ) := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hx'] with z hz
      simp [hz]
    exact contDiffAt_const.congr_of_eventuallyEq h0

theorem weak_dbar_holo_mul {Ω : Set ℂ} (hΩ : IsOpen Ω) {H : ℂ → ℂ}
    (hH : DifferentiableOn ℂ H Ω) {α : ℂ → ℂ} (hα : ContDiff ℝ (⊤ : ℕ∞) α)
    (hαs : tsupport α ⊆ Ω) (z : ℂ) : dbar (fun z ↦ H z * α z) z = H z * dbar α z := by
  by_cases hz : z ∈ Ω
  · have hHz : DifferentiableAt ℂ H z := hH.differentiableAt (hΩ.mem_nhds hz)
    rw [dbar_mul (hHz.restrictScalars ℝ) (hα.differentiable (by simp)).differentiableAt,
      dbar_eq_zero_of_differentiableAt hHz]
    ring
  · have hz' : z ∉ tsupport α := fun h ↦ hz (hαs h)
    have h0 : (fun z ↦ H z * α z) =ᶠ[𝓝 z] fun _ ↦ (0 : ℂ) := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hz'] with w hw
      simp [hw]
    rw [dbar_congr h0, image_eq_zero_of_notMem_tsupport
      (fun h ↦ hz' (tsupport_dbar_subset α h))]
    simp [dbar]

theorem integral_holo_mul_dbar_div {Ω : Set ℂ} (hΩ : IsOpen Ω) {H : ℂ → ℂ} {ζ : ℂ}
    (hζ : ζ ∈ Ω) (hH : DifferentiableOn ℂ H Ω) {α : ℂ → ℂ} (hα : ContDiff ℝ (⊤ : ℕ∞) α)
    (hαc : HasCompactSupport α) (hαs : tsupport α ⊆ Ω) :
    ∫ z, H z * dbar α z / ((Real.pi : ℂ) * (z - ζ)) = -(H ζ * α ζ) := by
  have hβ := weak_contDiff_holo_mul hΩ hH hα hαs
  have hβc : HasCompactSupport (fun z ↦ H z * α z) := hαc.mul_left
  have hP := pompeiu hβ hβc ζ
  rw [cauchyTransform] at hP
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have heq : ∀ z, H z * dbar α z / ((Real.pi : ℂ) * (z - ζ)) =
      -((1 / Real.pi : ℂ) * (dbar (fun z ↦ H z * α z) z / (ζ - z))) := by
    intro z
    rw [weak_dbar_holo_mul hΩ hH hα hαs z]
    by_cases hz : z = ζ
    · subst hz; simp
    · have : z - ζ ≠ 0 := sub_ne_zero.2 hz
      have : ζ - z ≠ 0 := sub_ne_zero.2 (Ne.symm hz)
      field_simp
      ring
  simp_rw [heq]
  rw [integral_neg, integral_const_mul, hP]

/-- The integrand `(z, ζ) ↦ H z ζ / (π (z − ζ)) · f ζ` is a.e.-strongly measurable on
`μ.prod (volume.restrict Ω)`. -/
theorem weak_aestronglyMeasurable_kernel_prod {Ω : Set ℂ} {H : ℂ → ℂ → ℂ} {f : ℂ → ℂ}
    (μ : Measure ℂ) (hHm : Measurable (Function.uncurry H))
    (hf : AEStronglyMeasurable f (volume.restrict Ω)) :
    AEStronglyMeasurable (fun p : ℂ × ℂ ↦ H p.1 p.2 / ((Real.pi : ℂ) * (p.1 - p.2)) * f p.2)
      (μ.prod (volume.restrict Ω)) := by
  have h1 : Measurable (fun p : ℂ × ℂ ↦ H p.1 p.2 / ((Real.pi : ℂ) * (p.1 - p.2))) :=
    hHm.div (measurable_const.mul (measurable_fst.sub measurable_snd))
  exact h1.aestronglyMeasurable.mul hf.comp_snd

/-- The kernel operator `z ↦ ∫_Ω H z ζ / (π (z − ζ)) f ζ` is a.e.-strongly measurable. -/
theorem weak_aestronglyMeasurable_kernelOp {Ω : Set ℂ} {H : ℂ → ℂ → ℂ} {f : ℂ → ℂ}
    (hHm : Measurable (Function.uncurry H)) (hf : AEStronglyMeasurable f (volume.restrict Ω)) :
    AEStronglyMeasurable (fun z ↦ ∫ ζ in Ω, H z ζ / ((Real.pi : ℂ) * (z - ζ)) * f ζ) volume :=
  (weak_aestronglyMeasurable_kernel_prod volume hHm hf).integral_prod_right'

theorem isWeakDbarSol_kernel {Ω : Set ℂ} (hΩ : IsOpen Ω) {H : ℂ → ℂ → ℂ} {f : ℂ → ℂ}
    (hHm : Measurable (Function.uncurry H))
    (hHd : ∀ ζ ∈ Ω, DifferentiableOn ℂ (fun z ↦ H z ζ) Ω) (hH1 : ∀ ζ ∈ Ω, H ζ ζ = 1)
    (hf : AEStronglyMeasurable f (volume.restrict Ω)) (hfl : LocallyIntegrableOn f Ω)
    (hloc : ∀ K ⊆ Ω, IsCompact K →
      ∫⁻ z in K, ∫⁻ ζ in Ω, ‖H z ζ / ((Real.pi : ℂ) * (z - ζ))‖ₑ * ‖f ζ‖ₑ < ∞) :
    IsWeakDbarSol Ω (fun z ↦ ∫ ζ in Ω, H z ζ / ((Real.pi : ℂ) * (z - ζ)) * f ζ) f := by
  set u : ℂ → ℂ := fun z ↦ ∫ ζ in Ω, H z ζ / ((Real.pi : ℂ) * (z - ζ)) * f ζ with hu_def
  have hum : AEStronglyMeasurable u volume := weak_aestronglyMeasurable_kernelOp hHm hf
  have hupt : ∀ z, ‖u z‖ₑ ≤ ∫⁻ ζ in Ω, ‖H z ζ / ((Real.pi : ℂ) * (z - ζ))‖ₑ * ‖f ζ‖ₑ := by
    intro z
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
    simp_rw [enorm_mul]
  refine ⟨?_, hfl, fun α hα hαc hαs ↦ ?_⟩
  · rw [locallyIntegrableOn_iff hΩ.isLocallyClosed]
    intro K hK hKc
    refine ⟨hum.restrict, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    exact (lintegral_mono hupt).trans_lt (hloc K hK hKc)
  -- the identity
  have hα1 : ContDiff ℝ 1 α := hα.of_le (by exact_mod_cast le_top)
  obtain ⟨C, hC⟩ := (continuous_dbar hα1).bounded_above_of_compact_support
    (hasCompactSupport_dbar hαc)
  set K := tsupport α
  have hKc : IsCompact K := hαc.isCompact
  set F : ℂ → ℂ → ℂ := fun z ζ ↦ dbar α z * (H z ζ / ((Real.pi : ℂ) * (z - ζ)) * f ζ) with hF
  have hdb : ∀ z, ‖dbar α z‖ₑ ≤ K.indicator (fun _ ↦ ENNReal.ofReal C) z := by
    intro z
    by_cases hz : z ∈ K
    · rw [indicator_of_mem hz, ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hC z)
    · rw [image_eq_zero_of_notMem_tsupport (fun h ↦ hz (tsupport_dbar_subset α h))]
      simp
  have hint : Integrable (Function.uncurry F) (volume.prod (volume.restrict Ω)) := by
    refine ⟨(continuous_dbar hα1).aestronglyMeasurable.comp_fst.mul
      (weak_aestronglyMeasurable_kernel_prod volume hHm hf), ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    calc ∫⁻ p, ‖Function.uncurry F p‖ₑ ∂(volume.prod (volume.restrict Ω))
        ≤ ∫⁻ z, ∫⁻ ζ in Ω, ‖F z ζ‖ₑ := lintegral_prod_le _
      _ ≤ ∫⁻ z, K.indicator (fun z ↦ ENNReal.ofReal C *
            ∫⁻ ζ in Ω, ‖H z ζ / ((Real.pi : ℂ) * (z - ζ))‖ₑ * ‖f ζ‖ₑ) z := by
          refine lintegral_mono fun z ↦ ?_
          simp only [hF, enorm_mul]
          by_cases hz : z ∈ K
          · rw [indicator_of_mem hz, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
            refine lintegral_mono fun ζ ↦ ?_
            have := hdb z
            rw [indicator_of_mem hz] at this
            exact mul_le_mul_of_nonneg_right this (zero_le)
          · rw [indicator_of_notMem hz,
              image_eq_zero_of_notMem_tsupport (fun h ↦ hz (tsupport_dbar_subset α h))]
            simp
      _ = ENNReal.ofReal C * ∫⁻ z in K,
            ∫⁻ ζ in Ω, ‖H z ζ / ((Real.pi : ℂ) * (z - ζ))‖ₑ * ‖f ζ‖ₑ := by
          rw [lintegral_indicator hKc.measurableSet, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hloc K hαs hKc)
  have h1 : ∫ z, u z * dbar α z = ∫ z, ∫ ζ in Ω, F z ζ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun z ↦ ?_)
    simp only [hu_def, hF]
    rw [integral_const_mul, mul_comm]
  rw [h1, integral_integral_swap hint]
  have h2 : ∀ ζ ∈ Ω, ∫ z, F z ζ = -(f ζ * α ζ) := by
    intro ζ hζ
    have : ∀ z, F z ζ = f ζ * (H z ζ * dbar α z / ((Real.pi : ℂ) * (z - ζ))) := by
      intro z; simp only [hF]; ring
    simp_rw [this]
    rw [integral_const_mul, integral_holo_mul_dbar_div hΩ hζ (hHd ζ hζ) hα hαc hαs, hH1 ζ hζ]
    ring
  rw [setIntegral_congr_fun hΩ.measurableSet h2, integral_neg,
    setIntegral_eq_integral_of_forall_compl_eq_zero]
  intro x hx
  rw [image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hαs h)), mul_zero]

/-! ## §5 Conjugated-kernel operators (used by M11 and M12) -/

theorem disc_kernel_operator {φ : ℂ → ℝ} (hφ : ContinuousOn φ 𝔻) {c A : ℝ} (hc0 : 0 < c)
    (hc1 : c < 1) {H : ℂ → ℂ → ℂ} (hHm : Measurable (Function.uncurry H))
    (hHd : ∀ ζ ∈ 𝔻, DifferentiableOn ℂ (fun z ↦ H z ζ) 𝔻) (hH1 : ∀ ζ ∈ 𝔻, H ζ ζ = 1)
    (hHb : ∀ z ∈ 𝔻, ∀ ζ ∈ 𝔻, ‖H z ζ‖ ≤ A * Real.exp (φ z - φ ζ) *
      ((1 - ‖z‖ ^ 2) / (1 - ‖ζ‖ ^ 2)) ^ c * ((1 - ‖ζ‖ ^ 2) / ‖1 - conj ζ * z‖))
    (f : ℂ → ℂ) (hf : AEStronglyMeasurable f (volume.restrict 𝔻))
    (hadm : ∃ p : ℝ≥0∞, 1 ≤ p ∧
      eLpNorm (fun z ↦ f z * ((1 - ‖z‖ ^ 2) * Real.exp (-φ z) : ℝ)) p discMeasure < ∞) :
    IsWeakDbarSol 𝔻 (fun z ↦ ∫ ζ in 𝔻, H z ζ / ((Real.pi : ℂ) * (z - ζ)) * f ζ) f ∧
      ∀ p : ℝ≥0∞, 1 ≤ p →
        eLpNorm (fun z ↦ (∫ ζ in 𝔻, H z ζ / ((Real.pi : ℂ) * (z - ζ)) * f ζ) *
            (Real.exp (-φ z) : ℝ)) p discMeasure ≤
          ENNReal.ofReal (24 * A / (c * (1 - c))) *
            eLpNorm (fun z ↦ f z * ((1 - ‖z‖ ^ 2) * Real.exp (-φ z) : ℝ)) p discMeasure :=
  sorry

theorem plane_kernel_operator {φ : ℂ → ℝ} (hφ : Continuous φ) {c A : ℝ} (hc : 0 < c)
    {H : ℂ → ℂ → ℂ} (hHm : Measurable (Function.uncurry H))
    (hHd : ∀ ζ, Differentiable ℂ (fun z ↦ H z ζ)) (hH1 : ∀ ζ, H ζ ζ = 1)
    (hHb : ∀ z ζ, ‖H z ζ‖ ≤ A * Real.exp (φ z - φ ζ) * Real.exp (-c * ‖z - ζ‖ ^ 2))
    (f : ℂ → ℂ) (hf : AEStronglyMeasurable f volume)
    (hadm : ∃ p : ℝ≥0∞, 1 ≤ p ∧ eLpNorm (fun z ↦ f z * (Real.exp (-φ z) : ℝ)) p volume < ∞) :
    IsWeakDbarSol univ (fun z ↦ ∫ ζ, H z ζ / ((Real.pi : ℂ) * (z - ζ)) * f ζ) f ∧
      ∀ p : ℝ≥0∞, 1 ≤ p →
        eLpNorm (fun z ↦ (∫ ζ, H z ζ / ((Real.pi : ℂ) * (z - ζ)) * f ζ) *
            (Real.exp (-φ z) : ℝ)) p volume ≤
          ENNReal.ofReal (A * Real.sqrt (Real.pi / c)) *
            eLpNorm (fun z ↦ f z * (Real.exp (-φ z) : ℝ)) p volume := sorry

/-! ## §6 Lemma 7 -/

/-- The kernel of Lemma 7, `K(z, ζ) = (1/π) (1 - |ζ|²) / ((1 - ζ̄ z)(z - ζ))`. -/
def discKernel (z ζ : ℂ) : ℂ :=
  ((1 - ‖ζ‖ ^ 2 : ℝ) : ℂ) / (1 - conj ζ * z) / ((Real.pi : ℂ) * (z - ζ))

/-- The solution operator of Lemma 7. -/
def lemma7Op (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∫ ζ in 𝔻, discKernel z ζ * f ζ

theorem lemma7_isWeakDbarSol {f : ℂ → ℂ} (hf : AEStronglyMeasurable f (volume.restrict 𝔻))
    (hfi : ∫⁻ ζ in 𝔻, ‖f ζ‖ₑ * ENNReal.ofReal (1 - ‖ζ‖ ^ 2) < ∞) :
    IsWeakDbarSol 𝔻 (lemma7Op f) f := sorry

theorem lemma7 {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (f : ℂ → ℂ)
    (hf : AEStronglyMeasurable f (volume.restrict 𝔻))
    (hadm : ∃ p : ℝ≥0∞, 1 ≤ p ∧ eLpNorm (fun z ↦ f z * ((1 - ‖z‖ ^ 2) ^ (1 + α) : ℝ)) p
      discMeasure < ∞) :
    IsWeakDbarSol 𝔻 (lemma7Op f) f ∧ ∀ p : ℝ≥0∞, 1 ≤ p →
      eLpNorm (fun z ↦ lemma7Op f z * ((1 - ‖z‖ ^ 2) ^ α : ℝ)) p discMeasure ≤
        ENNReal.ofReal (24 / (α * (1 - α))) *
          eLpNorm (fun z ↦ f z * ((1 - ‖z‖ ^ 2) ^ (1 + α) : ℝ)) p discMeasure := sorry

theorem lemma7_Lp_printed {α p : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hp : 1 ≤ p) (f : ℂ → ℂ)
    (hf : AEStronglyMeasurable f (volume.restrict 𝔻))
    (hfin : ∫⁻ z in 𝔻, ENNReal.ofReal (‖f z * (1 - ‖z‖ ^ 2)‖ ^ p * (1 - ‖z‖ ^ 2) ^ (α - 1)) < ∞) :
    IsWeakDbarSol 𝔻 (lemma7Op f) f ∧
      ∫⁻ z in 𝔻, ENNReal.ofReal (‖lemma7Op f z‖ ^ p * (1 - ‖z‖ ^ 2) ^ (α - 1)) ≤
        ENNReal.ofReal ((24 * p ^ 2 / (α * (p - α))) ^ p) *
          ∫⁻ z in 𝔻, ENNReal.ofReal (‖f z * (1 - ‖z‖ ^ 2)‖ ^ p * (1 - ‖z‖ ^ 2) ^ (α - 1)) :=
  sorry

theorem lemma7_sup {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (f : ℂ → ℂ)
    (hf : AEStronglyMeasurable f (volume.restrict 𝔻)) {M : ℝ}
    (hM : ∀ᵐ ζ ∂(volume.restrict 𝔻), ‖f ζ‖ * (1 - ‖ζ‖ ^ 2) ^ (1 + α) ≤ M) :
    IsWeakDbarSol 𝔻 (lemma7Op f) f ∧
      ∀ z ∈ 𝔻, ‖lemma7Op f z‖ * (1 - ‖z‖ ^ 2) ^ α ≤ 24 / (α * (1 - α)) * M := sorry

/-! ## §7 Lemma 8 -/

/-- The kernel of Lemma 8, `(1/π) e^{2α(ζ̄ z - |ζ|²)} / (z - ζ)`. -/
def planeKernel (α : ℝ) (z ζ : ℂ) : ℂ :=
  Complex.exp (2 * α * (conj ζ * z - ((‖ζ‖ ^ 2 : ℝ) : ℂ))) / ((Real.pi : ℂ) * (z - ζ))

def lemma8Op (α : ℝ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∫ ζ, planeKernel α z ζ * f ζ

theorem norm_exp_planeKernel_num (α : ℝ) (z ζ : ℂ) :
    ‖Complex.exp (2 * α * (conj ζ * z - ((‖ζ‖ ^ 2 : ℝ) : ℂ)))‖ =
      Real.exp (α * ‖z‖ ^ 2 - α * ‖ζ‖ ^ 2) * Real.exp (-α * ‖z - ζ‖ ^ 2) := sorry

theorem lemma8 {α : ℝ} (hα : 0 < α) (f : ℂ → ℂ) (hf : AEStronglyMeasurable f volume)
    (hadm : ∃ p : ℝ≥0∞, 1 ≤ p ∧
      eLpNorm (fun z ↦ f z * (Real.exp (-α * ‖z‖ ^ 2) : ℂ)) p volume < ∞) :
    IsWeakDbarSol univ (lemma8Op α f) f ∧ ∀ p : ℝ≥0∞, 1 ≤ p →
      eLpNorm (fun z ↦ lemma8Op α f z * (Real.exp (-α * ‖z‖ ^ 2) : ℂ)) p volume ≤
        ENNReal.ofReal (Real.sqrt (Real.pi / α)) *
          eLpNorm (fun z ↦ f z * (Real.exp (-α * ‖z‖ ^ 2) : ℂ)) p volume := sorry

end OC
