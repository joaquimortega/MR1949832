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
    (h : (1 - ‖a‖) / 2 ≤ ‖a - w‖) : ‖1 - conj a * w‖ ≤ 5 * ‖a - w‖ := by
  have ha1 : ‖a‖ < 1 := norm_lt_one_of_mem_disc ha
  have e : 1 - conj a * w = (1 - conj a * a) + conj a * (a - w) := by ring
  rw [e]
  calc ‖(1 - conj a * a) + conj a * (a - w)‖
      ≤ ‖1 - conj a * a‖ + ‖conj a * (a - w)‖ := norm_add_le _ _
    _ = (1 - ‖a‖ ^ 2) + ‖a‖ * ‖a - w‖ := by
        rw [norm_one_sub_conj_mul_self ha, norm_mul, Complex.norm_conj]
    _ ≤ 5 * ‖a - w‖ := by nlinarith [norm_nonneg a, norm_nonneg (a - w), sq_nonneg (1 - ‖a‖)]

-- FALSE?: a = 0, s = 10: LHS = 2π ∫₀^{1/2} (1 - r²)^{-10} dr ≈ 1.84 · 2π > 2π = RHS.
-- The statement needs `s ≤ 1`; see `lintegral_FR_near_of_le_one`, which `lintegral_FR` uses.
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

/-- `∫₀ᵇ (1-ρ)^{-s-1} dρ = ((1-b)^{-s} - 1)/s`. -/
theorem fr_lintegral_Ioc_rpow {s b : ℝ} (hs0 : 0 < s) (hb0 : 0 ≤ b) (hb1 : b < 1) :
    ∫⁻ ρ in Ioc 0 b, ENNReal.ofReal ((1 - ρ) ^ (-s - 1)) =
      ENNReal.ofReal (((1 - b) ^ (-s) - 1) / s) := by
  have hcont : ContinuousOn (fun ρ : ℝ => (1 - ρ) ^ (-s - 1)) (Icc 0 b) := by
    refine ContinuousOn.rpow_const (by fun_prop) (fun x hx => Or.inl ?_)
    linarith [hx.2]
  rw [← ofReal_integral_eq_lintegral_ofReal
    ((hcont.integrableOn_Icc).mono_set Ioc_subset_Icc_self)]
  · congr 1
    rw [← intervalIntegral.integral_of_le hb0,
      intervalIntegral.integral_comp_sub_left (fun x => x ^ (-s - 1)), integral_rpow]
    · rw [show -s - 1 + 1 = -s by ring, sub_zero, Real.one_rpow]
      field_simp
      ring
    · right
      refine ⟨by linarith, fun h0 => ?_⟩
      rw [uIcc_of_le (by linarith)] at h0
      linarith [h0.1]
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with ρ hρ
    exact Real.rpow_nonneg (by linarith [hρ.2]) _

/-- `∫_b^1 (1-ρ)^{-s} dρ = (1-b)^{1-s}/(1-s)`. -/
theorem fr_lintegral_Ioo_rpow {s b : ℝ} (hs1 : s < 1) (hb1 : b < 1) :
    ∫⁻ ρ in Ioo b 1, ENNReal.ofReal ((1 - ρ) ^ (-s)) =
      ENNReal.ofReal ((1 - b) ^ (1 - s) / (1 - s)) := by
  have hii : IntervalIntegrable (fun x : ℝ => x ^ (-s)) volume 0 (1 - b) :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hii2 : IntervalIntegrable (fun ρ : ℝ => (1 - ρ) ^ (-s)) volume b 1 := by
    have := hii.comp_sub_left 1
    simp only [sub_zero, sub_sub_cancel] at this
    exact this.symm
  have hint : IntegrableOn (fun ρ : ℝ => (1 - ρ) ^ (-s)) (Ioo b 1) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hb1.le).1 hii2
  rw [← ofReal_integral_eq_lintegral_ofReal hint]
  · congr 1
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hb1.le,
      intervalIntegral.integral_comp_sub_left (fun x => x ^ (-s)), integral_rpow (Or.inl (by linarith))]
    rw [show -s + 1 = 1 - s by ring, sub_self, Real.zero_rpow (by linarith), sub_zero]
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with ρ hρ
    exact Real.rpow_nonneg (by linarith [hρ.2]) _

theorem lintegral_Ioo_rpow_div_le {s b : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hb0 : 0 ≤ b)
    (hb1 : b < 1) :
    ∫⁻ ρ in Ioo (0 : ℝ) 1, ENNReal.ofReal ((1 - ρ) ^ (-s) / (1 - b * ρ)) ≤
      ENNReal.ofReal ((1 - b) ^ (-s) / (s * (1 - s))) := by
  have hsub : Ioo (0 : ℝ) 1 ⊆ Ioc 0 b ∪ Ioo b 1 := by
    intro ρ hρ
    rcases le_or_gt ρ b with h | h
    · exact Or.inl ⟨hρ.1, h⟩
    · exact Or.inr ⟨h, hρ.2⟩
  have hδ : 0 < 1 - b := by linarith
  set X := (1 - b) ^ (-s) with hX
  have hX0 : 0 ≤ X := Real.rpow_nonneg hδ.le _
  have hXe : (1 - b)⁻¹ * ((1 - b) ^ (1 - s) / (1 - s)) = X / (1 - s) := by
    rw [show 1 - s = 1 + -s by ring, Real.rpow_add hδ, Real.rpow_one, hX]
    field_simp
  calc ∫⁻ ρ in Ioo (0 : ℝ) 1, ENNReal.ofReal ((1 - ρ) ^ (-s) / (1 - b * ρ))
      ≤ ∫⁻ ρ in Ioc 0 b ∪ Ioo b 1, ENNReal.ofReal ((1 - ρ) ^ (-s) / (1 - b * ρ)) :=
        lintegral_mono_set hsub
    _ ≤ (∫⁻ ρ in Ioc 0 b, ENNReal.ofReal ((1 - ρ) ^ (-s) / (1 - b * ρ))) +
          ∫⁻ ρ in Ioo b 1, ENNReal.ofReal ((1 - ρ) ^ (-s) / (1 - b * ρ)) :=
        lintegral_union_le _ _ _
    _ ≤ (∫⁻ ρ in Ioc 0 b, ENNReal.ofReal ((1 - ρ) ^ (-s - 1))) +
          ∫⁻ ρ in Ioo b 1, ENNReal.ofReal ((1 - b)⁻¹) * ENNReal.ofReal ((1 - ρ) ^ (-s)) := by
        gcongr ?_ + ?_
        · refine setLIntegral_mono' measurableSet_Ioc fun ρ hρ => ENNReal.ofReal_le_ofReal ?_
          have h1 : 0 < 1 - ρ := by linarith [hρ.2]
          have h2 : 1 - ρ ≤ 1 - b * ρ := by nlinarith [hρ.1]
          rw [Real.rpow_sub_one h1.ne']
          exact div_le_div_of_nonneg_left (Real.rpow_nonneg h1.le _) h1 h2
        · refine setLIntegral_mono' measurableSet_Ioo fun ρ hρ => ?_
          rw [← ENNReal.ofReal_mul (by positivity)]
          apply ENNReal.ofReal_le_ofReal
          have h1 : 0 < 1 - ρ := by linarith [hρ.2]
          have h2 : 1 - b ≤ 1 - b * ρ := by nlinarith [hρ.2]
          rw [inv_mul_eq_div]
          exact div_le_div_of_nonneg_left (Real.rpow_nonneg h1.le _) hδ h2
    _ = ENNReal.ofReal ((X - 1) / s) + ENNReal.ofReal (X / (1 - s)) := by
        rw [fr_lintegral_Ioc_rpow hs0 hb0 hb1, lintegral_const_mul _ (by fun_prop),
          fr_lintegral_Ioo_rpow hs1 hb1, ← ENNReal.ofReal_mul (by positivity), hXe]
    _ ≤ ENNReal.ofReal (X / s) + ENNReal.ofReal (X / (1 - s)) := by
        gcongr
        linarith
    _ = ENNReal.ofReal (X / (s * (1 - s))) := by
        have : 0 < 1 - s := by linarith
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        field_simp
        ring

theorem lintegral_disc_rpow_div_normSq {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {a : ℂ}
    (ha : a ∈ 𝔻) :
    ∫⁻ w in 𝔻, ENNReal.ofReal ((1 - ‖w‖) ^ (-s) / ‖1 - conj a * w‖ ^ 2) ≤
      ENNReal.ofReal (2 * Real.pi / (s * (1 - s)) * (1 - ‖a‖) ^ (-s)) := by
  have ha1 : ‖a‖ < 1 := norm_lt_one_of_mem_disc ha
  have hm : Measurable fun w : ℂ => ENNReal.ofReal ((1 - ‖w‖) ^ (-s) / ‖1 - conj a * w‖ ^ 2) := by
    fun_prop
  rw [lintegral_ball_eq_lintegral_circle 0 1 hm]
  calc ∫⁻ ρ in Ioo (0 : ℝ) 1, ENNReal.ofReal ρ * ∫⁻ θ in Ioc 0 (2 * Real.pi),
        ENNReal.ofReal ((1 - ‖circleMap 0 ρ θ‖) ^ (-s) / ‖1 - conj a * circleMap 0 ρ θ‖ ^ 2)
      ≤ ∫⁻ ρ in Ioo (0 : ℝ) 1, ENNReal.ofReal (2 * Real.pi) *
          ENNReal.ofReal ((1 - ρ) ^ (-s) / (1 - ‖a‖ * ρ)) := by
        refine setLIntegral_mono' measurableSet_Ioo fun ρ hρ => ?_
        have hρ0 : 0 < ρ := hρ.1
        have hρ1 : ρ < 1 := hρ.2
        have haρ : ‖a‖ * ρ < 1 := by nlinarith [norm_nonneg a]
        have hX : 0 ≤ (1 - ρ) ^ (-s) := Real.rpow_nonneg (by linarith) _
        have heq : ∀ θ, ENNReal.ofReal ((1 - ‖circleMap 0 ρ θ‖) ^ (-s) /
            ‖1 - conj a * circleMap 0 ρ θ‖ ^ 2) = ENNReal.ofReal ((1 - ρ) ^ (-s)) *
            ENNReal.ofReal (‖1 - conj a * circleMap 0 ρ θ‖⁻¹ ^ 2) := by
          intro θ
          rw [norm_circleMap_zero, abs_of_pos hρ0, ← ENNReal.ofReal_mul hX, inv_pow,
            div_eq_mul_inv]
        simp_rw [heq]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_circle_inv_normSq_one_sub hρ0.le haρ, ← ENNReal.ofReal_mul hX,
          ← ENNReal.ofReal_mul hρ0.le, ← ENNReal.ofReal_mul Real.two_pi_pos.le]
        apply ENNReal.ofReal_le_ofReal
        have h1 : 0 < 1 - ‖a‖ * ρ := by linarith
        have h2 : 1 - ‖a‖ * ρ ≤ 1 - ‖a‖ ^ 2 * ρ ^ 2 := by
          nlinarith [mul_nonneg (norm_nonneg a) hρ0.le]
        have h3 : 0 < 1 - ‖a‖ ^ 2 * ρ ^ 2 := lt_of_lt_of_le h1 h2
        rw [mul_div_assoc', mul_div_assoc', mul_div_assoc']
        rw [div_le_div_iff₀ h3 h1]
        have : 0 ≤ 2 * Real.pi * (1 - ρ) ^ (-s) := by positivity
        nlinarith [mul_le_mul_of_nonneg_left h2 this, mul_nonneg this h1.le]
    _ = ENNReal.ofReal (2 * Real.pi) *
          ∫⁻ ρ in Ioo (0 : ℝ) 1, ENNReal.ofReal ((1 - ρ) ^ (-s) / (1 - ‖a‖ * ρ)) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (2 * Real.pi) * ENNReal.ofReal ((1 - ‖a‖) ^ (-s) / (s * (1 - s))) := by
        gcongr
        exact lintegral_Ioo_rpow_div_le hs0 hs1 (norm_nonneg a) ha1
    _ = ENNReal.ofReal (2 * Real.pi / (s * (1 - s)) * (1 - ‖a‖) ^ (-s)) := by
        rw [← ENNReal.ofReal_mul Real.two_pi_pos.le]
        congr 1
        ring

/-- The near part of the Forelli–Rudin integral, for `0 < s ≤ 1` (`lintegral_FR_near` without
`s ≤ 1` is false). -/
theorem lintegral_FR_near_of_le_one {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) {a : ℂ} (ha : a ∈ 𝔻) :
    ∫⁻ w in ball a ((1 - ‖a‖) / 2),
        ENNReal.ofReal ((1 - ‖w‖ ^ 2) ^ (-s) / (‖1 - conj a * w‖ * ‖a - w‖)) ≤
      ENNReal.ofReal (2 * Real.pi * (1 - ‖a‖) ^ (-s)) := by
  have ha1 : ‖a‖ < 1 := norm_lt_one_of_mem_disc ha
  set d := 1 - ‖a‖ with hd
  have hd0 : 0 < d := by linarith
  have hd2 : 0 < d / 2 := by linarith
  calc ∫⁻ w in ball a (d / 2),
        ENNReal.ofReal ((1 - ‖w‖ ^ 2) ^ (-s) / (‖1 - conj a * w‖ * ‖a - w‖))
      ≤ ∫⁻ w in ball a (d / 2), ENNReal.ofReal ((d / 2) ^ (-s) / d) *
          ENNReal.ofReal ‖w - a‖⁻¹ := by
        refine setLIntegral_mono' measurableSet_ball fun w hw => ?_
        rw [← ENNReal.ofReal_mul (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        have hwa : ‖w - a‖ < d / 2 := by rwa [mem_ball, dist_eq_norm] at hw
        have hw1 : ‖w‖ < 1 - d / 2 := by
          have := norm_le_norm_sub_add w a  -- ‖w‖ ≤ ‖w - a‖ + ‖a‖
          linarith
        have hwn := norm_nonneg w
        have h1 : d / 2 ≤ 1 - ‖w‖ ^ 2 := by nlinarith
        have h2 : (1 - ‖w‖ ^ 2) ^ (-s) ≤ (d / 2) ^ (-s) :=
          Real.rpow_le_rpow_of_nonpos hd2 h1 (by linarith)
        have h3 : d ≤ ‖1 - conj a * w‖ := by
          have := one_sub_mul_le_norm_one_sub_conj_mul a w
          nlinarith [norm_nonneg a]
        rw [norm_sub_rev a w, ← div_div, div_eq_mul_inv _ ‖w - a‖]
        gcongr
    _ = ENNReal.ofReal ((d / 2) ^ (-s) / d) * ENNReal.ofReal (2 * Real.pi * (d / 2)) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_inv_norm_sub_ball a hd2.le]
    _ ≤ ENNReal.ofReal (2 * Real.pi * d ^ (-s)) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        rw [Real.div_rpow hd0.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
        have h2s : (2 : ℝ) ^ s ≤ 2 := by
          simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hs1
        have h2s0 : 0 < (2 : ℝ) ^ s := by positivity
        have hds : 0 ≤ d ^ (-s) := Real.rpow_nonneg hd0.le _
        field_simp
        nlinarith [Real.pi_pos, mul_le_mul_of_nonneg_left h2s (mul_nonneg Real.pi_pos.le hds)]

theorem lintegral_FR {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {a : ℂ} (ha : a ∈ 𝔻) :
    ∫⁻ w in 𝔻, ENNReal.ofReal ((1 - ‖w‖ ^ 2) ^ (-s) / (‖1 - conj a * w‖ * ‖a - w‖)) ≤
      ENNReal.ofReal (24 * Real.pi / (s * (1 - s)) * (1 - ‖a‖ ^ 2) ^ (-s)) := by
  have ha1 : ‖a‖ < 1 := norm_lt_one_of_mem_disc ha
  set d := 1 - ‖a‖ with hd
  have hd0 : 0 < d := by linarith
  set N := ball a (d / 2) with hN
  set g : ℂ → ℝ≥0∞ := fun w =>
    ENNReal.ofReal ((1 - ‖w‖ ^ 2) ^ (-s) / (‖1 - conj a * w‖ * ‖a - w‖)) with hg
  have hsub : 𝔻 ⊆ N ∪ (𝔻 \ N) := fun w hw => by
    by_cases h : w ∈ N
    · exact Or.inl h
    · exact Or.inr ⟨hw, h⟩
  have hfar : ∫⁻ w in 𝔻 \ N, g w ≤
      ENNReal.ofReal 5 * ENNReal.ofReal (2 * Real.pi / (s * (1 - s)) * d ^ (-s)) := by
    calc ∫⁻ w in 𝔻 \ N, g w
        ≤ ∫⁻ w in 𝔻 \ N, ENNReal.ofReal 5 *
            ENNReal.ofReal ((1 - ‖w‖) ^ (-s) / ‖1 - conj a * w‖ ^ 2) := by
          refine setLIntegral_mono' (measurableSet_ball.diff measurableSet_ball) fun w hw => ?_
          rw [hg, ← ENNReal.ofReal_mul (by norm_num)]
          apply ENNReal.ofReal_le_ofReal
          have hwD : w ∈ 𝔻 := hw.1
          have hw1 : ‖w‖ < 1 := norm_lt_one_of_mem_disc hwD
          have haw : d / 2 ≤ ‖a - w‖ := by
            have := hw.2
            rw [hN, mem_ball, dist_eq_norm, not_lt, norm_sub_rev] at this
            exact this
          have h5 := norm_one_sub_conj_mul_le_five_mul ha hwD haw
          have hY : 0 < ‖1 - conj a * w‖ := norm_one_sub_conj_mul_pos ha hwD
          have hZ : 0 < ‖a - w‖ := lt_of_lt_of_le (by linarith) haw
          have hX : (1 - ‖w‖ ^ 2) ^ (-s) ≤ (1 - ‖w‖) ^ (-s) :=
            Real.rpow_le_rpow_of_nonpos (by linarith) (by nlinarith [norm_nonneg w])
              (by linarith)
          have hX0 : 0 ≤ (1 - ‖w‖) ^ (-s) / ‖1 - conj a * w‖ ^ 2 :=
            div_nonneg (Real.rpow_nonneg (by linarith) _) (by positivity)
          rw [div_le_iff₀ (mul_pos hY hZ)]
          calc (1 - ‖w‖ ^ 2) ^ (-s) ≤ (1 - ‖w‖) ^ (-s) := hX
            _ = 5 * ((1 - ‖w‖) ^ (-s) / ‖1 - conj a * w‖ ^ 2) * (‖1 - conj a * w‖ *
                  (‖1 - conj a * w‖ / 5)) := by field_simp
            _ ≤ 5 * ((1 - ‖w‖) ^ (-s) / ‖1 - conj a * w‖ ^ 2) * (‖1 - conj a * w‖ * ‖a - w‖) := by
                exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith) hY.le)
                  (by positivity)
      _ ≤ ∫⁻ w in 𝔻, ENNReal.ofReal 5 *
            ENNReal.ofReal ((1 - ‖w‖) ^ (-s) / ‖1 - conj a * w‖ ^ 2) :=
          lintegral_mono_set sdiff_subset
      _ = ENNReal.ofReal 5 *
            ∫⁻ w in 𝔻, ENNReal.ofReal ((1 - ‖w‖) ^ (-s) / ‖1 - conj a * w‖ ^ 2) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ _ := by gcongr; exact lintegral_disc_rpow_div_normSq hs0 hs1 ha
  calc ∫⁻ w in 𝔻, g w ≤ ∫⁻ w in N ∪ (𝔻 \ N), g w := lintegral_mono_set hsub
    _ ≤ (∫⁻ w in N, g w) + ∫⁻ w in 𝔻 \ N, g w := lintegral_union_le _ _ _
    _ ≤ ENNReal.ofReal (2 * Real.pi * d ^ (-s)) +
          ENNReal.ofReal 5 * ENNReal.ofReal (2 * Real.pi / (s * (1 - s)) * d ^ (-s)) :=
        add_le_add (lintegral_FR_near_of_le_one hs0 hs1.le ha) hfar
    _ ≤ _ := by
        have hP0 : 0 < s * (1 - s) := mul_pos hs0 (by linarith)
        have hP1 : s * (1 - s) ≤ 1 := by nlinarith
        have hD0 : 0 ≤ d ^ (-s) := Real.rpow_nonneg hd0.le _
        have hE0 : 0 < 1 - ‖a‖ ^ 2 := by nlinarith [norm_nonneg a]
        have hDE : d ^ (-s) ≤ 2 * (1 - ‖a‖ ^ 2) ^ (-s) := by
          have h1 : (1 - ‖a‖ ^ 2) / 2 ≤ d := by nlinarith [norm_nonneg a]
          calc d ^ (-s) ≤ ((1 - ‖a‖ ^ 2) / 2) ^ (-s) :=
                Real.rpow_le_rpow_of_nonpos (by positivity) h1 (by linarith)
            _ = 2 ^ s * (1 - ‖a‖ ^ 2) ^ (-s) := by
                rw [Real.div_rpow hE0.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
                field_simp
            _ ≤ 2 * (1 - ‖a‖ ^ 2) ^ (-s) := by
                gcongr
                simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hs1.le
        rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity)
          (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        have hA : 2 * Real.pi * d ^ (-s) ≤ 2 * Real.pi * d ^ (-s) / (s * (1 - s)) :=
          le_div_self (by positivity) hP0 hP1
        calc 2 * Real.pi * d ^ (-s) + 5 * (2 * Real.pi / (s * (1 - s)) * d ^ (-s))
            ≤ 2 * Real.pi * d ^ (-s) / (s * (1 - s)) +
                5 * (2 * Real.pi / (s * (1 - s)) * d ^ (-s)) := by linarith
          _ = 12 * Real.pi / (s * (1 - s)) * d ^ (-s) := by ring
          _ ≤ 12 * Real.pi / (s * (1 - s)) * (2 * (1 - ‖a‖ ^ 2) ^ (-s)) := by gcongr
          _ = 24 * Real.pi / (s * (1 - s)) * (1 - ‖a‖ ^ 2) ^ (-s) := by ring

/-- Forelli–Rudin, the case `∫_𝔻 dm(w)/|1 − z̄w|³ ≲ (1 − |z|²)⁻¹` used by M08 (far field in the
disc, `farField_sum_le_disc`). -/
theorem integral_one_sub_conj_mul_rpow_neg_three_le :
    ∃ C : ℝ, ∀ z ∈ 𝔻,
      ∫⁻ w in 𝔻, ENNReal.ofReal (1 / ‖1 - conj z * w‖ ^ 3) ≤ ENNReal.ofReal (C / (1 - ‖z‖ ^ 2)) := by
  refine ⟨16 * Real.pi, fun z hz => ?_⟩
  have hz1 : ‖z‖ < 1 := norm_lt_one_of_mem_disc hz
  set u := 1 - ‖z‖ with hu
  have hu0 : 0 < u := by linarith
  have hs : (0 : ℝ) < 1 / 2 := by norm_num
  calc ∫⁻ w in 𝔻, ENNReal.ofReal (1 / ‖1 - conj z * w‖ ^ 3)
      ≤ ∫⁻ w in 𝔻, ENNReal.ofReal (u ^ (-(1 / 2 : ℝ))) *
          ENNReal.ofReal ((1 - ‖w‖) ^ (-(1 / 2 : ℝ)) / ‖1 - conj z * w‖ ^ 2) := by
        refine setLIntegral_mono' measurableSet_ball fun w hw => ?_
        rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hu0.le _)]
        apply ENNReal.ofReal_le_ofReal
        have hw1 : ‖w‖ < 1 := norm_lt_one_of_mem_disc hw
        set v := 1 - ‖w‖ with hv
        have hv0 : 0 < v := by linarith
        set Y := ‖1 - conj z * w‖ with hY
        have hY0 : 0 < Y := norm_one_sub_conj_mul_pos hz hw
        have hYl := one_sub_mul_le_norm_one_sub_conj_mul z w
        have hYu : u ≤ Y := by nlinarith [norm_nonneg z, norm_nonneg w]
        have hYv : v ≤ Y := by nlinarith [norm_nonneg z, norm_nonneg w]
        have hsq : Real.sqrt u * Real.sqrt v ≤ Y := by
          rw [← Real.sqrt_mul hu0.le, ← Real.sqrt_sq hY0.le]
          exact Real.sqrt_le_sqrt (by nlinarith)
        have hsu : 0 < Real.sqrt u := Real.sqrt_pos.2 hu0
        have hsv : 0 < Real.sqrt v := Real.sqrt_pos.2 hv0
        rw [Real.rpow_neg hu0.le, Real.rpow_neg hv0.le, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
        rw [show (Real.sqrt u)⁻¹ * ((Real.sqrt v)⁻¹ / Y ^ 2) = 1 / (Real.sqrt u * Real.sqrt v * Y ^ 2)
          by field_simp]
        apply one_div_le_one_div_of_le (by positivity)
        rw [pow_succ']
        nlinarith [mul_le_mul_of_nonneg_right hsq (sq_nonneg Y)]
    _ = ENNReal.ofReal (u ^ (-(1 / 2 : ℝ))) *
          ∫⁻ w in 𝔻, ENNReal.ofReal ((1 - ‖w‖) ^ (-(1 / 2 : ℝ)) / ‖1 - conj z * w‖ ^ 2) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (u ^ (-(1 / 2 : ℝ))) *
          ENNReal.ofReal (2 * Real.pi / (1 / 2 * (1 - 1 / 2)) * u ^ (-(1 / 2 : ℝ))) := by
        gcongr
        exact lintegral_disc_rpow_div_normSq hs (by norm_num) hz
    _ ≤ ENNReal.ofReal (16 * Real.pi / (1 - ‖z‖ ^ 2)) := by
        rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hu0.le _)]
        apply ENNReal.ofReal_le_ofReal
        have hE : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
        have hE2 : 1 - ‖z‖ ^ 2 ≤ 2 * u := by nlinarith [norm_nonneg z]
        have huu : u ^ (-(1 / 2 : ℝ)) * u ^ (-(1 / 2 : ℝ)) = u⁻¹ := by
          rw [← Real.rpow_add hu0]; norm_num [Real.rpow_neg_one]
        calc u ^ (-(1 / 2 : ℝ)) * (2 * Real.pi / (1 / 2 * (1 - 1 / 2)) * u ^ (-(1 / 2 : ℝ)))
            = 8 * Real.pi / u := by
              rw [mul_comm, mul_assoc, mul_comm (u ^ _), huu]; field_simp; norm_num
          _ ≤ 16 * Real.pi / (1 - ‖z‖ ^ 2) := by
              rw [div_le_div_iff₀ hu0 hE]
              nlinarith [Real.pi_pos]

/-! ## §3 Positive model kernels and their Schur bounds -/

/-- The positive model kernel of the disc, `(1-|z|²)^c (1-|ζ|²)^{1-c} / (|1-ζ̄z| |z-ζ|)`. -/
def discModel (c : ℝ) (z ζ : ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal ((1 - ‖z‖ ^ 2) ^ c * (1 - ‖ζ‖ ^ 2) ^ (1 - c) /
    (‖1 - conj ζ * z‖ * ‖z - ζ‖))

theorem measurable_discModel (c : ℝ) : Measurable (Function.uncurry (discModel c)) := by
  unfold discModel Function.uncurry
  fun_prop

theorem norm_one_sub_conj_mul_comm (a b : ℂ) : ‖1 - conj a * b‖ = ‖1 - conj b * a‖ := by
  rw [← Complex.norm_conj (1 - conj b * a)]
  congr 1
  simp [map_sub, mul_comm]

theorem measurable_discDensity :
    Measurable fun z : ℂ ↦ ENNReal.ofReal (1 / (1 - ‖z‖ ^ 2)) := by fun_prop

theorem lintegral_discMeasure_eq (g : ℂ → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ z, g z ∂discMeasure = ∫⁻ z in 𝔻, ENNReal.ofReal (1 / (1 - ‖z‖ ^ 2)) * g z := by
  rw [discMeasure, lintegral_withDensity_eq_lintegral_mul _ measurable_discDensity hg]
  rfl

theorem ae_discMeasure_mem : ∀ᵐ z ∂discMeasure, z ∈ 𝔻 :=
  (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_ball)

theorem lintegral_discModel_left {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) {z : ℂ} (hz : z ∈ 𝔻) :
    ∫⁻ ζ, discModel c z ζ ∂discMeasure ≤ ENNReal.ofReal (24 * Real.pi / (c * (1 - c))) := by
  have hz0 : 0 < 1 - ‖z‖ ^ 2 := one_sub_normSq_pos hz
  rw [lintegral_discMeasure_eq _ ((measurable_discModel c).of_uncurry_left)]
  calc ∫⁻ ζ in 𝔻, ENNReal.ofReal (1 / (1 - ‖ζ‖ ^ 2)) * discModel c z ζ
      = ∫⁻ ζ in 𝔻, ENNReal.ofReal ((1 - ‖z‖ ^ 2) ^ c) *
          ENNReal.ofReal ((1 - ‖ζ‖ ^ 2) ^ (-c) / (‖1 - conj z * ζ‖ * ‖z - ζ‖)) := by
        refine setLIntegral_congr_fun measurableSet_ball fun ζ hζ => ?_
        have hζ0 : 0 < 1 - ‖ζ‖ ^ 2 := one_sub_normSq_pos hζ
        rw [discModel, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity), norm_one_sub_conj_mul_comm ζ z]
        congr 1
        rw [show 1 - c = 1 + -c by ring, Real.rpow_add hζ0, Real.rpow_one]
        field_simp
    _ = ENNReal.ofReal ((1 - ‖z‖ ^ 2) ^ c) * ∫⁻ ζ in 𝔻,
          ENNReal.ofReal ((1 - ‖ζ‖ ^ 2) ^ (-c) / (‖1 - conj z * ζ‖ * ‖z - ζ‖)) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal ((1 - ‖z‖ ^ 2) ^ c) *
          ENNReal.ofReal (24 * Real.pi / (c * (1 - c)) * (1 - ‖z‖ ^ 2) ^ (-c)) := by
        gcongr
        exact lintegral_FR hc0 hc1 hz
    _ = ENNReal.ofReal (24 * Real.pi / (c * (1 - c))) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [Real.rpow_neg hz0.le]
        have : (1 - ‖z‖ ^ 2) ^ c ≠ 0 := (Real.rpow_pos_of_pos hz0 _).ne'
        field_simp

theorem lintegral_discModel_right {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) {ζ : ℂ} (hζ : ζ ∈ 𝔻) :
    ∫⁻ z, discModel c z ζ ∂discMeasure ≤ ENNReal.ofReal (24 * Real.pi / (c * (1 - c))) := by
  have hζ0 : 0 < 1 - ‖ζ‖ ^ 2 := one_sub_normSq_pos hζ
  rw [lintegral_discMeasure_eq _ ((measurable_discModel c).of_uncurry_right)]
  calc ∫⁻ z in 𝔻, ENNReal.ofReal (1 / (1 - ‖z‖ ^ 2)) * discModel c z ζ
      = ∫⁻ z in 𝔻, ENNReal.ofReal ((1 - ‖ζ‖ ^ 2) ^ (1 - c)) *
          ENNReal.ofReal ((1 - ‖z‖ ^ 2) ^ (-(1 - c)) / (‖1 - conj ζ * z‖ * ‖ζ - z‖)) := by
        refine setLIntegral_congr_fun measurableSet_ball fun z hz => ?_
        have hz0 : 0 < 1 - ‖z‖ ^ 2 := one_sub_normSq_pos hz
        rw [discModel, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity), norm_sub_rev ζ z]
        congr 1
        rw [show c = 1 + -(1 - c) by ring, Real.rpow_add hz0, Real.rpow_one,
          show 1 - (1 + -(1 - c)) = 1 - c by ring]
        field_simp
    _ = ENNReal.ofReal ((1 - ‖ζ‖ ^ 2) ^ (1 - c)) * ∫⁻ z in 𝔻,
          ENNReal.ofReal ((1 - ‖z‖ ^ 2) ^ (-(1 - c)) / (‖1 - conj ζ * z‖ * ‖ζ - z‖)) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal ((1 - ‖ζ‖ ^ 2) ^ (1 - c)) * ENNReal.ofReal
          (24 * Real.pi / ((1 - c) * (1 - (1 - c))) * (1 - ‖ζ‖ ^ 2) ^ (-(1 - c))) := by
        gcongr
        exact lintegral_FR (by linarith) (by linarith) hζ
    _ = ENNReal.ofReal (24 * Real.pi / (c * (1 - c))) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [Real.rpow_neg hζ0.le, show 1 - (1 - c) = c by ring]
        have : (1 - ‖ζ‖ ^ 2) ^ (1 - c) ≠ 0 := (Real.rpow_pos_of_pos hζ0 _).ne'
        field_simp

instance sigmaFinite_discMeasure : SigmaFinite discMeasure := by
  unfold discMeasure; infer_instance

theorem eLpNorm_discModel_le {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) {F : ℂ → ℝ≥0∞}
    (hF : AEMeasurable F discMeasure) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    eLpNorm (fun z ↦ ∫⁻ ζ, discModel c z ζ * F ζ ∂discMeasure) p discMeasure ≤
      ENNReal.ofReal (24 * Real.pi / (c * (1 - c))) * eLpNorm F p discMeasure :=
  schur_test_le_max (measurable_discModel c)
    (ae_discMeasure_mem.mono fun _ hz => lintegral_discModel_left hc0 hc1 hz)
    (ae_discMeasure_mem.mono fun _ hζ => lintegral_discModel_right hc0 hc1 hζ) hF hp

/-- The Gaussian model kernel of the plane, `e^{-c|z-ζ|²} / |z-ζ|`. -/
def planeModel (c : ℝ) (z ζ : ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-c * ‖z - ζ‖ ^ 2) / ‖z - ζ‖)

theorem measurable_planeModel (c : ℝ) : Measurable (Function.uncurry (planeModel c)) := by
  unfold planeModel Function.uncurry
  fun_prop

theorem lintegral_planeModel_aux {c : ℝ} (hc : 0 < c) (z : ℂ) :
    ∫⁻ ζ, ENNReal.ofReal (Real.exp (-c * ‖ζ - z‖ ^ 2) / ‖ζ - z‖) =
      ENNReal.ofReal (Real.pi * Real.sqrt (Real.pi / c)) := by
  rw [lintegral_comp_norm_sub z (F := fun s ↦ ENNReal.ofReal (Real.exp (-c * s ^ 2) / s))
    (by fun_prop)]
  rw [setLIntegral_congr_fun measurableSet_Ioi (g := fun s ↦ ENNReal.ofReal (Real.exp (-c * s ^ 2)))
    (fun s (hs : 0 < s) ↦ by
      rw [← ENNReal.ofReal_mul hs.le]; congr 1; field_simp)]
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_exp_neg_mul_sq hc).integrableOn
    (Filter.Eventually.of_forall fun s ↦ (Real.exp_pos _).le), integral_gaussian_Ioi,
    ← ENNReal.ofReal_mul Real.two_pi_pos.le]
  congr 1
  ring

theorem lintegral_planeModel_left {c : ℝ} (hc : 0 < c) (z : ℂ) :
    ∫⁻ ζ, planeModel c z ζ = ENNReal.ofReal (Real.pi * Real.sqrt (Real.pi / c)) := by
  simp_rw [planeModel, norm_sub_rev z]
  exact lintegral_planeModel_aux hc z

theorem lintegral_planeModel_right {c : ℝ} (hc : 0 < c) (ζ : ℂ) :
    ∫⁻ z, planeModel c z ζ = ENNReal.ofReal (Real.pi * Real.sqrt (Real.pi / c)) :=
  lintegral_planeModel_aux hc ζ

theorem eLpNorm_planeModel_le {c : ℝ} (hc : 0 < c) {F : ℂ → ℝ≥0∞} (hF : AEMeasurable F)
    {p : ℝ≥0∞} (hp : 1 ≤ p) :
    eLpNorm (fun z ↦ ∫⁻ ζ, planeModel c z ζ * F ζ) p volume ≤
      ENNReal.ofReal (Real.pi * Real.sqrt (Real.pi / c)) * eLpNorm F p volume :=
  schur_test_le_max (measurable_planeModel c)
    (Filter.Eventually.of_forall fun z => (lintegral_planeModel_left hc z).le)
    (Filter.Eventually.of_forall fun ζ => (lintegral_planeModel_right hc ζ).le) hF hp

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

theorem continuousOn_discDensity : ContinuousOn (fun z : ℂ ↦ 1 / (1 - ‖z‖ ^ 2)) 𝔻 :=
  continuousOn_const.div (by fun_prop) fun _ hz ↦ (one_sub_normSq_pos hz).ne'

theorem volume_restrict_disc_le_discMeasure : volume.restrict 𝔻 ≤ discMeasure := by
  calc volume.restrict 𝔻 = (volume.restrict 𝔻).withDensity 1 := withDensity_one.symm
    _ ≤ discMeasure := by
      refine withDensity_mono ?_
      filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
      simp only [Pi.one_apply, ENNReal.one_le_ofReal]
      have := one_sub_normSq_pos hz
      rw [le_div_iff₀ this]
      nlinarith [norm_nonneg z]

theorem discMeasure_lt_top_of_isCompact {K : Set ℂ} (hK : IsCompact K) (hKD : K ⊆ 𝔻) :
    discMeasure K < ∞ := by
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn (continuousOn_discDensity.mono hKD)
  rw [discMeasure, withDensity_apply _ hK.measurableSet]
  calc ∫⁻ z in K, ENNReal.ofReal (1 / (1 - ‖z‖ ^ 2)) ∂(volume.restrict 𝔻)
      ≤ ∫⁻ z in K, ENNReal.ofReal B ∂(volume.restrict 𝔻) :=
        setLIntegral_mono' hK.measurableSet fun z hz ↦
          ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (hB z hz))
    _ = ENNReal.ofReal B * (volume.restrict 𝔻) K := setLIntegral_const _ _
    _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (lt_of_le_of_lt (Measure.restrict_apply_le _ _) hK.measure_lt_top)

theorem lintegral_lt_top_of_eLpNorm_discMeasure {g : ℂ → ℝ≥0∞}
    (hg : AEStronglyMeasurable g discMeasure) {K : Set ℂ} (hK : IsCompact K) (hKD : K ⊆ 𝔻)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hfin : eLpNorm g p discMeasure < ∞) :
    ∫⁻ z in K, g z < ∞ := by
  have h1 : volume.restrict K ≤ discMeasure.restrict K := by
    calc volume.restrict K = (volume.restrict 𝔻).restrict K := by
          rw [Measure.restrict_restrict_of_subset hKD]
      _ ≤ discMeasure.restrict K :=
          Measure.restrict_mono subset_rfl volume_restrict_disc_le_discMeasure
  have hexp : 0 ≤ 1 / (1 : ℝ≥0∞).toReal - 1 / p.toReal := by
    rw [ENNReal.toReal_one, div_one, sub_nonneg]
    rcases eq_or_ne p ∞ with rfl | hpt
    · simp
    · exact div_le_one_of_le₀ (by rw [← ENNReal.toReal_one]; exact ENNReal.toReal_mono hpt hp)
        ENNReal.toReal_nonneg
  calc ∫⁻ z in K, g z ≤ ∫⁻ z, g z ∂(discMeasure.restrict K) := lintegral_mono' h1 le_rfl
    _ = eLpNorm g 1 (discMeasure.restrict K) := by
        rw [eLpNorm_one_eq_lintegral_enorm hg.restrict]; simp
    _ ≤ eLpNorm g p (discMeasure.restrict K) *
          (discMeasure.restrict K) univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / p.toReal) :=
        eLpNorm_le_eLpNorm_mul_rpow_measure_univ hp hg.restrict
    _ ≤ eLpNorm g p discMeasure *
          (discMeasure.restrict K) univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / p.toReal) := by
        gcongr
        exact Measure.restrict_le_self
    _ < ∞ := by
        refine ENNReal.mul_lt_top hfin (ENNReal.rpow_lt_top_of_nonneg hexp ?_)
        rw [Measure.restrict_apply_univ]
        exact (discMeasure_lt_top_of_isCompact hK hKD).ne

/-- The pointwise bound of the conjugated disc kernel by the positive model kernel. -/
theorem norm_discKernelH_le {φ : ℂ → ℝ} {c A : ℝ} {H : ℂ → ℂ → ℂ}
    (hHb : ∀ z ∈ 𝔻, ∀ ζ ∈ 𝔻, ‖H z ζ‖ ≤ A * Real.exp (φ z - φ ζ) *
      ((1 - ‖z‖ ^ 2) / (1 - ‖ζ‖ ^ 2)) ^ c * ((1 - ‖ζ‖ ^ 2) / ‖1 - conj ζ * z‖))
    {z ζ : ℂ} (hz : z ∈ 𝔻) (hζ : ζ ∈ 𝔻) :
    ‖H z ζ / ((Real.pi : ℂ) * (z - ζ))‖ ≤ A / Real.pi * Real.exp (φ z - φ ζ) *
      ((1 - ‖z‖ ^ 2) ^ c * (1 - ‖ζ‖ ^ 2) ^ (1 - c) / (‖1 - conj ζ * z‖ * ‖z - ζ‖)) := by
  have hz0 := one_sub_normSq_pos hz
  have hζ0 := one_sub_normSq_pos hζ
  have hY := norm_one_sub_conj_mul_pos hζ hz
  have hpi := Real.pi_pos
  rw [norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg hpi.le]
  rcases eq_or_ne z ζ with rfl | hne
  · simp
  have hZ : 0 < ‖z - ζ‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  have hζc := Real.rpow_pos_of_pos hζ0 c
  calc ‖H z ζ‖ / (Real.pi * ‖z - ζ‖)
      ≤ (A * Real.exp (φ z - φ ζ) * ((1 - ‖z‖ ^ 2) / (1 - ‖ζ‖ ^ 2)) ^ c *
          ((1 - ‖ζ‖ ^ 2) / ‖1 - conj ζ * z‖)) / (Real.pi * ‖z - ζ‖) := by
        gcongr
        exact hHb z hz ζ hζ
    _ = _ := by
        rw [Real.div_rpow hz0.le hζ0.le, Real.rpow_sub hζ0, Real.rpow_one]
        field_simp

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
            eLpNorm (fun z ↦ f z * ((1 - ‖z‖ ^ 2) * Real.exp (-φ z) : ℝ)) p discMeasure := by
  set u : ℂ → ℂ := fun z ↦ ∫ ζ in 𝔻, H z ζ / ((Real.pi : ℂ) * (z - ζ)) * f ζ with hu
  set F : ℂ → ℂ := fun z ↦ f z * ((1 - ‖z‖ ^ 2) * Real.exp (-φ z) : ℝ) with hFdef
  obtain ⟨p₀, hp₀, hFfin⟩ := hadm
  have h0 : (0 : ℂ) ∈ 𝔻 := mem_ball_self one_pos
  have hA : 1 ≤ A := by
    have := hHb 0 h0 0 h0
    simpa [hH1 0 h0] using this
  have hpi := Real.pi_pos
  have hAπ : 0 ≤ A / Real.pi := div_nonneg (by linarith) hpi.le
  have hνac : discMeasure ≪ volume.restrict 𝔻 := withDensity_absolutelyContinuous _ _
  have hwc : ContinuousOn (fun z : ℂ ↦ (((1 - ‖z‖ ^ 2) * Real.exp (-φ z) : ℝ) : ℂ)) 𝔻 :=
    Complex.continuous_ofReal.comp_continuousOn
      ((by fun_prop : Continuous fun z : ℂ ↦ 1 - ‖z‖ ^ 2).continuousOn.mul
        (Real.continuous_exp.comp_continuousOn hφ.neg))
  have hF : AEStronglyMeasurable F discMeasure :=
    (hf.mul (hwc.aestronglyMeasurable measurableSet_ball)).mono_ac hνac
  have hFe : AEMeasurable (fun z ↦ ‖F z‖ₑ) discMeasure := hF.enorm
  have hFnorm : ∀ ζ ∈ 𝔻, ‖F ζ‖ = ‖f ζ‖ * ((1 - ‖ζ‖ ^ 2) * Real.exp (-φ ζ)) := by
    intro ζ hζ
    rw [hFdef, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (mul_nonneg (one_sub_normSq_pos hζ).le (Real.exp_pos _).le)]
  set TF : ℂ → ℝ≥0∞ := fun z ↦ ∫⁻ ζ, discModel c z ζ * ‖F ζ‖ₑ ∂discMeasure with hTF
  have hTFm : AEStronglyMeasurable TF discMeasure := by
    have : AEMeasurable (fun q : ℂ × ℂ ↦ discModel c q.1 q.2 * ‖F q.2‖ₑ)
        (discMeasure.prod discMeasure) :=
      (measurable_discModel c).aemeasurable.mul hFe.comp_snd
    exact this.lintegral_prod_right'.aestronglyMeasurable
  have hTFb : ∀ p : ℝ≥0∞, 1 ≤ p →
      eLpNorm TF p discMeasure ≤
        ENNReal.ofReal (24 * Real.pi / (c * (1 - c))) * eLpNorm F p discMeasure := by
    intro p hp
    have := eLpNorm_discModel_le hc0 hc1 hFe hp
    rwa [eLpNorm_enorm _ hF] at this
  -- the key pointwise estimate
  have hKP : ∀ z ∈ 𝔻, ∫⁻ ζ in 𝔻, ‖H z ζ / ((Real.pi : ℂ) * (z - ζ))‖ₑ * ‖f ζ‖ₑ ≤
      ENNReal.ofReal (A / Real.pi * Real.exp (φ z)) * TF z := by
    intro z hz
    simp only [hTF]
    rw [discMeasure, lintegral_withDensity_eq_lintegral_mul_non_measurable _
      measurable_discDensity (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top),
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_mono' measurableSet_ball fun ζ hζ ↦ ?_
    have hz0 := one_sub_normSq_pos hz
    have hζ0 := one_sub_normSq_pos hζ
    have hM0 : 0 ≤ (1 - ‖z‖ ^ 2) ^ c * (1 - ‖ζ‖ ^ 2) ^ (1 - c) /
        (‖1 - conj ζ * z‖ * ‖z - ζ‖) := by positivity
    simp only [Pi.mul_apply, discModel]
    rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm,
      ← ENNReal.ofReal_mul (norm_nonneg _), ← ENNReal.ofReal_mul hM0,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      hFnorm ζ hζ]
    apply ENNReal.ofReal_le_ofReal
    calc ‖H z ζ / ((Real.pi : ℂ) * (z - ζ))‖ * ‖f ζ‖
        ≤ (A / Real.pi * Real.exp (φ z - φ ζ) *
            ((1 - ‖z‖ ^ 2) ^ c * (1 - ‖ζ‖ ^ 2) ^ (1 - c) / (‖1 - conj ζ * z‖ * ‖z - ζ‖))) *
              ‖f ζ‖ :=
          mul_le_mul_of_nonneg_right (norm_discKernelH_le hHb hz hζ) (norm_nonneg _)
      _ = _ := by
          rw [Real.exp_sub, Real.exp_neg]
          field_simp
  -- local integrability of `f`
  have hfl : LocallyIntegrableOn f 𝔻 := by
    rw [locallyIntegrableOn_iff isOpen_ball.isLocallyClosed]
    intro K hKD hK
    refine ⟨hf.mono_measure (Measure.restrict_mono hKD le_rfl), ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hφ.mono hKD)
    obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn (continuousOn_discDensity.mono hKD)
    calc ∫⁻ z in K, ‖f z‖ₑ ≤ ∫⁻ z in K, ENNReal.ofReal (Real.exp C * B) * ‖F z‖ₑ := by
          refine setLIntegral_mono' hK.measurableSet fun z hzK ↦ ?_
          have hz := hKD hzK
          have hz0 := one_sub_normSq_pos hz
          rw [← ofReal_norm, ← ofReal_norm,
            ← ENNReal.ofReal_mul (mul_nonneg (Real.exp_pos _).le
              ((norm_nonneg _).trans (hB z hzK))), hFnorm z hz]
          apply ENNReal.ofReal_le_ofReal
          have h1 : Real.exp (φ z) ≤ Real.exp C :=
            Real.exp_le_exp.2 ((le_abs_self _).trans (hC z hzK))
          have h2 : 1 / (1 - ‖z‖ ^ 2) ≤ B := (le_abs_self _).trans (hB z hzK)
          calc ‖f z‖ = (Real.exp (φ z) * (1 / (1 - ‖z‖ ^ 2))) *
                (‖f z‖ * ((1 - ‖z‖ ^ 2) * Real.exp (-φ z))) := by
                rw [Real.exp_neg]; field_simp
            _ ≤ (Real.exp C * B) * (‖f z‖ * ((1 - ‖z‖ ^ 2) * Real.exp (-φ z))) := by
                gcongr
      _ = ENNReal.ofReal (Real.exp C * B) * ∫⁻ z in K, ‖F z‖ₑ :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          (lintegral_lt_top_of_eLpNorm_discMeasure hFe.aestronglyMeasurable hK hKD hp₀
            (by rwa [eLpNorm_enorm _ hF]))
  -- the local Fubini condition
  have hloc : ∀ K ⊆ 𝔻, IsCompact K →
      ∫⁻ z in K, ∫⁻ ζ in 𝔻, ‖H z ζ / ((Real.pi : ℂ) * (z - ζ))‖ₑ * ‖f ζ‖ₑ < ∞ := by
    intro K hKD hK
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hφ.mono hKD)
    calc ∫⁻ z in K, ∫⁻ ζ in 𝔻, ‖H z ζ / ((Real.pi : ℂ) * (z - ζ))‖ₑ * ‖f ζ‖ₑ
        ≤ ∫⁻ z in K, ENNReal.ofReal (A / Real.pi * Real.exp C) * TF z := by
          refine setLIntegral_mono' hK.measurableSet fun z hzK ↦ (hKP z (hKD hzK)).trans ?_
          gcongr
          exact (le_abs_self _).trans (hC z hzK)
      _ = ENNReal.ofReal (A / Real.pi * Real.exp C) * ∫⁻ z in K, TF z :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          (lintegral_lt_top_of_eLpNorm_discMeasure hTFm hK hKD hp₀
            ((hTFb p₀ hp₀).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hFfin)))
  refine ⟨isWeakDbarSol_kernel isOpen_ball hHm hHd hH1 hf hfl hloc, fun p hp ↦ ?_⟩
  -- the `L^p` estimate
  have hum : AEStronglyMeasurable u volume := weak_aestronglyMeasurable_kernelOp hHm hf
  have hEc : ContinuousOn (fun z : ℂ ↦ ((Real.exp (-φ z) : ℝ) : ℂ)) 𝔻 :=
    Complex.continuous_ofReal.comp_continuousOn (Real.continuous_exp.comp_continuousOn hφ.neg)
  have hv : AEStronglyMeasurable (fun z ↦ u z * ((Real.exp (-φ z) : ℝ) : ℂ)) discMeasure :=
    (hum.restrict.mul (hEc.aestronglyMeasurable measurableSet_ball)).mono_ac hνac
  have hpt : ∀ᵐ z ∂discMeasure, ‖u z * ((Real.exp (-φ z) : ℝ) : ℂ)‖ₑ ≤
      ‖ENNReal.ofReal (A / Real.pi) * TF z‖ₑ := by
    filter_upwards [ae_discMeasure_mem] with z hz
    rw [enorm_eq_self, enorm_mul, ← ofReal_norm (((Real.exp (-φ z) : ℝ) : ℂ)),
      Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    calc ‖u z‖ₑ * ENNReal.ofReal (Real.exp (-φ z))
        ≤ (∫⁻ ζ in 𝔻, ‖H z ζ / ((Real.pi : ℂ) * (z - ζ))‖ₑ * ‖f ζ‖ₑ) *
            ENNReal.ofReal (Real.exp (-φ z)) := by
          gcongr
          refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
          simp_rw [enorm_mul]
      _ ≤ ENNReal.ofReal (A / Real.pi * Real.exp (φ z)) * TF z *
            ENNReal.ofReal (Real.exp (-φ z)) := by
          gcongr
          exact hKP z hz
      _ = ENNReal.ofReal (A / Real.pi) * TF z := by
          rw [mul_comm _ (TF z), mul_assoc, ← ENNReal.ofReal_mul (by positivity), mul_assoc,
            ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one, mul_comm]
  calc eLpNorm (fun z ↦ u z * ((Real.exp (-φ z) : ℝ) : ℂ)) p discMeasure
      ≤ eLpNorm (fun z ↦ ENNReal.ofReal (A / Real.pi) * TF z) p discMeasure :=
        eLpNorm_mono_enorm_ae hv hpt
    _ = ENNReal.ofReal (A / Real.pi) * eLpNorm TF p discMeasure :=
        eLpNorm_const_mul_ennreal hTFm
    _ ≤ ENNReal.ofReal (A / Real.pi) *
          (ENNReal.ofReal (24 * Real.pi / (c * (1 - c))) * eLpNorm F p discMeasure) := by
        gcongr
        exact hTFb p hp
    _ = ENNReal.ofReal (24 * A / (c * (1 - c))) * eLpNorm F p discMeasure := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hAπ]
        congr 2
        field_simp

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

/-- The numerator `H(z, ζ) = (1 - |ζ|²)/(1 - ζ̄ z)` of the kernel of Lemma 7. -/
def lemma7H (z ζ : ℂ) : ℂ := ((1 - ‖ζ‖ ^ 2 : ℝ) : ℂ) / (1 - conj ζ * z)

theorem measurable_lemma7H : Measurable (Function.uncurry lemma7H) := by
  unfold lemma7H Function.uncurry
  fun_prop

theorem differentiableOn_lemma7H {ζ : ℂ} (hζ : ζ ∈ 𝔻) :
    DifferentiableOn ℂ (fun z ↦ lemma7H z ζ) 𝔻 := by
  unfold lemma7H
  exact (differentiableOn_const _).div ((differentiableOn_const _).sub
    ((differentiableOn_const _).mul differentiableOn_id))
    fun z hz ↦ one_sub_conj_mul_ne_zero_of_mem hζ hz

theorem lemma7H_self {ζ : ℂ} (hζ : ζ ∈ 𝔻) : lemma7H ζ ζ = 1 := by
  rw [lemma7H, one_sub_conj_mul_self]
  exact div_self (by exact_mod_cast (one_sub_normSq_pos hζ).ne')

theorem norm_lemma7H {z ζ : ℂ} (hζ : ζ ∈ 𝔻) :
    ‖lemma7H z ζ‖ = (1 - ‖ζ‖ ^ 2) / ‖1 - conj ζ * z‖ := by
  rw [lemma7H, norm_div, Complex.norm_real, Real.norm_of_nonneg (one_sub_normSq_pos hζ).le]

theorem lemma7Op_eq (f : ℂ → ℂ) :
    lemma7Op f = fun z ↦ ∫ ζ in 𝔻, lemma7H z ζ / ((Real.pi : ℂ) * (z - ζ)) * f ζ := rfl

theorem lemma7_isWeakDbarSol {f : ℂ → ℂ} (hf : AEStronglyMeasurable f (volume.restrict 𝔻))
    (hfi : ∫⁻ ζ in 𝔻, ‖f ζ‖ₑ * ENNReal.ofReal (1 - ‖ζ‖ ^ 2) < ∞) :
    IsWeakDbarSol 𝔻 (lemma7Op f) f := by
  rw [lemma7Op_eq]
  have hpi := Real.pi_pos
  refine isWeakDbarSol_kernel isOpen_ball measurable_lemma7H
    (fun ζ hζ ↦ differentiableOn_lemma7H hζ) (fun ζ hζ ↦ lemma7H_self hζ) hf ?_ ?_
  · -- local integrability of `f`
    rw [locallyIntegrableOn_iff isOpen_ball.isLocallyClosed]
    intro K hKD hK
    refine ⟨hf.mono_measure (Measure.restrict_mono hKD le_rfl), ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn (continuousOn_discDensity.mono hKD)
    calc ∫⁻ z in K, ‖f z‖ₑ
        ≤ ∫⁻ z in K, ENNReal.ofReal B * (‖f z‖ₑ * ENNReal.ofReal (1 - ‖z‖ ^ 2)) := by
          refine setLIntegral_mono' hK.measurableSet fun z hzK ↦ ?_
          have hz0 := one_sub_normSq_pos (hKD hzK)
          have hB' : 1 / (1 - ‖z‖ ^ 2) ≤ B := (le_abs_self _).trans (hB z hzK)
          have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB z hzK)
          rw [mul_comm (‖f z‖ₑ), ← mul_assoc, ← ENNReal.ofReal_mul hB0]
          calc ‖f z‖ₑ = 1 * ‖f z‖ₑ := (one_mul _).symm
            _ ≤ ENNReal.ofReal (B * (1 - ‖z‖ ^ 2)) * ‖f z‖ₑ := by
                gcongr
                rw [ENNReal.one_le_ofReal, ← div_le_iff₀ hz0]
                exact hB'
      _ = ENNReal.ofReal B * ∫⁻ z in K, ‖f z‖ₑ * ENNReal.ofReal (1 - ‖z‖ ^ 2) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal B * ∫⁻ z in 𝔻, ‖f z‖ₑ * ENNReal.ofReal (1 - ‖z‖ ^ 2) := by
          gcongr
      _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfi
  · -- the local Fubini condition
    intro K hKD hK
    obtain ⟨r, hr1, hKr⟩ := exists_lt_subset_ball hK.isClosed hKD
    set C0 : ℝ := 1 / (Real.pi * (1 - r)) with hC0
    have hC0p : 0 ≤ C0 := by
      have : 0 < 1 - r := by linarith
      positivity
    set g : ℂ → ℝ≥0∞ := fun ζ ↦ ‖f ζ‖ₑ * ENNReal.ofReal (1 - ‖ζ‖ ^ 2) with hg
    have hgm : AEMeasurable g (volume.restrict 𝔻) := hf.enorm.mul (by fun_prop)
    calc ∫⁻ z in K, ∫⁻ ζ in 𝔻, ‖lemma7H z ζ / ((Real.pi : ℂ) * (z - ζ))‖ₑ * ‖f ζ‖ₑ
        ≤ ∫⁻ z in K, ∫⁻ ζ in 𝔻, ENNReal.ofReal (C0 * ‖z - ζ‖⁻¹) * g ζ := by
          refine setLIntegral_mono' hK.measurableSet fun z hzK ↦ ?_
          refine setLIntegral_mono' measurableSet_ball fun ζ hζ ↦ ?_
          have hz := hKD hzK
          have hzr : ‖z‖ < r := by simpa using hKr hzK
          have hζ0 := one_sub_normSq_pos hζ
          have hY : 1 - r ≤ ‖1 - conj ζ * z‖ := by
            have := one_sub_mul_le_norm_one_sub_conj_mul ζ z
            have hζ1 := norm_lt_one_of_mem_disc hζ
            nlinarith [norm_nonneg ζ, norm_nonneg z]
          have hr0 : 0 < 1 - r := by linarith
          rw [hg, ← mul_assoc, ← ofReal_norm, ← ofReal_norm (f ζ),
            ← ENNReal.ofReal_mul (norm_nonneg _), ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_mul (by positivity)]
          apply ENNReal.ofReal_le_ofReal
          rw [norm_div, norm_lemma7H hζ, norm_mul, Complex.norm_real,
            Real.norm_of_nonneg hpi.le]
          rcases eq_or_ne z ζ with rfl | hne
          · simp
          have hZ : 0 < ‖z - ζ‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
          rw [hC0]
          have hYp : 0 < ‖1 - conj ζ * z‖ := lt_of_lt_of_le hr0 hY
          have hN : 0 ≤ (1 - ‖ζ‖ ^ 2) * ‖f ζ‖ := mul_nonneg hζ0.le (norm_nonneg _)
          calc _ = (1 - ‖ζ‖ ^ 2) * ‖f ζ‖ / (‖1 - conj ζ * z‖ * (Real.pi * ‖z - ζ‖)) := by
                field_simp
            _ ≤ (1 - ‖ζ‖ ^ 2) * ‖f ζ‖ / ((1 - r) * (Real.pi * ‖z - ζ‖)) := by
                gcongr
            _ = _ := by field_simp
      _ = ∫⁻ ζ in 𝔻, ∫⁻ z in K, ENNReal.ofReal (C0 * ‖z - ζ‖⁻¹) * g ζ := by
          refine lintegral_lintegral_swap ?_
          exact ((by fun_prop : Measurable fun q : ℂ × ℂ ↦
            ENNReal.ofReal (C0 * ‖q.1 - q.2‖⁻¹)).aemeasurable).mul hgm.comp_snd
      _ = ∫⁻ ζ in 𝔻, g ζ * (ENNReal.ofReal C0 * ∫⁻ z in K, ENNReal.ofReal ‖z - ζ‖⁻¹) := by
          refine lintegral_congr fun ζ ↦ ?_
          rw [lintegral_mul_const _ (by fun_prop), mul_comm]
          congr 1
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          refine lintegral_congr fun z ↦ ?_
          rw [← ENNReal.ofReal_mul hC0p]
      _ ≤ ∫⁻ ζ in 𝔻, g ζ * (ENNReal.ofReal C0 * (ENNReal.ofReal (2 * Real.pi) + volume K)) := by
          gcongr with ζ
          exact lintegral_inv_norm_sub_le_of_set K ζ
      _ = (∫⁻ ζ in 𝔻, g ζ) * (ENNReal.ofReal C0 * (ENNReal.ofReal (2 * Real.pi) + volume K)) :=
          lintegral_mul_const' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
            (ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, hK.measure_lt_top.ne⟩))
      _ < ∞ := ENNReal.mul_lt_top hfi (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
            (ENNReal.add_lt_top.2 ⟨ENNReal.ofReal_lt_top, hK.measure_lt_top⟩))

theorem exp_mul_log_eq_rpow {P : ℝ} (hP : 0 < P) (α : ℝ) :
    Real.exp (α * Real.log P) = P ^ α := by
  rw [Real.rpow_def_of_pos hP, mul_comm]

theorem lemma7 {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (f : ℂ → ℂ)
    (hf : AEStronglyMeasurable f (volume.restrict 𝔻))
    (hadm : ∃ p : ℝ≥0∞, 1 ≤ p ∧ eLpNorm (fun z ↦ f z * ((1 - ‖z‖ ^ 2) ^ (1 + α) : ℝ)) p
      discMeasure < ∞) :
    IsWeakDbarSol 𝔻 (lemma7Op f) f ∧ ∀ p : ℝ≥0∞, 1 ≤ p →
      eLpNorm (fun z ↦ lemma7Op f z * ((1 - ‖z‖ ^ 2) ^ α : ℝ)) p discMeasure ≤
        ENNReal.ofReal (24 / (α * (1 - α))) *
          eLpNorm (fun z ↦ f z * ((1 - ‖z‖ ^ 2) ^ (1 + α) : ℝ)) p discMeasure := by
  set φ : ℂ → ℝ := fun z ↦ -α * Real.log (1 - ‖z‖ ^ 2) with hφ
  have hφc : ContinuousOn φ 𝔻 :=
    continuousOn_const.mul ((by fun_prop : Continuous fun z : ℂ ↦ 1 - ‖z‖ ^ 2).continuousOn.log
      fun z hz ↦ (one_sub_normSq_pos hz).ne')
  have hexp : ∀ z ∈ 𝔻, Real.exp (-φ z) = (1 - ‖z‖ ^ 2) ^ α := by
    intro z hz
    simp only [hφ, neg_mul, neg_neg]
    exact exp_mul_log_eq_rpow (one_sub_normSq_pos hz) α
  have hW : ∀ z ∈ 𝔻, (1 - ‖z‖ ^ 2) * Real.exp (-φ z) = (1 - ‖z‖ ^ 2) ^ (1 + α) := by
    intro z hz
    rw [hexp z hz, Real.rpow_add (one_sub_normSq_pos hz), Real.rpow_one]
  have hRHS : ∀ p, eLpNorm (fun z ↦ f z * ((1 - ‖z‖ ^ 2) * Real.exp (-φ z) : ℝ)) p discMeasure =
      eLpNorm (fun z ↦ f z * ((1 - ‖z‖ ^ 2) ^ (1 + α) : ℝ)) p discMeasure := by
    intro p
    refine eLpNorm_congr_ae (ae_discMeasure_mem.mono fun z hz ↦ ?_)
    simp only [hW z hz]
  have hHb : ∀ z ∈ 𝔻, ∀ ζ ∈ 𝔻, ‖lemma7H z ζ‖ ≤ 1 * Real.exp (φ z - φ ζ) *
      ((1 - ‖z‖ ^ 2) / (1 - ‖ζ‖ ^ 2)) ^ α * ((1 - ‖ζ‖ ^ 2) / ‖1 - conj ζ * z‖) := by
    intro z hz ζ hζ
    have hz0 := one_sub_normSq_pos hz
    have hζ0 := one_sub_normSq_pos hζ
    rw [norm_lemma7H hζ, Real.exp_sub]
    simp only [hφ]
    rw [exp_mul_log_eq_rpow hz0, exp_mul_log_eq_rpow hζ0, Real.div_rpow hz0.le hζ0.le,
      Real.rpow_neg hz0.le, Real.rpow_neg hζ0.le]
    have := Real.rpow_pos_of_pos hz0 α
    have := Real.rpow_pos_of_pos hζ0 α
    apply le_of_eq
    field_simp
  obtain ⟨hsol, hest⟩ := disc_kernel_operator hφc hα0 hα1 measurable_lemma7H
    (fun ζ hζ ↦ differentiableOn_lemma7H hζ) (fun ζ hζ ↦ lemma7H_self hζ) hHb f hf
    (by obtain ⟨p, hp, h⟩ := hadm; exact ⟨p, hp, by rwa [hRHS]⟩)
  refine ⟨hsol, fun p hp ↦ ?_⟩
  have := hest p hp
  rw [hRHS, mul_one] at this
  calc eLpNorm (fun z ↦ lemma7Op f z * ((1 - ‖z‖ ^ 2) ^ α : ℝ)) p discMeasure
      = eLpNorm (fun z ↦ (∫ ζ in 𝔻, lemma7H z ζ / ((Real.pi : ℂ) * (z - ζ)) * f ζ) *
          (Real.exp (-φ z) : ℝ)) p discMeasure := by
        refine eLpNorm_congr_ae (ae_discMeasure_mem.mono fun z hz ↦ ?_)
        simp only [hexp z hz]
        rfl
    _ ≤ _ := this

/-- `‖G (1-|z|²)^b‖_{L^p(ν)}^p = ∫_𝔻 |G|^p (1-|z|²)^{bp-1} dm`. -/
theorem eLpNorm_rpow_discMeasure {G : ℂ → ℂ} (hG : AEStronglyMeasurable G discMeasure)
    {b p : ℝ} (hp : 0 < p) :
    eLpNorm (fun z ↦ G z * ((1 - ‖z‖ ^ 2) ^ b : ℝ)) (ENNReal.ofReal p) discMeasure ^ p =
      ∫⁻ z in 𝔻, ENNReal.ofReal (‖G z‖ ^ p * (1 - ‖z‖ ^ 2) ^ (b * p - 1)) := by
  have hm : AEStronglyMeasurable (fun z ↦ G z * ((1 - ‖z‖ ^ 2) ^ b : ℝ)) discMeasure :=
    hG.mul (by fun_prop : Measurable fun z : ℂ ↦ (((1 - ‖z‖ ^ 2) ^ b : ℝ) : ℂ)).aestronglyMeasurable
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hp) ENNReal.ofReal_ne_top hm,
    ENNReal.toReal_ofReal hp.le, ← ENNReal.rpow_mul, one_div_mul_cancel hp.ne', ENNReal.rpow_one,
    discMeasure, lintegral_withDensity_eq_lintegral_mul_non_measurable _
      measurable_discDensity (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  refine setLIntegral_congr_fun measurableSet_ball fun z hz ↦ ?_
  have hz0 := one_sub_normSq_pos hz
  simp only [Pi.mul_apply]
  rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp.le,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hz0.le _),
    Real.mul_rpow (norm_nonneg _) (Real.rpow_nonneg hz0.le _), ← Real.rpow_mul hz0.le,
    Real.rpow_sub_one hz0.ne']
  field_simp

theorem lemma7_Lp_printed {α p : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hp : 1 ≤ p) (f : ℂ → ℂ)
    (hf : AEStronglyMeasurable f (volume.restrict 𝔻))
    (hfin : ∫⁻ z in 𝔻, ENNReal.ofReal (‖f z * (1 - ‖z‖ ^ 2)‖ ^ p * (1 - ‖z‖ ^ 2) ^ (α - 1)) < ∞) :
    IsWeakDbarSol 𝔻 (lemma7Op f) f ∧
      ∫⁻ z in 𝔻, ENNReal.ofReal (‖lemma7Op f z‖ ^ p * (1 - ‖z‖ ^ 2) ^ (α - 1)) ≤
        ENNReal.ofReal ((24 * p ^ 2 / (α * (p - α))) ^ p) *
          ∫⁻ z in 𝔻, ENNReal.ofReal (‖f z * (1 - ‖z‖ ^ 2)‖ ^ p * (1 - ‖z‖ ^ 2) ^ (α - 1)) := by
  have hp0 : 0 < p := by linarith
  have ha0 : 0 < α / p := div_pos hα0 hp0
  have ha1 : α / p < 1 := (div_lt_one hp0).2 (by linarith)
  have hνac : discMeasure ≪ volume.restrict 𝔻 := withDensity_absolutelyContinuous _ _
  have hfν : AEStronglyMeasurable f discMeasure := hf.mono_ac hνac
  have huν : AEStronglyMeasurable (lemma7Op f) discMeasure :=
    (weak_aestronglyMeasurable_kernelOp measurable_lemma7H hf).restrict.mono_ac hνac
  have hF : eLpNorm (fun z ↦ f z * ((1 - ‖z‖ ^ 2) ^ (1 + α / p) : ℝ)) (ENNReal.ofReal p)
      discMeasure ^ p =
      ∫⁻ z in 𝔻, ENNReal.ofReal (‖f z * (1 - ‖z‖ ^ 2)‖ ^ p * (1 - ‖z‖ ^ 2) ^ (α - 1)) := by
    rw [eLpNorm_rpow_discMeasure hfν hp0]
    refine setLIntegral_congr_fun measurableSet_ball fun z hz ↦ ?_
    have hz0 := one_sub_normSq_pos hz
    congr 1
    have e : (1 - (‖z‖ : ℂ) ^ 2) = ((1 - ‖z‖ ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [e, norm_mul, Complex.norm_real, Real.norm_of_nonneg hz0.le,
      Real.mul_rpow (norm_nonneg _) hz0.le, mul_assoc, ← Real.rpow_add hz0]
    congr 2
    field_simp
    ring
  have hU : eLpNorm (fun z ↦ lemma7Op f z * ((1 - ‖z‖ ^ 2) ^ (α / p) : ℝ)) (ENNReal.ofReal p)
      discMeasure ^ p =
      ∫⁻ z in 𝔻, ENNReal.ofReal (‖lemma7Op f z‖ ^ p * (1 - ‖z‖ ^ 2) ^ (α - 1)) := by
    rw [eLpNorm_rpow_discMeasure huν hp0]
    refine setLIntegral_congr_fun measurableSet_ball fun z hz ↦ ?_
    congr 3
    field_simp
  have hadm : eLpNorm (fun z ↦ f z * ((1 - ‖z‖ ^ 2) ^ (1 + α / p) : ℝ)) (ENNReal.ofReal p)
      discMeasure < ∞ := by
    rw [← ENNReal.rpow_lt_top_iff_of_pos hp0, hF]
    exact hfin
  obtain ⟨hsol, hest⟩ := lemma7 ha0 ha1 f hf
    ⟨ENNReal.ofReal p, ENNReal.one_le_ofReal.2 hp, hadm⟩
  refine ⟨hsol, ?_⟩
  have h := ENNReal.rpow_le_rpow (hest (ENNReal.ofReal p) (ENNReal.one_le_ofReal.2 hp)) hp0.le
  rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, hU, hF,
    ENNReal.ofReal_rpow_of_nonneg (by
      have : 0 < α / p * (1 - α / p) := mul_pos ha0 (by linarith)
      positivity) hp0.le] at h
  convert h using 4
  have hpa : 0 < p - α := by linarith
  field_simp

theorem lemma7_sup {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (f : ℂ → ℂ)
    (hf : AEStronglyMeasurable f (volume.restrict 𝔻)) {M : ℝ}
    (hM : ∀ᵐ ζ ∂(volume.restrict 𝔻), ‖f ζ‖ * (1 - ‖ζ‖ ^ 2) ^ (1 + α) ≤ M) :
    IsWeakDbarSol 𝔻 (lemma7Op f) f ∧
      ∀ z ∈ 𝔻, ‖lemma7Op f z‖ * (1 - ‖z‖ ^ 2) ^ α ≤ 24 / (α * (1 - α)) * M := by
  have hpi := Real.pi_pos
  have h0 : (0 : ℂ) ∈ 𝔻 := mem_ball_self one_pos
  have hvol : volume.restrict 𝔻 ≠ 0 := by
    rw [Ne, Measure.restrict_eq_zero]
    exact (measure_ball_pos volume (0 : ℂ) one_pos).ne'
  have : (ae (volume.restrict 𝔻)).NeBot := ae_neBot.2 hvol
  have hM0 : 0 ≤ M := by
    obtain ⟨ζ, hζ⟩ := (hM.and (ae_restrict_mem measurableSet_ball)).exists
    exact le_trans (mul_nonneg (norm_nonneg _)
      (Real.rpow_nonneg (one_sub_normSq_pos hζ.2).le _)) hζ.1
  have hM' : ∀ᵐ ζ ∂(volume.restrict 𝔻),
      ‖f ζ‖ * (1 - ‖ζ‖ ^ 2) ≤ M * (1 - ‖ζ‖ ^ 2) ^ (-α) := by
    filter_upwards [hM, ae_restrict_mem measurableSet_ball] with ζ h hζ
    have hζ0 := one_sub_normSq_pos hζ
    rw [Real.rpow_add hζ0, Real.rpow_one] at h
    rw [Real.rpow_neg hζ0.le]
    have := Real.rpow_pos_of_pos hζ0 α
    rw [le_mul_inv_iff₀ this]
    linarith [h]
  have hfi : ∫⁻ ζ in 𝔻, ‖f ζ‖ₑ * ENNReal.ofReal (1 - ‖ζ‖ ^ 2) < ∞ := by
    calc ∫⁻ ζ in 𝔻, ‖f ζ‖ₑ * ENNReal.ofReal (1 - ‖ζ‖ ^ 2)
        ≤ ∫⁻ ζ in 𝔻, ENNReal.ofReal M *
            ENNReal.ofReal ((1 - ‖ζ‖) ^ (-α) / ‖1 - conj 0 * ζ‖ ^ 2) := by
          refine lintegral_mono_ae ?_
          filter_upwards [hM', ae_restrict_mem measurableSet_ball] with ζ h hζ
          have hζ1 := norm_lt_one_of_mem_disc hζ
          rw [← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _), ← ENNReal.ofReal_mul hM0]
          apply ENNReal.ofReal_le_ofReal
          simp only [map_zero, zero_mul, sub_zero, norm_one, one_pow, div_one]
          refine h.trans (mul_le_mul_of_nonneg_left ?_ hM0)
          exact Real.rpow_le_rpow_of_nonpos (by linarith)
            (by nlinarith [norm_nonneg ζ]) (by linarith)
      _ = ENNReal.ofReal M * ∫⁻ ζ in 𝔻,
            ENNReal.ofReal ((1 - ‖ζ‖) ^ (-α) / ‖1 - conj 0 * ζ‖ ^ 2) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal M * ENNReal.ofReal
            (2 * Real.pi / (α * (1 - α)) * (1 - ‖(0 : ℂ)‖) ^ (-α)) := by
          gcongr
          exact lintegral_disc_rpow_div_normSq hα0 hα1 h0
      _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  refine ⟨lemma7_isWeakDbarSol hf hfi, fun z hz ↦ ?_⟩
  have hz0 := one_sub_normSq_pos hz
  have hint : ∫⁻ ζ in 𝔻, ENNReal.ofReal ‖discKernel z ζ * f ζ‖ ≤
      ENNReal.ofReal (M / Real.pi * (24 * Real.pi / (α * (1 - α)) * (1 - ‖z‖ ^ 2) ^ (-α))) := by
    calc ∫⁻ ζ in 𝔻, ENNReal.ofReal ‖discKernel z ζ * f ζ‖
        ≤ ∫⁻ ζ in 𝔻, ENNReal.ofReal (M / Real.pi) *
            ENNReal.ofReal ((1 - ‖ζ‖ ^ 2) ^ (-α) / (‖1 - conj z * ζ‖ * ‖z - ζ‖)) := by
          refine lintegral_mono_ae ?_
          filter_upwards [hM', ae_restrict_mem measurableSet_ball] with ζ h hζ
          rw [← ENNReal.ofReal_mul (div_nonneg hM0 hpi.le)]
          apply ENNReal.ofReal_le_ofReal
          rw [norm_mul, discKernel, norm_div, norm_div, norm_mul, Complex.norm_real,
            Complex.norm_real, Real.norm_of_nonneg (one_sub_normSq_pos hζ).le,
            Real.norm_of_nonneg hpi.le, norm_one_sub_conj_mul_comm ζ z]
          rcases eq_or_ne z ζ with rfl | hne
          · simp
          have hZ : 0 < ‖z - ζ‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
          have hY := norm_one_sub_conj_mul_pos hz hζ
          calc (1 - ‖ζ‖ ^ 2) / ‖1 - conj z * ζ‖ / (Real.pi * ‖z - ζ‖) * ‖f ζ‖
              = (‖f ζ‖ * (1 - ‖ζ‖ ^ 2)) / (Real.pi * (‖1 - conj z * ζ‖ * ‖z - ζ‖)) := by
                field_simp
            _ ≤ (M * (1 - ‖ζ‖ ^ 2) ^ (-α)) / (Real.pi * (‖1 - conj z * ζ‖ * ‖z - ζ‖)) := by
                gcongr
            _ = M / Real.pi * ((1 - ‖ζ‖ ^ 2) ^ (-α) / (‖1 - conj z * ζ‖ * ‖z - ζ‖)) := by
                field_simp
      _ = ENNReal.ofReal (M / Real.pi) * ∫⁻ ζ in 𝔻,
            ENNReal.ofReal ((1 - ‖ζ‖ ^ 2) ^ (-α) / (‖1 - conj z * ζ‖ * ‖z - ζ‖)) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (M / Real.pi) *
            ENNReal.ofReal (24 * Real.pi / (α * (1 - α)) * (1 - ‖z‖ ^ 2) ^ (-α)) := by
          gcongr
          exact lintegral_FR hα0 hα1 hz
      _ = _ := (ENNReal.ofReal_mul (div_nonneg hM0 hpi.le)).symm
  have hP := Real.rpow_pos_of_pos hz0 α
  have h1 : ‖lemma7Op f z‖ ≤
      M / Real.pi * (24 * Real.pi / (α * (1 - α)) * (1 - ‖z‖ ^ 2) ^ (-α)) := by
    unfold lemma7Op
    exact (norm_integral_le_lintegral_norm _).trans
      (ENNReal.toReal_le_of_le_ofReal (by
        have : 0 < α * (1 - α) := mul_pos hα0 (by linarith)
        have := Real.rpow_nonneg hz0.le (-α)
        positivity) hint)
  calc ‖lemma7Op f z‖ * (1 - ‖z‖ ^ 2) ^ α
      ≤ (M / Real.pi * (24 * Real.pi / (α * (1 - α)) * (1 - ‖z‖ ^ 2) ^ (-α))) *
          (1 - ‖z‖ ^ 2) ^ α := mul_le_mul_of_nonneg_right h1 hP.le
    _ = 24 / (α * (1 - α)) * M := by
        rw [Real.rpow_neg hz0.le]
        have : α * (1 - α) ≠ 0 := (mul_pos hα0 (by linarith)).ne'
        field_simp

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
