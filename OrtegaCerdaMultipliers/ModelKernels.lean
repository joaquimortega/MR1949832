import OrtegaCerdaMultipliers.Foundations.Basic
import OrtegaCerdaMultipliers.Foundations.Pompeiu
import OrtegaCerdaMultipliers.Foundations.Polar

/-!
# M10 (ModelKernels) — Lemmas 7 and 8, the Schur test, Forelli–Rudin integrals

See `blueprint/M10_ModelKernels.md`.  Scaffold: statements, proofs `sorry`; definitions are real.

Reconciliation: the Forelli–Rudin bound `integral_one_sub_conj_mul_rpow_neg_three_le` that M08
uses for the far field in the disc is stated here (M08 imports M10).
-/

open MeasureTheory Metric Set Complex
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace OC

/-! ## §1 Schur test -/

theorem schur_test {X : Type*} [MeasurableSpace X] {ν : Measure X} [SFinite ν]
    {k : X → X → ℝ≥0∞} (hk : Measurable (Function.uncurry k)) {A B : ℝ≥0∞}
    (hA : ∀ᵐ x ∂ν, ∫⁻ y, k x y ∂ν ≤ A) (hB : ∀ᵐ y ∂ν, ∫⁻ x, k x y ∂ν ≤ B)
    {F : X → ℝ≥0∞} (hF : AEMeasurable F ν) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    eLpNorm (fun x ↦ ∫⁻ y, k x y * F y ∂ν) p ν ≤
      A ^ (1 - p⁻¹.toReal) * B ^ p⁻¹.toReal * eLpNorm F p ν := sorry

theorem schur_test_le_max {X : Type*} [MeasurableSpace X] {ν : Measure X} [SFinite ν]
    {k : X → X → ℝ≥0∞} (hk : Measurable (Function.uncurry k)) {A : ℝ≥0∞}
    (hA : ∀ᵐ x ∂ν, ∫⁻ y, k x y ∂ν ≤ A) (hB : ∀ᵐ y ∂ν, ∫⁻ x, k x y ∂ν ≤ A)
    {F : X → ℝ≥0∞} (hF : AEMeasurable F ν) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    eLpNorm (fun x ↦ ∫⁻ y, k x y * F y ∂ν) p ν ≤ A * eLpNorm F p ν := sorry

/-! ## §2 Forelli–Rudin estimate -/

theorem norm_one_sub_conj_mul_le_five_mul {a w : ℂ} (ha : a ∈ 𝔻) (hw : w ∈ 𝔻)
    (h : (1 - ‖a‖) / 2 ≤ ‖a - w‖) : ‖1 - conj a * w‖ ≤ 5 * ‖a - w‖ := sorry

theorem lintegral_FR_near {s : ℝ} (hs0 : 0 < s) {a : ℂ} (ha : a ∈ 𝔻) :
    ∫⁻ w in ball a ((1 - ‖a‖) / 2),
        ENNReal.ofReal ((1 - ‖w‖ ^ 2) ^ (-s) / (‖1 - conj a * w‖ * ‖a - w‖)) ≤
      ENNReal.ofReal (2 * Real.pi * (1 - ‖a‖) ^ (-s)) := sorry

theorem lintegral_circle_inv_normSq_one_sub {a : ℂ} {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (h : ‖a‖ * ρ < 1) :
    ∫⁻ θ in Ioc 0 (2 * Real.pi),
        ENNReal.ofReal (‖1 - conj a * circleMap 0 ρ θ‖⁻¹ ^ 2) =
      ENNReal.ofReal (2 * Real.pi / (1 - ‖a‖ ^ 2 * ρ ^ 2)) := sorry

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

theorem integral_holo_mul_dbar_div {Ω : Set ℂ} (hΩ : IsOpen Ω) {H : ℂ → ℂ} {ζ : ℂ}
    (hζ : ζ ∈ Ω) (hH : DifferentiableOn ℂ H Ω) {α : ℂ → ℂ} (hα : ContDiff ℝ (⊤ : ℕ∞) α)
    (hαc : HasCompactSupport α) (hαs : tsupport α ⊆ Ω) :
    ∫ z, H z * dbar α z / ((Real.pi : ℂ) * (z - ζ)) = -(H ζ * α ζ) := sorry

theorem isWeakDbarSol_kernel {Ω : Set ℂ} (hΩ : IsOpen Ω) {H : ℂ → ℂ → ℂ} {f : ℂ → ℂ}
    (hHm : Measurable (Function.uncurry H))
    (hHd : ∀ ζ ∈ Ω, DifferentiableOn ℂ (fun z ↦ H z ζ) Ω) (hH1 : ∀ ζ ∈ Ω, H ζ ζ = 1)
    (hf : AEStronglyMeasurable f (volume.restrict Ω)) (hfl : LocallyIntegrableOn f Ω)
    (hloc : ∀ K ⊆ Ω, IsCompact K →
      ∫⁻ z in K, ∫⁻ ζ in Ω, ‖H z ζ / ((Real.pi : ℂ) * (z - ζ))‖ₑ * ‖f ζ‖ₑ < ∞) :
    IsWeakDbarSol Ω (fun z ↦ ∫ ζ in Ω, H z ζ / ((Real.pi : ℂ) * (z - ζ)) * f ζ) f := sorry

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
