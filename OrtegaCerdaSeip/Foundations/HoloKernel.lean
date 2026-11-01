import OrtegaCerdaSeip.Foundations.Pompeiu
import OrtegaCerdaSeip.Foundations.Wirtinger

/-!
# Foundations — the weak `∂̄`-equation for holomorphic perturbations of the Cauchy kernel

See `blueprint/M05_Lemma4.md` (§1.1) and `blueprint/M04_Jones.md` (§1.4).

`integral_holo_mul_dbar_div`: if `H` is holomorphic on an open `Ω ∋ ζ` and `α` is a test function
supported in `Ω`, then `∫ H(z) ∂̄α(z) / (π(z - ζ)) dm(z) = -H(ζ) α(ζ)`.  With `H(ζ) = 1` this says
that the kernel `H(z)/(π(z - ζ))` is a fundamental solution of `∂̄` at `ζ`.  It is used for the
kernel `sin ε(z-ζ)/(π ε (z-ζ)²)` of Lemma 4 (M05) and for Jones' kernel (M04).

**Provenance.** Copied from `OrtegaCerdaMultipliers/ModelKernels.lean` (§4, lemmas
`weak_contDiff_holo_mul`, `weak_dbar_holo_mul`, `integral_holo_mul_dbar_div`) of the companion
project `../MR1949832` (github.com/joaquimortega/MR1949832, commit `a9c02a4`, same author,
Apache-2.0).  Changes: namespace `OC` → `OCS`, imports.
-/

open MeasureTheory Metric Set Complex
open scoped ENNReal NNReal ComplexConjugate Topology

noncomputable section

namespace OCS

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

end OCS
