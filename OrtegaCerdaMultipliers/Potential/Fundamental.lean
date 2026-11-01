import OrtegaCerdaMultipliers.Foundations.Wirtinger
import OrtegaCerdaMultipliers.Foundations.Polar
import OrtegaCerdaMultipliers.Foundations.Hyperbolic

/-!
# M02 (Potentials) §1 — The logarithmic kernel

See `blueprint/M02_Potentials.md` §1.  Scaffold: statements, proofs `sorry`.

* `∫ log|z − ζ| Δχ(z) dm(z) = 2π χ(ζ)` (fundamental solution of the standard Laplacian);
* integration by parts against test functions for `C²` functions;
* the Green kernel `log ρ(ζ, z)` of `𝔻`;
* (requested by M13 §4.2) the uniform `L¹` bound for `log|z − a|` and the weak Laplacian of the
  logarithmic potential of a compactly supported finite measure.
-/

open MeasureTheory Metric Set Complex
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace OC

theorem locallyIntegrable_log_norm_sub (ζ : ℂ) :
    LocallyIntegrable (fun z : ℂ ↦ Real.log ‖z - ζ‖) := sorry

/-- **Fundamental solution.** `∫ log|z − ζ| Δχ(z) dm(z) = 2π χ(ζ)`. -/
theorem integral_log_norm_sub_mul_laplacian {χ : ℂ → ℝ} (hχ : ContDiff ℝ 2 χ)
    (hc : HasCompactSupport χ) (ζ : ℂ) :
    ∫ z, Real.log ‖z - ζ‖ * Laplacian.laplacian χ z = 2 * Real.pi * χ ζ := sorry

/-- Integration by parts against a test function, for `U ∈ C²(Ω)`. -/
theorem integral_mul_laplacian_of_contDiffOn {Ω : Set ℂ} (hΩ : IsOpen Ω) {U χ : ℂ → ℝ}
    (hU : ContDiffOn ℝ 2 U Ω) (hχ : ContDiff ℝ 2 χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ Ω) :
    ∫ z, U z * Laplacian.laplacian χ z = ∫ z, Laplacian.laplacian U z * χ z := sorry

/-- **Green kernel of the disc.** `∫ log ρ(ζ, z) Δχ(z) dm(z) = 2π χ(ζ)` for `χ` supported in `𝔻`. -/
theorem integral_log_pseudoHyp_mul_laplacian {χ : ℂ → ℝ} (hχ : ContDiff ℝ 2 χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ 𝔻) {ζ : ℂ} (hζ : ζ ∈ 𝔻) :
    ∫ z, Real.log (pseudoHyp ζ z) * Laplacian.laplacian χ z = 2 * Real.pi * χ ζ := sorry

/-! ### Requested by M13 (§4.2) -/

/-- Uniform local integrability of `log|z − a|` for `a` in a compact set. -/
theorem integrableOn_log_norm_sub_uniform {K K' : Set ℂ} (hK : IsCompact K)
    (hK' : IsCompact K') :
    ∃ M : ℝ, ∀ a ∈ K', IntegrableOn (fun z ↦ Real.log ‖z - a‖) K ∧
      ∫ z in K, |Real.log ‖z - a‖| ≤ M := sorry

/-- `Δ (∫ log|z − ζ| dν(ζ)) = 2π ν` weakly, for a finite measure with compact support. -/
theorem integral_logPotential_mul_laplacian (ν : Measure ℂ) [IsFiniteMeasure ν] {L : Set ℂ}
    (hL : IsCompact L) (hνL : ν Lᶜ = 0) (χ : ℂ → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hc : HasCompactSupport χ) :
    ∫ z, (∫ ζ, Real.log ‖z - ζ‖ ∂ν) * Laplacian.laplacian χ z = 2 * Real.pi * ∫ ζ, χ ζ ∂ν :=
  sorry

end OC
