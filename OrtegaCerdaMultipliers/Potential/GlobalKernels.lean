import OrtegaCerdaMultipliers.Potential.Fundamental

/-!
# M02 (Potentials) Appendix A — The paper's global kernels (documentation; not used)

See `blueprint/M02_Potentials.md`, Appendix A.  Scaffold: statements, proofs `sorry`.  These
kernels are not used by the formal proof of Lemma 6 (which uses local potentials, §4); they
document the paper's construction (p. 371) and its sign error in the plane.
-/

open MeasureTheory Metric Set Complex
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace OC

/-- Plane kernel of Lemma 6, sign of the quadratic term corrected. -/
def kPlane (z ζ : ℂ) : ℝ :=
  (4 * Real.pi)⁻¹ * Real.log (‖z - ζ‖ ^ 2) -
    (2 * Real.pi)⁻¹ * (if 1 ≤ ‖ζ‖ then
      Real.log ‖ζ‖ - (z / ζ).re - (z ^ 2 / (2 * ζ ^ 2)).re else 0)

/-- Disc kernel of Lemma 6. -/
def kDisc (z ζ : ℂ) : ℝ :=
  (4 * Real.pi)⁻¹ * (Real.log (pseudoHyp ζ z ^ 2) +
    (1 - ‖ζ‖ ^ 2) * (1 / (1 - conj z * ζ) + 1 / (1 - z * conj ζ) - 1).re)

theorem kDisc_eq {z ζ : ℂ} (hz : z ∈ 𝔻) (hζ : ζ ∈ 𝔻) :
    kDisc z ζ = (4 * Real.pi)⁻¹ * (Real.log (pseudoHyp ζ z ^ 2) + (1 - pseudoHyp ζ z ^ 2) +
      ‖z‖ ^ 2 * (1 - ‖ζ‖ ^ 2) ^ 2 / ‖1 - conj ζ * z‖ ^ 2) := sorry

/-- **Andersson–Pascuas estimate** with explicit constant `4/π`. -/
theorem abs_kDisc_le {z ζ : ℂ} (hz : z ∈ 𝔻) (hζ : ζ ∈ 𝔻) (hne : z ≠ ζ) :
    |kDisc z ζ| ≤ 4 / Real.pi * ((1 - ‖ζ‖ ^ 2) / ‖1 - conj ζ * z‖) ^ 2 *
      (1 + Real.log (1 / pseudoHyp ζ z)) := sorry

theorem abs_kPlane_le {z ζ : ℂ} (hζ : 1 ≤ ‖ζ‖) (hzζ : 2 * ‖z‖ ≤ ‖ζ‖) :
    |kPlane z ζ| ≤ (3 * Real.pi)⁻¹ * (‖z‖ / ‖ζ‖) ^ 3 := sorry

end OC
