import OrtegaCerdaMultipliers.Multiplier.Kernel
import OrtegaCerdaMultipliers.Multiplier.Cells
import OrtegaCerdaMultipliers.Multiplier.NearField

/-!
# M08 (Multiplier) — The corrected estimates (2), (3) for `S`

See `blueprint/M08_Multiplier.md` §2.6.  Scaffold: statements, proofs `sorry`.
-/

open MeasureTheory Metric Set Complex
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace OC

/-- Estimate (2), corrected: `M log(d/ρ) − C ≤ S(z) ≤ log(d/ρ) + C` off the nodes, and
`d(z, Λ) ≤ C ρ(z)` everywhere.  Here `ρ = massRadius (lapNorm μ)`. -/
theorem multPot_bounds_plane (Cd : ℝ≥0) (R₀ η A B : ℝ) (N : ℕ) (hη : 0 < η) (hA : 0 < A)
    (hB : 0 ≤ B) (hN : 1 ≤ N) :
    ∃ (M : ℕ) (C : ℝ), 1 ≤ M ∧ 0 < C ∧ ∀ (μ : Measure ℂ) (R : ℕ → Set ℂ) (c : ℕ → ℂ)
      (m : ℕ → ℕ) (Λ : ℕ → Multiset ℂ), MeasClassPlane μ Cd R₀ →
      IsCells univ dist (massRadius (lapNorm μ)) (lapNorm μ) N η A R c →
      IsNodes univ dist (massRadius (lapNorm μ)) (lapNorm μ) N B R c m Λ → (∀ i, 3 ≤ m i) →
      (∀ z, ∃ w ∈ nodeSet Λ, dist z w ≤ C * massRadius (lapNorm μ) z) ∧
      ∀ z, z ∉ nodeSet Λ → ∀ d : ℝ, (∀ w ∈ nodeSet Λ, d ≤ dist z w) →
        (∃ w ∈ nodeSet Λ, dist z w ≤ d) →
        M * Real.log (d / massRadius (lapNorm μ) z) - C ≤ multPot kerPlane (lapNorm μ) R Λ z ∧
        multPot kerPlane (lapNorm μ) R Λ z ≤ Real.log (d / massRadius (lapNorm μ) z) + C := sorry

/-- Estimate (3), corrected (disc, hyperbolic distance). -/
theorem multPot_bounds_disc (Cd : ℝ≥0) (R₀ η A B ρ₀ : ℝ) (N : ℕ) (hη : 0 < η) (hA : 0 < A)
    (hB : 0 ≤ B) (hρ₀ : 0 < ρ₀) (hN : 1 ≤ N) :
    ∃ (M : ℕ) (C : ℝ), 1 ≤ M ∧ 0 < C ∧ ∀ (μ : Measure ℂ) (R : ℕ → Set ℂ) (c : ℕ → ℂ)
      (m : ℕ → ℕ) (Λ : ℕ → Multiset ℂ), MeasClassDisc μ Cd R₀ →
      IsCells 𝔻 hypDist (massRadiusDisc (lapNorm μ)) (lapNorm μ) N η A R c →
      IsNodes 𝔻 hypDist (massRadiusDisc (lapNorm μ)) (lapNorm μ) N B R c m Λ →
      (∀ i, 2 ≤ m i) → (∀ i, massRadiusDisc (lapNorm μ) (c i) ≤ ρ₀ → 3 ≤ m i) →
      (∀ z ∈ 𝔻, ∃ w ∈ nodeSet Λ, hypDist z w ≤ C * massRadiusDisc (lapNorm μ) z) ∧
      ∀ z ∈ 𝔻, z ∉ nodeSet Λ → ∀ d : ℝ, (∀ w ∈ nodeSet Λ, d ≤ hypDist z w) →
        (∃ w ∈ nodeSet Λ, hypDist z w ≤ d) →
        M * Real.log (d / massRadiusDisc (lapNorm μ) z) - C ≤
            multPot kerDisc (lapNorm μ) R Λ z ∧
        multPot kerDisc (lapNorm μ) R Λ z ≤ Real.log (d / massRadiusDisc (lapNorm μ) z) + C :=
  sorry

end OC
