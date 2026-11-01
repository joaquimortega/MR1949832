import OrtegaCerdaMultipliers.Multiplier.Cells
import OrtegaCerdaMultipliers.Potential.Fundamental
import OrtegaCerdaMultipliers.LogModulusWeak

/-!
# M08 (Multiplier) — Convergence, continuity and Laplacian of the potential `S`

See `blueprint/M08_Multiplier.md` §2.5.  Scaffold: statements, proofs `sorry`.

These are the fields of M07's `IsWeakLogModulus` for `v = ψ + S`.
-/

open MeasureTheory Metric Set Complex
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace OC

/-- `S` is a weak log-modulus datum (M07 `IsWeakLogModulus` fields), plane. -/
theorem multPot_props_plane {ψ : ℂ → ℝ} {μ : Measure ℂ} {Cd : ℝ≥0} {R₀ : ℝ} {N : ℕ}
    {η A B : ℝ} {R : ℕ → Set ℂ} {c : ℕ → ℂ} {m : ℕ → ℕ} {Λ : ℕ → Multiset ℂ}
    (hw : WeightClassPlane ψ μ Cd R₀) (hη : 0 < η)
    (hC : IsCells univ dist (massRadius (lapNorm μ)) (lapNorm μ) N η A R c)
    (hN : IsNodes univ dist (massRadius (lapNorm μ)) (lapNorm μ) N B R c m Λ)
    (hm : ∀ i, 3 ≤ m i) :
    (∀ K : Set ℂ, IsCompact K → (K ∩ Function.support (nodeCount Λ)).Finite) ∧
    (∀ z, Summable fun i ↦ cellPot kerPlane (lapNorm μ) R Λ i z) ∧
    LocallyIntegrable (fun z ↦ ψ z + multPot kerPlane (lapNorm μ) R Λ z) ∧
    ContinuousOn (fun z ↦ ψ z + multPot kerPlane (lapNorm μ) R Λ z)
      (univ \ Function.support (nodeCount Λ)) ∧
    ∀ χ : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ →
      ∫ z, (ψ z + multPot kerPlane (lapNorm μ) R Λ z) * Laplacian.laplacian χ z =
        2 * Real.pi * ∑ᶠ ζ, (nodeCount Λ ζ : ℝ) * χ ζ := sorry

/-- Same, disc. -/
theorem multPot_props_disc {ψ : ℂ → ℝ} {μ : Measure ℂ} {Cd : ℝ≥0} {R₀ : ℝ} {N : ℕ}
    {η A B ρ₀ : ℝ} {R : ℕ → Set ℂ} {c : ℕ → ℂ} {m : ℕ → ℕ} {Λ : ℕ → Multiset ℂ}
    (hw : WeightClassDisc ψ μ Cd R₀) (hη : 0 < η) (hρ₀ : 0 < ρ₀)
    (hC : IsCells 𝔻 hypDist (massRadiusDisc (lapNorm μ)) (lapNorm μ) N η A R c)
    (hN : IsNodes 𝔻 hypDist (massRadiusDisc (lapNorm μ)) (lapNorm μ) N B R c m Λ)
    (hm2 : ∀ i, 2 ≤ m i) (hm3 : ∀ i, massRadiusDisc (lapNorm μ) (c i) ≤ ρ₀ → 3 ≤ m i) :
    (∀ K ⊆ 𝔻, IsCompact K → (K ∩ Function.support (nodeCount Λ)).Finite) ∧
    (∀ z ∈ 𝔻, Summable fun i ↦ cellPot kerDisc (lapNorm μ) R Λ i z) ∧
    LocallyIntegrableOn (fun z ↦ ψ z + multPot kerDisc (lapNorm μ) R Λ z) 𝔻 ∧
    ContinuousOn (fun z ↦ ψ z + multPot kerDisc (lapNorm μ) R Λ z)
      (𝔻 \ Function.support (nodeCount Λ)) ∧
    ∀ χ : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ → tsupport χ ⊆ 𝔻 →
      ∫ z, (ψ z + multPot kerDisc (lapNorm μ) R Λ z) * Laplacian.laplacian χ z =
        2 * Real.pi * ∑ᶠ ζ, (nodeCount Λ ζ : ℝ) * χ ζ := sorry

end OC
