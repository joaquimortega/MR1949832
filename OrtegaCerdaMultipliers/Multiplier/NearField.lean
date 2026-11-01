import OrtegaCerdaMultipliers.Multiplier.Basic
import OrtegaCerdaMultipliers.Multiplier.Defs
import OrtegaCerdaMultipliers.ModelKernels

/-!
# M08 (Multiplier) — The area-counting near-field lemma and the far-field sums

See `blueprint/M08_Multiplier.md` §2.4.  Scaffold: statements, proofs `sorry`.
-/

open MeasureTheory Metric Set Complex
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace OC

/-- **Area-counting near-field lemma (plane)** — replaces the paper's Lemma 3. -/
theorem nearField_sum_le_plane (Cd : ℝ≥0) (R₀ η A δ : ℝ) (hη : 0 < η) (hδ : 0 < δ) :
    ∃ C : ℝ, ∀ (ν : Measure ℂ) (N : ℕ) (R : ℕ → Set ℂ) (c : ℕ → ℂ),
      MeasClassPlane ν Cd R₀ → IsCells univ dist (massRadius ν) ν N η A R c → ∀ z : ℂ,
      ∀ F : Finset ℕ, (∀ i ∈ F, δ * massRadius ν z ≤ dist z (c i) ∧ dist z (c i) ≤ 1 / 4 ∧
          A * massRadius ν (c i) ≤ dist z (c i)) →
        ∑ i ∈ F, (massRadius ν (c i) / dist z (c i)) ^ 3 ≤ C := sorry

/-- **Area-counting near-field lemma (disc)**. -/
theorem nearField_sum_le_disc (Cd : ℝ≥0) (R₀ η A δ : ℝ) (hη : 0 < η) (hδ : 0 < δ) :
    ∃ C : ℝ, ∀ (ν : Measure ℂ) (N : ℕ) (R : ℕ → Set ℂ) (c : ℕ → ℂ),
      MeasClassDisc ν Cd R₀ → IsCells 𝔻 hypDist (massRadiusDisc ν) ν N η A R c → ∀ z ∈ 𝔻,
      ∀ F : Finset ℕ, (∀ i ∈ F, δ * massRadiusDisc ν z ≤ hypDist z (c i) ∧
          hypDist z (c i) ≤ 1 / 4 ∧ A * massRadiusDisc ν (c i) ≤ hypDist z (c i)) →
        ∑ i ∈ F, (massRadiusDisc ν (c i) / hypDist z (c i)) ^ 3 ≤ C := sorry

/-- Far field (plane). -/
theorem farField_sum_le_plane (Cd : ℝ≥0) (R₀ η A M₀ : ℝ) (hη : 0 < η) (hM₀ : 0 < M₀) :
    ∃ C : ℝ, ∀ (ν : Measure ℂ) (N : ℕ) (R : ℕ → Set ℂ) (c : ℕ → ℂ),
      MeasClassPlane ν Cd R₀ → IsCells univ dist (massRadius ν) ν N η A R c → ∀ z : ℂ,
      ∀ F : Finset ℕ, (∀ i ∈ F, M₀ ≤ dist z (c i) ∧ 2 * A * massRadius ν (c i) ≤ dist z (c i)) →
        ∑ i ∈ F, (massRadius ν (c i) / dist z (c i)) ^ 3 ≤ C := sorry

/-- Far field (disc): the Forelli–Rudin sum. -/
theorem farField_sum_le_disc (Cd : ℝ≥0) (R₀ η A M₀ : ℝ) (hη : 0 < η) (hM₀ : 0 < M₀) :
    ∃ C : ℝ, ∀ (ν : Measure ℂ) (N : ℕ) (R : ℕ → Set ℂ) (c : ℕ → ℂ),
      MeasClassDisc ν Cd R₀ → IsCells 𝔻 hypDist (massRadiusDisc ν) ν N η A R c → ∀ z ∈ 𝔻,
      ∀ F : Finset ℕ, (∀ i ∈ F, M₀ ≤ hypDist z (c i)) →
        ∑ i ∈ F, (1 - ‖z‖ ^ 2) * ((1 - ‖c i‖ ^ 2) * massRadiusDisc ν (c i)) ^ 2 /
          ‖1 - conj z * c i‖ ^ 3 ≤ C := sorry

end OC
