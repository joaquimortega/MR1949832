import OrtegaCerdaMultipliers.Multiplier.Defs
import OrtegaCerdaMultipliers.Partition.Lemma4

/-!
# M08 (Multiplier) — Geometry of cells and nodes

See `blueprint/M08_Multiplier.md` §2.3.  Scaffold: statements, proofs `sorry`.
-/

open MeasureTheory Metric Set Complex
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace OC

/-- From M05's partition to cells (`c i` = centre of the inner ball). -/
theorem IsMassPartition.exists_cells {ν : Measure ℂ} {Ω : Set ℂ} {d : ℂ → ℂ → ℝ} {ρ : ℂ → ℝ}
    {N : ℕ} {a A : ℝ} {R : ℕ → Set ℂ} (hP : IsMassPartition ν Ω d ρ N a A R) :
    ∃ c : ℕ → ℂ, IsCells Ω d ρ ν N a A R c := sorry

/-- Bounded number of near cells, near/far dichotomy for nodes (plane). -/
theorem cells_near_plane (Cd : ℝ≥0) (R₀ η A B K₀ : ℝ) (hη : 0 < η) (hK₀ : 2 * (A + B) ≤ K₀) :
    ∃ (Mc : ℕ) (δ C₃ : ℝ), 0 < δ ∧ 0 < C₃ ∧ ∀ (ν : Measure ℂ) (N : ℕ) (R : ℕ → Set ℂ)
      (c : ℕ → ℂ) (m : ℕ → ℕ) (Λ : ℕ → Multiset ℂ), MeasClassPlane ν Cd R₀ → 1 ≤ N →
      IsCells univ dist (massRadius ν) ν N η A R c →
      IsNodes univ dist (massRadius ν) ν N B R c m Λ → ∀ z : ℂ,
        {i | dist z (c i) < K₀ * massRadius ν (c i)}.encard ≤ Mc ∧
        (∀ i, dist z (c i) < K₀ * massRadius ν (c i) →
          ∀ w ∈ R i ∪ {w | w ∈ Λ i}, dist z w ≤ C₃ * massRadius ν z) ∧
        (∀ i, K₀ * massRadius ν (c i) ≤ dist z (c i) →
          δ * massRadius ν z ≤ dist z (c i) ∧ ∀ w ∈ Λ i, δ * massRadius ν z ≤ 2 * dist z w) ∧
        (∃ i, z ∈ R i ∧ dist z (c i) < K₀ * massRadius ν (c i)) := sorry

/-- Local finiteness: a bounded set meets only finitely many enlarged cells. -/
theorem finite_cells_plane {ν : Measure ℂ} {Cd : ℝ≥0} {R₀ : ℝ} {N : ℕ} {η A : ℝ}
    {R : ℕ → Set ℂ} {c : ℕ → ℂ} (hν : MeasClassPlane ν Cd R₀) (hη : 0 < η)
    (hC : IsCells univ dist (massRadius ν) ν N η A R c) (K : Set ℂ)
    (hK : Bornology.IsBounded K) (L : ℝ) :
    {i | ∃ z ∈ K, dist z (c i) < L}.Finite := sorry

/-- Bounded number of near cells, near/far dichotomy for nodes (disc). -/
theorem cells_near_disc (Cd : ℝ≥0) (R₀ η A B K₀ : ℝ) (hη : 0 < η) (hK₀ : 2 * (A + B) ≤ K₀) :
    ∃ (Mc : ℕ) (δ C₃ : ℝ), 0 < δ ∧ 0 < C₃ ∧ ∀ (ν : Measure ℂ) (N : ℕ) (R : ℕ → Set ℂ)
      (c : ℕ → ℂ) (m : ℕ → ℕ) (Λ : ℕ → Multiset ℂ), MeasClassDisc ν Cd R₀ → 1 ≤ N →
      IsCells 𝔻 hypDist (massRadiusDisc ν) ν N η A R c →
      IsNodes 𝔻 hypDist (massRadiusDisc ν) ν N B R c m Λ → ∀ z ∈ 𝔻,
        {i | hypDist z (c i) < K₀ * massRadiusDisc ν (c i)}.encard ≤ Mc ∧
        (∀ i, hypDist z (c i) < K₀ * massRadiusDisc ν (c i) →
          ∀ w ∈ R i ∪ {w | w ∈ Λ i}, hypDist z w ≤ C₃ * massRadiusDisc ν z) ∧
        (∀ i, K₀ * massRadiusDisc ν (c i) ≤ hypDist z (c i) →
          δ * massRadiusDisc ν z ≤ hypDist z (c i) ∧
            ∀ w ∈ Λ i, δ * massRadiusDisc ν z ≤ 2 * hypDist z w) ∧
        (∃ i, z ∈ R i ∧ hypDist z (c i) < K₀ * massRadiusDisc ν (c i)) := sorry

/-- Local finiteness (disc): a compact subset of `𝔻` meets only finitely many enlarged cells. -/
theorem finite_cells_disc {ν : Measure ℂ} {Cd : ℝ≥0} {R₀ : ℝ} {N : ℕ} {η A : ℝ}
    {R : ℕ → Set ℂ} {c : ℕ → ℂ} (hν : MeasClassDisc ν Cd R₀) (hη : 0 < η)
    (hC : IsCells 𝔻 hypDist (massRadiusDisc ν) ν N η A R c) (K : Set ℂ) (hK𝔻 : K ⊆ 𝔻)
    (hK : IsCompact K) (L : ℝ) :
    {i | ∃ z ∈ K, hypDist z (c i) < L}.Finite := sorry

end OC
