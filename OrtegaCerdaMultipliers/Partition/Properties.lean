import OrtegaCerdaMultipliers.Partition.Lemma4

/-!
# M05 (Partition) — Claim 2 and the properties of the partitions used later

See `blueprint/M05_Partition.md` §2.4.  Scaffold: statements, proofs `sorry`.
-/

open MeasureTheory Metric Set Complex
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace OC

section PartitionProps
variable {μ : Measure ℂ} {N : ℕ} {a A : ℝ} {R : ℕ → Set ℂ}

/-- **Claim 2**, lower bound: a piece is not inside a ball of radius `< ρ(z)` around `z`. -/
theorem claim2_lower_plane (hP : IsMassPartition μ univ dist (massRadius μ) N a A R)
    (hN : 1 ≤ N) (i : ℕ) {z : ℂ} (hz : z ∈ R i) {r : ℝ} (hr : R i ⊆ closedBall z r) :
    massRadius μ z ≤ r := sorry

/-- **Claim 2**, comparability of `ρ` inside a piece (diameters of neighbours, via Claim 1). -/
theorem claim2_plane (hd : IsLocallyDoubling μ) (hfin : ∀ z r, μ (ball z r) < ∞)
    (hm : ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ z, 1 ≤ μ (ball z R₀))
    (hP : IsMassPartition μ univ dist (massRadius μ) N a A R) (K : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ i j, ∀ z ∈ R i, ∀ w ∈ R j,
      dist z w ≤ K * max (massRadius μ z) (massRadius μ w) → massRadius μ w ≤ C * massRadius μ z :=
  sorry

/-- Pieces meeting `B(z, Kρ(z))` are boundedly many. -/
theorem finite_near_plane (hd : IsLocallyDoubling μ) (hfin : ∀ z r, μ (ball z r) < ∞)
    (hm : ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ z, 1 ≤ μ (ball z R₀))
    (hP : IsMassPartition μ univ dist (massRadius μ) N a A R) (hN : 1 ≤ N) (K : ℝ) :
    ∃ M : ℕ, ∀ z : ℂ, {i | ∃ w ∈ R i, dist z w ≤ K * massRadius μ z}.encard ≤ M := sorry

/-- Bounded number of neighbours of a piece. -/
theorem finite_neighbours_plane (hd : IsLocallyDoubling μ) (hfin : ∀ z r, μ (ball z r) < ∞)
    (hm : ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ z, 1 ≤ μ (ball z R₀))
    (hP : IsMassPartition μ univ dist (massRadius μ) N a A R) (hN : 1 ≤ N) (K : ℝ) :
    ∃ M : ℕ, ∀ i, {j | ∃ z ∈ R i, ∃ w ∈ R j, dist z w ≤ K * massRadius μ z}.encard ≤ M := sorry

/-- For a piece missing `B(z, ηρ(z))`, all its points are at comparable distance from `z`. -/
theorem far_comparable_plane (hm : ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ z, 1 ≤ μ (ball z R₀))
    (hP : IsMassPartition μ univ dist (massRadius μ) N a A R) {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ (z : ℂ) (i : ℕ), (∀ w ∈ R i, η * massRadius μ z ≤ dist z w) →
      ∀ w ∈ R i, ∀ w' ∈ R i, dist z w' ≤ C * dist z w := sorry

theorem far_comparable_disc (hm : ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ z ∈ 𝔻, 1 ≤ μ (hypBall z R₀))
    (hP : IsMassPartition μ 𝔻 hypDist (massRadiusDisc μ) N a A R) {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ 𝔻, ∀ i : ℕ, (∀ w ∈ R i, η * massRadiusDisc μ z ≤ hypDist z w) →
      ∀ w ∈ R i, ∀ w' ∈ R i, hypDist z w' ≤ C * hypDist z w := sorry

theorem finite_near_disc (hd : IsLocallyDoublingDisc μ)
    (hfin : ∀ z ∈ 𝔻, ∀ r, μ (hypBall z r) < ∞)
    (hm : ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ z ∈ 𝔻, 1 ≤ μ (hypBall z R₀))
    (hP : IsMassPartition μ 𝔻 hypDist (massRadiusDisc μ) N a A R) (hN : 1 ≤ N) (K : ℝ) :
    ∃ M : ℕ, ∀ z ∈ 𝔻, {i | ∃ w ∈ R i, hypDist z w ≤ K * massRadiusDisc μ z}.encard ≤ M := sorry

theorem claim2_disc (hd : IsLocallyDoublingDisc μ) (hfin : ∀ z ∈ 𝔻, ∀ r, μ (hypBall z r) < ∞)
    (hm : ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ z ∈ 𝔻, 1 ≤ μ (hypBall z R₀))
    (hP : IsMassPartition μ 𝔻 hypDist (massRadiusDisc μ) N a A R) (K : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ i j, ∀ z ∈ R i, ∀ w ∈ R j,
      hypDist z w ≤ K * max (massRadiusDisc μ z) (massRadiusDisc μ w) →
        massRadiusDisc μ w ≤ C * massRadiusDisc μ z := sorry

theorem claim2_lower_disc (hP : IsMassPartition μ 𝔻 hypDist (massRadiusDisc μ) N a A R)
    (hN : 1 ≤ N) (i : ℕ) {z : ℂ} (hz : z ∈ R i) {r : ℝ}
    (hr : R i ⊆ {w | w ∈ 𝔻 ∧ hypDist z w ≤ r}) : massRadiusDisc μ z ≤ r := sorry

theorem finite_neighbours_disc (hd : IsLocallyDoublingDisc μ)
    (hfin : ∀ z ∈ 𝔻, ∀ r, μ (hypBall z r) < ∞)
    (hm : ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ z ∈ 𝔻, 1 ≤ μ (hypBall z R₀))
    (hP : IsMassPartition μ 𝔻 hypDist (massRadiusDisc μ) N a A R) (hN : 1 ≤ N) (K : ℝ) :
    ∃ M : ℕ, ∀ i, {j | ∃ z ∈ R i, ∃ w ∈ R j, hypDist z w ≤ K * massRadiusDisc μ z}.encard ≤ M :=
  sorry

/-! Line versions (`Ω = ℝ ⊆ ℂ`, `ρ(z) = massRadiusLine μ z.re`). -/

theorem claim2_lower_line
    (hP : IsMassPartition μ (range fun t : ℝ ↦ (t : ℂ)) dist (fun z ↦ massRadiusLine μ z.re) N a A R)
    (hN : 1 ≤ N) (i : ℕ) {z : ℂ} (hz : z ∈ R i) {r : ℝ} (hr : R i ⊆ closedBall z r) :
    massRadiusLine μ z.re ≤ r := sorry

theorem finite_near_line (hd : IsLocallyDoublingLine μ)
    (hfin : ∀ x r : ℝ, μ (lineInterval x r) < ∞)
    (hm : ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ x : ℝ, 1 ≤ μ (lineInterval x R₀))
    (hP : IsMassPartition μ (range fun t : ℝ ↦ (t : ℂ)) dist (fun z ↦ massRadiusLine μ z.re) N a A R)
    (hN : 1 ≤ N) (K : ℝ) :
    ∃ M : ℕ, ∀ x : ℝ, {i | ∃ w ∈ R i, dist (x : ℂ) w ≤ K * massRadiusLine μ x}.encard ≤ M := sorry

theorem far_comparable_line (hm : ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ x : ℝ, 1 ≤ μ (lineInterval x R₀))
    (hP : IsMassPartition μ (range fun t : ℝ ↦ (t : ℂ)) dist (fun z ↦ massRadiusLine μ z.re) N a A R)
    {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ (x : ℝ) (i : ℕ), (∀ w ∈ R i, η * massRadiusLine μ x ≤ dist (x : ℂ) w) →
      ∀ w ∈ R i, ∀ w' ∈ R i, dist (x : ℂ) w' ≤ C * dist (x : ℂ) w := sorry

/-- Euclidean size of the disc pieces. -/
theorem euclid_size_disc (hm : ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ z ∈ 𝔻, 1 ≤ μ (hypBall z R₀))
    (hP : IsMassPartition μ 𝔻 hypDist (massRadiusDisc μ) N a A R) :
    ∃ C : ℝ, 0 < C ∧ ∀ i, ∀ z ∈ R i, ∀ w ∈ R i,
      ‖z - w‖ ≤ C * (1 - ‖z‖ ^ 2) * massRadiusDisc μ z := sorry

/-- Sum over pieces versus integral (generic). -/
theorem IsMassPartition.mass_mul_le_setLIntegral {Ω : Set ℂ} {d : ℂ → ℂ → ℝ} {ρ : ℂ → ℝ}
    (hP : IsMassPartition μ Ω d ρ N a A R) (i : ℕ) {c : ℝ≥0∞} {f : ℂ → ℝ≥0∞}
    (hc : ∀ z ∈ R i, c ≤ f z) : (N : ℝ≥0∞) * c ≤ ∫⁻ z in R i, f z ∂μ := sorry

theorem IsMassPartition.lintegral_biUnion {Ω : Set ℂ} {d : ℂ → ℂ → ℝ} {ρ : ℂ → ℝ}
    (hP : IsMassPartition μ Ω d ρ N a A R) (S : Set ℕ) (f : ℂ → ℝ≥0∞) :
    ∫⁻ z in ⋃ i ∈ S, R i, f z ∂μ = ∑' i : S, ∫⁻ z in R i, f z ∂μ := sorry

theorem IsMassPartition.existsUnique_mem {Ω : Set ℂ} {d : ℂ → ℂ → ℝ} {ρ : ℂ → ℝ}
    (hP : IsMassPartition μ Ω d ρ N a A R) {z : ℂ} (hz : z ∈ Ω) : ∃! i, z ∈ R i := sorry

end PartitionProps

end OC
