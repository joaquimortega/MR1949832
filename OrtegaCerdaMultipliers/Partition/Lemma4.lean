import OrtegaCerdaMultipliers.Partition.Cayley
import OrtegaCerdaMultipliers.Doubling.Quant
import OrtegaCerdaMultipliers.Partition.LineCuts

/-!
# M05 (Partition) — Lemma 4: partitions into pieces of mass `N`

See `blueprint/M05_Partition.md` §2.3.  Scaffold: statements, proofs `sorry`; definitions are real.

`IsMassPartition`, `lemma4_plane`, `lemma4_disc` (horocyclic boxes), `lemma4_line`, and the
quantitative forms `lemma4_plane_quant`, `lemma4_disc_quant` requested by M08 §4.1 (constants
depending only on `(C_d, R₀)`, chosen before the measure).
-/

open MeasureTheory Metric Set Complex
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace OC

/-- `R : ℕ → Set ℂ` partitions `Ω` into measurable pieces of `μ`-mass `N`; each piece has
`d`-diameter `≤ A ρ(z)` (any `z` in it) and contains the `d`-ball of radius `a ρ(c)` around one
of its points `c`. -/
structure IsMassPartition (μ : Measure ℂ) (Ω : Set ℂ) (d : ℂ → ℂ → ℝ) (ρ : ℂ → ℝ) (N : ℕ)
    (a A : ℝ) (R : ℕ → Set ℂ) : Prop where
  measurableSet : ∀ i, MeasurableSet (R i)
  pairwise_disjoint : Pairwise (Function.onFun Disjoint R)
  iUnion_eq : ⋃ i, R i = Ω
  measure_eq : ∀ i, μ (R i) = N
  dist_le : ∀ i, ∀ z ∈ R i, ∀ w ∈ R i, d z w ≤ A * ρ z
  inner : ∀ i, ∃ c ∈ R i, {w | w ∈ Ω ∧ d c w < a * ρ c} ⊆ R i

/-- **Lemma 4 (plane).** -/
theorem lemma4_plane {μ : Measure ℂ} (hd : IsLocallyDoubling μ)
    (hfin : ∀ z r, μ (ball z r) < ∞) (hm : ∃ R : ℝ, 0 < R ∧ ∀ z, 1 ≤ μ (ball z R))
    (N : ℕ) (hN : 1 ≤ N) :
    ∃ (a A L : ℝ) (R : ℕ → Set ℂ), 0 < a ∧ 0 < A ∧ 1 ≤ L ∧
      IsMassPartition μ univ dist (massRadius μ) N a A R ∧
      ∀ i, ∃ x₁ x₂ y₁ y₂ : ℝ, IsRectLE L x₁ x₂ y₁ y₂ ∧ R i = rect x₁ x₂ y₁ y₂ := sorry

/-- **Lemma 4 (disc)**: horocyclic boxes (preimages of rectangles under Cayley). -/
theorem lemma4_disc {μ : Measure ℂ} (hd : IsLocallyDoublingDisc μ)
    (hfin : ∀ z ∈ 𝔻, ∀ r, μ (hypBall z r) < ∞)
    (hm : ∃ R : ℝ, 0 < R ∧ ∀ z ∈ 𝔻, 1 ≤ μ (hypBall z R)) (N : ℕ) (hN : 1 ≤ N) :
    ∃ (a A L Λ : ℝ) (R : ℕ → Set ℂ), 0 < a ∧ 0 < A ∧ 1 ≤ L ∧ 0 < Λ ∧
      IsMassPartition μ 𝔻 hypDist (massRadiusDisc μ) N a A R ∧
      ∀ i, ∃ x₁ x₂ y₁ y₂ : ℝ, IsRectLE L x₁ x₂ y₁ y₂ ∧ 0 < y₁ ∧ y₂ - y₁ ≤ Λ * y₁ ∧
        R i = discBox x₁ x₂ y₁ y₂ := sorry

/-- **Lemma 4 (line)**: intervals of mass `N`. -/
theorem lemma4_line {μ : Measure ℂ} (hd : IsLocallyDoublingLine μ)
    (hfin : ∀ x r : ℝ, μ (lineInterval x r) < ∞)
    (hm : ∃ R : ℝ, 0 < R ∧ ∀ x : ℝ, 1 ≤ μ (lineInterval x R)) (N : ℕ) (hN : 1 ≤ N) :
    ∃ (a A : ℝ) (R : ℕ → Set ℂ), 0 < a ∧ 0 < A ∧
      IsMassPartition μ (range fun t : ℝ ↦ (t : ℂ)) dist (fun z ↦ massRadiusLine μ z.re) N a A R ∧
      ∀ i, ∃ s t : ℝ, s < t ∧ R i = (fun u : ℝ ↦ (u : ℂ)) '' Ico s t := by
  obtain ⟨Cd, R₀, hC⟩ := lineCut_measClassLine_of hd hfin hm
  obtain ⟨a, A, ha, hA, h⟩ := lineCut_partition_quant Cd R₀ N hN
  obtain ⟨R, h1, h2, h3, h4, h5, h6, h7⟩ := h μ hC
  exact ⟨a, A, R, ha, hA, ⟨h1, h2, h3, h4, h5, h6⟩, h7⟩

/-! ### Claim 2 and the consequences used by M08/M09 (plane; disc and line analogous) -/

/-! ### Quantitative forms (requested by M08 §4.1) -/

/-- (M05, quantitative Lemma 4). -/
theorem lemma4_plane_quant (Cd : ℝ≥0) (R₀ : ℝ) (N : ℕ) (hN : 1 ≤ N) : ∃ a A : ℝ, 0 < a ∧ 0 < A ∧
    ∀ ν : Measure ℂ, MeasClassPlane ν Cd R₀ →
      ∃ R : ℕ → Set ℂ, IsMassPartition ν univ dist (massRadius ν) N a A R := sorry
theorem lemma4_disc_quant (Cd : ℝ≥0) (R₀ : ℝ) (N : ℕ) (hN : 1 ≤ N) : ∃ a A : ℝ, 0 < a ∧ 0 < A ∧
    ∀ ν : Measure ℂ, MeasClassDisc ν Cd R₀ →
      ∃ R : ℕ → Set ℂ, IsMassPartition ν 𝔻 hypDist (massRadiusDisc ν) N a A R := sorry
theorem lemma4_line_quant (Cd : ℝ≥0) (R₀ : ℝ) (N : ℕ) (hN : 1 ≤ N) : ∃ a A : ℝ, 0 < a ∧ 0 < A ∧
    ∀ ν : Measure ℂ, MeasClassLine ν Cd R₀ →
      ∃ R : ℕ → Set ℂ, IsMassPartition ν (range fun t : ℝ ↦ (t : ℂ)) dist
        (fun z ↦ massRadiusLine ν z.re) N a A R := by
  obtain ⟨a, A, ha, hA, h⟩ := lineCut_partition_quant Cd R₀ N hN
  refine ⟨a, A, ha, hA, fun ν hν ↦ ?_⟩
  obtain ⟨R, h1, h2, h3, h4, h5, h6, -⟩ := h ν hν
  exact ⟨R, ⟨h1, h2, h3, h4, h5, h6⟩⟩

end OC
