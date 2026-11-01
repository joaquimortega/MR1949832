import OrtegaCerdaMultipliers.Doubling.Quant
import OrtegaCerdaMultipliers.Foundations.HyperbolicExtra

/-!
# M08 (Multiplier) — Definitions

See `blueprint/M08_Multiplier.md` §2.1.  All definitions are real.

`WeightClassPlane/Disc`, cells and nodes (`IsCells`, `IsNodes`, `nodeCount`, `nodeSet`), the
kernels, `cellPot`, `multPot`, Taylor polynomials, and the conclusions `Thm4BoundsPlane/Disc`.
Reconciliation: `lapNorm`, `IsLocallyDoublingWith`, `IsLocallyDoublingDiscWith`,
`MeasClassPlane`, `MeasClassDisc` are defined in M03 (`Doubling/Quant.lean`), since the
quantitative M03/M05 lemmas are stated with them; `hypArea` is in M01
(`Foundations/HyperbolicExtra.lean`); `IsMassPartition` is M05's.
-/

open MeasureTheory Metric Set Complex
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace OC

/-- The class of weights with parameters `(Cd, R₀)` (plane). -/
structure WeightClassPlane (ψ : ℂ → ℝ) (μ : Measure ℂ) (Cd : ℝ≥0) (R₀ : ℝ) : Prop where
  weight : IsSubharmonicWeight univ ψ μ
  meas : MeasClassPlane μ Cd R₀

/-- The class of weights with parameters `(Cd, R₀)` (disc). -/
structure WeightClassDisc (ψ : ℂ → ℝ) (μ : Measure ℂ) (Cd : ℝ≥0) (R₀ : ℝ) : Prop where
  weight : IsSubharmonicWeight 𝔻 ψ μ
  meas : MeasClassDisc μ Cd R₀

/-- Cells with centres `c i ∈ R i`; the cell radius is `ρ(c i)`. -/
structure IsCells (Ω : Set ℂ) (d : ℂ → ℂ → ℝ) (ρ : ℂ → ℝ) (ν : Measure ℂ) (N : ℕ) (η A : ℝ)
    (R : ℕ → Set ℂ) (c : ℕ → ℂ) : Prop where
  measurableSet : ∀ i, MeasurableSet (R i)
  pairwise_disjoint : Pairwise (Function.onFun Disjoint R)
  iUnion_eq : ⋃ i, R i = Ω
  center_mem : ∀ i, c i ∈ R i
  subset : ∀ i, ∀ w ∈ R i, d (c i) w ≤ A * ρ (c i)
  inner : ∀ i, {w | w ∈ Ω ∧ d (c i) w < η * ρ (c i)} ⊆ R i
  measure_eq : ∀ i, ν (R i) = N

/-- Node multisets: `N` nodes per cell, within `B ρ(c i)` of the centre, matching the complex
moments `0, …, m i − 1` of `ν|R i`. -/
structure IsNodes (Ω : Set ℂ) (d : ℂ → ℂ → ℝ) (ρ : ℂ → ℝ) (ν : Measure ℂ) (N : ℕ) (B : ℝ)
    (R : ℕ → Set ℂ) (c : ℕ → ℂ) (m : ℕ → ℕ) (Λ : ℕ → Multiset ℂ) : Prop where
  card : ∀ i, Multiset.card (Λ i) = N
  mem : ∀ i, ∀ w ∈ Λ i, w ∈ Ω
  near : ∀ i, ∀ w ∈ Λ i, d (c i) w ≤ B * ρ (c i)
  moments : ∀ i, ∀ j < m i, ∫ ζ in R i, ζ ^ j ∂ν = ((Λ i).map (· ^ j)).sum

/-- Multiplicity of `w` as a node. -/
def nodeCount (Λ : ℕ → Multiset ℂ) (w : ℂ) : ℕ := ∑ᶠ i, (Λ i).count w

/-- The set of all nodes. -/
def nodeSet (Λ : ℕ → Multiset ℂ) : Set ℂ := {w | ∃ i, w ∈ Λ i}

/-- Kernels: `log|z − ζ|` and the Green kernel `log |(z − ζ)/(1 − ζ̄ z)|`. -/
def kerPlane (z ζ : ℂ) : ℝ := Real.log ‖z - ζ‖
def kerDisc (z ζ : ℂ) : ℝ := Real.log (pseudoHyp ζ z)

/-- Potential of `Σ_{λ∈Λ i} δ_λ − ν|R i` at `z`. -/
def cellPot (k : ℂ → ℂ → ℝ) (ν : Measure ℂ) (R : ℕ → Set ℂ) (Λ : ℕ → Multiset ℂ) (i : ℕ)
    (z : ℂ) : ℝ :=
  ((Λ i).map (k z)).sum - ∫ ζ in R i, k z ζ ∂ν

/-- `S(z) = Σ_i cellPot i z`. -/
def multPot (k : ℂ → ℂ → ℝ) (ν : Measure ℂ) (R : ℕ → Set ℂ) (Λ : ℕ → Multiset ℂ) (z : ℂ) : ℝ :=
  ∑' i, cellPot k ν R Λ i z

/-- Taylor polynomial of degree `< m` of `ζ ↦ log|z − ζ|` at `c`. -/
def taylorPlane (m : ℕ) (z c ζ : ℂ) : ℝ :=
  Real.log ‖z - c‖ - (∑ k ∈ Finset.Ico 1 m, ((ζ - c) / (z - c)) ^ k / (k : ℂ)).re

/-- Taylor polynomial of degree `< m` of `ζ ↦ log|(z − ζ)/(1 − z̄ζ)|` at `c`. -/
def taylorDisc (m : ℕ) (z c ζ : ℂ) : ℝ :=
  Real.log (pseudoHyp c z) - (∑ k ∈ Finset.Ico 1 m,
    (((ζ - c) / (z - c)) ^ k - (conj z * (ζ - c) / (1 - conj z * c)) ^ k) / (k : ℂ)).re

/-- The conclusion of Theorem 4 (plane), plus the Remark `d(z,Λ) ≲ ρ(z)`. -/
def Thm4BoundsPlane (ψ : ℂ → ℝ) (μ : Measure ℂ) (h : ℂ → ℂ) (M : ℕ) (C : ℝ≥0) : Prop :=
  ∀ z : ℂ,
    C⁻¹ * (edistSet z {w | h w = 0} / ENNReal.ofReal (massRadius μ z)) ^ M ≤
        ENNReal.ofReal (‖h z‖ * Real.exp (-ψ z)) ∧
      ENNReal.ofReal (‖h z‖ * Real.exp (-ψ z)) ≤
        C * (edistSet z {w | h w = 0} / ENNReal.ofReal (massRadius μ z)) ∧
      edistSet z {w | h w = 0} ≤ C * ENNReal.ofReal (massRadius μ z)

/-- The conclusion of Theorem 4 (disc), plus the Remark `d(z,Λ) ≲ ρ(z)`. -/
def Thm4BoundsDisc (ψ : ℂ → ℝ) (μ : Measure ℂ) (h : ℂ → ℂ) (M : ℕ) (C : ℝ≥0) : Prop :=
  ∀ z ∈ 𝔻,
    C⁻¹ * (hypDistSet z {w | w ∈ 𝔻 ∧ h w = 0} / ENNReal.ofReal (massRadiusDisc μ z)) ^ M ≤
        ENNReal.ofReal (‖h z‖ * Real.exp (-ψ z)) ∧
      ENNReal.ofReal (‖h z‖ * Real.exp (-ψ z)) ≤
        C * (hypDistSet z {w | w ∈ 𝔻 ∧ h w = 0} / ENNReal.ofReal (massRadiusDisc μ z)) ∧
      hypDistSet z {w | w ∈ 𝔻 ∧ h w = 0} ≤ C * ENNReal.ofReal (massRadiusDisc μ z)

end OC
