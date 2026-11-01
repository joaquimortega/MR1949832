import OrtegaCerdaMultipliers.Line.Partition

/-!
# M13 (Theorem5) — The correction potential `S = Σ_k T_k`

See `blueprint/M13_Theorem5.md` §3.5–§3.6.  Scaffold: statements, proofs `sorry`; definitions are
real.
-/

open MeasureTheory Metric Set Complex
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace OC

/-- `T_k(z) = (1/2π) ∫_{I_k} (½ log|z−ν₊| + ½ log|z−ν₋| − log|z−t|) dσ_α(t)`, using `σ_α(I_k) = 4π`. -/
def lineTerm (μ : Measure ℂ) (α s : ℝ) (k : ℤ) (z : ℂ) : ℝ :=
  Real.log ‖z - lineNode μ α s k true‖ + Real.log ‖z - lineNode μ α s k false‖ -
    (1 / (2 * Real.pi)) *
      ((∫ t in Ioc (lineKnot μ α k) (lineKnot μ α (k + 1)), Real.log ‖z - t‖ ∂linePull μ) -
        2 * α * ∫ t in lineKnot μ α k..lineKnot μ α (k + 1), Real.log ‖z - t‖)

/-- The correction potential `S = Σ_k T_k`. -/
def linePotential (μ : Measure ℂ) (α s : ℝ) (z : ℂ) : ℝ :=
  ∑' k : ℤ, lineTerm μ α s k z

/-- The nodes of sign `b`, as a subset of `ℂ`. -/
def lineNodeSet (μ : Measure ℂ) (α s : ℝ) (b : Bool) : Set ℂ :=
  range fun k : ℤ ↦ ((lineNode μ α s k b : ℝ) : ℂ)

/-- Zero set of the multiplier with offset `s`. -/
def lineZeroSet (μ : Measure ℂ) (α s : ℝ) : Set ℂ :=
  lineNodeSet μ α s true ∪ lineNodeSet μ α s false

/-- Its counting function: `2` at `λ_k` when `s = 0`, `1` at `λ_k ± s a_k` when `0 < s ≤ s₀`. -/
def lineZeroCount (μ : Measure ℂ) (α s : ℝ) (z : ℂ) : ℕ :=
  (lineNodeSet μ α s true).indicator 1 z + (lineNodeSet μ α s false).indicator 1 z

/-! 13.5 far-field and near-field estimates of a single term -/
theorem IsLineMeasure.abs_lineTerm_le_of_far {μ : Measure ℂ} (hμ : IsLineMeasure μ) :
    ∃ α₁ : ℝ, 0 < α₁ ∧ ∀ α : ℝ, 0 ≤ α → α ≤ α₁ → ∀ s : ℝ, 0 ≤ s → s ≤ 1 / 2 → ∀ (k : ℤ) (z : ℂ),
      2 * lineLength μ α k ≤ ‖z - lineCentre μ α k‖ →
      |lineTerm μ α s k z| ≤ 8 * (lineLength μ α k / ‖z - lineCentre μ α k‖) ^ 2 := sorry
theorem IsLineMeasure.lineTerm_le_of_near {μ : Measure ℂ} (hμ : IsLineMeasure μ) :
    ∃ α₁ C : ℝ, 0 < α₁ ∧ ∀ α : ℝ, 0 ≤ α → α ≤ α₁ → ∀ s : ℝ, 0 ≤ s → s ≤ 1 / 2 →
      ∀ (k : ℤ) (z : ℂ), ‖z - lineCentre μ α k‖ < 2 * lineLength μ α k →
      (∀ b : Bool, z ≠ lineNode μ α s k b) → lineTerm μ α s k z ≤ C := sorry
theorem IsLineMeasure.le_lineTerm_of_near {μ : Measure ℂ} (hμ : IsLineMeasure μ) :
    ∃ α₁ s₁ C : ℝ, 0 < α₁ ∧ 0 < s₁ ∧ s₁ ≤ 1 / 8 ∧ ∀ α : ℝ, 0 ≤ α → α ≤ α₁ →
      ∀ s : ℝ, 0 ≤ s → s ≤ s₁ →
      ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ (k : ℤ) (z : ℂ),
      ‖z - lineCentre μ α k‖ < 2 * lineLength μ α k →
      (∀ b : Bool, η * massRadiusLine μ (lineNode μ α s k b) ≤ ‖z - lineNode μ α s k b‖) →
      2 * Real.log η - C ≤ lineTerm μ α s k z := sorry

/-! 13.6 the potential: summability and two-sided bounds -/
theorem IsLineMeasure.summable_lineTerm {μ : Measure ℂ} (hμ : IsLineMeasure μ) :
    ∃ α₁ : ℝ, 0 < α₁ ∧ ∀ α : ℝ, 0 ≤ α → α ≤ α₁ → ∀ s : ℝ, 0 ≤ s → s ≤ 1 / 2 → ∀ z : ℂ,
      Summable fun k : ℤ ↦ lineTerm μ α s k z := sorry
theorem IsLineMeasure.linePotential_bounds {μ : Measure ℂ} (hμ : IsLineMeasure μ) :
    ∃ α₁ s₁ C : ℝ, 0 < α₁ ∧ 0 < s₁ ∧ s₁ ≤ 1 / 8 ∧ ∀ α : ℝ, 0 ≤ α → α ≤ α₁ →
      ∀ s : ℝ, 0 ≤ s → s ≤ s₁ →
      (∀ z, z ∉ lineZeroSet μ α s → linePotential μ α s z ≤ C) ∧
      ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ z : ℂ,
        (∀ ν ∈ lineZeroSet μ α s, η * massRadiusLine μ ν.re ≤ ‖z - ν‖) →
        -C * (1 + |Real.log η|) ≤ linePotential μ α s z := sorry

end OC
