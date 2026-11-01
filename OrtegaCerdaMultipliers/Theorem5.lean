import OrtegaCerdaMultipliers.Line.Potential
import OrtegaCerdaMultipliers.LogModulusWeak
import OrtegaCerdaMultipliers.Potential.Fundamental

/-!
# M13 (Theorem5) — Theorem 5: multipliers for Laplacians carried by the real line

See `blueprint/M13_Theorem5.md` §3.7–§3.8.  Scaffold: statements, proofs `sorry`.  `theorem5`
(verbatim from `comparator/statements.lean`) is proved from `lineMultipliers` (case `α = 0`).

Upstream (reconciled): `logKernel`, `weylLaplacian` and the unconditional M07 entry point
(`LogModulusWeak.lean`); `integrableOn_log_norm_sub_uniform`,
`integral_logPotential_mul_laplacian` (M02, `Potential/Fundamental.lean`); `IsLineMeasure` and
L1–L8 (M03, `Doubling/LineMeasure.lean`).
-/

open MeasureTheory Metric Set Complex
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace OC

/-! 13.7 the Laplacian of `α|Im z|` -/
theorem integral_abs_im_mul_laplacian (χ : ℂ → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hc : HasCompactSupport χ) :
    ∫ z, |z.im| * Laplacian.laplacian χ z = 2 * ∫ t : ℝ, χ t := sorry

/-! 13.8 continuity of the logarithmic potential of a piece of `μ` -/
theorem IsLineMeasure.continuous_logPotential_Ioc {μ : Measure ℂ} (hμ : IsLineMeasure μ)
    (a b : ℝ) :
    Continuous fun z : ℂ ↦ ∫ t in Ioc a b, Real.log ‖z - t‖ ∂linePull μ := sorry

/-! 13.9 `φ − α|Im z| + S` is the log-modulus of an entire function (M07 weak entry) -/
theorem isWeakLogModulus_linePotential {φ : ℂ → ℝ} {μ : Measure ℂ}
    (hφ : IsSubharmonicWeight univ φ μ) (hμ : IsLineMeasure μ) :
    ∃ α₁ s₁ : ℝ, 0 < α₁ ∧ 0 < s₁ ∧ s₁ ≤ 1 / 8 ∧ ∀ α : ℝ, 0 ≤ α → α ≤ α₁ →
      ∀ s : ℝ, 0 ≤ s → s ≤ s₁ →
      IsWeakLogModulus univ (lineZeroCount μ α s)
        (fun z ↦ φ z - α * |z.im| + linePotential μ α s z) := sorry

/-! 13.10 main export: two multipliers for `φ − α|Im z|` with disjoint exceptional sets -/
theorem lineMultipliers (φ : ℂ → ℝ) (μ : Measure ℂ) (hφ : IsSubharmonicWeight univ φ μ)
    (hd : IsLocallyDoublingLine μ) (hm : ∃ r : ℝ, 0 < r ∧ ∀ x : ℝ, 1 < μ (lineInterval x r)) :
    ∃ α₀ : ℝ, 0 < α₀ ∧ ∀ α : ℝ, 0 ≤ α → α ≤ α₀ →
      ∃ (f : Fin 2 → ℂ → ℂ) (ε C : ℝ), 0 < ε ∧ 0 < C ∧
        (∀ i, Differentiable ℂ (f i)) ∧ (∀ i, ∃ z₀, f i z₀ ≠ 0) ∧
        (∀ i (z : ℂ), f i z = 0 → z.im = 0) ∧
        (∀ i (z : ℂ), ‖f i z‖ ≤ C * Real.exp (φ z - α * |z.im|)) ∧
        (∀ z : ℂ, ∃ i, ∀ x : ℝ, f i x = 0 → ε * massRadiusLine μ x ≤ ‖z - x‖) ∧
        ∀ η : ℝ, 0 < η → ∃ c : ℝ, 0 < c ∧ ∀ i (z : ℂ),
          (∀ x : ℝ, f i x = 0 → η * massRadiusLine μ x ≤ ‖z - x‖) →
            c * Real.exp (φ z - α * |z.im|) ≤ ‖f i z‖ := sorry

/-- **Theorem 5** (statement verbatim from `comparator/statements.lean`). -/
theorem theorem5 (φ : ℂ → ℝ) (μ : Measure ℂ) (hφ : IsSubharmonicWeight univ φ μ)
    (hd : IsLocallyDoublingLine μ) (hm : ∃ r : ℝ, 0 < r ∧ ∀ x : ℝ, 1 < μ (lineInterval x r)) :
    ∃ f : ℂ → ℂ, Differentiable ℂ f ∧ (∃ z₀, f z₀ ≠ 0) ∧ (∀ z, f z = 0 → z.im = 0) ∧
      ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ,
        (∀ x : ℝ, f x = 0 → ε * massRadiusLine μ x ≤ ‖z - x‖) →
          C⁻¹ * Real.exp (φ z) ≤ ‖f z‖ ∧ ‖f z‖ ≤ C * Real.exp (φ z) := by
  obtain ⟨α₀, hα₀, H⟩ := lineMultipliers φ μ hφ hd hm
  obtain ⟨f, ε₀, C, hε₀, hC, hdiff, hne, hreal, hup, -, hlow⟩ := H 0 le_rfl hα₀.le
  refine ⟨f 0, hdiff 0, hne 0, hreal 0, fun ε hε ↦ ?_⟩
  obtain ⟨c, hc, hlow'⟩ := hlow ε hε
  refine ⟨max C c⁻¹, lt_max_of_lt_left hC, fun z hz ↦ ⟨?_, ?_⟩⟩
  · have h1 := hlow' 0 z hz
    simp only [zero_mul, sub_zero] at h1
    calc (max C c⁻¹)⁻¹ * Real.exp (φ z) ≤ c * Real.exp (φ z) := by
          gcongr
          rw [inv_le_comm₀ (lt_max_of_lt_left hC) hc]
          exact le_max_right _ _
      _ ≤ ‖f 0 z‖ := h1
  · have h2 := hup 0 z
    simp only [zero_mul, sub_zero] at h2
    calc ‖f 0 z‖ ≤ C * Real.exp (φ z) := h2
      _ ≤ max C c⁻¹ * Real.exp (φ z) := by gcongr; exact le_max_left _ _

end OC
