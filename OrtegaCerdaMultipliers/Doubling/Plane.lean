import OrtegaCerdaMultipliers.Doubling.Abstract

/-!
# M03 (Doubling) — Geometry instances for normed spaces; the plane

See `blueprint/M03_Doubling.md` §2.2.  Scaffold: statements, proofs `sorry`.

`BallGeometry` for finite-dimensional real normed spaces (so `ℂ` and `ℝ`), porous lines and
segments in `ℂ`, `IsDoubling → IsLocallyDoubling`.
-/

open MeasureTheory Metric Set Complex
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace OC

instance ballGeometry_normed (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] : BallGeometry E := sorry

example : BallGeometry ℂ := inferInstance
example : BallGeometry ℝ := inferInstance

theorem isLocallyDoubling_iff (μ : Measure ℂ) : IsLocallyDoubling μ ↔ IsLocDoublingM μ :=
  Iff.rfl

theorem massRadius_eq (μ : Measure ℂ) : massRadius μ = massRadiusM μ := rfl

theorem IsDoubling.isLocallyDoubling {μ : Measure ℂ} (h : IsDoubling μ) : IsLocallyDoubling μ :=
  sorry

/-- Real affine lines in `ℂ` are porous. -/
theorem isPorous_line (p v : ℂ) : IsPorous {z : ℂ | ∃ t : ℝ, z = p + t * v} := sorry

theorem isPorous_segment (a b : ℂ) : IsPorous (segment ℝ a b) := sorry

end OC
