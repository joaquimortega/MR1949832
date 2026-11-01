import OrtegaCerdaMultipliers.Doubling.Plane

/-!
# M03 (Doubling) — The line: pull-back of `μ` to `ℝ`

See `blueprint/M03_Doubling.md` §2.2.  Scaffold: statements, proofs `sorry`; definitions are real.

`linePull μ = μ.comap ofReal`, transfer of `IsLocallyDoublingLine` and `massRadiusLine`.
-/

open MeasureTheory Metric Set Complex
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace OC

/-- The pull-back of `μ` to `ℝ`. -/
def linePull (μ : Measure ℂ) : Measure ℝ := μ.comap fun x : ℝ ↦ (x : ℂ)

theorem linePull_ball (μ : Measure ℂ) (x r : ℝ) : linePull μ (ball x r) = μ (lineInterval x r) :=
  sorry

theorem linePull_apply (μ : Measure ℂ) (s : Set ℝ) :
    linePull μ s = μ ((fun x : ℝ ↦ (x : ℂ)) '' s) := sorry

theorem IsLocallyDoublingLine.isLocDoublingM {μ : Measure ℂ} (h : IsLocallyDoublingLine μ) :
    IsLocDoublingM (linePull μ) := sorry

theorem massRadiusLine_eq (μ : Measure ℂ) (x : ℝ) :
    massRadiusLine μ x = massRadiusM (linePull μ) x := sorry

theorem IsLocallyDoublingLine.measure_image_eq {μ : Measure ℂ} (h : IsLocallyDoublingLine μ)
    (s : Set ℂ) : μ s = μ (s ∩ range fun x : ℝ ↦ (x : ℂ)) := sorry

end OC
