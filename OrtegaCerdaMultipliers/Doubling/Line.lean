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

/-- `ofReal` is a measurable embedding (a closed isometric embedding). -/
theorem measurableEmbedding_ofReal' : MeasurableEmbedding fun x : ℝ ↦ (x : ℂ) :=
  Complex.isometry_ofReal.isClosedEmbedding.measurableEmbedding

theorem linePull_ball (μ : Measure ℂ) (x r : ℝ) : linePull μ (ball x r) = μ (lineInterval x r) := by
  rw [linePull, measurableEmbedding_ofReal'.comap_apply, Real.ball_eq_Ioo]
  rfl

theorem linePull_apply (μ : Measure ℂ) (s : Set ℝ) :
    linePull μ s = μ ((fun x : ℝ ↦ (x : ℂ)) '' s) :=
  measurableEmbedding_ofReal'.comap_apply μ s

theorem IsLocallyDoublingLine.isLocDoublingM {μ : Measure ℂ} (h : IsLocallyDoublingLine μ) :
    IsLocDoublingM (linePull μ) := by
  obtain ⟨_, C, hC⟩ := h
  refine ⟨C, fun x r hr h2r ↦ ?_⟩
  rw [linePull_ball, linePull_ball]
  exact hC x r hr h2r

theorem massRadiusLine_eq (μ : Measure ℂ) (x : ℝ) :
    massRadiusLine μ x = massRadiusM (linePull μ) x := by
  simp only [massRadiusLine, massRadiusM, linePull_ball]

theorem IsLocallyDoublingLine.measure_image_eq {μ : Measure ℂ} (h : IsLocallyDoublingLine μ)
    (s : Set ℂ) : μ s = μ (s ∩ range fun x : ℝ ↦ (x : ℂ)) := by
  have hc : (range fun x : ℝ ↦ (x : ℂ))ᶜ = {z : ℂ | z.im ≠ 0} := by
    ext z
    simp only [mem_compl_iff, mem_range, not_exists]
    constructor
    · intro hz him
      exact hz z.re (Complex.ext (by simp) (by simp [him]))
    · intro him x hx
      apply him
      rw [← hx]
      simp
  exact (measure_inter_conull (by rw [hc]; exact h.1)).symm

end OC
