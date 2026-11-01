import OrtegaCerdaMultipliers.Multiplier.Defs

/-!
# M08 (Multiplier) — Elementary auxiliary lemmas

Helper file (not in the blueprint's file list): monotonicity of `tanh`, the Euclidean size of
closed hyperbolic balls, and similar small facts used throughout M08.
-/

open MeasureTheory Metric Set Complex
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace OC

theorem tanh_mem_Ioo (x : ℝ) : Real.tanh x ∈ Ioo (-1 : ℝ) 1 :=
  ⟨Real.neg_one_lt_tanh x, Real.tanh_lt_one x⟩

theorem tanh_le_tanh {a b : ℝ} (h : a ≤ b) : Real.tanh a ≤ Real.tanh b := by
  rwa [← Real.artanh_le_artanh_iff (tanh_mem_Ioo a) (tanh_mem_Ioo b), Real.artanh_tanh,
    Real.artanh_tanh]

theorem tanh_lt_tanh {a b : ℝ} (h : a < b) : Real.tanh a < Real.tanh b := by
  rwa [← Real.artanh_lt_artanh_iff (tanh_mem_Ioo a) (tanh_mem_Ioo b), Real.artanh_tanh,
    Real.artanh_tanh]

theorem tanh_pos' {x : ℝ} (hx : 0 < x) : 0 < Real.tanh x := by
  simpa [Real.tanh_zero] using tanh_lt_tanh hx

/-- A point at hyperbolic distance `≤ r` from `z` lies in the closed Euclidean disc of radius
`tanh (artanh ‖z‖ + r) < 1`. -/
theorem norm_le_of_hypDist_le {z w : ℂ} (hz : z ∈ 𝔻) (hw : w ∈ 𝔻) {r : ℝ}
    (h : hypDist z w ≤ r) : ‖w‖ ≤ Real.tanh (Real.artanh ‖z‖ + r) := by
  have h0 : (0 : ℂ) ∈ 𝔻 := mem_ball_self one_pos
  have htri := hypDist_triangle h0 hz hw
  rw [hypDist_zero_left, hypDist_zero_left] at htri
  have hw1 : ‖w‖ ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [norm_nonneg w], norm_lt_one_of_mem_disc hw⟩
  calc ‖w‖ = Real.tanh (Real.artanh ‖w‖) := (Real.tanh_artanh hw1).symm
    _ ≤ Real.tanh (Real.artanh ‖z‖ + r) := tanh_le_tanh (by linarith)

/-- The closed hyperbolic ball is contained in a compact subset of `𝔻`. -/
theorem closedHypBall_subset_closedBall {z : ℂ} (hz : z ∈ 𝔻) (r : ℝ) :
    {w | w ∈ 𝔻 ∧ hypDist z w ≤ r} ⊆ closedBall 0 (Real.tanh (Real.artanh ‖z‖ + r)) :=
  fun w hw ↦ by rw [mem_closedBall, dist_zero_right]; exact norm_le_of_hypDist_le hz hw.1 hw.2

theorem closedBall_tanh_subset_disc (s : ℝ) : closedBall (0 : ℂ) (Real.tanh s) ⊆ 𝔻 :=
  closedBall_subset_ball (Real.tanh_lt_one s)

end OC
