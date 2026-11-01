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

namespace OC

theorem tanh_div_one_sub_tanh_eq (s : ℝ) :
    Real.tanh s / (1 - Real.tanh s) = (Real.exp (2 * s) - 1) / 2 := by
  rw [tanh_eq_exp_two_mul]
  have h := Real.exp_pos (2 * s)
  field_simp
  ring

theorem exp_two_mul_sub_one_le (s : ℝ) (hs : 0 ≤ s) :
    (Real.exp (2 * s) - 1) / 2 ≤ s * Real.exp (2 * s) := by
  have h1 := Real.add_one_le_exp (-(2 * s))
  have h2 : Real.exp (2 * s) * Real.exp (-(2 * s)) = 1 := by
    rw [← Real.exp_add]; simp
  have h3 := Real.exp_pos (2 * s)
  nlinarith

/-- Euclidean size of a hyperbolic neighbourhood: `|w - c| ≤ s e^{2s} (1 - |c|²)`. -/
theorem norm_sub_le_mul_exp {c w : ℂ} (hc : c ∈ 𝔻) (hw : w ∈ 𝔻) {s : ℝ} (hs0 : 0 ≤ s)
    (hs : hypDist c w ≤ s) : ‖w - c‖ ≤ s * Real.exp (2 * s) * (1 - ‖c‖ ^ 2) := by
  have h := norm_sub_le_of_hypDist_le hc hw hs (Real.tanh_lt_one s)
  rw [tanh_div_one_sub_tanh_eq] at h
  exact h.trans (mul_le_mul_of_nonneg_right (exp_two_mul_sub_one_le s hs0)
    (one_sub_normSq_pos hc).le)

theorem norm_one_sub_conj_mul_comm (z c : ℂ) : ‖1 - conj c * z‖ = ‖1 - conj z * c‖ := by
  rw [← Complex.norm_conj (1 - conj c * z)]; simp [map_sub, mul_comm]

/-- `|z - c| = tanh β(c, z) · |1 - z̄ c|`. -/
theorem norm_sub_eq_tanh_mul {z c : ℂ} (hz : z ∈ 𝔻) (hc : c ∈ 𝔻) :
    ‖z - c‖ = Real.tanh (hypDist c z) * ‖1 - conj z * c‖ := by
  rw [tanh_hypDist hc hz, pseudoHyp, norm_sub_rev c z, norm_one_sub_conj_mul_comm,
    div_mul_cancel₀ _ (norm_one_sub_conj_mul_pos hz hc).ne']

theorem one_sub_normSq_le_two_mul_norm {z c : ℂ} (hz : z ∈ 𝔻) (hc : c ∈ 𝔻) :
    1 - ‖c‖ ^ 2 ≤ 2 * ‖1 - conj z * c‖ := by
  have h1 := one_sub_mul_le_norm_one_sub_conj_mul z c
  have hz1 := norm_lt_one_of_mem_disc hz
  have hc1 := norm_lt_one_of_mem_disc hc
  nlinarith [norm_nonneg z, norm_nonneg c]

theorem exp_quarter_le : Real.exp (1 / 4) ≤ 4 / 3 := by
  by_contra h
  push Not at h
  have h4 : (4 / 3 : ℝ) ^ 4 < Real.exp (1 / 4) ^ 4 := pow_lt_pow_left₀ h (by norm_num) (by norm_num)
  rw [← Real.exp_nat_mul] at h4
  norm_num at h4
  have := Real.exp_one_lt_d9
  linarith

end OC

namespace OC

theorem tanh_le_self {x : ℝ} (hx : 0 ≤ x) : Real.tanh x ≤ x := by
  set t := Real.tanh x
  have ht0 : 0 ≤ t := tanh_nonneg_of_nonneg hx
  have ht1 : t < 1 := Real.tanh_lt_one x
  have habs : |t| < 1 := by rw [abs_of_nonneg ht0]; exact ht1
  have hs := Real.hasSum_log_sub_log_of_abs_lt_one habs
  have hle := le_hasSum hs 0 fun j _ ↦ by positivity
  have hx' : x = Real.artanh t := (Real.artanh_tanh x).symm
  rw [Real.artanh_eq_half_log ⟨by linarith, ht1.le⟩,
    Real.log_div (by linarith) (by linarith)] at hx'
  simp at hle
  linarith

/-- `tanh x ≥ c x` on `[0, S]`, with `c = min (1/5) (tanh 1 / S)`. -/
theorem mul_le_tanh {S x : ℝ} (hS : 0 < S) (hx : 0 ≤ x) (hxS : x ≤ S) :
    min (1 / 5) (Real.tanh 1 / S) * x ≤ Real.tanh x := by
  by_cases h1 : x ≤ 1
  · calc min (1 / 5) (Real.tanh 1 / S) * x ≤ 1 / 5 * x :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) hx
      _ = x / 5 := by ring
      _ ≤ Real.tanh x := div_five_le_tanh hx h1
  · push Not at h1
    calc min (1 / 5) (Real.tanh 1 / S) * x ≤ Real.tanh 1 / S * x :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hx
      _ ≤ Real.tanh 1 / S * S := by
          gcongr
          exact div_nonneg (tanh_pos' one_pos).le hS.le
      _ = Real.tanh 1 := by field_simp
      _ ≤ Real.tanh x := tanh_le_tanh h1.le

end OC
