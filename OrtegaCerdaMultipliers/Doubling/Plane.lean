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
    [FiniteDimensional ℝ E] [Nontrivial E] : BallGeometry E where
  exists_between x y s hs hsd := by
    by_cases hxy : x = y
    · subst hxy
      rw [dist_self] at hsd
      have hs0 : s = 0 := le_antisymm hsd hs
      subst hs0
      exact ⟨x, by simp, by simp⟩
    · have hd : 0 < dist x y := dist_pos.2 hxy
      have hc0 : 0 ≤ s / dist x y := div_nonneg hs hd.le
      have hc1 : s / dist x y ≤ 1 := (div_le_one hd).2 hsd
      have hnorm : ‖y - x‖ = dist x y := by rw [← dist_eq_norm, dist_comm]
      refine ⟨x + (s / dist x y) • (y - x), le_of_eq ?_, le_of_eq ?_⟩
      · rw [dist_eq_norm, show x - (x + (s / dist x y) • (y - x)) = -((s / dist x y) • (y - x)) by
          abel, norm_neg, norm_smul, Real.norm_of_nonneg hc0, hnorm, div_mul_cancel₀ _ hd.ne']
      · rw [dist_eq_norm, show x + (s / dist x y) • (y - x) - y = (1 - s / dist x y) • (x - y) by
          module, norm_smul, Real.norm_of_nonneg (by linarith), ← dist_eq_norm]
        field_simp
  exists_far x r := by
    obtain ⟨v, hv⟩ := exists_ne (0 : E)
    refine ⟨x + (max r 0 / ‖v‖) • v, ?_⟩
    rw [dist_eq_norm, show x - (x + (max r 0 / ‖v‖) • v) = -((max r 0 / ‖v‖) • v) by abel,
      norm_neg, norm_smul, Real.norm_of_nonneg (by positivity),
      div_mul_cancel₀ _ (norm_ne_zero_iff.2 hv)]
    exact le_max_left _ _
  covering R ε hε := by
    classical
    obtain ⟨t, -, htfin, hcov⟩ := finite_cover_balls_of_compact (isCompact_closedBall (0 : E) |R|) hε
    refine ⟨htfin.toFinset.card, fun x ↦ ⟨htfin.toFinset.image (x + ·), Finset.card_image_le, ?_⟩⟩
    intro z hz
    have hz' : z - x ∈ closedBall (0 : E) |R| := by
      rw [mem_closedBall_zero_iff, ← dist_eq_norm]
      exact (mem_ball.1 hz).le.trans (le_abs_self R)
    obtain ⟨y, hy, hzy⟩ := mem_iUnion₂.1 (hcov hz')
    refine mem_iUnion₂.2 ⟨x + y, Finset.mem_image.2 ⟨y, htfin.mem_toFinset.2 hy, rfl⟩, ?_⟩
    rw [mem_ball, dist_eq_norm] at hzy ⊢
    rwa [show z - (x + y) = z - x - y by abel]

example : BallGeometry ℂ := inferInstance
example : BallGeometry ℝ := inferInstance

theorem isLocallyDoubling_iff (μ : Measure ℂ) : IsLocallyDoubling μ ↔ IsLocDoublingM μ :=
  Iff.rfl

theorem massRadius_eq (μ : Measure ℂ) : massRadius μ = massRadiusM μ := rfl

theorem IsDoubling.isLocallyDoubling {μ : Measure ℂ} (h : IsDoubling μ) : IsLocallyDoubling μ := by
  obtain ⟨C, hC⟩ := h
  exact ⟨C, fun z r hr _ ↦ hC z r hr⟩

/-- Real affine lines in `ℂ` are porous. -/
theorem isPorous_line (p v : ℂ) : IsPorous {z : ℂ | ∃ t : ℝ, z = p + t * v} := by
  refine ⟨1, 1, one_pos, one_pos, ?_⟩
  rintro y ⟨t₀, rfl⟩ s hs _
  by_cases hv : v = 0
  · subst hv
    refine ⟨p + t₀ * 0 + s, ?_, ?_⟩
    · rw [dist_eq_norm, show p + t₀ * 0 - (p + t₀ * 0 + s) = -(s : ℂ) by ring, norm_neg,
        Complex.norm_real, Real.norm_of_nonneg hs.le]
    · rintro e ⟨t, rfl⟩
      rw [dist_eq_norm, show p + t₀ * 0 + s - (p + t * 0) = (s : ℂ) by ring,
        Complex.norm_real, Real.norm_of_nonneg hs.le, one_mul]
  · have hvn : 0 < ‖v‖ := norm_pos_iff.2 hv
    refine ⟨p + t₀ * v + ((s / ‖v‖ : ℝ) : ℂ) * I * v, le_of_eq ?_, ?_⟩
    · rw [dist_eq_norm, show p + t₀ * v - (p + t₀ * v + ((s / ‖v‖ : ℝ) : ℂ) * I * v) =
          -(((s / ‖v‖ : ℝ) : ℂ) * I * v) by ring, norm_neg, norm_mul, norm_mul, Complex.norm_I,
        Complex.norm_real, Real.norm_of_nonneg (by positivity), mul_one,
        div_mul_cancel₀ _ hvn.ne']
    · rintro e ⟨t, rfl⟩
      rw [one_mul, dist_eq_norm]
      have e1 : p + t₀ * v + ((s / ‖v‖ : ℝ) : ℂ) * I * v - (p + t * v) =
          v * (((t₀ - t : ℝ) : ℂ) + ((s / ‖v‖ : ℝ) : ℂ) * I) := by
        push_cast
        ring
      rw [e1, norm_mul]
      have him := Complex.abs_im_le_norm (((t₀ - t : ℝ) : ℂ) + ((s / ‖v‖ : ℝ) : ℂ) * I)
      have him' : (((t₀ - t : ℝ) : ℂ) + ((s / ‖v‖ : ℝ) : ℂ) * I).im = s / ‖v‖ := by simp
      rw [him', abs_of_pos (by positivity)] at him
      calc s = ‖v‖ * (s / ‖v‖) := by field_simp
        _ ≤ _ := by gcongr

theorem isPorous_segment (a b : ℂ) : IsPorous (segment ℝ a b) := by
  refine (isPorous_line a (b - a)).mono ?_
  rw [segment_eq_image]
  rintro z ⟨θ, -, rfl⟩
  refine ⟨θ, ?_⟩
  simp only [Complex.real_smul]
  push_cast
  ring

end OC
