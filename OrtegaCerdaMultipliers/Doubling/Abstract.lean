/-
Copyright (c) 2026 Joaquim Ortega-Cerdà. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joaquim Ortega-Cerdà
-/
import OrtegaCerdaMultipliers.Doubling.AbstractBase

/-!
# M03 (Doubling) — Locally doubling measures on a metric space

See `blueprint/M03_Doubling.md` §2.1.  All proofs are complete.

Second part of the theory of §2 on an abstract metric space `X` with `BallGeometry` (the first
part is `Doubling/AbstractBase.lean`): the mass radius, Claim 1, Lemma 3, [Chr91, Lemma 2.3],
growth, decay, bounded count.
-/

open MeasureTheory Metric Set Complex
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace OC

section Abstract

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

/-! ### The mass radius -/

omit [OpensMeasurableSpace X] in
theorem massRadiusM_le {μ : Measure X} {x : X} {R : ℝ} (hR : 0 < R) (h : 1 ≤ μ (ball x R)) :
    massRadiusM μ x ≤ R :=
  csInf_le ⟨0, fun _ hr ↦ hr.1.le⟩ ⟨hR, h⟩

omit [OpensMeasurableSpace X] in
theorem massRadiusM_nonneg (μ : Measure X) (x : X) : 0 ≤ massRadiusM μ x :=
  Real.sInf_nonneg fun _ hr ↦ hr.1.le

omit [OpensMeasurableSpace X] in
theorem measure_ball_lt_one_of_lt_massRadiusM' {μ : Measure X} {x : X} {r : ℝ}
    (hr : r < massRadiusM μ x) : μ (ball x r) < 1 := by
  by_cases hr0 : r ≤ 0
  · rw [ball_eq_empty.2 hr0, measure_empty]
    exact zero_lt_one
  rw [not_le] at hr0
  by_contra h
  rw [not_lt] at h
  exact absurd (massRadiusM_le hr0 h) (not_le.2 hr)

omit [OpensMeasurableSpace X] in
theorem measure_ball_massRadiusM_le_one (μ : Measure X) (x : X) :
    μ (ball x (massRadiusM μ x)) ≤ 1 := by
  have := tendsto_measure_iUnion_atTop (μ := μ) (monotone_ball_sub x (massRadiusM μ x))
  rw [iUnion_ball_sub] at this
  refine le_of_tendsto' this fun n ↦ (measure_ball_lt_one_of_lt_massRadiusM' ?_).le
  have : 0 < 1 / ((n : ℝ) + 1) := by positivity
  linarith

omit [OpensMeasurableSpace X] in
theorem one_le_measure_ball_of_massRadiusM_lt {μ : Measure X} {x : X}
    (hne : ∃ r, 0 < r ∧ 1 ≤ μ (ball x r)) {r : ℝ} (hr : massRadiusM μ x < r) :
    1 ≤ μ (ball x r) := by
  obtain ⟨r', hr'S, hr'r⟩ := exists_lt_of_csInf_lt (s := {r | 0 < r ∧ 1 ≤ μ (ball x r)}) hne hr
  exact hr'S.2.trans (measure_mono (ball_subset_ball hr'r.le))

omit [OpensMeasurableSpace X] in
theorem measure_ball_lt_one_of_lt_massRadiusM {μ : Measure X} {x : X} {r : ℝ}
    (hr : r < massRadiusM μ x) : μ (ball x r) < 1 :=
  measure_ball_lt_one_of_lt_massRadiusM' hr

theorem one_le_measure_closedBall_massRadiusM {μ : Measure X} {x : X}
    (hfin : ∀ r, μ (ball x r) < ∞) (hne : ∃ r, 0 < r ∧ 1 ≤ μ (ball x r)) :
    1 ≤ μ (closedBall x (massRadiusM μ x)) := by
  have := tendsto_measure_iInter_atTop (μ := μ)
    (fun n ↦ measurableSet_ball.nullMeasurableSet) (antitone_ball_add x (massRadiusM μ x))
    ⟨0, (hfin _).ne⟩
  rw [iInter_ball_add] at this
  refine ge_of_tendsto' this fun n ↦ one_le_measure_ball_of_massRadiusM_lt hne ?_
  have : 0 < 1 / ((n : ℝ) + 1) := by positivity
  linarith

theorem IsLocDoublingM.massRadiusM_pos [BallGeometry X] {μ : Measure X}
    (hd : IsLocDoublingM μ) (hfin : ∀ x : X, ∀ r : ℝ, μ (ball x r) < ∞) {x : X}
    (hne : ∃ r, 0 < r ∧ 1 ≤ μ (ball x r)) : 0 < massRadiusM μ x := by
  have htend := tendsto_measure_iInter_atTop (μ := μ)
    (fun n ↦ measurableSet_ball.nullMeasurableSet) (antitone_ball_add x 0) ⟨0, (hfin x _).ne⟩
  rw [iInter_ball_add, closedBall_zero, hd.measure_singleton hfin x] at htend
  obtain ⟨n, hn⟩ := (htend.eventually (gt_mem_nhds zero_lt_one)).exists
  simp only [Function.comp_apply, zero_add] at hn
  have hle : 1 / ((n : ℝ) + 1) ≤ massRadiusM μ x := by
    refine le_csInf hne fun r hr ↦ ?_
    by_contra h
    rw [not_le] at h
    exact absurd (hr.2.trans (measure_mono (ball_subset_ball h.le))) (not_le.2 hn)
  have : 0 < 1 / ((n : ℝ) + 1) := by positivity
  linarith

theorem IsLocDoublingM.measure_ball_massRadiusM [BallGeometry X]
    [TopologicalSpace.SeparableSpace X] {μ : Measure X} (hd : IsLocDoublingM μ)
    (hfin : ∀ x : X, ∀ r : ℝ, μ (ball x r) < ∞) {x : X}
    (hne : ∃ r, 0 < r ∧ 1 ≤ μ (ball x r)) : μ (ball x (massRadiusM μ x)) = 1 := by
  refine le_antisymm (measure_ball_massRadiusM_le_one μ x) ?_
  rw [← hd.measure_closedBall hfin]
  exact one_le_measure_closedBall_massRadiusM (hfin x) hne

omit [OpensMeasurableSpace X] in
theorem lipschitzWith_massRadiusM {μ : Measure X} (hne : ∀ x : X, ∃ r, 0 < r ∧ 1 ≤ μ (ball x r)) :
    LipschitzWith 1 (massRadiusM μ) := by
  have key : ∀ x y, massRadiusM μ y ≤ massRadiusM μ x + dist x y := by
    intro x y
    have : massRadiusM μ y - dist x y ≤ massRadiusM μ x := by
      refine le_csInf (hne x) ?_
      rintro r ⟨hr, hr1⟩
      have hsub : ball x r ⊆ ball y (r + dist x y) := by
        intro z hz
        rw [mem_ball] at hz ⊢
        have := dist_triangle z x y
        linarith
      have : massRadiusM μ y ≤ r + dist x y :=
        massRadiusM_le (by positivity) (hr1.trans (measure_mono hsub))
      linarith
    linarith
  exact LipschitzWith.of_le_add fun x y ↦ by
    have := key y x
    rwa [dist_comm] at this

omit [OpensMeasurableSpace X] in
/-- `ρ(y) ≤ ρ(x) + d(x,y)`. -/
theorem massRadiusM_le_add_dist {μ : Measure X} (hne : ∀ x : X, ∃ r, 0 < r ∧ 1 ≤ μ (ball x r))
    (x y : X) : massRadiusM μ y ≤ massRadiusM μ x + dist x y := by
  have := (lipschitzWith_massRadiusM hne).dist_le_mul y x
  rw [NNReal.coe_one, one_mul, Real.dist_eq, dist_comm y x] at this
  linarith [le_abs_self (massRadiusM μ y - massRadiusM μ x)]

/-- `μ(B(x,r)) ≍ (r/ρ(x))^{s or δ}` for `ρ(x) ≤ r ≤ R₁`. -/
theorem IsLocDoublingM.measure_ball_massRadiusM_bounds [BallGeometry X]
    [TopologicalSpace.SeparableSpace X] {μ : Measure X} (hd : IsLocDoublingM μ)
    (hfin : ∀ x : X, ∀ r : ℝ, μ (ball x r) < ∞)
    (hm : ∃ R : ℝ, 0 < R ∧ ∀ x : X, 1 ≤ μ (ball x R)) (R₁ : ℝ) :
    ∃ c C δ s : ℝ, 0 < c ∧ 0 < C ∧ 0 < δ ∧ 0 < s ∧ ∀ (x : X) (r : ℝ),
      massRadiusM μ x ≤ r → r ≤ R₁ →
        ENNReal.ofReal (c * (r / massRadiusM μ x) ^ δ) ≤ μ (ball x r) ∧
        μ (ball x r) ≤ ENNReal.ofReal (C * (r / massRadiusM μ x) ^ s) := by
  obtain ⟨c, δ, hc, hδ, hlow⟩ := hd.rpow_le_measure_ball R₁
  obtain ⟨C, s, hC, hs, hup⟩ := hd.measure_ball_le_rpow R₁
  obtain ⟨R, hR, hRm⟩ := hm
  refine ⟨c, C, δ, s, hc, hC, hδ, hs, fun x r hρr hrR ↦ ?_⟩
  have hne : ∃ r, 0 < r ∧ 1 ≤ μ (ball x r) := ⟨R, hR, hRm x⟩
  have hρ := hd.massRadiusM_pos hfin hne
  have h1 := hd.measure_ball_massRadiusM hfin hne
  have hxx : dist x x ≤ r := by rw [dist_self]; linarith
  constructor
  · simpa [h1] using hlow x x r (massRadiusM μ x) hρ hρr hrR hxx
  · simpa [h1] using hup x x r (massRadiusM μ x) hρ hρr hrR hxx

/-- **Claim 1**. -/
theorem IsLocDoublingM.claim1 [BallGeometry X] {μ : Measure X} (hd : IsLocDoublingM μ)
    (hfin : ∀ x : X, ∀ r : ℝ, μ (ball x r) < ∞)
    (hm : ∃ R : ℝ, 0 < R ∧ ∀ x : X, 1 ≤ μ (ball x R)) (K : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x y : X,
      dist x y ≤ K * max (massRadiusM μ x) (massRadiusM μ y) →
        massRadiusM μ x ≤ C * massRadiusM μ y := by
  obtain ⟨R, hR, hRm⟩ := hm
  set K' := max K 0
  have hK' : 0 ≤ K' := le_max_right _ _
  obtain ⟨c, δ, hc, hδ, hlow⟩ := hd.rpow_le_measure_ball ((K' + 1) * R)
  obtain ⟨Cu, s, hCu, -, hup⟩ := hd.measure_ball_le_rpow ((K' + 1) * R)
  set C₂ := 2 * (Cu * (K' + 1) ^ s / c) ^ (1 / δ) with hC₂def
  refine ⟨max 2 C₂, lt_max_of_lt_left two_pos, fun x y hxy ↦ ?_⟩
  have hnex : ∃ r, 0 < r ∧ 1 ≤ μ (ball x r) := ⟨R, hR, hRm x⟩
  have hney : ∃ r, 0 < r ∧ 1 ≤ μ (ball y r) := ⟨R, hR, hRm y⟩
  have hρx := hd.massRadiusM_pos hfin hnex
  have hρy := hd.massRadiusM_pos hfin hney
  have hρxR : massRadiusM μ x ≤ R := massRadiusM_le hR (hRm x)
  set ρx := massRadiusM μ x
  set ρy := massRadiusM μ y with hρydef
  by_cases h2 : ρx ≤ 2 * ρy
  · exact h2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hρy.le)
  rw [not_le] at h2
  have hmax : max ρx ρy = ρx := max_eq_left (by linarith)
  have hd' : dist x y ≤ K' * ρx := by
    rw [hmax] at hxy
    exact hxy.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hρx.le)
  have hy2 : 1 ≤ μ (ball y (2 * ρy)) := one_le_measure_ball_of_massRadiusM_lt hney (by linarith)
  have hRK : R ≤ (K' + 1) * R := by nlinarith
  have hL := hlow y y ρx (2 * ρy) (by positivity) h2.le (hρxR.trans hRK)
    (by rw [dist_self]; positivity)
  have hsub : ball y ρx ⊆ ball x ((K' + 1) * ρx) := by
    intro z hz
    rw [mem_ball] at hz ⊢
    have := dist_triangle z y x
    rw [dist_comm y x] at this
    linarith
  have hU := hup x x ((K' + 1) * ρx) ρx hρx (by nlinarith) (by nlinarith)
    (by rw [dist_self]; positivity)
  have hx1 : μ (ball x ρx) ≤ 1 := measure_ball_massRadiusM_le_one μ x
  have hchain : ENNReal.ofReal (c * (ρx / (2 * ρy)) ^ δ) ≤ ENNReal.ofReal (Cu * (K' + 1) ^ s) := by
    calc ENNReal.ofReal (c * (ρx / (2 * ρy)) ^ δ)
        ≤ ENNReal.ofReal (c * (ρx / (2 * ρy)) ^ δ) * μ (ball y (2 * ρy)) :=
          le_mul_of_one_le_right' hy2
      _ ≤ μ (ball y ρx) := hL
      _ ≤ μ (ball x ((K' + 1) * ρx)) := measure_mono hsub
      _ ≤ ENNReal.ofReal (Cu * ((K' + 1) * ρx / ρx) ^ s) * μ (ball x ρx) := hU
      _ ≤ ENNReal.ofReal (Cu * ((K' + 1) * ρx / ρx) ^ s) * 1 := by gcongr
      _ = ENNReal.ofReal (Cu * (K' + 1) ^ s) := by
          rw [mul_one, mul_div_assoc, div_self hρx.ne', mul_one]
  have hreal : c * (ρx / (2 * ρy)) ^ δ ≤ Cu * (K' + 1) ^ s :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hchain
  have h3 : ρx / (2 * ρy) ≤ (Cu * (K' + 1) ^ s / c) ^ (1 / δ) := by
    have h4 : (ρx / (2 * ρy)) ^ δ ≤ Cu * (K' + 1) ^ s / c := by
      rw [le_div_iff₀ hc]
      linarith
    calc ρx / (2 * ρy) = ((ρx / (2 * ρy)) ^ δ) ^ (1 / δ) := by
          rw [← Real.rpow_mul (by positivity), mul_one_div_cancel hδ.ne', Real.rpow_one]
      _ ≤ _ := Real.rpow_le_rpow (by positivity) h4 (by positivity)
  rw [div_le_iff₀ (by positivity)] at h3
  calc ρx ≤ (Cu * (K' + 1) ^ s / c) ^ (1 / δ) * (2 * ρy) := h3
    _ = C₂ * ρy := by rw [hC₂def]; ring
    _ ≤ max 2 C₂ * ρy := mul_le_mul_of_nonneg_right (le_max_right _ _) hρy.le

/-- Decay of `ρ(ζ)/d(z,ζ)`, power form (proved before Lemma 3, which uses it). -/
theorem IsLocDoublingM.massRadiusM_div_dist_le_aux [BallGeometry X] {μ : Measure X}
    (hd : IsLocDoublingM μ) (hfin : ∀ x : X, ∀ r : ℝ, μ (ball x r) < ∞)
    (hm : ∃ R : ℝ, 0 < R ∧ ∀ x : X, 1 ≤ μ (ball x R)) (M₀ : ℝ) :
    ∃ C α : ℝ, 0 < C ∧ 0 < α ∧ α ≤ 1 ∧ ∀ z ζ : X, massRadiusM μ z ≤ dist z ζ → dist z ζ ≤ M₀ →
      massRadiusM μ ζ / dist z ζ ≤ C * (massRadiusM μ z / dist z ζ) ^ α := by
  obtain ⟨R, hR, hRm⟩ := hm
  have hne : ∀ x : X, ∃ r, 0 < r ∧ 1 ≤ μ (ball x r) := fun x ↦ ⟨R, hR, hRm x⟩
  obtain ⟨CU, s, hCU, hs, hup⟩ := hd.measure_ball_le_rpow (3 * M₀)
  obtain ⟨c, δ, hc, hδ, hlow⟩ := hd.rpow_le_measure_ball (3 * M₀)
  set α := min 1 (δ / s)
  have hα : 0 < α := lt_min one_pos (by positivity)
  refine ⟨3 * (CU / c) ^ (1 / s), α, by positivity, hα, min_le_left _ _,
    fun z ζ hzd hdM ↦ ?_⟩
  set d := dist z ζ
  set ρz := massRadiusM μ z
  set ρζ := massRadiusM μ ζ
  have hρz : 0 < ρz := hd.massRadiusM_pos hfin (hne z)
  have hρζ : 0 < ρζ := hd.massRadiusM_pos hfin (hne ζ)
  have hdpos : 0 < d := hρz.trans_le hzd
  have hlip : ρζ ≤ ρz + d := massRadiusM_le_add_dist hne z ζ
  have hU := hup z ζ (3 * d) ρζ hρζ (by linarith) (by linarith) (by linarith)
  have hL := hlow z z (3 * d) (2 * ρz) (by positivity) (by linarith) (by linarith)
    (by rw [dist_self]; positivity)
  have h1 : μ (ball ζ ρζ) ≤ 1 := measure_ball_massRadiusM_le_one μ ζ
  have h2 : 1 ≤ μ (ball z (2 * ρz)) := one_le_measure_ball_of_massRadiusM_lt (hne z) (by linarith)
  set P := 3 * d / ρζ with hPdef
  set Q := 3 * d / (2 * ρz) with hQdef
  have hPpos : 0 < P := by positivity
  have hQpos : 0 < Q := by positivity
  have hchain : ENNReal.ofReal (c * Q ^ δ) ≤ ENNReal.ofReal (CU * P ^ s) := by
    calc ENNReal.ofReal (c * Q ^ δ) ≤ ENNReal.ofReal (c * Q ^ δ) * μ (ball z (2 * ρz)) :=
          le_mul_of_one_le_right' h2
      _ ≤ μ (ball z (3 * d)) := hL
      _ ≤ ENNReal.ofReal (CU * P ^ s) * μ (ball ζ ρζ) := hU
      _ ≤ ENNReal.ofReal (CU * P ^ s) * 1 := by gcongr
      _ = ENNReal.ofReal (CU * P ^ s) := mul_one _
  have hreal : c * Q ^ δ ≤ CU * P ^ s := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hchain
  have hPQ : (c / CU) ^ (1 / s) * Q ^ (δ / s) ≤ P := by
    have h3 : c / CU * Q ^ δ ≤ P ^ s := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hCU]
      linarith
    have h4 := Real.rpow_le_rpow (by positivity) h3 (by positivity : 0 ≤ 1 / s)
    rwa [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hQpos.le,
      ← Real.rpow_mul hPpos.le, mul_one_div_cancel hs.ne', Real.rpow_one, mul_one_div] at h4
  have hQinv : Q⁻¹ ≤ ρz / d := by
    rw [hQdef, inv_div, div_le_div_iff₀ (by positivity) hdpos]
    nlinarith
  have hv1 : ρz / d ≤ 1 := (div_le_one hdpos).2 hzd
  have hvpos : 0 < ρz / d := by positivity
  calc ρζ / d = 3 / P := by rw [hPdef]; field_simp
    _ ≤ 3 / ((c / CU) ^ (1 / s) * Q ^ (δ / s)) :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity) hPQ
    _ = 3 * (CU / c) ^ (1 / s) * (Q⁻¹) ^ (δ / s) := by
        rw [Real.inv_rpow hQpos.le, ← inv_div c CU, Real.inv_rpow (by positivity)]
        field_simp
    _ ≤ 3 * (CU / c) ^ (1 / s) * (ρz / d) ^ (δ / s) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hQinv (by positivity))
          (by positivity)
    _ ≤ 3 * (CU / c) ^ (1 / s) * (ρz / d) ^ α :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_ge hvpos hv1 (min_le_right _ _)) (by positivity)

/-- Decay, geometric form (proved before Lemma 3, which uses it). -/
theorem IsLocDoublingM.decay_aux [BallGeometry X] {μ : Measure X}
    (hd : IsLocDoublingM μ) (hfin : ∀ x : X, ∀ r : ℝ, μ (ball x r) < ∞)
    (hm : ∃ R : ℝ, 0 < R ∧ ∀ x : X, 1 ≤ μ (ball x R)) (M₀ : ℝ) :
    ∃ C θ : ℝ, 0 < C ∧ 0 < θ ∧ θ < 1 ∧ ∀ (z ζ : X) (n : ℕ),
      2 ^ n * massRadiusM μ z ≤ dist z ζ → dist z ζ ≤ M₀ →
        massRadiusM μ ζ / dist z ζ ≤ C * θ ^ n := by
  obtain ⟨C, α, hC, hα, _, h⟩ := hd.massRadiusM_div_dist_le_aux hfin hm M₀
  obtain ⟨R, hR, hRm⟩ := hm
  have hne : ∀ x : X, ∃ r, 0 < r ∧ 1 ≤ μ (ball x r) := fun x ↦ ⟨R, hR, hRm x⟩
  refine ⟨C, (2 : ℝ) ^ (-α), hC, by positivity,
    Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith), fun z ζ n hn hM ↦ ?_⟩
  have hρz := hd.massRadiusM_pos hfin (hne z)
  have h2n : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ one_le_two
  have hle : massRadiusM μ z ≤ dist z ζ := (le_mul_of_one_le_left hρz.le h2n).trans hn
  have hdpos : 0 < dist z ζ := hρz.trans_le hle
  refine (h z ζ hle hM).trans (mul_le_mul_of_nonneg_left ?_ hC.le)
  have hv : massRadiusM μ z / dist z ζ ≤ ((2 : ℝ) ^ n)⁻¹ := by
    rw [div_le_iff₀ hdpos, ← div_eq_inv_mul, le_div_iff₀ (by positivity)]
    linarith
  calc (massRadiusM μ z / dist z ζ) ^ α ≤ (((2 : ℝ) ^ n)⁻¹) ^ α :=
        Real.rpow_le_rpow (by positivity) hv hα.le
    _ = ((2 : ℝ) ^ (-α)) ^ n := by
      rw [Real.inv_rpow (by positivity), ← Real.rpow_natCast (2 : ℝ) n,
        ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast ((2 : ℝ) ^ (-α)) n,
        ← Real.rpow_mul (by norm_num), ← Real.rpow_neg (by norm_num)]
      congr 1
      ring

omit [OpensMeasurableSpace X] in
/-- Pointwise bound for the fine part of Lemma 3: the integrand is dominated by a constant on
`ball w ρ(w)` plus a geometric series of indicators of the balls `ball w (min (2^(n+1) ρ(w)) 1)`. -/
private theorem lemma3_fine_pointwise {μ : Measure X}
    (hne : ∀ x : X, ∃ r, 0 < r ∧ 1 ≤ μ (ball x r)) {C θ : ℝ} (hC : 0 < C) (hθ : 0 < θ)
    (hdecay : ∀ (z ζ : X) (n : ℕ), 2 ^ n * massRadiusM μ z ≤ dist z ζ → dist z ζ ≤ 1 →
      massRadiusM μ ζ / dist z ζ ≤ C * θ ^ n)
    (m : ℕ) {δ : ℝ} (hδ : 0 < δ) (w z : X) (hρw : 0 < massRadiusM μ w) (hz : z ∈ ball w 1) :
    ENNReal.ofReal ((massRadiusM μ z / max (dist z w) (δ * massRadiusM μ w)) ^ m) ≤
      (ball w (massRadiusM μ w)).indicator (fun _ ↦ ENNReal.ofReal ((2 / δ) ^ m)) z +
        ∑' n : ℕ, (ball w (min (2 ^ (n + 1) * massRadiusM μ w) 1)).indicator
          (fun _ ↦ ENNReal.ofReal (C ^ m) * ENNReal.ofReal (θ ^ m) ^ n) z := by
  set a : ℝ≥0∞ := ENNReal.ofReal ((2 / δ) ^ m)
  set ρw := massRadiusM μ w
  set r : ℕ → ℝ := fun n ↦ min (2 ^ (n + 1) * ρw) 1
  set g₀ : X → ℝ≥0∞ := (ball w ρw).indicator (fun _ ↦ a) with hg₀def
  set g : ℕ → X → ℝ≥0∞ := fun n ↦
    (ball w (r n)).indicator (fun _ ↦ ENNReal.ofReal (C ^ m) * ENNReal.ofReal (θ ^ m) ^ n)
    with hgdef
  rw [mem_ball] at hz
  have hρz : 0 ≤ massRadiusM μ z := massRadiusM_nonneg μ z
  have hmaxpos : 0 < max (dist z w) (δ * ρw) := lt_max_of_lt_right (by positivity)
  by_cases hdw : dist z w < ρw
  · have hz' : z ∈ ball w ρw := hdw
    have hlip : massRadiusM μ z ≤ ρw + dist z w := by
      have := massRadiusM_le_add_dist hne w z
      rwa [dist_comm] at this
    have hratio : massRadiusM μ z / max (dist z w) (δ * ρw) ≤ 2 / δ := by
      rw [div_le_div_iff₀ hmaxpos hδ]
      have := le_max_right (dist z w) (δ * ρw)
      nlinarith
    calc ENNReal.ofReal ((massRadiusM μ z / max (dist z w) (δ * ρw)) ^ m) ≤ a :=
          ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by positivity) hratio m)
      _ = g₀ z := by simp only [hg₀def, indicator_of_mem hz']
      _ ≤ g₀ z + ∑' n, g n z := le_self_add
  · rw [not_lt] at hdw
    have hdpos : 0 < dist z w := hρw.trans_le hdw
    have hq1 : 1 ≤ dist z w / ρw := (one_le_div hρw).2 hdw
    set L := Real.logb 2 (dist z w / ρw)
    have hL0 : 0 ≤ L := Real.logb_nonneg one_lt_two hq1
    set n := ⌊L⌋₊
    have h2L : (2 : ℝ) ^ L = dist z w / ρw := Real.rpow_logb (by norm_num) (by norm_num)
      (by positivity)
    have hn1 : 2 ^ n * ρw ≤ dist z w := by
      have : (2 : ℝ) ^ n ≤ dist z w / ρw := by
        calc (2 : ℝ) ^ n = 2 ^ (n : ℝ) := (Real.rpow_natCast 2 n).symm
          _ ≤ 2 ^ L := Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.floor_le hL0)
          _ = _ := h2L
      rwa [le_div_iff₀ hρw] at this
    have hn2 : dist z w < 2 ^ (n + 1) * ρw := by
      have : dist z w / ρw < 2 ^ (n + 1) := by
        calc dist z w / ρw = 2 ^ L := h2L.symm
          _ < 2 ^ ((n + 1 : ℕ) : ℝ) := Real.rpow_lt_rpow_of_exponent_lt one_lt_two (by
              push_cast
              exact Nat.lt_floor_add_one L)
          _ = 2 ^ (n + 1) := Real.rpow_natCast 2 (n + 1)
      rwa [div_lt_iff₀ hρw] at this
    have hdec := hdecay w z n (by rw [dist_comm]; exact hn1) (by rw [dist_comm]; exact hz.le)
    rw [dist_comm] at hdec
    have hratio : massRadiusM μ z / max (dist z w) (δ * ρw) ≤ C * θ ^ n :=
      (div_le_div_of_nonneg_left hρz hdpos (le_max_left _ _)).trans hdec
    have hz' : z ∈ ball w (r n) := by
      rw [mem_ball]
      exact lt_min hn2 hz
    calc ENNReal.ofReal ((massRadiusM μ z / max (dist z w) (δ * ρw)) ^ m)
        ≤ ENNReal.ofReal ((C * θ ^ n) ^ m) :=
          ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by positivity) hratio m)
      _ = ENNReal.ofReal (C ^ m) * ENNReal.ofReal (θ ^ m) ^ n := by
          rw [mul_pow, ← pow_mul, mul_comm n m, pow_mul, ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_pow (pow_nonneg hθ.le m) n]
      _ = g n z := by simp only [hgdef, indicator_of_mem hz']
      _ ≤ ∑' k, g k z := le_tsum (f := fun k ↦ g k z) n
      _ ≤ g₀ z + ∑' k, g k z := le_add_self

/-- Fine part of Lemma 3: integration over `ball w 1`, uniformly in `w`. -/
theorem IsLocDoublingM.lemma3_fine [BallGeometry X] {μ : Measure X} (hd : IsLocDoublingM μ)
    (hfin : ∀ x : X, ∀ r : ℝ, μ (ball x r) < ∞)
    (hm : ∃ R : ℝ, 0 < R ∧ ∀ x : X, 1 ≤ μ (ball x R)) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ δ : ℝ, 0 < δ → ∃ CF : ℝ≥0∞, CF ≠ ∞ ∧ ∀ w : X,
      ∫⁻ z in ball w 1,
        ENNReal.ofReal ((massRadiusM μ z / max (dist z w) (δ * massRadiusM μ w)) ^ m) ∂μ
          ≤ CF := by
  obtain ⟨C, θ, hC, hθ, hθ1, hdecay⟩ := hd.decay_aux hfin hm 1
  obtain ⟨D, hD1, hD⟩ := hd.measure_ball_le_pow 1
  obtain ⟨R, hR, hRm⟩ := hm
  have hne : ∀ x : X, ∃ r, 0 < r ∧ 1 ≤ μ (ball x r) := fun x ↦ ⟨R, hR, hRm x⟩
  have hDpos : (0 : ℝ) < D := by linarith
  obtain ⟨m₀, hm₀⟩ := exists_pow_lt_of_lt_one (by positivity : (0 : ℝ) < 1 / D) hθ1
  refine ⟨m₀, fun m hm δ hδ ↦ ?_⟩
  have hθm : θ ^ m * D < 1 := by
    have h1 : θ ^ m ≤ θ ^ m₀ := pow_le_pow_of_le_one hθ.le hθ1.le hm
    have h2 : θ ^ m₀ * D < 1 := by rwa [lt_div_iff₀ hDpos] at hm₀
    nlinarith
  set q : ℝ≥0∞ := ENNReal.ofReal (θ ^ m) * D with hqdef
  have hq : q < 1 := by
    rw [hqdef, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_lt_one.2 hθm
  set a : ℝ≥0∞ := ENNReal.ofReal ((2 / δ) ^ m)
  set b : ℝ≥0∞ := ENNReal.ofReal (C ^ m) * (D : ℝ≥0∞) ^ 2 with hbdef
  refine ⟨a + b * (1 - q)⁻¹, ?_, fun w ↦ ?_⟩
  · exact ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.mul_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top))
      (ENNReal.inv_ne_top.2 (tsub_pos_iff_lt.2 hq).ne')⟩
  set ρw := massRadiusM μ w
  have hρw : 0 < ρw := hd.massRadiusM_pos hfin (hne w)
  set r : ℕ → ℝ := fun n ↦ min (2 ^ (n + 1) * ρw) 1
  set g₀ : X → ℝ≥0∞ := (ball w ρw).indicator (fun _ ↦ a)
  set g : ℕ → X → ℝ≥0∞ := fun n ↦
    (ball w (r n)).indicator (fun _ ↦ ENNReal.ofReal (C ^ m) * ENNReal.ofReal (θ ^ m) ^ n)
  have hpt : ∀ z ∈ ball w 1,
      ENNReal.ofReal ((massRadiusM μ z / max (dist z w) (δ * ρw)) ^ m) ≤
        g₀ z + ∑' n, g n z := fun z hz ↦
    lemma3_fine_pointwise hne hC hθ hdecay m hδ w z hρw hz
  have hmass : ∀ n : ℕ, μ (ball w (r n)) ≤ (D : ℝ≥0∞) ^ (n + 2) := by
    intro n
    have h := hD w w (r n) ρw (n + 1) hρw (min_le_right _ _)
      (by rw [dist_self]; exact le_min (by positivity) zero_le_one) (min_le_left _ _)
    calc μ (ball w (r n)) ≤ (D : ℝ≥0∞) ^ (n + 1 + 1) * μ (ball w ρw) := h
      _ ≤ (D : ℝ≥0∞) ^ (n + 1 + 1) * 1 := by
          gcongr
          exact measure_ball_massRadiusM_le_one μ w
      _ = (D : ℝ≥0∞) ^ (n + 2) := by rw [mul_one]
  calc ∫⁻ z in ball w 1, ENNReal.ofReal ((massRadiusM μ z / max (dist z w) (δ * ρw)) ^ m) ∂μ
      ≤ ∫⁻ z in ball w 1, (g₀ z + ∑' n, g n z) ∂μ := setLIntegral_mono' measurableSet_ball hpt
    _ ≤ ∫⁻ z, (g₀ z + ∑' n, g n z) ∂μ := setLIntegral_le_lintegral _ _
    _ = ∫⁻ z, g₀ z ∂μ + ∑' n, ∫⁻ z, g n z ∂μ := by
        rw [lintegral_add_left (measurable_const.indicator measurableSet_ball),
          lintegral_tsum fun n ↦ (measurable_const.indicator measurableSet_ball).aemeasurable]
    _ ≤ a * μ (ball w ρw) +
          ∑' n, (ENNReal.ofReal (C ^ m) * ENNReal.ofReal (θ ^ m) ^ n) * μ (ball w (r n)) := by
        gcongr with n
        · exact lintegral_indicator_const_le _ _
        · exact lintegral_indicator_const_le _ _
    _ ≤ a * 1 + ∑' n, (ENNReal.ofReal (C ^ m) * ENNReal.ofReal (θ ^ m) ^ n) *
          (D : ℝ≥0∞) ^ (n + 2) := by
        gcongr with n
        · exact measure_ball_massRadiusM_le_one μ w
        · exact hmass n
    _ = a + b * (1 - q)⁻¹ := by
        rw [mul_one, ← ENNReal.tsum_geometric, ← ENNReal.tsum_mul_left]
        congr 1
        congr 1
        ext n
        rw [hbdef, hqdef]
        ring

/-- **Lemma 3**, truncated form (contains the paper's statement on `δρ(w) ≤ d < R₁`). -/
theorem IsLocDoublingM.lemma3 [BallGeometry X]
    {μ : Measure X} (hd : IsLocDoublingM μ) (hfin : ∀ x : X, ∀ r : ℝ, μ (ball x r) < ∞)
    (hm : ∃ R : ℝ, 0 < R ∧ ∀ x : X, 1 ≤ μ (ball x R)) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ δ R₁ : ℝ, 0 < δ → ∃ C : ℝ≥0, ∀ w : X,
      ∫⁻ z in ball w R₁,
        ENNReal.ofReal ((massRadiusM μ z / max (dist z w) (δ * massRadiusM μ w)) ^ m) ∂μ ≤ C := by
  obtain ⟨m₀, hfine⟩ := hd.lemma3_fine hfin hm
  obtain ⟨R, hR, hRm⟩ := hm
  have hne : ∀ x : X, ∃ r, 0 < r ∧ 1 ≤ μ (ball x r) := fun x ↦ ⟨R, hR, hRm x⟩
  have hρmeas : Measurable (massRadiusM μ) :=
    (lipschitzWith_massRadiusM hne).continuous.measurable
  refine ⟨m₀, fun m hm δ R₁ hδ ↦ ?_⟩
  have hFmeas' : ∀ (y : X) (c : ℝ), Measurable fun z ↦
      ENNReal.ofReal ((massRadiusM μ z / max (dist z y) (c * massRadiusM μ y)) ^ m) := by
    intro y c
    exact ENNReal.measurable_ofReal.comp ((hρmeas.div
      ((continuous_id.dist continuous_const).measurable.max measurable_const)).pow_const _)
  obtain ⟨CF, hCF, hCFw⟩ := hfine m hm δ hδ
  obtain ⟨CF', hCF', hCFw'⟩ := hfine m hm (1 / R) (by positivity)
  obtain ⟨K, hK⟩ := BallGeometry.covering (X := X) R₁ 1 one_pos
  have hfinC : CF + K * CF' ≠ ∞ :=
    ENNReal.add_ne_top.2 ⟨hCF, ENNReal.mul_ne_top (ENNReal.natCast_ne_top K) hCF'⟩
  refine ⟨(CF + K * CF').toNNReal, fun w ↦ ?_⟩
  rw [ENNReal.coe_toNNReal hfinC]
  obtain ⟨s, hs, hcov⟩ := hK w
  have hpt : ∀ z ∈ ball w R₁,
      ENNReal.ofReal ((massRadiusM μ z / max (dist z w) (δ * massRadiusM μ w)) ^ m) ≤
        (ball w 1).indicator (fun z ↦
          ENNReal.ofReal ((massRadiusM μ z / max (dist z w) (δ * massRadiusM μ w)) ^ m)) z +
        ∑ y ∈ s, (ball y 1).indicator (fun z ↦
          ENNReal.ofReal ((massRadiusM μ z / max (dist z y) (1 / R * massRadiusM μ y)) ^ m)) z := by
    intro z hz
    by_cases hz1 : z ∈ ball w 1
    · rw [indicator_of_mem hz1]
      exact le_self_add
    · rw [mem_ball, not_lt] at hz1
      obtain ⟨y, hy, hzy⟩ := mem_iUnion₂.1 (hcov hz)
      have hρz := massRadiusM_nonneg μ z
      have hρy : massRadiusM μ y ≤ R := massRadiusM_le hR (hRm y)
      have hρypos : 0 < massRadiusM μ y := hd.massRadiusM_pos hfin (hne y)
      have hM1 : 1 ≤ max (dist z w) (δ * massRadiusM μ w) := hz1.trans (le_max_left _ _)
      have hM2pos : 0 < max (dist z y) (1 / R * massRadiusM μ y) :=
        lt_max_of_lt_right (by positivity)
      have hM2 : max (dist z y) (1 / R * massRadiusM μ y) ≤ 1 := by
        refine max_le (mem_ball.1 hzy).le ?_
        rw [div_mul_eq_mul_div, one_mul, div_le_one hR]
        exact hρy
      have hratio : massRadiusM μ z / max (dist z w) (δ * massRadiusM μ w) ≤
          massRadiusM μ z / max (dist z y) (1 / R * massRadiusM μ y) :=
        div_le_div_of_nonneg_left hρz hM2pos (hM2.trans hM1)
      calc ENNReal.ofReal ((massRadiusM μ z / max (dist z w) (δ * massRadiusM μ w)) ^ m)
          ≤ ENNReal.ofReal ((massRadiusM μ z / max (dist z y) (1 / R * massRadiusM μ y)) ^ m) :=
            ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by positivity) hratio m)
        _ = (ball y 1).indicator (fun z ↦
              ENNReal.ofReal ((massRadiusM μ z / max (dist z y) (1 / R * massRadiusM μ y)) ^ m))
              z := by rw [indicator_of_mem hzy]
        _ ≤ ∑ y ∈ s, (ball y 1).indicator (fun z ↦
              ENNReal.ofReal ((massRadiusM μ z / max (dist z y) (1 / R * massRadiusM μ y)) ^ m))
              z :=
            Finset.single_le_sum (f := fun y ↦ (ball y 1).indicator (fun z ↦
              ENNReal.ofReal ((massRadiusM μ z / max (dist z y) (1 / R * massRadiusM μ y)) ^ m))
              z) (fun _ _ ↦ zero_le) hy
        _ ≤ _ := le_add_self
  calc ∫⁻ z in ball w R₁,
        ENNReal.ofReal ((massRadiusM μ z / max (dist z w) (δ * massRadiusM μ w)) ^ m) ∂μ
      ≤ ∫⁻ z in ball w R₁, ((ball w 1).indicator (fun z ↦
          ENNReal.ofReal ((massRadiusM μ z / max (dist z w) (δ * massRadiusM μ w)) ^ m)) z +
        ∑ y ∈ s, (ball y 1).indicator (fun z ↦
          ENNReal.ofReal ((massRadiusM μ z / max (dist z y) (1 / R * massRadiusM μ y)) ^ m)) z)
          ∂μ := setLIntegral_mono' measurableSet_ball hpt
    _ ≤ ∫⁻ z, ((ball w 1).indicator (fun z ↦
          ENNReal.ofReal ((massRadiusM μ z / max (dist z w) (δ * massRadiusM μ w)) ^ m)) z +
        ∑ y ∈ s, (ball y 1).indicator (fun z ↦
          ENNReal.ofReal ((massRadiusM μ z / max (dist z y) (1 / R * massRadiusM μ y)) ^ m)) z)
          ∂μ := setLIntegral_le_lintegral _ _
    _ = ∫⁻ z in ball w 1,
          ENNReal.ofReal ((massRadiusM μ z / max (dist z w) (δ * massRadiusM μ w)) ^ m) ∂μ +
        ∑ y ∈ s, ∫⁻ z in ball y 1,
          ENNReal.ofReal ((massRadiusM μ z / max (dist z y) (1 / R * massRadiusM μ y)) ^ m)
            ∂μ := by
        rw [lintegral_add_left ((hFmeas' w δ).indicator measurableSet_ball),
          lintegral_finsetSum _ (fun y _ ↦ (hFmeas' y _).indicator measurableSet_ball),
          lintegral_indicator measurableSet_ball]
        congr 1
        exact Finset.sum_congr rfl fun y _ ↦ lintegral_indicator measurableSet_ball _
    _ ≤ CF + ∑ _y ∈ s, CF' := by
        gcongr with y
        · exact hCFw w
        · exact hCFw' y
    _ = CF + s.card * CF' := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ CF + K * CF' := by gcongr

/-- **Lemma 3** as printed (region `δρ(w) ≤ d(z,w) < R₁`). -/
theorem IsLocDoublingM.lemma3_paper [BallGeometry X]
    {μ : Measure X} (hd : IsLocDoublingM μ) (hfin : ∀ x : X, ∀ r : ℝ, μ (ball x r) < ∞)
    (hm : ∃ R : ℝ, 0 < R ∧ ∀ x : X, 1 ≤ μ (ball x R)) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ δ R₁ : ℝ, 0 < δ → ∃ C : ℝ≥0, ∀ w : X,
      ∫⁻ z in {z | δ * massRadiusM μ w ≤ dist z w ∧ dist z w < R₁},
        ENNReal.ofReal ((massRadiusM μ z / dist z w) ^ m) ∂μ ≤ C := by
  obtain ⟨m₀, h⟩ := hd.lemma3 hfin hm
  refine ⟨m₀, fun m hm δ R₁ hδ ↦ ?_⟩
  obtain ⟨C, hC⟩ := h m hm δ R₁ hδ
  refine ⟨C, fun w ↦ ?_⟩
  have hcont : Continuous fun z ↦ dist z w := continuous_id.dist continuous_const
  have hS : MeasurableSet {z | δ * massRadiusM μ w ≤ dist z w ∧ dist z w < R₁} :=
    (measurableSet_le measurable_const hcont.measurable).inter
      (measurableSet_lt hcont.measurable measurable_const)
  calc ∫⁻ z in {z | δ * massRadiusM μ w ≤ dist z w ∧ dist z w < R₁},
        ENNReal.ofReal ((massRadiusM μ z / dist z w) ^ m) ∂μ
      = ∫⁻ z in {z | δ * massRadiusM μ w ≤ dist z w ∧ dist z w < R₁},
          ENNReal.ofReal ((massRadiusM μ z / max (dist z w) (δ * massRadiusM μ w)) ^ m) ∂μ := by
        refine setLIntegral_congr_fun hS fun z hz ↦ ?_
        rw [max_eq_left hz.1]
    _ ≤ ∫⁻ z in ball w R₁,
          ENNReal.ofReal ((massRadiusM μ z / max (dist z w) (δ * massRadiusM μ w)) ^ m) ∂μ :=
        lintegral_mono_set fun z hz ↦ mem_ball.2 hz.2
    _ ≤ C := hC w

omit [MeasurableSpace X] [OpensMeasurableSpace X] in
/-- Pointwise dyadic bound behind [Chr91, Lemma 2.3]. -/
theorem ofReal_log_le_tsum_indicator (x y : X) {R : ℝ} (hR : 0 < R) :
    ENNReal.ofReal (Real.log (R / dist x y)) ≤
      ∑' k : ℕ, (ball x (R / 2 ^ k)).indicator (fun _ ↦ ENNReal.ofReal (Real.log 2)) y := by
  by_cases hd0 : dist x y = 0
  · rw [hd0, div_zero, Real.log_zero, ENNReal.ofReal_zero]
    exact zero_le
  have hdpos : 0 < dist x y := lt_of_le_of_ne dist_nonneg (Ne.symm hd0)
  by_cases hdR : R ≤ dist x y
  · rw [ENNReal.ofReal_of_nonpos (Real.log_nonpos (by positivity) ((div_le_one hdpos).2 hdR))]
    exact zero_le
  rw [not_le] at hdR
  set L := Real.logb 2 (R / dist x y) with hLdef
  set n := ⌈L⌉₊
  have hmem : ∀ k < n, y ∈ ball x (R / 2 ^ k) := by
    intro k hk
    rw [mem_ball, dist_comm]
    have hkL : (k : ℝ) < L := Nat.lt_ceil.1 hk
    have h2 : (2 : ℝ) ^ k < R / dist x y := by
      calc (2 : ℝ) ^ k = 2 ^ (k : ℝ) := (Real.rpow_natCast 2 k).symm
        _ < 2 ^ L := Real.rpow_lt_rpow_of_exponent_lt one_lt_two hkL
        _ = R / dist x y := Real.rpow_logb (by norm_num) (by norm_num) (by positivity)
    rw [lt_div_iff₀ hdpos] at h2
    rw [lt_div_iff₀ (by positivity)]
    linarith
  calc ENNReal.ofReal (Real.log (R / dist x y)) = ENNReal.ofReal (L * Real.log 2) := by
        rw [hLdef, Real.logb, div_mul_cancel₀ _ (Real.log_pos one_lt_two).ne']
    _ ≤ ENNReal.ofReal (n * Real.log 2) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (Nat.le_ceil L)
          (Real.log_nonneg one_le_two))
    _ = ∑ k ∈ Finset.range n,
          (ball x (R / 2 ^ k)).indicator (fun _ ↦ ENNReal.ofReal (Real.log 2)) y := by
        rw [Finset.sum_congr rfl (fun k hk ↦ indicator_of_mem (hmem k (Finset.mem_range.1 hk)) _),
          Finset.sum_const, Finset.card_range, nsmul_eq_mul,
          ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    _ ≤ ∑' k : ℕ, (ball x (R / 2 ^ k)).indicator (fun _ ↦ ENNReal.ofReal (Real.log 2)) y :=
        sum_le_tsum _

/-- **[Chr91, Lemma 2.3]**. -/
theorem IsLocDoublingM.christ_lemma23 [BallGeometry X] {μ : Measure X}
    (hd : IsLocDoublingM μ) (R₁ : ℝ) :
    ∃ C : ℝ≥0, ∀ (x : X) (R : ℝ), 0 < R → R ≤ R₁ →
      ∫⁻ y in ball x R, ENNReal.ofReal (Real.log (R / dist x y)) ∂μ ≤ C * μ (ball x R) := by
  obtain ⟨η, hη, hη'⟩ := hd.reverse_doubling R₁
  set q : ℝ≥0∞ := (1 + (η : ℝ≥0∞))⁻¹
  have h1η0 : (1 + (η : ℝ≥0∞)) ≠ 0 := (lt_of_lt_of_le one_pos le_self_add).ne'
  have h1ηt : (1 + (η : ℝ≥0∞)) ≠ ∞ := by simp
  have hq1 : q < 1 := by
    refine ENNReal.inv_lt_one.mpr ?_
    have : (0 : ℝ≥0∞) < η := by exact_mod_cast hη
    exact ENNReal.lt_add_right ENNReal.one_ne_top this.ne'
  set c : ℝ≥0∞ := ENNReal.ofReal (Real.log 2)
  have hCne : c * (1 - q)⁻¹ ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.inv_ne_top.2 (tsub_pos_iff_lt.2 hq1).ne')
  refine ⟨(c * (1 - q)⁻¹).toNNReal, fun x R hR hRR₁ ↦ ?_⟩
  rw [ENNReal.coe_toNNReal hCne]
  have hstep : ∀ k : ℕ, μ (ball x (R / 2 ^ k)) ≤ q ^ k * μ (ball x R) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have h := hη' x (R / 2 ^ (k + 1)) (by positivity)
        ((div_le_self hR.le (one_le_pow₀ one_le_two)).trans hRR₁)
      rw [show 2 * (R / 2 ^ (k + 1)) = R / 2 ^ k by rw [pow_succ]; field_simp] at h
      have h' : μ (ball x (R / 2 ^ (k + 1))) ≤ q * μ (ball x (R / 2 ^ k)) :=
        (ENNReal.mul_le_iff_le_inv h1η0 h1ηt).mp h
      calc μ (ball x (R / 2 ^ (k + 1))) ≤ q * μ (ball x (R / 2 ^ k)) := h'
        _ ≤ q * (q ^ k * μ (ball x R)) := by gcongr
        _ = q ^ (k + 1) * μ (ball x R) := by ring
  calc ∫⁻ y in ball x R, ENNReal.ofReal (Real.log (R / dist x y)) ∂μ
      ≤ ∫⁻ y in ball x R, ∑' k : ℕ, (ball x (R / 2 ^ k)).indicator (fun _ ↦ c) y ∂μ :=
        lintegral_mono fun y ↦ ofReal_log_le_tsum_indicator x y hR
    _ ≤ ∫⁻ y, ∑' k : ℕ, (ball x (R / 2 ^ k)).indicator (fun _ ↦ c) y ∂μ :=
        setLIntegral_le_lintegral _ _
    _ = ∑' k : ℕ, ∫⁻ y, (ball x (R / 2 ^ k)).indicator (fun _ ↦ c) y ∂μ :=
        lintegral_tsum fun k ↦ (measurable_const.indicator measurableSet_ball).aemeasurable
    _ ≤ ∑' k : ℕ, c * μ (ball x (R / 2 ^ k)) :=
        tsum_le_tsum fun k ↦ lintegral_indicator_const_le _ _
    _ ≤ ∑' k : ℕ, c * (q ^ k * μ (ball x R)) := tsum_le_tsum fun k ↦ by
        gcongr
        exact hstep k
    _ = c * (1 - q)⁻¹ * μ (ball x R) := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, ENNReal.tsum_geometric]
        ring

theorem IsLocDoublingM.integrableOn_log_dist [BallGeometry X] {μ : Measure X}
    (hd : IsLocDoublingM μ) (hfin : ∀ x : X, ∀ r : ℝ, μ (ball x r) < ∞) (x : X) (R : ℝ) :
    IntegrableOn (fun y ↦ Real.log (dist x y)) (ball x R) μ := by
  by_cases hR : R ≤ 0
  · rw [ball_eq_empty.2 hR]
    exact integrableOn_empty
  rw [not_le] at hR
  obtain ⟨C, hC⟩ := hd.christ_lemma23 R
  have hmeas : Measurable fun y ↦ Real.log (dist x y) :=
    Real.measurable_log.comp (continuous_const.dist continuous_id).measurable
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  change ∫⁻ y in ball x R, ‖Real.log (dist x y)‖ₑ ∂μ < ∞
  have hpt : ∀ y ∈ ball x R, ‖Real.log (dist x y)‖ₑ ≤
      ENNReal.ofReal (Real.log (R / dist x y)) + ENNReal.ofReal |Real.log R| := by
    intro y hy
    rw [mem_ball, dist_comm] at hy
    by_cases hd0 : dist x y = 0
    · rw [hd0, Real.log_zero, eNorm_zero]
      exact zero_le
    have hdpos : 0 < dist x y := lt_of_le_of_ne dist_nonneg (Ne.symm hd0)
    have hlogq : 0 ≤ Real.log (R / dist x y) := Real.log_nonneg ((one_le_div hdpos).2 hy.le)
    rw [Real.eNorm_eq_ofReal_abs, ← ENNReal.ofReal_add hlogq (abs_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [Real.log_div hR.ne' hdpos.ne'] at hlogq ⊢
    rw [abs_le]
    constructor <;> linarith [le_abs_self (Real.log R), neg_abs_le (Real.log R)]
  calc ∫⁻ y in ball x R, ‖Real.log (dist x y)‖ₑ ∂μ
      ≤ ∫⁻ y in ball x R, (ENNReal.ofReal (Real.log (R / dist x y)) +
          ENNReal.ofReal |Real.log R|) ∂μ := setLIntegral_mono' measurableSet_ball hpt
    _ = ∫⁻ y in ball x R, ENNReal.ofReal (Real.log (R / dist x y)) ∂μ +
          ENNReal.ofReal |Real.log R| * μ (ball x R) := by
        rw [lintegral_add_right _ measurable_const, setLIntegral_const]
    _ ≤ C * μ (ball x R) + ENNReal.ofReal |Real.log R| * μ (ball x R) := by
        gcongr
        exact hC x R hR le_rfl
    _ < ∞ := ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.coe_lt_top (hfin x R),
        ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hfin x R)⟩

/-- **Growth**: balls of a fixed large radius have mass `> p`. No doubling needed. -/
theorem exists_radius_lt_measure_ball [BallGeometry X] {μ : Measure X}
    (hm : ∃ R : ℝ, 0 < R ∧ ∀ x : X, 1 ≤ μ (ball x R)) (p : ℝ≥0) :
    ∃ r : ℝ, 0 < r ∧ ∀ x : X, (p : ℝ≥0∞) < μ (ball x r) := by
  obtain ⟨R, hR, hRm⟩ := hm
  set k : ℕ := ⌊p⌋₊ + 1 with hkdef
  refine ⟨2 * k * R, by positivity, fun x ↦ ?_⟩
  have hy : ∀ i : ℕ, ∃ y, dist x y = 2 * i * R := fun i ↦ exists_dist_eq x (by positivity)
  choose y hy using hy
  have key : ∀ i j : ℕ, i < j → 2 * R ≤ dist (y i) (y j) := by
    intro i j hij
    have h1 := dist_triangle x (y i) (y j)
    rw [hy, hy] at h1
    have : (i : ℝ) + 1 ≤ j := by exact_mod_cast hij
    nlinarith
  have hdisj : Set.PairwiseDisjoint (↑(Finset.range k)) (fun i ↦ ball (y i) R) := by
    intro i _ j _ hij
    rw [Function.onFun, Set.disjoint_left]
    intro z hz1 hz2
    rw [mem_ball] at hz1 hz2
    have h1 := dist_triangle (y i) z (y j)
    rw [dist_comm (y i) z] at h1
    rcases lt_or_gt_of_ne hij with h | h
    · linarith [key i j h]
    · have := key j i h
      rw [dist_comm] at this
      linarith
  have hsub : ⋃ i ∈ Finset.range k, ball (y i) R ⊆ ball x (2 * k * R) := by
    intro z hz
    obtain ⟨i, hi, hz⟩ := mem_iUnion₂.1 hz
    rw [Finset.mem_range] at hi
    rw [mem_ball] at hz ⊢
    have h1 := dist_triangle z (y i) x
    rw [dist_comm (y i) x, hy] at h1
    have : (i : ℝ) + 1 ≤ k := by exact_mod_cast hi
    nlinarith
  have hpk : (p : ℝ≥0∞) < k := by
    have : p < (k : ℝ≥0) := by
      rw [hkdef]
      push_cast
      exact Nat.lt_floor_add_one p
    exact_mod_cast this
  calc (p : ℝ≥0∞) < k := hpk
    _ = ∑ _i ∈ Finset.range k, (1 : ℝ≥0∞) := by simp
    _ ≤ ∑ i ∈ Finset.range k, μ (ball (y i) R) := Finset.sum_le_sum fun i _ ↦ hRm (y i)
    _ = μ (⋃ i ∈ Finset.range k, ball (y i) R) :=
        (measure_biUnion_finset hdisj fun i _ ↦ measurableSet_ball).symm
    _ ≤ μ (ball x (2 * k * R)) := measure_mono hsub

omit [OpensMeasurableSpace X] in
theorem IsLocDoublingM.smul {μ : Measure X} (hd : IsLocDoublingM μ) (c : ℝ≥0∞) :
    IsLocDoublingM (c • μ) := by
  obtain ⟨C, hC⟩ := hd
  refine ⟨C, fun x r hr h2r ↦ ?_⟩
  simp only [smul_apply, smul_eq_mul]
  calc c * μ (ball x (2 * r)) ≤ c * (C * μ (ball x r)) := by gcongr; exact hC x r hr h2r
    _ = C * (c * μ (ball x r)) := by ring

/-- Mass radius for `N⁻¹ μ` versus `μ` (reduction of mass-`N` pieces to mass-`1` pieces). -/
theorem IsLocDoublingM.massRadiusM_inv_smul [BallGeometry X] {μ : Measure X}
    (hd : IsLocDoublingM μ) (hfin : ∀ x : X, ∀ r : ℝ, μ (ball x r) < ∞)
    (hm : ∃ R : ℝ, 0 < R ∧ ∀ x : X, 1 ≤ μ (ball x R)) (N : ℕ) (hN : 1 ≤ N) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ x : X, massRadiusM μ x ≤ massRadiusM ((N : ℝ≥0∞)⁻¹ • μ) x ∧
      massRadiusM ((N : ℝ≥0∞)⁻¹ • μ) x ≤ C * massRadiusM μ x := by
  obtain ⟨rN, hrN, hrNm⟩ := exists_radius_lt_measure_ball hm (N : ℝ≥0)
  obtain ⟨R, hR, hRm⟩ := hm
  obtain ⟨c, δ, hc, hδ, hlow⟩ := hd.rpow_le_measure_ball rN
  set C₀ := max 1 (((N : ℝ) / c) ^ (1 / δ))
  have hC₀1 : 1 ≤ C₀ := le_max_left _ _
  refine ⟨2 * C₀, by linarith, fun x ↦ ?_⟩
  have hN0 : (N : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hNt : (N : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top N
  have hiff : ∀ s : Set X, 1 ≤ ((N : ℝ≥0∞)⁻¹ • μ) s ↔ (N : ℝ≥0∞) ≤ μ s := by
    intro s
    rw [smul_apply, smul_eq_mul, ← ENNReal.mul_le_iff_le_inv hN0 hNt, mul_one]
  have hNnn : ((N : ℝ≥0) : ℝ≥0∞) = (N : ℝ≥0∞) := by simp
  have hSν : ∃ r, 0 < r ∧ 1 ≤ ((N : ℝ≥0∞)⁻¹ • μ) (ball x r) :=
    ⟨rN, hrN, (hiff _).2 (by rw [← hNnn]; exact (hrNm x).le)⟩
  have hne : ∃ r, 0 < r ∧ 1 ≤ μ (ball x r) := ⟨R, hR, hRm x⟩
  have hρ := hd.massRadiusM_pos hfin hne
  constructor
  · refine le_csInf hSν ?_
    rintro r ⟨hr, hr1⟩
    refine massRadiusM_le hr ?_
    have h1 : (1 : ℝ≥0∞) ≤ N := by exact_mod_cast hN
    exact h1.trans ((hiff _).1 hr1)
  · set ρ := massRadiusM μ x
    by_cases hcase : 2 * C₀ * ρ ≤ rN
    · refine massRadiusM_le (by positivity) ((hiff _).2 ?_)
      have h2 : 1 ≤ μ (ball x (2 * ρ)) := one_le_measure_ball_of_massRadiusM_lt hne (by linarith)
      have hL := hlow x x (2 * C₀ * ρ) (2 * ρ) (by positivity) (by nlinarith) hcase
        (by rw [dist_self]; positivity)
      have hratio : 2 * C₀ * ρ / (2 * ρ) = C₀ := by field_simp
      rw [hratio] at hL
      have hreal : (N : ℝ) ≤ c * C₀ ^ δ := by
        have h3 : ((N : ℝ) / c) ^ (1 / δ) ≤ C₀ := le_max_right _ _
        have h4 : (((N : ℝ) / c) ^ (1 / δ)) ^ δ ≤ C₀ ^ δ :=
          Real.rpow_le_rpow (by positivity) h3 hδ.le
        rw [← Real.rpow_mul (by positivity), one_div_mul_cancel hδ.ne', Real.rpow_one] at h4
        rw [div_le_iff₀ hc] at h4
        linarith
      calc (N : ℝ≥0∞) = ENNReal.ofReal N := (ENNReal.ofReal_natCast N).symm
        _ ≤ ENNReal.ofReal (c * C₀ ^ δ) := ENNReal.ofReal_le_ofReal hreal
        _ ≤ ENNReal.ofReal (c * C₀ ^ δ) * μ (ball x (2 * ρ)) := le_mul_of_one_le_right' h2
        _ ≤ μ (ball x (2 * C₀ * ρ)) := hL
    · rw [not_le] at hcase
      have h1 : massRadiusM ((N : ℝ≥0∞)⁻¹ • μ) x ≤ rN :=
        massRadiusM_le hrN ((hiff _).2 (by rw [← hNnn]; exact (hrNm x).le))
      linarith

/-- **Decay of `ρ(ζ)/d(z,ζ)`** (coordinator addition (1)), power form. -/
theorem IsLocDoublingM.massRadiusM_div_dist_le [BallGeometry X] {μ : Measure X}
    (hd : IsLocDoublingM μ) (hfin : ∀ x : X, ∀ r : ℝ, μ (ball x r) < ∞)
    (hm : ∃ R : ℝ, 0 < R ∧ ∀ x : X, 1 ≤ μ (ball x R)) (M₀ : ℝ) :
    ∃ C α : ℝ, 0 < C ∧ 0 < α ∧ α ≤ 1 ∧ ∀ z ζ : X, massRadiusM μ z ≤ dist z ζ → dist z ζ ≤ M₀ →
      massRadiusM μ ζ / dist z ζ ≤ C * (massRadiusM μ z / dist z ζ) ^ α :=
  hd.massRadiusM_div_dist_le_aux hfin hm M₀

/-- **Decay**, geometric form: `d(z,ζ) ≥ 2ⁿ ρ(z)`, `d ≤ M₀` ⟹ `ρ(ζ)/d(z,ζ) ≤ C θⁿ`. -/
theorem IsLocDoublingM.decay [BallGeometry X] {μ : Measure X}
    (hd : IsLocDoublingM μ) (hfin : ∀ x : X, ∀ r : ℝ, μ (ball x r) < ∞)
    (hm : ∃ R : ℝ, 0 < R ∧ ∀ x : X, 1 ≤ μ (ball x R)) (M₀ : ℝ) :
    ∃ C θ : ℝ, 0 < C ∧ 0 < θ ∧ θ < 1 ∧ ∀ (z ζ : X) (n : ℕ),
      2 ^ n * massRadiusM μ z ≤ dist z ζ → dist z ζ ≤ M₀ →
        massRadiusM μ ζ / dist z ζ ≤ C * θ ^ n :=
  hd.decay_aux hfin hm M₀

omit [MeasurableSpace X] [OpensMeasurableSpace X] in
/-- Disjoint open balls of radius `a` in a `BallGeometry` space have `2a`-separated centres. -/
theorem le_dist_of_disjoint_ball [BallGeometry X] {x y : X} {a : ℝ}
    (h : Disjoint (ball x a) (ball y a)) : 2 * a ≤ dist x y := by
  by_contra hlt
  rw [not_le] at hlt
  have h0 := dist_nonneg (x := x) (y := y)
  obtain ⟨m, hm1, hm2⟩ := BallGeometry.exists_between x y (dist x y / 2) (by positivity)
    (by linarith)
  refine Set.disjoint_left.1 h (show m ∈ ball x a by rw [mem_ball, dist_comm]; linarith)
    (show m ∈ ball y a by rw [mem_ball]; linarith)

omit [MeasurableSpace X] [OpensMeasurableSpace X] in
/-- **Bounded count** (coordinator addition (2)), abstract form: disjoint sets containing a ball
of radius `a` and contained in a ball of radius `D` around the same centre; at most `M` of them
meet a ball of radius `b`. -/
theorem BallGeometry.encard_le_of_disjoint [BallGeometry X] (a b D : ℝ) (ha : 0 < a) :
    ∃ M : ℕ, ∀ {ι : Type*} (E : ι → Set X) (c : ι → X) (z : X),
      Pairwise (Function.onFun Disjoint E) →
      (∀ i, ball (c i) a ⊆ E i) → (∀ i, E i ⊆ ball (c i) D) →
        {i | (E i ∩ ball z b).Nonempty}.encard ≤ M := by
  obtain ⟨K, hK⟩ := BallGeometry.covering (X := X) (b + D) a ha
  refine ⟨K, fun {ι} E c z hdisj hin hout ↦ ?_⟩
  obtain ⟨s, hs, hcov⟩ := hK z
  set I := {i | (E i ∩ ball z b).Nonempty}
  have hcI : ∀ i ∈ I, c i ∈ ball z (b + D) := by
    rintro i ⟨p, hp1, hp2⟩
    have h1 := hout i hp1
    rw [mem_ball] at h1 hp2 ⊢
    have := dist_triangle (c i) p z
    rw [dist_comm (c i) p] at this
    linarith
  have hch : ∀ i ∈ I, ∃ y ∈ s, c i ∈ ball y a := fun i hi ↦ by
    simpa using hcov (hcI i hi)
  have : Nonempty X := ⟨z⟩
  choose! g hgs hgc using hch
  have hinj : InjOn g I := by
    intro i hi j hj hij
    by_contra hne
    have hsep := le_dist_of_disjoint_ball
      ((show Disjoint (E i) (E j) from hdisj hne).mono (hin i) (hin j))
    have h1 := hgc i hi
    have h2 := hgc j hj
    rw [hij] at h1
    rw [mem_ball] at h1 h2
    have := dist_triangle (c i) (g j) (c j)
    rw [dist_comm (g j) (c j)] at this
    linarith
  have hmaps : MapsTo g I (s : Set X) := fun i hi ↦ hgs i hi
  calc I.encard ≤ (s : Set X).encard := encard_le_encard_of_injOn hmaps hinj
    _ = s.card := encard_coe_eq_coe_finsetCard s
    _ ≤ K := by exact_mod_cast hs

end Abstract

end OC
