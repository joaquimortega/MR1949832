import OrtegaCerdaMultipliers.Foundations.Basic
import OrtegaCerdaMultipliers.Foundations.Polar

/-!
# M01 (Foundations) — Uniformly separated sets in `ℂ`

See `blueprint/M01_Foundations.md`.

**Provenance.** Copied from `BerndtssonOrtegaCerda/Geometry/Separated.lean`
(BOC module M04, blueprint `M04_Separated.md`) of the companion project
`../MR1340337` at commit `22104d9` (same author, Apache-2.0).  Changes: namespace
`BOC` → `OC`, imports adjusted; the BOC definitions not in `OrtegaCerdaMultipliers/Defs.lean`
are in `Foundations/Basic.lean`.
-/

open MeasureTheory Metric Set Complex
open scoped ENNReal NNReal ComplexConjugate Topology

noncomputable section

namespace OC

variable {Γ : Set ℂ} {ε : ℝ}

theorem pairwiseDisjoint_ball_of_sep (hε : ∀ a ∈ Γ, ∀ b ∈ Γ, a ≠ b → ε ≤ dist a b) :
    Γ.PairwiseDisjoint (fun a ↦ Metric.ball a (ε / 2)) := by
  intro a ha b hb hab
  exact Metric.ball_disjoint_ball (by linarith [hε a ha b hb hab])

/-- Area comparison: if `t` is a finite subset of `Γ ∩ ball z R` (with `Γ` `ε`-separated and
`R > 0`), then `#t · (ε/2)² ≤ (R + ε/2)²`. -/
theorem card_mul_sq_le_of_sep (hε0 : 0 < ε) (hε : ∀ a ∈ Γ, ∀ b ∈ Γ, a ≠ b → ε ≤ dist a b)
    {z : ℂ} {R : ℝ} (hR : 0 < R) (t : Finset ℂ) (ht : ↑t ⊆ Γ ∩ Metric.ball z R) :
    (t.card : ℝ) * (ε / 2) ^ 2 ≤ (R + ε / 2) ^ 2 := by
  have hd : (t : Set ℂ).PairwiseDisjoint (fun a ↦ Metric.ball a (ε / 2)) :=
    (pairwiseDisjoint_ball_of_sep hε).subset (ht.trans inter_subset_left)
  have hsub : (⋃ a ∈ t, Metric.ball a (ε / 2)) ⊆ Metric.ball z (R + ε / 2) := by
    refine Set.iUnion₂_subset fun a ha ↦ Metric.ball_subset_ball' ?_
    have := mem_ball.1 (ht ha).2
    linarith
  have hvol := measure_mono (μ := volume) hsub
  rw [measure_biUnion_finset hd (fun _ _ ↦ measurableSet_ball)] at hvol
  simp only [Complex.volume_ball, Finset.sum_const, nsmul_eq_mul] at hvol
  rw [← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi, ← ENNReal.ofReal_pow (by positivity),
    ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_le_ofReal_iff (by positivity)] at hvol
  nlinarith [Real.pi_pos]

/-- The counting bound: a finite subset of `Γ ∩ ball z R` has at most `(2R/ε + 1)²` elements. -/
theorem card_le_of_sep (hε0 : 0 < ε) (hε : ∀ a ∈ Γ, ∀ b ∈ Γ, a ≠ b → ε ≤ dist a b)
    {z : ℂ} {R : ℝ} (t : Finset ℂ) (ht : ↑t ⊆ Γ ∩ Metric.ball z R) :
    (t.card : ℝ) ≤ (2 * R / ε + 1) ^ 2 := by
  rcases le_or_gt R 0 with hR | hR
  · have : t = ∅ := by
      rw [Metric.ball_eq_empty.2 hR, inter_empty] at ht
      exact Finset.coe_eq_empty.1 (Set.subset_empty_iff.1 ht)
    subst this
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  · have h := card_mul_sq_le_of_sep hε0 hε hR t ht
    have he : (2 * R / ε + 1) ^ 2 = (R + ε / 2) ^ 2 / (ε / 2) ^ 2 := by
      field_simp
    rw [he, le_div_iff₀ (by positivity)]
    exact h

/-- The counting bound with the explicit constant `⌊(2R/ε + 1)²⌋₊`. -/
theorem card_le_floor_of_sep (hε0 : 0 < ε) (hε : ∀ a ∈ Γ, ∀ b ∈ Γ, a ≠ b → ε ≤ dist a b)
    {z : ℂ} {R : ℝ} (t : Finset ℂ) (ht : ↑t ⊆ Γ ∩ Metric.ball z R) :
    t.card ≤ ⌊(2 * R / ε + 1) ^ 2⌋₊ :=
  Nat.le_floor (card_le_of_sep hε0 hε t ht)

theorem finite_inter_ball_of_sep (hε0 : 0 < ε) (hε : ∀ a ∈ Γ, ∀ b ∈ Γ, a ≠ b → ε ≤ dist a b)
    (z : ℂ) (R : ℝ) : (Γ ∩ Metric.ball z R).Finite := by
  by_contra h
  obtain ⟨t, ht, hcard⟩ := Set.Infinite.exists_subset_card_eq h (⌊(2 * R / ε + 1) ^ 2⌋₊ + 1)
  have := card_le_floor_of_sep hε0 hε t ht
  omega

theorem ncard_inter_ball_le_of_sep (hε0 : 0 < ε) (hε : ∀ a ∈ Γ, ∀ b ∈ Γ, a ≠ b → ε ≤ dist a b)
    (z : ℂ) (R : ℝ) : (Γ ∩ Metric.ball z R).ncard ≤ ⌊(2 * R / ε + 1) ^ 2⌋₊ := by
  have hfin := finite_inter_ball_of_sep hε0 hε z R
  rw [Set.ncard_eq_toFinset_card _ hfin]
  exact card_le_floor_of_sep hε0 hε _ (by rw [Set.Finite.coe_toFinset])

theorem ncard_inter_ball_le_of_sep' (hε0 : 0 < ε) (hε : ∀ a ∈ Γ, ∀ b ∈ Γ, a ≠ b → ε ≤ dist a b)
    (z : ℂ) (R : ℝ) : ((Γ ∩ Metric.ball z R).ncard : ℝ) ≤ (2 * R / ε + 1) ^ 2 := by
  have hfin := finite_inter_ball_of_sep hε0 hε z R
  rw [Set.ncard_eq_toFinset_card _ hfin]
  exact card_le_of_sep hε0 hε _ (by rw [Set.Finite.coe_toFinset])

theorem IsSeparated.finite_inter_ball (hΓ : IsSeparated Γ) (z : ℂ) (R : ℝ) :
    (Γ ∩ Metric.ball z R).Finite := by
  obtain ⟨ε, hε0, hε⟩ := hΓ
  exact finite_inter_ball_of_sep hε0 hε z R

theorem IsSeparated.exists_ncard_le (hΓ : IsSeparated Γ) (R : ℝ) :
    ∃ N : ℕ, ∀ z : ℂ, (Γ ∩ Metric.ball z R).ncard ≤ N := by
  obtain ⟨ε, hε0, hε⟩ := hΓ
  exact ⟨_, fun z ↦ ncard_inter_ball_le_of_sep hε0 hε z R⟩

theorem IsSeparated.countable (hΓ : IsSeparated Γ) : Γ.Countable := by
  obtain ⟨ε, hε0, hε⟩ := hΓ
  exact (pairwiseDisjoint_ball_of_sep hε).countable_of_isOpen (fun _ _ ↦ isOpen_ball)
    (fun _ _ ↦ nonempty_ball.2 (by positivity))

theorem IsSeparated.volume_eq_zero (hΓ : IsSeparated Γ) : volume Γ = 0 := by
  exact hΓ.countable.measure_zero volume

theorem IsSeparated.isClosed (hΓ : IsSeparated Γ) : IsClosed Γ := by
  obtain ⟨ε, hε0, hε⟩ := hΓ
  exact Metric.isClosed_of_pairwise_le_dist hε0 (fun a ha b hb hab ↦ hε a ha b hb hab)

theorem IsSeparated.mono {Γ' : Set ℂ} (hΓ : IsSeparated Γ) (h : Γ' ⊆ Γ) : IsSeparated Γ' := by
  obtain ⟨ε, hε0, hε⟩ := hΓ
  exact ⟨ε, hε0, fun a ha b hb hab ↦ hε a (h ha) b (h hb) hab⟩

/-- Pointwise bounded overlap: if every finite family of points of `Γ` within distance `R` of `z`
has at most `N` elements, then `∑_{a ∈ Γ} 1_{ball a R}(z) F(z) ≤ N F(z)`. -/
theorem tsum_indicator_ball_le {R : ℝ} {N : ℕ} {z : ℂ}
    (hN : ∀ t : Finset ℂ, ↑t ⊆ Γ ∩ Metric.ball z R → t.card ≤ N) (F : ℂ → ℝ≥0∞) :
    ∑' a : Γ, (Metric.ball (a : ℂ) R).indicator F z ≤ (N : ℝ≥0∞) * F z := by
  refine ENNReal.summable.tsum_le_of_sum_le fun s ↦ ?_
  classical
  simp only [Set.indicator_apply]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  gcongr
  rw [← Finset.card_map (Function.Embedding.subtype _)]
  apply hN
  intro w hw
  simp only [Finset.coe_map, Function.Embedding.coe_subtype, Finset.coe_filter, mem_image,
    mem_ofPred_eq] at hw
  obtain ⟨a, ⟨_, ha⟩, rfl⟩ := hw
  exact ⟨a.2, Metric.mem_ball_comm.1 ha⟩

/-- Bounded overlap with an explicit counting hypothesis. -/
theorem tsum_lintegral_ball_le_of_card_le [Countable Γ] {R : ℝ} {N : ℕ}
    (hN : ∀ z : ℂ, ∀ t : Finset ℂ, ↑t ⊆ Γ ∩ Metric.ball z R → t.card ≤ N)
    (F : ℂ → ℝ≥0∞) (hF : Measurable F) :
    ∑' a : Γ, ∫⁻ z in Metric.ball (a : ℂ) R, F z ≤ (N : ℝ≥0∞) * ∫⁻ z, F z := by
  simp_rw [← lintegral_indicator measurableSet_ball]
  rw [← lintegral_tsum (fun a ↦ (hF.indicator measurableSet_ball).aemeasurable),
    ← lintegral_const_mul _ hF]
  exact lintegral_mono fun z ↦ tsum_indicator_ball_le (hN z) F

theorem IsSeparated.exists_tsum_lintegral_ball_le (hΓ : IsSeparated Γ) (R : ℝ) :
    ∃ N : ℕ, ∀ F : ℂ → ℝ≥0∞, Measurable F →
      ∑' a : Γ, ∫⁻ z in Metric.ball (a : ℂ) R, F z ≤ (N : ℝ≥0∞) * ∫⁻ z, F z := by
  have : Countable Γ := hΓ.countable.to_subtype
  obtain ⟨ε, hε0, hε⟩ := hΓ
  exact ⟨_, tsum_lintegral_ball_le_of_card_le fun z t ht ↦ card_le_floor_of_sep hε0 hε t ht⟩

theorem tsum_lintegral_ball_le_of_sep (hε0 : 0 < ε)
    (hε : ∀ a ∈ Γ, ∀ b ∈ Γ, a ≠ b → ε ≤ dist a b) (F : ℂ → ℝ≥0∞) (hF : Measurable F) :
    ∑' a : Γ, ∫⁻ z in Metric.ball (a : ℂ) (ε / 2), F z ≤ ∫⁻ z, F z := by
  have : Countable Γ := (IsSeparated.countable ⟨ε, hε0, hε⟩).to_subtype
  have h := tsum_lintegral_ball_le_of_card_le (R := ε / 2) (N := 1) (Γ := Γ) ?_ F hF
  · simpa using h
  intro z t ht
  rw [Finset.card_le_one]
  intro a ha b hb
  by_contra hab
  have h1 := ht ha
  have h2 := ht hb
  rw [mem_inter_iff, mem_ball] at h1 h2
  have := hε a h1.1 b h2.1 hab
  have := dist_triangle_right a b z
  linarith

theorem IsSeparated.locallyFinite_ball (hΓ : IsSeparated Γ) (R : ℝ) :
    LocallyFinite (fun a : Γ ↦ Metric.ball (a : ℂ) R) := by
  intro x
  refine ⟨Metric.ball x 1, ball_mem_nhds _ one_pos, ?_⟩
  refine ((hΓ.finite_inter_ball x (R + 1)).preimage Subtype.val_injective.injOn).subset ?_
  rintro ⟨a, ha⟩ ⟨w, hw1, hw2⟩
  rw [mem_ball] at hw1 hw2
  refine ⟨ha, ?_⟩
  rw [mem_ball]
  have := dist_triangle a w x
  rw [dist_comm] at hw1
  linarith

end OC
