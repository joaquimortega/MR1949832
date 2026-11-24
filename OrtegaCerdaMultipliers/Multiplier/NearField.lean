/-
Copyright (c) 2026 Joaquim Ortega-Cerdà. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joaquim Ortega-Cerdà
-/
import OrtegaCerdaMultipliers.Multiplier.Basic
import OrtegaCerdaMultipliers.Multiplier.Cells
import OrtegaCerdaMultipliers.ModelKernels

/-!
# M08 (Multiplier) — The area-counting near-field lemma and the far-field sums

See `blueprint/M08_Multiplier.md` §2.4, §3.5, §3.6.
-/

open MeasureTheory Metric Set Complex
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace OC

/-! ### The dyadic summation behind the near-field lemma -/

/-- Dyadic index: `2^n t ≤ β < 2^(n+1) t` for `n = dyadicIdx t β` when `t ≤ β`. -/
def dyadicIdx (t β : ℝ) : ℕ := Nat.log 2 ⌊β / t⌋₊

theorem dyadicIdx_spec {t β : ℝ} (ht : 0 < t) (hβ : t ≤ β) :
    2 ^ dyadicIdx t β * t ≤ β ∧ β < 2 ^ (dyadicIdx t β + 1) * t := by
  have hq : 1 ≤ β / t := by rw [le_div_iff₀ ht]; linarith
  have hlog : Int.log 2 (β / t) = (dyadicIdx t β : ℤ) := Int.log_of_one_le_right 2 hq
  have h1 := Int.zpow_log_le_self (b := 2) (by norm_num) (by linarith : 0 < β / t)
  have h2 := Int.lt_zpow_succ_log_self (b := 2) (by norm_num) (β / t)
  rw [hlog] at h1 h2
  push_cast at h1 h2
  rw [zpow_natCast] at h1
  rw [show ((dyadicIdx t β : ℤ) + 1) = ((dyadicIdx t β + 1 : ℕ) : ℤ) by push_cast; ring,
    zpow_natCast] at h2
  constructor
  · rwa [le_div_iff₀ ht] at h1
  · rwa [div_lt_iff₀ ht] at h2

/-- Dyadic summation: ring-wise `ℓ²` bounds and a geometric decay of the maximum give a bounded
`ℓ³` sum. -/
theorem dyadic_sum_le {F : Finset ℕ} {r β : ℕ → ℝ} {t Q C' α : ℝ} (ht : 0 < t) (hα : 0 < α)
    (hQ0 : 0 ≤ Q) (hC' : 0 ≤ C') (hβ : ∀ i ∈ F, t ≤ β i)
    (hQ : ∀ n : ℕ, ∑ i ∈ F.filter (fun i ↦ 2 ^ n * t ≤ β i ∧ β i < 2 ^ (n + 1) * t),
      (r i / β i) ^ 2 ≤ Q)
    (hmax : ∀ n : ℕ, ∀ i ∈ F, 2 ^ n * t ≤ β i → β i < 2 ^ (n + 1) * t →
      r i / β i ≤ C' * ((2 : ℝ) ^ (-α)) ^ n) :
    ∑ i ∈ F, (r i / β i) ^ 3 ≤ C' * Q / (1 - (2 : ℝ) ^ (-α)) := by
  set θ := (2 : ℝ) ^ (-α)
  have hθ0 : 0 ≤ θ := by positivity
  have hθ1 : θ < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  set g : ℕ → ℕ := fun i ↦ dyadicIdx t (β i)
  rw [← Finset.sum_fiberwise_of_maps_to (g := g) (t := F.image g)
    (fun i hi ↦ Finset.mem_image_of_mem g hi)]
  have hfib : ∀ n ∈ F.image g, ∑ i ∈ F with g i = n, (r i / β i) ^ 3 ≤ C' * Q * θ ^ n := by
    intro n _
    have hsub : ∀ i ∈ F.filter (fun i ↦ g i = n),
        i ∈ F.filter (fun i ↦ 2 ^ n * t ≤ β i ∧ β i < 2 ^ (n + 1) * t) := by
      intro i hi
      rw [Finset.mem_filter] at hi ⊢
      refine ⟨hi.1, ?_⟩
      rw [← hi.2]; exact dyadicIdx_spec ht (hβ i hi.1)
    calc ∑ i ∈ F with g i = n, (r i / β i) ^ 3
        ≤ ∑ i ∈ F with g i = n, C' * θ ^ n * (r i / β i) ^ 2 := by
          refine Finset.sum_le_sum fun i hi ↦ ?_
          have hi' := Finset.mem_filter.1 (hsub i hi)
          have hm := hmax n i hi'.1 hi'.2.1 hi'.2.2
          calc (r i / β i) ^ 3 = (r i / β i) * (r i / β i) ^ 2 := by ring
            _ ≤ C' * θ ^ n * (r i / β i) ^ 2 := by gcongr
      _ = C' * θ ^ n * ∑ i ∈ F with g i = n, (r i / β i) ^ 2 := by rw [Finset.mul_sum]
      _ ≤ C' * θ ^ n * ∑ i ∈ F.filter (fun i ↦ 2 ^ n * t ≤ β i ∧ β i < 2 ^ (n + 1) * t),
            (r i / β i) ^ 2 := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg
            (fun i hi ↦ hsub i hi) fun i _ _ ↦ by positivity) (by positivity)
      _ ≤ C' * θ ^ n * Q := mul_le_mul_of_nonneg_left (hQ n) (by positivity)
      _ = C' * Q * θ ^ n := by ring
  calc ∑ n ∈ F.image g, ∑ i ∈ F with g i = n, (r i / β i) ^ 3
      ≤ ∑ n ∈ F.image g, C' * Q * θ ^ n := Finset.sum_le_sum hfib
    _ = C' * Q * ∑ n ∈ F.image g, θ ^ n := by rw [Finset.mul_sum]
    _ ≤ C' * Q * ∑' n, θ ^ n := by
        gcongr
        exact Summable.sum_le_tsum _ (fun n _ ↦ by positivity)
          (summable_geometric_of_lt_one hθ0 hθ1)
    _ = C' * Q / (1 - θ) := by rw [tsum_geometric_of_lt_one hθ0 hθ1, div_eq_mul_inv]



theorem one_div_two_pow_mul_rpow {δ α : ℝ} (hδ : 0 < δ) (n : ℕ) :
    (1 / (2 ^ n * δ)) ^ α = ((2 : ℝ) ^ (-α)) ^ n * δ ^ (-α) := by
  rw [one_div, Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity),
    Real.mul_rpow (by positivity) hδ.le, ← Real.rpow_natCast, ← Real.rpow_natCast,
    ← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num), mul_comm,
    mul_comm (n : ℝ) (-α), mul_comm]

/-- Geometric decay of the ratio `ρᵢ / β` inside a dyadic ring (abstract form of the second half
of the near-field estimate, shared by the plane and the disc). -/
theorem near_ratio_bound {ρz ρi β δ Cdec C₁ α : ℝ} {n : ℕ} (hδ : 0 < δ) (hα : 0 < α)
    (hCdec : 0 ≤ Cdec) (hC₁ : 0 ≤ C₁) (hρz : 0 < ρz) (hβ : δ * ρz ≤ β)
    (hlo : 2 ^ n * (δ * ρz) ≤ β) (hdec : ρz ≤ β → ρi / β ≤ Cdec * (ρz / β) ^ α)
    (hcl : β < ρz → ρi ≤ C₁ * ρz) :
    ρi / β ≤ max Cdec (C₁ / δ) * δ ^ (-α) * ((2 : ℝ) ^ (-α)) ^ n := by
  have hβpos : 0 < β := (by positivity : 0 < δ * ρz).trans_le hβ
  have hθ : (1 / (2 ^ n * δ)) ^ α = ((2 : ℝ) ^ (-α)) ^ n * δ ^ (-α) :=
    one_div_two_pow_mul_rpow hδ n
  have h0 : 0 ≤ ((2 : ℝ) ^ (-α)) ^ n * δ ^ (-α) := by positivity
  by_cases hcase : ρz ≤ β
  · have h2 : ρz / β ≤ 1 / (2 ^ n * δ) := by
      rw [div_le_div_iff₀ hβpos (by positivity)]
      nlinarith
    have h3 : (ρz / β) ^ α ≤ (1 / (2 ^ n * δ)) ^ α :=
      Real.rpow_le_rpow (by positivity) h2 hα.le
    rw [hθ] at h3
    calc ρi / β ≤ Cdec * (ρz / β) ^ α := hdec hcase
      _ ≤ Cdec * (((2 : ℝ) ^ (-α)) ^ n * δ ^ (-α)) := by gcongr
      _ ≤ max Cdec (C₁ / δ) * δ ^ (-α) * ((2 : ℝ) ^ (-α)) ^ n := by
          have : Cdec ≤ max Cdec (C₁ / δ) := le_max_left _ _
          nlinarith
  · push Not at hcase
    have h1 := hcl hcase
    have h2 : ρi / β ≤ C₁ / δ := by
      rw [div_le_div_iff₀ hβpos hδ]
      nlinarith [mul_le_mul_of_nonneg_left hβ hC₁]
    have h3 : 1 ≤ ((2 : ℝ) ^ (-α)) ^ n * δ ^ (-α) := by
      rw [← hθ]
      apply Real.one_le_rpow _ hα.le
      rw [le_div_iff₀ (by positivity), one_mul]
      have : 2 ^ n * δ * ρz < ρz := by nlinarith
      nlinarith
    calc ρi / β ≤ C₁ / δ := h2
      _ ≤ C₁ / δ * (((2 : ℝ) ^ (-α)) ^ n * δ ^ (-α)) :=
          le_mul_of_one_le_right (by positivity) h3
      _ ≤ max Cdec (C₁ / δ) * δ ^ (-α) * ((2 : ℝ) ^ (-α)) ^ n := by
          have : C₁ / δ ≤ max Cdec (C₁ / δ) := le_max_right _ _
          nlinarith

/-- Squares of ratios in a dyadic ring: `∑ ρᵢ² ≤ B` and `s ≤ βᵢ` give `∑ (ρᵢ/βᵢ)² ≤ B / s²`. -/
theorem sum_sq_div_le {Fn : Finset ℕ} {ρ β : ℕ → ℝ} {s B : ℝ} (hs : 0 < s)
    (hβ : ∀ i ∈ Fn, s ≤ β i) (hB : ∑ i ∈ Fn, ρ i ^ 2 ≤ B) :
    ∑ i ∈ Fn, (ρ i / β i) ^ 2 ≤ B / s ^ 2 := by
  calc ∑ i ∈ Fn, (ρ i / β i) ^ 2 ≤ ∑ i ∈ Fn, ρ i ^ 2 / s ^ 2 :=
        Finset.sum_le_sum fun i hi ↦ by
          rw [div_pow]
          gcongr
          exact hβ i hi
    _ = (∑ i ∈ Fn, ρ i ^ 2) / s ^ 2 := by rw [Finset.sum_div]
    _ ≤ B / s ^ 2 := by gcongr

/-- **Area-counting near-field lemma (plane)** — replaces the paper's Lemma 3. -/
theorem nearField_sum_le_plane (Cd : ℝ≥0) (R₀ η A δ : ℝ) (hη : 0 < η) (hδ : 0 < δ) :
    ∃ C : ℝ, ∀ (ν : Measure ℂ) (N : ℕ) (R : ℕ → Set ℂ) (c : ℕ → ℂ),
      MeasClassPlane ν Cd R₀ → IsCells univ dist (massRadius ν) ν N η A R c → ∀ z : ℂ,
      ∀ F : Finset ℕ, (∀ i ∈ F, δ * massRadius ν z ≤ dist z (c i) ∧ dist z (c i) ≤ 1 / 4 ∧
          A * massRadius ν (c i) ≤ dist z (c i)) →
        ∑ i ∈ F, (massRadius ν (c i) / dist z (c i)) ^ 3 ≤ C := by
  obtain ⟨Cdec, α, hCdec, hα, hdec⟩ := decay_plane_quant Cd R₀
  obtain ⟨C₁, hC₁, hcl⟩ := claim1_plane_quant Cd R₀ 1
  set Q := 36 / η ^ 2 with hQ
  set C' := max Cdec (C₁ / δ) * δ ^ (-α)
  refine ⟨C' * Q / (1 - (2 : ℝ) ^ (-α)), ?_⟩
  intro ν N R c hν hC z F hF
  have hρ : ∀ w, 0 < massRadius ν w := fun w ↦ (hcl ν hν w w).1
  have hρz := hρ z
  have hA : η / 2 ≤ A := hC.half_le_A_plane (i := 0) (hρ _) hη
  set t := δ * massRadius ν z
  have ht0 : 0 < t := by positivity
  refine dyadic_sum_le (r := fun i ↦ massRadius ν (c i)) (β := fun i ↦ dist z (c i))
    ht0 hα (by positivity) (by positivity) (fun i hi ↦ (hF i hi).1)
    ?_ ?_
  · intro n
    set Fn := F.filter (fun i ↦ 2 ^ n * t ≤ dist z (c i) ∧ dist z (c i) < 2 ^ (n + 1) * t)
    set b := 6 * (2 ^ n * t) with hb
    have hb0 : 0 < b := by positivity
    have hsub : ∀ i ∈ Fn, ball (c i) (η * massRadius ν (c i)) ⊆ R i :=
      fun i _ w hw ↦ hC.inner i ⟨mem_univ _, by rw [dist_comm]; exact hw⟩
    have hball : ∀ i ∈ Fn, ball (c i) (η * massRadius ν (c i)) ⊆ ball z b := by
      intro i hi w hw
      have hi' := Finset.mem_filter.1 hi
      rw [mem_ball] at hw ⊢
      have htri := dist_triangle w (c i) z
      have h3 := (hF i hi'.1).2.2
      have hηA : η * massRadius ν (c i) ≤ 2 * (A * massRadius ν (c i)) := by
        nlinarith [hρ (c i)]
      have : dist z (c i) < 2 ^ (n + 1) * t := hi'.2.2
      rw [pow_succ] at this
      rw [dist_comm (c i) z] at htri
      linarith
    have hdisj : (Fn : Set ℕ).PairwiseDisjoint
        fun i ↦ ball (c i) (η * massRadius ν (c i)) := by
      intro i hi j hj hij
      exact (hC.pairwise_disjoint hij).mono (hsub i hi) (hsub j hj)
    have hcount := sum_le_of_pairwiseDisjoint (μ := volume)
      (E := fun i ↦ ball (c i) (η * massRadius ν (c i))) (U := ball z b)
      (f := fun i ↦ Real.pi * (η * massRadius ν (c i)) ^ 2)
      (V := Real.pi * b ^ 2) (fun i _ ↦ isOpen_ball.measurableSet) hdisj
      hball (fun i _ ↦ by positivity)
      (fun i _ ↦ (volume_ball_complex _ (by have := hρ (c i); positivity)).ge)
      (by positivity) (volume_ball_complex _ hb0.le).le
    rw [← Finset.mul_sum] at hcount
    have hsum : ∑ i ∈ Fn, (massRadius ν (c i)) ^ 2 ≤ b ^ 2 / η ^ 2 := by
      have h1 : ∑ i ∈ Fn, (η * massRadius ν (c i)) ^ 2 ≤ b ^ 2 := by
        have := Real.pi_pos; nlinarith
      simp_rw [mul_pow] at h1
      rw [← Finset.mul_sum] at h1
      rw [le_div_iff₀ (by positivity), mul_comm]
      linarith
    exact (sum_sq_div_le (by positivity) (fun i hi ↦ (Finset.mem_filter.1 hi).2.1) hsum).trans
      (le_of_eq (by rw [hb, hQ]; field_simp; ring))
  · intro n i hi hlo _
    have hβ := hF i hi
    refine near_ratio_bound hδ hα hCdec.le (by linarith) hρz hβ.1 hlo
      (fun h ↦ hdec ν hν z (c i) h hβ.2.1) fun h ↦ (hcl ν hν (c i) z).2.2 ?_
    rw [dist_comm, one_mul]
    exact h.le.trans (le_max_right _ _)

/-- **Area-counting near-field lemma (disc)**. -/
theorem nearField_sum_le_disc (Cd : ℝ≥0) (R₀ η A δ : ℝ) (hη : 0 < η) (hδ : 0 < δ) :
    ∃ C : ℝ, ∀ (ν : Measure ℂ) (N : ℕ) (R : ℕ → Set ℂ) (c : ℕ → ℂ),
      MeasClassDisc ν Cd R₀ → IsCells 𝔻 hypDist (massRadiusDisc ν) ν N η A R c → ∀ z ∈ 𝔻,
      ∀ F : Finset ℕ, (∀ i ∈ F, δ * massRadiusDisc ν z ≤ hypDist z (c i) ∧
          hypDist z (c i) ≤ 1 / 4 ∧ A * massRadiusDisc ν (c i) ≤ hypDist z (c i)) →
        ∑ i ∈ F, (massRadiusDisc ν (c i) / hypDist z (c i)) ^ 3 ≤ C := by
  obtain ⟨Cdec, α, hCdec, hα, hdec⟩ := decay_disc_quant Cd R₀
  obtain ⟨C₁, hC₁, hcl⟩ := claim1_disc_quant Cd R₀ 1
  set Q := 36 * Real.exp 3 / η ^ 2 with hQ
  set C' := max Cdec (C₁ / δ) * δ ^ (-α)
  refine ⟨C' * Q / (1 - (2 : ℝ) ^ (-α)), ?_⟩
  intro ν N R c hν hC z hz F hF
  have hci := hC.center_mem'
  have hρ : ∀ w ∈ 𝔻, 0 < massRadiusDisc ν w := fun w hw ↦ (hcl ν hν w hw w hw).1
  have hρz := hρ z hz
  have hA : η / 2 ≤ A := hC.half_le_A_disc (i := 0) (hρ _ (hci 0)) hη
  set t := δ * massRadiusDisc ν z
  have ht0 : 0 < t := by positivity
  refine dyadic_sum_le (r := fun i ↦ massRadiusDisc ν (c i)) (β := fun i ↦ hypDist z (c i))
    ht0 hα (by positivity) (by positivity) (fun i hi ↦ (hF i hi).1)
    ?_ ?_
  · -- ring-wise area bound
    intro n
    set Fn := F.filter (fun i ↦ 2 ^ n * t ≤ hypDist z (c i) ∧ hypDist z (c i) < 2 ^ (n + 1) * t)
    rcases Fn.eq_empty_or_nonempty with hne | ⟨i₀, hi₀⟩
    · rw [hne, Finset.sum_empty]; positivity
    have hi₀' := Finset.mem_filter.1 hi₀
    set b := 6 * (2 ^ n * t) with hb
    have hb0 : 0 < b := by positivity
    have hb32 : b ≤ 3 / 2 := by
      have := (hF i₀ hi₀'.1).2.1; rw [hb]; linarith [hi₀'.2.1]
    have hsub : ∀ i ∈ Fn, hypBall (c i) (η * massRadiusDisc ν (c i)) ⊆ R i :=
      fun i _ w hw ↦ hC.inner i hw
    have hball : ∀ i ∈ Fn, hypBall (c i) (η * massRadiusDisc ν (c i)) ⊆ hypBall z b := by
      intro i hi w hw
      have hi' := Finset.mem_filter.1 hi
      refine ⟨hw.1, ?_⟩
      have htri := hypDist_triangle hz (hci i) hw.1
      have h3 := (hF i hi'.1).2.2
      have hηA : η * massRadiusDisc ν (c i) ≤ 2 * (A * massRadiusDisc ν (c i)) := by
        nlinarith [hρ _ (hci i)]
      have : hypDist z (c i) < 2 ^ (n + 1) * t := hi'.2.2
      rw [pow_succ] at this
      linarith [hw.2]
    have hdisj : (Fn : Set ℕ).PairwiseDisjoint
        fun i ↦ hypBall (c i) (η * massRadiusDisc ν (c i)) := by
      intro i hi j hj hij
      exact (hC.pairwise_disjoint hij).mono (hsub i hi) (hsub j hj)
    have hcount := sum_le_of_pairwiseDisjoint (μ := hypArea)
      (E := fun i ↦ hypBall (c i) (η * massRadiusDisc ν (c i))) (U := hypBall z b)
      (f := fun i ↦ Real.pi * Real.sinh (η * massRadiusDisc ν (c i)) ^ 2)
      (V := Real.pi * Real.sinh b ^ 2) (fun i _ ↦ (isOpen_hypBall _ _).measurableSet) hdisj
      hball (fun i _ ↦ by positivity)
      (fun i _ ↦ (hypArea_hypBall (hci i) (by have := hρ _ (hci i); positivity)).ge)
      (by positivity) (hypArea_hypBall hz hb0.le).le
    rw [← Finset.mul_sum] at hcount
    have hsum : ∑ i ∈ Fn, (massRadiusDisc ν (c i)) ^ 2 ≤ b ^ 2 * Real.exp 3 / η ^ 2 := by
      have h1 : ∑ i ∈ Fn, Real.sinh (η * massRadiusDisc ν (c i)) ^ 2 ≤ Real.sinh b ^ 2 := by
        have := Real.pi_pos; nlinarith
      have h2 : ∑ i ∈ Fn, (η * massRadiusDisc ν (c i)) ^ 2 ≤
          ∑ i ∈ Fn, Real.sinh (η * massRadiusDisc ν (c i)) ^ 2 :=
        Finset.sum_le_sum fun i _ ↦ by
          have h0 : 0 ≤ η * massRadiusDisc ν (c i) := by have := hρ _ (hci i); positivity
          gcongr; exact Real.self_le_sinh_iff.2 h0
      have h3 : Real.sinh b ^ 2 ≤ b ^ 2 * Real.exp 3 := by
        have := sinh_le_mul_exp hb0.le
        have h4 : Real.exp b ^ 2 ≤ Real.exp 3 := by
          rw [← Real.exp_nat_mul]; exact Real.exp_le_exp.2 (by push_cast; linarith)
        calc Real.sinh b ^ 2 ≤ (b * Real.exp b) ^ 2 := by gcongr
          _ = b ^ 2 * Real.exp b ^ 2 := by ring
          _ ≤ b ^ 2 * Real.exp 3 := by gcongr
      simp_rw [mul_pow] at h2
      rw [← Finset.mul_sum] at h2
      rw [le_div_iff₀ (by positivity), mul_comm]
      linarith
    exact (sum_sq_div_le (by positivity) (fun i hi ↦ (Finset.mem_filter.1 hi).2.1) hsum).trans
      (le_of_eq (by rw [hb, hQ]; field_simp; ring))
  · -- geometric decay of the ratio
    intro n i hi hlo _
    have hβ := hF i hi
    refine near_ratio_bound hδ hα hCdec.le (by linarith) hρz hβ.1 hlo
      (fun h ↦ hdec ν hν z hz (c i) (hci i) h hβ.2.1) fun h ↦
        (hcl ν hν (c i) (hci i) z hz).2.2 ?_
    rw [hypDist_comm, one_mul]
    exact h.le.trans (le_max_right _ _)

/-- Far field (plane). -/
theorem farField_sum_le_plane (Cd : ℝ≥0) (R₀ η A M₀ : ℝ) (hη : 0 < η) (hM₀ : 0 < M₀) :
    ∃ C : ℝ, ∀ (ν : Measure ℂ) (N : ℕ) (R : ℕ → Set ℂ) (c : ℕ → ℂ),
      MeasClassPlane ν Cd R₀ → IsCells univ dist (massRadius ν) ν N η A R c → ∀ z : ℂ,
      ∀ F : Finset ℕ, (∀ i ∈ F, M₀ ≤ dist z (c i) ∧ 2 * A * massRadius ν (c i) ≤ dist z (c i)) →
        ∑ i ∈ F, (massRadius ν (c i) / dist z (c i)) ^ 3 ≤ C := by
  obtain ⟨C₁, -, hcl⟩ := claim1_plane_quant Cd R₀ 0
  set a := min η (η / 2)
  have ha0 : 0 < a := lt_min hη (by linarith)
  set Q := 16 / a ^ 2 with hQ
  set C' := max R₀ 0 / M₀ with hC'
  refine ⟨C' * Q / (1 - (2 : ℝ) ^ (-(1 : ℝ))), ?_⟩
  intro ν N R c hν hC z F hF
  have hρ : ∀ w, 0 < massRadius ν w := fun w ↦ (hcl ν hν w w).1
  have hρR : ∀ w, massRadius ν w ≤ R₀ := fun w ↦ (hcl ν hν w w).2.1
  have hA : η / 2 ≤ A := hC.half_le_A_plane (i := 0) (hρ _) hη
  have haA : a ≤ A := (min_le_right _ _).trans hA
  have haη : a ≤ η := min_le_left _ _
  refine dyadic_sum_le (r := fun i ↦ massRadius ν (c i)) (β := fun i ↦ dist z (c i))
    hM₀ one_pos (by positivity) (by positivity) (fun i hi ↦ (hF i hi).1)
    ?_ ?_
  · intro n
    set Fn := F.filter (fun i ↦ 2 ^ n * M₀ ≤ dist z (c i) ∧ dist z (c i) < 2 ^ (n + 1) * M₀)
    set b := 4 * (2 ^ n * M₀) with hb
    have hb0 : 0 < b := by positivity
    have hsub : ∀ i ∈ Fn, ball (c i) (a * massRadius ν (c i)) ⊆ R i := by
      intro i _ w hw
      refine hC.inner i ⟨mem_univ _, ?_⟩
      rw [dist_comm]
      exact (mem_ball.1 hw).trans_le (mul_le_mul_of_nonneg_right haη (hρ _).le)
    have hball : ∀ i ∈ Fn, ball (c i) (a * massRadius ν (c i)) ⊆ ball z b := by
      intro i hi w hw
      have hi' := Finset.mem_filter.1 hi
      rw [mem_ball] at hw ⊢
      have htri := dist_triangle w (c i) z
      have h3 := (hF i hi'.1).2
      have haA' : a * massRadius ν (c i) ≤ A * massRadius ν (c i) :=
        mul_le_mul_of_nonneg_right haA (hρ _).le
      have : dist z (c i) < 2 ^ (n + 1) * M₀ := hi'.2.2
      rw [pow_succ] at this
      rw [dist_comm (c i) z] at htri
      nlinarith
    have hdisj : (Fn : Set ℕ).PairwiseDisjoint
        fun i ↦ ball (c i) (a * massRadius ν (c i)) := by
      intro i hi j hj hij
      exact (hC.pairwise_disjoint hij).mono (hsub i hi) (hsub j hj)
    have hcount := sum_le_of_pairwiseDisjoint (μ := volume)
      (E := fun i ↦ ball (c i) (a * massRadius ν (c i))) (U := ball z b)
      (f := fun i ↦ Real.pi * (a * massRadius ν (c i)) ^ 2)
      (V := Real.pi * b ^ 2) (fun i _ ↦ isOpen_ball.measurableSet) hdisj
      hball (fun i _ ↦ by positivity)
      (fun i _ ↦ (volume_ball_complex _ (by have := hρ (c i); positivity)).ge)
      (by positivity) (volume_ball_complex _ hb0.le).le
    rw [← Finset.mul_sum] at hcount
    have hsum : ∑ i ∈ Fn, (massRadius ν (c i)) ^ 2 ≤ b ^ 2 / a ^ 2 := by
      have h1 : ∑ i ∈ Fn, (a * massRadius ν (c i)) ^ 2 ≤ b ^ 2 := by
        have := Real.pi_pos; nlinarith
      simp_rw [mul_pow] at h1
      rw [← Finset.mul_sum] at h1
      rw [le_div_iff₀ (by positivity), mul_comm]
      linarith
    calc ∑ i ∈ Fn, (massRadius ν (c i) / dist z (c i)) ^ 2
        ≤ ∑ i ∈ Fn, (massRadius ν (c i)) ^ 2 / (2 ^ n * M₀) ^ 2 :=
          Finset.sum_le_sum fun i hi ↦ by
            have hi' := Finset.mem_filter.1 hi
            rw [div_pow]
            gcongr
            exact hi'.2.1
      _ = (∑ i ∈ Fn, (massRadius ν (c i)) ^ 2) / (2 ^ n * M₀) ^ 2 := by
          rw [Finset.sum_div]
      _ ≤ b ^ 2 / a ^ 2 / (2 ^ n * M₀) ^ 2 := by gcongr
      _ = Q := by rw [hb, hQ]; field_simp; ring
  · intro n i _ hlo _
    have hdpos : 0 < dist z (c i) := lt_of_lt_of_le (by positivity) hlo
    have h2 : (2 : ℝ) ^ (-(1 : ℝ)) = 1 / 2 := by rw [Real.rpow_neg_one]; norm_num
    rw [h2, hC', div_pow, one_pow]
    rw [div_le_iff₀ hdpos]
    have hR := (hρR (c i)).trans (le_max_left R₀ 0)
    have : max R₀ 0 / M₀ * (1 / 2 ^ n) * dist z (c i) ≥
        max R₀ 0 / M₀ * (1 / 2 ^ n) * (2 ^ n * M₀) := by
      gcongr
    have e : max R₀ 0 / M₀ * (1 / 2 ^ n) * (2 ^ n * M₀) = max R₀ 0 := by field_simp
    linarith

/-- Lower bound of the local integral of the Forelli–Rudin kernel on a small Euclidean ball. -/
private theorem farDisc_lintegral_ge {z a : ℂ} {r s S : ℝ} (hz : z ∈ 𝔻) (ha : a ∈ 𝔻)
    (hr : 0 ≤ r) (hball : ball a r ⊆ hypBall a s) (hs : s ≤ S) :
    ENNReal.ofReal (Real.exp (-(6 * S)) / ‖1 - conj z * a‖ ^ 3) *
        ENNReal.ofReal (Real.pi * r ^ 2) ≤
      ∫⁻ w in ball a r, ENNReal.ofReal (1 / ‖1 - conj z * w‖ ^ 3) := by
  have hD := norm_one_sub_conj_mul_pos hz ha
  rw [← volume_ball_complex a hr, ← setLIntegral_const]
  refine setLIntegral_mono' isOpen_ball.measurableSet fun w hw ↦ ?_
  have hw' := hball hw
  have hcomp := (norm_one_sub_conj_mul_comparable hz ha hw'.1 hw'.2.le).1
  have hDw := norm_one_sub_conj_mul_pos hz hw'.1
  apply ENNReal.ofReal_le_ofReal
  have he : Real.exp (2 * s) ≤ Real.exp (2 * S) := Real.exp_le_exp.2 (by linarith)
  have h1 : ‖1 - conj z * w‖ ≤ Real.exp (2 * S) * ‖1 - conj z * a‖ :=
    hcomp.trans (by gcongr)
  have h3 : ‖1 - conj z * w‖ ^ 3 ≤ Real.exp (6 * S) * ‖1 - conj z * a‖ ^ 3 := by
    have : Real.exp (6 * S) = Real.exp (2 * S) ^ 3 := by
      rw [← Real.exp_nat_mul]; ring_nf
    rw [this, ← mul_pow]; gcongr
  rw [Real.exp_neg, div_le_div_iff₀ (pow_pos hD 3) (pow_pos hDw 3)]
  have := Real.exp_pos (6 * S)
  field_simp
  nlinarith

/-- Pointwise real estimate of a term of the Forelli–Rudin far-field sum on the disc. -/
private theorem farDisc_real_bound {x y ρ η ct S D r : ℝ} (hx : 0 ≤ x) (hy : 0 < y) (hρ : 0 < ρ)
    (hη : 0 < η) (hct : 0 < ct) (hD : 0 < D) (hr : r = Real.tanh (η * ρ) * y / 2)
    (hct_le : ct * (η * ρ) ≤ Real.tanh (η * ρ)) :
    x * (y * ρ) ^ 2 / D ^ 3 ≤ 4 * Real.exp (6 * S) / (Real.pi * ct ^ 2 * η ^ 2) * x *
      (Real.exp (-(6 * S)) / D ^ 3 * (Real.pi * r ^ 2)) := by
  have hr2 : (ct * η * ρ * y / 2) ^ 2 ≤ r ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_right hct_le hy.le
    gcongr
    rw [hr]
    linarith
  calc x * (y * ρ) ^ 2 / D ^ 3
      = x * (4 / (ct ^ 2 * η ^ 2 * D ^ 3)) * (ct * η * ρ * y / 2) ^ 2 := by
        field_simp
        ring
    _ ≤ x * (4 / (ct ^ 2 * η ^ 2 * D ^ 3)) * r ^ 2 := by gcongr
    _ = _ := by
        rw [Real.exp_neg]
        field_simp

/-- Far field (disc): the Forelli–Rudin sum. -/
theorem farField_sum_le_disc (Cd : ℝ≥0) (R₀ η A M₀ : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, ∀ (ν : Measure ℂ) (N : ℕ) (R : ℕ → Set ℂ) (c : ℕ → ℂ),
      MeasClassDisc ν Cd R₀ → IsCells 𝔻 hypDist (massRadiusDisc ν) ν N η A R c → ∀ z ∈ 𝔻,
      ∀ F : Finset ℕ, (∀ i ∈ F, M₀ ≤ hypDist z (c i)) →
        ∑ i ∈ F, (1 - ‖z‖ ^ 2) * ((1 - ‖c i‖ ^ 2) * massRadiusDisc ν (c i)) ^ 2 /
          ‖1 - conj z * c i‖ ^ 3 ≤ C := by
  obtain ⟨CFR, hFR⟩ := integral_one_sub_conj_mul_rpow_neg_three_le
  obtain ⟨C₁, -, hcl⟩ := claim1_disc_quant Cd R₀ 0
  set S := η * max R₀ 0 + 1
  have hS0 : 0 < S := by positivity
  set ct := min (1 / 5) (Real.tanh 1 / S)
  have hct0 : 0 < ct := lt_min (by norm_num) (div_pos (tanh_pos' one_pos) hS0)
  set K := 4 * Real.exp (6 * S) / (Real.pi * ct ^ 2 * η ^ 2)
  refine ⟨K * max CFR 0, ?_⟩
  intro ν N R c hν hC z hz F _
  have hci := hC.center_mem'
  have hρ : ∀ i, 0 < massRadiusDisc ν (c i) := fun i ↦ (hcl ν hν (c i) (hci i) (c i) (hci i)).1
  have hρR : ∀ i, massRadiusDisc ν (c i) ≤ R₀ := fun i ↦
    (hcl ν hν (c i) (hci i) (c i) (hci i)).2.1
  have hzpos := one_sub_normSq_pos hz
  set r : ℕ → ℝ := fun i ↦ Real.tanh (η * massRadiusDisc ν (c i)) * (1 - ‖c i‖ ^ 2) / 2 with hr
  set E : ℕ → Set ℂ := fun i ↦ ball (c i) (r i)
  have hsη : ∀ i, η * massRadiusDisc ν (c i) ≤ S := fun i ↦ by
    have : η * massRadiusDisc ν (c i) ≤ η * max R₀ 0 :=
      mul_le_mul_of_nonneg_left ((hρR i).trans (le_max_left _ _)) hη.le
    linarith
  have hEhyp : ∀ i, E i ⊆ hypBall (c i) (η * massRadiusDisc ν (c i)) := fun i ↦
    ball_subset_hypBall_tanh (hci i) (mul_pos hη (hρ i))
  have hER : ∀ i, E i ⊆ R i := fun i w hw ↦ hC.inner i (hEhyp i hw)
  have hdisj : (F : Set ℕ).PairwiseDisjoint E := by
    intro i _ j _ hij
    exact (hC.pairwise_disjoint hij).mono (hER i) (hER j)
  set f : ℂ → ℝ≥0∞ := fun w ↦ ENNReal.ofReal (1 / ‖1 - conj z * w‖ ^ 3)
  have hD : ∀ i, 0 < ‖1 - conj z * c i‖ := fun i ↦ norm_one_sub_conj_mul_pos hz (hci i)
  have hterm : ∀ i ∈ F, ENNReal.ofReal ((1 - ‖z‖ ^ 2) *
      ((1 - ‖c i‖ ^ 2) * massRadiusDisc ν (c i)) ^ 2 / ‖1 - conj z * c i‖ ^ 3) ≤
      ENNReal.ofReal (K * (1 - ‖z‖ ^ 2)) * ∫⁻ w in E i, f w := by
    intro i _
    set g := Real.exp (-(6 * S)) / ‖1 - conj z * c i‖ ^ 3
    have hri : 0 ≤ r i := by
      have := one_sub_normSq_pos (hci i)
      have := tanh_nonneg_of_nonneg (mul_pos hη (hρ i)).le
      simp only [hr]; positivity
    have hlow : ENNReal.ofReal g * ENNReal.ofReal (Real.pi * r i ^ 2) ≤ ∫⁻ w in E i, f w :=
      farDisc_lintegral_ge hz (hci i) hri (hEhyp i) (hsη i)
    have hct_le : ct * (η * massRadiusDisc ν (c i)) ≤ Real.tanh (η * massRadiusDisc ν (c i)) :=
      mul_le_tanh hS0 (mul_pos hη (hρ i)).le (hsη i)
    have hreal : (1 - ‖z‖ ^ 2) * ((1 - ‖c i‖ ^ 2) * massRadiusDisc ν (c i)) ^ 2 /
        ‖1 - conj z * c i‖ ^ 3 ≤ K * (1 - ‖z‖ ^ 2) * (g * (Real.pi * r i ^ 2)) :=
      farDisc_real_bound hzpos.le (one_sub_normSq_pos (hci i)) (hρ i) hη hct0 (hD i) rfl hct_le
    calc ENNReal.ofReal ((1 - ‖z‖ ^ 2) *
          ((1 - ‖c i‖ ^ 2) * massRadiusDisc ν (c i)) ^ 2 / ‖1 - conj z * c i‖ ^ 3)
        ≤ ENNReal.ofReal (K * (1 - ‖z‖ ^ 2) * (g * (Real.pi * r i ^ 2))) :=
          ENNReal.ofReal_le_ofReal hreal
      _ = ENNReal.ofReal (K * (1 - ‖z‖ ^ 2)) *
            (ENNReal.ofReal g * ENNReal.ofReal (Real.pi * r i ^ 2)) := by
          rw [ENNReal.ofReal_mul (show 0 ≤ K * (1 - ‖z‖ ^ 2) by positivity),
            ENNReal.ofReal_mul (show 0 ≤ g by positivity)]
      _ ≤ ENNReal.ofReal (K * (1 - ‖z‖ ^ 2)) * ∫⁻ w in E i, f w := by gcongr
  have hsumE : ∑ i ∈ F, ∫⁻ w in E i, f w ≤ ENNReal.ofReal (max CFR 0 / (1 - ‖z‖ ^ 2)) := by
    rw [← lintegral_biUnion_finset hdisj (fun i _ ↦ isOpen_ball.measurableSet)]
    refine (lintegral_mono_set ?_).trans ((hFR z hz).trans (ENNReal.ofReal_le_ofReal ?_))
    · exact iUnion₂_subset fun i _ ↦ (hER i).trans (hC.subset_univ i)
    · gcongr; exact le_max_left _ _
  have hnn : ∀ i ∈ F, 0 ≤ (1 - ‖z‖ ^ 2) * ((1 - ‖c i‖ ^ 2) * massRadiusDisc ν (c i)) ^ 2 /
      ‖1 - conj z * c i‖ ^ 3 := fun i _ ↦ by positivity
  rw [← ENNReal.ofReal_le_ofReal_iff (by positivity), ENNReal.ofReal_sum_of_nonneg hnn]
  calc ∑ i ∈ F, ENNReal.ofReal ((1 - ‖z‖ ^ 2) *
        ((1 - ‖c i‖ ^ 2) * massRadiusDisc ν (c i)) ^ 2 / ‖1 - conj z * c i‖ ^ 3)
      ≤ ∑ i ∈ F, ENNReal.ofReal (K * (1 - ‖z‖ ^ 2)) * ∫⁻ w in E i, f w :=
        Finset.sum_le_sum hterm
    _ = ENNReal.ofReal (K * (1 - ‖z‖ ^ 2)) * ∑ i ∈ F, ∫⁻ w in E i, f w := by
        rw [Finset.mul_sum]
    _ ≤ ENNReal.ofReal (K * (1 - ‖z‖ ^ 2)) * ENNReal.ofReal (max CFR 0 / (1 - ‖z‖ ^ 2)) := by
        gcongr
    _ = ENNReal.ofReal (K * max CFR 0) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp

end OC
