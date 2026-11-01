import OrtegaCerdaMultipliers.Multiplier.Basic
import OrtegaCerdaMultipliers.Multiplier.Cells
import OrtegaCerdaMultipliers.ModelKernels

/-!
# M08 (Multiplier) — The area-counting near-field lemma and the far-field sums

See `blueprint/M08_Multiplier.md` §2.4.  Scaffold: statements, proofs `sorry`.
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
    (hQ0 : 0 ≤ Q) (hC' : 0 ≤ C') (hβ : ∀ i ∈ F, t ≤ β i) (hr : ∀ i ∈ F, 0 ≤ r i)
    (hQ : ∀ n : ℕ, ∑ i ∈ F.filter (fun i ↦ 2 ^ n * t ≤ β i ∧ β i < 2 ^ (n + 1) * t),
      (r i / β i) ^ 2 ≤ Q)
    (hmax : ∀ n : ℕ, ∀ i ∈ F, 2 ^ n * t ≤ β i → β i < 2 ^ (n + 1) * t →
      r i / β i ≤ C' * ((2 : ℝ) ^ (-α)) ^ n) :
    ∑ i ∈ F, (r i / β i) ^ 3 ≤ C' * Q / (1 - (2 : ℝ) ^ (-α)) := by
  set θ := (2 : ℝ) ^ (-α) with hθ
  have hθ0 : 0 ≤ θ := by positivity
  have hθ1 : θ < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hβpos : ∀ i ∈ F, 0 < β i := fun i hi ↦ ht.trans_le (hβ i hi)
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
          have h0 : 0 ≤ r i / β i := div_nonneg (hr i hi'.1) (hβpos i hi'.1).le
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

/-- **Area-counting near-field lemma (plane)** — replaces the paper's Lemma 3. -/
theorem nearField_sum_le_plane (Cd : ℝ≥0) (R₀ η A δ : ℝ) (hη : 0 < η) (hδ : 0 < δ) :
    ∃ C : ℝ, ∀ (ν : Measure ℂ) (N : ℕ) (R : ℕ → Set ℂ) (c : ℕ → ℂ),
      MeasClassPlane ν Cd R₀ → IsCells univ dist (massRadius ν) ν N η A R c → ∀ z : ℂ,
      ∀ F : Finset ℕ, (∀ i ∈ F, δ * massRadius ν z ≤ dist z (c i) ∧ dist z (c i) ≤ 1 / 4 ∧
          A * massRadius ν (c i) ≤ dist z (c i)) →
        ∑ i ∈ F, (massRadius ν (c i) / dist z (c i)) ^ 3 ≤ C := sorry

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
  set C' := max Cdec (C₁ / δ) * δ ^ (-α) with hC'
  refine ⟨C' * Q / (1 - (2 : ℝ) ^ (-α)), ?_⟩
  intro ν N R c hν hC z hz F hF
  have hci := hC.center_mem'
  have hρ : ∀ w ∈ 𝔻, 0 < massRadiusDisc ν w := fun w hw ↦ (hcl ν hν w hw w hw).1
  have hρz := hρ z hz
  have hA : η / 2 ≤ A := hC.half_le_A_disc (i := 0) (hρ _ (hci 0)) hη
  set t := δ * massRadiusDisc ν z with ht
  have ht0 : 0 < t := by positivity
  refine dyadic_sum_le (r := fun i ↦ massRadiusDisc ν (c i)) (β := fun i ↦ hypDist z (c i))
    ht0 hα (by positivity) (by positivity) (fun i hi ↦ (hF i hi).1)
    (fun i _ ↦ (hρ _ (hci i)).le) ?_ ?_
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
    calc ∑ i ∈ Fn, (massRadiusDisc ν (c i) / hypDist z (c i)) ^ 2
        ≤ ∑ i ∈ Fn, (massRadiusDisc ν (c i)) ^ 2 / (2 ^ n * t) ^ 2 :=
          Finset.sum_le_sum fun i hi ↦ by
            have hi' := Finset.mem_filter.1 hi
            rw [div_pow]
            gcongr
            exact hi'.2.1
      _ = (∑ i ∈ Fn, (massRadiusDisc ν (c i)) ^ 2) / (2 ^ n * t) ^ 2 := by
          rw [Finset.sum_div]
      _ ≤ b ^ 2 * Real.exp 3 / η ^ 2 / (2 ^ n * t) ^ 2 := by gcongr
      _ = Q := by rw [hb, hQ]; field_simp; ring
  · -- geometric decay of the ratio
    intro n i hi hlo hhi
    have hβ := hF i hi
    have hβpos : 0 < hypDist z (c i) := ht0.trans_le hβ.1
    have hθ : (1 / (2 ^ n * δ)) ^ α = ((2 : ℝ) ^ (-α)) ^ n * δ ^ (-α) :=
      one_div_two_pow_mul_rpow hδ n
    by_cases hcase : massRadiusDisc ν z ≤ hypDist z (c i)
    · have h1 := hdec ν hν z hz (c i) (hci i) hcase hβ.2.1
      have h2 : massRadiusDisc ν z / hypDist z (c i) ≤ 1 / (2 ^ n * δ) := by
        rw [div_le_div_iff₀ hβpos (by positivity)]
        have : 2 ^ n * t ≤ hypDist z (c i) := hlo
        rw [ht] at this; nlinarith
      have h3 : (massRadiusDisc ν z / hypDist z (c i)) ^ α ≤ (1 / (2 ^ n * δ)) ^ α :=
        Real.rpow_le_rpow (by positivity) h2 hα.le
      rw [hθ] at h3
      calc massRadiusDisc ν (c i) / hypDist z (c i)
          ≤ Cdec * (massRadiusDisc ν z / hypDist z (c i)) ^ α := h1
        _ ≤ Cdec * (((2 : ℝ) ^ (-α)) ^ n * δ ^ (-α)) := by gcongr
        _ ≤ max Cdec (C₁ / δ) * δ ^ (-α) * ((2 : ℝ) ^ (-α)) ^ n := by
            have : Cdec ≤ max Cdec (C₁ / δ) := le_max_left _ _
            have h0 : 0 ≤ ((2 : ℝ) ^ (-α)) ^ n * δ ^ (-α) := by positivity
            nlinarith
    · push Not at hcase
      have hle : hypDist (c i) z ≤ 1 * max (massRadiusDisc ν (c i)) (massRadiusDisc ν z) := by
        rw [hypDist_comm, one_mul]; exact hcase.le.trans (le_max_right _ _)
      have h1 := (hcl ν hν (c i) (hci i) z hz).2.2 hle
      have h2 : massRadiusDisc ν (c i) / hypDist z (c i) ≤ C₁ / δ := by
        rw [div_le_div_iff₀ hβpos hδ]
        have := hβ.1; rw [ht] at this; nlinarith
      have h3 : 1 ≤ ((2 : ℝ) ^ (-α)) ^ n * δ ^ (-α) := by
        rw [← hθ]
        apply Real.one_le_rpow _ hα.le
        rw [le_div_iff₀ (by positivity), one_mul]
        have : 2 ^ n * t ≤ hypDist z (c i) := hlo
        rw [ht] at this
        have : 2 ^ n * δ * massRadiusDisc ν z < massRadiusDisc ν z := by nlinarith
        nlinarith
      calc massRadiusDisc ν (c i) / hypDist z (c i) ≤ C₁ / δ := h2
        _ ≤ C₁ / δ * (((2 : ℝ) ^ (-α)) ^ n * δ ^ (-α)) := le_mul_of_one_le_right (by positivity) h3
        _ ≤ max Cdec (C₁ / δ) * δ ^ (-α) * ((2 : ℝ) ^ (-α)) ^ n := by
            have : C₁ / δ ≤ max Cdec (C₁ / δ) := le_max_right _ _
            have h0 : 0 ≤ ((2 : ℝ) ^ (-α)) ^ n * δ ^ (-α) := by positivity
            nlinarith

/-- Far field (plane). -/
theorem farField_sum_le_plane (Cd : ℝ≥0) (R₀ η A M₀ : ℝ) (hη : 0 < η) (hM₀ : 0 < M₀) :
    ∃ C : ℝ, ∀ (ν : Measure ℂ) (N : ℕ) (R : ℕ → Set ℂ) (c : ℕ → ℂ),
      MeasClassPlane ν Cd R₀ → IsCells univ dist (massRadius ν) ν N η A R c → ∀ z : ℂ,
      ∀ F : Finset ℕ, (∀ i ∈ F, M₀ ≤ dist z (c i) ∧ 2 * A * massRadius ν (c i) ≤ dist z (c i)) →
        ∑ i ∈ F, (massRadius ν (c i) / dist z (c i)) ^ 3 ≤ C := sorry

/-- Far field (disc): the Forelli–Rudin sum. -/
theorem farField_sum_le_disc (Cd : ℝ≥0) (R₀ η A M₀ : ℝ) (hη : 0 < η) (hM₀ : 0 < M₀) :
    ∃ C : ℝ, ∀ (ν : Measure ℂ) (N : ℕ) (R : ℕ → Set ℂ) (c : ℕ → ℂ),
      MeasClassDisc ν Cd R₀ → IsCells 𝔻 hypDist (massRadiusDisc ν) ν N η A R c → ∀ z ∈ 𝔻,
      ∀ F : Finset ℕ, (∀ i ∈ F, M₀ ≤ hypDist z (c i)) →
        ∑ i ∈ F, (1 - ‖z‖ ^ 2) * ((1 - ‖c i‖ ^ 2) * massRadiusDisc ν (c i)) ^ 2 /
          ‖1 - conj z * c i‖ ^ 3 ≤ C := sorry

end OC
