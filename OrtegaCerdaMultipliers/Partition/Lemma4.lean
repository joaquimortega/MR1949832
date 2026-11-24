/-
Copyright (c) 2026 Joaquim Ortega-Cerdà. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joaquim Ortega-Cerdà
-/
import OrtegaCerdaMultipliers.Partition.Cayley
import OrtegaCerdaMultipliers.Doubling.Quant
import OrtegaCerdaMultipliers.Partition.LineCuts

/-!
# M05 (Partition) — Lemma 4: partitions into pieces of mass `N`

See `blueprint/M05_Partition.md` §2.3.  Proofs complete (they use the upstream M01/M03 interfaces).

`IsMassPartition`, `lemma4_plane`, `lemma4_disc` (horocyclic boxes), `lemma4_line`, and the
quantitative forms `lemma4_plane_quant`, `lemma4_disc_quant` requested by M08 §4.1 (constants
depending only on `(C_d, R₀)`, chosen before the measure).
-/

open MeasureTheory Metric Set Complex
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace OC

/-- `R : ℕ → Set ℂ` partitions `Ω` into measurable pieces of `μ`-mass `N`; each piece has
`d`-diameter `≤ A ρ(z)` (any `z` in it) and contains the `d`-ball of radius `a ρ(c)` around one
of its points `c`. -/
structure IsMassPartition (μ : Measure ℂ) (Ω : Set ℂ) (d : ℂ → ℂ → ℝ) (ρ : ℂ → ℝ) (N : ℕ)
    (a A : ℝ) (R : ℕ → Set ℂ) : Prop where
  measurableSet : ∀ i, MeasurableSet (R i)
  pairwise_disjoint : Pairwise (Function.onFun Disjoint R)
  iUnion_eq : ⋃ i, R i = Ω
  measure_eq : ∀ i, μ (R i) = N
  dist_le : ∀ i, ∀ z ∈ R i, ∀ w ∈ R i, d z w ≤ A * ρ z
  inner : ∀ i, ∃ c ∈ R i, {w | w ∈ Ω ∧ d c w < a * ρ c} ⊆ R i

/-! ### Helpers for the constructions (M05 §3.6, §3.8) -/

theorem l4_midThird_subset {x₁ x₂ : ℝ} (hx : x₁ ≤ x₂) (y₁ y₂ : ℝ) :
    midThird x₁ x₂ y₁ y₂ ⊆ rect x₁ x₂ y₁ y₂ := by
  unfold midThird
  split_ifs
  · exact rect_subset_rect (by linarith) (by linarith) le_rfl le_rfl
  · exact rect_subset_rect le_rfl le_rfl (by linarith) (by linarith)

theorem l4_measurableSet_midThird (x₁ x₂ y₁ y₂ : ℝ) : MeasurableSet (midThird x₁ x₂ y₁ y₂) := by
  unfold midThird; split_ifs <;> exact measurableSet_rect _ _ _ _

/-- Iterated doubling up to a scale. -/
theorem l4_iter {f : ℝ → ℝ≥0∞} {C : ℝ≥0∞} {R₁ : ℝ}
    (hf : ∀ r, 0 < r → r ≤ R₁ → f (2 * r) ≤ C * f r) :
    ∀ (k : ℕ) (r : ℝ), 0 < r → 2 ^ k * r ≤ 2 * R₁ → f (2 ^ k * r) ≤ C ^ k * f r := by
  intro k
  induction k with
  | zero => intro r _ _; simp
  | succ k ih =>
    intro r hr hk
    have hpos : 0 < 2 ^ k * r := by positivity
    have h1 : 2 ^ k * r ≤ R₁ := by rw [pow_succ] at hk; linarith
    calc f (2 ^ (k + 1) * r) = f (2 * (2 ^ k * r)) := by congr 1; ring
      _ ≤ C * f (2 ^ k * r) := hf _ hpos h1
      _ ≤ C * (C ^ k * f r) := by gcongr; exact ih r hr (by linarith)
      _ = C ^ (k + 1) * f r := by ring

/-- A countable family of finite partitions of disjoint blocks, reindexed by `ℕ`. -/
theorem l4_sigma_partition {n : ℤ × ℤ → ℕ} (hn : ∀ jk, 1 ≤ n jk) (B : ℤ × ℤ → Set ℂ)
    (hB : Pairwise (Function.onFun Disjoint B)) (f : (Σ jk : ℤ × ℤ, Fin (n jk)) → Set ℂ)
    (hf : ∀ jk, Pairwise (Function.onFun Disjoint fun a : Fin (n jk) ↦ f ⟨jk, a⟩))
    (hfB : ∀ jk, ⋃ a, f ⟨jk, a⟩ = B jk) :
    ∃ e : ℕ ≃ (Σ jk : ℤ × ℤ, Fin (n jk)), Pairwise (Function.onFun Disjoint fun i ↦ f (e i)) ∧
      ⋃ i, f (e i) = ⋃ jk, B jk := by
  have : Infinite (Σ jk : ℤ × ℤ, Fin (n jk)) :=
    Infinite.of_injective (fun jk : ℤ × ℤ ↦ (⟨jk, ⟨0, hn jk⟩⟩ : Σ jk : ℤ × ℤ, Fin (n jk)))
      (fun a b h ↦ congrArg Sigma.fst h)
  obtain ⟨e⟩ := nonempty_equiv_of_countable (α := ℕ) (β := Σ jk : ℤ × ℤ, Fin (n jk))
  have hsub : ∀ jk a, f ⟨jk, a⟩ ⊆ B jk := fun jk a ↦
    (hfB jk) ▸ subset_iUnion (fun a ↦ f ⟨jk, a⟩) a
  have hfd : Pairwise (Function.onFun Disjoint f) := by
    rintro ⟨jk, a⟩ ⟨jk', b⟩ hne
    by_cases h : jk = jk'
    · subst h
      have : a ≠ b := fun hab ↦ hne (by rw [hab])
      exact hf jk this
    · exact (hB h).mono (hsub jk a) (hsub jk' b)
  refine ⟨e, fun i j hij ↦ hfd (fun h ↦ hij (e.injective h)), ?_⟩
  rw [e.surjective.iUnion_comp f, iUnion_sigma]
  exact iUnion_congr hfB

/-- Growth with an explicit radius in the plane: `N + 1` disjoint balls of radius `R₀`. -/
theorem l4_growth_plane {ν : Measure ℂ} {R₀ : ℝ} (hR₀ : 0 < R₀)
    (hmass : ∀ z, 1 < ν (ball z R₀)) (N : ℕ) (z : ℂ) :
    (N : ℝ≥0∞) < ν (ball z (((N : ℝ) + 1) * R₀)) := by
  set c : ℕ → ℂ := fun k ↦ z + (((2 * k - N) * R₀ : ℝ) : ℂ) with hc
  have hdc : ∀ k k' : ℕ, dist (c k) (c k') = |(2 * (k : ℝ) - N) * R₀ - (2 * k' - N) * R₀| := by
    intro k k'
    simp only [hc]
    rw [dist_add_left, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have hdisj : (↑(Finset.range (N + 1)) : Set ℕ).PairwiseDisjoint fun k ↦ ball (c k) R₀ := by
    intro k _ k' _ hkk'
    simp only [Function.onFun]
    rw [Set.disjoint_left]
    intro w hw hw'
    rw [mem_ball] at hw hw'
    have h := (dist_triangle (c k) w (c k')).trans_lt
      (add_lt_add (by rwa [dist_comm] at hw) hw')
    rw [hdc] at h
    have habs : 2 * R₀ ≤ |(2 * (k : ℝ) - N) * R₀ - (2 * k' - N) * R₀| := by
      rw [show (2 * (k : ℝ) - N) * R₀ - (2 * k' - N) * R₀ = 2 * R₀ * ((k : ℝ) - k') by ring,
        abs_mul, abs_of_pos (by positivity : 0 < 2 * R₀)]
      have : (1 : ℝ) ≤ |(k : ℝ) - k'| := by
        rcases lt_or_gt_of_ne hkk' with h | h
        · have : (k : ℝ) + 1 ≤ k' := by exact_mod_cast h
          rw [abs_of_neg (by linarith)]; linarith
        · have : (k' : ℝ) + 1 ≤ k := by exact_mod_cast h
          rw [abs_of_pos (by linarith)]; linarith
      nlinarith
    linarith
  have hsub : (⋃ k ∈ Finset.range (N + 1), ball (c k) R₀) ⊆ ball z (((N : ℝ) + 1) * R₀) := by
    refine iUnion₂_subset fun k hk ↦ ?_
    have hk' : (k : ℝ) ≤ N := by
      have := Finset.mem_range.1 hk; exact_mod_cast Nat.lt_succ_iff.1 this
    intro w hw
    rw [mem_ball] at hw ⊢
    have h1 : dist (c k) z ≤ N * R₀ := by
      simp only [hc]
      rw [dist_comm, dist_self_add_right, Complex.norm_real, Real.norm_eq_abs, abs_mul,
        abs_of_pos hR₀]
      have : |2 * (k : ℝ) - N| ≤ N := by
        rw [abs_le]; constructor <;> linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]
      nlinarith
    linarith [dist_triangle w (c k) z]
  calc (N : ℝ≥0∞) < ((N + 1 : ℕ) : ℝ≥0∞) := by exact_mod_cast Nat.lt_succ_self N
    _ = ∑ _k ∈ Finset.range (N + 1), (1 : ℝ≥0∞) := by simp
    _ ≤ ∑ k ∈ Finset.range (N + 1), ν (ball (c k) R₀) :=
        Finset.sum_le_sum fun k _ ↦ (hmass _).le
    _ = ν (⋃ k ∈ Finset.range (N + 1), ball (c k) R₀) :=
        (measure_biUnion_finset hdisj fun k _ ↦ measurableSet_ball).symm
    _ ≤ _ := measure_mono hsub

theorem l4_rect_subset_ball (x₁ x₂ y₁ y₂ : ℝ) :
    rect x₁ x₂ y₁ y₂ ⊆ ball 0 (|x₁| + |x₂| + |y₁| + |y₂| + 1) := by
  rintro z ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
  rw [mem_ball_zero_iff]
  have h0 := Complex.norm_le_abs_re_add_abs_im z
  have : |z.re| ≤ |x₁| + |x₂| := by
    rw [abs_le]
    constructor <;> linarith [neg_abs_le x₁, le_abs_self x₂, abs_nonneg x₁, abs_nonneg x₂]
  have : |z.im| ≤ |y₁| + |y₂| := by
    rw [abs_le]
    constructor <;> linarith [neg_abs_le y₁, le_abs_self y₂, abs_nonneg y₁, abs_nonneg y₂]
  linarith

/-- The mass radius is at most `r` once the ball of radius `r` has mass `≥ 1`. -/
theorem l4_massRadius_le {ν : Measure ℂ} {z : ℂ} {r : ℝ} (hr : 0 < r) (h : 1 ≤ ν (ball z r)) :
    massRadius ν z ≤ r :=
  csInf_le ⟨0, fun _ hx ↦ hx.1.le⟩ ⟨hr, h⟩

theorem l4_massRadiusDisc_le {ν : Measure ℂ} {z : ℂ} {r : ℝ} (hr : 0 < r)
    (h : 1 ≤ ν (hypBall z r)) : massRadiusDisc ν z ≤ r :=
  csInf_le ⟨0, fun _ hx ↦ hx.1.le⟩ ⟨hr, h⟩

/-- `μ = N • (N⁻¹ • μ)`. -/
theorem l4_smul_apply {ν : Measure ℂ} {N : ℕ} (hN : 1 ≤ N) (s : Set ℂ) :
    ν s = N * ((N : ℝ≥0∞)⁻¹ • ν) s := by
  have hNne : (N : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  rw [smul_apply, smul_eq_mul, ← mul_assoc,
    ENNReal.mul_inv_cancel hNne (ENNReal.natCast_ne_top N), one_mul]

/-- `C₁ ^ k ≤ ⌈C₁ ^ k⌉₊` in `ℝ≥0∞`. -/
theorem l4_coe_pow_le_ceil (C₁ : ℝ≥0) (k : ℕ) :
    (C₁ : ℝ≥0∞) ^ k ≤ ((⌈(C₁ : ℝ) ^ k⌉₊ : ℕ) : ℝ≥0∞) := by
  rw [← ENNReal.coe_pow, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_natCast]
  exact ENNReal.ofReal_le_ofReal (by push_cast; exact Nat.le_ceil _)

/-- The mass of a piece of the normalised measure `N⁻¹ ν`. -/
theorem l4_inv_smul_apply {ν : Measure ℂ} {N : ℕ} (s : Set ℂ) :
    ((N : ℝ≥0∞)⁻¹ • ν) s = (N : ℝ≥0∞)⁻¹ * ν s := by
  rw [smul_apply, smul_eq_mul]

/-- Assembling the pieces: `ν`-mass-one rectangles inside the blocks
`[X j k, X j (k+1)) × [lo j, hi j)`, reindexed by `ℕ`. -/
theorem l4_assemble {ν : Measure ℂ} {P : ℝ → ℝ → ℝ → ℝ → Prop} {C₀ : ℕ} {L : ℝ}
    (hpart : ∀ (n : ℕ) (x₁ x₂ y₁ y₂ : ℝ), 1 ≤ n → IsRectLE 3 x₁ x₂ y₁ y₂ → P x₁ x₂ y₁ y₂ →
      ν (rect x₁ x₂ y₁ y₂) = n → ∃ q : Fin n → ℝ × ℝ × ℝ × ℝ,
        Pairwise (Function.onFun Disjoint fun i ↦ rect (q i).1 (q i).2.1 (q i).2.2.1 (q i).2.2.2) ∧
        (⋃ i, rect (q i).1 (q i).2.1 (q i).2.2.1 (q i).2.2.2) = rect x₁ x₂ y₁ y₂ ∧
        ∀ i, RectGood ν P C₀ L (q i))
    (X : ℤ → ℤ → ℝ) (lo hi : ℤ → ℝ) (n : ℤ → ℤ → ℕ) (hn1 : ∀ j k, 1 ≤ n j k)
    (hXmono : ∀ j, StrictMono (X j)) (hlohi : ∀ j j', j < j' → hi j ≤ lo j')
    (hblock : ∀ j k, IsRectLE 3 (X j k) (X j (k + 1)) (lo j) (hi j) ∧
      P (X j k) (X j (k + 1)) (lo j) (hi j) ∧
      ν (rect (X j k) (X j (k + 1)) (lo j) (hi j)) = n j k) :
    ∃ g : ℕ → ℝ × ℝ × ℝ × ℝ,
      Pairwise (Function.onFun Disjoint fun i ↦ rect (g i).1 (g i).2.1 (g i).2.2.1 (g i).2.2.2) ∧
      (⋃ i, rect (g i).1 (g i).2.1 (g i).2.2.1 (g i).2.2.2) =
        ⋃ jk : ℤ × ℤ, rect (X jk.1 jk.2) (X jk.1 (jk.2 + 1)) (lo jk.1) (hi jk.1) ∧
      ∀ i, RectGood ν P C₀ L (g i) := by
  set nn : ℤ × ℤ → ℕ := fun jk ↦ n jk.1 jk.2
  set B : ℤ × ℤ → Set ℂ := fun jk ↦
    rect (X jk.1 jk.2) (X jk.1 (jk.2 + 1)) (lo jk.1) (hi jk.1) with hB
  have hblock' : ∀ jk : ℤ × ℤ, ∃ q : Fin (nn jk) → ℝ × ℝ × ℝ × ℝ,
      Pairwise (Function.onFun Disjoint fun i ↦ rect (q i).1 (q i).2.1 (q i).2.2.1 (q i).2.2.2) ∧
      (⋃ i, rect (q i).1 (q i).2.1 (q i).2.2.1 (q i).2.2.2) = B jk ∧
      ∀ i, RectGood ν P C₀ L (q i) := fun ⟨j, k⟩ ↦
    hpart (n j k) _ _ _ _ (hn1 j k) (hblock j k).1 (hblock j k).2.1 (hblock j k).2.2
  choose q hqdisj hqunion hqgood using hblock'
  have hBdisj : Pairwise (Function.onFun Disjoint B) := by
    rintro ⟨j, k⟩ ⟨j', k'⟩ hne
    simp only [Function.onFun, hB]
    by_cases hj : j = j'
    · subst hj
      have hk : k ≠ k' := fun h ↦ hne (by rw [h])
      rcases lt_or_gt_of_ne hk with h | h
      · exact rect_disjoint_x ((hXmono j).monotone (by omega))
      · exact (rect_disjoint_x ((hXmono j).monotone (by omega))).symm
    · rcases lt_or_gt_of_ne hj with h | h
      · exact rect_disjoint_y (hlohi _ _ h)
      · exact (rect_disjoint_y (hlohi _ _ h)).symm
  set f : (Σ jk : ℤ × ℤ, Fin (nn jk)) → Set ℂ := fun p ↦
    rect (q p.1 p.2).1 (q p.1 p.2).2.1 (q p.1 p.2).2.2.1 (q p.1 p.2).2.2.2
  obtain ⟨e, hedisj, heunion⟩ := l4_sigma_partition (fun jk ↦ hn1 jk.1 jk.2) B hBdisj f
    (fun jk ↦ hqdisj jk) (fun jk ↦ hqunion jk)
  exact ⟨fun i ↦ q (e i).1 (e i).2, hedisj, heunion, fun i ↦ hqgood _ _⟩

/-- Plane: the normalised measure `N⁻¹ ν` is in the class `MeasClassM` with radius `(N+1) R₀`. -/
theorem l4_plane_mu {ν : Measure ℂ} {Cd : ℝ≥0} {R₀ : ℝ} {N : ℕ} (hN : 1 ≤ N) (hR₀ : 0 < R₀)
    (hν : MeasClassPlane ν Cd R₀) :
    MeasClassM ((N : ℝ≥0∞)⁻¹ • ν) Cd (((N : ℝ) + 1) * R₀) ∧
      ∀ s : Set ℂ, Bornology.IsBounded s → ((N : ℝ≥0∞)⁻¹ • ν) s < ∞ := by
  have hNne : (N : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hNtop : (N : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top N
  have hfinν : ∀ s : Set ℂ, Bornology.IsBounded s → ν s < ∞ := fun s hs ↦ by
    obtain ⟨r, hr⟩ := hs.subset_closedBall 0
    exact (measure_mono hr).trans_lt (hν.finite _ (isCompact_closedBall 0 r))
  have hfin'b : ∀ s : Set ℂ, Bornology.IsBounded s → ((N : ℝ≥0∞)⁻¹ • ν) s < ∞ := fun s hs ↦ by
    rw [l4_inv_smul_apply]
    exact ENNReal.mul_lt_top (ENNReal.inv_lt_top.2 (by positivity)) (hfinν s hs)
  refine ⟨⟨fun z r hr h2r ↦ ?_, fun z ↦ ?_, fun z r ↦ hfin'b _ Metric.isBounded_ball⟩, hfin'b⟩
  · rw [l4_inv_smul_apply, l4_inv_smul_apply, mul_left_comm]
    gcongr
    exact hν.doubling z r hr h2r
  · rw [l4_inv_smul_apply]
    calc (1 : ℝ≥0∞) = (N : ℝ≥0∞)⁻¹ * N := (ENNReal.inv_mul_cancel hNne hNtop).symm
      _ ≤ (N : ℝ≥0∞)⁻¹ * ν (ball z (((N : ℝ) + 1) * R₀)) := by
          gcongr; exact (l4_growth_plane hR₀ hν.mass N z).le

/-- Plane: a doubling measure of locally finite mass does not charge horizontal or vertical
lines. -/
theorem l4_plane_null {μ : Measure ℂ} (hd : IsLocallyDoubling μ)
    (hfin : ∀ z r, μ (ball z r) < ∞) :
    (∀ x : ℝ, μ {w | w.re = x} = 0) ∧ ∀ y : ℝ, μ {w | w.im = y} = 0 := by
  refine ⟨fun x ↦ ?_, fun y ↦ ?_⟩
  · have : {w : ℂ | w.re = x} = {z | ∃ t : ℝ, z = (x : ℂ) + t * I} := by
      ext w
      simp only [mem_ofPred_eq]
      constructor
      · intro h; exact ⟨w.im, Complex.ext (by simp [h]) (by simp)⟩
      · rintro ⟨t, rfl⟩; simp
    rw [this]
    exact measure_eq_zero_of_isPorous_plane hd hfin (isPorous_line _ _)
  · have : {w : ℂ | w.im = y} = {z | ∃ t : ℝ, z = (y : ℂ) * I + t * 1} := by
      ext w
      simp only [mem_ofPred_eq]
      constructor
      · intro h; exact ⟨w.re, Complex.ext (by simp) (by simp [h])⟩
      · rintro ⟨t, rfl⟩; simp
    rw [this]
    exact measure_eq_zero_of_isPorous_plane hd hfin (isPorous_line _ _)

/-- Plane: coarse rows `[jS, (j+1)S)`, cut into blocks of integer mass. -/
theorem l4_plane_rows {μ : Measure ℂ} {R' S : ℝ} (hS : S = 2 * R') (hS0 : 0 < S)
    (hre : ∀ x : ℝ, μ {w | w.re = x} = 0) (hmass : ∀ z, 1 ≤ μ (ball z R'))
    (hfinR : ∀ x₁ x₂ y₁ y₂ : ℝ, μ (rect x₁ x₂ y₁ y₂) < ∞) (j : ℤ) :
    ∃ x : ℤ → ℝ, StrictMono x ∧
      (∀ k, S ≤ x (k + 1) - x k ∧ x (k + 1) - x k ≤ 2 * S) ∧
      (∀ t : ℝ, ∃ k, t ∈ Ico (x k) (x (k + 1))) ∧
      ∀ k, ∃ n : ℕ, 1 ≤ n ∧ μ (rect (x k) (x (k + 1)) (j * S) ((j + 1) * S)) = n := by
  refine exists_strip_cuts hre hS0 (fun a b ↦ hfinR _ _ _ _) fun a ↦ ?_
  refine (hmass ((a + R' : ℝ) + ((j * S + R' : ℝ) : ℂ) * I)).trans (measure_mono ?_)
  intro w hw
  have h1 := (Complex.abs_re_le_norm _).trans_lt (mem_ball.1 hw |>.trans_le' (by
    rw [Complex.dist_eq]))
  have h2 := (Complex.abs_im_le_norm _).trans_lt (mem_ball.1 hw |>.trans_le' (by
    rw [Complex.dist_eq]))
  simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
    Complex.I_im] at h1 h2
  rw [abs_lt] at h1 h2
  refine ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

/-- Plane: a rectangle of mass `> C₀` has a middle third of mass `> 1`. -/
theorem l4_plane_C0 {μ : Measure ℂ} {S : ℝ} {C₁ : ℝ≥0} {C₀ : ℕ}
    (hpow : ∀ z (k : ℕ) r, 0 < r → 2 ^ k * r ≤ 2 * (16 * S) →
      μ (ball z (2 ^ k * r)) ≤ (C₁ : ℝ≥0∞) ^ k * μ (ball z r))
    (hC₁5 : (C₁ : ℝ≥0∞) ^ 5 ≤ (C₀ : ℝ≥0∞)) (x₁ x₂ y₁ y₂ : ℝ) (hg : IsRectLE 3 x₁ x₂ y₁ y₂)
    (hP : x₂ - x₁ ≤ 2 * S ∧ y₂ - y₁ ≤ 2 * S) (hlt : (C₀ : ℝ≥0∞) < μ (rect x₁ x₂ y₁ y₂)) :
    1 < μ (midThird x₁ x₂ y₁ y₂) := by
  obtain ⟨p, r, hr, h6r, hin, hout⟩ := rect_inner_outer (by norm_num : (1 : ℝ) ≤ 3) hg
  have hrS : r ≤ S / 3 := by
    have := max_le hP.1 hP.2; linarith
  have h32 : μ (rect x₁ x₂ y₁ y₂) ≤ (C₁ : ℝ≥0∞) ^ 5 * μ (midThird x₁ x₂ y₁ y₂) := by
    calc μ (rect x₁ x₂ y₁ y₂) ≤ μ (ball p (2 ^ 5 * r)) :=
          measure_mono (hout.trans (ball_subset_ball (by nlinarith)))
      _ ≤ (C₁ : ℝ≥0∞) ^ 5 * μ (ball p r) := hpow p 5 r hr (by nlinarith)
      _ ≤ (C₁ : ℝ≥0∞) ^ 5 * μ (midThird x₁ x₂ y₁ y₂) := by gcongr
  by_contra hle
  push Not at hle
  have := hlt.trans_le (h32.trans (by
    calc (C₁ : ℝ≥0∞) ^ 5 * μ (midThird x₁ x₂ y₁ y₂) ≤ (C₁ : ℝ≥0∞) ^ 5 * 1 := by gcongr
      _ ≤ (C₀ : ℝ≥0∞) := by rw [mul_one]; exact hC₁5))
  exact lt_irrefl _ this

/-- Plane: Euclidean doubling at scale `σ` inside admissible rectangles. -/
theorem l4_plane_sigma {μ : Measure ℂ} {S C_E : ℝ} {C₁ : ℝ≥0} (hCE : C_E = (C₁ : ℝ) ^ 3)
    (hpow : ∀ z (k : ℕ) r, 0 < r → 2 ^ k * r ≤ 2 * (16 * S) →
      μ (ball z (2 ^ k * r)) ≤ (C₁ : ℝ≥0∞) ^ k * μ (ball z r)) (x₁ x₂ y₁ y₂ : ℝ)
    (_ : IsRectLE 3 x₁ x₂ y₁ y₂) (hP : x₂ - x₁ ≤ 2 * S ∧ y₂ - y₁ ≤ 2 * S) :
    1 * max (x₂ - x₁) (y₂ - y₁) ≤ max (x₂ - x₁) (y₂ - y₁) ∧
      ∀ w ∈ rect x₁ x₂ y₁ y₂, ∀ r : ℝ, 0 < r → r ≤ max (x₂ - x₁) (y₂ - y₁) →
        μ (ball w (4 * r)) ≤ ENNReal.ofReal C_E * μ (ball w (r / 2)) := by
  refine ⟨by rw [one_mul], fun w _ r hr hrσ ↦ ?_⟩
  have hrS : r ≤ 2 * S := hrσ.trans (max_le hP.1 hP.2)
  have := hpow w 3 (r / 2) (by positivity) (by nlinarith)
  rw [show (2 : ℝ) ^ 3 * (r / 2) = 4 * r by ring] at this
  rw [hCE, ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_coe_nnreal]
  exact this

/-- Plane: the pieces of the partition have `d`-diameter `≤ A' CN ρ_ν`. -/
theorem l4_plane_size {μ ν : Measure ℂ} {S c δ M A' CN : ℝ} {C₁ : ℝ≥0} {C₀ : ℕ}
    {x₁ x₂ y₁ y₂ : ℝ} {T : Set ℂ} (hc : 0 < c) (hδ : 0 < δ) (hM : M = (C₁ : ℝ) ^ 6 * C₀)
    (hA'1 : 1 ≤ A') (hA'2 : (M / c) ^ (1 / δ) ≤ A')
    (hpow : ∀ z (k : ℕ) r, 0 < r → 2 ^ k * r ≤ 2 * (16 * S) →
      μ (ball z (2 ^ k * r)) ≤ (C₁ : ℝ≥0∞) ^ k * μ (ball z r))
    (hlow : ∀ z r, massRadius μ z ≤ r → r ≤ 12 * S →
      ENNReal.ofReal (c * (r / massRadius μ z) ^ δ) ≤ μ (ball z r))
    (hρ' : ∀ z, 0 < massRadius μ z) (hCNz : ∀ z, massRadius μ z ≤ CN * massRadius ν z)
    (hg : IsRectLE 3 x₁ x₂ y₁ y₂) (hPb : x₂ - x₁ ≤ 2 * S ∧ y₂ - y₁ ≤ 2 * S)
    (hμb : μ (rect x₁ x₂ y₁ y₂) ≤ C₀) (hsub : T ⊆ rect x₁ x₂ y₁ y₂) :
    ∀ z ∈ T, ∀ w ∈ T, dist z w ≤ A' * CN * massRadius ν z := by
  have hM0 : 0 ≤ M := by rw [hM]; positivity
  obtain ⟨p, r, hr, h6r, hin, hout⟩ := rect_inner_outer (by norm_num : (1 : ℝ) ≤ 3) hg
  have hrS : r ≤ S / 3 := by
    have := max_le hPb.1 hPb.2; linarith
  have hgx := hg.1
  intro z hz w hw
  have hzp : dist z p < 18 * r := by
    have := hout (hsub hz); rw [mem_ball] at this; linarith
  have hwp : dist w p < 18 * r := by
    have := hout (hsub hw); rw [mem_ball] at this; linarith
  have hzw : dist z w < 36 * r := by
    linarith [dist_triangle z p w, dist_comm w p]
  have hball : μ (ball z (36 * r)) ≤ ENNReal.ofReal M := by
    calc μ (ball z (36 * r)) ≤ μ (ball p (2 ^ 6 * r)) := by
          refine measure_mono fun y hy ↦ ?_
          rw [mem_ball] at hy ⊢
          linarith [dist_triangle y z p]
      _ ≤ (C₁ : ℝ≥0∞) ^ 6 * μ (ball p r) := hpow p 6 r hr (by nlinarith)
      _ ≤ (C₁ : ℝ≥0∞) ^ 6 * C₀ := by
          gcongr
          exact (measure_mono (hin.trans (l4_midThird_subset hgx.le _ _))).trans hμb
      _ = ENNReal.ofReal M := by
          rw [hM, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity),
            ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_natCast]
  have h36 : 36 * r ≤ A' * massRadius μ z := by
    rcases le_or_gt (massRadius μ z) (36 * r) with hle | hlt
    · have h1 := (hlow z (36 * r) hle (by linarith)).trans hball
      rw [ENNReal.ofReal_le_ofReal_iff hM0] at h1
      exact (l4_le_of_rpow hc hδ (hρ' z) (by positivity) h1).trans
        (mul_le_mul_of_nonneg_right hA'2 (hρ' z).le)
    · exact hlt.le.trans (le_mul_of_one_le_left (hρ' z).le hA'1)
  calc dist z w ≤ A' * massRadius μ z := hzw.le.trans h36
    _ ≤ A' * (CN * massRadius ν z) :=
        mul_le_mul_of_nonneg_left (hCNz z) (by linarith)
    _ = A' * CN * massRadius ν z := by ring

/-- Plane: every piece contains the ball of radius `ρ_ν(p) / (6 L)` around a point `p`. -/
theorem l4_plane_fat {ν : Measure ℂ} {N : ℕ} {L : ℝ} {x₁ x₂ y₁ y₂ : ℝ} (hN : 1 ≤ N)
    (hL1 : 1 ≤ L) (hLe : IsRectLE L x₁ x₂ y₁ y₂) (hμ1 : ν (rect x₁ x₂ y₁ y₂) = N) :
    ∃ c ∈ rect x₁ x₂ y₁ y₂, {w | w ∈ (univ : Set ℂ) ∧ dist c w < 1 / (6 * L) * massRadius ν c} ⊆
      rect x₁ x₂ y₁ y₂ := by
  obtain ⟨p, r, hr, -, hin, hout⟩ := rect_inner_outer hL1 hLe
  have hmid := l4_midThird_subset (x₁ := x₁) hLe.1.le y₁ y₂
  have hpP : p ∈ rect x₁ x₂ y₁ y₂ := hmid (hin (mem_ball_self hr))
  have hρ : massRadius ν p ≤ 6 * L * r := by
    refine l4_massRadius_le (by positivity) ?_
    calc (1 : ℝ≥0∞) ≤ N := by exact_mod_cast hN
      _ = ν (rect x₁ x₂ y₁ y₂) := hμ1.symm
      _ ≤ ν (ball p (6 * L * r)) := measure_mono hout
  refine ⟨p, hpP, fun w ⟨_, hw⟩ ↦ hmid (hin ?_)⟩
  rw [mem_ball, dist_comm]
  calc dist p w < 1 / (6 * L) * massRadius ν p := hw
    _ ≤ 1 / (6 * L) * (6 * L * r) := by gcongr
    _ = r := by field_simp

/-- Plane: the partition of `ℂ` into rectangles of mass one for `μ` (admissible rectangles have
sides `≤ 2 S`), with side ratio `≤ rectRatioBound C₀ C_E 1`. -/
theorem l4_plane_pieces {μ : Measure ℂ} {Cd : ℝ≥0} {R' S C_E : ℝ} {C₁ : ℝ≥0} {C₀ : ℕ}
    (hS : S = 2 * R') (hR'0 : 0 < R') (hclass : MeasClassM μ Cd R')
    (hfinB : ∀ s : Set ℂ, Bornology.IsBounded s → μ s < ∞)
    (hC₁ : ∀ μ' : Measure ℂ, IsLocDoublingMWith μ' Cd → ∀ x : ℂ, ∀ r : ℝ, 0 < r →
      r ≤ 16 * S → μ' (ball x (2 * r)) ≤ C₁ * μ' (ball x r))
    (hC₀ : (C₁ : ℝ≥0∞) ^ 5 ≤ (C₀ : ℝ≥0∞)) (hCE : C_E = (C₁ : ℝ) ^ 3) :
    ∃ g : ℕ → ℝ × ℝ × ℝ × ℝ,
      Pairwise (Function.onFun Disjoint fun i ↦ rect (g i).1 (g i).2.1 (g i).2.2.1 (g i).2.2.2) ∧
      (⋃ i, rect (g i).1 (g i).2.1 (g i).2.2.1 (g i).2.2.2) = univ ∧
      ∀ i, RectGood μ (fun x₁ x₂ y₁ y₂ ↦ x₂ - x₁ ≤ 2 * S ∧ y₂ - y₁ ≤ 2 * S) C₀
        (rectRatioBound C₀ C_E 1) (g i) := by
  have hS0 : 0 < S := by rw [hS]; positivity
  obtain ⟨hre, him⟩ := l4_plane_null ⟨Cd, hclass.doubling⟩
    (fun z r ↦ hfinB _ Metric.isBounded_ball)
  have hfinR : ∀ x₁ x₂ y₁ y₂ : ℝ, μ (rect x₁ x₂ y₁ y₂) < ∞ := fun x₁ x₂ y₁ y₂ ↦
    hfinB _ (Metric.isBounded_ball.subset (l4_rect_subset_ball x₁ x₂ y₁ y₂))
  choose X hXmono hXgap hXcov hXn using fun j ↦ l4_plane_rows hS hS0 hre hclass.mass hfinR j
  choose n hn1 hnμ using hXn
  have hpow : ∀ z (k : ℕ) r, 0 < r → 2 ^ k * r ≤ 2 * (16 * S) →
      μ (ball z (2 ^ k * r)) ≤ (C₁ : ℝ≥0∞) ^ k * μ (ball z r) := fun z ↦
    l4_iter (f := fun r ↦ μ (ball z r)) (hC₁ μ hclass.doubling z)
  have hpart := exists_rect_partition hre him
    (fun x₁ x₂ y₁ y₂ ↦ x₂ - x₁ ≤ 2 * S ∧ y₂ - y₁ ≤ 2 * S)
    (fun x₁ x₂ y₁ y₂ x₁' x₂' y₁' y₂' h h1 h2 h3 h4 ↦
      ⟨by linarith [h.1], by linarith [h.2]⟩)
    C₀ (l4_plane_C0 hpow hC₀) (fun x₁ x₂ y₁ y₂ ↦ max (x₂ - x₁) (y₂ - y₁)) C_E 1 one_pos
    (l4_plane_sigma hCE hpow)
  obtain ⟨g, hgdisj, hgunion, hgood⟩ := l4_assemble hpart X (fun j ↦ (j : ℝ) * S)
    (fun j ↦ ((j : ℝ) + 1) * S) n hn1 hXmono
    (fun j j' h ↦ by
      have : (j : ℝ) + 1 ≤ j' := by exact_mod_cast h
      nlinarith)
    (fun j k ↦ by
      have hg := hXgap j k
      have hl : ((j : ℝ) + 1) * S - j * S = S := by ring
      exact ⟨⟨hXmono j (lt_add_one k), by nlinarith, by rw [hl]; linarith, by rw [hl]; linarith⟩,
        ⟨hg.2, by rw [hl]; linarith⟩, hnμ j k⟩)
  refine ⟨g, hgdisj, ?_, hgood⟩
  rw [hgunion]
  refine eq_univ_of_forall fun z ↦ mem_iUnion.2 ?_
  set j := ⌊z.im / S⌋
  have hj1 : (j : ℝ) ≤ z.im / S := Int.floor_le _
  have hj2 : z.im / S < j + 1 := Int.lt_floor_add_one _
  rw [le_div_iff₀ hS0] at hj1
  rw [div_lt_iff₀ hS0] at hj2
  obtain ⟨k, hk⟩ := hXcov j z.re
  exact ⟨(j, k), hk, ⟨hj1, hj2⟩⟩

/-- **Lemma 4 (plane)**, uniform form with the shape of the pieces. -/
theorem l4_plane_strong (Cd : ℝ≥0) (R₀ : ℝ) (N : ℕ) (hN : 1 ≤ N) :
    ∃ a A L : ℝ, 0 < a ∧ 0 < A ∧ 1 ≤ L ∧ ∀ ν : Measure ℂ, MeasClassPlane ν Cd R₀ →
      ∃ R : ℕ → Set ℂ, IsMassPartition ν univ dist (massRadius ν) N a A R ∧
        ∀ i, ∃ x₁ x₂ y₁ y₂ : ℝ, IsRectLE L x₁ x₂ y₁ y₂ ∧ R i = rect x₁ x₂ y₁ y₂ := by
  by_cases hR₀ : 0 < R₀
  swap
  · refine ⟨1, 1, 1, one_pos, one_pos, le_rfl, fun ν hν ↦ ?_⟩
    exfalso
    have h := hν.mass 0
    rw [ball_eq_empty.2 (not_lt.1 hR₀), measure_empty] at h
    exact absurd h (not_lt.2 zero_le)
  -- constants, chosen before the measure
  set R' : ℝ := ((N : ℝ) + 1) * R₀
  have hR'0 : 0 < R' := by positivity
  set S : ℝ := 2 * R'
  obtain ⟨C₁, -, hC₁⟩ := doubling_upTo_quant (X := ℂ) Cd (16 * S)
  set C₀ : ℕ := ⌈(C₁ : ℝ) ^ 5⌉₊
  set C_E : ℝ := (C₁ : ℝ) ^ 3 with hCE
  set L : ℝ := rectRatioBound C₀ C_E 1
  have hL1 : 1 ≤ L := one_le_rectRatioBound _ _ _
  obtain ⟨c, Cb, δ, sb, hc, -, hδ, -, hb⟩ :=
    measure_ball_massRadiusM_bounds_quant (X := ℂ) Cd R' (12 * S)
  obtain ⟨CN, hCN1, hCN⟩ := massRadiusM_inv_smul_quant (X := ℂ) Cd R₀ N hN
  set M : ℝ := (C₁ : ℝ) ^ 6 * C₀ with hM
  set A' : ℝ := max 1 ((M / c) ^ (1 / δ))
  have hA'1 : 1 ≤ A' := le_max_left _ _
  have : 0 < L := by linarith
  have : 0 < CN := by linarith
  refine ⟨1 / (6 * L), A' * CN, L, by positivity, by positivity, hL1, fun ν hν ↦ ?_⟩
  obtain ⟨hclass', hfin'b⟩ := l4_plane_mu hN hR₀ hν
  obtain ⟨g, hgdisj, hgcover, hgood⟩ := l4_plane_pieces rfl hR'0 hclass' hfin'b hC₁
    (l4_coe_pow_le_ceil C₁ 5) hCE
  have hfin' : ∀ z r, ((N : ℝ≥0∞)⁻¹ • ν) (ball z r) < ∞ := fun z r ↦
    hfin'b _ Metric.isBounded_ball
  have hρ' : ∀ z, 0 < massRadius ((N : ℝ≥0∞)⁻¹ • ν) z := fun z ↦
    massRadius_pos ⟨Cd, hclass'.doubling⟩ hfin' ⟨R', hR'0, hclass'.mass⟩ z
  have hpow : ∀ z (k : ℕ) r, 0 < r → 2 ^ k * r ≤ 2 * (16 * S) →
      ((N : ℝ≥0∞)⁻¹ • ν) (ball z (2 ^ k * r)) ≤
        (C₁ : ℝ≥0∞) ^ k * ((N : ℝ≥0∞)⁻¹ • ν) (ball z r) := fun z ↦
    l4_iter (f := fun r ↦ ((N : ℝ≥0∞)⁻¹ • ν) (ball z r)) (hC₁ _ hclass'.doubling z)
  have hmass : ∀ i, ν (rect (g i).1 (g i).2.1 (g i).2.2.1 (g i).2.2.2) = N := fun i ↦ by
    rw [l4_smul_apply hN, (hgood i).1, mul_one]
  refine ⟨fun i ↦ rect (g i).1 (g i).2.1 (g i).2.2.1 (g i).2.2.2,
    ⟨fun i ↦ measurableSet_rect _ _ _ _, hgdisj, hgcover, hmass, fun i ↦ ?_, fun i ↦ ?_⟩,
    fun i ↦ ?_⟩
  · -- upper size
    obtain ⟨-, -, x₁', x₂', y₁', y₂', hg, hPb, hμb, hsub⟩ := hgood i
    exact l4_plane_size hc hδ hM hA'1 (le_max_right _ _) hpow
      (fun z r h1 h2 ↦ (hb _ hclass' z r h1 h2).1) hρ'
      (fun z ↦ (hCN ν hν.measClassM z).2) hg hPb hμb hsub
  · -- fatness
    exact l4_plane_fat hN hL1 (hgood i).2.1 (hmass i)
  · exact ⟨_, _, _, _, (hgood i).2.1, rfl⟩

/-- Coordinates of nested non-degenerate rectangles. -/
theorem l4_rect_subset_coords {x₁ x₂ y₁ y₂ x₁' x₂' y₁' y₂' : ℝ} (hx : x₁ < x₂) (hy : y₁ < y₂)
    (h : rect x₁ x₂ y₁ y₂ ⊆ rect x₁' x₂' y₁' y₂') :
    x₁' ≤ x₁ ∧ x₂ ≤ x₂' ∧ y₁' ≤ y₁ ∧ y₂ ≤ y₂' := by
  have h0 := h (show (⟨x₁, y₁⟩ : ℂ) ∈ rect x₁ x₂ y₁ y₂ from ⟨⟨le_rfl, hx⟩, ⟨le_rfl, hy⟩⟩)
  refine ⟨h0.1.1, ?_, h0.2.1, ?_⟩
  · by_contra hc
    push Not at hc
    have := h (show (⟨max x₁ x₂', y₁⟩ : ℂ) ∈ rect x₁ x₂ y₁ y₂ from
      ⟨⟨le_max_left _ _, max_lt hx hc⟩, ⟨le_rfl, hy⟩⟩)
    exact absurd this.1.2 (not_lt.2 (le_max_right _ _))
  · by_contra hc
    push Not at hc
    have := h (show (⟨x₁, max y₁ y₂'⟩ : ℂ) ∈ rect x₁ x₂ y₁ y₂ from
      ⟨⟨le_rfl, hx⟩, ⟨le_max_left _ _, max_lt hy hc⟩⟩)
    exact absurd this.2.2 (not_lt.2 (le_max_right _ _))

theorem l4_cayleyPre_mono {S T : Set ℂ} (h : S ⊆ T) : cayleyPre S ⊆ cayleyPre T :=
  fun _ hz ↦ ⟨hz.1, h hz.2⟩

/-- A compact subset of `𝔻` lies in a hyperbolic ball around `0`. -/
theorem l4_compact_subset_hypBall {K : Set ℂ} (hK𝔻 : K ⊆ 𝔻) (hK : IsCompact K) :
    ∃ r : ℝ, K ⊆ hypBall 0 r := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, empty_subset _⟩
  obtain ⟨w₀, hw₀, hmax⟩ := hK.exists_isMaxOn hne continuous_norm.continuousOn
  refine ⟨Real.artanh ‖w₀‖ + 1, fun w hw ↦ ⟨hK𝔻 hw, ?_⟩⟩
  rw [hypDist_zero_left]
  have h1 : ‖w‖ ≤ ‖w₀‖ := hmax hw
  have h2 : ‖w₀‖ < 1 := mem_ball_zero_iff.1 (hK𝔻 hw₀)
  have := Real.artanh_le_artanh (by linarith [norm_nonneg w]) h2 h1
  linarith

/-- The mass radius of `N⁻¹ μ` through `discPull`. -/
theorem l4_massRadiusM_discPull_smul (ν : Measure ℂ) (c : ℝ≥0∞) (a : HDisc) :
    massRadiusM (c • discPull ν) a = massRadiusDisc (c • ν) a.val := by
  unfold massRadiusM massRadiusDisc
  congr 1
  ext r
  simp only [mem_ofPred_eq, smul_apply, smul_eq_mul, discPull_ball]

/-- The inner/outer ball property of `discBox_inner_outer`, for the constants `(Λ, L, A, D)`. -/
def DiscBoxBalls (Λ L A D : ℝ) : Prop :=
  ∀ x₁ x₂ y₁ y₂ : ℝ, IsRectLE L x₁ x₂ y₁ y₂ → 0 < y₁ → y₂ - y₁ ≤ Λ * y₁ →
    ∃ p ∈ 𝔻, ∃ β : ℝ, 0 < β ∧ A * β ≤ D ∧
      hypBall p β ⊆ cayleyPre (midThird x₁ x₂ y₁ y₂) ∧ discBox x₁ x₂ y₁ y₂ ⊆ hypBall p (A * β)

/-- Disc: the normalised measure `N⁻¹ ν` is in the class `MeasClassDisc` with radius
`(2 N + 1) R₀`. -/
theorem l4_disc_mu {ν : Measure ℂ} {Cd : ℝ≥0} {R₀ : ℝ} {N : ℕ} (hN : 1 ≤ N) (hR₀ : 0 < R₀)
    (hν : MeasClassDisc ν Cd R₀) :
    MeasClassDisc ((N : ℝ≥0∞)⁻¹ • ν) Cd ((2 * ⌈(N : ℝ) / 1⌉₊ + 1) * R₀) := by
  have hNne : (N : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hNtop : (N : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top N
  refine ⟨fun z hz r hr h2r ↦ ?_, fun z hz ↦ ?_, fun K hK hKc ↦ ?_⟩
  · rw [l4_inv_smul_apply, l4_inv_smul_apply, mul_left_comm]
    gcongr
    exact hν.doubling z hz r hr h2r
  · have hmassN : (N : ℝ≥0∞) < ν (hypBall z ((2 * ⌈(N : ℝ) / 1⌉₊ + 1) * R₀)) := by
      have := ofReal_lt_measure_hypBall hR₀ one_pos
        (fun z hz ↦ by rw [ENNReal.ofReal_one]; exact (hν.mass z hz).le) (N : ℝ) hz
      rwa [ENNReal.ofReal_natCast] at this
    rw [l4_inv_smul_apply]
    calc (1 : ℝ≥0∞) = (N : ℝ≥0∞)⁻¹ * N := (ENNReal.inv_mul_cancel hNne hNtop).symm
      _ < (N : ℝ≥0∞)⁻¹ * ν (hypBall z ((2 * ⌈(N : ℝ) / 1⌉₊ + 1) * R₀)) := by
          rw [mul_comm ((N : ℝ≥0∞)⁻¹) (N : ℝ≥0∞), mul_comm ((N : ℝ≥0∞)⁻¹) (ν _)]
          exact ENNReal.mul_lt_mul_left (ENNReal.inv_ne_zero.2 hNtop) (ENNReal.inv_ne_top.2 hNne)
            hmassN
  · rw [l4_inv_smul_apply]
    exact ENNReal.mul_lt_top (ENNReal.inv_lt_top.2 (by positivity)) (hν.finite K hK hKc)

/-- Disc: balls have finite mass for a measure of the class `MeasClassDisc`. -/
theorem l4_disc_finB {μ : Measure ℂ} {Cd : ℝ≥0} {R' : ℝ} (h : MeasClassDisc μ Cd R') :
    ∀ z ∈ 𝔻, ∀ r, μ (hypBall z r) < ∞ := fun z hz r ↦
  (discPull_ball μ ⟨z, hz⟩ r).symm.trans_lt (h.measClassM_discPull.finite ⟨z, hz⟩ r)

/-- Disc: the push-forward `cayley_* (μ|𝔻)` does not charge horizontal or vertical lines. -/
theorem l4_disc_null {μ : Measure ℂ} (hd : IsLocallyDoublingDisc μ)
    (hfinB : ∀ z ∈ 𝔻, ∀ r, μ (hypBall z r) < ∞) :
    (∀ x : ℝ, (μ.restrict 𝔻).map cayley {w | w.re = x} = 0) ∧
      ∀ y : ℝ, (μ.restrict 𝔻).map cayley {w | w.im = y} = 0 := by
  have hcayPre𝔻 : ∀ S, cayleyPre S ∩ 𝔻 = cayleyPre S := fun S ↦
    inter_eq_left.2 fun _ hz ↦ hz.1
  refine ⟨fun x ↦ ?_, fun y ↦ ?_⟩
  · rw [map_restrict_cayley_apply μ
      ((isClosed_eq Complex.continuous_re continuous_const).measurableSet), ← hcayPre𝔻]
    exact measure_inter_disc_eq_zero_of_isPorous hd hfinB (isPorous_cayley_re x)
  · rw [map_restrict_cayley_apply μ
      ((isClosed_eq Complex.continuous_im continuous_const).measurableSet), ← hcayPre𝔻]
    exact measure_inter_disc_eq_zero_of_isPorous hd hfinB (isPorous_cayley_im y)

/-- Disc: coarse rows `[Λ^j, Λ^{j+1})` of the model half-plane, cut into blocks of integer
mass. -/
theorem l4_disc_rows {μ : Measure ℂ} {Cd : ℝ≥0} {R' Λ : ℝ} (hR'0 : 0 < R')
    (hΛ : Λ = 64 * Real.exp (4 * R')) (hΛ1 : 1 < Λ) (hclass : MeasClassDisc μ Cd R')
    (hre : ∀ x : ℝ, (μ.restrict 𝔻).map cayley {w | w.re = x} = 0) (j : ℤ) :
    ∃ x : ℤ → ℝ, StrictMono x ∧
      (∀ k, (Λ - 1) * Λ ^ j ≤ x (k + 1) - x k ∧ x (k + 1) - x k ≤ 2 * ((Λ - 1) * Λ ^ j)) ∧
      (∀ t : ℝ, ∃ k, t ∈ Ico (x k) (x (k + 1))) ∧
      ∀ k, ∃ n : ℕ, 1 ≤ n ∧
        (μ.restrict 𝔻).map cayley (rect (x k) (x (k + 1)) (Λ ^ j) (Λ * Λ ^ j)) = n := by
  have hΛ0 : 0 < Λ := by linarith
  have hν'rect : ∀ x₁ x₂ y₁ y₂, (μ.restrict 𝔻).map cayley (rect x₁ x₂ y₁ y₂) =
      μ (discBox x₁ x₂ y₁ y₂) := fun _ _ _ _ ↦
    map_restrict_cayley_apply μ (measurableSet_rect _ _ _ _)
  have hfinR : ∀ x₁ x₂ y₁ y₂ : ℝ, 0 < y₁ → (μ.restrict 𝔻).map cayley (rect x₁ x₂ y₁ y₂) < ∞ := by
    intro x₁ x₂ y₁ y₂ hy
    obtain ⟨K, hKc, hK𝔻, hsub⟩ := exists_isCompact_discBox_subset x₁ x₂ hy y₂
    rw [hν'rect]
    exact (measure_mono hsub).trans_lt (hclass.finite K hK𝔻 hKc)
  have hpj : 0 < Λ ^ j := zpow_pos hΛ0 j
  refine exists_strip_cuts hre (by nlinarith) (fun a b ↦ hfinR _ _ _ _ hpj) fun a ↦ ?_
  subst hΛ
  obtain ⟨p, hp, hsub⟩ := exists_hypBall_subset_discBox_row hR'0 hpj a
  rw [hν'rect]
  exact (hclass.mass p hp).le.trans (measure_mono hsub)

/-- Disc: the doubling estimate for hyperbolic balls up to the scale `D₃`, in the form used for
`2^i β` with `i ≤ k₃ + 2`. -/
theorem l4_disc_hpow {μ : Measure ℂ} {Cd : ℝ≥0} {R' D₃ R₁ : ℝ} {k₃ : ℕ} {C₁ : ℝ≥0}
    (hclass : MeasClassDisc μ Cd R') (hD₃ : 0 < D₃) (hR₁ : R₁ = 2 ^ (k₃ + 2) * D₃)
    (hC₁ : ∀ μ' : Measure HDisc, IsLocDoublingMWith μ' Cd → ∀ x : HDisc, ∀ r : ℝ, 0 < r →
      r ≤ R₁ → μ' (ball x (2 * r)) ≤ C₁ * μ' (ball x r)) :
    ∀ p ∈ 𝔻, ∀ β : ℝ, 0 < β → β ≤ D₃ → ∀ i ≤ k₃ + 2,
      μ (hypBall p (2 ^ i * β)) ≤ (C₁ : ℝ≥0∞) ^ i * μ (hypBall p β) := by
  have hM' := hclass.measClassM_discPull
  have hdC : ∀ p ∈ 𝔻, ∀ r, 0 < r → r ≤ R₁ →
      μ (hypBall p (2 * r)) ≤ C₁ * μ (hypBall p r) := fun p hp r hr hrR ↦ by
    have := hC₁ (discPull μ) hM'.doubling (HDisc.mk p hp) r hr hrR
    have e1 : discPull μ (ball (HDisc.mk p hp) (2 * r)) = μ (hypBall p (2 * r)) :=
      discPull_ball μ _ _
    have e2 : discPull μ (ball (HDisc.mk p hp) r) = μ (hypBall p r) := discPull_ball μ _ _
    rwa [e1, e2] at this
  have hpow : ∀ p ∈ 𝔻, ∀ (k : ℕ) r, 0 < r → 2 ^ k * r ≤ 2 * R₁ →
      μ (hypBall p (2 ^ k * r)) ≤ (C₁ : ℝ≥0∞) ^ k * μ (hypBall p r) := fun p hp ↦
    l4_iter (f := fun r ↦ μ (hypBall p r)) (hdC p hp)
  intro p hp β hβ hβD i hi
  refine hpow p hp i β hβ ?_
  have h1 : (2 : ℝ) ^ i ≤ 2 ^ (k₃ + 2) := pow_le_pow_right₀ (by norm_num) hi
  have h2 : (2 : ℝ) ^ i * β ≤ 2 ^ (k₃ + 2) * D₃ := mul_le_mul h1 hβD hβ.le (by positivity)
  have h3 : 0 ≤ (2 : ℝ) ^ (k₃ + 2) * D₃ := by positivity
  rw [hR₁]; linarith

/-- Disc: monotonicity of the admissibility predicate. -/
theorem l4_disc_P_mono {Λ : ℝ} (hΛ0 : 0 < Λ) {x₁ x₂ y₁ y₂ x₁' x₂' y₁' y₂' : ℝ}
    (h : 0 < y₁ ∧ y₂ - y₁ ≤ Λ * y₁ ∧ x₂ - x₁ ≤ 2 * Λ * y₁) (h1 : x₁ ≤ x₁') (h2 : x₂' ≤ x₂)
    (h3 : y₁ ≤ y₁') (h4 : y₂' ≤ y₂) : 0 < y₁' ∧ y₂' - y₁' ≤ Λ * y₁' ∧ x₂' - x₁' ≤ 2 * Λ * y₁' := by
  obtain ⟨h5, h6, h7⟩ := h
  have h8 : Λ * y₁ ≤ Λ * y₁' := mul_le_mul_of_nonneg_left h3 hΛ0.le
  exact ⟨by linarith, by linarith, by linarith⟩

/-- Disc: a box of mass `> C₀` has a middle third of mass `> 1` for the model measure. -/
theorem l4_disc_C0 {μ : Measure ℂ} {Λ A₃ D₃ : ℝ} {k₃ : ℕ} {C₁ : ℝ≥0} {C₀ : ℕ} (hA₃ : 1 ≤ A₃)
    (hk₃A : A₃ ≤ 2 ^ k₃) (hio₃ : DiscBoxBalls Λ 3 A₃ D₃)
    (hpowD : ∀ p ∈ 𝔻, ∀ β : ℝ, 0 < β → β ≤ D₃ → ∀ i ≤ k₃ + 2,
      μ (hypBall p (2 ^ i * β)) ≤ (C₁ : ℝ≥0∞) ^ i * μ (hypBall p β))
    (hC₁k : (C₁ : ℝ≥0∞) ^ k₃ ≤ (C₀ : ℝ≥0∞)) (x₁ x₂ y₁ y₂ : ℝ) (hg : IsRectLE 3 x₁ x₂ y₁ y₂)
    (hP : 0 < y₁ ∧ y₂ - y₁ ≤ Λ * y₁ ∧ x₂ - x₁ ≤ 2 * Λ * y₁)
    (hlt : (C₀ : ℝ≥0∞) < (μ.restrict 𝔻).map cayley (rect x₁ x₂ y₁ y₂)) :
    1 < (μ.restrict 𝔻).map cayley (midThird x₁ x₂ y₁ y₂) := by
  obtain ⟨p, hp, β, hβ, hAβ, hin, hout⟩ := hio₃ x₁ x₂ y₁ y₂ hg hP.1 hP.2.1
  have hβD : β ≤ D₃ := (le_mul_of_one_le_left hβ.le hA₃).trans hAβ
  have h32 : (μ.restrict 𝔻).map cayley (rect x₁ x₂ y₁ y₂) ≤
      (C₁ : ℝ≥0∞) ^ k₃ * (μ.restrict 𝔻).map cayley (midThird x₁ x₂ y₁ y₂) := by
    rw [map_restrict_cayley_apply μ (measurableSet_rect _ _ _ _),
      map_restrict_cayley_apply μ (l4_measurableSet_midThird _ _ _ _)]
    calc μ (discBox x₁ x₂ y₁ y₂) ≤ μ (hypBall p (2 ^ k₃ * β)) :=
          measure_mono (hout.trans fun w hw ↦ ⟨hw.1, hw.2.trans_le
            (mul_le_mul_of_nonneg_right hk₃A hβ.le)⟩)
      _ ≤ (C₁ : ℝ≥0∞) ^ k₃ * μ (hypBall p β) := hpowD p hp β hβ hβD k₃ (by omega)
      _ ≤ (C₁ : ℝ≥0∞) ^ k₃ * μ (cayleyPre (midThird x₁ x₂ y₁ y₂)) := by gcongr
  by_contra hle
  push Not at hle
  have := hlt.trans_le (h32.trans (by
    calc (C₁ : ℝ≥0∞) ^ k₃ * (μ.restrict 𝔻).map cayley (midThird x₁ x₂ y₁ y₂) ≤
        (C₁ : ℝ≥0∞) ^ k₃ * 1 := by gcongr
      _ ≤ (C₀ : ℝ≥0∞) := by rw [mul_one]; exact hC₁k))
  exact lt_irrefl _ this

/-- Disc: Euclidean doubling at scale `y₁ / 16` for the model measure inside admissible boxes. -/
theorem l4_disc_sigma {μ : Measure ℂ} {Λ κ C_E : ℝ} (hΛ0 : 0 < Λ) (hκ : κ = 1 / (48 * Λ))
    (hCE : ∀ w : ℂ, 0 < w.im → ∀ r : ℝ, 0 < r → r ≤ w.im / 16 →
      (μ.restrict 𝔻).map cayley (ball w (4 * r)) ≤
        ENNReal.ofReal C_E * (μ.restrict 𝔻).map cayley (ball w (r / 2)))
    (x₁ x₂ y₁ y₂ : ℝ) (hg : IsRectLE 3 x₁ x₂ y₁ y₂)
    (hP : 0 < y₁ ∧ y₂ - y₁ ≤ Λ * y₁ ∧ x₂ - x₁ ≤ 2 * Λ * y₁) :
    κ * max (x₂ - x₁) (y₂ - y₁) ≤ y₁ / 16 ∧
      ∀ w ∈ rect x₁ x₂ y₁ y₂, ∀ r : ℝ, 0 < r → r ≤ y₁ / 16 →
        (μ.restrict 𝔻).map cayley (ball w (4 * r)) ≤
          ENNReal.ofReal C_E * (μ.restrict 𝔻).map cayley (ball w (r / 2)) := by
  obtain ⟨hy0, hl, -⟩ := hP
  refine ⟨?_, fun w hw r hr hry ↦ hCE w (by linarith [hw.2.1]) r hr
    (hry.trans (by linarith [hw.2.1]))⟩
  have hg3 := hg.2.2.1
  have hΛy : 0 ≤ Λ * y₁ := by positivity
  have hmax : max (x₂ - x₁) (y₂ - y₁) ≤ 3 * (Λ * y₁) := by
    apply max_le <;> linarith
  have hκ0 : 0 ≤ κ := by rw [hκ]; positivity
  calc κ * max (x₂ - x₁) (y₂ - y₁) ≤ κ * (3 * (Λ * y₁)) := mul_le_mul_of_nonneg_left hmax hκ0
    _ = y₁ / 16 := by rw [hκ]; field_simp; ring

/-- Disc: the partition of the model half-plane into rectangles of mass one for `cayley_* μ`,
with side ratio `≤ rectRatioBound C₀ C_E κ`. -/
theorem l4_disc_pieces {μ : Measure ℂ} {Cd : ℝ≥0} {R' Λ A₃ D₃ R₁ C_E κ : ℝ} {k₃ : ℕ} {C₁ : ℝ≥0}
    {C₀ : ℕ} (hR'0 : 0 < R') (hΛ : Λ = 64 * Real.exp (4 * R')) (hΛ1 : 1 < Λ)
    (hclass : MeasClassDisc μ Cd R') (hA₃ : 1 ≤ A₃) (hD₃ : 0 < D₃) (hk₃A : A₃ ≤ 2 ^ k₃)
    (hio₃ : DiscBoxBalls Λ 3 A₃ D₃) (hR₁ : R₁ = 2 ^ (k₃ + 2) * D₃)
    (hC₁ : ∀ μ' : Measure HDisc, IsLocDoublingMWith μ' Cd → ∀ x : HDisc, ∀ r : ℝ, 0 < r →
      r ≤ R₁ → μ' (ball x (2 * r)) ≤ C₁ * μ' (ball x r))
    (hC₀ : (C₁ : ℝ≥0∞) ^ k₃ ≤ (C₀ : ℝ≥0∞)) (hκ : κ = 1 / (48 * Λ))
    (hCE : ∀ μ' : Measure ℂ,
      (∀ z ∈ 𝔻, ∀ r : ℝ, 0 < r → 2 * r < 1 → μ' (hypBall z (2 * r)) ≤ Cd * μ' (hypBall z r)) →
      ∀ w : ℂ, 0 < w.im → ∀ r : ℝ, 0 < r → r ≤ w.im / 16 →
        (μ'.restrict 𝔻).map cayley (ball w (4 * r)) ≤
          ENNReal.ofReal C_E * (μ'.restrict 𝔻).map cayley (ball w (r / 2))) :
    ∃ g : ℕ → ℝ × ℝ × ℝ × ℝ,
      Pairwise (Function.onFun Disjoint fun i ↦ rect (g i).1 (g i).2.1 (g i).2.2.1 (g i).2.2.2) ∧
      (⋃ i, rect (g i).1 (g i).2.1 (g i).2.2.1 (g i).2.2.2) = {w : ℂ | 0 < w.im} ∧
      ∀ i, RectGood ((μ.restrict 𝔻).map cayley)
        (fun x₁ x₂ y₁ y₂ ↦ 0 < y₁ ∧ y₂ - y₁ ≤ Λ * y₁ ∧ x₂ - x₁ ≤ 2 * Λ * y₁) C₀
        (rectRatioBound C₀ C_E κ) (g i) := by
  have hΛ0 : 0 < Λ := by linarith
  obtain ⟨hre, him⟩ := l4_disc_null ⟨Cd, hclass.doubling⟩ (l4_disc_finB hclass)
  choose X hXmono hXgap hXcov hXn using fun j ↦ l4_disc_rows hR'0 hΛ hΛ1 hclass hre j
  choose n hn1 hnμ using hXn
  have hpowD := l4_disc_hpow hclass hD₃ hR₁ hC₁
  have hpart := exists_rect_partition hre him
    (fun x₁ x₂ y₁ y₂ ↦ 0 < y₁ ∧ y₂ - y₁ ≤ Λ * y₁ ∧ x₂ - x₁ ≤ 2 * Λ * y₁)
    (fun _ _ _ _ _ _ _ _ h h1 h2 h3 h4 ↦ l4_disc_P_mono hΛ0 h h1 h2 h3 h4)
    C₀ (l4_disc_C0 hA₃ hk₃A hio₃ hpowD hC₀)
    (fun _ _ y₁ _ ↦ y₁ / 16) C_E κ (by rw [hκ]; positivity)
    (l4_disc_sigma hΛ0 hκ (hCE μ hclass.doubling))
  obtain ⟨g, hgdisj, hgunion, hgood⟩ := l4_assemble hpart X (fun j ↦ Λ ^ j) (fun j ↦ Λ * Λ ^ j)
    n hn1 hXmono
    (fun j j' h ↦ by
      rw [← zpow_one_add₀ hΛ0.ne', add_comm]
      exact zpow_le_zpow_right₀ hΛ1.le (by omega))
    (fun j k ↦ by
      have hg := hXgap j k
      have hpj : 0 < Λ ^ j := zpow_pos hΛ0 j
      have hl : Λ * Λ ^ j - Λ ^ j = (Λ - 1) * Λ ^ j := by ring
      have hh : 0 < (Λ - 1) * Λ ^ j := mul_pos (by linarith) hpj
      have e2 : 2 * Λ * Λ ^ j = 2 * (Λ * Λ ^ j) := by ring
      have hlt : Λ ^ j < Λ * Λ ^ j := (lt_mul_iff_one_lt_left hpj).2 hΛ1
      exact ⟨⟨hXmono j (lt_add_one k), hlt, by rw [hl]; linarith, by rw [hl]; linarith⟩,
        ⟨hpj, by rw [hl]; linarith, by rw [e2]; linarith⟩, hnμ j k⟩)
  refine ⟨g, hgdisj, ?_, hgood⟩
  rw [hgunion]
  apply Subset.antisymm
  · refine iUnion_subset fun jk w hw ↦ ?_
    exact (zpow_pos hΛ0 jk.1).trans_le hw.2.1
  · intro w hw
    obtain ⟨j, hj1, hj2⟩ := exists_mem_Ico_zpow hw hΛ1
    obtain ⟨k, hk⟩ := hXcov j w.re
    refine mem_iUnion.2 ⟨(j, k), hk, hj1, ?_⟩
    rw [zpow_add_one₀ hΛ0.ne', mul_comm] at hj2
    exact hj2

/-- Disc: the pieces `cayleyPre R` of a partition of the half-plane into rectangles are a
partition of `𝔻` into measurable sets. -/
theorem l4_disc_partition {g : ℕ → ℝ × ℝ × ℝ × ℝ}
    (hgdisj : Pairwise (Function.onFun Disjoint fun i ↦
      rect (g i).1 (g i).2.1 (g i).2.2.1 (g i).2.2.2))
    (hgcover : (⋃ i, rect (g i).1 (g i).2.1 (g i).2.2.1 (g i).2.2.2) = {w : ℂ | 0 < w.im}) :
    (∀ i, MeasurableSet (cayleyPre (rect (g i).1 (g i).2.1 (g i).2.2.1 (g i).2.2.2))) ∧
      Pairwise (Function.onFun Disjoint fun i ↦
        cayleyPre (rect (g i).1 (g i).2.1 (g i).2.2.1 (g i).2.2.2)) ∧
      ⋃ i, cayleyPre (rect (g i).1 (g i).2.1 (g i).2.2.1 (g i).2.2.2) = 𝔻 := by
  refine ⟨fun i ↦ ?_, fun i j hij ↦ ?_, ?_⟩
  · exact (measurable_cayley (measurableSet_rect _ _ _ _)).inter measurableSet_ball |>.congr
      (by ext z; simp only [cayleyPre, mem_inter_iff, mem_preimage, mem_ofPred_eq]; exact and_comm)
  · change Disjoint (cayleyPre _) (cayleyPre _)
    exact Set.disjoint_left.2 fun z hz1 hz2 ↦ Set.disjoint_left.1 (hgdisj hij) hz1.2 hz2.2
  · apply Subset.antisymm
    · exact iUnion_subset fun i z hz ↦ hz.1
    · intro z hz
      have hw : cayley z ∈ ⋃ i, rect (g i).1 (g i).2.1 (g i).2.2.1 (g i).2.2.2 := by
        rw [hgcover]; exact cayley_im_pos hz
      obtain ⟨i, hi⟩ := mem_iUnion.1 hw
      exact mem_iUnion.2 ⟨i, hz, hi⟩

/-- Disc: the hyperbolic mass-radius bound of the normalised measure, from `hb`. -/
theorem l4_disc_low {μ : Measure ℂ} {Cd : ℝ≥0} {R' R₂ c δ Cb sb : ℝ}
    (hclass : MeasClassDisc μ Cd R')
    (hb : ∀ μ' : Measure HDisc, MeasClassM μ' Cd R' → ∀ (x : HDisc) (r : ℝ),
      massRadiusM μ' x ≤ r → r ≤ R₂ →
        ENNReal.ofReal (c * (r / massRadiusM μ' x) ^ δ) ≤ μ' (ball x r) ∧
          μ' (ball x r) ≤ ENNReal.ofReal (Cb * (r / massRadiusM μ' x) ^ sb)) :
    ∀ z ∈ 𝔻, ∀ r, massRadiusDisc μ z ≤ r → r ≤ R₂ →
      ENNReal.ofReal (c * (r / massRadiusDisc μ z) ^ δ) ≤ μ (hypBall z r) := by
  intro z hz r hle hr
  have hmr : massRadiusDisc μ z = massRadiusM (discPull μ) (HDisc.mk z hz) :=
    massRadiusDisc_eq μ (HDisc.mk z hz)
  have hbl : discPull μ (ball (HDisc.mk z hz) r) = μ (hypBall z r) := discPull_ball μ _ _
  have hb' := (hb (discPull μ) hclass.measClassM_discPull (HDisc.mk z hz) r
    (by rw [← hmr]; exact hle) hr).1
  rwa [hbl, ← hmr] at hb'

/-- Disc: the pieces have hyperbolic diameter `≤ A' CN ρ_ν`. -/
theorem l4_disc_size {μ ν : Measure ℂ} {Λ A₃ D₃ c δ M A' CN : ℝ} {k₃ : ℕ} {C₁ : ℝ≥0} {C₀ : ℕ}
    {x₁ x₂ y₁ y₂ : ℝ} {T : Set ℂ} (hA₃ : 1 ≤ A₃) (hk₃A : A₃ ≤ 2 ^ k₃) (hc : 0 < c)
    (hδ : 0 < δ) (hM : M = (C₁ : ℝ) ^ (k₃ + 2) * C₀) (hA'1 : 1 ≤ A') (hA'2 : (M / c) ^ (1 / δ) ≤ A')
    (hio₃ : DiscBoxBalls Λ 3 A₃ D₃)
    (hpowD : ∀ p ∈ 𝔻, ∀ β : ℝ, 0 < β → β ≤ D₃ → ∀ i ≤ k₃ + 2,
      μ (hypBall p (2 ^ i * β)) ≤ (C₁ : ℝ≥0∞) ^ i * μ (hypBall p β))
    (hlow : ∀ z ∈ 𝔻, ∀ r, massRadiusDisc μ z ≤ r → r ≤ 2 * D₃ →
      ENNReal.ofReal (c * (r / massRadiusDisc μ z) ^ δ) ≤ μ (hypBall z r))
    (hρ' : ∀ z ∈ 𝔻, 0 < massRadiusDisc μ z)
    (hCNz : ∀ z ∈ 𝔻, massRadiusDisc μ z ≤ CN * massRadiusDisc ν z)
    (hg : IsRectLE 3 x₁ x₂ y₁ y₂) (hPb : 0 < y₁ ∧ y₂ - y₁ ≤ Λ * y₁ ∧ x₂ - x₁ ≤ 2 * Λ * y₁)
    (hμb : μ (discBox x₁ x₂ y₁ y₂) ≤ C₀) (hsub : T ⊆ discBox x₁ x₂ y₁ y₂) :
    ∀ z ∈ T, ∀ w ∈ T, hypDist z w ≤ A' * CN * massRadiusDisc ν z := by
  have hM0 : 0 ≤ M := by rw [hM]; positivity
  obtain ⟨p, hp, β, hβ, hAβ, hin, hout⟩ := hio₃ x₁ x₂ y₁ y₂ hg hPb.1 hPb.2.1
  have hβD : β ≤ D₃ := (le_mul_of_one_le_left hβ.le hA₃).trans hAβ
  intro z hz w hw
  have hzB := hsub hz
  have hwB := hsub hw
  have hzp := (hout hzB).2
  have hwp := (hout hwB).2
  have hzD := hzB.1
  have hwD := hwB.1
  have hzw : hypDist z w < 2 * (A₃ * β) := by
    have := hypDist_triangle hzD hp hwD
    rw [hypDist_comm z p] at this
    linarith
  have hball : μ (hypBall z (2 * (A₃ * β))) ≤ ENNReal.ofReal M := by
    calc μ (hypBall z (2 * (A₃ * β))) ≤ μ (hypBall p (2 ^ (k₃ + 2) * β)) := by
          refine measure_mono fun y hy ↦ ⟨hy.1, ?_⟩
          have := hypDist_triangle hp hzD hy.1
          have h4 : 3 * (A₃ * β) ≤ 2 ^ (k₃ + 2) * β := by
            have h5 : 3 * A₃ ≤ 2 ^ (k₃ + 2) := by
              rw [pow_add]; norm_num; linarith
            have := mul_le_mul_of_nonneg_right h5 hβ.le
            linarith
          linarith [hy.2]
      _ ≤ (C₁ : ℝ≥0∞) ^ (k₃ + 2) * μ (hypBall p β) := hpowD p hp β hβ hβD _ le_rfl
      _ ≤ (C₁ : ℝ≥0∞) ^ (k₃ + 2) * C₀ := by
          gcongr
          exact (measure_mono (hin.trans (l4_cayleyPre_mono
            (l4_midThird_subset hg.1.le _ _)))).trans hμb
      _ = ENNReal.ofReal M := by
          rw [hM, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity),
            ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_natCast]
  have h2A : 2 * (A₃ * β) ≤ A' * massRadiusDisc μ z := by
    rcases le_or_gt (massRadiusDisc μ z) (2 * (A₃ * β)) with hle | hlt
    · have h1 := (hlow z hzD (2 * (A₃ * β)) hle (by linarith)).trans hball
      rw [ENNReal.ofReal_le_ofReal_iff hM0] at h1
      exact (l4_le_of_rpow hc hδ (hρ' z hzD) (by positivity) h1).trans
        (mul_le_mul_of_nonneg_right hA'2 (hρ' z hzD).le)
    · exact hlt.le.trans (le_mul_of_one_le_left (hρ' z hzD).le hA'1)
  calc hypDist z w ≤ A' * massRadiusDisc μ z := hzw.le.trans h2A
    _ ≤ A' * (CN * massRadiusDisc ν z) := mul_le_mul_of_nonneg_left (hCNz z hzD) (by linarith)
    _ = A' * CN * massRadiusDisc ν z := by ring

/-- Disc: every piece contains the hyperbolic ball of radius `ρ_ν(p) / A_L` around a point `p`. -/
theorem l4_disc_fat {ν : Measure ℂ} {N : ℕ} {Λ L A_L D_L x₁ x₂ y₁ y₂ : ℝ} (hN : 1 ≤ N)
    (hA_L : 1 ≤ A_L) (hioL : DiscBoxBalls Λ L A_L D_L) (hLe : IsRectLE L x₁ x₂ y₁ y₂)
    (hy0 : 0 < y₁) (hl : y₂ - y₁ ≤ Λ * y₁) (hμ : ν (cayleyPre (rect x₁ x₂ y₁ y₂)) = N) :
    ∃ c ∈ cayleyPre (rect x₁ x₂ y₁ y₂), {w | w ∈ 𝔻 ∧ hypDist c w < 1 / A_L * massRadiusDisc ν c} ⊆
      cayleyPre (rect x₁ x₂ y₁ y₂) := by
  have : 0 < A_L := by linarith
  obtain ⟨p, hp, β, hβ, -, hin, hout⟩ := hioL _ _ _ _ hLe hy0 hl
  have hmid := l4_cayleyPre_mono (l4_midThird_subset hLe.1.le y₁ y₂)
  have hpP : p ∈ cayleyPre (rect x₁ x₂ y₁ y₂) :=
    hmid (hin ⟨hp, by rw [hypDist_self]; exact hβ⟩)
  have hρ : massRadiusDisc ν p ≤ A_L * β := by
    refine l4_massRadiusDisc_le (by positivity) ?_
    calc (1 : ℝ≥0∞) ≤ N := by exact_mod_cast hN
      _ = ν (cayleyPre (rect x₁ x₂ y₁ y₂)) := hμ.symm
      _ ≤ ν (hypBall p (A_L * β)) := measure_mono hout
  refine ⟨p, hpP, fun w ⟨hw𝔻, hw⟩ ↦ hmid (hin ⟨hw𝔻, ?_⟩)⟩
  calc hypDist p w < 1 / A_L * massRadiusDisc ν p := hw
    _ ≤ 1 / A_L * (A_L * β) := by gcongr
    _ = β := by field_simp

/-- **Lemma 4 (disc)**, uniform form with the shape of the pieces. -/
theorem l4_disc_strong (Cd : ℝ≥0) (R₀ : ℝ) (N : ℕ) (hN : 1 ≤ N) :
    ∃ a A L Λ : ℝ, 0 < a ∧ 0 < A ∧ 1 ≤ L ∧ 0 < Λ ∧ ∀ ν : Measure ℂ, MeasClassDisc ν Cd R₀ →
      ∃ R : ℕ → Set ℂ, IsMassPartition ν 𝔻 hypDist (massRadiusDisc ν) N a A R ∧
        ∀ i, ∃ x₁ x₂ y₁ y₂ : ℝ, IsRectLE L x₁ x₂ y₁ y₂ ∧ 0 < y₁ ∧ y₂ - y₁ ≤ Λ * y₁ ∧
          R i = discBox x₁ x₂ y₁ y₂ := by
  have h0D : (0 : ℂ) ∈ 𝔻 := mem_ball_self one_pos
  by_cases hR₀ : 0 < R₀
  swap
  · refine ⟨1, 1, 1, 1, one_pos, one_pos, le_rfl, one_pos, fun ν hν ↦ ?_⟩
    exfalso
    have h := hν.mass 0 h0D
    have he : hypBall 0 R₀ = ∅ := by
      ext w
      simp only [hypBall, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and, not_lt]
      intro _
      exact (not_lt.1 hR₀).trans (hypDist_nonneg _ _)
    rw [he, measure_empty] at h
    exact absurd h (not_lt.2 zero_le)
  -- constants, chosen before the measure
  set R' : ℝ := (2 * ⌈(N : ℝ) / 1⌉₊ + 1) * R₀
  have hR'0 : 0 < R' := by positivity
  set Λ : ℝ := 64 * Real.exp (4 * R') with hΛ
  have hΛ1 : 1 < Λ := by
    have : 1 ≤ Real.exp (4 * R') := Real.one_le_exp (by positivity)
    rw [hΛ]; linarith
  have hΛ0 : 0 < Λ := by linarith
  obtain ⟨A₃, D₃, hA₃, hD₃, hio₃⟩ := discBox_inner_outer Λ 3 hΛ0 (by norm_num)
  set k₃ : ℕ := ⌈A₃⌉₊
  have hk₃A : A₃ ≤ 2 ^ k₃ := (Nat.le_ceil A₃).trans (by exact_mod_cast (Nat.lt_two_pow_self).le)
  set R₁ : ℝ := 2 ^ (k₃ + 2) * D₃ with hR₁
  obtain ⟨C₁, -, hC₁⟩ := doubling_upTo_quant (X := HDisc) Cd R₁
  set C₀ : ℕ := ⌈(C₁ : ℝ) ^ k₃⌉₊
  obtain ⟨C_E, -, hCE⟩ := euclid_doubling_cayley_quant Cd
  set κ : ℝ := 1 / (48 * Λ) with hκ
  set L : ℝ := rectRatioBound C₀ C_E κ
  have hL1 : 1 ≤ L := one_le_rectRatioBound _ _ _
  obtain ⟨A_L, D_L, hA_L, -, hioL⟩ := discBox_inner_outer Λ L hΛ0 hL1
  obtain ⟨c, Cb, δ, sb, hc, -, hδ, -, hb⟩ :=
    measure_ball_massRadiusM_bounds_quant (X := HDisc) Cd R' (2 * D₃)
  obtain ⟨CN, hCN1, hCN⟩ := massRadiusM_inv_smul_quant (X := HDisc) Cd R₀ N hN
  set M : ℝ := (C₁ : ℝ) ^ (k₃ + 2) * C₀ with hM
  set A' : ℝ := max 1 ((M / c) ^ (1 / δ))
  have hA'1 : 1 ≤ A' := le_max_left _ _
  have : 0 < CN := by linarith
  have : 0 < A_L := by linarith
  refine ⟨1 / A_L, A' * CN, L, Λ, by positivity, by positivity, hL1, hΛ0, fun ν hν ↦ ?_⟩
  have hclass' := l4_disc_mu hN hR₀ hν
  obtain ⟨g, hgdisj, hgcover, hgood⟩ := l4_disc_pieces hR'0 hΛ hΛ1 hclass' hA₃ hD₃ hk₃A hio₃ hR₁
    hC₁ (l4_coe_pow_le_ceil C₁ k₃) hκ hCE
  obtain ⟨hmeas, hdisj, hcover⟩ := l4_disc_partition hgdisj hgcover
  have hmass : ∀ i, ν (cayleyPre (rect (g i).1 (g i).2.1 (g i).2.2.1 (g i).2.2.2)) = N :=
    fun i ↦ by
      rw [l4_smul_apply hN, ← map_restrict_cayley_apply _ (measurableSet_rect _ _ _ _),
        (hgood i).1, mul_one]
  have hCNz : ∀ z ∈ 𝔻, massRadiusDisc ((N : ℝ≥0∞)⁻¹ • ν) z ≤ CN * massRadiusDisc ν z :=
    fun z hz ↦ by
      have h := (hCN (discPull ν) hν.measClassM_discPull (HDisc.mk z hz)).2
      rwa [l4_massRadiusM_discPull_smul ν _ (HDisc.mk z hz),
        ← massRadiusDisc_eq ν (HDisc.mk z hz)] at h
  refine ⟨fun i ↦ cayleyPre (rect (g i).1 (g i).2.1 (g i).2.2.1 (g i).2.2.2),
    ⟨hmeas, hdisj, hcover, hmass, fun i ↦ ?_, fun i ↦ ?_⟩, fun i ↦ ?_⟩
  · -- upper size
    obtain ⟨-, -, x₁', x₂', y₁', y₂', hg, hPb, hμb, hsub⟩ := hgood i
    refine l4_disc_size hA₃ hk₃A hc hδ hM hA'1 (le_max_right _ _) hio₃
      (l4_disc_hpow hclass' hD₃ hR₁ hC₁) (l4_disc_low hclass' hb)
      (fun z hz ↦ massRadiusDisc_pos ⟨Cd, hclass'.doubling⟩ (l4_disc_finB hclass')
        ⟨R', hR'0, fun z hz ↦ (hclass'.mass z hz).le⟩ hz) hCNz hg hPb ?_
      (l4_cayleyPre_mono hsub)
    exact (map_restrict_cayley_apply _ (measurableSet_rect _ _ _ _)).symm.trans_le hμb
  · -- fatness
    obtain ⟨-, hLe, x₁', x₂', y₁', y₂', -, hPb, -, hsub⟩ := hgood i
    obtain ⟨h1, h2, h3, h4⟩ := l4_rect_subset_coords hLe.1 hLe.2.1 hsub
    obtain ⟨hy0, hl, -⟩ := l4_disc_P_mono hΛ0 hPb h1 h2 h3 h4
    exact l4_disc_fat hN hA_L hioL hLe hy0 hl (hmass i)
  · obtain ⟨-, hLe, x₁', x₂', y₁', y₂', -, hPb, -, hsub⟩ := hgood i
    obtain ⟨h1, h2, h3, h4⟩ := l4_rect_subset_coords hLe.1 hLe.2.1 hsub
    obtain ⟨hy0, hl, -⟩ := l4_disc_P_mono hΛ0 hPb h1 h2 h3 h4
    exact ⟨_, _, _, _, hLe, hy0, hl, rfl⟩

/-- **Lemma 4 (plane).** -/
theorem lemma4_plane {μ : Measure ℂ} (hd : IsLocallyDoubling μ)
    (hfin : ∀ z r, μ (ball z r) < ∞) (hm : ∃ R : ℝ, 0 < R ∧ ∀ z, 1 ≤ μ (ball z R))
    (N : ℕ) (hN : 1 ≤ N) :
    ∃ (a A L : ℝ) (R : ℕ → Set ℂ), 0 < a ∧ 0 < A ∧ 1 ≤ L ∧
      IsMassPartition μ univ dist (massRadius μ) N a A R ∧
      ∀ i, ∃ x₁ x₂ y₁ y₂ : ℝ, IsRectLE L x₁ x₂ y₁ y₂ ∧ R i = rect x₁ x₂ y₁ y₂ := by
  obtain ⟨C, hC⟩ := hd
  obtain ⟨r, -, hr⟩ := exists_radius_lt_measure_ball_plane hm 1
  have hclass : MeasClassPlane μ C r := ⟨hC, fun z ↦ by simpa using hr z, fun K hK ↦ by
    obtain ⟨ρ, hρ⟩ := hK.isBounded.subset_ball 0
    exact (measure_mono hρ).trans_lt (hfin 0 ρ)⟩
  obtain ⟨a, A, L, ha, hA, hL, h⟩ := l4_plane_strong C r N hN
  obtain ⟨R, hR, hshape⟩ := h μ hclass
  exact ⟨a, A, L, R, ha, hA, hL, hR, hshape⟩

/-- **Lemma 4 (disc)**: horocyclic boxes (preimages of rectangles under Cayley). -/
theorem lemma4_disc {μ : Measure ℂ} (hd : IsLocallyDoublingDisc μ)
    (hfin : ∀ z ∈ 𝔻, ∀ r, μ (hypBall z r) < ∞)
    (hm : ∃ R : ℝ, 0 < R ∧ ∀ z ∈ 𝔻, 1 ≤ μ (hypBall z R)) (N : ℕ) (hN : 1 ≤ N) :
    ∃ (a A L Λ : ℝ) (R : ℕ → Set ℂ), 0 < a ∧ 0 < A ∧ 1 ≤ L ∧ 0 < Λ ∧
      IsMassPartition μ 𝔻 hypDist (massRadiusDisc μ) N a A R ∧
      ∀ i, ∃ x₁ x₂ y₁ y₂ : ℝ, IsRectLE L x₁ x₂ y₁ y₂ ∧ 0 < y₁ ∧ y₂ - y₁ ≤ Λ * y₁ ∧
        R i = discBox x₁ x₂ y₁ y₂ := by
  obtain ⟨C, hC⟩ := hd
  obtain ⟨r, -, hr⟩ := exists_radius_lt_measure_hypBall hm 1
  have hclass : MeasClassDisc μ C r := ⟨hC, fun z hz ↦ by simpa using hr z hz, fun K hK hKc ↦ by
    obtain ⟨ρ, hρ⟩ := l4_compact_subset_hypBall hK hKc
    exact (measure_mono hρ).trans_lt (hfin 0 (mem_ball_self one_pos) ρ)⟩
  obtain ⟨a, A, L, Λ, ha, hA, hL, hΛ, h⟩ := l4_disc_strong C r N hN
  obtain ⟨R, hR, hshape⟩ := h μ hclass
  exact ⟨a, A, L, Λ, R, ha, hA, hL, hΛ, hR, hshape⟩

/-- **Lemma 4 (line)**: intervals of mass `N`. -/
theorem lemma4_line {μ : Measure ℂ} (hd : IsLocallyDoublingLine μ)
    (hfin : ∀ x r : ℝ, μ (lineInterval x r) < ∞)
    (hm : ∃ R : ℝ, 0 < R ∧ ∀ x : ℝ, 1 ≤ μ (lineInterval x R)) (N : ℕ) (hN : 1 ≤ N) :
    ∃ (a A : ℝ) (R : ℕ → Set ℂ), 0 < a ∧ 0 < A ∧
      IsMassPartition μ (range fun t : ℝ ↦ (t : ℂ)) dist (fun z ↦ massRadiusLine μ z.re) N a A R ∧
      ∀ i, ∃ s t : ℝ, s < t ∧ R i = (fun u : ℝ ↦ (u : ℂ)) '' Ico s t := by
  obtain ⟨Cd, R₀, hC⟩ := lineCut_measClassLine_of hd hfin hm
  obtain ⟨a, A, ha, hA, h⟩ := lineCut_partition_quant Cd R₀ N hN
  obtain ⟨R, h1, h2, h3, h4, h5, h6, h7⟩ := h μ hC
  exact ⟨a, A, R, ha, hA, ⟨h1, h2, h3, h4, h5, h6⟩, h7⟩

/-! ### Claim 2 and the consequences used by M08/M09 (plane; disc and line analogous) -/

/-! ### Quantitative forms (requested by M08 §4.1) -/

/-- (M05, quantitative Lemma 4). -/
theorem lemma4_plane_quant (Cd : ℝ≥0) (R₀ : ℝ) (N : ℕ) (hN : 1 ≤ N) : ∃ a A : ℝ, 0 < a ∧ 0 < A ∧
    ∀ ν : Measure ℂ, MeasClassPlane ν Cd R₀ →
      ∃ R : ℕ → Set ℂ, IsMassPartition ν univ dist (massRadius ν) N a A R := by
  obtain ⟨a, A, L, ha, hA, -, h⟩ := l4_plane_strong Cd R₀ N hN
  exact ⟨a, A, ha, hA, fun ν hν ↦ (h ν hν).imp fun R hR ↦ hR.1⟩
theorem lemma4_disc_quant (Cd : ℝ≥0) (R₀ : ℝ) (N : ℕ) (hN : 1 ≤ N) : ∃ a A : ℝ, 0 < a ∧ 0 < A ∧
    ∀ ν : Measure ℂ, MeasClassDisc ν Cd R₀ →
      ∃ R : ℕ → Set ℂ, IsMassPartition ν 𝔻 hypDist (massRadiusDisc ν) N a A R := by
  obtain ⟨a, A, L, Λ, ha, hA, -, -, h⟩ := l4_disc_strong Cd R₀ N hN
  exact ⟨a, A, ha, hA, fun ν hν ↦ (h ν hν).imp fun R hR ↦ hR.1⟩
theorem lemma4_line_quant (Cd : ℝ≥0) (R₀ : ℝ) (N : ℕ) (hN : 1 ≤ N) : ∃ a A : ℝ, 0 < a ∧ 0 < A ∧
    ∀ ν : Measure ℂ, MeasClassLine ν Cd R₀ →
      ∃ R : ℕ → Set ℂ, IsMassPartition ν (range fun t : ℝ ↦ (t : ℂ)) dist
        (fun z ↦ massRadiusLine ν z.re) N a A R := by
  obtain ⟨a, A, ha, hA, h⟩ := lineCut_partition_quant Cd R₀ N hN
  refine ⟨a, A, ha, hA, fun ν hν ↦ ?_⟩
  obtain ⟨R, h1, h2, h3, h4, h5, h6, -⟩ := h ν hν
  exact ⟨R, ⟨h1, h2, h3, h4, h5, h6⟩⟩

end OC
