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

theorem l4_midThird_subset {x₁ x₂ y₁ y₂ : ℝ} (hx : x₁ ≤ x₂) (hy : y₁ ≤ y₂) :
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

/-- From `c (r/ρ)^δ ≤ M` to `r ≤ (M/c)^{1/δ} ρ`. -/
theorem l4_le_of_rpow {c δ M r ρ : ℝ} (hc : 0 < c) (hδ : 0 < δ) (hM : 0 ≤ M) (hρ : 0 < ρ)
    (hr : 0 ≤ r) (h : c * (r / ρ) ^ δ ≤ M) : r ≤ (M / c) ^ (1 / δ) * ρ := by
  have h2 : (r / ρ) ^ δ ≤ M / c := by rw [le_div_iff₀ hc]; linarith
  have h3 : r / ρ ≤ (M / c) ^ (1 / δ) := by
    have h4 := Real.rpow_le_rpow (by positivity) h2 (show (0 : ℝ) ≤ 1 / δ by positivity)
    rwa [← Real.rpow_mul (by positivity), mul_one_div_cancel hδ.ne', Real.rpow_one] at h4
  rwa [div_le_iff₀ hρ] at h3

/-- A countable family of finite partitions of disjoint blocks, reindexed by `ℕ`. -/
theorem l4_sigma_partition {n : ℤ × ℤ → ℕ} (hn : ∀ jk, 1 ≤ n jk) (B : ℤ × ℤ → Set ℂ)
    (hB : Pairwise (Function.onFun Disjoint B)) (f : (Σ jk : ℤ × ℤ, Fin (n jk)) → Set ℂ)
    (hf : ∀ jk, Pairwise (Function.onFun Disjoint fun a : Fin (n jk) ↦ f ⟨jk, a⟩))
    (hfB : ∀ jk, ⋃ a, f ⟨jk, a⟩ = B jk) :
    ∃ e : ℕ ≃ (Σ jk : ℤ × ℤ, Fin (n jk)), Pairwise (Function.onFun Disjoint fun i ↦ f (e i)) ∧
      ⋃ i, f (e i) = ⋃ jk, B jk := by
  haveI : Infinite (Σ jk : ℤ × ℤ, Fin (n jk)) :=
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
    rw [abs_le]; constructor <;> linarith [neg_abs_le x₁, le_abs_self x₂, abs_nonneg x₁, abs_nonneg x₂]
  have : |z.im| ≤ |y₁| + |y₂| := by
    rw [abs_le]; constructor <;> linarith [neg_abs_le y₁, le_abs_self y₂, abs_nonneg y₁, abs_nonneg y₂]
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
  rw [Measure.smul_apply, smul_eq_mul, ← mul_assoc,
    ENNReal.mul_inv_cancel hNne (ENNReal.natCast_ne_top N), one_mul]

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
    exact absurd h (not_lt.2 zero_le')
  -- constants, chosen before the measure
  set R' : ℝ := ((N : ℝ) + 1) * R₀ with hR'
  have hR'0 : 0 < R' := by positivity
  set S : ℝ := 2 * R' with hS
  have hS0 : 0 < S := by positivity
  obtain ⟨C₁, hC₁1, hC₁⟩ := doubling_upTo_quant (X := ℂ) Cd (16 * S)
  set C₀ : ℕ := ⌈(C₁ : ℝ) ^ 5⌉₊ with hC₀
  set C_E : ℝ := (C₁ : ℝ) ^ 3 with hCE
  set L : ℝ := rectRatioBound C₀ C_E 1 with hL
  have hL1 : 1 ≤ L := one_le_rectRatioBound _ _ _
  obtain ⟨c, Cb, δ, sb, hc, -, hδ, -, hb⟩ :=
    measure_ball_massRadiusM_bounds_quant (X := ℂ) Cd R' (12 * S)
  obtain ⟨CN, hCN1, hCN⟩ := massRadiusM_inv_smul_quant (X := ℂ) Cd R₀ N hN
  set M : ℝ := (C₁ : ℝ) ^ 6 * C₀ with hM
  have hM0 : 0 ≤ M := by positivity
  set A' : ℝ := max 1 ((M / c) ^ (1 / δ)) with hA'
  have hA'1 : 1 ≤ A' := le_max_left _ _
  have hL0 : 0 < L := by linarith
  have hCN0 : 0 < CN := by linarith
  refine ⟨1 / (6 * L), A' * CN, L, by positivity, by positivity, hL1, fun ν hν ↦ ?_⟩
  -- the measure `μ' = ν / N` and its properties
  set μ' : Measure ℂ := (N : ℝ≥0∞)⁻¹ • ν with hμ'
  have hNne : (N : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hNtop : (N : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top N
  have hμ'apply : ∀ s, μ' s = (N : ℝ≥0∞)⁻¹ * ν s := fun s ↦ by
    rw [hμ', Measure.smul_apply, smul_eq_mul]
  have hfinν : ∀ s : Set ℂ, Bornology.IsBounded s → ν s < ∞ := fun s hs ↦ by
    obtain ⟨r, hr⟩ := hs.subset_closedBall 0
    exact (measure_mono hr).trans_lt (hν.finite _ (isCompact_closedBall 0 r))
  have hfin'b : ∀ s : Set ℂ, Bornology.IsBounded s → μ' s < ∞ := fun s hs ↦ by
    rw [hμ'apply]; exact ENNReal.mul_lt_top (ENNReal.inv_lt_top.2 (by positivity)) (hfinν s hs)
  have hfin' : ∀ z r, μ' (ball z r) < ∞ := fun z r ↦ hfin'b _ Metric.isBounded_ball
  have hdbl' : IsLocDoublingMWith μ' Cd := fun z r hr h2r ↦ by
    rw [hμ'apply, hμ'apply, mul_left_comm]
    gcongr
    exact hν.doubling z r hr h2r
  have hmass' : ∀ z, 1 ≤ μ' (ball z R') := fun z ↦ by
    rw [hμ'apply]
    calc (1 : ℝ≥0∞) = (N : ℝ≥0∞)⁻¹ * N := (ENNReal.inv_mul_cancel hNne hNtop).symm
      _ ≤ (N : ℝ≥0∞)⁻¹ * ν (ball z R') := by gcongr; exact (l4_growth_plane hR₀ hν.mass N z).le
  have hclass' : MeasClassM μ' Cd R' := ⟨hdbl', hmass', hfin'⟩
  have hd' : IsLocallyDoubling μ' := ⟨Cd, hdbl'⟩
  have hdC : ∀ z r, 0 < r → r ≤ 16 * S → μ' (ball z (2 * r)) ≤ C₁ * μ' (ball z r) :=
    hC₁ μ' hdbl'
  have hpow : ∀ z (k : ℕ) r, 0 < r → 2 ^ k * r ≤ 2 * (16 * S) →
      μ' (ball z (2 ^ k * r)) ≤ (C₁ : ℝ≥0∞) ^ k * μ' (ball z r) := fun z ↦
    l4_iter (f := fun r ↦ μ' (ball z r)) (hdC z)
  have hre' : ∀ x : ℝ, μ' {w | w.re = x} = 0 := by
    intro x
    have : {w : ℂ | w.re = x} = {z | ∃ t : ℝ, z = (x : ℂ) + t * I} := by
      ext w
      simp only [mem_setOf_eq]
      constructor
      · intro h; exact ⟨w.im, Complex.ext (by simp [h]) (by simp)⟩
      · rintro ⟨t, rfl⟩; simp
    rw [this]
    exact measure_eq_zero_of_isPorous_plane hd' hfin' (isPorous_line _ _)
  have him' : ∀ y : ℝ, μ' {w | w.im = y} = 0 := by
    intro y
    have : {w : ℂ | w.im = y} = {z | ∃ t : ℝ, z = (y : ℂ) * I + t * 1} := by
      ext w
      simp only [mem_setOf_eq]
      constructor
      · intro h; exact ⟨w.re, Complex.ext (by simp) (by simp [h])⟩
      · rintro ⟨t, rfl⟩; simp
    rw [this]
    exact measure_eq_zero_of_isPorous_plane hd' hfin' (isPorous_line _ _)
  have hfinR : ∀ x₁ x₂ y₁ y₂ : ℝ, μ' (rect x₁ x₂ y₁ y₂) < ∞ := fun x₁ x₂ y₁ y₂ ↦
    hfin'b _ (Metric.isBounded_ball.subset (l4_rect_subset_ball x₁ x₂ y₁ y₂))
  -- coarse rows `[jS, (j+1)S)`
  have hrow : ∀ j : ℤ, ∃ x : ℤ → ℝ, StrictMono x ∧
      (∀ k, S ≤ x (k + 1) - x k ∧ x (k + 1) - x k ≤ 2 * S) ∧
      (∀ t : ℝ, ∃ k, t ∈ Ico (x k) (x (k + 1))) ∧
      ∀ k, ∃ n : ℕ, 1 ≤ n ∧ μ' (rect (x k) (x (k + 1)) (j * S) ((j + 1) * S)) = n := by
    intro j
    refine exists_strip_cuts hre' hS0 (fun a b ↦ hfinR _ _ _ _) fun a ↦ ?_
    refine (hmass' ((a + R' : ℝ) + ((j * S + R' : ℝ) : ℂ) * I)).trans (measure_mono ?_)
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
  choose X hXmono hXgap hXcov hXn using hrow
  choose n hn1 hnμ using hXn
  -- admissibility, the threshold `C₀` and the doubling scale
  set P : ℝ → ℝ → ℝ → ℝ → Prop := fun x₁ x₂ y₁ y₂ ↦ x₂ - x₁ ≤ 2 * S ∧ y₂ - y₁ ≤ 2 * S with hPdef
  have hPher : ∀ x₁ x₂ y₁ y₂ x₁' x₂' y₁' y₂' : ℝ, P x₁ x₂ y₁ y₂ → x₁ ≤ x₁' → x₂' ≤ x₂ →
      y₁ ≤ y₁' → y₂' ≤ y₂ → P x₁' x₂' y₁' y₂' := by
    intro x₁ x₂ y₁ y₂ x₁' x₂' y₁' y₂' h h1 h2 h3 h4
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  have hC₁5 : ((C₁ : ℝ≥0∞)) ^ 5 ≤ (C₀ : ℝ≥0∞) := by
    rw [← ENNReal.coe_pow, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (by push_cast; exact Nat.le_ceil _)
  have hC₀' : ∀ x₁ x₂ y₁ y₂ : ℝ, IsRectLE 3 x₁ x₂ y₁ y₂ → P x₁ x₂ y₁ y₂ →
      (C₀ : ℝ≥0∞) < μ' (rect x₁ x₂ y₁ y₂) → 1 < μ' (midThird x₁ x₂ y₁ y₂) := by
    intro x₁ x₂ y₁ y₂ hg hP hlt
    obtain ⟨p, r, hr, h6r, hin, hout⟩ := rect_inner_outer (by norm_num : (1 : ℝ) ≤ 3) hg
    have hrS : r ≤ S / 3 := by
      have := max_le hP.1 hP.2; linarith
    have h32 : μ' (rect x₁ x₂ y₁ y₂) ≤ (C₁ : ℝ≥0∞) ^ 5 * μ' (midThird x₁ x₂ y₁ y₂) := by
      calc μ' (rect x₁ x₂ y₁ y₂) ≤ μ' (ball p (2 ^ 5 * r)) :=
            measure_mono (hout.trans (ball_subset_ball (by nlinarith)))
        _ ≤ (C₁ : ℝ≥0∞) ^ 5 * μ' (ball p r) := hpow p 5 r hr (by nlinarith)
        _ ≤ (C₁ : ℝ≥0∞) ^ 5 * μ' (midThird x₁ x₂ y₁ y₂) := by gcongr
    by_contra hle
    push_neg at hle
    have := hlt.trans_le (h32.trans (by
      calc (C₁ : ℝ≥0∞) ^ 5 * μ' (midThird x₁ x₂ y₁ y₂) ≤ (C₁ : ℝ≥0∞) ^ 5 * 1 := by gcongr
        _ ≤ (C₀ : ℝ≥0∞) := by rw [mul_one]; exact hC₁5))
    exact lt_irrefl _ this
  have hσ' : ∀ x₁ x₂ y₁ y₂ : ℝ, IsRectLE 3 x₁ x₂ y₁ y₂ → P x₁ x₂ y₁ y₂ →
      1 * max (x₂ - x₁) (y₂ - y₁) ≤ max (x₂ - x₁) (y₂ - y₁) ∧
      ∀ w ∈ rect x₁ x₂ y₁ y₂, ∀ r : ℝ, 0 < r → r ≤ max (x₂ - x₁) (y₂ - y₁) →
        μ' (ball w (4 * r)) ≤ ENNReal.ofReal C_E * μ' (ball w (r / 2)) := by
    intro x₁ x₂ y₁ y₂ _ hP
    refine ⟨by rw [one_mul], fun w _ r hr hrσ ↦ ?_⟩
    have hrS : r ≤ 2 * S := hrσ.trans (max_le hP.1 hP.2)
    have := hpow w 3 (r / 2) (by positivity) (by nlinarith)
    rw [show (2 : ℝ) ^ 3 * (r / 2) = 4 * r by ring] at this
    rw [hCE, ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_coe_nnreal]
    exact this
  have hpart := exists_rect_partition hre' him' P hPher (fun _ _ _ _ _ ↦ hfinR _ _ _ _) C₀ hC₀'
    (fun x₁ x₂ y₁ y₂ ↦ max (x₂ - x₁) (y₂ - y₁)) C_E 1 one_pos hσ'
  -- the blocks
  set nn : ℤ × ℤ → ℕ := fun jk ↦ n jk.1 jk.2 with hnn
  set B : ℤ × ℤ → Set ℂ := fun jk ↦
    rect (X jk.1 jk.2) (X jk.1 (jk.2 + 1)) (jk.1 * S) ((jk.1 + 1) * S) with hB
  have hblock : ∀ jk : ℤ × ℤ, ∃ q : Fin (nn jk) → ℝ × ℝ × ℝ × ℝ,
      Pairwise (Function.onFun Disjoint fun i ↦ rect (q i).1 (q i).2.1 (q i).2.2.1 (q i).2.2.2) ∧
      (⋃ i, rect (q i).1 (q i).2.1 (q i).2.2.1 (q i).2.2.2) = B jk ∧
      ∀ i, μ' (rect (q i).1 (q i).2.1 (q i).2.2.1 (q i).2.2.2) = 1 ∧
        IsRectLE L (q i).1 (q i).2.1 (q i).2.2.1 (q i).2.2.2 ∧
        ∃ x₁' x₂' y₁' y₂' : ℝ, IsRectLE 3 x₁' x₂' y₁' y₂' ∧ P x₁' x₂' y₁' y₂' ∧
          μ' (rect x₁' x₂' y₁' y₂') ≤ C₀ ∧
          rect (q i).1 (q i).2.1 (q i).2.2.1 (q i).2.2.2 ⊆ rect x₁' x₂' y₁' y₂' := by
    rintro ⟨j, k⟩
    have hg := hXgap j k
    have hl : ((j : ℝ) + 1) * S - j * S = S := by ring
    exact hpart (n j k) _ _ _ _ (hn1 j k)
      ⟨hXmono j (lt_add_one k), by nlinarith, by rw [hl]; linarith, by rw [hl]; linarith⟩
      ⟨hg.2, by rw [hl]; linarith⟩ (hnμ j k)
  choose q hqdisj hqunion hqprops using hblock
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
      · have : ((j : ℝ) + 1) ≤ j' := by exact_mod_cast h
        exact rect_disjoint_y (by nlinarith)
      · have : ((j' : ℝ) + 1) ≤ j := by exact_mod_cast h
        exact (rect_disjoint_y (by nlinarith)).symm
  have hBcover : ⋃ jk, B jk = univ := by
    refine eq_univ_of_forall fun z ↦ mem_iUnion.2 ?_
    set j := ⌊z.im / S⌋
    have hj1 : (j : ℝ) ≤ z.im / S := Int.floor_le _
    have hj2 : z.im / S < j + 1 := Int.lt_floor_add_one _
    rw [le_div_iff₀ hS0] at hj1
    rw [div_lt_iff₀ hS0] at hj2
    obtain ⟨k, hk⟩ := hXcov j z.re
    exact ⟨(j, k), hk, ⟨hj1, hj2⟩⟩
  set f : (Σ jk : ℤ × ℤ, Fin (nn jk)) → Set ℂ := fun p ↦
    rect (q p.1 p.2).1 (q p.1 p.2).2.1 (q p.1 p.2).2.2.1 (q p.1 p.2).2.2.2 with hf
  obtain ⟨e, hedisj, heunion⟩ := l4_sigma_partition (fun jk ↦ hn1 jk.1 jk.2) B hBdisj f
    (fun jk ↦ hqdisj jk) (fun jk ↦ hqunion jk)
  refine ⟨fun i ↦ f (e i), ⟨fun i ↦ measurableSet_rect _ _ _ _, hedisj,
    by rw [heunion, hBcover], fun i ↦ ?_, fun i ↦ ?_, fun i ↦ ?_⟩, fun i ↦ ?_⟩
  · -- mass `N`
    rw [l4_smul_apply hN, ← hμ', (hqprops _ _).1, mul_one]
  · -- upper size
    obtain ⟨-, -, x₁', x₂', y₁', y₂', hg, hPb, hμb, hsub⟩ := hqprops (e i).1 (e i).2
    obtain ⟨p, r, hr, h6r, hin, hout⟩ := rect_inner_outer (by norm_num : (1 : ℝ) ≤ 3) hg
    have hrS : r ≤ S / 3 := by
      have := max_le hPb.1 hPb.2; linarith
    have hgx := hg.1
    have hgy := hg.2.1
    intro z hz w hw
    have hzp : dist z p < 18 * r := by
      have := hout (hsub hz); rw [mem_ball] at this; linarith
    have hwp : dist w p < 18 * r := by
      have := hout (hsub hw); rw [mem_ball] at this; linarith
    have hzw : dist z w < 36 * r := by
      linarith [dist_triangle z p w, dist_comm w p]
    have hball : μ' (ball z (36 * r)) ≤ ENNReal.ofReal M := by
      calc μ' (ball z (36 * r)) ≤ μ' (ball p (2 ^ 6 * r)) := by
            refine measure_mono fun y hy ↦ ?_
            rw [mem_ball] at hy ⊢
            linarith [dist_triangle y z p]
        _ ≤ (C₁ : ℝ≥0∞) ^ 6 * μ' (ball p r) := hpow p 6 r hr (by nlinarith)
        _ ≤ (C₁ : ℝ≥0∞) ^ 6 * C₀ := by
            gcongr
            exact (measure_mono (hin.trans (l4_midThird_subset hgx.le hgy.le))).trans hμb
        _ = ENNReal.ofReal M := by
            rw [hM, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity),
              ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_natCast]
    have hρ' : 0 < massRadius μ' z := massRadius_pos hd' hfin' ⟨R', hR'0, hmass'⟩ z
    have h36 : 36 * r ≤ A' * massRadius μ' z := by
      rcases le_or_gt (massRadius μ' z) (36 * r) with hle | hlt
      · have h1 := ((hb μ' hclass' z (36 * r) hle (by linarith)).1).trans hball
        rw [ENNReal.ofReal_le_ofReal_iff hM0] at h1
        exact (l4_le_of_rpow hc hδ hM0 hρ' (by positivity) h1).trans
          (mul_le_mul_of_nonneg_right (le_max_right _ _) hρ'.le)
      · exact hlt.le.trans (le_mul_of_one_le_left hρ'.le hA'1)
    have hCNz := (hCN ν hν.measClassM z).2
    calc dist z w ≤ A' * massRadius μ' z := hzw.le.trans h36
      _ ≤ A' * (CN * massRadius ν z) := by gcongr; exact hCNz
      _ = A' * CN * massRadius ν z := by ring
  · -- fatness
    obtain ⟨hμ1, hLe, -⟩ := hqprops (e i).1 (e i).2
    obtain ⟨p, r, hr, -, hin, hout⟩ := rect_inner_outer hL1 hLe
    have hmid := l4_midThird_subset (x₁ := (q (e i).1 (e i).2).1) hLe.1.le hLe.2.1.le
    have hpP : p ∈ f (e i) := hmid (hin (mem_ball_self hr))
    have hρ : massRadius ν p ≤ 6 * L * r := by
      refine l4_massRadius_le (by positivity) ?_
      calc (1 : ℝ≥0∞) ≤ N := by exact_mod_cast hN
        _ = ν (f (e i)) := by rw [l4_smul_apply hN, ← hμ', hμ1, mul_one]
        _ ≤ ν (ball p (6 * L * r)) := measure_mono hout
    refine ⟨p, hpP, fun w ⟨_, hw⟩ ↦ hmid (hin ?_)⟩
    rw [mem_ball, dist_comm]
    calc dist p w < 1 / (6 * L) * massRadius ν p := hw
      _ ≤ 1 / (6 * L) * (6 * L * r) := by gcongr
      _ = r := by field_simp
  · obtain ⟨-, hLe, -⟩ := hqprops (e i).1 (e i).2
    exact ⟨_, _, _, _, hLe, rfl⟩

/-- Coordinates of nested non-degenerate rectangles. -/
theorem l4_rect_subset_coords {x₁ x₂ y₁ y₂ x₁' x₂' y₁' y₂' : ℝ} (hx : x₁ < x₂) (hy : y₁ < y₂)
    (h : rect x₁ x₂ y₁ y₂ ⊆ rect x₁' x₂' y₁' y₂') :
    x₁' ≤ x₁ ∧ x₂ ≤ x₂' ∧ y₁' ≤ y₁ ∧ y₂ ≤ y₂' := by
  have h0 := h (show (⟨x₁, y₁⟩ : ℂ) ∈ rect x₁ x₂ y₁ y₂ from ⟨⟨le_rfl, hx⟩, ⟨le_rfl, hy⟩⟩)
  refine ⟨h0.1.1, ?_, h0.2.1, ?_⟩
  · by_contra hc
    push_neg at hc
    have := h (show (⟨max x₁ x₂', y₁⟩ : ℂ) ∈ rect x₁ x₂ y₁ y₂ from
      ⟨⟨le_max_left _ _, max_lt hx hc⟩, ⟨le_rfl, hy⟩⟩)
    exact absurd this.1.2 (not_lt.2 (le_max_right _ _))
  · by_contra hc
    push_neg at hc
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
  simp only [mem_setOf_eq, Measure.smul_apply, smul_eq_mul, discPull_ball]

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
      simp only [hypBall, mem_setOf_eq, mem_empty_iff_false, iff_false, not_and, not_lt]
      intro _
      exact (not_lt.1 hR₀).trans (hypDist_nonneg _ _)
    rw [he, measure_empty] at h
    exact absurd h (not_lt.2 zero_le')
  -- constants, chosen before the measure
  set R' : ℝ := (2 * ⌈(N : ℝ) / 1⌉₊ + 1) * R₀ with hR'
  have hR'0 : 0 < R' := by positivity
  set Λ : ℝ := 64 * Real.exp (4 * R') with hΛ
  have hΛ1 : 1 < Λ := by
    have : 1 ≤ Real.exp (4 * R') := Real.one_le_exp (by positivity)
    rw [hΛ]; linarith
  have hΛ0 : 0 < Λ := by linarith
  obtain ⟨A₃, D₃, hA₃, hD₃, hio₃⟩ := discBox_inner_outer Λ 3 hΛ0 (by norm_num)
  set k₃ : ℕ := ⌈A₃⌉₊ with hk₃
  have hk₃A : A₃ ≤ 2 ^ k₃ := (Nat.le_ceil A₃).trans (by exact_mod_cast (Nat.lt_two_pow_self).le)
  set R₁ : ℝ := 2 ^ (k₃ + 2) * D₃ with hR₁
  obtain ⟨C₁, hC₁1, hC₁⟩ := doubling_upTo_quant (X := HDisc) Cd R₁
  set C₀ : ℕ := ⌈(C₁ : ℝ) ^ k₃⌉₊ with hC₀
  obtain ⟨C_E, hC_E, hCE⟩ := euclid_doubling_cayley_quant Cd
  set κ : ℝ := 1 / (48 * Λ) with hκ
  have hκ0 : 0 < κ := by positivity
  set L : ℝ := rectRatioBound C₀ C_E κ with hL
  have hL1 : 1 ≤ L := one_le_rectRatioBound _ _ _
  obtain ⟨A_L, D_L, hA_L, hD_L, hioL⟩ := discBox_inner_outer Λ L hΛ0 hL1
  obtain ⟨c, Cb, δ, sb, hc, -, hδ, -, hb⟩ :=
    measure_ball_massRadiusM_bounds_quant (X := HDisc) Cd R' (2 * D₃)
  obtain ⟨CN, hCN1, hCN⟩ := massRadiusM_inv_smul_quant (X := HDisc) Cd R₀ N hN
  set M : ℝ := (C₁ : ℝ) ^ (k₃ + 2) * C₀ with hM
  have hM0 : 0 ≤ M := by positivity
  set A' : ℝ := max 1 ((M / c) ^ (1 / δ)) with hA'
  have hA'1 : 1 ≤ A' := le_max_left _ _
  have hCN0 : 0 < CN := by linarith
  have hA_L0 : 0 < A_L := by linarith
  refine ⟨1 / A_L, A' * CN, L, Λ, by positivity, by positivity, hL1, hΛ0, fun ν hν ↦ ?_⟩
  -- the measure `μ' = ν / N`
  set μ' : Measure ℂ := (N : ℝ≥0∞)⁻¹ • ν with hμ'
  have hNne : (N : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hNtop : (N : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top N
  have hμ'apply : ∀ s, μ' s = (N : ℝ≥0∞)⁻¹ * ν s := fun s ↦ by
    rw [hμ', Measure.smul_apply, smul_eq_mul]
  have hdbl' : ∀ z ∈ 𝔻, ∀ r : ℝ, 0 < r → 2 * r < 1 →
      μ' (hypBall z (2 * r)) ≤ Cd * μ' (hypBall z r) := fun z hz r hr h2r ↦ by
    rw [hμ'apply, hμ'apply, mul_left_comm]
    gcongr
    exact hν.doubling z hz r hr h2r
  have hmassN : ∀ z ∈ 𝔻, (N : ℝ≥0∞) < ν (hypBall z R') := fun z hz ↦ by
    have := ofReal_lt_measure_hypBall hR₀ one_pos
      (fun z hz ↦ by rw [ENNReal.ofReal_one]; exact (hν.mass z hz).le) (N : ℝ) hz
    rwa [ENNReal.ofReal_natCast] at this
  have hmass' : ∀ z ∈ 𝔻, 1 < μ' (hypBall z R') := fun z hz ↦ by
    rw [hμ'apply]
    calc (1 : ℝ≥0∞) = (N : ℝ≥0∞)⁻¹ * N := (ENNReal.inv_mul_cancel hNne hNtop).symm
      _ < (N : ℝ≥0∞)⁻¹ * ν (hypBall z R') := by
          rw [mul_comm ((N : ℝ≥0∞)⁻¹) (N : ℝ≥0∞), mul_comm ((N : ℝ≥0∞)⁻¹) (ν _)]
          exact ENNReal.mul_lt_mul_left (ENNReal.inv_ne_zero.2 hNtop) (ENNReal.inv_ne_top.2 hNne)
            (hmassN z hz)
  have hfinK' : ∀ K ⊆ 𝔻, IsCompact K → μ' K < ∞ := fun K hK hKc ↦ by
    rw [hμ'apply]
    exact ENNReal.mul_lt_top (ENNReal.inv_lt_top.2 (by positivity)) (hν.finite K hK hKc)
  have hclass' : MeasClassDisc μ' Cd R' := ⟨hdbl', hmass', hfinK'⟩
  have hM' := hclass'.measClassM_discPull
  have hfinB : ∀ z ∈ 𝔻, ∀ r, μ' (hypBall z r) < ∞ := fun z hz r ↦ by
    exact (discPull_ball μ' ⟨z, hz⟩ r).symm.trans_lt (hM'.finite ⟨z, hz⟩ r)
  have hd' : IsLocallyDoublingDisc μ' := ⟨Cd, hdbl'⟩
  have hdC : ∀ p ∈ 𝔻, ∀ r, 0 < r → r ≤ R₁ →
      μ' (hypBall p (2 * r)) ≤ C₁ * μ' (hypBall p r) := fun p hp r hr hrR ↦ by
    have := hC₁ (discPull μ') hM'.doubling (HDisc.mk p hp) r hr hrR
    have e1 : discPull μ' (ball (HDisc.mk p hp) (2 * r)) = μ' (hypBall p (2 * r)) :=
      discPull_ball μ' _ _
    have e2 : discPull μ' (ball (HDisc.mk p hp) r) = μ' (hypBall p r) := discPull_ball μ' _ _
    rwa [e1, e2] at this
  have hpow : ∀ p ∈ 𝔻, ∀ (k : ℕ) r, 0 < r → 2 ^ k * r ≤ 2 * R₁ →
      μ' (hypBall p (2 ^ k * r)) ≤ (C₁ : ℝ≥0∞) ^ k * μ' (hypBall p r) := fun p hp ↦
    l4_iter (f := fun r ↦ μ' (hypBall p r)) (hdC p hp)
  -- the model measure `ν' = cayley_* (μ'|𝔻)` in the upper half-plane
  set ν' : Measure ℂ := (μ'.restrict 𝔻).map cayley with hν'
  have hν'apply : ∀ S, MeasurableSet S → ν' S = μ' (cayleyPre S) := fun S hS ↦
    map_restrict_cayley_apply μ' hS
  have hν'rect : ∀ x₁ x₂ y₁ y₂, ν' (rect x₁ x₂ y₁ y₂) = μ' (discBox x₁ x₂ y₁ y₂) :=
    fun _ _ _ _ ↦ hν'apply _ (measurableSet_rect _ _ _ _)
  have hcayPre𝔻 : ∀ S, cayleyPre S ∩ 𝔻 = cayleyPre S := fun S ↦
    inter_eq_left.2 fun _ hz ↦ hz.1
  have hre' : ∀ x : ℝ, ν' {w | w.re = x} = 0 := by
    intro x
    rw [hν'apply _ ((isClosed_eq Complex.continuous_re continuous_const).measurableSet),
      ← hcayPre𝔻]
    exact measure_inter_disc_eq_zero_of_isPorous hd' hfinB (isPorous_cayley_re x)
  have him' : ∀ y : ℝ, ν' {w | w.im = y} = 0 := by
    intro y
    rw [hν'apply _ ((isClosed_eq Complex.continuous_im continuous_const).measurableSet),
      ← hcayPre𝔻]
    exact measure_inter_disc_eq_zero_of_isPorous hd' hfinB (isPorous_cayley_im y)
  have hfinR : ∀ x₁ x₂ y₁ y₂ : ℝ, 0 < y₁ → ν' (rect x₁ x₂ y₁ y₂) < ∞ := by
    intro x₁ x₂ y₁ y₂ hy
    obtain ⟨K, hKc, hK𝔻, hsub⟩ := exists_isCompact_discBox_subset x₁ x₂ hy y₂
    rw [hν'rect]
    exact (measure_mono hsub).trans_lt (hfinK' K hK𝔻 hKc)
  -- coarse rows `[Λ^j, Λ^{j+1})`
  have hrow : ∀ j : ℤ, ∃ x : ℤ → ℝ, StrictMono x ∧
      (∀ k, (Λ - 1) * Λ ^ j ≤ x (k + 1) - x k ∧ x (k + 1) - x k ≤ 2 * ((Λ - 1) * Λ ^ j)) ∧
      (∀ t : ℝ, ∃ k, t ∈ Ico (x k) (x (k + 1))) ∧
      ∀ k, ∃ n : ℕ, 1 ≤ n ∧ ν' (rect (x k) (x (k + 1)) (Λ ^ j) (Λ * Λ ^ j)) = n := by
    intro j
    have hpj : 0 < Λ ^ j := zpow_pos hΛ0 j
    refine exists_strip_cuts hre' (by nlinarith) (fun a b ↦ hfinR _ _ _ _ hpj) fun a ↦ ?_
    obtain ⟨p, hp, hsub⟩ := exists_hypBall_subset_discBox_row hR'0 hpj a
    rw [hν'rect]
    exact (hmass' p hp).le.trans (measure_mono hsub)
  choose X hXmono hXgap hXcov hXn using hrow
  choose n hn1 hnμ using hXn
  -- admissibility, the threshold `C₀` and the Euclidean doubling scale
  set P : ℝ → ℝ → ℝ → ℝ → Prop := fun x₁ x₂ y₁ y₂ ↦
    0 < y₁ ∧ y₂ - y₁ ≤ Λ * y₁ ∧ x₂ - x₁ ≤ 2 * Λ * y₁ with hPdef
  have hPher : ∀ x₁ x₂ y₁ y₂ x₁' x₂' y₁' y₂' : ℝ, P x₁ x₂ y₁ y₂ → x₁ ≤ x₁' → x₂' ≤ x₂ →
      y₁ ≤ y₁' → y₂' ≤ y₂ → P x₁' x₂' y₁' y₂' := by
    intro x₁ x₂ y₁ y₂ x₁' x₂' y₁' y₂' h h1 h2 h3 h4
    obtain ⟨h5, h6, h7⟩ := h
    have h8 : Λ * y₁ ≤ Λ * y₁' := mul_le_mul_of_nonneg_left h3 hΛ0.le
    exact ⟨by linarith, by linarith, by linarith⟩
  have hC₁k : ((C₁ : ℝ≥0∞)) ^ k₃ ≤ (C₀ : ℝ≥0∞) := by
    rw [← ENNReal.coe_pow, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (by push_cast; exact Nat.le_ceil _)
  have hβle : ∀ β : ℝ, 0 < β → A₃ * β ≤ D₃ → β ≤ D₃ := fun β hβ h ↦
    (le_mul_of_one_le_left hβ.le hA₃).trans h
  have hk₃pos : (0 : ℝ) < 2 ^ k₃ := by positivity
  have hpow_ok : ∀ β : ℝ, 0 < β → β ≤ D₃ → ∀ i ≤ k₃ + 2, (2 : ℝ) ^ i * β ≤ 2 * R₁ := by
    intro β hβ hβD i hi
    have h1 : (2 : ℝ) ^ i ≤ 2 ^ (k₃ + 2) := pow_le_pow_right₀ (by norm_num) hi
    have h2 : (2 : ℝ) ^ i * β ≤ 2 ^ (k₃ + 2) * D₃ :=
      mul_le_mul h1 hβD hβ.le (by positivity)
    have h3 : 0 ≤ (2 : ℝ) ^ (k₃ + 2) * D₃ := by positivity
    rw [hR₁]; linarith
  have hC₀' : ∀ x₁ x₂ y₁ y₂ : ℝ, IsRectLE 3 x₁ x₂ y₁ y₂ → P x₁ x₂ y₁ y₂ →
      (C₀ : ℝ≥0∞) < ν' (rect x₁ x₂ y₁ y₂) → 1 < ν' (midThird x₁ x₂ y₁ y₂) := by
    intro x₁ x₂ y₁ y₂ hg hP hlt
    obtain ⟨p, hp, β, hβ, hAβ, hin, hout⟩ := hio₃ x₁ x₂ y₁ y₂ hg hP.1 hP.2.1
    have hβD := hβle β hβ hAβ
    have h32 : ν' (rect x₁ x₂ y₁ y₂) ≤ (C₁ : ℝ≥0∞) ^ k₃ * ν' (midThird x₁ x₂ y₁ y₂) := by
      rw [hν'rect, hν'apply _ (l4_measurableSet_midThird _ _ _ _)]
      calc μ' (discBox x₁ x₂ y₁ y₂) ≤ μ' (hypBall p (2 ^ k₃ * β)) :=
            measure_mono (hout.trans fun w hw ↦ ⟨hw.1, hw.2.trans_le
              (mul_le_mul_of_nonneg_right hk₃A hβ.le)⟩)
        _ ≤ (C₁ : ℝ≥0∞) ^ k₃ * μ' (hypBall p β) :=
            hpow p hp k₃ β hβ (hpow_ok β hβ hβD k₃ (by omega))
        _ ≤ (C₁ : ℝ≥0∞) ^ k₃ * μ' (cayleyPre (midThird x₁ x₂ y₁ y₂)) := by gcongr
    by_contra hle
    push_neg at hle
    have := hlt.trans_le (h32.trans (by
      calc (C₁ : ℝ≥0∞) ^ k₃ * ν' (midThird x₁ x₂ y₁ y₂) ≤ (C₁ : ℝ≥0∞) ^ k₃ * 1 := by gcongr
        _ ≤ (C₀ : ℝ≥0∞) := by rw [mul_one]; exact hC₁k))
    exact lt_irrefl _ this
  have hσ' : ∀ x₁ x₂ y₁ y₂ : ℝ, IsRectLE 3 x₁ x₂ y₁ y₂ → P x₁ x₂ y₁ y₂ →
      κ * max (x₂ - x₁) (y₂ - y₁) ≤ y₁ / 16 ∧
      ∀ w ∈ rect x₁ x₂ y₁ y₂, ∀ r : ℝ, 0 < r → r ≤ y₁ / 16 →
        ν' (ball w (4 * r)) ≤ ENNReal.ofReal C_E * ν' (ball w (r / 2)) := by
    intro x₁ x₂ y₁ y₂ hg hP
    obtain ⟨hy0, hl, -⟩ := hP
    refine ⟨?_, fun w hw r hr hry ↦ hCE μ' hdbl' w (by linarith [hw.2.1]) r hr
      (hry.trans (by linarith [hw.2.1]))⟩
    have hg3 := hg.2.2.1
    have hΛy : 0 ≤ Λ * y₁ := by positivity
    have hmax : max (x₂ - x₁) (y₂ - y₁) ≤ 3 * (Λ * y₁) := by
      apply max_le <;> linarith
    calc κ * max (x₂ - x₁) (y₂ - y₁) ≤ κ * (3 * (Λ * y₁)) := by gcongr
      _ = y₁ / 16 := by rw [hκ]; field_simp; ring
  have hpart := exists_rect_partition hre' him' P hPher (fun _ _ _ _ hP ↦ hfinR _ _ _ _ hP.1)
    C₀ hC₀' (fun _ _ y₁ _ ↦ y₁ / 16) C_E κ hκ0 hσ'
  -- the blocks
  set nn : ℤ × ℤ → ℕ := fun jk ↦ n jk.1 jk.2 with hnn
  set B : ℤ × ℤ → Set ℂ := fun jk ↦
    rect (X jk.1 jk.2) (X jk.1 (jk.2 + 1)) (Λ ^ jk.1) (Λ * Λ ^ jk.1) with hB
  have hblock : ∀ jk : ℤ × ℤ, ∃ q : Fin (nn jk) → ℝ × ℝ × ℝ × ℝ,
      Pairwise (Function.onFun Disjoint fun i ↦ rect (q i).1 (q i).2.1 (q i).2.2.1 (q i).2.2.2) ∧
      (⋃ i, rect (q i).1 (q i).2.1 (q i).2.2.1 (q i).2.2.2) = B jk ∧
      ∀ i, ν' (rect (q i).1 (q i).2.1 (q i).2.2.1 (q i).2.2.2) = 1 ∧
        IsRectLE L (q i).1 (q i).2.1 (q i).2.2.1 (q i).2.2.2 ∧
        ∃ x₁' x₂' y₁' y₂' : ℝ, IsRectLE 3 x₁' x₂' y₁' y₂' ∧ P x₁' x₂' y₁' y₂' ∧
          ν' (rect x₁' x₂' y₁' y₂') ≤ C₀ ∧
          rect (q i).1 (q i).2.1 (q i).2.2.1 (q i).2.2.2 ⊆ rect x₁' x₂' y₁' y₂' := by
    rintro ⟨j, k⟩
    have hg := hXgap j k
    have hpj : 0 < Λ ^ j := zpow_pos hΛ0 j
    have hl : Λ * Λ ^ j - Λ ^ j = (Λ - 1) * Λ ^ j := by ring
    have hh : 0 < (Λ - 1) * Λ ^ j := mul_pos (by linarith) hpj
    have e1 : (Λ - 1) * Λ ^ j = Λ * Λ ^ j - Λ ^ j := by ring
    have e2 : 2 * Λ * Λ ^ j = 2 * (Λ * Λ ^ j) := by ring
    have hlt : Λ ^ j < Λ * Λ ^ j := (lt_mul_iff_one_lt_left hpj).2 hΛ1
    exact hpart (n j k) _ _ _ _ (hn1 j k)
      ⟨hXmono j (lt_add_one k), hlt, by rw [hl]; linarith, by rw [hl]; linarith⟩
      ⟨hpj, by rw [hl]; linarith, by rw [e2]; linarith⟩ (hnμ j k)
  choose q hqdisj hqunion hqprops using hblock
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
      · refine rect_disjoint_y ?_
        rw [← zpow_one_add₀ hΛ0.ne', add_comm]
        exact zpow_le_zpow_right₀ hΛ1.le (by omega)
      · refine (rect_disjoint_y ?_).symm
        rw [← zpow_one_add₀ hΛ0.ne', add_comm]
        exact zpow_le_zpow_right₀ hΛ1.le (by omega)
  have hBcover : ⋃ jk, B jk = {w : ℂ | 0 < w.im} := by
    apply Subset.antisymm
    · refine iUnion_subset fun jk w hw ↦ ?_
      exact (zpow_pos hΛ0 jk.1).trans_le hw.2.1
    · intro w hw
      obtain ⟨j, hj1, hj2⟩ := exists_mem_Ico_zpow hw hΛ1
      obtain ⟨k, hk⟩ := hXcov j w.re
      refine mem_iUnion.2 ⟨(j, k), hk, hj1, ?_⟩
      rw [zpow_add_one₀ hΛ0.ne', mul_comm] at hj2
      exact hj2
  set f : (Σ jk : ℤ × ℤ, Fin (nn jk)) → Set ℂ := fun p ↦
    rect (q p.1 p.2).1 (q p.1 p.2).2.1 (q p.1 p.2).2.2.1 (q p.1 p.2).2.2.2 with hf
  obtain ⟨e, hedisj, heunion⟩ := l4_sigma_partition (fun jk ↦ hn1 jk.1 jk.2) B hBdisj f
    (fun jk ↦ hqdisj jk) (fun jk ↦ hqunion jk)
  -- the pieces are the Cayley preimages
  have hP_piece : ∀ i, P (q (e i).1 (e i).2).1 (q (e i).1 (e i).2).2.1
      (q (e i).1 (e i).2).2.2.1 (q (e i).1 (e i).2).2.2.2 := by
    intro i
    obtain ⟨-, hLe, x₁', x₂', y₁', y₂', -, hPb, -, hsub⟩ := hqprops (e i).1 (e i).2
    obtain ⟨h1, h2, h3, h4⟩ := l4_rect_subset_coords hLe.1 hLe.2.1 hsub
    exact hPher _ _ _ _ _ _ _ _ hPb h1 h2 h3 h4
  refine ⟨fun i ↦ cayleyPre (f (e i)), ⟨fun i ↦ ?_, fun i j hij ↦ ?_, ?_, fun i ↦ ?_,
    fun i ↦ ?_, fun i ↦ ?_⟩, fun i ↦ ?_⟩
  · -- measurability
    exact (measurable_cayley (measurableSet_rect _ _ _ _)).inter measurableSet_ball |>.congr
      (by ext z; simp only [cayleyPre, mem_inter_iff, mem_preimage, mem_setOf_eq]; exact and_comm)
  · -- disjointness
    show Disjoint (cayleyPre (f (e i))) (cayleyPre (f (e j)))
    exact Set.disjoint_left.2 fun z hz1 hz2 ↦ Set.disjoint_left.1 (hedisj hij) hz1.2 hz2.2
  · -- covering
    apply Subset.antisymm
    · exact iUnion_subset fun i z hz ↦ hz.1
    · intro z hz
      have hw : cayley z ∈ ⋃ i, f (e i) := by
        rw [heunion, hBcover]; exact cayley_im_pos hz
      obtain ⟨i, hi⟩ := mem_iUnion.1 hw
      exact mem_iUnion.2 ⟨i, hz, hi⟩
  · -- mass `N`
    rw [l4_smul_apply hN, ← hμ', ← hν'apply _ (measurableSet_rect _ _ _ _),
      (hqprops _ _).1, mul_one]
  · -- upper size
    obtain ⟨-, -, x₁', x₂', y₁', y₂', hg, hPb, hμb, hsub⟩ := hqprops (e i).1 (e i).2
    obtain ⟨p, hp, β, hβ, hAβ, hin, hout⟩ := hio₃ x₁' x₂' y₁' y₂' hg hPb.1 hPb.2.1
    have hβD := hβle β hβ hAβ
    intro z hz w hw
    have hzB : z ∈ discBox x₁' x₂' y₁' y₂' := l4_cayleyPre_mono hsub hz
    have hwB : w ∈ discBox x₁' x₂' y₁' y₂' := l4_cayleyPre_mono hsub hw
    have hzp := (hout hzB).2
    have hwp := (hout hwB).2
    have hzD := hz.1
    have hwD := hw.1
    have hzw : hypDist z w < 2 * (A₃ * β) := by
      have := hypDist_triangle hzD hp hwD
      rw [hypDist_comm z p] at this
      linarith
    have hball : μ' (hypBall z (2 * (A₃ * β))) ≤ ENNReal.ofReal M := by
      calc μ' (hypBall z (2 * (A₃ * β))) ≤ μ' (hypBall p (2 ^ (k₃ + 2) * β)) := by
            refine measure_mono fun y hy ↦ ⟨hy.1, ?_⟩
            have := hypDist_triangle hp hzD hy.1
            have h4 : 3 * (A₃ * β) ≤ 2 ^ (k₃ + 2) * β := by
              have h5 : 3 * A₃ ≤ 2 ^ (k₃ + 2) := by
                rw [pow_add]; norm_num; linarith
              have := mul_le_mul_of_nonneg_right h5 hβ.le
              linarith
            linarith [hy.2]
        _ ≤ (C₁ : ℝ≥0∞) ^ (k₃ + 2) * μ' (hypBall p β) :=
            hpow p hp (k₃ + 2) β hβ (hpow_ok β hβ hβD _ le_rfl)
        _ ≤ (C₁ : ℝ≥0∞) ^ (k₃ + 2) * C₀ := by
            gcongr
            exact (measure_mono (hin.trans (l4_cayleyPre_mono
              (l4_midThird_subset hg.1.le hg.2.1.le)))).trans
              ((hν'rect x₁' x₂' y₁' y₂').symm.trans_le hμb)
        _ = ENNReal.ofReal M := by
            rw [hM, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity),
              ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_natCast]
    have hρ' : 0 < massRadiusDisc μ' z :=
      massRadiusDisc_pos hd' hfinB ⟨R', hR'0, fun z hz ↦ (hmass' z hz).le⟩ hzD
    have h2A : 2 * (A₃ * β) ≤ A' * massRadiusDisc μ' z := by
      rcases le_or_gt (massRadiusDisc μ' z) (2 * (A₃ * β)) with hle | hlt
      · have hmr : massRadiusDisc μ' z = massRadiusM (discPull μ') (HDisc.mk z hzD) :=
          massRadiusDisc_eq μ' (HDisc.mk z hzD)
        have hbl : discPull μ' (ball (HDisc.mk z hzD) (2 * (A₃ * β))) =
            μ' (hypBall z (2 * (A₃ * β))) := discPull_ball μ' _ _
        have hb' := (hb (discPull μ') hM' (HDisc.mk z hzD) (2 * (A₃ * β))
          (by rw [← hmr]; exact hle) (by linarith)).1
        rw [hbl, ← hmr] at hb'
        have h1 := hb'.trans hball
        rw [ENNReal.ofReal_le_ofReal_iff hM0] at h1
        exact (l4_le_of_rpow hc hδ hM0 hρ' (by positivity) h1).trans
          (mul_le_mul_of_nonneg_right (le_max_right _ _) hρ'.le)
      · exact hlt.le.trans (le_mul_of_one_le_left hρ'.le hA'1)
    have hCNz := (hCN (discPull ν) hν.measClassM_discPull (HDisc.mk z hzD)).2
    have e1 : massRadiusM ((N : ℝ≥0∞)⁻¹ • discPull ν) (HDisc.mk z hzD) = massRadiusDisc μ' z :=
      l4_massRadiusM_discPull_smul ν _ (HDisc.mk z hzD)
    have e2 : massRadiusM (discPull ν) (HDisc.mk z hzD) = massRadiusDisc ν z :=
      (massRadiusDisc_eq ν (HDisc.mk z hzD)).symm
    rw [e1, e2] at hCNz
    calc hypDist z w ≤ A' * massRadiusDisc μ' z := hzw.le.trans h2A
      _ ≤ A' * (CN * massRadiusDisc ν z) := by gcongr
      _ = A' * CN * massRadiusDisc ν z := by ring
  · -- fatness
    obtain ⟨hμ1, hLe, -⟩ := hqprops (e i).1 (e i).2
    obtain ⟨hy0, hl, -⟩ := hP_piece i
    obtain ⟨p, hp, β, hβ, -, hin, hout⟩ := hioL _ _ _ _ hLe hy0 hl
    have hmid := l4_cayleyPre_mono (l4_midThird_subset hLe.1.le hLe.2.1.le) (S :=
      midThird (q (e i).1 (e i).2).1 (q (e i).1 (e i).2).2.1 (q (e i).1 (e i).2).2.2.1
        (q (e i).1 (e i).2).2.2.2)
    have hpP : p ∈ cayleyPre (f (e i)) :=
      hmid (hin ⟨hp, by rw [hypDist_self]; exact hβ⟩)
    have hρ : massRadiusDisc ν p ≤ A_L * β := by
      refine l4_massRadiusDisc_le (by positivity) ?_
      calc (1 : ℝ≥0∞) ≤ N := by exact_mod_cast hN
        _ = ν (cayleyPre (f (e i))) := by
            rw [l4_smul_apply hN, ← hμ', ← hν'apply _ (measurableSet_rect _ _ _ _), hμ1, mul_one]
        _ ≤ ν (hypBall p (A_L * β)) := measure_mono hout
    refine ⟨p, hpP, fun w ⟨hw𝔻, hw⟩ ↦ hmid (hin ⟨hw𝔻, ?_⟩)⟩
    calc hypDist p w < 1 / A_L * massRadiusDisc ν p := hw
      _ ≤ 1 / A_L * (A_L * β) := by gcongr
      _ = β := by field_simp
  · obtain ⟨-, hLe, -⟩ := hqprops (e i).1 (e i).2
    obtain ⟨hy0, hl, -⟩ := hP_piece i
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
