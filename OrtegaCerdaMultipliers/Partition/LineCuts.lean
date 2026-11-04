import OrtegaCerdaMultipliers.Doubling.Quant
import OrtegaCerdaMultipliers.Partition.Rectangles

/-!
# M05 (Partition) — Lemma 4 on the line: cutting `ℝ` into intervals of mass `N`

See `blueprint/M05_Partition.md` §3.9.  This file is imported by `Partition/Lemma4.lean`, where
`IsMassPartition` is defined, so the fields of `IsMassPartition` are spelled out here; the glue
`lemma4_line`, `lemma4_line_quant` is in `Lemma4.lean`.
-/

open MeasureTheory Metric Set Complex
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace OC

/-- The per-measure hypotheses of `lemma4_line` place `μ` in some class `MeasClassLine μ Cd R₀`. -/
theorem lineCut_measClassLine_of {μ : Measure ℂ} (hd : IsLocallyDoublingLine μ)
    (hfin : ∀ x r : ℝ, μ (lineInterval x r) < ∞)
    (hm : ∃ R : ℝ, 0 < R ∧ ∀ x : ℝ, 1 ≤ μ (lineInterval x R)) :
    ∃ (Cd : ℝ≥0) (R₀ : ℝ), MeasClassLine μ Cd R₀ := by
  obtain ⟨C, hC⟩ := hd.2
  obtain ⟨r, -, hr⟩ := exists_radius_lt_measure_lineInterval hm 1
  refine ⟨C, r, ⟨hd.1, hC⟩, fun x ↦ by simpa using hr x, fun K hK ↦ ?_⟩
  obtain ⟨ρ, hρ⟩ := hK.isBounded.subset_closedBall 0
  calc μ K ≤ μ (K ∩ {z | z.im = 0}) + μ (K \ {z | z.im = 0}) := measure_le_inter_add_sdiff _ _ _
    _ ≤ μ (lineInterval 0 (ρ + 1)) + μ {z : ℂ | z.im ≠ 0} := by
        gcongr
        · rintro z ⟨hzK, hz⟩
          have h1 := mem_closedBall_zero_iff.1 (hρ hzK)
          refine ⟨z.re, ⟨?_, ?_⟩, Complex.ext (by simp) (by simp [hz.symm])⟩ <;>
          · have := Complex.abs_re_le_norm z
            have := abs_le.1 (this.trans h1)
            linarith
        · intro z hz; exact hz.2
    _ < ∞ := by rw [hd.1, add_zero]; exact hfin 0 (ρ + 1)

/-! ### Helpers -/

theorem prop_dist_ofReal_line (x t : ℝ) : dist (x : ℂ) (t : ℂ) = |x - t| := by
  rw [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

theorem prop_massRadiusLine_le_line {ν : Measure ℂ} {x r : ℝ} (hr : 0 < r)
    (h : 1 ≤ ν (lineInterval x r)) : massRadiusLine ν x ≤ r :=
  csInf_le ⟨0, fun _ hx ↦ hx.1.le⟩ ⟨hr, h⟩

theorem lineCut_image_Ico (s t : ℝ) :
    (fun u : ℝ ↦ (u : ℂ)) '' Ico s t = {z : ℂ | z.im = 0 ∧ z.re ∈ Ico s t} := by
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩; exact ⟨by simp, by simpa using hu⟩
  · rintro ⟨h1, h2⟩; exact ⟨z.re, h2, Complex.ext (by simp) (by simp [h1])⟩

theorem lineCut_lineInterval_eq (x r : ℝ) :
    lineInterval x r = {z : ℂ | z.im = 0 ∧ z.re ∈ Ioo (x - r) (x + r)} := by
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩; exact ⟨by simp, by simpa using hu⟩
  · rintro ⟨h1, h2⟩; exact ⟨z.re, h2, Complex.ext (by simp) (by simp [h1])⟩

theorem lineCut_measurableSet_im_eq : MeasurableSet {z : ℂ | z.im = 0} :=
  (isClosed_eq Complex.continuous_im continuous_const).measurableSet

theorem lineCut_measurableSet_lineInterval (x r : ℝ) : MeasurableSet (lineInterval x r) := by
  rw [lineCut_lineInterval_eq]
  exact lineCut_measurableSet_im_eq.inter (measurableSet_Ioo.preimage Complex.measurable_re)

theorem lineCut_measurableSet_image_Ico (s t : ℝ) :
    MeasurableSet ((fun u : ℝ ↦ (u : ℂ)) '' Ico s t) := by
  rw [lineCut_image_Ico]
  exact lineCut_measurableSet_im_eq.inter (measurableSet_Ico.preimage Complex.measurable_re)

/-- For a measure carried by `ℝ`, a rectangle across the axis has the mass of its trace. -/
theorem lineCut_measure_rect {μ : Measure ℂ} (hμ : μ {z | z.im ≠ 0} = 0) (s t : ℝ) :
    μ (rect s t (-1) 1) = μ ((fun u : ℝ ↦ (u : ℂ)) '' Ico s t) := by
  have he : (fun u : ℝ ↦ (u : ℂ)) '' Ico s t = rect s t (-1) 1 ∩ {z | z.im = 0} := by
    rw [lineCut_image_Ico]
    ext z
    simp only [mem_ofPred_eq, mem_inter_iff, rect_mem_iff, mem_Ico]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨⟨h2, by rw [h1]; norm_num, by rw [h1]; norm_num⟩, h1⟩
    · rintro ⟨⟨h2, _⟩, h1⟩; exact ⟨h1, h2⟩
  rw [he, ← measure_inter_add_sdiff (rect s t (-1) 1) lineCut_measurableSet_im_eq]
  have : μ (rect s t (-1) 1 \ {z | z.im = 0}) = 0 :=
    measure_mono_null (fun z hz ↦ hz.2) hμ
  rw [this, add_zero]

/-- Growth with an explicit radius: `N + 1` disjoint intervals of radius `R₀`. -/
theorem lineCut_growth {μ : Measure ℂ} {R₀ : ℝ} (hR₀ : 0 < R₀)
    (hmass : ∀ x : ℝ, 1 < μ (lineInterval x R₀)) (N : ℕ) (x : ℝ) :
    (N : ℝ≥0∞) < μ (lineInterval x (((N : ℝ) + 1) * R₀)) := by
  set I : ℕ → Set ℂ := fun k ↦ lineInterval (x + (2 * k - N) * R₀) R₀ with hI
  have hdisj : (↑(Finset.range (N + 1)) : Set ℕ).PairwiseDisjoint I := by
    intro k _ k' _ hkk'
    simp only [Function.onFun, hI, lineCut_lineInterval_eq]
    rw [Set.disjoint_left]
    rintro z ⟨_, h1, h2⟩ ⟨_, h3, h4⟩
    rcases lt_or_gt_of_ne hkk' with h | h
    · have : (k : ℝ) + 1 ≤ k' := by exact_mod_cast h
      nlinarith
    · have : (k' : ℝ) + 1 ≤ k := by exact_mod_cast h
      nlinarith
  have hsub : (⋃ k ∈ Finset.range (N + 1), I k) ⊆ lineInterval x (((N : ℝ) + 1) * R₀) := by
    refine iUnion₂_subset fun k hk ↦ ?_
    have hk' : (k : ℝ) ≤ N := by
      have := Finset.mem_range.1 hk; exact_mod_cast Nat.lt_succ_iff.1 this
    simp only [hI, lineCut_lineInterval_eq]
    rintro z ⟨h0, h1, h2⟩
    have : (0 : ℝ) ≤ k := k.cast_nonneg
    exact ⟨h0, by nlinarith, by nlinarith⟩
  calc (N : ℝ≥0∞) < ((N + 1 : ℕ) : ℝ≥0∞) := by exact_mod_cast Nat.lt_succ_self N
    _ = ∑ _k ∈ Finset.range (N + 1), (1 : ℝ≥0∞) := by simp
    _ ≤ ∑ k ∈ Finset.range (N + 1), μ (I k) := Finset.sum_le_sum fun k _ ↦ (hmass _).le
    _ = μ (⋃ k ∈ Finset.range (N + 1), I k) :=
        (measure_biUnion_finset hdisj fun k _ ↦ lineCut_measurableSet_lineInterval _ _).symm
    _ ≤ _ := measure_mono hsub

/-- A strictly monotone sequence on `ℤ`, unbounded in both directions, covers `ℝ`. -/
theorem lineCut_exists_Ico {x : ℤ → ℝ} (hmono : StrictMono x) (hup : ∀ T, ∃ k, T < x k)
    (hdown : ∀ T, ∃ k, x k ≤ T) (t : ℝ) : ∃ k, t ∈ Ico (x k) (x (k + 1)) := by
  obtain ⟨K, hK⟩ := hup t
  obtain ⟨k₀, hk₀⟩ := hdown t
  obtain ⟨k, hk, hmax⟩ := Int.exists_greatest_of_bdd (P := fun k ↦ x k ≤ t)
    ⟨K, fun k hk ↦ by
      by_contra hlt
      push Not at hlt
      have := hmono.monotone hlt.le
      linarith⟩ ⟨k₀, hk₀⟩
  refine ⟨k, hk, ?_⟩
  by_contra hle
  push Not at hle
  have := hmax (k + 1) hle
  omega

/-- **Lemma 4 (line)**, uniform form with the fields of `IsMassPartition` spelled out: intervals
`[s, t)` of mass `N`, with constants depending only on `(Cd, R₀, N)`. -/
theorem lineCut_partition_quant (Cd : ℝ≥0) (R₀ : ℝ) (N : ℕ) (hN : 1 ≤ N) :
    ∃ a A : ℝ, 0 < a ∧ 0 < A ∧ ∀ μ : Measure ℂ, MeasClassLine μ Cd R₀ →
      ∃ R : ℕ → Set ℂ, (∀ i, MeasurableSet (R i)) ∧ Pairwise (Function.onFun Disjoint R) ∧
        ⋃ i, R i = range (fun t : ℝ ↦ (t : ℂ)) ∧ (∀ i, μ (R i) = N) ∧
        (∀ i, ∀ z ∈ R i, ∀ w ∈ R i, dist z w ≤ A * massRadiusLine μ z.re) ∧
        (∀ i, ∃ c ∈ R i, {w | w ∈ range (fun t : ℝ ↦ (t : ℂ)) ∧
          dist c w < a * massRadiusLine μ c.re} ⊆ R i) ∧
        ∀ i, ∃ s t : ℝ, s < t ∧ R i = (fun u : ℝ ↦ (u : ℂ)) '' Ico s t := by
  by_cases hR₀ : 0 < R₀
  swap
  · refine ⟨1, 1, one_pos, one_pos, fun μ hμ ↦ ?_⟩
    exfalso
    have h := hμ.mass 0
    have he : lineInterval 0 R₀ = ∅ := by
      rw [lineCut_lineInterval_eq]
      ext z
      simp only [mem_ofPred_eq, mem_Ioo, mem_empty_iff_false, iff_false, not_and]
      intro _ h1
      linarith
    rw [he, measure_empty] at h
    exact absurd h (not_lt.2 (zero_le))
  set rN : ℝ := ((N : ℝ) + 1) * R₀ with hrN
  have hrN0 : 0 < rN := by positivity
  set R₁ : ℝ := 2 * rN with hR₁
  obtain ⟨C₁, hC₁1, hC₁⟩ := doubling_upTo_quant (X := ℝ) Cd R₁
  obtain ⟨c, Cb, δ, sb, hc, -, hδ, -, hb⟩ :=
    measure_ball_massRadiusM_bounds_quant (X := ℝ) Cd R₀ R₁
  set M : ℝ := (C₁ : ℝ) ^ 2 * N with hM
  have hM0 : 0 ≤ M := by positivity
  set A : ℝ := max 1 ((M / c) ^ (1 / δ)) with hA
  refine ⟨1 / 2, A, by norm_num, lt_of_lt_of_le one_pos (le_max_left _ _), fun μ hμ ↦ ?_⟩
  -- per-measure facts
  have hcar : μ {z | z.im ≠ 0} = 0 := hμ.doubling.1
  have hM' := hμ.measClassM_linePull
  have hdbl : ∀ x r : ℝ, 0 < r → r ≤ R₁ →
      μ (lineInterval x (2 * r)) ≤ C₁ * μ (lineInterval x r) := by
    intro x r hr hrR
    have := hC₁ (linePull μ) hM'.doubling x r hr hrR
    rwa [linePull_ball, linePull_ball] at this
  have hlow : ∀ x r : ℝ, massRadiusLine μ x ≤ r → r ≤ R₁ →
      ENNReal.ofReal (c * (r / massRadiusLine μ x) ^ δ) ≤ μ (lineInterval x r) := by
    intro x r h1 h2
    rw [massRadiusLine_eq] at h1 ⊢
    have := (hb (linePull μ) hM' x r h1 h2).1
    rwa [linePull_ball] at this
  have hd : IsLocallyDoublingLine μ := ⟨hcar, Cd, hμ.doubling.2⟩
  have hfinI : ∀ x r : ℝ, μ (lineInterval x r) < ∞ := fun x r ↦ by
    refine (measure_mono ?_).trans_lt (hμ.finite _ (isCompact_closedBall (x : ℂ) r))
    rintro z ⟨u, hu, rfl⟩
    rw [mem_closedBall, prop_dist_ofReal_line, abs_le]
    constructor <;> linarith [hu.1, hu.2]
  have hpos : ∀ x, 0 < massRadiusLine μ x :=
    massRadiusLine_pos hd hfinI ⟨R₀, hR₀, fun x ↦ (hμ.mass x).le⟩
  have hre : ∀ x : ℝ, μ {w : ℂ | w.re = x} = 0 := by
    intro x
    refine measure_mono_null (t := {(x : ℂ)} ∪ {z | z.im ≠ 0}) ?_
      (measure_union_null (measure_singleton_line hd hfinI _) hcar)
    intro w hw
    by_cases him : w.im = 0
    · left; exact Complex.ext (by simpa using hw) (by simpa using him)
    · right; exact him
  have hfinR : ∀ a b : ℝ, μ (rect a b (-1) 1) < ∞ := by
    intro a b
    refine (measure_mono ?_).trans_lt (hμ.finite _ (isCompact_closedBall (0 : ℂ) (|a| + |b| + 1)))
    rintro z ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
    rw [mem_closedBall_zero_iff]
    refine (Complex.norm_le_abs_re_add_abs_im z).trans ?_
    have : |z.re| ≤ |a| + |b| := by
      rw [abs_le]; constructor <;> linarith [neg_abs_le a, le_abs_self b, abs_nonneg a, abs_nonneg b]
    have : |z.im| ≤ 1 := by rw [abs_le]; constructor <;> linarith
    linarith
  have hgrow : ∀ x : ℝ, (N : ℝ≥0∞) < μ (lineInterval x rN) := lineCut_growth hR₀ hμ.mass N
  have hbig : ∀ s : ℝ, (N : ℝ≥0∞) < μ (rect s (s + R₁) (-1) 1) := by
    intro s
    refine (hgrow (s + rN)).trans_le (measure_mono ?_)
    rintro z ⟨u, hu, rfl⟩
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> simp <;> linarith [hu.1, hu.2]
  -- one step to the right / to the left
  have hstepR : ∀ s : ℝ, ∃ t, s < t ∧ t ≤ s + R₁ ∧ μ (rect s t (-1) 1) = N := by
    intro s
    have hc' := rect_continuous_toReal hre (hfinR s)
    have h0 : (μ (rect s s (-1) 1)).toReal = 0 := by simp [rect_eq_empty_of_le le_rfl]
    have h1 : (N : ℝ) < (μ (rect s (s + R₁) (-1) 1)).toReal := by
      have := (ENNReal.toReal_lt_toReal (ENNReal.natCast_ne_top N) (hfinR _ _).ne).2 (hbig s)
      simpa using this
    obtain ⟨t, ⟨ht1, ht2⟩, hFt⟩ := intermediate_value_Icc (show s ≤ s + R₁ by linarith)
      hc'.continuousOn (show (N : ℝ) ∈ Icc _ _ from ⟨by rw [h0]; positivity, h1.le⟩)
    refine ⟨t, ?_, ht2, rect_eq_natCast_of_toReal (hfinR _ _) hFt⟩
    rcases eq_or_lt_of_le ht1 with rfl | h
    · change (μ (rect s s (-1) 1)).toReal = N at hFt
      rw [h0] at hFt
      have : (1 : ℝ) ≤ N := by exact_mod_cast hN
      linarith
    · exact h
  have hstepL : ∀ b : ℝ, ∃ t, b - R₁ ≤ t ∧ t < b ∧ μ (rect t b (-1) 1) = N := by
    intro b
    set a := b - R₁
    set G : ℝ → ℝ := fun t ↦ (μ (rect a b (-1) 1)).toReal - (μ (rect a t (-1) 1)).toReal
      with hG
    have hcG : Continuous G := continuous_const.sub (rect_continuous_toReal hre (hfinR a))
    have hGt : ∀ t, a ≤ t → t ≤ b → G t = (μ (rect t b (-1) 1)).toReal := by
      intro t h1 h2
      simp only [hG]
      rw [rect_toReal_add_x μ h1 h2 (hfinR _ _)]
      ring
    have hab : a ≤ b := by simp only [a]; linarith
    have hGb : G b = 0 := by rw [hGt b hab le_rfl]; simp [rect_eq_empty_of_le le_rfl]
    have hGa : (N : ℝ) < G a := by
      rw [hGt a le_rfl hab]
      have := (ENNReal.toReal_lt_toReal (ENNReal.natCast_ne_top N) (hfinR _ _).ne).2 (hbig a)
      simpa [a] using this
    obtain ⟨t, ⟨ht1, ht2⟩, hGt'⟩ := intermediate_value_Icc' hab hcG.continuousOn
      (show (N : ℝ) ∈ Icc (G b) (G a) from ⟨by rw [hGb]; positivity, hGa.le⟩)
    rw [hGt t ht1 ht2] at hGt'
    refine ⟨t, ht1, ?_, rect_eq_natCast_of_toReal (hfinR _ _) hGt'⟩
    rcases eq_or_lt_of_le ht2 with rfl | h
    · rw [rect_eq_empty_of_le le_rfl] at hGt'
      simp at hGt'
      have : (1 : ℝ) ≤ N := by exact_mod_cast hN
      linarith
    · exact h
  choose fR hfR using hstepR
  choose fL hfL using hstepL
  set x : ℤ → ℝ := fun k ↦ if 0 ≤ k then fR^[k.toNat] 0 else fL^[(-k).toNat] 0 with hx
  have hxpos : ∀ n : ℕ, x n = fR^[n] 0 := by
    intro n; simp [hx]
  have hxneg : ∀ n : ℕ, x (-(n : ℤ)) = fL^[n] 0 := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hx]
    · have : ¬ (0 ≤ -(n : ℤ)) := by omega
      simp only [hx, this, ite_false, neg_neg, Int.toNat_natCast]
  have hblock : ∀ k : ℤ, x k < x (k + 1) ∧ x (k + 1) - x k ≤ R₁ ∧
      μ (rect (x k) (x (k + 1)) (-1) 1) = N := by
    intro k
    rcases Int.eq_nat_or_neg k with ⟨n, rfl | rfl⟩
    · have e : x ((n : ℤ) + 1) = fR (x n) := by
        rw [show ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) by push_cast; ring, hxpos, hxpos,
          Function.iterate_succ_apply']
      obtain ⟨h1, h2, hn⟩ := hfR (x n)
      rw [e]
      exact ⟨h1, by linarith, hn⟩
    · rcases Nat.eq_zero_or_pos n with rfl | hn
      · have e : x ((0 : ℤ) + 1) = fR (x 0) := by
          have := hxpos 1
          simp only [Nat.cast_one, Function.iterate_one] at this
          rw [zero_add, this]
          congr 1
        simp only [Nat.cast_zero, neg_zero]
        obtain ⟨h1, h2, hn⟩ := hfR (x 0)
        rw [e]
        exact ⟨h1, by linarith, hn⟩
      · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hn
        have e1 : -((0 + m + 1 : ℕ) : ℤ) + 1 = -(m : ℤ) := by push_cast; ring
        have e2 : x (-((0 + m + 1 : ℕ) : ℤ)) = fL (x (-(m : ℤ))) := by
          rw [hxneg, hxneg, show 0 + m + 1 = m + 1 by ring, Function.iterate_succ_apply']
        rw [e1, e2]
        obtain ⟨h1, h2, hn⟩ := hfL (x (-(m : ℤ)))
        exact ⟨h2, by linarith, hn⟩
  have hmono : StrictMono x := strictMono_int_of_lt_succ fun k ↦ (hblock k).1
  -- masses of consecutive blocks add up, so the cut points escape to `±∞`
  have hmassR : ∀ n : ℕ, μ (rect (x 0) (x n) (-1) 1) = n * N := by
    intro n
    induction n with
    | zero => simp [rect_eq_empty_of_le le_rfl]
    | succ n ih =>
      have := measure_rect_add_x μ (y₁ := -1) (y₂ := 1)
        (hmono.monotone (show (0 : ℤ) ≤ n by omega)) (hmono.monotone (show (n : ℤ) ≤ n + 1 by omega))
      rw [show ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 by push_cast; ring, this, ih, (hblock n).2.2]
      push_cast; ring
  have hmassL : ∀ n : ℕ, μ (rect (x (-(n : ℤ))) (x 0) (-1) 1) = n * N := by
    intro n
    induction n with
    | zero => simp [rect_eq_empty_of_le le_rfl]
    | succ n ih =>
      have := measure_rect_add_x μ (y₁ := -1) (y₂ := 1)
        (hmono.monotone (show -((n + 1 : ℕ) : ℤ) ≤ -(n : ℤ) by omega))
        (hmono.monotone (show -(n : ℤ) ≤ 0 by omega))
      rw [this, ih]
      have hb := (hblock (-((n + 1 : ℕ) : ℤ))).2.2
      rw [show -((n + 1 : ℕ) : ℤ) + 1 = -(n : ℤ) by push_cast; ring] at hb
      rw [hb]
      push_cast; ring
  have hN1 : (1 : ℝ≥0∞) ≤ N := by exact_mod_cast hN
  have hup : ∀ T, ∃ k, T < x k := by
    intro T
    by_contra hcon
    push Not at hcon
    obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt (hfinR (x 0) T).ne
    have h1 : μ (rect (x 0) (x n) (-1) 1) ≤ μ (rect (x 0) T (-1) 1) :=
      measure_mono (rect_subset_rect le_rfl (hcon n) le_rfl le_rfl)
    rw [hmassR] at h1
    have : (n : ℝ≥0∞) ≤ n * N := by
      calc (n : ℝ≥0∞) = n * 1 := (mul_one _).symm
        _ ≤ n * N := by gcongr
    exact absurd (hn.trans_le (this.trans h1)) (lt_irrefl _)
  have hdown : ∀ T, ∃ k, x k ≤ T := by
    intro T
    by_contra hcon
    push Not at hcon
    obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt (hfinR T (x 0)).ne
    have h1 : μ (rect (x (-(n : ℤ))) (x 0) (-1) 1) ≤ μ (rect T (x 0) (-1) 1) :=
      measure_mono (rect_subset_rect (hcon _).le le_rfl le_rfl le_rfl)
    rw [hmassL] at h1
    have : (n : ℝ≥0∞) ≤ n * N := by
      calc (n : ℝ≥0∞) = n * 1 := (mul_one _).symm
        _ ≤ n * N := by gcongr
    exact absurd (hn.trans_le (this.trans h1)) (lt_irrefl _)
  -- the pieces
  set P : ℤ → Set ℂ := fun k ↦ (fun u : ℝ ↦ (u : ℂ)) '' Ico (x k) (x (k + 1)) with hP
  have hPmass : ∀ k, μ (P k) = N := fun k ↦ by
    simp only [hP]; rw [← lineCut_measure_rect hcar]; exact (hblock k).2.2
  have hPdisj : Pairwise (Function.onFun Disjoint P) := by
    intro k k' hkk'
    simp only [Function.onFun, hP, lineCut_image_Ico]
    rw [Set.disjoint_left]
    rintro z ⟨_, h1, h2⟩ ⟨_, h3, h4⟩
    rcases lt_or_gt_of_ne hkk' with h | h
    · have := hmono.monotone (show k + 1 ≤ k' by omega); linarith
    · have := hmono.monotone (show k' + 1 ≤ k by omega); linarith
  have hPcover : ⋃ k, P k = range (fun t : ℝ ↦ (t : ℂ)) := by
    apply Subset.antisymm
    · exact iUnion_subset fun k ↦ image_subset_range _ _
    · rintro z ⟨t, rfl⟩
      obtain ⟨k, hk⟩ := lineCut_exists_Ico hmono hup hdown t
      exact mem_iUnion.2 ⟨k, t, hk, rfl⟩
  have hPdist : ∀ k, ∀ z ∈ P k, ∀ w ∈ P k, dist z w ≤ A * massRadiusLine μ z.re := by
    rintro k z ⟨u, hu, rfl⟩ w ⟨v, hv, rfl⟩
    obtain ⟨hk1, hk2, -⟩ := hblock k
    set L := x (k + 1) - x k with hL
    have hL0 : 0 < L := by linarith
    simp only [Complex.ofReal_re]
    rw [prop_dist_ofReal_line]
    have hdist : |u - v| ≤ L := by
      rw [abs_le]; constructor <;> linarith [hu.1, hu.2, hv.1, hv.2]
    set m := (x k + x (k + 1)) / 2 with hm
    have hsub1 : lineInterval u L ⊆ lineInterval m (2 * L) := by
      simp only [lineCut_lineInterval_eq]
      rintro z ⟨h0, h1, h2⟩
      exact ⟨h0, by linarith [hu.1, hu.2], by linarith [hu.1, hu.2]⟩
    have hsub2 : lineInterval m (L / 2) ⊆ P k := by
      simp only [lineCut_lineInterval_eq, hP, lineCut_image_Ico]
      rintro z ⟨h0, h1, h2⟩
      exact ⟨h0, by linarith, by linarith⟩
    have hmassL : μ (lineInterval u L) ≤ ENNReal.ofReal M := by
      calc μ (lineInterval u L) ≤ μ (lineInterval m (2 * L)) := measure_mono hsub1
        _ ≤ C₁ * μ (lineInterval m L) := hdbl m L hL0 (by linarith)
        _ ≤ C₁ * (C₁ * μ (lineInterval m (L / 2))) := by
            gcongr
            have := hdbl m (L / 2) (by positivity) (by linarith)
            rwa [show 2 * (L / 2) = L by ring] at this
        _ ≤ C₁ * (C₁ * N) := by gcongr; exact (measure_mono hsub2).trans (hPmass k).le
        _ = ENNReal.ofReal M := by
            rw [hM, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity),
              ENNReal.ofReal_natCast, ENNReal.ofReal_coe_nnreal]
            ring
    have hρ := hpos u
    have hLA : L ≤ A * massRadiusLine μ u := by
      rcases le_or_gt (massRadiusLine μ u) L with hle | hlt
      · have h1 := (hlow u L hle (by linarith)).trans hmassL
        rw [ENNReal.ofReal_le_ofReal_iff hM0] at h1
        have h2 : (L / massRadiusLine μ u) ^ δ ≤ M / c := by
          rw [le_div_iff₀ hc]; linarith
        have h3 : L / massRadiusLine μ u ≤ (M / c) ^ (1 / δ) := by
          have h4 := Real.rpow_le_rpow (by positivity) h2 (show (0 : ℝ) ≤ 1 / δ by positivity)
          rwa [← Real.rpow_mul (by positivity), mul_one_div_cancel hδ.ne', Real.rpow_one] at h4
        rw [div_le_iff₀ hρ] at h3
        exact h3.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hρ.le)
      · exact hlt.le.trans (le_mul_of_one_le_left hρ.le (le_max_left _ _))
    exact hdist.trans hLA
  have hPinner : ∀ k, ∃ c ∈ P k, {w | w ∈ range (fun t : ℝ ↦ (t : ℂ)) ∧
      dist c w < 1 / 2 * massRadiusLine μ c.re} ⊆ P k := by
    intro k
    obtain ⟨hk1, -, -⟩ := hblock k
    set m := (x k + x (k + 1)) / 2 with hm
    have hmP : (m : ℂ) ∈ P k := ⟨m, ⟨by linarith, by linarith⟩, rfl⟩
    have hρm : massRadiusLine μ m ≤ x (k + 1) - x k := by
      refine prop_massRadiusLine_le_line (by linarith) ?_
      refine le_trans ?_ (measure_mono (show P k ⊆ lineInterval m (x (k + 1) - x k) from ?_))
      · rw [hPmass]; exact_mod_cast hN
      · simp only [hP, lineCut_image_Ico, lineCut_lineInterval_eq]
        rintro z ⟨h0, h1, h2⟩
        exact ⟨h0, by linarith, by linarith⟩
    refine ⟨m, hmP, ?_⟩
    rintro w ⟨⟨v, rfl⟩, hw⟩
    simp only [Complex.ofReal_re] at hw
    rw [prop_dist_ofReal_line] at hw
    have := abs_lt.1 hw
    exact ⟨v, ⟨by linarith, by linarith⟩, rfl⟩
  -- reindex `ℤ ≃ ℕ`
  set e := Equiv.intEquivNat
  refine ⟨fun i ↦ P (e.symm i), fun i ↦ lineCut_measurableSet_image_Ico _ _, ?_, ?_,
    fun i ↦ hPmass _, fun i ↦ hPdist _, fun i ↦ hPinner _, fun i ↦ ⟨_, _, (hblock _).1, rfl⟩⟩
  · intro i j hij
    exact hPdisj (fun h ↦ hij (e.symm.injective h))
  · rw [← hPcover]
    exact e.symm.surjective.iUnion_comp P

end OC
