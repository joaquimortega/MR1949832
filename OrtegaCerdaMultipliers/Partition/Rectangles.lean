import OrtegaCerdaMultipliers.Doubling.Export

/-!
# M05 (Partition) — Rectangle combinatorics for a measure on `ℂ`

See `blueprint/M05_Partition.md` §2.1.  Scaffold: statements, proofs `sorry`; definitions are real.

Coordinate rectangles, the middle third, strip cuts, slab reverse doubling (the gap behind
"we use Lemma 1", p. 365), and the bisection-and-slicing core `exists_rect_partition`.
-/

open MeasureTheory Metric Set Complex
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace OC

/-- The half-open coordinate rectangle `[x₁, x₂) × [y₁, y₂)`. -/
def rect (x₁ x₂ y₁ y₂ : ℝ) : Set ℂ := {w : ℂ | w.re ∈ Ico x₁ x₂ ∧ w.im ∈ Ico y₁ y₂}

/-- Non-degenerate rectangle with side ratio at most `L`. -/
def IsRectLE (L x₁ x₂ y₁ y₂ : ℝ) : Prop :=
  x₁ < x₂ ∧ y₁ < y₂ ∧ x₂ - x₁ ≤ L * (y₂ - y₁) ∧ y₂ - y₁ ≤ L * (x₂ - x₁)

/-- The middle third of a rectangle along its longer side. -/
def midThird (x₁ x₂ y₁ y₂ : ℝ) : Set ℂ :=
  if y₂ - y₁ ≤ x₂ - x₁ then rect (x₁ + (x₂ - x₁) / 3) (x₂ - (x₂ - x₁) / 3) y₁ y₂
  else rect x₁ x₂ (y₁ + (y₂ - y₁) / 3) (y₂ - (y₂ - y₁) / 3)

theorem measurableSet_rect (x₁ x₂ y₁ y₂ : ℝ) : MeasurableSet (rect x₁ x₂ y₁ y₂) :=
  (measurableSet_Ico.preimage measurable_re).inter (measurableSet_Ico.preimage measurable_im)

theorem rect_mem_iff {x₁ x₂ y₁ y₂ : ℝ} {w : ℂ} :
    w ∈ rect x₁ x₂ y₁ y₂ ↔ (x₁ ≤ w.re ∧ w.re < x₂) ∧ (y₁ ≤ w.im ∧ w.im < y₂) := Iff.rfl

/-- Splitting a rectangle by a vertical line. -/
theorem rect_union_x {a b c y₁ y₂ : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    rect a b y₁ y₂ ∪ rect b c y₁ y₂ = rect a c y₁ y₂ := by
  ext w
  simp only [mem_union, rect_mem_iff]
  constructor
  · rintro (⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩)
    · exact ⟨⟨h1, h2.trans_le hbc⟩, h3⟩
    · exact ⟨⟨hab.trans h1, h2⟩, h3⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    rcases lt_or_ge w.re b with h | h
    · exact Or.inl ⟨⟨h1, h⟩, h3⟩
    · exact Or.inr ⟨⟨h, h2⟩, h3⟩

theorem rect_disjoint_x {a b c d y₁ y₂ y₃ y₄ : ℝ} (hbc : b ≤ c) :
    Disjoint (rect a b y₁ y₂) (rect c d y₃ y₄) := by
  rw [Set.disjoint_left]
  rintro w ⟨⟨_, h2⟩, _⟩ ⟨⟨h3, _⟩, _⟩
  exact absurd (h2.trans_le hbc) (not_lt.2 h3)

theorem rect_disjoint_y {a b c d y₁ y₂ y₃ y₄ : ℝ} (h : y₂ ≤ y₃) :
    Disjoint (rect a b y₁ y₂) (rect c d y₃ y₄) := by
  rw [Set.disjoint_left]
  rintro w ⟨_, ⟨_, h2⟩⟩ ⟨_, ⟨h3, _⟩⟩
  exact absurd (h2.trans_le h) (not_lt.2 h3)

theorem rect_union_y {x₁ x₂ a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    rect x₁ x₂ a b ∪ rect x₁ x₂ b c = rect x₁ x₂ a c := by
  ext w
  simp only [mem_union, rect_mem_iff]
  constructor
  · rintro (⟨h3, ⟨h1, h2⟩⟩ | ⟨h3, ⟨h1, h2⟩⟩)
    · exact ⟨h3, ⟨h1, h2.trans_le hbc⟩⟩
    · exact ⟨h3, ⟨hab.trans h1, h2⟩⟩
  · rintro ⟨h3, ⟨h1, h2⟩⟩
    rcases lt_or_ge w.im b with h | h
    · exact Or.inl ⟨h3, ⟨h1, h⟩⟩
    · exact Or.inr ⟨h3, ⟨h, h2⟩⟩

theorem rect_subset_rect {x₁ x₂ y₁ y₂ x₁' x₂' y₁' y₂' : ℝ} (h1 : x₁' ≤ x₁) (h2 : x₂ ≤ x₂')
    (h3 : y₁' ≤ y₁) (h4 : y₂ ≤ y₂') : rect x₁ x₂ y₁ y₂ ⊆ rect x₁' x₂' y₁' y₂' := by
  rintro w ⟨⟨a, b⟩, ⟨c, d⟩⟩
  exact ⟨⟨h1.trans a, b.trans_le h2⟩, ⟨h3.trans c, d.trans_le h4⟩⟩

/-- Additivity of the mass in the `x`-direction. -/
theorem measure_rect_add_x (ν : Measure ℂ) {a b c y₁ y₂ : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    ν (rect a c y₁ y₂) = ν (rect a b y₁ y₂) + ν (rect b c y₁ y₂) := by
  rw [← rect_union_x hab hbc, measure_union (rect_disjoint_x le_rfl) (measurableSet_rect _ _ _ _)]

theorem measure_rect_add_y (ν : Measure ℂ) {x₁ x₂ a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    ν (rect x₁ x₂ a c) = ν (rect x₁ x₂ a b) + ν (rect x₁ x₂ b c) := by
  rw [← rect_union_y hab hbc, measure_union (rect_disjoint_y le_rfl) (measurableSet_rect _ _ _ _)]

theorem rect_eq_empty_of_le {x₁ x₂ y₁ y₂ : ℝ} (h : x₂ ≤ x₁) : rect x₁ x₂ y₁ y₂ = ∅ := by
  ext w
  simp only [rect_mem_iff, mem_empty_iff_false, iff_false, not_and]
  intro h1 h2
  linarith

/-- Continuity of the mass of a rectangle in its right edge. -/
theorem continuous_measure_rect_right {ν : Measure ℂ} (hre : ∀ x : ℝ, ν {w | w.re = x} = 0)
    {x₁ y₁ y₂ : ℝ} (hfin : ∀ x₂, ν (rect x₁ x₂ y₁ y₂) < ∞) :
    Continuous fun x₂ : ℝ ↦ ν (rect x₁ x₂ y₁ y₂) := by
  have hmono : Monotone fun x₂ : ℝ ↦ ν (rect x₁ x₂ y₁ y₂) := fun a b hab ↦
    measure_mono (rect_subset_rect le_rfl hab le_rfl le_rfl)
  refine continuous_iff_continuousAt.2 fun t ↦ ?_
  refine tendsto_order.2 ⟨fun a ha ↦ ?_, fun b hb ↦ ?_⟩
  · -- continuity from below
    have hU : (⋃ n : ℕ, rect x₁ (t - 1 / ((n : ℝ) + 1)) y₁ y₂) = rect x₁ t y₁ y₂ := by
      ext w
      simp only [mem_iUnion, rect_mem_iff]
      constructor
      · rintro ⟨n, ⟨h1, h2⟩, h3⟩
        refine ⟨⟨h1, h2.trans_le ?_⟩, h3⟩
        have : 0 < 1 / ((n : ℝ) + 1) := by positivity
        linarith
      · rintro ⟨⟨h1, h2⟩, h3⟩
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 h2)
        exact ⟨n, ⟨h1, by linarith⟩, h3⟩
    have hm : Monotone fun n : ℕ ↦ rect x₁ (t - 1 / ((n : ℝ) + 1)) y₁ y₂ := by
      intro m n hmn
      refine rect_subset_rect le_rfl ?_ le_rfl le_rfl
      have : 1 / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hmn 1)
      linarith
    have ht := tendsto_measure_iUnion_atTop (μ := ν) hm
    rw [hU] at ht
    obtain ⟨n, hn⟩ := (ht.eventually (lt_mem_nhds ha)).exists
    have hpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
    filter_upwards [Ioi_mem_nhds (show t - 1 / ((n : ℝ) + 1) < t by linarith)] with s hs
    exact hn.trans_le (hmono (le_of_lt hs))
  · -- continuity from above
    have hI : (⋂ n : ℕ, rect x₁ (t + 1 / ((n : ℝ) + 1)) y₁ y₂) ⊆
        rect x₁ t y₁ y₂ ∪ {w | w.re = t} := by
      intro w hw
      simp only [mem_iInter, rect_mem_iff] at hw
      rcases lt_trichotomy w.re t with h | h | h
      · exact Or.inl ⟨⟨(hw 0).1.1, h⟩, (hw 0).2⟩
      · exact Or.inr h
      · obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 h)
        have := (hw n).1.2
        linarith
    have hm : Antitone fun n : ℕ ↦ rect x₁ (t + 1 / ((n : ℝ) + 1)) y₁ y₂ := by
      intro m n hmn
      refine rect_subset_rect le_rfl ?_ le_rfl le_rfl
      have : 1 / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hmn 1)
      linarith
    have ht := tendsto_measure_iInter_atTop (μ := ν)
      (fun n ↦ (measurableSet_rect _ _ _ _).nullMeasurableSet) hm ⟨0, (hfin _).ne⟩
    have hle : ν (⋂ n : ℕ, rect x₁ (t + 1 / ((n : ℝ) + 1)) y₁ y₂) ≤ ν (rect x₁ t y₁ y₂) :=
      (measure_mono hI).trans ((measure_union_le _ _).trans (by rw [hre t, add_zero]))
    obtain ⟨n, hn⟩ := (ht.eventually (gt_mem_nhds (hle.trans_lt hb))).exists
    have hpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
    filter_upwards [Iio_mem_nhds (show t < t + 1 / ((n : ℝ) + 1) by linarith)] with s hs
    exact (hmono (le_of_lt hs)).trans_lt hn

/-- Coarse step: slicing a horizontal strip into blocks of integer mass and width in `[h, 2h]`. -/
theorem exists_strip_cuts {ν : Measure ℂ} (hre : ∀ x : ℝ, ν {w | w.re = x} = 0)
    {y₁ y₂ h : ℝ} (hh : 0 < h) (hfin : ∀ a b : ℝ, ν (rect a b y₁ y₂) < ∞)
    (hmass : ∀ a : ℝ, 1 ≤ ν (rect a (a + h) y₁ y₂)) :
    ∃ x : ℤ → ℝ, StrictMono x ∧ (∀ k, h ≤ x (k + 1) - x k ∧ x (k + 1) - x k ≤ 2 * h) ∧
      (∀ t : ℝ, ∃ k, t ∈ Ico (x k) (x (k + 1))) ∧
      ∀ k, ∃ n : ℕ, 1 ≤ n ∧ ν (rect (x k) (x (k + 1)) y₁ y₂) = n := sorry

/-- Slab reverse doubling (the missing argument behind "we use Lemma 1", p. 365): a vertical slab
of width `s` in a rectangle has a neighbouring slab of comparable mass, provided `s` is at most
the height and the scale `σ` at which `ν` is Euclidean doubling. -/
theorem slab_reverse_doubling_right {ν : Measure ℂ} {C_E u s y₁ y₂ : ℝ} (hs : 0 < s)
    (hsl : s ≤ y₂ - y₁)
    (hED : ∀ w ∈ rect (u + s) (u + 3 * s) y₁ y₂, ∀ r : ℝ, 0 < r → r ≤ s →
      ν (ball w (4 * r)) ≤ ENNReal.ofReal C_E * ν (ball w (r / 2))) :
    ν (rect u (u + s) y₁ y₂) ≤ ENNReal.ofReal (2 * C_E) * ν (rect (u + s) (u + 3 * s) y₁ y₂) :=
  sorry

theorem slab_reverse_doubling_left {ν : Measure ℂ} {C_E u s y₁ y₂ : ℝ} (hs : 0 < s)
    (hsl : s ≤ y₂ - y₁)
    (hED : ∀ w ∈ rect (u - 2 * s) u y₁ y₂, ∀ r : ℝ, 0 < r → r ≤ s →
      ν (ball w (4 * r)) ≤ ENNReal.ofReal C_E * ν (ball w (r / 2))) :
    ν (rect u (u + s) y₁ y₂) ≤ ENNReal.ofReal (2 * C_E) * ν (rect (u - 2 * s) u y₁ y₂) := sorry

/-- The coordinate swap `x + iy ↦ y + ix`, used to reduce vertical cuts to horizontal ones. -/
def swapReIm (z : ℂ) : ℂ := I * conj z

@[simp] theorem swapReIm_re (z : ℂ) : (swapReIm z).re = z.im := by simp [swapReIm]

@[simp] theorem swapReIm_im (z : ℂ) : (swapReIm z).im = z.re := by simp [swapReIm]

@[simp] theorem swapReIm_swapReIm (z : ℂ) : swapReIm (swapReIm z) = z := by
  apply Complex.ext <;> simp

theorem dist_swapReIm (z w : ℂ) : dist (swapReIm z) (swapReIm w) = dist z w := by
  rw [Complex.dist_eq, Complex.dist_eq, swapReIm, swapReIm, ← mul_sub, ← map_sub, norm_mul,
    Complex.norm_I, one_mul, Complex.norm_conj]

theorem continuous_swapReIm : Continuous swapReIm :=
  continuous_const.mul Complex.continuous_conj

theorem measurable_swapReIm : Measurable swapReIm := continuous_swapReIm.measurable

theorem preimage_swapReIm_ball (w : ℂ) (r : ℝ) : swapReIm ⁻¹' ball w r = ball (swapReIm w) r := by
  ext z
  simp only [mem_preimage, mem_ball]
  rw [← dist_swapReIm z (swapReIm w), swapReIm_swapReIm]

theorem preimage_swapReIm_rect (x₁ x₂ y₁ y₂ : ℝ) :
    swapReIm ⁻¹' rect x₁ x₂ y₁ y₂ = rect y₁ y₂ x₁ x₂ := by
  ext z
  simp only [mem_preimage, rect_mem_iff, swapReIm_re, swapReIm_im]
  exact and_comm

/-- Euclidean inner/outer balls of a rectangle of side ratio `≤ L`. -/
theorem rect_inner_outer {L : ℝ} (hL : 1 ≤ L) {x₁ x₂ y₁ y₂ : ℝ} (h : IsRectLE L x₁ x₂ y₁ y₂) :
    ∃ (p : ℂ) (r : ℝ), 0 < r ∧ 6 * r ≤ max (x₂ - x₁) (y₂ - y₁) ∧
      ball p r ⊆ midThird x₁ x₂ y₁ y₂ ∧ rect x₁ x₂ y₁ y₂ ⊆ ball p (6 * L * r) := by
  obtain ⟨hx, hy, hxL, hyL⟩ := h
  set w := x₂ - x₁ with hw
  set l := y₂ - y₁ with hl
  have hw0 : 0 < w := sub_pos.2 hx
  have hl0 : 0 < l := sub_pos.2 hy
  set m := min w l with hm
  have hm0 : 0 < m := lt_min hw0 hl0
  set p : ℂ := ⟨(x₁ + x₂) / 2, (y₁ + y₂) / 2⟩ with hp
  refine ⟨p, m / 6, by positivity, by
    rw [show 6 * (m / 6) = m by ring]; exact (min_le_left _ _).trans (le_max_left _ _), ?_, ?_⟩
  · intro z hz
    rw [mem_ball, Complex.dist_eq] at hz
    have hre : |z.re - p.re| < m / 6 := by
      have := (Complex.abs_re_le_norm (z - p)).trans_lt hz; simpa using this
    have him : |z.im - p.im| < m / 6 := by
      have := (Complex.abs_im_le_norm (z - p)).trans_lt hz; simpa using this
    rw [abs_lt] at hre him
    have hmw : m ≤ w := min_le_left _ _
    have hml : m ≤ l := min_le_right _ _
    simp only [hp] at hre him
    unfold midThird
    split_ifs with hlw
    · refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> linarith
    · refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> linarith
  · intro z hz
    obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hz
    rw [mem_ball, Complex.dist_eq]
    have hM : max w l ≤ L * m := by
      rcases le_total w l with hwl | hwl
      · rw [max_eq_right hwl, hm, min_eq_left hwl]; exact hyL
      · rw [max_eq_left hwl, hm, min_eq_right hwl]; exact hxL
    have hsq : ‖z - p‖ ^ 2 < (6 * L * (m / 6)) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [Complex.sub_re, Complex.sub_im, hp]
      have e1 : (z.re - (x₁ + x₂) / 2) ^ 2 ≤ (w / 2) ^ 2 := by
        apply sq_le_sq' <;> linarith
      have e2 : (z.im - (y₁ + y₂) / 2) ^ 2 ≤ (l / 2) ^ 2 := by
        apply sq_le_sq' <;> linarith
      have e3 : (w / 2) ^ 2 + (l / 2) ^ 2 < (max w l) ^ 2 := by
        have := le_max_left w l
        have := le_max_right w l
        nlinarith
      have e4 : (max w l) ^ 2 ≤ (6 * L * (m / 6)) ^ 2 := by
        rw [show 6 * L * (m / 6) = L * m by ring]
        exact pow_le_pow_left₀ (lt_max_of_lt_left hw0).le hM 2
      nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 (by positivity) hsq

/-- The number of slab doublings in the proof of `exists_rect_partition` (M05 §3.5):
`k₀ = ⌈log(C₀ + 1) / log(1 + η_s)⌉₊` with `η_s = 1/(2 max C_E 1)`. -/
def rectRatioK₀ (C₀ : ℕ) (C_E : ℝ) : ℕ :=
  ⌈Real.log (C₀ + 1) / Real.log (1 + 1 / (2 * max C_E 1))⌉₊

/-- The explicit side-ratio bound of `exists_rect_partition` (M05 §3.5): `L = max 3 (1/c_*)`
with `c_* = 3^{-k₀} min(1/4, κ)`.  It depends only on `C₀`, `C_E` and `κ`, not on the measure. -/
def rectRatioBound (C₀ : ℕ) (C_E κ : ℝ) : ℝ :=
  max 3 (3 ^ rectRatioK₀ C₀ C_E / min (1 / 4) κ)

theorem one_le_rectRatioBound (C₀ : ℕ) (C_E κ : ℝ) : 1 ≤ rectRatioBound C₀ C_E κ :=
  le_trans (by norm_num) (le_max_left _ _)

/-- **Bisection + slicing** (the core of Lemma 4).  `P` is a hereditary admissibility predicate,
`C₀` is such that admissible good rectangles of mass `> C₀` have middle third of mass `> 1`, and
`ν` is Euclidean doubling at the scale `σ` inside admissible rectangles; then every admissible
good rectangle of integer mass `n ≥ 1` splits into `n` rectangles of mass `1`, each of side ratio
`≤ L = rectRatioBound C₀ C_E κ` (explicit, independent of `ν`) and contained in an admissible
good rectangle of mass `≤ C₀`. -/
theorem exists_rect_partition {ν : Measure ℂ} (hre : ∀ x : ℝ, ν {w | w.re = x} = 0)
    (him : ∀ y : ℝ, ν {w | w.im = y} = 0)
    (P : ℝ → ℝ → ℝ → ℝ → Prop)
    (hP : ∀ x₁ x₂ y₁ y₂ x₁' x₂' y₁' y₂' : ℝ, P x₁ x₂ y₁ y₂ → x₁ ≤ x₁' → x₂' ≤ x₂ → y₁ ≤ y₁' →
      y₂' ≤ y₂ → P x₁' x₂' y₁' y₂')
    (hfin : ∀ x₁ x₂ y₁ y₂ : ℝ, P x₁ x₂ y₁ y₂ → ν (rect x₁ x₂ y₁ y₂) < ∞)
    (C₀ : ℕ) (hC₀ : ∀ x₁ x₂ y₁ y₂ : ℝ, IsRectLE 3 x₁ x₂ y₁ y₂ → P x₁ x₂ y₁ y₂ →
      (C₀ : ℝ≥0∞) < ν (rect x₁ x₂ y₁ y₂) → 1 < ν (midThird x₁ x₂ y₁ y₂))
    (σ : ℝ → ℝ → ℝ → ℝ → ℝ) (C_E κ : ℝ) (hκ : 0 < κ)
    (hσ : ∀ x₁ x₂ y₁ y₂ : ℝ, IsRectLE 3 x₁ x₂ y₁ y₂ → P x₁ x₂ y₁ y₂ →
      κ * max (x₂ - x₁) (y₂ - y₁) ≤ σ x₁ x₂ y₁ y₂ ∧
      ∀ w ∈ rect x₁ x₂ y₁ y₂, ∀ r : ℝ, 0 < r → r ≤ σ x₁ x₂ y₁ y₂ →
        ν (ball w (4 * r)) ≤ ENNReal.ofReal C_E * ν (ball w (r / 2))) :
    ∀ (n : ℕ) (x₁ x₂ y₁ y₂ : ℝ), 1 ≤ n → IsRectLE 3 x₁ x₂ y₁ y₂ →
      P x₁ x₂ y₁ y₂ → ν (rect x₁ x₂ y₁ y₂) = n →
      ∃ q : Fin n → ℝ × ℝ × ℝ × ℝ,
        Pairwise (Function.onFun Disjoint fun i ↦ rect (q i).1 (q i).2.1 (q i).2.2.1 (q i).2.2.2) ∧
        (⋃ i, rect (q i).1 (q i).2.1 (q i).2.2.1 (q i).2.2.2) = rect x₁ x₂ y₁ y₂ ∧
        ∀ i, ν (rect (q i).1 (q i).2.1 (q i).2.2.1 (q i).2.2.2) = 1 ∧
          IsRectLE (rectRatioBound C₀ C_E κ) (q i).1 (q i).2.1 (q i).2.2.1 (q i).2.2.2 ∧
          ∃ x₁' x₂' y₁' y₂' : ℝ, IsRectLE 3 x₁' x₂' y₁' y₂' ∧ P x₁' x₂' y₁' y₂' ∧
            ν (rect x₁' x₂' y₁' y₂') ≤ C₀ ∧
            rect (q i).1 (q i).2.1 (q i).2.2.1 (q i).2.2.2 ⊆ rect x₁' x₂' y₁' y₂' := sorry

end OC
