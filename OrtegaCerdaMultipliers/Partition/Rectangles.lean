import OrtegaCerdaMultipliers.Doubling.Export

/-!
# M05 (Partition) — Rectangle combinatorics for a measure on `ℂ`

See `blueprint/M05_Partition.md` §2.1.  Proofs complete (they use the upstream M01/M03 interfaces).

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

/-- The real-valued mass of `rect a t` is continuous in `t`. -/
theorem rect_continuous_toReal {ν : Measure ℂ} (hre : ∀ x : ℝ, ν {w | w.re = x} = 0)
    {a y₁ y₂ : ℝ} (hfin : ∀ b, ν (rect a b y₁ y₂) < ∞) :
    Continuous fun t : ℝ ↦ (ν (rect a t y₁ y₂)).toReal :=
  ENNReal.continuousOn_toReal.comp_continuous (continuous_measure_rect_right hre hfin)
    fun t ↦ (hfin t).ne

theorem rect_toReal_add_x (ν : Measure ℂ) {a b c y₁ y₂ : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (hfin : ν (rect a c y₁ y₂) < ∞) :
    (ν (rect a c y₁ y₂)).toReal = (ν (rect a b y₁ y₂)).toReal + (ν (rect b c y₁ y₂)).toReal := by
  have h := measure_rect_add_x ν (y₁ := y₁) (y₂ := y₂) hab hbc
  rw [h] at hfin ⊢
  exact ENNReal.toReal_add (ENNReal.add_lt_top.1 hfin).1.ne (ENNReal.add_lt_top.1 hfin).2.ne

theorem rect_eq_natCast_of_toReal {ν : Measure ℂ} {S : Set ℂ} (hS : ν S < ∞) {n : ℕ}
    (h : (ν S).toReal = n) : ν S = n := by
  rw [← ENNReal.ofReal_toReal hS.ne, h, ENNReal.ofReal_natCast]

theorem rect_strip_step_right {ν : Measure ℂ} (hre : ∀ x : ℝ, ν {w | w.re = x} = 0)
    {y₁ y₂ h : ℝ} (hh : 0 < h) (hfin : ∀ a b : ℝ, ν (rect a b y₁ y₂) < ∞)
    (hmass : ∀ a : ℝ, 1 ≤ ν (rect a (a + h) y₁ y₂)) (a : ℝ) :
    ∃ t, a + h ≤ t ∧ t ≤ a + 2 * h ∧ ∃ n : ℕ, 1 ≤ n ∧ ν (rect a t y₁ y₂) = n := by
  set F : ℝ → ℝ := fun t ↦ (ν (rect a t y₁ y₂)).toReal with hF
  have hc : Continuous F := rect_continuous_toReal hre (hfin a)
  have h1 : 1 ≤ F (a + h) := by
    have := ENNReal.toReal_mono (hfin _ _).ne (hmass a)
    simpa using this
  have h2 : F (a + h) + 1 ≤ F (a + 2 * h) := by
    simp only [hF]
    rw [rect_toReal_add_x ν (show a ≤ a + h by linarith) (show a + h ≤ a + 2 * h by linarith)
      (hfin _ _)]
    have := ENNReal.toReal_mono (hfin _ _).ne (hmass (a + h))
    rw [show a + h + h = a + 2 * h by ring] at this
    simp only [ENNReal.toReal_one] at this
    linarith
  set m := ⌈F (a + h)⌉₊
  have hm1 : F (a + h) ≤ m := Nat.le_ceil _
  have hm2 : (m : ℝ) < F (a + h) + 1 := Nat.ceil_lt_add_one (by linarith)
  obtain ⟨t, ⟨ht1, ht2⟩, hFt⟩ := intermediate_value_Icc (show a + h ≤ a + 2 * h by linarith)
    hc.continuousOn ⟨hm1, by linarith⟩
  refine ⟨t, ht1, ht2, m, Nat.one_le_ceil_iff.2 (by linarith), ?_⟩
  exact rect_eq_natCast_of_toReal (hfin _ _) hFt

theorem rect_strip_step_left {ν : Measure ℂ} (hre : ∀ x : ℝ, ν {w | w.re = x} = 0)
    {y₁ y₂ h : ℝ} (hh : 0 < h) (hfin : ∀ a b : ℝ, ν (rect a b y₁ y₂) < ∞)
    (hmass : ∀ a : ℝ, 1 ≤ ν (rect a (a + h) y₁ y₂)) (b : ℝ) :
    ∃ t, b - 2 * h ≤ t ∧ t ≤ b - h ∧ ∃ n : ℕ, 1 ≤ n ∧ ν (rect t b y₁ y₂) = n := by
  set c := b - 2 * h
  set G : ℝ → ℝ := fun t ↦ (ν (rect c b y₁ y₂)).toReal - (ν (rect c t y₁ y₂)).toReal with hG
  have hc : Continuous G := continuous_const.sub (rect_continuous_toReal hre (hfin c))
  have hGt : ∀ t, c ≤ t → t ≤ b → G t = (ν (rect t b y₁ y₂)).toReal := by
    intro t h1 h2
    simp only [hG]
    rw [rect_toReal_add_x ν h1 h2 (hfin _ _)]
    ring
  have h1 : 1 ≤ G (b - h) := by
    rw [hGt _ (by simp only [c]; linarith) (by linarith)]
    have := ENNReal.toReal_mono (hfin _ _).ne (hmass (b - h))
    rw [show b - h + h = b by ring] at this
    simpa using this
  have h2 : G (b - h) + 1 ≤ G c := by
    rw [hGt _ (by simp only [c]; linarith) (by linarith), hGt _ le_rfl (by simp only [c]; linarith),
      rect_toReal_add_x ν (show c ≤ b - h by simp only [c]; linarith) (show b - h ≤ b by linarith)
      (hfin _ _)]
    have := ENNReal.toReal_mono (hfin _ _).ne (hmass c)
    rw [show c + h = b - h by simp only [c]; ring] at this
    simp only [ENNReal.toReal_one] at this
    linarith
  set m := ⌈G (b - h)⌉₊
  have hm1 : G (b - h) ≤ m := Nat.le_ceil _
  have hm2 : (m : ℝ) < G (b - h) + 1 := Nat.ceil_lt_add_one (by linarith)
  obtain ⟨t, ⟨ht1, ht2⟩, hGt'⟩ := intermediate_value_Icc' (show c ≤ b - h by simp only [c]; linarith)
    hc.continuousOn ⟨hm1, by linarith⟩
  refine ⟨t, ht1, ht2, m, Nat.one_le_ceil_iff.2 (by linarith), ?_⟩
  rw [hGt t ht1 (by linarith)] at hGt'
  exact rect_eq_natCast_of_toReal (hfin _ _) hGt'

/-- A strictly monotone sequence on `ℤ` with gaps `≥ h > 0` covers `ℝ` by its intervals. -/
theorem rect_exists_Ico_of_gap {x : ℤ → ℝ} {h : ℝ} (hh : 0 < h)
    (hgap : ∀ k, h ≤ x (k + 1) - x k) (t : ℝ) : ∃ k, t ∈ Ico (x k) (x (k + 1)) := by
  have hmono : StrictMono x := strictMono_int_of_lt_succ fun k ↦ by linarith [hgap k]
  have hup : ∀ n : ℕ, x 0 + n * h ≤ x n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have := hgap n
      push_cast at this ⊢
      linarith
  have hdown : ∀ n : ℕ, x (-n) ≤ x 0 - n * h := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have := hgap (-(n + 1 : ℕ))
      rw [show (-((n + 1 : ℕ) : ℤ) + 1) = -(n : ℤ) by push_cast; ring] at this
      push_cast at this ⊢
      linarith
  obtain ⟨N, hN⟩ := exists_nat_gt ((|t| + |x 0|) / h)
  have hNh : |t| + |x 0| < N * h := by rwa [div_lt_iff₀ hh] at hN
  obtain ⟨k, hk, hmax⟩ := Int.exists_greatest_of_bdd (P := fun k ↦ x k ≤ t)
    ⟨N, fun k hk ↦ by
      by_contra hlt
      push_neg at hlt
      have := hmono.monotone hlt.le
      have := hup N
      have := le_abs_self t
      have := neg_abs_le (x 0)
      linarith⟩
    ⟨-N, by
      have := hdown N
      have := neg_abs_le t
      have := le_abs_self (x 0)
      linarith⟩
  refine ⟨k, hk, ?_⟩
  by_contra hle
  push_neg at hle
  have := hmax (k + 1) hle
  omega

/-- Coarse step: slicing a horizontal strip into blocks of integer mass and width in `[h, 2h]`. -/
theorem exists_strip_cuts {ν : Measure ℂ} (hre : ∀ x : ℝ, ν {w | w.re = x} = 0)
    {y₁ y₂ h : ℝ} (hh : 0 < h) (hfin : ∀ a b : ℝ, ν (rect a b y₁ y₂) < ∞)
    (hmass : ∀ a : ℝ, 1 ≤ ν (rect a (a + h) y₁ y₂)) :
    ∃ x : ℤ → ℝ, StrictMono x ∧ (∀ k, h ≤ x (k + 1) - x k ∧ x (k + 1) - x k ≤ 2 * h) ∧
      (∀ t : ℝ, ∃ k, t ∈ Ico (x k) (x (k + 1))) ∧
      ∀ k, ∃ n : ℕ, 1 ≤ n ∧ ν (rect (x k) (x (k + 1)) y₁ y₂) = n := by
  choose fR hfR using rect_strip_step_right hre hh hfin hmass
  choose fL hfL using rect_strip_step_left hre hh hfin hmass
  set x : ℤ → ℝ := fun k ↦ if 0 ≤ k then fR^[k.toNat] 0 else fL^[(-k).toNat] 0 with hx
  have hxpos : ∀ n : ℕ, x n = fR^[n] 0 := by
    intro n; simp [hx]
  have hxneg : ∀ n : ℕ, x (-(n : ℤ)) = fL^[n] 0 := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hx]
    · have : ¬ (0 ≤ -(n : ℤ)) := by omega
      simp only [hx, this, if_false, neg_neg, Int.toNat_natCast]
  -- each block is a step of `fR` or of `fL`
  have hblock : ∀ k : ℤ, h ≤ x (k + 1) - x k ∧ x (k + 1) - x k ≤ 2 * h ∧
      ∃ n : ℕ, 1 ≤ n ∧ ν (rect (x k) (x (k + 1)) y₁ y₂) = n := by
    intro k
    rcases Int.eq_nat_or_neg k with ⟨n, rfl | rfl⟩
    · have e : x ((n : ℤ) + 1) = fR (x n) := by
        rw [show ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) by push_cast; ring, hxpos, hxpos,
          Function.iterate_succ_apply']
      obtain ⟨h1, h2, hn⟩ := hfR (x n)
      rw [e]
      exact ⟨by linarith, by linarith, hn⟩
    · rcases Nat.eq_zero_or_pos n with rfl | hn
      · have e : x ((0 : ℤ) + 1) = fR (x 0) := by
          have := hxpos 1
          simp only [Nat.cast_one, Function.iterate_one] at this
          rw [zero_add, this]
          congr 1
        simp only [Nat.cast_zero, neg_zero]
        obtain ⟨h1, h2, hn⟩ := hfR (x 0)
        rw [e]
        exact ⟨by linarith, by linarith, hn⟩
      · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hn
        have e1 : -((0 + m + 1 : ℕ) : ℤ) + 1 = -(m : ℤ) := by push_cast; ring
        have e2 : x (-((0 + m + 1 : ℕ) : ℤ)) = fL (x (-(m : ℤ))) := by
          rw [hxneg, hxneg, show 0 + m + 1 = m + 1 by ring, Function.iterate_succ_apply']
        rw [e1, e2]
        obtain ⟨h1, h2, hn⟩ := hfL (x (-(m : ℤ)))
        exact ⟨by linarith, by linarith, hn⟩
  refine ⟨x, strictMono_int_of_lt_succ fun k ↦ by linarith [(hblock k).1],
    fun k ↦ ⟨(hblock k).1, (hblock k).2.1⟩, rect_exists_Ico_of_gap hh (fun k ↦ (hblock k).1),
    fun k ↦ (hblock k).2.2⟩

theorem rect_mem_ball_of_abs {z : ℂ} {a b s : ℝ} (hs : 0 < s) (h1 : |z.re - a| ≤ s / 2)
    (h2 : |z.im - b| ≤ s / 2) : z ∈ ball (⟨a, b⟩ : ℂ) s := by
  rw [mem_ball, Complex.dist_eq]
  have hsq : ‖z - ⟨a, b⟩‖ ^ 2 < s ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im]
    have e1 : (z.re - a) * (z.re - a) ≤ (s / 2) ^ 2 := by
      rw [← sq]; apply sq_le_sq' <;> linarith [abs_le.1 h1]
    have e2 : (z.im - b) * (z.im - b) ≤ (s / 2) ^ 2 := by
      rw [← sq]; apply sq_le_sq' <;> linarith [abs_le.1 h2]
    nlinarith
  exact lt_of_pow_lt_pow_left₀ 2 hs.le hsq

theorem rect_abs_lt_of_mem_ball {z c : ℂ} {r : ℝ} (h : z ∈ ball c r) :
    |z.re - c.re| < r ∧ |z.im - c.im| < r := by
  rw [mem_ball, Complex.dist_eq] at h
  exact ⟨by have := (Complex.abs_re_le_norm (z - c)).trans_lt h; simpa using this,
    by have := (Complex.abs_im_le_norm (z - c)).trans_lt h; simpa using this⟩

/-- Core of the slab reverse doubling: the slab is covered by balls of radius `s` centred on its
mid-line; each is compared, by one doubling step, with a ball of radius `s/2` centred on the
vertical line `re = v` (at distance `2s`); those smaller balls lie in `T` and overlap at most
twice. -/
theorem rect_slab_core {ν : Measure ℂ} {C_E u s y₁ y₂ v : ℝ} {T : Set ℂ} (hs : 0 < s)
    (hsl : s ≤ y₂ - y₁) (hv : |u + s / 2 - v| = 2 * s)
    (hT : ∀ η : ℝ, y₁ + s / 2 ≤ η → η ≤ y₂ - s / 2 → ball (⟨v, η⟩ : ℂ) (s / 2) ⊆ T ∧
      ν (ball (⟨v, η⟩ : ℂ) (4 * s)) ≤ ENNReal.ofReal C_E * ν (ball (⟨v, η⟩ : ℂ) (s / 2))) :
    ν (rect u (u + s) y₁ y₂) ≤ ENNReal.ofReal (2 * C_E) * ν T := by
  classical
  set hgt : ℕ → ℝ := fun j ↦ y₁ + (j + 1 / 2) * s with hhgt
  set good : ℕ → Prop := fun j ↦ ((j : ℝ) + 1) * s ≤ y₂ - y₁ with hgood
  set E : ℕ → Set ℂ := fun j ↦ if good j then ball (⟨u + s / 2, hgt j⟩ : ℂ) s else ∅ with hE
  set D : ℕ → Set ℂ := fun j ↦ if good j then ball (⟨v, hgt j⟩ : ℂ) (s / 2) else ∅ with hD
  have hgt_lo : ∀ j : ℕ, y₁ + s / 2 ≤ hgt j := fun j ↦ by
    simp only [hhgt]; have : (0 : ℝ) ≤ j := j.cast_nonneg; nlinarith
  have hgt_hi : ∀ j : ℕ, good j → hgt j ≤ y₂ - s / 2 := fun j hj ↦ by
    simp only [hhgt]; simp only [hgood] at hj; nlinarith
  -- shifting each ball of the cover
  have hshift : ∀ η : ℝ, ball (⟨u + s / 2, η⟩ : ℂ) s ⊆ ball (⟨v, η⟩ : ℂ) (4 * s) := by
    intro η z hz
    rw [mem_ball] at hz ⊢
    have hd : dist (⟨u + s / 2, η⟩ : ℂ) ⟨v, η⟩ = 2 * s := by
      rw [Complex.dist_eq, ← hv]
      have : (⟨u + s / 2, η⟩ : ℂ) - ⟨v, η⟩ = ((u + s / 2 - v : ℝ) : ℂ) := by
        apply Complex.ext <;> simp
      rw [this, Complex.norm_real, Real.norm_eq_abs]
    linarith [dist_triangle z ⟨u + s / 2, η⟩ ⟨v, η⟩]
  have hEj : ∀ j, ν (E j) ≤ ENNReal.ofReal C_E * ν (D j) := by
    intro j
    by_cases hj : good j
    · simp only [hE, hD, if_pos hj]
      exact (measure_mono (hshift _)).trans (hT _ (hgt_lo j) (hgt_hi j hj)).2
    · simp only [hE, hD, if_neg hj, measure_empty, mul_zero, le_refl]
  have htop : ν (ball (⟨u + s / 2, y₂ - s / 2⟩ : ℂ) s) ≤
      ENNReal.ofReal C_E * ν (ball (⟨v, y₂ - s / 2⟩ : ℂ) (s / 2)) :=
    (measure_mono (hshift _)).trans (hT _ (by linarith) le_rfl).2
  -- the cover
  have hcover : rect u (u + s) y₁ y₂ ⊆ (⋃ j, E j) ∪ ball (⟨u + s / 2, y₂ - s / 2⟩ : ℂ) s := by
    rintro z ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
    have hre : |z.re - (u + s / 2)| ≤ s / 2 := by rw [abs_le]; constructor <;> linarith
    by_cases htop' : y₂ - s ≤ z.im
    · exact Or.inr (rect_mem_ball_of_abs hs hre (by rw [abs_le]; constructor <;> linarith))
    · push_neg at htop'
      left
      set j := ⌊(z.im - y₁) / s⌋₊
      have hj1 : (j : ℝ) ≤ (z.im - y₁) / s := Nat.floor_le (div_nonneg (by linarith) hs.le)
      have hj2 : (z.im - y₁) / s < j + 1 := Nat.lt_floor_add_one _
      rw [le_div_iff₀ hs] at hj1
      rw [div_lt_iff₀ hs] at hj2
      have hgj : good j := by simp only [hgood]; nlinarith
      refine mem_iUnion.2 ⟨j, ?_⟩
      simp only [hE, if_pos hgj]
      refine rect_mem_ball_of_abs hs hre ?_
      simp only [hhgt]
      rw [abs_le]; constructor <;> nlinarith
  -- the comparison balls are disjoint and lie in `T`
  have hDdisj : Pairwise (Function.onFun Disjoint D) := by
    intro i j hij
    simp only [Function.onFun, hD]
    split_ifs with hi hj
    · rw [Set.disjoint_left]
      intro z hzi hzj
      have a1 := (rect_abs_lt_of_mem_ball hzi).2
      have a2 := (rect_abs_lt_of_mem_ball hzj).2
      simp only [hhgt] at a1 a2
      rw [abs_lt] at a1 a2
      rcases lt_or_gt_of_ne hij with h | h
      · have : (i : ℝ) + 1 ≤ j := by exact_mod_cast h
        nlinarith
      · have : (j : ℝ) + 1 ≤ i := by exact_mod_cast h
        nlinarith
    all_goals simp
  have hDmeas : ∀ j, MeasurableSet (D j) := fun j ↦ by
    simp only [hD]; split_ifs
    · exact measurableSet_ball
    · exact MeasurableSet.empty
  have hDT : (⋃ j, D j) ⊆ T := by
    refine iUnion_subset fun j ↦ ?_
    simp only [hD]; split_ifs with hj
    · exact (hT _ (hgt_lo j) (hgt_hi j hj)).1
    · exact empty_subset _
  have hsum : ∑' j, ν (D j) ≤ ν T := by
    rw [← measure_iUnion hDdisj hDmeas]; exact measure_mono hDT
  have htopT : ν (ball (⟨v, y₂ - s / 2⟩ : ℂ) (s / 2)) ≤ ν T :=
    measure_mono (hT _ (by linarith) le_rfl).1
  calc ν (rect u (u + s) y₁ y₂)
      ≤ ν ((⋃ j, E j) ∪ ball (⟨u + s / 2, y₂ - s / 2⟩ : ℂ) s) := measure_mono hcover
    _ ≤ ∑' j, ν (E j) + ν (ball (⟨u + s / 2, y₂ - s / 2⟩ : ℂ) s) :=
        (measure_union_le _ _).trans (add_le_add (measure_iUnion_le _) le_rfl)
    _ ≤ ∑' j, ENNReal.ofReal C_E * ν (D j) +
          ENNReal.ofReal C_E * ν (ball (⟨v, y₂ - s / 2⟩ : ℂ) (s / 2)) :=
        add_le_add (ENNReal.tsum_le_tsum hEj) htop
    _ = ENNReal.ofReal C_E * (∑' j, ν (D j) + ν (ball (⟨v, y₂ - s / 2⟩ : ℂ) (s / 2))) := by
        rw [ENNReal.tsum_mul_left, mul_add]
    _ ≤ ENNReal.ofReal C_E * (ν T + ν T) := by gcongr
    _ = ENNReal.ofReal (2 * C_E) * ν T := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat, ← two_mul,
          ← mul_assoc, mul_comm (ENNReal.ofReal C_E) 2]

/-- Slab reverse doubling (the missing argument behind "we use Lemma 1", p. 365): a vertical slab
of width `s` in a rectangle has a neighbouring slab of comparable mass, provided `s` is at most
the height and the scale `σ` at which `ν` is Euclidean doubling. -/
theorem slab_reverse_doubling_right {ν : Measure ℂ} {C_E u s y₁ y₂ : ℝ} (hs : 0 < s)
    (hsl : s ≤ y₂ - y₁)
    (hED : ∀ w ∈ rect (u + s) (u + 3 * s) y₁ y₂, ∀ r : ℝ, 0 < r → r ≤ s →
      ν (ball w (4 * r)) ≤ ENNReal.ofReal C_E * ν (ball w (r / 2))) :
    ν (rect u (u + s) y₁ y₂) ≤ ENNReal.ofReal (2 * C_E) * ν (rect (u + s) (u + 3 * s) y₁ y₂) := by
  refine rect_slab_core (v := u + 5 * s / 2) hs hsl ?_ fun η h1 h2 ↦ ⟨?_, ?_⟩
  · rw [show u + s / 2 - (u + 5 * s / 2) = -(2 * s) by ring, abs_neg, abs_of_pos (by linarith)]
  · intro z hz
    obtain ⟨a1, a2⟩ := rect_abs_lt_of_mem_ball hz
    rw [abs_lt] at a1 a2
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  · exact hED _ ⟨⟨by simp; linarith, by simp; linarith⟩, ⟨by simp; linarith, by simp; linarith⟩⟩
      s hs le_rfl

theorem slab_reverse_doubling_left {ν : Measure ℂ} {C_E u s y₁ y₂ : ℝ} (hs : 0 < s)
    (hsl : s ≤ y₂ - y₁)
    (hED : ∀ w ∈ rect (u - 2 * s) u y₁ y₂, ∀ r : ℝ, 0 < r → r ≤ s →
      ν (ball w (4 * r)) ≤ ENNReal.ofReal C_E * ν (ball w (r / 2))) :
    ν (rect u (u + s) y₁ y₂) ≤ ENNReal.ofReal (2 * C_E) * ν (rect (u - 2 * s) u y₁ y₂) := by
  refine rect_slab_core (v := u - 3 * s / 2) hs hsl ?_ fun η h1 h2 ↦ ⟨?_, ?_⟩
  · rw [show u + s / 2 - (u - 3 * s / 2) = 2 * s by ring, abs_of_pos (by linarith)]
  · intro z hz
    obtain ⟨a1, a2⟩ := rect_abs_lt_of_mem_ball hz
    rw [abs_lt] at a1 a2
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  · exact hED _ ⟨⟨by simp; linarith, by simp; linarith⟩, ⟨by simp; linarith, by simp; linarith⟩⟩
      s hs le_rfl

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

/-! ### The core construction (M05 §3.5) -/

theorem rectCore_continuousOn {ν : Measure ℂ} (hre : ∀ x : ℝ, ν {w | w.re = x} = 0)
    {x₁ x₂ y₁ y₂ : ℝ} (hQ : ν (rect x₁ x₂ y₁ y₂) < ∞) :
    ContinuousOn (fun t ↦ (ν (rect x₁ t y₁ y₂)).toReal) (Icc x₁ x₂) := by
  set Q := rect x₁ x₂ y₁ y₂ with hQdef
  have hre' : ∀ x : ℝ, ν.restrict Q {w | w.re = x} = 0 := fun x ↦
    nonpos_iff_eq_zero.1 ((Measure.restrict_apply_le _ _).trans (hre x).le)
  have hfin' : ∀ b, ν.restrict Q (rect x₁ b y₁ y₂) < ∞ := fun b ↦
    (measure_mono (subset_univ _)).trans_lt (by rw [Measure.restrict_apply_univ]; exact hQ)
  refine (rect_continuous_toReal hre' hfin').continuousOn.congr fun t ht ↦ ?_
  simp only
  rw [Measure.restrict_apply (measurableSet_rect _ _ _ _),
    inter_eq_left.2 (rect_subset_rect le_rfl ht.2 le_rfl le_rfl)]

theorem rectCore_bisect_x {ν : Measure ℂ} (hre : ∀ x : ℝ, ν {w | w.re = x} = 0)
    {x₁ x₂ y₁ y₂ : ℝ} (hx : x₁ < x₂) {n : ℕ} (hQ : ν (rect x₁ x₂ y₁ y₂) = n)
    (hmid : 1 < ν (rect (x₁ + (x₂ - x₁) / 3) (x₂ - (x₂ - x₁) / 3) y₁ y₂)) :
    ∃ t : ℝ, ∃ n₁ n₂ : ℕ, x₁ + (x₂ - x₁) / 3 < t ∧ t < x₂ - (x₂ - x₁) / 3 ∧ 1 ≤ n₁ ∧ 1 ≤ n₂ ∧
      n₁ + n₂ = n ∧ ν (rect x₁ t y₁ y₂) = n₁ ∧ ν (rect t x₂ y₁ y₂) = n₂ := by
  have hQf : ν (rect x₁ x₂ y₁ y₂) < ∞ := by rw [hQ]; exact ENNReal.natCast_lt_top n
  set F : ℝ → ℝ := fun t ↦ (ν (rect x₁ t y₁ y₂)).toReal with hF
  have hc := rectCore_continuousOn hre hQf
  set a := x₁ + (x₂ - x₁) / 3 with ha
  set b := x₂ - (x₂ - x₁) / 3 with hb
  have hxa : x₁ ≤ a := by linarith
  have hab : a ≤ b := by linarith
  have hbx : b ≤ x₂ := by linarith
  have hfin_sub : ∀ c d, x₁ ≤ c → d ≤ x₂ → ν (rect c d y₁ y₂) < ∞ := fun c d hc hd ↦
    (measure_mono (rect_subset_rect hc hd le_rfl le_rfl)).trans_lt hQf
  have hFab : F a + 1 < F b := by
    simp only [hF]
    rw [rect_toReal_add_x ν hxa hab (hfin_sub _ _ le_rfl hbx)]
    have := (ENNReal.toReal_lt_toReal ENNReal.one_ne_top (hfin_sub _ _ hxa hbx).ne).2 hmid
    simp only [ENNReal.toReal_one] at this
    linarith
  have hFx₂ : F x₂ = n := by simp only [hF, hQ, ENNReal.toReal_natCast]
  have hFb : F b ≤ n := by
    rw [← hFx₂]
    exact ENNReal.toReal_mono hQf.ne (measure_mono (rect_subset_rect le_rfl hbx le_rfl le_rfl))
  have hFa0 : 0 ≤ F a := ENNReal.toReal_nonneg
  set n₁ := ⌊F a⌋₊ + 1 with hn₁
  have hn₁a : F a < n₁ := by rw [hn₁]; push_cast; exact Nat.lt_floor_add_one _
  have hn₁b : (n₁ : ℝ) < F b := by
    have : (⌊F a⌋₊ : ℝ) ≤ F a := Nat.floor_le hFa0
    rw [hn₁]; push_cast; linarith
  obtain ⟨t, ⟨ht1, ht2⟩, hFt⟩ :=
    intermediate_value_Ioo hab (hc.mono (Icc_subset_Icc hxa hbx)) ⟨hn₁a, hn₁b⟩
  have hn₁n : n₁ < n := by exact_mod_cast hn₁b.trans_le hFb
  refine ⟨t, n₁, n - n₁, ht1, ht2, Nat.le_add_left 1 _, by omega, by omega, ?_, ?_⟩
  · exact rect_eq_natCast_of_toReal (hfin_sub _ _ le_rfl (by linarith)) hFt
  · refine rect_eq_natCast_of_toReal (hfin_sub _ _ (by linarith) le_rfl) ?_
    have := rect_toReal_add_x ν (y₁ := y₁) (y₂ := y₂) (show x₁ ≤ t by linarith)
      (show t ≤ x₂ by linarith) hQf
    rw [hQ, ENNReal.toReal_natCast] at this
    simp only [hF] at hFt
    rw [Nat.cast_sub hn₁n.le]
    linarith

theorem rectCore_exists_index {t : ℕ → ℝ} (n : ℕ) {a : ℝ} (h0 : t 0 ≤ a) (hn : a < t n) :
    ∃ i < n, t i ≤ a ∧ a < t (i + 1) := by
  induction n with
  | zero => exact absurd (h0.trans_lt hn) (lt_irrefl _)
  | succ n ih =>
    by_cases h : t n ≤ a
    · exact ⟨n, Nat.lt_succ_self n, h, hn⟩
    · push_neg at h
      obtain ⟨i, hi, h1, h2⟩ := ih h
      exact ⟨i, by omega, h1, h2⟩

theorem rectCore_slice_x {ν : Measure ℂ} (hre : ∀ x : ℝ, ν {w | w.re = x} = 0)
    {x₁ x₂ y₁ y₂ : ℝ} (hx : x₁ < x₂) {n : ℕ} (hn : 1 ≤ n) (hQ : ν (rect x₁ x₂ y₁ y₂) = n) :
    ∃ t : ℕ → ℝ, t 0 = x₁ ∧ t n = x₂ ∧ Monotone t ∧ (∀ i < n, t i < t (i + 1)) ∧
      ∀ i < n, ν (rect (t i) (t (i + 1)) y₁ y₂) = 1 := by
  have hQf : ν (rect x₁ x₂ y₁ y₂) < ∞ := by rw [hQ]; exact ENNReal.natCast_lt_top n
  set F : ℝ → ℝ := fun t ↦ (ν (rect x₁ t y₁ y₂)).toReal with hF
  have hc : ContinuousOn F (Icc x₁ x₂) := rectCore_continuousOn hre hQf
  have hF0 : F x₁ = 0 := by simp [hF, rect_eq_empty_of_le le_rfl]
  have hFn : F x₂ = n := by simp only [hF, hQ, ENNReal.toReal_natCast]
  have hex : ∀ j : ℕ, ∃ τ, j ≤ n → τ ∈ Icc x₁ x₂ ∧ F τ = j := by
    intro j
    by_cases hj : j ≤ n
    · obtain ⟨τ, hτ, hFτ⟩ := intermediate_value_Icc hx.le hc
        (show (j : ℝ) ∈ Icc (F x₁) (F x₂) from
          ⟨by rw [hF0]; positivity, by rw [hFn]; exact_mod_cast hj⟩)
      exact ⟨τ, fun _ ↦ ⟨hτ, hFτ⟩⟩
    · exact ⟨x₁, fun h ↦ absurd h hj⟩
  choose τ hτ using hex
  set t : ℕ → ℝ := fun j ↦ if j = 0 then x₁ else if n ≤ j then x₂ else τ j with ht
  have htI : ∀ j, t j ∈ Icc x₁ x₂ := by
    intro j
    simp only [ht]
    split_ifs with h1 h2
    · exact ⟨le_rfl, hx.le⟩
    · exact ⟨hx.le, le_rfl⟩
    · exact (hτ j (by omega)).1
  have htF : ∀ j ≤ n, F (t j) = j := by
    intro j hj
    simp only [ht]
    split_ifs with h1 h2
    · rw [h1, hF0]; simp
    · rw [show j = n by omega, hFn]
    · exact (hτ j hj).2
  have hFmono : ∀ a b, a ∈ Icc x₁ x₂ → b ∈ Icc x₁ x₂ → a ≤ b → F a ≤ F b := by
    intro a b _ hb hab
    exact ENNReal.toReal_mono
      ((measure_mono (rect_subset_rect le_rfl hb.2 le_rfl le_rfl)).trans_lt hQf).ne
      (measure_mono (rect_subset_rect le_rfl hab le_rfl le_rfl))
  have hlt : ∀ i j, i < j → j ≤ n → t i < t j := by
    intro i j hij hjn
    by_contra hle
    push_neg at hle
    have := hFmono _ _ (htI j) (htI i) hle
    rw [htF j hjn, htF i (by omega)] at this
    have : (j : ℝ) > i := by exact_mod_cast hij
    linarith
  have hmono : Monotone t := by
    intro i j hij
    rcases eq_or_lt_of_le hij with rfl | hij
    · exact le_rfl
    by_cases hjn : j ≤ n
    · exact (hlt i j hij hjn).le
    · have : t j = x₂ := by
        simp only [ht]
        rw [if_neg (by omega), if_pos (by omega)]
      rw [this]; exact (htI i).2
  refine ⟨t, by simp [ht], ?_, hmono, fun i hi ↦ hlt i (i + 1) (by omega) hi, fun i hi ↦ ?_⟩
  · simp only [ht]; rw [if_neg (by omega), if_pos le_rfl]
  · have hadd := rect_toReal_add_x ν (y₁ := y₁) (y₂ := y₂) (htI i).1 (hmono (Nat.le_succ i))
      ((measure_mono (rect_subset_rect le_rfl (htI (i + 1)).2 le_rfl le_rfl)).trans_lt hQf)
    have h1 := htF i (by omega)
    have h2 := htF (i + 1) hi
    simp only [hF] at h1 h2
    rw [h1, h2] at hadd
    refine (rect_eq_natCast_of_toReal (n := 1)
      ((measure_mono (rect_subset_rect (htI i).1 (htI (i + 1)).2 le_rfl le_rfl)).trans_lt hQf)
      ?_).trans Nat.cast_one
    push_cast at hadd ⊢
    linarith

theorem rectCore_slices_x {t : ℕ → ℝ} (n : ℕ) (htm : Monotone t) (y₁ y₂ : ℝ) :
    Pairwise (Function.onFun Disjoint fun i : Fin n ↦ rect (t i) (t (i + 1)) y₁ y₂) ∧
    (⋃ i : Fin n, rect (t i) (t (i + 1)) y₁ y₂) = rect (t 0) (t n) y₁ y₂ := by
  refine ⟨fun i j hij ↦ ?_, ?_⟩
  · have hij' : (i : ℕ) ≠ j := fun h ↦ hij (Fin.ext h)
    rcases lt_or_gt_of_ne hij' with h | h
    · exact rect_disjoint_x (htm (by omega))
    · exact (rect_disjoint_x (htm (by omega))).symm
  · ext w
    simp only [mem_iUnion]
    constructor
    · rintro ⟨i, hw⟩
      exact rect_subset_rect (htm (Nat.zero_le _)) (htm (by omega)) le_rfl le_rfl hw
    · rintro ⟨⟨h1, h2⟩, h3⟩
      obtain ⟨i, hi, hi1, hi2⟩ := rectCore_exists_index n h1 h2
      exact ⟨⟨i, hi⟩, ⟨hi1, hi2⟩, h3⟩

theorem rectCore_slices_y {t : ℕ → ℝ} (n : ℕ) (htm : Monotone t) (x₁ x₂ : ℝ) :
    Pairwise (Function.onFun Disjoint fun i : Fin n ↦ rect x₁ x₂ (t i) (t (i + 1))) ∧
    (⋃ i : Fin n, rect x₁ x₂ (t i) (t (i + 1))) = rect x₁ x₂ (t 0) (t n) := by
  refine ⟨fun i j hij ↦ ?_, ?_⟩
  · have hij' : (i : ℕ) ≠ j := fun h ↦ hij (Fin.ext h)
    rcases lt_or_gt_of_ne hij' with h | h
    · exact rect_disjoint_y (htm (by omega))
    · exact (rect_disjoint_y (htm (by omega))).symm
  · ext w
    simp only [mem_iUnion]
    constructor
    · rintro ⟨i, hw⟩
      exact rect_subset_rect le_rfl le_rfl (htm (Nat.zero_le _)) (htm (by omega)) hw
    · rintro ⟨h3, ⟨h1, h2⟩⟩
      obtain ⟨i, hi, hi1, hi2⟩ := rectCore_exists_index n h1 h2
      exact ⟨⟨i, hi⟩, h3, ⟨hi1, hi2⟩⟩

theorem rectCore_pow_ge (C₀ : ℕ) (C_E : ℝ) :
    (C₀ : ℝ) + 1 ≤ (1 + 1 / (2 * max C_E 1)) ^ rectRatioK₀ C₀ C_E := by
  have hC : 1 ≤ max C_E 1 := le_max_right _ _
  have hlog : 0 < Real.log (1 + 1 / (2 * max C_E 1)) :=
    Real.log_pos (by have : 0 < 1 / (2 * max C_E 1) := by positivity
                     linarith)
  have hk := Nat.le_ceil (Real.log (C₀ + 1) / Real.log (1 + 1 / (2 * max C_E 1)))
  rw [div_le_iff₀ hlog] at hk
  rw [← Real.log_le_log_iff (by positivity) (by positivity), Real.log_pow]
  exact hk

theorem rectCore_growth {A B : ℕ → ℝ} {C : ℝ} (hC : 1 ≤ C) (k : ℕ) (h0 : A 0 = 1)
    (hstep : ∀ i < k, A (i + 1) = A i + B i ∧ A i ≤ 2 * C * B i) :
    (1 + 1 / (2 * C)) ^ k ≤ A k := by
  induction k with
  | zero => simp [h0]
  | succ k ih =>
    have ih' := ih (fun i hi ↦ hstep i (by omega))
    obtain ⟨h1, h2⟩ := hstep k (by omega)
    have hB : A k / (2 * C) ≤ B k := by rw [div_le_iff₀ (by positivity)]; linarith
    rw [pow_succ, h1]
    calc (1 + 1 / (2 * C)) ^ k * (1 + 1 / (2 * C)) ≤ A k * (1 + 1 / (2 * C)) := by
          gcongr
      _ = A k + A k / (2 * C) := by ring
      _ ≤ A k + B k := by linarith

/-- The final slices are not thin (M05 §3.5, Case B, via slab reverse doubling). -/
theorem rectCore_slice_wide {ν : Measure ℂ} {C₀ : ℕ} {C_E κ x₁ x₂ y₁ y₂ t t' : ℝ}
    (hlw : y₂ - y₁ ≤ x₂ - x₁) (hw3 : x₂ - x₁ ≤ 3 * (y₂ - y₁)) (hx : x₁ ≤ t) (htt' : t < t')
    (ht' : t' ≤ x₂) (hQ : ν (rect x₁ x₂ y₁ y₂) ≤ C₀) (hS : ν (rect t t' y₁ y₂) = 1)
    (hED : ∀ w ∈ rect x₁ x₂ y₁ y₂, ∀ r : ℝ, 0 < r → r ≤ κ * (x₂ - x₁) →
      ν (ball w (4 * r)) ≤ ENNReal.ofReal C_E * ν (ball w (r / 2))) :
    min (1 / 4) κ / 3 ^ rectRatioK₀ C₀ C_E * (x₂ - x₁) ≤ t' - t := by
  set C := max C_E 1 with hCdef
  have hC : 1 ≤ C := le_max_right _ _
  set k₀ := rectRatioK₀ C₀ C_E with hk₀
  have hw : 0 < x₂ - x₁ := by linarith
  have hs : 0 < t' - t := sub_pos.2 htt'
  have h3 : (0 : ℝ) < 3 ^ k₀ := by positivity
  by_contra hcon
  push_neg at hcon
  have hsk : 3 ^ k₀ * (t' - t) < min (1 / 4) κ * (x₂ - x₁) := by
    rw [div_mul_eq_mul_div, lt_div_iff₀ h3] at hcon; linarith
  have hm1 : min (1 / 4) κ ≤ 1 / 4 := min_le_left _ _
  have hm2 : min (1 / 4) κ ≤ κ := min_le_right _ _
  have hsk1 : 3 ^ k₀ * (t' - t) < (x₂ - x₁) / 4 := by nlinarith
  have hsk2 : 3 ^ k₀ * (t' - t) < κ * (x₂ - x₁) := by nlinarith
  have hQf : ν (rect x₁ x₂ y₁ y₂) < ∞ := hQ.trans_lt (ENNReal.natCast_lt_top _)
  have hfin_sub : ∀ c d, x₁ ≤ c → d ≤ x₂ → ν (rect c d y₁ y₂) < ∞ := fun c d hc hd ↦
    (measure_mono (rect_subset_rect hc hd le_rfl le_rfl)).trans_lt hQf
  have hED' : ∀ c d, x₁ ≤ c → d ≤ x₂ → ∀ w ∈ rect c d y₁ y₂, ∀ r : ℝ, 0 < r →
      r ≤ κ * (x₂ - x₁) → ν (ball w (4 * r)) ≤ ENNReal.ofReal C * ν (ball w (r / 2)) := by
    intro c d hc hd w hw r hr hrκ
    exact (hED w (rect_subset_rect hc hd le_rfl le_rfl hw) r hr hrκ).trans
      (by gcongr; exact le_max_left _ _)
  have hpow := rectCore_pow_ge C₀ C_E
  have hQr : (ν (rect x₁ x₂ y₁ y₂)).toReal ≤ C₀ := by
    have := ENNReal.toReal_mono (ENNReal.natCast_ne_top C₀) hQ
    simpa using this
  have h3i : ∀ i ≤ k₀, (3 : ℝ) ^ i * (t' - t) ≤ 3 ^ k₀ * (t' - t) := fun i hi ↦ by
    gcongr
    · norm_num
  have hsl : ∀ i ≤ k₀, (3 : ℝ) ^ i * (t' - t) ≤ y₂ - y₁ := fun i hi ↦ by
    have := h3i i hi; linarith
  rcases le_or_gt ((x₂ - x₁) / 4) (x₂ - t') with hright | hleft
  · -- grow to the right
    set A : ℕ → ℝ := fun i ↦ (ν (rect t (t + 3 ^ i * (t' - t)) y₁ y₂)).toReal with hA
    set B : ℕ → ℝ := fun i ↦
      (ν (rect (t + 3 ^ i * (t' - t)) (t + 3 * (3 ^ i * (t' - t))) y₁ y₂)).toReal with hB
    have hend : ∀ i ≤ k₀, t + 3 ^ i * (t' - t) ≤ x₂ := fun i hi ↦ by
      have := h3i i hi; linarith
    have hA0 : A 0 = 1 := by
      simp only [hA, pow_zero, one_mul, add_sub_cancel, hS, ENNReal.toReal_one]
    have hstep : ∀ i < k₀, A (i + 1) = A i + B i ∧ A i ≤ 2 * C * B i := by
      intro i hi
      have hsi : 0 < 3 ^ i * (t' - t) := by positivity
      have e : (3 : ℝ) ^ (i + 1) * (t' - t) = 3 * (3 ^ i * (t' - t)) := by ring
      have hend' : t + 3 * (3 ^ i * (t' - t)) ≤ x₂ := by rw [← e]; exact hend (i + 1) hi
      constructor
      · simp only [hA, hB]
        rw [e]
        exact rect_toReal_add_x ν (by linarith) (by linarith) (hfin_sub _ _ hx hend')
      · have hslab := slab_reverse_doubling_right (ν := ν) (C_E := C) (u := t) (y₁ := y₁)
          (y₂ := y₂) hsi (hsl i hi.le) (fun w hw r hr hrs ↦
            hED' _ _ (by linarith) hend' w hw r hr (by have := h3i i hi.le; linarith))
        have := ENNReal.toReal_mono
          (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hfin_sub _ _ (by linarith) hend').ne) hslab
        rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at this
    have hg := rectCore_growth hC k₀ hA0 hstep
    have hAk : A k₀ ≤ C₀ := (ENNReal.toReal_mono hQf.ne
      (measure_mono (rect_subset_rect hx (hend k₀ le_rfl) le_rfl le_rfl))).trans hQr
    linarith
  · -- grow to the left
    have h30 : t' - t ≤ 3 ^ k₀ * (t' - t) := by
      have := h3i 0 (Nat.zero_le _); simpa using this
    have hroom : (x₂ - x₁) / 4 ≤ t - x₁ := by linarith
    set A : ℕ → ℝ := fun i ↦ (ν (rect (t' - 3 ^ i * (t' - t)) t' y₁ y₂)).toReal with hA
    set B : ℕ → ℝ := fun i ↦
      (ν (rect (t' - 3 * (3 ^ i * (t' - t))) (t' - 3 ^ i * (t' - t)) y₁ y₂)).toReal with hB
    have hstart : ∀ i ≤ k₀, x₁ ≤ t' - 3 ^ i * (t' - t) := fun i hi ↦ by
      have := h3i i hi; linarith
    have hA0 : A 0 = 1 := by
      simp only [hA, pow_zero, one_mul, sub_sub_cancel, hS, ENNReal.toReal_one]
    have hstep : ∀ i < k₀, A (i + 1) = A i + B i ∧ A i ≤ 2 * C * B i := by
      intro i hi
      have hsi : 0 < 3 ^ i * (t' - t) := by positivity
      have e : (3 : ℝ) ^ (i + 1) * (t' - t) = 3 * (3 ^ i * (t' - t)) := by ring
      have hstart' : x₁ ≤ t' - 3 * (3 ^ i * (t' - t)) := by rw [← e]; exact hstart (i + 1) hi
      constructor
      · simp only [hA, hB]
        rw [e, add_comm (ν (rect (t' - 3 ^ i * (t' - t)) t' y₁ y₂)).toReal]
        exact rect_toReal_add_x ν (by linarith) (by linarith) (hfin_sub _ _ hstart' ht')
      · have hslab := slab_reverse_doubling_left (ν := ν) (C_E := C)
          (u := t' - 3 ^ i * (t' - t)) (y₁ := y₁) (y₂ := y₂) hsi (hsl i hi.le)
          (fun w hw r hr hrs ↦ hED' _ _ (by linarith) (by linarith) w hw r hr
            (by have := h3i i hi.le; linarith))
        rw [show t' - 3 ^ i * (t' - t) + 3 ^ i * (t' - t) = t' by ring,
          show t' - 3 ^ i * (t' - t) - 2 * (3 ^ i * (t' - t)) = t' - 3 * (3 ^ i * (t' - t)) by
            ring] at hslab
        have := ENNReal.toReal_mono
          (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
            (hfin_sub _ _ hstart' (by linarith)).ne) hslab
        rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at this
    have hg := rectCore_growth hC k₀ hA0 hstep
    have hAk : A k₀ ≤ C₀ := (ENNReal.toReal_mono hQf.ne
      (measure_mono (rect_subset_rect (hstart k₀ le_rfl) ht' le_rfl le_rfl))).trans hQr
    linarith

/-! #### Transfer through the coordinate swap -/

theorem rectCore_map_swap_rect (ν : Measure ℂ) (a b c d : ℝ) :
    ν.map swapReIm (rect a b c d) = ν (rect c d a b) := by
  rw [Measure.map_apply measurable_swapReIm (measurableSet_rect _ _ _ _), preimage_swapReIm_rect]

theorem rectCore_map_swap_ball (ν : Measure ℂ) (w : ℂ) (r : ℝ) :
    ν.map swapReIm (ball w r) = ν (ball (swapReIm w) r) := by
  rw [Measure.map_apply measurable_swapReIm measurableSet_ball, preimage_swapReIm_ball]

theorem rectCore_map_swap_re {ν : Measure ℂ} (him : ∀ y : ℝ, ν {w | w.im = y} = 0) (x : ℝ) :
    ν.map swapReIm {w | w.re = x} = 0 := by
  rw [Measure.map_apply measurable_swapReIm
    ((isClosed_eq Complex.continuous_re continuous_const).measurableSet)]
  have : swapReIm ⁻¹' {w | w.re = x} = {w | w.im = x} := by ext; simp
  rw [this, him]

theorem rectCore_bisect_y {ν : Measure ℂ} (him : ∀ y : ℝ, ν {w | w.im = y} = 0)
    {x₁ x₂ y₁ y₂ : ℝ} (hy : y₁ < y₂) {n : ℕ} (hQ : ν (rect x₁ x₂ y₁ y₂) = n)
    (hmid : 1 < ν (rect x₁ x₂ (y₁ + (y₂ - y₁) / 3) (y₂ - (y₂ - y₁) / 3))) :
    ∃ t : ℝ, ∃ n₁ n₂ : ℕ, y₁ + (y₂ - y₁) / 3 < t ∧ t < y₂ - (y₂ - y₁) / 3 ∧ 1 ≤ n₁ ∧ 1 ≤ n₂ ∧
      n₁ + n₂ = n ∧ ν (rect x₁ x₂ y₁ t) = n₁ ∧ ν (rect x₁ x₂ t y₂) = n₂ := by
  have := rectCore_bisect_x (ν := ν.map swapReIm) (rectCore_map_swap_re him) (y₁ := x₁)
    (y₂ := x₂) hy (by rw [rectCore_map_swap_rect]; exact hQ)
    (by rw [rectCore_map_swap_rect]; exact hmid)
  simpa only [rectCore_map_swap_rect] using this

theorem rectCore_slice_y {ν : Measure ℂ} (him : ∀ y : ℝ, ν {w | w.im = y} = 0)
    {x₁ x₂ y₁ y₂ : ℝ} (hy : y₁ < y₂) {n : ℕ} (hn : 1 ≤ n) (hQ : ν (rect x₁ x₂ y₁ y₂) = n) :
    ∃ t : ℕ → ℝ, t 0 = y₁ ∧ t n = y₂ ∧ Monotone t ∧ (∀ i < n, t i < t (i + 1)) ∧
      ∀ i < n, ν (rect x₁ x₂ (t i) (t (i + 1))) = 1 := by
  have := rectCore_slice_x (ν := ν.map swapReIm) (rectCore_map_swap_re him) (y₁ := x₁)
    (y₂ := x₂) hy hn (by rw [rectCore_map_swap_rect]; exact hQ)
  simpa only [rectCore_map_swap_rect] using this

theorem rectCore_slice_wide_y {ν : Measure ℂ} {C₀ : ℕ} {C_E κ x₁ x₂ y₁ y₂ t t' : ℝ}
    (hwl : x₂ - x₁ ≤ y₂ - y₁) (hl3 : y₂ - y₁ ≤ 3 * (x₂ - x₁)) (hy : y₁ ≤ t) (htt' : t < t')
    (ht' : t' ≤ y₂) (hQ : ν (rect x₁ x₂ y₁ y₂) ≤ C₀) (hS : ν (rect x₁ x₂ t t') = 1)
    (hED : ∀ w ∈ rect x₁ x₂ y₁ y₂, ∀ r : ℝ, 0 < r → r ≤ κ * (y₂ - y₁) →
      ν (ball w (4 * r)) ≤ ENNReal.ofReal C_E * ν (ball w (r / 2))) :
    min (1 / 4) κ / 3 ^ rectRatioK₀ C₀ C_E * (y₂ - y₁) ≤ t' - t := by
  refine rectCore_slice_wide (ν := ν.map swapReIm) (y₁ := x₁) (y₂ := x₂) hwl hl3 hy htt' ht'
    (by rw [rectCore_map_swap_rect]; exact hQ) (by rw [rectCore_map_swap_rect]; exact hS)
    fun w hw r hr hrκ ↦ ?_
  rw [rectCore_map_swap_ball, rectCore_map_swap_ball]
  refine hED _ ?_ r hr hrκ
  rw [← preimage_swapReIm_rect] at hw
  exact hw

theorem rectCore_combine {G : ℝ × ℝ × ℝ × ℝ → Prop} {n₁ n₂ : ℕ} {U₁ U₂ : Set ℂ}
    (h₁ : ∃ q : Fin n₁ → ℝ × ℝ × ℝ × ℝ,
      Pairwise (Function.onFun Disjoint fun i ↦ rect (q i).1 (q i).2.1 (q i).2.2.1 (q i).2.2.2) ∧
      (⋃ i, rect (q i).1 (q i).2.1 (q i).2.2.1 (q i).2.2.2) = U₁ ∧ ∀ i, G (q i))
    (h₂ : ∃ q : Fin n₂ → ℝ × ℝ × ℝ × ℝ,
      Pairwise (Function.onFun Disjoint fun i ↦ rect (q i).1 (q i).2.1 (q i).2.2.1 (q i).2.2.2) ∧
      (⋃ i, rect (q i).1 (q i).2.1 (q i).2.2.1 (q i).2.2.2) = U₂ ∧ ∀ i, G (q i))
    (hU : Disjoint U₁ U₂) :
    ∃ q : Fin (n₁ + n₂) → ℝ × ℝ × ℝ × ℝ,
      Pairwise (Function.onFun Disjoint fun i ↦ rect (q i).1 (q i).2.1 (q i).2.2.1 (q i).2.2.2) ∧
      (⋃ i, rect (q i).1 (q i).2.1 (q i).2.2.1 (q i).2.2.2) = U₁ ∪ U₂ ∧ ∀ i, G (q i) := by
  obtain ⟨q₁, hd₁, hu₁, hg₁⟩ := h₁
  obtain ⟨q₂, hd₂, hu₂, hg₂⟩ := h₂
  have hs₁ : ∀ i, rect (q₁ i).1 (q₁ i).2.1 (q₁ i).2.2.1 (q₁ i).2.2.2 ⊆ U₁ := fun i ↦
    hu₁ ▸ subset_iUnion (fun i ↦ rect (q₁ i).1 (q₁ i).2.1 (q₁ i).2.2.1 (q₁ i).2.2.2) i
  have hs₂ : ∀ i, rect (q₂ i).1 (q₂ i).2.1 (q₂ i).2.2.1 (q₂ i).2.2.2 ⊆ U₂ := fun i ↦
    hu₂ ▸ subset_iUnion (fun i ↦ rect (q₂ i).1 (q₂ i).2.1 (q₂ i).2.2.1 (q₂ i).2.2.2) i
  refine ⟨Fin.append q₁ q₂, ?_, ?_, ?_⟩
  · intro i j hij
    induction i using Fin.addCases with
    | left a =>
      induction j using Fin.addCases with
      | left b =>
        simp only [Function.onFun, Fin.append_left]
        exact hd₁ (fun h ↦ hij (by rw [h]))
      | right b =>
        simp only [Function.onFun, Fin.append_left, Fin.append_right]
        exact hU.mono (hs₁ a) (hs₂ b)
    | right a =>
      induction j using Fin.addCases with
      | left b =>
        simp only [Function.onFun, Fin.append_left, Fin.append_right]
        exact (hU.mono (hs₁ b) (hs₂ a)).symm
      | right b =>
        simp only [Function.onFun, Fin.append_right]
        exact hd₂ (fun h ↦ hij (by rw [h]))
  · ext z
    simp only [mem_iUnion, mem_union]
    constructor
    · rintro ⟨i, hi⟩
      induction i using Fin.addCases with
      | left a =>
        simp only [Fin.append_left] at hi
        exact Or.inl (hs₁ a hi)
      | right a =>
        simp only [Fin.append_right] at hi
        exact Or.inr (hs₂ a hi)
    · rintro (h | h)
      · rw [← hu₁, mem_iUnion] at h
        obtain ⟨a, ha⟩ := h
        exact ⟨Fin.castAdd n₂ a, by simpa only [Fin.append_left] using ha⟩
      · rw [← hu₂, mem_iUnion] at h
        obtain ⟨a, ha⟩ := h
        exact ⟨Fin.natAdd n₁ a, by simpa only [Fin.append_right] using ha⟩
  · intro i
    induction i using Fin.addCases with
    | left a => simpa only [Fin.append_left] using hg₁ a
    | right a => simpa only [Fin.append_right] using hg₂ a

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
            rect (q i).1 (q i).2.1 (q i).2.2.1 (q i).2.2.2 ⊆ rect x₁' x₂' y₁' y₂' := by
  set L := rectRatioBound C₀ C_E κ with hLdef
  set cs := min (1 / 4) κ / 3 ^ rectRatioK₀ C₀ C_E with hcs
  have hmin : 0 < min (1 / 4) κ := lt_min (by norm_num) hκ
  have hcs0 : 0 < cs := by positivity
  have hL3 : 3 ≤ L := le_max_left _ _
  have hLcs : 1 / cs ≤ L := by rw [hcs, one_div_div]; exact le_max_right _ _
  -- the side-ratio bound for a slice of relative width `≥ cs`
  have hratio : ∀ {s w l : ℝ}, 0 < s → cs * w ≤ s → s ≤ w → l ≤ w → w ≤ 3 * l →
      s ≤ L * l ∧ l ≤ L * s := by
    intro s w l hs hsw hsw' hlw hwl
    have hl : 0 ≤ l := by linarith
    refine ⟨by nlinarith, ?_⟩
    have h1 : w ≤ s / cs := by rw [le_div_iff₀ hcs0]; linarith
    have h2 : s / cs ≤ L * s := by
      rw [div_eq_mul_one_div, mul_comm]; exact mul_le_mul_of_nonneg_right hLcs hs.le
    linarith
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro x₁ x₂ y₁ y₂ hn hQg hQP hQ
  have hQg' := hQg
  obtain ⟨hx, hy, hw3, hl3⟩ := hQg'
  by_cases hnC : n ≤ C₀
  · -- Case B: slice the block into `n` pieces of mass one along its longer side
    have hQC : ν (rect x₁ x₂ y₁ y₂) ≤ C₀ := by rw [hQ]; exact_mod_cast hnC
    obtain ⟨hσκ, hED⟩ := hσ x₁ x₂ y₁ y₂ hQg hQP
    rcases le_or_gt (y₂ - y₁) (x₂ - x₁) with hlw | hlw
    · obtain ⟨t, ht0, htn, htm, htlt, hmass⟩ := rectCore_slice_x hre hx hn hQ
      have hwide : ∀ i < n, cs * (x₂ - x₁) ≤ t (i + 1) - t i := fun i hi ↦
        rectCore_slice_wide hlw hw3 (ht0 ▸ htm (Nat.zero_le i)) (htlt i hi)
          (htn ▸ htm (by omega)) hQC (hmass i hi) fun w hw r hr hrκ ↦ hED w hw r hr (by
            rw [max_eq_left hlw] at hσκ; linarith)
      obtain ⟨hdisj, hunion⟩ := rectCore_slices_x n htm y₁ y₂
      rw [ht0, htn] at hunion
      refine ⟨fun i ↦ (t i, t (i + 1), y₁, y₂), hdisj, hunion, fun i ↦
        ⟨hmass i i.2, ?_, x₁, x₂, y₁, y₂, hQg, hQP, hQC, ?_⟩⟩
      · have hs := htlt i i.2
        have hle : t (i + 1) - t i ≤ x₂ - x₁ := by
          have := htm (Nat.zero_le i); have := htm (show i + 1 ≤ n by omega)
          rw [ht0] at *; rw [htn] at *; linarith
        obtain ⟨h1, h2⟩ := hratio (sub_pos.2 hs) (hwide i i.2) hle hlw hw3
        exact ⟨hs, hy, h1, h2⟩
      · exact rect_subset_rect (ht0 ▸ htm (Nat.zero_le _)) (htn ▸ htm (by omega)) le_rfl le_rfl
    · obtain ⟨t, ht0, htn, htm, htlt, hmass⟩ := rectCore_slice_y him hy hn hQ
      have hwide : ∀ i < n, cs * (y₂ - y₁) ≤ t (i + 1) - t i := fun i hi ↦
        rectCore_slice_wide_y hlw.le hl3 (ht0 ▸ htm (Nat.zero_le i)) (htlt i hi)
          (htn ▸ htm (by omega)) hQC (hmass i hi) fun w hw r hr hrκ ↦ hED w hw r hr (by
            rw [max_eq_right hlw.le] at hσκ; linarith)
      obtain ⟨hdisj, hunion⟩ := rectCore_slices_y n htm x₁ x₂
      rw [ht0, htn] at hunion
      refine ⟨fun i ↦ (x₁, x₂, t i, t (i + 1)), hdisj, hunion, fun i ↦
        ⟨hmass i i.2, ?_, x₁, x₂, y₁, y₂, hQg, hQP, hQC, ?_⟩⟩
      · have hs := htlt i i.2
        have hle : t (i + 1) - t i ≤ y₂ - y₁ := by
          have := htm (Nat.zero_le i); have := htm (show i + 1 ≤ n by omega)
          rw [ht0] at *; rw [htn] at *; linarith
        obtain ⟨h1, h2⟩ := hratio (sub_pos.2 hs) (hwide i i.2) hle hlw.le hl3
        exact ⟨hx, hs, h2, h1⟩
      · exact rect_subset_rect le_rfl le_rfl (ht0 ▸ htm (Nat.zero_le _)) (htn ▸ htm (by omega))
  · -- Case A: bisect through the middle third of the longer side
    push_neg at hnC
    have hmid := hC₀ x₁ x₂ y₁ y₂ hQg hQP (by rw [hQ]; exact_mod_cast hnC)
    rcases le_or_gt (y₂ - y₁) (x₂ - x₁) with hlw | hlw
    · rw [midThird, if_pos hlw] at hmid
      obtain ⟨t, n₁, n₂, ht1, ht2, hn₁, hn₂, hsum, hm₁, hm₂⟩ := rectCore_bisect_x hre hx hQ hmid
      subst hsum
      have h₁ := ih n₁ (by omega) x₁ t y₁ y₂ hn₁
        ⟨by linarith, hy, by linarith, by linarith⟩
        (hP _ _ _ _ _ _ _ _ hQP le_rfl (by linarith) le_rfl le_rfl) hm₁
      have h₂ := ih n₂ (by omega) t x₂ y₁ y₂ hn₂
        ⟨by linarith, hy, by linarith, by linarith⟩
        (hP _ _ _ _ _ _ _ _ hQP (by linarith) le_rfl le_rfl le_rfl) hm₂
      have := rectCore_combine (G := fun p ↦ ν (rect p.1 p.2.1 p.2.2.1 p.2.2.2) = 1 ∧
        IsRectLE L p.1 p.2.1 p.2.2.1 p.2.2.2 ∧ ∃ x₁' x₂' y₁' y₂' : ℝ, IsRectLE 3 x₁' x₂' y₁' y₂' ∧
          P x₁' x₂' y₁' y₂' ∧ ν (rect x₁' x₂' y₁' y₂') ≤ C₀ ∧
          rect p.1 p.2.1 p.2.2.1 p.2.2.2 ⊆ rect x₁' x₂' y₁' y₂')
        h₁ h₂ (rect_disjoint_x le_rfl)
      rwa [rect_union_x (by linarith) (by linarith)] at this
    · rw [midThird, ite_eq_right_iff.mpr (fun h ↦ absurd h (not_le.2 hlw))] at hmid
      obtain ⟨t, n₁, n₂, ht1, ht2, hn₁, hn₂, hsum, hm₁, hm₂⟩ := rectCore_bisect_y him hy hQ hmid
      subst hsum
      have h₁ := ih n₁ (by omega) x₁ x₂ y₁ t hn₁
        ⟨hx, by linarith, by linarith, by linarith⟩
        (hP _ _ _ _ _ _ _ _ hQP le_rfl le_rfl le_rfl (by linarith)) hm₁
      have h₂ := ih n₂ (by omega) x₁ x₂ t y₂ hn₂
        ⟨hx, by linarith, by linarith, by linarith⟩
        (hP _ _ _ _ _ _ _ _ hQP le_rfl le_rfl (by linarith) le_rfl) hm₂
      have := rectCore_combine (G := fun p ↦ ν (rect p.1 p.2.1 p.2.2.1 p.2.2.2) = 1 ∧
        IsRectLE L p.1 p.2.1 p.2.2.1 p.2.2.2 ∧ ∃ x₁' x₂' y₁' y₂' : ℝ, IsRectLE 3 x₁' x₂' y₁' y₂' ∧
          P x₁' x₂' y₁' y₂' ∧ ν (rect x₁' x₂' y₁' y₂') ≤ C₀ ∧
          rect p.1 p.2.1 p.2.2.1 p.2.2.2 ⊆ rect x₁' x₂' y₁' y₂')
        h₁ h₂ (rect_disjoint_y le_rfl)
      rwa [rect_union_y (by linarith) (by linarith)] at this

end OC
