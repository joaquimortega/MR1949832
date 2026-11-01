import OrtegaCerdaMultipliers.Doubling.Abstract

/-!
# M03 (Doubling) — The abstract theory with explicit constants

Helper file for `Doubling/Quant.lean` (M03b).  The statements of `Doubling/Abstract.lean` choose
their constants after the measure; the uniform (`_quant`) versions need constants chosen after the
doubling constant `Cd` only.  Here the basic estimates of `blueprint/M03_Doubling.md` §3.2–3.6 are
proved with *explicit* constants, as functions of a doubling constant `C` valid up to a radius `R`
(`M03b.DoublingUpTo μ C R`), so that uniformity is automatic.

* `M03b.doublingUpTo_of_local`: local doubling with constant `Cd` gives `M03b.DoublingUpTo μ (max
  Cd 1) R`
  for `R < 1/2`;
* `M03b.exists_doublingUpTo` (scale-up, §3.2): `∀ Cd R, ∃ C, ∀ μ` locally doubling with `Cd`,
  `M03b.DoublingUpTo μ C R`;
* `M03b.DoublingUpTo.measure_ball_le_pow`, `.measure_ball_le_rpow` (§3.4);
* `M03b.DoublingUpTo.reverse` (§3.5), `.pow_le_measure_ball` and `.rpow_le_measure_ball` (§3.6).
-/

open MeasureTheory Metric Set
open scoped ENNReal NNReal

noncomputable section

namespace OC

/-- `a ^ (log_b q) = q ^ (log_b a)`. -/
theorem M03b.rpow_logb_swap {b a q : ℝ} (hb : 0 < b) (hb1 : b ≠ 1) (ha : 0 < a) (hq : 0 < q) :
    a ^ Real.logb b q = q ^ Real.logb b a := by
  conv_lhs => rw [← Real.rpow_logb hb hb1 ha]
  conv_rhs => rw [← Real.rpow_logb hb hb1 hq]
  rw [← Real.rpow_mul hb.le, ← Real.rpow_mul hb.le, mul_comm]

section Uniform

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

/-- Doubling with constant `C` at every radius `0 < r ≤ R`. -/
def M03b.DoublingUpTo (μ : Measure X) (C : ℝ≥0) (R : ℝ) : Prop :=
  ∀ x : X, ∀ r : ℝ, 0 < r → r ≤ R → μ (ball x (2 * r)) ≤ C * μ (ball x r)

omit [OpensMeasurableSpace X] in
theorem M03b.DoublingUpTo.mono {μ : Measure X} {C C' : ℝ≥0} {R R' : ℝ} (h : M03b.DoublingUpTo μ C R)
    (hC : C ≤ C') (hR : R' ≤ R) : M03b.DoublingUpTo μ C' R' := fun x r hr hrR ↦
  (h x r hr (hrR.trans hR)).trans (by gcongr)

omit [OpensMeasurableSpace X] in
/-- Local doubling with constant `Cd` gives doubling with `max Cd 1` up to any radius `< 1/2`. -/
theorem M03b.doublingUpTo_of_local {μ : Measure X} {Cd : ℝ≥0}
    (hμ : ∀ x : X, ∀ r : ℝ, 0 < r → 2 * r < 1 → μ (ball x (2 * r)) ≤ Cd * μ (ball x r))
    {R : ℝ} (hR : R < 1 / 2) : M03b.DoublingUpTo μ (max Cd 1) R := fun x r hr hrR ↦
  (hμ x r hr (by linarith)).trans (by gcongr; exact le_max_left _ _)

omit [OpensMeasurableSpace X] in
/-- Chain lemma (§3.2): if `d(x,y) ≤ nδ` then `μ(B(y,δ)) ≤ Cⁿ μ(B(x,δ))`. -/
theorem M03b.DoublingUpTo.chain [BallGeometry X] {μ : Measure X} {C : ℝ≥0} {δ : ℝ}
    (h : M03b.DoublingUpTo μ C δ) (hC : 1 ≤ C) (hδ : 0 < δ) :
    ∀ n : ℕ, ∀ x y : X, dist x y ≤ n * δ → μ (ball y δ) ≤ C ^ n * μ (ball x δ) := by
  have step : ∀ x y : X, dist x y ≤ δ → μ (ball y δ) ≤ C * μ (ball x δ) := by
    intro x y hxy
    refine (measure_mono fun w hw ↦ ?_).trans (h x δ hδ le_rfl)
    rw [mem_ball] at hw ⊢
    calc dist w x ≤ dist w y + dist y x := dist_triangle _ _ _
      _ < δ + δ := add_lt_add_of_lt_of_le hw (by rwa [dist_comm])
      _ = 2 * δ := by ring
  intro n
  induction n with
  | zero =>
    intro x y hxy
    have : x = y := dist_le_zero.1 (by simpa using hxy)
    subst this
    simp
  | succ n ih =>
    intro x y hxy
    by_cases hc : dist x y ≤ δ
    · refine (step x y hc).trans ?_
      gcongr
      exact le_self_pow₀ (by exact_mod_cast hC) (Nat.succ_ne_zero n)
    · obtain ⟨m, hxm, hmy⟩ := BallGeometry.exists_between x y δ hδ.le (not_le.1 hc).le
      have h1 := ih m y (by push_cast at hxy; linarith)
      have h2 := step x m hxm
      calc μ (ball y δ) ≤ C ^ n * μ (ball m δ) := h1
        _ ≤ C ^ n * (C * μ (ball x δ)) := by gcongr
        _ = C ^ (n + 1) * μ (ball x δ) := by rw [← mul_assoc, pow_succ]

omit [OpensMeasurableSpace X] in
/-- **Scale-up** (§3.2), uniform: the constant depends only on `Cd` and `R`. -/
theorem M03b.exists_doublingUpTo [BallGeometry X] (Cd : ℝ≥0) (R : ℝ) :
    ∃ C : ℝ≥0, 1 ≤ C ∧ ∀ μ : Measure X,
      (∀ x : X, ∀ r : ℝ, 0 < r → 2 * r < 1 → μ (ball x (2 * r)) ≤ Cd * μ (ball x r)) →
      M03b.DoublingUpTo μ C R := by
  obtain ⟨K, hK⟩ := BallGeometry.covering (X := X) (2 * R) (1 / 4) (by norm_num)
  set C₀ : ℝ≥0 := max Cd 1 with hC₀
  have hC₀1 : 1 ≤ C₀ := le_max_right _ _
  set n₀ : ℕ := ⌈8 * R + 1⌉₊ with hn₀
  refine ⟨max C₀ (K * C₀ ^ n₀), le_trans hC₀1 (le_max_left _ _), fun μ hμ x r hr hrR ↦ ?_⟩
  by_cases h2r : 2 * r < 1
  · exact (hμ x r hr h2r).trans (by gcongr; exact (le_max_left _ _).trans (le_max_left _ _))
  have hr2 : 1 / 2 ≤ r := by linarith [not_lt.1 h2r]
  have hloc : M03b.DoublingUpTo μ C₀ (1 / 4) := M03b.doublingUpTo_of_local hμ (by norm_num)
  obtain ⟨s, hs, hcov⟩ := hK x
  have hsub : ball x (2 * r) ⊆ ⋃ y ∈ s, (ball y (1 / 4) ∩ ball x (2 * r)) := by
    intro w hw
    have hw' : w ∈ ball x (2 * R) := ball_subset_ball (by linarith) hw
    obtain ⟨y, hy, hwy⟩ := mem_iUnion₂.1 (hcov hw')
    exact mem_iUnion₂.2 ⟨y, hy, hwy, hw⟩
  have hterm : ∀ y ∈ s, μ (ball y (1 / 4) ∩ ball x (2 * r)) ≤ C₀ ^ n₀ * μ (ball x r) := by
    intro y _
    rcases (ball y (1 / 4) ∩ ball x (2 * r)).eq_empty_or_nonempty with he | ⟨w, hwy, hwx⟩
    · rw [he, measure_empty]; positivity
    have hxy : dist x y ≤ n₀ * (1 / 4) := by
      rw [mem_ball] at hwy hwx
      have h1 : (8 * R + 1 : ℝ) ≤ n₀ := Nat.le_ceil _
      calc dist x y ≤ dist x w + dist w y := dist_triangle _ _ _
        _ ≤ 2 * r + 1 / 4 := by rw [dist_comm]; linarith
        _ ≤ n₀ * (1 / 4) := by linarith
    calc μ (ball y (1 / 4) ∩ ball x (2 * r)) ≤ μ (ball y (1 / 4)) := measure_mono inter_subset_left
      _ ≤ C₀ ^ n₀ * μ (ball x (1 / 4)) :=
          hloc.chain hC₀1 (by norm_num) n₀ x y hxy
      _ ≤ C₀ ^ n₀ * μ (ball x r) := by gcongr; linarith
  calc μ (ball x (2 * r)) ≤ μ (⋃ y ∈ s, (ball y (1 / 4) ∩ ball x (2 * r))) := measure_mono hsub
    _ ≤ ∑ y ∈ s, μ (ball y (1 / 4) ∩ ball x (2 * r)) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _y ∈ s, (C₀ ^ n₀ : ℝ≥0∞) * μ (ball x r) := Finset.sum_le_sum hterm
    _ = (s.card : ℝ≥0∞) * (C₀ ^ n₀ * μ (ball x r)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (K : ℝ≥0∞) * (C₀ ^ n₀ * μ (ball x r)) := by gcongr
    _ = ((K * C₀ ^ n₀ : ℝ≥0) : ℝ≥0∞) * μ (ball x r) := by push_cast; ring
    _ ≤ ((max C₀ (K * C₀ ^ n₀) : ℝ≥0) : ℝ≥0∞) * μ (ball x r) := by
        gcongr; exact le_max_right _ _

omit [OpensMeasurableSpace X] in
/-- Iterated doubling: `μ(B(x, 2ʲρ)) ≤ Cʲ μ(B(x,ρ))` if `2ʲρ ≤ 2R`. -/
theorem M03b.DoublingUpTo.pow {μ : Measure X} {C : ℝ≥0} {R : ℝ} (h : M03b.DoublingUpTo μ C R)
    (x : X) {ρ : ℝ} (hρ : 0 < ρ) :
    ∀ j : ℕ, 2 ^ j * ρ ≤ 2 * R → μ (ball x (2 ^ j * ρ)) ≤ C ^ j * μ (ball x ρ) := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
    intro hj
    have hj' : 2 ^ j * ρ ≤ R := by rw [pow_succ] at hj; linarith
    have hpos : 0 < 2 ^ j * ρ := by positivity
    calc μ (ball x (2 ^ (j + 1) * ρ)) = μ (ball x (2 * (2 ^ j * ρ))) := by
          rw [pow_succ]; ring_nf
      _ ≤ C * μ (ball x (2 ^ j * ρ)) := h x _ hpos hj'
      _ ≤ C * (C ^ j * μ (ball x ρ)) := by gcongr; exact ih (by linarith)
      _ = C ^ (j + 1) * μ (ball x ρ) := by rw [← mul_assoc, pow_succ]; ring

omit [OpensMeasurableSpace X] in
/-- Lemma 1, upper inequality, `ℕ` form (§3.4). -/
theorem M03b.DoublingUpTo.measure_ball_le_pow {μ : Measure X} {C : ℝ≥0} {R : ℝ}
    (h : M03b.DoublingUpTo μ C R) (x x' : X) {r r' : ℝ} (k : ℕ) (_hr' : 0 < r') (hrR : r ≤ R)
    (hxx' : dist x x' ≤ r) (hrk : r ≤ 2 ^ k * r') :
    μ (ball x r) ≤ C ^ (k + 1) * μ (ball x' r') := by
  rcases le_or_gt r 0 with hr | hr
  · rw [ball_eq_empty.2 hr, measure_empty]; positivity
  set ρ := r / 2 ^ k with hρ
  have hρpos : 0 < ρ := by positivity
  have hρr' : ρ ≤ r' := by rw [hρ, div_le_iff₀ (by positivity)]; linarith
  have h2 : 2 ^ (k + 1) * ρ = 2 * r := by rw [hρ, pow_succ]; field_simp
  calc μ (ball x r) ≤ μ (ball x' (2 * r)) := measure_mono fun w hw ↦ by
        rw [mem_ball] at hw ⊢
        linarith [dist_triangle w x x']
    _ = μ (ball x' (2 ^ (k + 1) * ρ)) := by rw [h2]
    _ ≤ C ^ (k + 1) * μ (ball x' ρ) := h.pow x' hρpos (k + 1) (by rw [h2]; linarith)
    _ ≤ C ^ (k + 1) * μ (ball x' r') := by gcongr

omit [OpensMeasurableSpace X] in
/-- Lemma 1, upper inequality, power form (§3.4): constant `C²`, exponent `log₂ C`. -/
theorem M03b.DoublingUpTo.measure_ball_le_rpow {μ : Measure X} {C : ℝ≥0} {R : ℝ}
    (h : M03b.DoublingUpTo μ C R) (hC : 1 ≤ C) (x x' : X) {r r' : ℝ} (hr' : 0 < r') (hrr : r' ≤ r)
    (hrR : r ≤ R) (hxx' : dist x x' ≤ r) :
    μ (ball x r) ≤ ENNReal.ofReal ((C : ℝ) ^ 2 * (r / r') ^ Real.logb 2 C) *
      μ (ball x' r') := by
  set q := r / r' with hq
  have hq1 : 1 ≤ q := by rw [hq, le_div_iff₀ hr']; linarith
  have hq0 : 0 < q := by linarith
  have hlog : 0 ≤ Real.logb 2 q := Real.logb_nonneg (by norm_num) hq1
  set k := ⌈Real.logb 2 q⌉₊ with hk
  have hrk : r ≤ 2 ^ k * r' := by
    have h1 : q ≤ (2 : ℝ) ^ k := by
      calc q = (2 : ℝ) ^ Real.logb 2 q := (Real.rpow_logb (by norm_num) (by norm_num) hq0).symm
        _ ≤ (2 : ℝ) ^ (k : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.le_ceil _)
        _ = 2 ^ k := Real.rpow_natCast _ _
    rw [hq, div_le_iff₀ hr'] at h1
    linarith
  have key := h.measure_ball_le_pow x x' k hr' hrR hxx' hrk
  have hreal : ((C : ℝ)) ^ (k + 1) ≤ (C : ℝ) ^ 2 * q ^ Real.logb 2 C := by
    have hC1 : (1 : ℝ) ≤ C := by exact_mod_cast hC
    have hkl : (k : ℝ) + 1 ≤ Real.logb 2 q + 2 := by
      have := Nat.ceil_lt_add_one hlog
      rw [← hk] at this
      linarith
    calc ((C : ℝ)) ^ (k + 1) = (C : ℝ) ^ ((k : ℝ) + 1) := by
          rw [← Real.rpow_natCast]; push_cast; ring_nf
      _ ≤ (C : ℝ) ^ (Real.logb 2 q + 2) := Real.rpow_le_rpow_of_exponent_le hC1 hkl
      _ = (C : ℝ) ^ 2 * q ^ Real.logb 2 C := by
          rw [Real.rpow_add (by linarith), M03b.rpow_logb_swap (by norm_num) (by norm_num)
            (by linarith) hq0, Real.rpow_two, mul_comm]
  refine key.trans ?_
  calc (C : ℝ≥0∞) ^ (k + 1) * μ (ball x' r')
      = ENNReal.ofReal ((C : ℝ) ^ (k + 1)) * μ (ball x' r') := by
        rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_coe_nnreal]
    _ ≤ _ := by gcongr

/-- Reverse doubling (§3.5), explicit: `η = C⁻³`. -/
theorem M03b.DoublingUpTo.reverse [BallGeometry X] {μ : Measure X} {C : ℝ≥0} {R : ℝ}
    (h : M03b.DoublingUpTo μ C (2 * R)) (hC : 1 ≤ C) (x : X) {t : ℝ} (ht : 0 < t) (htR : t ≤ R) :
    (1 + ((C ^ 3)⁻¹ : ℝ≥0) : ℝ≥0∞) * μ (ball x t) ≤ μ (ball x (2 * t)) := by
  obtain ⟨y, hy⟩ := exists_dist_eq x (r := 3 * t / 2) (by positivity)
  have hdisj : Disjoint (ball x t) (ball y (t / 2)) := by
    refine Set.disjoint_left.2 fun w hwx hwy ↦ ?_
    rw [mem_ball] at hwx hwy
    have := dist_triangle x w y
    rw [dist_comm x w] at this
    linarith
  have hsub : ball x t ∪ ball y (t / 2) ⊆ ball x (2 * t) := by
    rintro w (hw | hw) <;> rw [mem_ball] at hw ⊢
    · linarith
    · have := dist_triangle w y x
      rw [dist_comm y x] at this
      linarith
  have hxy : μ (ball x t) ≤ C ^ 3 * μ (ball y (t / 2)) := by
    have h8 : (2 : ℝ) ^ 3 * (t / 2) = 4 * t := by ring
    calc μ (ball x t) ≤ μ (ball y (2 ^ 3 * (t / 2))) := measure_mono fun w hw ↦ by
          rw [mem_ball] at hw ⊢
          rw [h8]
          have := dist_triangle w x y
          linarith
      _ ≤ C ^ 3 * μ (ball y (t / 2)) := by
          have := h.pow y (by positivity : 0 < t / 2) 3 (by rw [h8]; linarith)
          exact_mod_cast this
  have hC3 : (C ^ 3 : ℝ≥0) ≠ 0 := pow_ne_zero _ (by positivity)
  have hη : (((C ^ 3)⁻¹ : ℝ≥0) : ℝ≥0∞) * μ (ball x t) ≤ μ (ball y (t / 2)) := by
    calc (((C ^ 3)⁻¹ : ℝ≥0) : ℝ≥0∞) * μ (ball x t)
        ≤ (((C ^ 3)⁻¹ : ℝ≥0) : ℝ≥0∞) * ((C ^ 3 : ℝ≥0) * μ (ball y (t / 2))) := by
          gcongr; exact_mod_cast hxy
      _ = μ (ball y (t / 2)) := by
          rw [← mul_assoc, ← ENNReal.coe_mul, inv_mul_cancel₀ hC3, ENNReal.coe_one, one_mul]
  calc (1 + ((C ^ 3)⁻¹ : ℝ≥0) : ℝ≥0∞) * μ (ball x t)
      = μ (ball x t) + (((C ^ 3)⁻¹ : ℝ≥0) : ℝ≥0∞) * μ (ball x t) := by ring
    _ ≤ μ (ball x t) + μ (ball y (t / 2)) := by gcongr
    _ = μ (ball x t ∪ ball y (t / 2)) := (measure_union hdisj measurableSet_ball).symm
    _ ≤ μ (ball x (2 * t)) := measure_mono hsub

/-- Iterated reverse doubling: `(1+η)ᵏ μ(B(x,ρ)) ≤ μ(B(x,2ᵏρ))` if `2ᵏρ ≤ 2R`. -/
theorem M03b.DoublingUpTo.reverse_pow [BallGeometry X] {μ : Measure X} {C : ℝ≥0} {R : ℝ}
    (h : M03b.DoublingUpTo μ C (2 * R)) (hC : 1 ≤ C) (x : X) {ρ : ℝ} (hρ : 0 < ρ) :
    ∀ k : ℕ, 2 ^ k * ρ ≤ 2 * R →
      (1 + ((C ^ 3)⁻¹ : ℝ≥0) : ℝ≥0∞) ^ k * μ (ball x ρ) ≤ μ (ball x (2 ^ k * ρ)) := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    have hk' : 2 ^ k * ρ ≤ R := by rw [pow_succ] at hk; linarith
    have hpos : 0 < 2 ^ k * ρ := by positivity
    calc (1 + ((C ^ 3)⁻¹ : ℝ≥0) : ℝ≥0∞) ^ (k + 1) * μ (ball x ρ)
        = (1 + ((C ^ 3)⁻¹ : ℝ≥0) : ℝ≥0∞) *
            ((1 + ((C ^ 3)⁻¹ : ℝ≥0) : ℝ≥0∞) ^ k * μ (ball x ρ)) := by ring
      _ ≤ (1 + ((C ^ 3)⁻¹ : ℝ≥0) : ℝ≥0∞) * μ (ball x (2 ^ k * ρ)) := by
          gcongr; exact ih (by linarith)
      _ ≤ μ (ball x (2 * (2 ^ k * ρ))) := h.reverse hC x (by positivity) hk'
      _ = μ (ball x (2 ^ (k + 1) * ρ)) := by rw [pow_succ]; ring_nf

/-- Lemma 1, lower inequality, power form (§3.6), explicit: with `η = C⁻³`,
`δ = log₂(1+η)` and `c = 1/(C(1+η))`. -/
theorem M03b.DoublingUpTo.rpow_le_measure_ball [BallGeometry X] {μ : Measure X} {C : ℝ≥0} {R : ℝ}
    (h : M03b.DoublingUpTo μ C (2 * R)) (hC : 1 ≤ C) (x x' : X) {r r' : ℝ} (hr' : 0 < r')
    (hrr : r' ≤ r) (hrR : r ≤ R) (hxx' : dist x x' ≤ r) :
    ENNReal.ofReal (1 / ((C : ℝ) * (1 + ((C : ℝ) ^ 3)⁻¹)) *
        (r / r') ^ Real.logb 2 (1 + ((C : ℝ) ^ 3)⁻¹)) * μ (ball x' r') ≤ μ (ball x r) := by
  set η : ℝ≥0 := (C ^ 3)⁻¹ with hη
  have hηr : ((η : ℝ)) = ((C : ℝ) ^ 3)⁻¹ := by rw [hη]; push_cast; ring
  rw [← hηr]
  set q := r / r' with hq
  have hq1 : 1 ≤ q := by rw [hq, le_div_iff₀ hr']; linarith
  have hq0 : 0 < q := by linarith
  have hlog : 0 ≤ Real.logb 2 q := Real.logb_nonneg (by norm_num) hq1
  set k := ⌊Real.logb 2 q⌋₊ with hk
  have hkr : 2 ^ k * r' ≤ r := by
    have h1 : (2 : ℝ) ^ k ≤ q := by
      calc (2 : ℝ) ^ k = (2 : ℝ) ^ (k : ℝ) := (Real.rpow_natCast _ _).symm
        _ ≤ (2 : ℝ) ^ Real.logb 2 q :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.floor_le hlog)
        _ = q := Real.rpow_logb (by norm_num) (by norm_num) hq0
    rw [hq, le_div_iff₀ hr'] at h1
    linarith
  have hR0 : 0 ≤ R := by linarith
  have h1 := h.reverse_pow hC x' hr' k (by linarith)
  have h2 : μ (ball x' (2 ^ k * r')) ≤ C * μ (ball x r) := by
    calc μ (ball x' (2 ^ k * r')) ≤ μ (ball x (2 * r)) := measure_mono fun w hw ↦ by
          rw [mem_ball] at hw ⊢
          linarith [dist_triangle w x' x, dist_comm x x']
      _ ≤ C * μ (ball x r) := h x r (by linarith) (by linarith)
  have hC0 : (0 : ℝ) < C := by exact_mod_cast (zero_lt_one.trans_le hC)
  have hη0 : (0 : ℝ) ≤ η := η.2
  -- `c q^δ ≤ (1+η)^k / C`
  have hreal : 1 / ((C : ℝ) * (1 + η)) * q ^ Real.logb 2 (1 + η) ≤ (1 + (η : ℝ)) ^ k / C := by
    have hk1 : Real.logb 2 q - 1 ≤ k := by
      have := Nat.lt_floor_add_one (Real.logb 2 q)
      rw [← hk] at this
      linarith
    have hpow : q ^ Real.logb 2 (1 + η) / (1 + η) ≤ (1 + (η : ℝ)) ^ k := by
      calc q ^ Real.logb 2 (1 + η) / (1 + η) = (1 + (η : ℝ)) ^ (Real.logb 2 q - 1) := by
            rw [Real.rpow_sub (by positivity), Real.rpow_one,
              M03b.rpow_logb_swap (by norm_num) (by norm_num) (by positivity) hq0]
        _ ≤ (1 + (η : ℝ)) ^ (k : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith) hk1
        _ = (1 + (η : ℝ)) ^ k := Real.rpow_natCast _ _
    calc 1 / ((C : ℝ) * (1 + η)) * q ^ Real.logb 2 (1 + η)
        = (q ^ Real.logb 2 (1 + η) / (1 + η)) / C := by field_simp
      _ ≤ (1 + (η : ℝ)) ^ k / C := by gcongr
  calc ENNReal.ofReal (1 / ((C : ℝ) * (1 + η)) * q ^ Real.logb 2 (1 + η)) * μ (ball x' r')
      ≤ ENNReal.ofReal ((1 + (η : ℝ)) ^ k / C) * μ (ball x' r') := by gcongr
    _ = (C⁻¹ : ℝ≥0) * ((1 + (η : ℝ≥0∞)) ^ k * μ (ball x' r')) := by
        rw [← mul_assoc]
        congr 1
        rw [div_eq_inv_mul, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity),
          ENNReal.ofReal_add zero_le_one hη0, ENNReal.ofReal_one, ENNReal.ofReal_coe_nnreal,
          ← NNReal.coe_inv, ENNReal.ofReal_coe_nnreal]
    _ ≤ (C⁻¹ : ℝ≥0) * μ (ball x' (2 ^ k * r')) := by gcongr
    _ ≤ (C⁻¹ : ℝ≥0) * (C * μ (ball x r)) := by gcongr
    _ = μ (ball x r) := by
        rw [← mul_assoc, ← ENNReal.coe_mul, inv_mul_cancel₀ (by positivity), ENNReal.coe_one,
          one_mul]

end Uniform

end OC
