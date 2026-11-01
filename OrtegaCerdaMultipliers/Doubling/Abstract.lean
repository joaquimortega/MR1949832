import OrtegaCerdaMultipliers.Defs

/-!
# M03 (Doubling) — Locally doubling measures on a metric space

See `blueprint/M03_Doubling.md` §2.1.  Scaffold: statements, proofs `sorry`; definitions are real.

The whole theory of §2 of the paper on an abstract metric space `X` with `BallGeometry`:
`IsLocDoublingM`, `BallGeometry`, `IsPorous`, `massRadiusM`, scale-up, Lemma 1, Lemma 2 (porous
sets are null), the mass radius, Claim 1, Lemma 3, [Chr91, Lemma 2.3], growth, decay, bounded
count.
-/

open MeasureTheory Metric Set Complex
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

set_option linter.unusedSectionVars false

namespace OC

section Abstract

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

/-- Local doubling on a metric space at scales `< 1`. -/
def IsLocDoublingM (μ : Measure X) : Prop :=
  ∃ C : ℝ≥0, ∀ x : X, ∀ r : ℝ, 0 < r → 2 * r < 1 → μ (ball x (2 * r)) ≤ C * μ (ball x r)

/-- Mass radius in a metric space: `ρ(x) = inf {r > 0 : μ(B(x,r)) ≥ 1}`. -/
def massRadiusM (μ : Measure X) (x : X) : ℝ :=
  sInf {r : ℝ | 0 < r ∧ 1 ≤ μ (ball x r)}

/-- Geometric hypotheses of §2 (satisfied by `ℂ`, `ℝ`, `HDisc`). -/
class BallGeometry (X : Type*) [MetricSpace X] : Prop where
  exists_between : ∀ (x y : X) (s : ℝ), 0 ≤ s → s ≤ dist x y →
    ∃ m, dist x m ≤ s ∧ dist m y ≤ dist x y - s
  exists_far : ∀ (x : X) (r : ℝ), ∃ y, r ≤ dist x y
  covering : ∀ R ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ x : X, ∃ s : Finset X, s.card ≤ K ∧
    ball x R ⊆ ⋃ y ∈ s, ball y ε

/-- Porosity (uniform, at scales `≤ s₀`, ratio `κ`). -/
def IsPorous (E : Set X) : Prop :=
  ∃ κ s₀ : ℝ, 0 < κ ∧ 0 < s₀ ∧ ∀ y ∈ E, ∀ s : ℝ, 0 < s → s ≤ s₀ →
    ∃ y', dist y y' ≤ s ∧ ∀ e ∈ E, κ * s ≤ dist y' e

theorem exists_dist_eq [BallGeometry X] (x : X) {r : ℝ} (hr : 0 ≤ r) : ∃ y, dist x y = r := by
  obtain ⟨y, hy⟩ := BallGeometry.exists_far x r
  obtain ⟨m, hm1, hm2⟩ := BallGeometry.exists_between x y r hr hy
  refine ⟨m, le_antisymm hm1 ?_⟩
  have := dist_triangle x m y
  linarith

/-- Local doubling with a constant `≥ 1` at base radii `≤ 1/4`. -/
theorem IsLocDoublingM.exists_const_quarter {μ : Measure X} (hd : IsLocDoublingM μ) :
    ∃ C : ℝ≥0, 1 ≤ C ∧ ∀ x : X, ∀ r : ℝ, 0 < r → r ≤ 1 / 4 →
      μ (ball x (2 * r)) ≤ C * μ (ball x r) := by
  obtain ⟨C, hC⟩ := hd
  refine ⟨max C 1, le_max_right _ _, fun x r hr hr4 ↦ ?_⟩
  calc μ (ball x (2 * r)) ≤ C * μ (ball x r) := hC x r hr (by linarith)
    _ ≤ (max C 1 : ℝ≥0) * μ (ball x r) := by gcongr; exact_mod_cast le_max_left _ _

/-- Chain lemma: if `d(x,y) ≤ n δ` with `2δ < 1`, then `μ B(y,δ) ≤ Cⁿ μ B(x,δ)`. -/
theorem chain_aux [BallGeometry X] {μ : Measure X} {C : ℝ≥0} (hC1 : 1 ≤ C) {δ : ℝ}
    (hδ : 0 < δ) (hC : ∀ x : X, μ (ball x (2 * δ)) ≤ C * μ (ball x δ)) :
    ∀ n : ℕ, ∀ x y : X, dist x y ≤ n * δ → μ (ball y δ) ≤ (C : ℝ≥0∞) ^ n * μ (ball x δ) := by
  intro n
  induction n with
  | zero =>
    intro x y h
    have h0 : dist x y = 0 := le_antisymm (by simpa using h) dist_nonneg
    rw [dist_eq_zero] at h0
    subst h0
    simp
  | succ n ih =>
    intro x y h
    have hC1' : (1 : ℝ≥0∞) ≤ C := by exact_mod_cast hC1
    by_cases hxy : dist x y ≤ δ
    · have hsub : ball y δ ⊆ ball x (2 * δ) := by
        intro z hz
        rw [mem_ball] at hz ⊢
        have := dist_triangle z y x
        rw [dist_comm y x] at this
        linarith
      calc μ (ball y δ) ≤ μ (ball x (2 * δ)) := measure_mono hsub
        _ ≤ C * μ (ball x δ) := hC x
        _ ≤ (C : ℝ≥0∞) ^ (n + 1) * μ (ball x δ) := by
          gcongr
          calc (C : ℝ≥0∞) = C ^ 1 := (pow_one _).symm
            _ ≤ C ^ (n + 1) := pow_le_pow_right₀ hC1' (by omega)
    · rw [not_le] at hxy
      obtain ⟨m, hm1, hm2⟩ := BallGeometry.exists_between x y δ hδ.le hxy.le
      have hmy : dist m y ≤ n * δ := by push_cast at h; linarith
      have hsub : ball m δ ⊆ ball x (2 * δ) := by
        intro z hz
        rw [mem_ball] at hz ⊢
        have := dist_triangle z m x
        rw [dist_comm m x] at this
        linarith
      calc μ (ball y δ) ≤ (C : ℝ≥0∞) ^ n * μ (ball m δ) := ih m y hmy
        _ ≤ (C : ℝ≥0∞) ^ n * (C * μ (ball x δ)) := by
          gcongr
          exact (measure_mono hsub).trans (hC x)
        _ = (C : ℝ≥0∞) ^ (n + 1) * μ (ball x δ) := by ring

theorem IsLocDoublingM.exists_const_of_le [BallGeometry X] {μ : Measure X}
    (hd : IsLocDoublingM μ) (R₁ : ℝ) :
    ∃ C : ℝ≥0, 1 ≤ C ∧ ∀ x : X, ∀ r : ℝ, 0 < r → r ≤ R₁ →
      μ (ball x (2 * r)) ≤ C * μ (ball x r) := by
  obtain ⟨C, hC1, hC⟩ := hd.exists_const_quarter
  obtain ⟨K, hK⟩ := BallGeometry.covering (X := X) (2 * R₁) (1 / 4) (by norm_num)
  set n₀ : ℕ := ⌈8 * R₁ + 1⌉₊ with hn₀
  refine ⟨max C (K * C ^ n₀), le_max_of_le_left hC1, fun x r hr hrR ↦ ?_⟩
  by_cases h4 : r ≤ 1 / 4
  · calc μ (ball x (2 * r)) ≤ C * μ (ball x r) := hC x r hr h4
      _ ≤ (max C (K * C ^ n₀) : ℝ≥0) * μ (ball x r) := by
        gcongr; exact_mod_cast le_max_left _ _
  rw [not_le] at h4
  obtain ⟨s, hs, hcov⟩ := hK x
  have hchain := chain_aux hC1 (δ := 1 / 4) (by norm_num)
    (fun y ↦ hC y (1 / 4) (by norm_num) le_rfl)
  have hsub : ball x (2 * r) ⊆ ⋃ y ∈ s, (ball y (1 / 4) ∩ ball x (2 * r)) := by
    intro z hz
    have : z ∈ ball x (2 * R₁) := ball_subset_ball (by linarith) hz
    obtain ⟨y, hy, hzy⟩ := mem_iUnion₂.1 (hcov this)
    exact mem_iUnion₂.2 ⟨y, hy, hzy, hz⟩
  have hterm : ∀ y ∈ s, μ (ball y (1 / 4) ∩ ball x (2 * r)) ≤
      (C : ℝ≥0∞) ^ n₀ * μ (ball x r) := by
    intro y _
    rcases (ball y (1 / 4) ∩ ball x (2 * r)).eq_empty_or_nonempty with he | ⟨z, hz1, hz2⟩
    · rw [he]; simp
    · have hdist : dist x y ≤ n₀ * (1 / 4) := by
        rw [mem_ball] at hz1 hz2
        have h1 := dist_triangle x z y
        rw [dist_comm x z] at h1
        have h2 : (8 * R₁ + 1 : ℝ) ≤ n₀ := Nat.le_ceil _
        linarith
      calc μ (ball y (1 / 4) ∩ ball x (2 * r)) ≤ μ (ball y (1 / 4)) :=
            measure_mono inter_subset_left
        _ ≤ (C : ℝ≥0∞) ^ n₀ * μ (ball x (1 / 4)) := hchain n₀ x y hdist
        _ ≤ (C : ℝ≥0∞) ^ n₀ * μ (ball x r) := by
          gcongr
  calc μ (ball x (2 * r)) ≤ μ (⋃ y ∈ s, (ball y (1 / 4) ∩ ball x (2 * r))) := measure_mono hsub
    _ ≤ ∑ y ∈ s, μ (ball y (1 / 4) ∩ ball x (2 * r)) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _y ∈ s, (C : ℝ≥0∞) ^ n₀ * μ (ball x r) := Finset.sum_le_sum hterm
    _ = s.card * ((C : ℝ≥0∞) ^ n₀ * μ (ball x r)) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ K * ((C : ℝ≥0∞) ^ n₀ * μ (ball x r)) := by gcongr
    _ = ((K * C ^ n₀ : ℝ≥0) : ℝ≥0∞) * μ (ball x r) := by push_cast; ring
    _ ≤ (max C (K * C ^ n₀) : ℝ≥0) * μ (ball x r) := by
        gcongr; exact_mod_cast le_max_right _ _

/-- Iterated doubling: `u ≤ 2ⁿ t`, `u ≤ 2R₁` ⟹ `μ B(x,u) ≤ Dⁿ μ B(x,t)`. -/
theorem measure_ball_le_pow_aux {μ : Measure X} {D : ℝ≥0} (hD1 : 1 ≤ D) {R₁ : ℝ}
    (hD : ∀ x : X, ∀ r : ℝ, 0 < r → r ≤ R₁ → μ (ball x (2 * r)) ≤ D * μ (ball x r)) :
    ∀ n : ℕ, ∀ (x : X) (t u : ℝ), 0 < t → u ≤ 2 ^ n * t → u ≤ 2 * R₁ →
      μ (ball x u) ≤ (D : ℝ≥0∞) ^ n * μ (ball x t) := by
  intro n
  induction n with
  | zero =>
    intro x t u _ hu _
    simp only [pow_zero, one_mul] at hu ⊢
    exact measure_mono (ball_subset_ball hu)
  | succ n ih =>
    intro x t u ht hu hu2
    have hD1' : (1 : ℝ≥0∞) ≤ D := by exact_mod_cast hD1
    by_cases hun : u ≤ 2 ^ n * t
    · calc μ (ball x u) ≤ (D : ℝ≥0∞) ^ n * μ (ball x t) := ih x t u ht hun hu2
        _ ≤ (D : ℝ≥0∞) ^ (n + 1) * μ (ball x t) :=
          mul_le_mul_left (pow_le_pow_right₀ hD1' (Nat.le_succ n)) _
    · rw [not_le] at hun
      have h2n : (0 : ℝ) < 2 ^ n * t := by positivity
      have hupos : 0 < u := h2n.trans hun
      have h1 := hD x (u / 2) (by linarith) (by linarith)
      rw [show 2 * (u / 2) = u by ring] at h1
      have hpow : (2 : ℝ) ^ (n + 1) * t = 2 * (2 ^ n * t) := by ring
      have h2 := ih x t (u / 2) ht (by rw [hpow] at hu; linarith) (by linarith)
      calc μ (ball x u) ≤ D * μ (ball x (u / 2)) := h1
        _ ≤ D * ((D : ℝ≥0∞) ^ n * μ (ball x t)) := by gcongr
        _ = (D : ℝ≥0∞) ^ (n + 1) * μ (ball x t) := by ring

theorem IsLocDoublingM.measure_ball_le_of_dist_le [BallGeometry X] {μ : Measure X}
    (hd : IsLocDoublingM μ) (R₁ : ℝ) :
    ∃ C : ℝ≥0, ∀ x y : X, ∀ r : ℝ, 0 < r → r ≤ R₁ → dist x y ≤ r →
      μ (ball y r) ≤ C * μ (ball x r) := by
  obtain ⟨C, _, hC⟩ := hd.exists_const_of_le R₁
  refine ⟨C, fun x y r hr hrR hxy ↦ ?_⟩
  have hsub : ball y r ⊆ ball x (2 * r) := by
    intro z hz
    rw [mem_ball] at hz ⊢
    have := dist_triangle z y x
    rw [dist_comm y x] at this
    linarith
  exact (measure_mono hsub).trans (hC x r hr hrR)

theorem IsLocDoublingM.measure_ball_le_pow [BallGeometry X] {μ : Measure X}
    (hd : IsLocDoublingM μ) (R₁ : ℝ) :
    ∃ C : ℝ≥0, 1 ≤ C ∧ ∀ (x x' : X) (r r' : ℝ) (k : ℕ), 0 < r' → r ≤ R₁ → dist x x' ≤ r →
      r ≤ 2 ^ k * r' → μ (ball x r) ≤ C ^ (k + 1) * μ (ball x' r') := by
  obtain ⟨D, hD1, hD⟩ := hd.exists_const_of_le R₁
  refine ⟨D, hD1, fun x x' r r' k hr' hrR hxx' hrk ↦ ?_⟩
  have hsub : ball x r ⊆ ball x' (2 * r) := by
    intro z hz
    rw [mem_ball] at hz ⊢
    have := dist_triangle z x x'
    linarith
  have hpow : (2 : ℝ) ^ (k + 1) * r' = 2 * (2 ^ k * r') := by ring
  calc μ (ball x r) ≤ μ (ball x' (2 * r)) := measure_mono hsub
    _ ≤ (D : ℝ≥0∞) ^ (k + 1) * μ (ball x' r') :=
      measure_ball_le_pow_aux hD1 hD (k + 1) x' r' (2 * r) hr' (by rw [hpow]; linarith)
        (by linarith)

theorem IsLocDoublingM.reverse_doubling [BallGeometry X] {μ : Measure X}
    (hd : IsLocDoublingM μ) (R₁ : ℝ) :
    ∃ η : ℝ≥0, 0 < η ∧ ∀ x : X, ∀ t : ℝ, 0 < t → t ≤ R₁ →
      (1 + η) * μ (ball x t) ≤ μ (ball x (2 * t)) := by
  obtain ⟨D, hD1, hD⟩ := hd.exists_const_of_le (2 * R₁)
  have hD3 : (0 : ℝ≥0) < D ^ 3 := pow_pos (lt_of_lt_of_le one_pos hD1) 3
  refine ⟨(D ^ 3)⁻¹, inv_pos.2 hD3, fun x t ht htR ↦ ?_⟩
  obtain ⟨y, hy⟩ := exists_dist_eq x (r := 3 * t / 2) (by positivity)
  have h4 : μ (ball x t) ≤ (D : ℝ≥0∞) ^ 3 * μ (ball y (t / 2)) := by
    have hsub : ball x t ⊆ ball y (4 * t) := by
      intro z hz
      rw [mem_ball] at hz ⊢
      have := dist_triangle z x y
      linarith
    calc μ (ball x t) ≤ μ (ball y (4 * t)) := measure_mono hsub
      _ ≤ (D : ℝ≥0∞) ^ 3 * μ (ball y (t / 2)) :=
        measure_ball_le_pow_aux hD1 hD 3 y (t / 2) (4 * t) (by positivity)
          (le_of_eq (by ring)) (by linarith)
  have hdisj : Disjoint (ball x t) (ball y (t / 2)) := by
    rw [Set.disjoint_left]
    intro z hz1 hz2
    rw [mem_ball] at hz1 hz2
    have := dist_triangle x z y
    rw [dist_comm x z] at this
    linarith
  have hsub : ball x t ∪ ball y (t / 2) ⊆ ball x (2 * t) := by
    rintro z (hz | hz) <;> rw [mem_ball] at hz ⊢
    · linarith
    · have := dist_triangle z y x
      rw [dist_comm y x] at this
      linarith
  have hη : (((D ^ 3)⁻¹ : ℝ≥0) : ℝ≥0∞) * μ (ball x t) ≤ μ (ball y (t / 2)) := by
    have hinv : (((D ^ 3)⁻¹ : ℝ≥0) : ℝ≥0∞) * (D : ℝ≥0∞) ^ 3 = 1 := by
      rw [← ENNReal.coe_pow, ← ENNReal.coe_mul, inv_mul_cancel₀ hD3.ne', ENNReal.coe_one]
    calc (((D ^ 3)⁻¹ : ℝ≥0) : ℝ≥0∞) * μ (ball x t)
        ≤ (((D ^ 3)⁻¹ : ℝ≥0) : ℝ≥0∞) * ((D : ℝ≥0∞) ^ 3 * μ (ball y (t / 2))) := by gcongr
      _ = μ (ball y (t / 2)) := by rw [← mul_assoc, hinv, one_mul]
  calc (1 + (((D ^ 3)⁻¹ : ℝ≥0) : ℝ≥0∞)) * μ (ball x t)
      = μ (ball x t) + (((D ^ 3)⁻¹ : ℝ≥0) : ℝ≥0∞) * μ (ball x t) := by rw [add_mul, one_mul]
    _ ≤ μ (ball x t) + μ (ball y (t / 2)) := by gcongr
    _ = μ (ball x t ∪ ball y (t / 2)) := (measure_union hdisj measurableSet_ball).symm
    _ ≤ μ (ball x (2 * t)) := measure_mono hsub

theorem rpow_logb_comm {a q : ℝ} (ha : 0 < a) (hq : 0 < q) :
    a ^ Real.logb 2 q = q ^ Real.logb 2 a := by
  rw [Real.rpow_def_of_pos ha, Real.rpow_def_of_pos hq, Real.logb, Real.logb]
  congr 1
  ring

theorem IsLocDoublingM.measure_ball_le_rpow [BallGeometry X] {μ : Measure X}
    (hd : IsLocDoublingM μ) (R₁ : ℝ) :
    ∃ C s : ℝ, 0 < C ∧ 0 < s ∧ ∀ (x x' : X) (r r' : ℝ), 0 < r' → r' ≤ r → r ≤ R₁ →
      dist x x' ≤ r → μ (ball x r) ≤ ENNReal.ofReal (C * (r / r') ^ s) * μ (ball x' r') := by
  obtain ⟨C₀, _, hC₀⟩ := hd.measure_ball_le_pow R₁
  set D : ℝ≥0 := max C₀ 2 with hDdef
  have hD2 : (2 : ℝ) ≤ D := by exact_mod_cast le_max_right C₀ 2
  have hCD : (C₀ : ℝ) ≤ D := by exact_mod_cast le_max_left C₀ 2
  have hDpos : (0 : ℝ) < D := by linarith
  refine ⟨(D : ℝ) ^ 2, Real.logb 2 D, by positivity, Real.logb_pos (by norm_num) (by linarith),
    ?_⟩
  intro x x' r r' hr' hrr hrR hxx'
  have hq1 : 1 ≤ r / r' := (one_le_div hr').2 hrr
  have hqpos : 0 < r / r' := by linarith
  set L := Real.logb 2 (r / r') with hL
  have hL0 : 0 ≤ L := Real.logb_nonneg (by norm_num) hq1
  set k := ⌈L⌉₊ with hkdef
  have hk : r ≤ 2 ^ k * r' := by
    have : r / r' ≤ 2 ^ k := by
      calc r / r' = 2 ^ L := (Real.rpow_logb (by norm_num) (by norm_num) hqpos).symm
        _ ≤ 2 ^ (k : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.le_ceil L)
        _ = 2 ^ k := Real.rpow_natCast 2 k
    rwa [div_le_iff₀ hr'] at this
  have h1 := hC₀ x x' r r' k hr' hrR hxx' hk
  have hreal : (C₀ : ℝ) ^ (k + 1) ≤ (D : ℝ) ^ 2 * (r / r') ^ Real.logb 2 D := by
    calc (C₀ : ℝ) ^ (k + 1) ≤ (D : ℝ) ^ (k + 1) := pow_le_pow_left₀ (by positivity) hCD _
      _ = (D : ℝ) ^ ((k : ℝ) + 1) := by rw [← Real.rpow_natCast]; push_cast; ring_nf
      _ ≤ (D : ℝ) ^ (L + 2) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith [Nat.ceil_lt_add_one hL0])
      _ = (D : ℝ) ^ 2 * (D : ℝ) ^ L := by rw [Real.rpow_add hDpos, Real.rpow_two, mul_comm]
      _ = (D : ℝ) ^ 2 * (r / r') ^ Real.logb 2 D := by rw [rpow_logb_comm hDpos hqpos]
  have hpow : (C₀ : ℝ≥0∞) ^ (k + 1) ≤ ENNReal.ofReal ((D : ℝ) ^ 2 * (r / r') ^ Real.logb 2 D) := by
    have e : (C₀ : ℝ≥0∞) ^ (k + 1) = ENNReal.ofReal ((C₀ : ℝ) ^ (k + 1)) := by
      rw [ENNReal.ofReal_pow (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal]
    rw [e]
    exact ENNReal.ofReal_le_ofReal hreal
  calc μ (ball x r) ≤ (C₀ : ℝ≥0∞) ^ (k + 1) * μ (ball x' r') := h1
    _ ≤ _ := by gcongr

theorem IsLocDoublingM.rpow_le_measure_ball [BallGeometry X] {μ : Measure X}
    (hd : IsLocDoublingM μ) (R₁ : ℝ) :
    ∃ c δ : ℝ, 0 < c ∧ 0 < δ ∧ ∀ (x x' : X) (r r' : ℝ), 0 < r' → r' ≤ r → r ≤ R₁ →
      dist x x' ≤ r → ENNReal.ofReal (c * (r / r') ^ δ) * μ (ball x' r') ≤ μ (ball x r) := by
  obtain ⟨η, hη, hη'⟩ := hd.reverse_doubling R₁
  obtain ⟨D, hD1, hD⟩ := hd.exists_const_of_le R₁
  have hD1' : (1 : ℝ) ≤ D := by exact_mod_cast hD1
  have hDpos : (0 : ℝ) < D := by linarith
  set a : ℝ := 1 + η with hadef
  have ha1 : 1 < a := by
    have : (0 : ℝ) < η := by exact_mod_cast hη
    linarith
  refine ⟨1 / (D * a), Real.logb 2 a, by positivity, Real.logb_pos (by norm_num) ha1, ?_⟩
  intro x x' r r' hr' hrr hrR hxx'
  have hq1 : 1 ≤ r / r' := (one_le_div hr').2 hrr
  have hqpos : 0 < r / r' := by linarith
  set L := Real.logb 2 (r / r') with hL
  have hL0 : 0 ≤ L := Real.logb_nonneg (by norm_num) hq1
  set k := ⌊L⌋₊ with hkdef
  have hk : 2 ^ k * r' ≤ r := by
    have : (2 : ℝ) ^ k ≤ r / r' := by
      calc (2 : ℝ) ^ k = 2 ^ (k : ℝ) := (Real.rpow_natCast 2 k).symm
        _ ≤ 2 ^ L := Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.floor_le hL0)
        _ = r / r' := Real.rpow_logb (by norm_num) (by norm_num) hqpos
    rwa [le_div_iff₀ hr'] at this
  have hiter : ∀ j : ℕ, 2 ^ j * r' ≤ r →
      (1 + (η : ℝ≥0∞)) ^ j * μ (ball x' r') ≤ μ (ball x' (2 ^ j * r')) := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      have hpow : (2 : ℝ) ^ (j + 1) * r' = 2 * (2 ^ j * r') := by ring
      have hj' : 2 ^ j * r' ≤ r / 2 := by rw [hpow] at hj; linarith
      have hjpos : 0 < 2 ^ j * r' := by positivity
      have h1 := ih (by linarith)
      have h2 := hη' x' (2 ^ j * r') hjpos (by linarith)
      calc (1 + (η : ℝ≥0∞)) ^ (j + 1) * μ (ball x' r')
          = (1 + (η : ℝ≥0∞)) * ((1 + (η : ℝ≥0∞)) ^ j * μ (ball x' r')) := by ring
        _ ≤ (1 + (η : ℝ≥0∞)) * μ (ball x' (2 ^ j * r')) := by gcongr
        _ ≤ μ (ball x' (2 * (2 ^ j * r'))) := h2
        _ = μ (ball x' (2 ^ (j + 1) * r')) := by rw [hpow]
  have hsub : ball x' (2 ^ k * r') ⊆ ball x (2 * r) := by
    intro z hz
    rw [mem_ball] at hz ⊢
    have := dist_triangle z x' x
    rw [dist_comm x' x] at this
    linarith
  have hmain : (1 + (η : ℝ≥0∞)) ^ k * μ (ball x' r') ≤ D * μ (ball x r) :=
    (hiter k hk).trans ((measure_mono hsub).trans (hD x r (by linarith) hrR))
  have hreal : (D : ℝ) * (1 / (D * a) * (r / r') ^ Real.logb 2 a) ≤ a ^ k := by
    rw [← rpow_logb_comm (by linarith) hqpos]
    have h1 : a ^ L ≤ a ^ ((k : ℝ) + 1) :=
      Real.rpow_le_rpow_of_exponent_le ha1.le (Nat.lt_floor_add_one L).le
    rw [Real.rpow_add (by linarith), Real.rpow_one, Real.rpow_natCast] at h1
    have e : (D : ℝ) * (1 / (D * a) * a ^ L) = a ^ L / a := by field_simp
    rw [e, div_le_iff₀ (by linarith)]
    exact h1
  have hennr : (D : ℝ≥0∞) * ENNReal.ofReal (1 / (D * a) * (r / r') ^ Real.logb 2 a) ≤
      (1 + (η : ℝ≥0∞)) ^ k := by
    have e1 : (D : ℝ≥0∞) = ENNReal.ofReal D := ENNReal.ofReal_coe_nnreal.symm
    have e2 : (1 + (η : ℝ≥0∞)) ^ k = ENNReal.ofReal (a ^ k) := by
      rw [ENNReal.ofReal_pow (by linarith), hadef, ENNReal.ofReal_add zero_le_one (NNReal.coe_nonneg _),
        ENNReal.ofReal_one, ENNReal.ofReal_coe_nnreal]
    rw [e1, e2, ← ENNReal.ofReal_mul hDpos.le]
    exact ENNReal.ofReal_le_ofReal hreal
  have hD0 : (D : ℝ≥0∞) ≠ 0 := by
    have : (0 : ℝ≥0) < D := lt_of_lt_of_le one_pos hD1
    exact_mod_cast this.ne'
  refine (ENNReal.mul_le_mul_iff_right hD0 ENNReal.coe_ne_top).mp ?_
  calc (D : ℝ≥0∞) * (ENNReal.ofReal (1 / (D * a) * (r / r') ^ Real.logb 2 a) * μ (ball x' r'))
      = ((D : ℝ≥0∞) * ENNReal.ofReal (1 / (D * a) * (r / r') ^ Real.logb 2 a)) *
          μ (ball x' r') := by ring
    _ ≤ (1 + (η : ℝ≥0∞)) ^ k * μ (ball x' r') := by gcongr
    _ ≤ D * μ (ball x r) := hmain

/-- **Lemma 1** in the paper's form. -/
theorem IsLocDoublingM.lemma1 [BallGeometry X] {μ : Measure X}
    (hd : IsLocDoublingM μ) (R₁ : ℝ) :
    ∃ γ A : ℝ, 0 < γ ∧ γ ≤ 1 ∧ 0 < A ∧
      ∀ (x x' : X) (r r' : ℝ), 0 < r' → r ≤ R₁ → dist x x' + r' ≤ r →
        0 < μ (ball x' r') → μ (ball x r) < ∞ →
        ((μ (ball x r)).toReal / (μ (ball x' r')).toReal) ^ γ ≤ A * (r / r') ∧
        r / r' ≤ A * ((μ (ball x r)).toReal / (μ (ball x' r')).toReal) ^ (1 / γ) := by
  obtain ⟨C, s, hC, hs, hup⟩ := hd.measure_ball_le_rpow R₁
  obtain ⟨c, δ, hc, hδ, hlow⟩ := hd.rpow_le_measure_ball R₁
  set γ := min 1 (min (1 / s) δ) with hγdef
  have hγ : 0 < γ := lt_min one_pos (lt_min (by positivity) hδ)
  have hγ1 : γ ≤ 1 := min_le_left _ _
  have hγs : γ ≤ 1 / s := (min_le_right _ _).trans (min_le_left _ _)
  have hγδ : γ ≤ δ := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨γ, max (C ^ (1 / s)) (c ^ (-1 / δ)), hγ, hγ1,
    lt_max_of_lt_left (Real.rpow_pos_of_pos hC _), ?_⟩
  intro x x' r r' hr' hrR hdr hpos hfin
  have hrr : r' ≤ r := by linarith [dist_nonneg (x := x) (y := x')]
  have hxx : dist x x' ≤ r := by linarith
  have hsub : ball x' r' ⊆ ball x r := by
    intro z hz
    rw [mem_ball] at hz ⊢
    have := dist_triangle z x' x
    rw [dist_comm x' x] at this
    linarith
  set A := μ (ball x r) with hAdef
  set B := μ (ball x' r') with hBdef
  have hBA : B ≤ A := measure_mono hsub
  have hBfin : B ≠ ∞ := (hBA.trans_lt hfin).ne
  have hAfin : A ≠ ∞ := hfin.ne
  have hb : 0 < B.toReal := ENNReal.toReal_pos hpos.ne' hBfin
  have hab : B.toReal ≤ A.toReal := ENNReal.toReal_mono hAfin hBA
  set Q := A.toReal / B.toReal with hQdef
  have hQ1 : 1 ≤ Q := (one_le_div hb).2 hab
  set q := r / r' with hqdef
  have hq1 : 1 ≤ q := (one_le_div hr').2 hrr
  have hU : A.toReal ≤ C * q ^ s * B.toReal := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hBfin)
      (hup x x' r r' hr' hrr hrR hxx)
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at this
  have hQU : Q ≤ C * q ^ s := by rw [div_le_iff₀ hb]; exact hU
  have hL : c * q ^ δ * B.toReal ≤ A.toReal := by
    have := ENNReal.toReal_mono hAfin (hlow x x' r r' hr' hrr hrR hxx)
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at this
  have hQL : c * q ^ δ ≤ Q := by rw [le_div_iff₀ hb]; exact hL
  constructor
  · calc Q ^ γ ≤ Q ^ (1 / s) := Real.rpow_le_rpow_of_exponent_le hQ1 hγs
      _ ≤ (C * q ^ s) ^ (1 / s) := Real.rpow_le_rpow (by linarith) hQU (by positivity)
      _ = C ^ (1 / s) * q := by
        rw [Real.mul_rpow hC.le (by positivity), ← Real.rpow_mul (by linarith),
          mul_one_div_cancel hs.ne', Real.rpow_one]
      _ ≤ max (C ^ (1 / s)) (c ^ (-1 / δ)) * q := by gcongr; exact le_max_left _ _
  · have hqδ : q ^ δ ≤ Q / c := by
      rw [le_div_iff₀ hc]
      linarith
    calc q = (q ^ δ) ^ (1 / δ) := by
          rw [← Real.rpow_mul (by linarith), mul_one_div_cancel hδ.ne', Real.rpow_one]
      _ ≤ (Q / c) ^ (1 / δ) := Real.rpow_le_rpow (by positivity) hqδ (by positivity)
      _ = c ^ (-1 / δ) * Q ^ (1 / δ) := by
          rw [Real.div_rpow (by linarith) hc.le, neg_div, Real.rpow_neg hc.le, div_eq_inv_mul]
      _ ≤ c ^ (-1 / δ) * Q ^ (1 / γ) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hQ1
            (one_div_le_one_div_of_le hγ hγδ)) (by positivity)
      _ ≤ max (C ^ (1 / s)) (c ^ (-1 / δ)) * Q ^ (1 / γ) := by gcongr; exact le_max_right _ _

theorem IsLocDoublingM.measure_singleton {μ : Measure X} (hd : IsLocDoublingM μ)
    [BallGeometry X] (hfin : ∀ x : X, ∀ r : ℝ, μ (ball x r) < ∞) (x : X) : μ {x} = 0 := by
  obtain ⟨η, hη, hη'⟩ := hd.reverse_doubling 1
  set q : ℝ≥0∞ := (1 + (η : ℝ≥0∞))⁻¹ with hqdef
  have h1η0 : (1 + (η : ℝ≥0∞)) ≠ 0 := (lt_of_lt_of_le one_pos le_self_add).ne'
  have h1ηt : (1 + (η : ℝ≥0∞)) ≠ ∞ := by simp
  have hq1 : q < 1 := by
    refine ENNReal.inv_lt_one.mpr ?_
    have : (0 : ℝ≥0∞) < η := by exact_mod_cast hη
    exact ENNReal.lt_add_right ENNReal.one_ne_top this.ne'
  have hstep : ∀ k : ℕ, μ (ball x ((1 / 2) ^ k)) ≤ q ^ k * μ (ball x 1) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have h := hη' x ((1 / 2) ^ (k + 1)) (by positivity)
        (pow_le_one₀ (by norm_num) (by norm_num))
      rw [show 2 * (1 / 2 : ℝ) ^ (k + 1) = (1 / 2) ^ k by ring] at h
      have h' : μ (ball x ((1 / 2) ^ (k + 1))) ≤ q * μ (ball x ((1 / 2) ^ k)) :=
        (ENNReal.mul_le_iff_le_inv h1η0 h1ηt).mp h
      calc μ (ball x ((1 / 2) ^ (k + 1))) ≤ q * μ (ball x ((1 / 2) ^ k)) := h'
        _ ≤ q * (q ^ k * μ (ball x 1)) := by gcongr
        _ = q ^ (k + 1) * μ (ball x 1) := by ring
  have htend : Filter.Tendsto (fun k : ℕ ↦ q ^ k * μ (ball x 1)) Filter.atTop (nhds 0) := by
    have := ENNReal.Tendsto.mul_const (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hq1)
      (Or.inr (hfin x 1).ne)
    simpa using this
  refine le_antisymm (ge_of_tendsto' htend fun k ↦ ?_) (zero_le)
  exact (measure_mono (singleton_subset_iff.2 (mem_ball_self (by positivity)))).trans (hstep k)

theorem IsLocDoublingM.measure_ball_pos [BallGeometry X] {μ : Measure X}
    (hd : IsLocDoublingM μ) (hm : ∃ R : ℝ, 0 < R ∧ ∀ x : X, 1 ≤ μ (ball x R))
    (x : X) {r : ℝ} (hr : 0 < r) : 0 < μ (ball x r) := by
  obtain ⟨R, hR, hRm⟩ := hm
  obtain ⟨C, _, hC⟩ := hd.measure_ball_le_pow R
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (R / r) (by norm_num : (1 : ℝ) < 2)
  have hk' : R ≤ 2 ^ k * r := by rw [div_lt_iff₀ hr] at hk; linarith
  have h := hC x x R r k hr le_rfl (by rw [dist_self]; exact hR.le) hk'
  have h1 : (1 : ℝ≥0∞) ≤ C ^ (k + 1) * μ (ball x r) := (hRm x).trans h
  rw [pos_iff_ne_zero]
  intro h0
  rw [h0, mul_zero] at h1
  exact absurd h1 (by norm_num)

theorem IsPorous.mono {E F : Set X} (hF : IsPorous F) (hEF : E ⊆ F) : IsPorous E := by
  obtain ⟨κ, s₀, hκ, hs₀, h⟩ := hF
  exact ⟨κ, s₀, hκ, hs₀, fun y hy s hs hss ↦ (h y (hEF hy) s hs hss).imp
    fun _ hy' ↦ ⟨hy'.1, fun e he ↦ hy'.2 e (hEF he)⟩⟩

/-- **Lemma 2 (abstract)**: porous sets are null. -/
theorem IsLocDoublingM.measure_eq_zero_of_isPorous [TopologicalSpace.SeparableSpace X]
    {μ : Measure X} (hd : IsLocDoublingM μ) (hfin : ∀ x : X, ∀ r : ℝ, μ (ball x r) < ∞)
    {E : Set X} (hE : IsPorous E) : μ E = 0 := sorry

theorem isPorous_sphere [BallGeometry X] (x : X) (r : ℝ) : IsPorous (sphere x r) := sorry

theorem IsLocDoublingM.measure_sphere [BallGeometry X] [TopologicalSpace.SeparableSpace X]
    {μ : Measure X} (hd : IsLocDoublingM μ) (hfin : ∀ x : X, ∀ r : ℝ, μ (ball x r) < ∞)
    (x : X) (r : ℝ) : μ (sphere x r) = 0 := sorry

theorem IsLocDoublingM.measure_closedBall [BallGeometry X] [TopologicalSpace.SeparableSpace X]
    {μ : Measure X} (hd : IsLocDoublingM μ) (hfin : ∀ x : X, ∀ r : ℝ, μ (ball x r) < ∞)
    (x : X) (r : ℝ) : μ (closedBall x r) = μ (ball x r) := sorry

theorem IsLocDoublingM.continuous_measure_ball [BallGeometry X]
    [TopologicalSpace.SeparableSpace X] {μ : Measure X} (hd : IsLocDoublingM μ)
    (hfin : ∀ x : X, ∀ r : ℝ, μ (ball x r) < ∞) (x : X) :
    Continuous fun r : ℝ ↦ μ (ball x r) := sorry

/-! ### The mass radius -/

theorem massRadiusM_le {μ : Measure X} {x : X} {R : ℝ} (hR : 0 < R) (h : 1 ≤ μ (ball x R)) :
    massRadiusM μ x ≤ R := sorry

theorem massRadiusM_nonneg (μ : Measure X) (x : X) : 0 ≤ massRadiusM μ x := sorry

theorem measure_ball_massRadiusM_le_one (μ : Measure X) (x : X) :
    μ (ball x (massRadiusM μ x)) ≤ 1 := sorry

theorem one_le_measure_ball_of_massRadiusM_lt {μ : Measure X} {x : X}
    (hne : ∃ r, 0 < r ∧ 1 ≤ μ (ball x r)) {r : ℝ} (hr : massRadiusM μ x < r) :
    1 ≤ μ (ball x r) := sorry

theorem measure_ball_lt_one_of_lt_massRadiusM {μ : Measure X} {x : X} {r : ℝ}
    (hr : r < massRadiusM μ x) : μ (ball x r) < 1 := sorry

theorem one_le_measure_closedBall_massRadiusM {μ : Measure X} {x : X}
    (hfin : ∀ r, μ (ball x r) < ∞) (hne : ∃ r, 0 < r ∧ 1 ≤ μ (ball x r)) :
    1 ≤ μ (closedBall x (massRadiusM μ x)) := sorry

theorem IsLocDoublingM.massRadiusM_pos [BallGeometry X] {μ : Measure X}
    (hd : IsLocDoublingM μ) (hfin : ∀ x : X, ∀ r : ℝ, μ (ball x r) < ∞) {x : X}
    (hne : ∃ r, 0 < r ∧ 1 ≤ μ (ball x r)) : 0 < massRadiusM μ x := sorry

theorem IsLocDoublingM.measure_ball_massRadiusM [BallGeometry X]
    [TopologicalSpace.SeparableSpace X] {μ : Measure X} (hd : IsLocDoublingM μ)
    (hfin : ∀ x : X, ∀ r : ℝ, μ (ball x r) < ∞) {x : X}
    (hne : ∃ r, 0 < r ∧ 1 ≤ μ (ball x r)) : μ (ball x (massRadiusM μ x)) = 1 := sorry

theorem lipschitzWith_massRadiusM {μ : Measure X} (hne : ∀ x : X, ∃ r, 0 < r ∧ 1 ≤ μ (ball x r)) :
    LipschitzWith 1 (massRadiusM μ) := sorry

/-- `μ(B(x,r)) ≍ (r/ρ(x))^{s or δ}` for `ρ(x) ≤ r ≤ R₁`. -/
theorem IsLocDoublingM.measure_ball_massRadiusM_bounds [BallGeometry X]
    [TopologicalSpace.SeparableSpace X] {μ : Measure X} (hd : IsLocDoublingM μ)
    (hfin : ∀ x : X, ∀ r : ℝ, μ (ball x r) < ∞)
    (hm : ∃ R : ℝ, 0 < R ∧ ∀ x : X, 1 ≤ μ (ball x R)) (R₁ : ℝ) :
    ∃ c C δ s : ℝ, 0 < c ∧ 0 < C ∧ 0 < δ ∧ 0 < s ∧ ∀ (x : X) (r : ℝ),
      massRadiusM μ x ≤ r → r ≤ R₁ →
        ENNReal.ofReal (c * (r / massRadiusM μ x) ^ δ) ≤ μ (ball x r) ∧
        μ (ball x r) ≤ ENNReal.ofReal (C * (r / massRadiusM μ x) ^ s) := sorry

/-- **Claim 1**. -/
theorem IsLocDoublingM.claim1 [BallGeometry X] {μ : Measure X} (hd : IsLocDoublingM μ)
    (hfin : ∀ x : X, ∀ r : ℝ, μ (ball x r) < ∞)
    (hm : ∃ R : ℝ, 0 < R ∧ ∀ x : X, 1 ≤ μ (ball x R)) (K : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x y : X,
      dist x y ≤ K * max (massRadiusM μ x) (massRadiusM μ y) →
        massRadiusM μ x ≤ C * massRadiusM μ y := sorry

/-- **Lemma 3**, truncated form (contains the paper's statement on `δρ(w) ≤ d < R₁`). -/
theorem IsLocDoublingM.lemma3 [BallGeometry X] [TopologicalSpace.SeparableSpace X]
    {μ : Measure X} (hd : IsLocDoublingM μ) (hfin : ∀ x : X, ∀ r : ℝ, μ (ball x r) < ∞)
    (hm : ∃ R : ℝ, 0 < R ∧ ∀ x : X, 1 ≤ μ (ball x R)) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ δ R₁ : ℝ, 0 < δ → ∃ C : ℝ≥0, ∀ w : X,
      ∫⁻ z in ball w R₁,
        ENNReal.ofReal ((massRadiusM μ z / max (dist z w) (δ * massRadiusM μ w)) ^ m) ∂μ ≤ C :=
  sorry

/-- **Lemma 3** as printed (region `δρ(w) ≤ d(z,w) < R₁`). -/
theorem IsLocDoublingM.lemma3_paper [BallGeometry X] [TopologicalSpace.SeparableSpace X]
    {μ : Measure X} (hd : IsLocDoublingM μ) (hfin : ∀ x : X, ∀ r : ℝ, μ (ball x r) < ∞)
    (hm : ∃ R : ℝ, 0 < R ∧ ∀ x : X, 1 ≤ μ (ball x R)) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ δ R₁ : ℝ, 0 < δ → ∃ C : ℝ≥0, ∀ w : X,
      ∫⁻ z in {z | δ * massRadiusM μ w ≤ dist z w ∧ dist z w < R₁},
        ENNReal.ofReal ((massRadiusM μ z / dist z w) ^ m) ∂μ ≤ C := sorry

/-- **[Chr91, Lemma 2.3]**. -/
theorem IsLocDoublingM.christ_lemma23 [BallGeometry X] {μ : Measure X}
    (hd : IsLocDoublingM μ) (R₁ : ℝ) :
    ∃ C : ℝ≥0, ∀ (x : X) (R : ℝ), 0 < R → R ≤ R₁ →
      ∫⁻ y in ball x R, ENNReal.ofReal (Real.log (R / dist x y)) ∂μ ≤ C * μ (ball x R) := sorry

theorem IsLocDoublingM.integrableOn_log_dist [BallGeometry X] {μ : Measure X}
    (hd : IsLocDoublingM μ) (hfin : ∀ x : X, ∀ r : ℝ, μ (ball x r) < ∞) (x : X) (R : ℝ) :
    IntegrableOn (fun y ↦ Real.log (dist x y)) (ball x R) μ := sorry

/-- **Growth**: balls of a fixed large radius have mass `> p`. No doubling needed. -/
theorem exists_radius_lt_measure_ball [BallGeometry X] {μ : Measure X}
    (hm : ∃ R : ℝ, 0 < R ∧ ∀ x : X, 1 ≤ μ (ball x R)) (p : ℝ≥0) :
    ∃ r : ℝ, 0 < r ∧ ∀ x : X, (p : ℝ≥0∞) < μ (ball x r) := sorry

theorem IsLocDoublingM.smul {μ : Measure X} (hd : IsLocDoublingM μ) (c : ℝ≥0∞) :
    IsLocDoublingM (c • μ) := sorry

/-- Mass radius for `N⁻¹ μ` versus `μ` (reduction of mass-`N` pieces to mass-`1` pieces). -/
theorem IsLocDoublingM.massRadiusM_inv_smul [BallGeometry X] {μ : Measure X}
    (hd : IsLocDoublingM μ) (hfin : ∀ x : X, ∀ r : ℝ, μ (ball x r) < ∞)
    (hm : ∃ R : ℝ, 0 < R ∧ ∀ x : X, 1 ≤ μ (ball x R)) (N : ℕ) (hN : 1 ≤ N) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ x : X, massRadiusM μ x ≤ massRadiusM ((N : ℝ≥0∞)⁻¹ • μ) x ∧
      massRadiusM ((N : ℝ≥0∞)⁻¹ • μ) x ≤ C * massRadiusM μ x := sorry

/-- **Decay of `ρ(ζ)/d(z,ζ)`** (coordinator addition (1)), power form. -/
theorem IsLocDoublingM.massRadiusM_div_dist_le [BallGeometry X] {μ : Measure X}
    (hd : IsLocDoublingM μ) (hfin : ∀ x : X, ∀ r : ℝ, μ (ball x r) < ∞)
    (hm : ∃ R : ℝ, 0 < R ∧ ∀ x : X, 1 ≤ μ (ball x R)) (M₀ : ℝ) :
    ∃ C α : ℝ, 0 < C ∧ 0 < α ∧ α ≤ 1 ∧ ∀ z ζ : X, massRadiusM μ z ≤ dist z ζ → dist z ζ ≤ M₀ →
      massRadiusM μ ζ / dist z ζ ≤ C * (massRadiusM μ z / dist z ζ) ^ α := sorry

/-- **Decay**, geometric form: `d(z,ζ) ≥ 2ⁿ ρ(z)`, `d ≤ M₀` ⟹ `ρ(ζ)/d(z,ζ) ≤ C θⁿ`. -/
theorem IsLocDoublingM.decay [BallGeometry X] {μ : Measure X}
    (hd : IsLocDoublingM μ) (hfin : ∀ x : X, ∀ r : ℝ, μ (ball x r) < ∞)
    (hm : ∃ R : ℝ, 0 < R ∧ ∀ x : X, 1 ≤ μ (ball x R)) (M₀ : ℝ) :
    ∃ C θ : ℝ, 0 < C ∧ 0 < θ ∧ θ < 1 ∧ ∀ (z ζ : X) (n : ℕ),
      2 ^ n * massRadiusM μ z ≤ dist z ζ → dist z ζ ≤ M₀ →
        massRadiusM μ ζ / dist z ζ ≤ C * θ ^ n := sorry

/-- Disjoint open balls of radius `a` in a `BallGeometry` space have `2a`-separated centres. -/
theorem le_dist_of_disjoint_ball [BallGeometry X] {x y : X} {a : ℝ}
    (h : Disjoint (ball x a) (ball y a)) : 2 * a ≤ dist x y := sorry

/-- **Bounded count** (coordinator addition (2)), abstract form: disjoint sets containing a ball
of radius `a` and contained in a ball of radius `D` around the same centre; at most `M` of them
meet a ball of radius `b`. -/
theorem BallGeometry.encard_le_of_disjoint [BallGeometry X] (a b D : ℝ) (ha : 0 < a) :
    ∃ M : ℕ, ∀ {ι : Type*} (E : ι → Set X) (c : ι → X) (z : X), Pairwise (Function.onFun Disjoint E) →
      (∀ i, ball (c i) a ⊆ E i) → (∀ i, E i ⊆ ball (c i) D) →
        {i | (E i ∩ ball z b).Nonempty}.encard ≤ M := sorry

end Abstract

end OC
