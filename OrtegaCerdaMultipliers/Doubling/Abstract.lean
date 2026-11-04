import OrtegaCerdaMultipliers.Defs

/-!
# M03 (Doubling) — Locally doubling measures on a metric space

See `blueprint/M03_Doubling.md` §2.1.  All proofs are complete.

The whole theory of §2 of the paper on an abstract metric space `X` with `BallGeometry`:
`IsLocDoublingM`, `BallGeometry`, `IsPorous`, `massRadiusM`, scale-up, Lemma 1, Lemma 2 (porous
sets are null), the mass radius, Claim 1, Lemma 3, [Chr91, Lemma 2.3], growth, decay, bounded
count.
-/

open MeasureTheory Metric Set Complex
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

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

omit [MeasurableSpace X] [OpensMeasurableSpace X] in
theorem exists_dist_eq [BallGeometry X] (x : X) {r : ℝ} (hr : 0 ≤ r) : ∃ y, dist x y = r := by
  obtain ⟨y, hy⟩ := BallGeometry.exists_far x r
  obtain ⟨m, hm1, hm2⟩ := BallGeometry.exists_between x y r hr hy
  refine ⟨m, le_antisymm hm1 ?_⟩
  have := dist_triangle x m y
  linarith

omit [OpensMeasurableSpace X] in
/-- Local doubling with a constant `≥ 1` at base radii `≤ 1/4`. -/
theorem IsLocDoublingM.exists_const_quarter {μ : Measure X} (hd : IsLocDoublingM μ) :
    ∃ C : ℝ≥0, 1 ≤ C ∧ ∀ x : X, ∀ r : ℝ, 0 < r → r ≤ 1 / 4 →
      μ (ball x (2 * r)) ≤ C * μ (ball x r) := by
  obtain ⟨C, hC⟩ := hd
  refine ⟨max C 1, le_max_right _ _, fun x r hr hr4 ↦ ?_⟩
  calc μ (ball x (2 * r)) ≤ C * μ (ball x r) := hC x r hr (by linarith)
    _ ≤ (max C 1 : ℝ≥0) * μ (ball x r) := by gcongr; exact_mod_cast le_max_left _ _

omit [OpensMeasurableSpace X] in
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

omit [OpensMeasurableSpace X] in
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

omit [OpensMeasurableSpace X] in
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

omit [OpensMeasurableSpace X] in
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

omit [OpensMeasurableSpace X] in
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

omit [OpensMeasurableSpace X] in
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

omit [OpensMeasurableSpace X] in
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

omit [MeasurableSpace X] [OpensMeasurableSpace X] in
theorem IsPorous.mono {E F : Set X} (hF : IsPorous F) (hEF : E ⊆ F) : IsPorous E := by
  obtain ⟨κ, s₀, hκ, hs₀, h⟩ := hF
  exact ⟨κ, s₀, hκ, hs₀, fun y hy s hs hss ↦ (h y (hEF hy) s hs hss).imp
    fun _ hy' ↦ ⟨hy'.1, fun e he ↦ hy'.2 e (hEF he)⟩⟩

/-- One scale of Lemma 2: a porous set inside `ball x₀ R₀` has mass at most `D^k` times the mass
of the points of `ball x₀ (R₀ + 1)` at distance in `(0, 2s)` from it. -/
theorem measure_le_of_isPorous_scale [TopologicalSpace.SeparableSpace X] {μ : Measure X}
    {D : ℝ≥0} (hD1 : 1 ≤ D)
    (hD : ∀ x : X, ∀ r : ℝ, 0 < r → r ≤ 1 / 4 → μ (ball x (2 * r)) ≤ D * μ (ball x r))
    {E : Set X} {κ s : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hs : 0 < s) (hs1 : s ≤ 1 / 20)
    (hpor : ∀ y ∈ E, ∃ y', dist y y' ≤ s ∧ ∀ e ∈ E, κ * s ≤ dist y' e)
    {k : ℕ} (hk : 10 ≤ 2 ^ k * κ) (x₀ : X) {R₀ : ℝ} (hEb : E ⊆ ball x₀ R₀) :
    μ E ≤ D ^ k * μ (ball x₀ (R₀ + 1) ∩ (fun ζ ↦ infDist ζ E) ⁻¹' Ioo 0 (2 * s)) := by
  rcases E.eq_empty_or_nonempty with hE0 | hEne
  · simp [hE0]
  choose! f hf1 hf2 using hpor
  obtain ⟨u, huE, hudisj, hucov⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement
    (fun y ↦ ball y (2 * s)) E (fun _ ↦ 2 * s) 2 one_lt_two (fun _ _ ↦ by positivity) (2 * s)
    (fun _ _ ↦ le_rfl) (fun y _ ↦ ⟨y, mem_ball_self (by positivity)⟩)
  have hucount : u.Countable := hudisj.countable_of_isOpen (fun _ _ ↦ isOpen_ball)
    (fun y _ ↦ ⟨y, mem_ball_self (by positivity)⟩)
  set hole : X → Set X := fun y ↦ ball (f y) (κ * s / 2) with hholedef
  have hκs : κ * s ≤ s := by nlinarith
  have hhole_sub : ∀ y ∈ E, hole y ⊆ ball y (2 * s) := by
    intro y hy z hz
    simp only [hole, mem_ball] at hz ⊢
    have h1 := dist_triangle z (f y) y
    rw [dist_comm (f y) y] at h1
    have h2 := hf1 y hy
    linarith
  have hholedisj : u.PairwiseDisjoint hole :=
    hudisj.mono_on fun y hy ↦ hhole_sub y (huE hy)
  have hEcov : E ⊆ ⋃ b ∈ u, ball b (4 * s) := by
    intro a ha
    obtain ⟨b, hb, ⟨z, hz1, hz2⟩, _⟩ := hucov a ha
    refine mem_iUnion₂.2 ⟨b, hb, ?_⟩
    simp only [mem_ball] at hz1 hz2 ⊢
    have := dist_triangle a z b
    rw [dist_comm a z] at this
    linarith
  have hball : ∀ b ∈ u, μ (ball b (4 * s)) ≤ (D : ℝ≥0∞) ^ k * μ (hole b) := by
    intro b hb
    have hsub : ball b (4 * s) ⊆ ball (f b) (5 * s) := by
      intro z hz
      rw [mem_ball] at hz ⊢
      have h1 := dist_triangle z b (f b)
      have h2 := hf1 b (huE hb)
      linarith
    have hks : 5 * s ≤ 2 ^ k * (κ * s / 2) := by
      have := mul_le_mul_of_nonneg_right hk hs.le
      have e : (2 : ℝ) ^ k * (κ * s / 2) = 2 ^ k * κ * s / 2 := by ring
      rw [e]
      linarith
    calc μ (ball b (4 * s)) ≤ μ (ball (f b) (5 * s)) := measure_mono hsub
      _ ≤ (D : ℝ≥0∞) ^ k * μ (ball (f b) (κ * s / 2)) :=
        measure_ball_le_pow_aux hD1 hD k (f b) (κ * s / 2) (5 * s) (by positivity) hks
          (by linarith)
  have hhole_shell : ∀ b ∈ u,
      hole b ⊆ ball x₀ (R₀ + 1) ∩ (fun ζ ↦ infDist ζ E) ⁻¹' Ioo 0 (2 * s) := by
    intro b hb ζ hζ
    have hbE := huE hb
    simp only [hole, mem_ball] at hζ
    have hfb := hf1 b hbE
    have hlow : κ * s / 2 ≤ infDist ζ E := by
      refine (le_infDist hEne).2 fun e he ↦ ?_
      have h1 := hf2 b hbE e he
      have h2 := dist_triangle (f b) ζ e
      rw [dist_comm (f b) ζ] at h2
      linarith
    have hup : infDist ζ E ≤ dist ζ b := infDist_le_dist_of_mem hbE
    have h3 := dist_triangle ζ (f b) b
    rw [dist_comm (f b) b] at h3
    have hb0 := hEb hbE
    rw [mem_ball] at hb0
    refine ⟨?_, ?_⟩
    · rw [mem_ball]
      have := dist_triangle ζ b x₀
      linarith
    · rw [mem_preimage, mem_Ioo]
      have : 0 < κ * s / 2 := by positivity
      constructor <;> linarith
  calc μ E ≤ μ (⋃ b ∈ u, ball b (4 * s)) := measure_mono hEcov
    _ ≤ ∑' b : u, μ (ball b (4 * s)) := measure_biUnion_le μ hucount _
    _ ≤ ∑' b : u, (D : ℝ≥0∞) ^ k * μ (hole b) := ENNReal.tsum_le_tsum fun b ↦ hball b b.2
    _ = (D : ℝ≥0∞) ^ k * ∑' b : u, μ (hole b) := ENNReal.tsum_mul_left
    _ = (D : ℝ≥0∞) ^ k * μ (⋃ b ∈ u, hole b) := by
        rw [measure_biUnion hucount hholedisj (fun _ _ ↦ measurableSet_ball)]
    _ ≤ _ := by gcongr; exact iUnion₂_subset hhole_shell

/-- Lemma 2 for a bounded porous set. -/
theorem measure_eq_zero_of_isPorous_of_subset_ball [TopologicalSpace.SeparableSpace X]
    {μ : Measure X} {D : ℝ≥0} (hD1 : 1 ≤ D)
    (hD : ∀ x : X, ∀ r : ℝ, 0 < r → r ≤ 1 / 4 → μ (ball x (2 * r)) ≤ D * μ (ball x r))
    (hfin : ∀ x : X, ∀ r : ℝ, μ (ball x r) < ∞) {E : Set X} (hE : IsPorous E) (x₀ : X)
    {R₀ : ℝ} (hEb : E ⊆ ball x₀ R₀) : μ E = 0 := by
  rcases E.eq_empty_or_nonempty with hE0 | ⟨y₀, hy₀⟩
  · simp [hE0]
  obtain ⟨κ, s₀, hκ, hs₀, hpor⟩ := hE
  have hκ1 : κ ≤ 1 := by
    obtain ⟨y', h1, h2⟩ := hpor y₀ hy₀ s₀ hs₀ le_rfl
    have h3 := h2 y₀ hy₀
    rw [dist_comm] at h3
    by_contra hcon
    push Not at hcon
    nlinarith
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (10 / κ) (by norm_num : (1 : ℝ) < 2)
  have hk' : 10 ≤ 2 ^ k * κ := by rw [div_lt_iff₀ hκ] at hk; linarith
  set s₁ := min s₀ (1 / 20) with hs₁def
  have hs₁ : 0 < s₁ := lt_min hs₀ (by norm_num)
  set a : ℕ → ℝ := fun n ↦ s₁ / (n + 1) with hadef
  have ha : ∀ n, 0 < a n := fun n ↦ by positivity
  have ha1 : ∀ n, a n ≤ s₁ := fun n ↦ div_le_self hs₁.le (by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith)
  set U : ℕ → Set X := fun n ↦ ball x₀ (R₀ + 1) ∩ (fun ζ ↦ infDist ζ E) ⁻¹' Ioo 0 (2 * a n)
    with hUdef
  have hbound : ∀ n, μ E ≤ (D : ℝ≥0∞) ^ k * μ (U n) := fun n ↦
    measure_le_of_isPorous_scale hD1 hD hκ hκ1 (ha n) ((ha1 n).trans (min_le_right _ _))
      (fun y hy ↦ hpor y hy (a n) (ha n) ((ha1 n).trans (min_le_left _ _))) hk' x₀ hEb
  have hmeas : ∀ n, MeasurableSet (U n) := fun n ↦
    measurableSet_ball.inter ((continuous_infDist_pt E).measurable measurableSet_Ioo)
  have hanti : Antitone U := by
    intro n m hnm ζ hζ
    refine ⟨hζ.1, ?_⟩
    have h2 := hζ.2
    rw [mem_preimage, mem_Ioo] at h2 ⊢
    have : a m ≤ a n := by
      simp only [hadef]
      gcongr
    constructor <;> linarith [h2.1, h2.2]
  have hinter : ⋂ n, U n = ∅ := by
    ext ζ
    simp only [mem_iInter, mem_empty_iff_false, iff_false, not_forall]
    by_cases hζ : 0 < infDist ζ E
    · obtain ⟨n, hn⟩ := exists_nat_gt (2 * s₁ / infDist ζ E)
      refine ⟨n, fun h ↦ ?_⟩
      have h2 := h.2
      rw [mem_preimage, mem_Ioo] at h2
      have hlt : 2 * a n < infDist ζ E := by
        simp only [hadef]
        rw [div_lt_iff₀ hζ] at hn
        rw [← mul_div_assoc, div_lt_iff₀ (by positivity)]
        nlinarith
      linarith [h2.2]
    · refine ⟨0, fun h ↦ hζ ?_⟩
      have h2 := h.2
      rw [mem_preimage, mem_Ioo] at h2
      exact h2.1
  have hU0 : μ (U 0) ≠ ∞ :=
    ((measure_mono inter_subset_left).trans_lt (hfin x₀ (R₀ + 1))).ne
  have htend := tendsto_measure_iInter_atTop (fun n ↦ (hmeas n).nullMeasurableSet) hanti ⟨0, hU0⟩
  rw [hinter, measure_empty] at htend
  have htend2 : Filter.Tendsto (fun n ↦ (D : ℝ≥0∞) ^ k * μ (U n)) Filter.atTop (nhds 0) := by
    have := ENNReal.Tendsto.const_mul htend
      (Or.inr (ENNReal.pow_ne_top ENNReal.coe_ne_top) : (0 : ℝ≥0∞) ≠ 0 ∨ (D : ℝ≥0∞) ^ k ≠ ∞)
    simpa [Function.comp_def] using this
  exact le_antisymm (ge_of_tendsto' htend2 hbound) zero_le

/-- **Lemma 2 (abstract)**: porous sets are null. -/
theorem IsLocDoublingM.measure_eq_zero_of_isPorous [TopologicalSpace.SeparableSpace X]
    {μ : Measure X} (hd : IsLocDoublingM μ) (hfin : ∀ x : X, ∀ r : ℝ, μ (ball x r) < ∞)
    {E : Set X} (hE : IsPorous E) : μ E = 0 := by
  obtain ⟨D, hD1, hD⟩ := hd.exists_const_quarter
  rcases E.eq_empty_or_nonempty with hE0 | ⟨x₀, _⟩
  · rw [hE0, measure_empty]
  have hcov : E = ⋃ n : ℕ, E ∩ ball x₀ n := by
    ext z
    simp only [mem_iUnion, mem_inter_iff, mem_ball]
    constructor
    · intro hz
      obtain ⟨n, hn⟩ := exists_nat_gt (dist z x₀)
      exact ⟨n, hz, hn⟩
    · rintro ⟨n, hz, _⟩
      exact hz
  rw [hcov]
  exact measure_iUnion_null fun n ↦ measure_eq_zero_of_isPorous_of_subset_ball hD1 hD hfin
    (hE.mono inter_subset_left) x₀ inter_subset_right

omit [MeasurableSpace X] [OpensMeasurableSpace X] in
theorem isPorous_sphere [BallGeometry X] (x : X) (r : ℝ) : IsPorous (sphere x r) := by
  rcases lt_trichotomy r 0 with hr | rfl | hr
  · refine ⟨1, 1, one_pos, one_pos, fun y hy ↦ ?_⟩
    rw [mem_sphere] at hy
    exact absurd hy (by linarith [dist_nonneg (x := y) (y := x)])
  · refine ⟨1, 1, one_pos, one_pos, fun y hy s hs _ ↦ ?_⟩
    rw [mem_sphere, dist_eq_zero] at hy
    subst hy
    obtain ⟨y', hy'⟩ := exists_dist_eq y hs.le
    refine ⟨y', hy'.le, fun e he ↦ ?_⟩
    rw [mem_sphere, dist_eq_zero] at he
    subst he
    rw [dist_comm, hy', one_mul]
  · refine ⟨1, r, one_pos, hr, fun y hy s hs hsr ↦ ?_⟩
    rw [mem_sphere] at hy
    obtain ⟨y', h1, h2⟩ := BallGeometry.exists_between y x s hs.le (by rw [hy]; exact hsr)
    refine ⟨y', h1, fun e he ↦ ?_⟩
    rw [mem_sphere] at he
    have := dist_triangle e y' x
    rw [hy] at h2
    rw [one_mul, dist_comm]
    linarith

theorem IsLocDoublingM.measure_sphere [BallGeometry X] [TopologicalSpace.SeparableSpace X]
    {μ : Measure X} (hd : IsLocDoublingM μ) (hfin : ∀ x : X, ∀ r : ℝ, μ (ball x r) < ∞)
    (x : X) (r : ℝ) : μ (sphere x r) = 0 :=
  hd.measure_eq_zero_of_isPorous hfin (isPorous_sphere x r)

theorem IsLocDoublingM.measure_closedBall [BallGeometry X] [TopologicalSpace.SeparableSpace X]
    {μ : Measure X} (hd : IsLocDoublingM μ) (hfin : ∀ x : X, ∀ r : ℝ, μ (ball x r) < ∞)
    (x : X) (r : ℝ) : μ (closedBall x r) = μ (ball x r) := by
  refine le_antisymm ?_ (measure_mono ball_subset_closedBall)
  calc μ (closedBall x r) ≤ μ (ball x r ∪ sphere x r) := by
        refine measure_mono fun z hz ↦ ?_
        rw [mem_closedBall] at hz
        rcases hz.lt_or_eq with h | h
        · exact Or.inl h
        · exact Or.inr h
    _ ≤ μ (ball x r) + μ (sphere x r) := measure_union_le _ _
    _ = μ (ball x r) := by rw [hd.measure_sphere hfin, add_zero]

omit [MeasurableSpace X] [OpensMeasurableSpace X] in
theorem monotone_ball_sub (x : X) (r : ℝ) :
    Monotone fun n : ℕ ↦ ball x (r - 1 / ((n : ℝ) + 1)) := by
  intro n m hnm
  apply ball_subset_ball
  have : (n : ℝ) ≤ m := by exact_mod_cast hnm
  have h1 : 1 / ((m : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) := by gcongr
  linarith

omit [MeasurableSpace X] [OpensMeasurableSpace X] in
theorem iUnion_ball_sub (x : X) (r : ℝ) :
    ⋃ n : ℕ, ball x (r - 1 / ((n : ℝ) + 1)) = ball x r := by
  ext z
  simp only [mem_iUnion, mem_ball]
  constructor
  · rintro ⟨n, hn⟩
    have : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  · intro hz
    have hpos : 0 < r - dist z x := by linarith
    obtain ⟨n, hn⟩ := exists_nat_gt (1 / (r - dist z x))
    refine ⟨n, ?_⟩
    have h1 : 1 / ((n : ℝ) + 1) < r - dist z x := by
      rw [div_lt_iff₀ (by positivity)]
      rw [div_lt_iff₀ hpos] at hn
      nlinarith
    linarith

omit [MeasurableSpace X] [OpensMeasurableSpace X] in
theorem antitone_ball_add (x : X) (r : ℝ) :
    Antitone fun n : ℕ ↦ ball x (r + 1 / ((n : ℝ) + 1)) := by
  intro n m hnm
  apply ball_subset_ball
  have : (n : ℝ) ≤ m := by exact_mod_cast hnm
  have h1 : 1 / ((m : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) := by gcongr
  linarith

omit [MeasurableSpace X] [OpensMeasurableSpace X] in
theorem iInter_ball_add (x : X) (r : ℝ) :
    ⋂ n : ℕ, ball x (r + 1 / ((n : ℝ) + 1)) = closedBall x r := by
  ext z
  simp only [mem_iInter, mem_ball, mem_closedBall]
  constructor
  · intro h
    by_contra hc
    rw [not_le] at hc
    have hpos : 0 < dist z x - r := by linarith
    obtain ⟨n, hn⟩ := exists_nat_gt (1 / (dist z x - r))
    have h1 : 1 / ((n : ℝ) + 1) < dist z x - r := by
      rw [div_lt_iff₀ (by positivity)]
      rw [div_lt_iff₀ hpos] at hn
      nlinarith
    linarith [h n]
  · intro hz n
    have : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith

theorem IsLocDoublingM.continuous_measure_ball [BallGeometry X]
    [TopologicalSpace.SeparableSpace X] {μ : Measure X} (hd : IsLocDoublingM μ)
    (hfin : ∀ x : X, ∀ r : ℝ, μ (ball x r) < ∞) (x : X) :
    Continuous fun r : ℝ ↦ μ (ball x r) := by
  rw [continuous_iff_continuousAt]
  intro r₀
  have hleft : Filter.Tendsto (fun n : ℕ ↦ μ (ball x (r₀ - 1 / ((n : ℝ) + 1)))) Filter.atTop
      (nhds (μ (ball x r₀))) := by
    have := tendsto_measure_iUnion_atTop (μ := μ) (monotone_ball_sub x r₀)
    rwa [iUnion_ball_sub] at this
  have hright : Filter.Tendsto (fun n : ℕ ↦ μ (ball x (r₀ + 1 / ((n : ℝ) + 1)))) Filter.atTop
      (nhds (μ (ball x r₀))) := by
    have := tendsto_measure_iInter_atTop (μ := μ)
      (fun n ↦ measurableSet_ball.nullMeasurableSet) (antitone_ball_add x r₀)
      ⟨0, (hfin x _).ne⟩
    rwa [iInter_ball_add, hd.measure_closedBall hfin] at this
  unfold ContinuousAt
  refine tendsto_order.2 ⟨fun a ha ↦ ?_, fun b hb ↦ ?_⟩
  · obtain ⟨n, hn⟩ := (hleft.eventually (lt_mem_nhds ha)).exists
    have hpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
    have hev : ∀ᶠ r in nhds r₀, r₀ - 1 / ((n : ℝ) + 1) < r := lt_mem_nhds (by linarith)
    exact hev.mono fun r hr ↦ hn.trans_le (measure_mono (ball_subset_ball hr.le))
  · obtain ⟨n, hn⟩ := (hright.eventually (gt_mem_nhds hb)).exists
    have hpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
    have hev : ∀ᶠ r in nhds r₀, r < r₀ + 1 / ((n : ℝ) + 1) := gt_mem_nhds (by linarith)
    exact hev.mono fun r hr ↦ (measure_mono (ball_subset_ball hr.le)).trans_lt hn

/-! ### The mass radius -/

omit [OpensMeasurableSpace X] in
theorem massRadiusM_le {μ : Measure X} {x : X} {R : ℝ} (hR : 0 < R) (h : 1 ≤ μ (ball x R)) :
    massRadiusM μ x ≤ R :=
  csInf_le ⟨0, fun _ hr ↦ hr.1.le⟩ ⟨hR, h⟩

omit [OpensMeasurableSpace X] in
theorem massRadiusM_nonneg (μ : Measure X) (x : X) : 0 ≤ massRadiusM μ x :=
  Real.sInf_nonneg fun _ hr ↦ hr.1.le

omit [OpensMeasurableSpace X] in
theorem measure_ball_lt_one_of_lt_massRadiusM' {μ : Measure X} {x : X} {r : ℝ}
    (hr : r < massRadiusM μ x) : μ (ball x r) < 1 := by
  by_cases hr0 : r ≤ 0
  · rw [ball_eq_empty.2 hr0, measure_empty]
    exact zero_lt_one
  rw [not_le] at hr0
  by_contra h
  rw [not_lt] at h
  exact absurd (massRadiusM_le hr0 h) (not_le.2 hr)

omit [OpensMeasurableSpace X] in
theorem measure_ball_massRadiusM_le_one (μ : Measure X) (x : X) :
    μ (ball x (massRadiusM μ x)) ≤ 1 := by
  have := tendsto_measure_iUnion_atTop (μ := μ) (monotone_ball_sub x (massRadiusM μ x))
  rw [iUnion_ball_sub] at this
  refine le_of_tendsto' this fun n ↦ (measure_ball_lt_one_of_lt_massRadiusM' ?_).le
  have : 0 < 1 / ((n : ℝ) + 1) := by positivity
  linarith

omit [OpensMeasurableSpace X] in
theorem one_le_measure_ball_of_massRadiusM_lt {μ : Measure X} {x : X}
    (hne : ∃ r, 0 < r ∧ 1 ≤ μ (ball x r)) {r : ℝ} (hr : massRadiusM μ x < r) :
    1 ≤ μ (ball x r) := by
  obtain ⟨r', hr'S, hr'r⟩ := exists_lt_of_csInf_lt (s := {r | 0 < r ∧ 1 ≤ μ (ball x r)}) hne hr
  exact hr'S.2.trans (measure_mono (ball_subset_ball hr'r.le))

omit [OpensMeasurableSpace X] in
theorem measure_ball_lt_one_of_lt_massRadiusM {μ : Measure X} {x : X} {r : ℝ}
    (hr : r < massRadiusM μ x) : μ (ball x r) < 1 :=
  measure_ball_lt_one_of_lt_massRadiusM' hr

theorem one_le_measure_closedBall_massRadiusM {μ : Measure X} {x : X}
    (hfin : ∀ r, μ (ball x r) < ∞) (hne : ∃ r, 0 < r ∧ 1 ≤ μ (ball x r)) :
    1 ≤ μ (closedBall x (massRadiusM μ x)) := by
  have := tendsto_measure_iInter_atTop (μ := μ)
    (fun n ↦ measurableSet_ball.nullMeasurableSet) (antitone_ball_add x (massRadiusM μ x))
    ⟨0, (hfin _).ne⟩
  rw [iInter_ball_add] at this
  refine ge_of_tendsto' this fun n ↦ one_le_measure_ball_of_massRadiusM_lt hne ?_
  have : 0 < 1 / ((n : ℝ) + 1) := by positivity
  linarith

theorem IsLocDoublingM.massRadiusM_pos [BallGeometry X] {μ : Measure X}
    (hd : IsLocDoublingM μ) (hfin : ∀ x : X, ∀ r : ℝ, μ (ball x r) < ∞) {x : X}
    (hne : ∃ r, 0 < r ∧ 1 ≤ μ (ball x r)) : 0 < massRadiusM μ x := by
  have htend := tendsto_measure_iInter_atTop (μ := μ)
    (fun n ↦ measurableSet_ball.nullMeasurableSet) (antitone_ball_add x 0) ⟨0, (hfin x _).ne⟩
  rw [iInter_ball_add, closedBall_zero, hd.measure_singleton hfin x] at htend
  obtain ⟨n, hn⟩ := (htend.eventually (gt_mem_nhds zero_lt_one)).exists
  simp only [Function.comp_apply, zero_add] at hn
  have hle : 1 / ((n : ℝ) + 1) ≤ massRadiusM μ x := by
    refine le_csInf hne fun r hr ↦ ?_
    by_contra h
    rw [not_le] at h
    exact absurd (hr.2.trans (measure_mono (ball_subset_ball h.le))) (not_le.2 hn)
  have : 0 < 1 / ((n : ℝ) + 1) := by positivity
  linarith

theorem IsLocDoublingM.measure_ball_massRadiusM [BallGeometry X]
    [TopologicalSpace.SeparableSpace X] {μ : Measure X} (hd : IsLocDoublingM μ)
    (hfin : ∀ x : X, ∀ r : ℝ, μ (ball x r) < ∞) {x : X}
    (hne : ∃ r, 0 < r ∧ 1 ≤ μ (ball x r)) : μ (ball x (massRadiusM μ x)) = 1 := by
  refine le_antisymm (measure_ball_massRadiusM_le_one μ x) ?_
  rw [← hd.measure_closedBall hfin]
  exact one_le_measure_closedBall_massRadiusM (hfin x) hne

omit [OpensMeasurableSpace X] in
theorem lipschitzWith_massRadiusM {μ : Measure X} (hne : ∀ x : X, ∃ r, 0 < r ∧ 1 ≤ μ (ball x r)) :
    LipschitzWith 1 (massRadiusM μ) := by
  have key : ∀ x y, massRadiusM μ y ≤ massRadiusM μ x + dist x y := by
    intro x y
    have : massRadiusM μ y - dist x y ≤ massRadiusM μ x := by
      refine le_csInf (hne x) ?_
      rintro r ⟨hr, hr1⟩
      have hsub : ball x r ⊆ ball y (r + dist x y) := by
        intro z hz
        rw [mem_ball] at hz ⊢
        have := dist_triangle z x y
        linarith
      have : massRadiusM μ y ≤ r + dist x y :=
        massRadiusM_le (by positivity) (hr1.trans (measure_mono hsub))
      linarith
    linarith
  exact LipschitzWith.of_le_add fun x y ↦ by
    have := key y x
    rwa [dist_comm] at this

omit [OpensMeasurableSpace X] in
/-- `ρ(y) ≤ ρ(x) + d(x,y)`. -/
theorem massRadiusM_le_add_dist {μ : Measure X} (hne : ∀ x : X, ∃ r, 0 < r ∧ 1 ≤ μ (ball x r))
    (x y : X) : massRadiusM μ y ≤ massRadiusM μ x + dist x y := by
  have := (lipschitzWith_massRadiusM hne).dist_le_mul y x
  rw [NNReal.coe_one, one_mul, Real.dist_eq, dist_comm y x] at this
  linarith [le_abs_self (massRadiusM μ y - massRadiusM μ x)]

/-- `μ(B(x,r)) ≍ (r/ρ(x))^{s or δ}` for `ρ(x) ≤ r ≤ R₁`. -/
theorem IsLocDoublingM.measure_ball_massRadiusM_bounds [BallGeometry X]
    [TopologicalSpace.SeparableSpace X] {μ : Measure X} (hd : IsLocDoublingM μ)
    (hfin : ∀ x : X, ∀ r : ℝ, μ (ball x r) < ∞)
    (hm : ∃ R : ℝ, 0 < R ∧ ∀ x : X, 1 ≤ μ (ball x R)) (R₁ : ℝ) :
    ∃ c C δ s : ℝ, 0 < c ∧ 0 < C ∧ 0 < δ ∧ 0 < s ∧ ∀ (x : X) (r : ℝ),
      massRadiusM μ x ≤ r → r ≤ R₁ →
        ENNReal.ofReal (c * (r / massRadiusM μ x) ^ δ) ≤ μ (ball x r) ∧
        μ (ball x r) ≤ ENNReal.ofReal (C * (r / massRadiusM μ x) ^ s) := by
  obtain ⟨c, δ, hc, hδ, hlow⟩ := hd.rpow_le_measure_ball R₁
  obtain ⟨C, s, hC, hs, hup⟩ := hd.measure_ball_le_rpow R₁
  obtain ⟨R, hR, hRm⟩ := hm
  refine ⟨c, C, δ, s, hc, hC, hδ, hs, fun x r hρr hrR ↦ ?_⟩
  have hne : ∃ r, 0 < r ∧ 1 ≤ μ (ball x r) := ⟨R, hR, hRm x⟩
  have hρ := hd.massRadiusM_pos hfin hne
  have h1 := hd.measure_ball_massRadiusM hfin hne
  have hxx : dist x x ≤ r := by rw [dist_self]; linarith
  constructor
  · simpa [h1] using hlow x x r (massRadiusM μ x) hρ hρr hrR hxx
  · simpa [h1] using hup x x r (massRadiusM μ x) hρ hρr hrR hxx

/-- **Claim 1**. -/
theorem IsLocDoublingM.claim1 [BallGeometry X] {μ : Measure X} (hd : IsLocDoublingM μ)
    (hfin : ∀ x : X, ∀ r : ℝ, μ (ball x r) < ∞)
    (hm : ∃ R : ℝ, 0 < R ∧ ∀ x : X, 1 ≤ μ (ball x R)) (K : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x y : X,
      dist x y ≤ K * max (massRadiusM μ x) (massRadiusM μ y) →
        massRadiusM μ x ≤ C * massRadiusM μ y := by
  obtain ⟨R, hR, hRm⟩ := hm
  set K' := max K 0 with hK'def
  have hK' : 0 ≤ K' := le_max_right _ _
  obtain ⟨c, δ, hc, hδ, hlow⟩ := hd.rpow_le_measure_ball ((K' + 1) * R)
  obtain ⟨Cu, s, hCu, hs, hup⟩ := hd.measure_ball_le_rpow ((K' + 1) * R)
  set C₂ := 2 * (Cu * (K' + 1) ^ s / c) ^ (1 / δ) with hC₂def
  refine ⟨max 2 C₂, lt_max_of_lt_left two_pos, fun x y hxy ↦ ?_⟩
  have hnex : ∃ r, 0 < r ∧ 1 ≤ μ (ball x r) := ⟨R, hR, hRm x⟩
  have hney : ∃ r, 0 < r ∧ 1 ≤ μ (ball y r) := ⟨R, hR, hRm y⟩
  have hρx := hd.massRadiusM_pos hfin hnex
  have hρy := hd.massRadiusM_pos hfin hney
  have hρxR : massRadiusM μ x ≤ R := massRadiusM_le hR (hRm x)
  set ρx := massRadiusM μ x with hρxdef
  set ρy := massRadiusM μ y with hρydef
  by_cases h2 : ρx ≤ 2 * ρy
  · exact h2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hρy.le)
  rw [not_le] at h2
  have hmax : max ρx ρy = ρx := max_eq_left (by linarith)
  have hd' : dist x y ≤ K' * ρx := by
    rw [hmax] at hxy
    exact hxy.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hρx.le)
  have hy2 : 1 ≤ μ (ball y (2 * ρy)) := one_le_measure_ball_of_massRadiusM_lt hney (by linarith)
  have hRK : R ≤ (K' + 1) * R := by nlinarith
  have hL := hlow y y ρx (2 * ρy) (by positivity) h2.le (hρxR.trans hRK)
    (by rw [dist_self]; positivity)
  have hsub : ball y ρx ⊆ ball x ((K' + 1) * ρx) := by
    intro z hz
    rw [mem_ball] at hz ⊢
    have := dist_triangle z y x
    rw [dist_comm y x] at this
    linarith
  have hU := hup x x ((K' + 1) * ρx) ρx hρx (by nlinarith) (by nlinarith)
    (by rw [dist_self]; positivity)
  have hx1 : μ (ball x ρx) ≤ 1 := measure_ball_massRadiusM_le_one μ x
  have hchain : ENNReal.ofReal (c * (ρx / (2 * ρy)) ^ δ) ≤ ENNReal.ofReal (Cu * (K' + 1) ^ s) := by
    calc ENNReal.ofReal (c * (ρx / (2 * ρy)) ^ δ)
        ≤ ENNReal.ofReal (c * (ρx / (2 * ρy)) ^ δ) * μ (ball y (2 * ρy)) :=
          le_mul_of_one_le_right' hy2
      _ ≤ μ (ball y ρx) := hL
      _ ≤ μ (ball x ((K' + 1) * ρx)) := measure_mono hsub
      _ ≤ ENNReal.ofReal (Cu * ((K' + 1) * ρx / ρx) ^ s) * μ (ball x ρx) := hU
      _ ≤ ENNReal.ofReal (Cu * ((K' + 1) * ρx / ρx) ^ s) * 1 := by gcongr
      _ = ENNReal.ofReal (Cu * (K' + 1) ^ s) := by
          rw [mul_one, mul_div_assoc, div_self hρx.ne', mul_one]
  have hreal : c * (ρx / (2 * ρy)) ^ δ ≤ Cu * (K' + 1) ^ s :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hchain
  have h3 : ρx / (2 * ρy) ≤ (Cu * (K' + 1) ^ s / c) ^ (1 / δ) := by
    have h4 : (ρx / (2 * ρy)) ^ δ ≤ Cu * (K' + 1) ^ s / c := by
      rw [le_div_iff₀ hc]
      linarith
    calc ρx / (2 * ρy) = ((ρx / (2 * ρy)) ^ δ) ^ (1 / δ) := by
          rw [← Real.rpow_mul (by positivity), mul_one_div_cancel hδ.ne', Real.rpow_one]
      _ ≤ _ := Real.rpow_le_rpow (by positivity) h4 (by positivity)
  rw [div_le_iff₀ (by positivity)] at h3
  calc ρx ≤ (Cu * (K' + 1) ^ s / c) ^ (1 / δ) * (2 * ρy) := h3
    _ = C₂ * ρy := by rw [hC₂def]; ring
    _ ≤ max 2 C₂ * ρy := mul_le_mul_of_nonneg_right (le_max_right _ _) hρy.le

/-- Decay of `ρ(ζ)/d(z,ζ)`, power form (proved before Lemma 3, which uses it). -/
theorem IsLocDoublingM.massRadiusM_div_dist_le_aux [BallGeometry X] {μ : Measure X}
    (hd : IsLocDoublingM μ) (hfin : ∀ x : X, ∀ r : ℝ, μ (ball x r) < ∞)
    (hm : ∃ R : ℝ, 0 < R ∧ ∀ x : X, 1 ≤ μ (ball x R)) (M₀ : ℝ) :
    ∃ C α : ℝ, 0 < C ∧ 0 < α ∧ α ≤ 1 ∧ ∀ z ζ : X, massRadiusM μ z ≤ dist z ζ → dist z ζ ≤ M₀ →
      massRadiusM μ ζ / dist z ζ ≤ C * (massRadiusM μ z / dist z ζ) ^ α := by
  obtain ⟨R, hR, hRm⟩ := hm
  have hne : ∀ x : X, ∃ r, 0 < r ∧ 1 ≤ μ (ball x r) := fun x ↦ ⟨R, hR, hRm x⟩
  obtain ⟨CU, s, hCU, hs, hup⟩ := hd.measure_ball_le_rpow (3 * M₀)
  obtain ⟨c, δ, hc, hδ, hlow⟩ := hd.rpow_le_measure_ball (3 * M₀)
  set α := min 1 (δ / s) with hαdef
  have hα : 0 < α := lt_min one_pos (by positivity)
  refine ⟨3 * (CU / c) ^ (1 / s), α, by positivity, hα, min_le_left _ _,
    fun z ζ hzd hdM ↦ ?_⟩
  set d := dist z ζ with hddef
  set ρz := massRadiusM μ z with hρzdef
  set ρζ := massRadiusM μ ζ with hρζdef
  have hρz : 0 < ρz := hd.massRadiusM_pos hfin (hne z)
  have hρζ : 0 < ρζ := hd.massRadiusM_pos hfin (hne ζ)
  have hdpos : 0 < d := hρz.trans_le hzd
  have hlip : ρζ ≤ ρz + d := massRadiusM_le_add_dist hne z ζ
  have hU := hup z ζ (3 * d) ρζ hρζ (by linarith) (by linarith) (by linarith)
  have hL := hlow z z (3 * d) (2 * ρz) (by positivity) (by linarith) (by linarith)
    (by rw [dist_self]; positivity)
  have h1 : μ (ball ζ ρζ) ≤ 1 := measure_ball_massRadiusM_le_one μ ζ
  have h2 : 1 ≤ μ (ball z (2 * ρz)) := one_le_measure_ball_of_massRadiusM_lt (hne z) (by linarith)
  set P := 3 * d / ρζ with hPdef
  set Q := 3 * d / (2 * ρz) with hQdef
  have hPpos : 0 < P := by positivity
  have hQpos : 0 < Q := by positivity
  have hchain : ENNReal.ofReal (c * Q ^ δ) ≤ ENNReal.ofReal (CU * P ^ s) := by
    calc ENNReal.ofReal (c * Q ^ δ) ≤ ENNReal.ofReal (c * Q ^ δ) * μ (ball z (2 * ρz)) :=
          le_mul_of_one_le_right' h2
      _ ≤ μ (ball z (3 * d)) := hL
      _ ≤ ENNReal.ofReal (CU * P ^ s) * μ (ball ζ ρζ) := hU
      _ ≤ ENNReal.ofReal (CU * P ^ s) * 1 := by gcongr
      _ = ENNReal.ofReal (CU * P ^ s) := mul_one _
  have hreal : c * Q ^ δ ≤ CU * P ^ s := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hchain
  have hPQ : (c / CU) ^ (1 / s) * Q ^ (δ / s) ≤ P := by
    have h3 : c / CU * Q ^ δ ≤ P ^ s := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hCU]
      linarith
    have h4 := Real.rpow_le_rpow (by positivity) h3 (by positivity : 0 ≤ 1 / s)
    rwa [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hQpos.le,
      ← Real.rpow_mul hPpos.le, mul_one_div_cancel hs.ne', Real.rpow_one, mul_one_div] at h4
  have hQinv : Q⁻¹ ≤ ρz / d := by
    rw [hQdef, inv_div, div_le_div_iff₀ (by positivity) hdpos]
    nlinarith
  have hv1 : ρz / d ≤ 1 := (div_le_one hdpos).2 hzd
  have hvpos : 0 < ρz / d := by positivity
  have hApos : 0 < (c / CU) ^ (1 / s) := by positivity
  have hBpos : 0 < Q ^ (δ / s) := by positivity
  calc ρζ / d = 3 / P := by rw [hPdef]; field_simp
    _ ≤ 3 / ((c / CU) ^ (1 / s) * Q ^ (δ / s)) :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity) hPQ
    _ = 3 * (CU / c) ^ (1 / s) * (Q⁻¹) ^ (δ / s) := by
        rw [Real.inv_rpow hQpos.le, ← inv_div c CU, Real.inv_rpow (by positivity)]
        field_simp
    _ ≤ 3 * (CU / c) ^ (1 / s) * (ρz / d) ^ (δ / s) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hQinv (by positivity))
          (by positivity)
    _ ≤ 3 * (CU / c) ^ (1 / s) * (ρz / d) ^ α :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_ge hvpos hv1 (min_le_right _ _)) (by positivity)

/-- Decay, geometric form (proved before Lemma 3, which uses it). -/
theorem IsLocDoublingM.decay_aux [BallGeometry X] {μ : Measure X}
    (hd : IsLocDoublingM μ) (hfin : ∀ x : X, ∀ r : ℝ, μ (ball x r) < ∞)
    (hm : ∃ R : ℝ, 0 < R ∧ ∀ x : X, 1 ≤ μ (ball x R)) (M₀ : ℝ) :
    ∃ C θ : ℝ, 0 < C ∧ 0 < θ ∧ θ < 1 ∧ ∀ (z ζ : X) (n : ℕ),
      2 ^ n * massRadiusM μ z ≤ dist z ζ → dist z ζ ≤ M₀ →
        massRadiusM μ ζ / dist z ζ ≤ C * θ ^ n := by
  obtain ⟨C, α, hC, hα, _, h⟩ := hd.massRadiusM_div_dist_le_aux hfin hm M₀
  obtain ⟨R, hR, hRm⟩ := hm
  have hne : ∀ x : X, ∃ r, 0 < r ∧ 1 ≤ μ (ball x r) := fun x ↦ ⟨R, hR, hRm x⟩
  refine ⟨C, (2 : ℝ) ^ (-α), hC, by positivity,
    Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith), fun z ζ n hn hM ↦ ?_⟩
  have hρz := hd.massRadiusM_pos hfin (hne z)
  have h2n : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ one_le_two
  have hle : massRadiusM μ z ≤ dist z ζ := (le_mul_of_one_le_left hρz.le h2n).trans hn
  have hdpos : 0 < dist z ζ := hρz.trans_le hle
  refine (h z ζ hle hM).trans (mul_le_mul_of_nonneg_left ?_ hC.le)
  have hv : massRadiusM μ z / dist z ζ ≤ ((2 : ℝ) ^ n)⁻¹ := by
    rw [div_le_iff₀ hdpos, ← div_eq_inv_mul, le_div_iff₀ (by positivity)]
    linarith
  calc (massRadiusM μ z / dist z ζ) ^ α ≤ (((2 : ℝ) ^ n)⁻¹) ^ α :=
        Real.rpow_le_rpow (by positivity) hv hα.le
    _ = ((2 : ℝ) ^ (-α)) ^ n := by
      rw [Real.inv_rpow (by positivity), ← Real.rpow_natCast (2 : ℝ) n,
        ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast ((2 : ℝ) ^ (-α)) n,
        ← Real.rpow_mul (by norm_num), ← Real.rpow_neg (by norm_num)]
      congr 1
      ring

/-- Fine part of Lemma 3: integration over `ball w 1`, uniformly in `w`. -/
theorem IsLocDoublingM.lemma3_fine [BallGeometry X] {μ : Measure X} (hd : IsLocDoublingM μ)
    (hfin : ∀ x : X, ∀ r : ℝ, μ (ball x r) < ∞)
    (hm : ∃ R : ℝ, 0 < R ∧ ∀ x : X, 1 ≤ μ (ball x R)) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ δ : ℝ, 0 < δ → ∃ CF : ℝ≥0∞, CF ≠ ∞ ∧ ∀ w : X,
      ∫⁻ z in ball w 1,
        ENNReal.ofReal ((massRadiusM μ z / max (dist z w) (δ * massRadiusM μ w)) ^ m) ∂μ
          ≤ CF := by
  obtain ⟨C, θ, hC, hθ, hθ1, hdecay⟩ := hd.decay_aux hfin hm 1
  obtain ⟨D, hD1, hD⟩ := hd.measure_ball_le_pow 1
  obtain ⟨R, hR, hRm⟩ := hm
  have hne : ∀ x : X, ∃ r, 0 < r ∧ 1 ≤ μ (ball x r) := fun x ↦ ⟨R, hR, hRm x⟩
  have hD1' : (1 : ℝ) ≤ D := by exact_mod_cast hD1
  have hDpos : (0 : ℝ) < D := by linarith
  obtain ⟨m₀, hm₀⟩ := exists_pow_lt_of_lt_one (by positivity : (0 : ℝ) < 1 / D) hθ1
  refine ⟨m₀, fun m hm δ hδ ↦ ?_⟩
  have hθm : θ ^ m * D < 1 := by
    have h1 : θ ^ m ≤ θ ^ m₀ := pow_le_pow_of_le_one hθ.le hθ1.le hm
    have h2 : θ ^ m₀ * D < 1 := by rwa [lt_div_iff₀ hDpos] at hm₀
    nlinarith
  set q : ℝ≥0∞ := ENNReal.ofReal (θ ^ m) * D with hqdef
  have hq : q < 1 := by
    rw [hqdef, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_lt_one.2 hθm
  set a : ℝ≥0∞ := ENNReal.ofReal ((2 / δ) ^ m) with hadef
  set b : ℝ≥0∞ := ENNReal.ofReal (C ^ m) * (D : ℝ≥0∞) ^ 2 with hbdef
  refine ⟨a + b * (1 - q)⁻¹, ?_, fun w ↦ ?_⟩
  · exact ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.mul_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top))
      (ENNReal.inv_ne_top.2 (tsub_pos_iff_lt.2 hq).ne')⟩
  set ρw := massRadiusM μ w with hρwdef
  have hρw : 0 < ρw := hd.massRadiusM_pos hfin (hne w)
  set r : ℕ → ℝ := fun n ↦ min (2 ^ (n + 1) * ρw) 1 with hrdef
  set g₀ : X → ℝ≥0∞ := (ball w ρw).indicator (fun _ ↦ a) with hg₀def
  set g : ℕ → X → ℝ≥0∞ := fun n ↦
    (ball w (r n)).indicator (fun _ ↦ ENNReal.ofReal (C ^ m) * ENNReal.ofReal (θ ^ m) ^ n)
    with hgdef
  have hpt : ∀ z ∈ ball w 1,
      ENNReal.ofReal ((massRadiusM μ z / max (dist z w) (δ * ρw)) ^ m) ≤
        g₀ z + ∑' n, g n z := by
    intro z hz
    rw [mem_ball] at hz
    have hρz : 0 ≤ massRadiusM μ z := massRadiusM_nonneg μ z
    have hmaxpos : 0 < max (dist z w) (δ * ρw) := lt_max_of_lt_right (by positivity)
    by_cases hdw : dist z w < ρw
    · have hz' : z ∈ ball w ρw := hdw
      have hlip : massRadiusM μ z ≤ ρw + dist z w := by
        have := massRadiusM_le_add_dist hne w z
        rwa [dist_comm] at this
      have hratio : massRadiusM μ z / max (dist z w) (δ * ρw) ≤ 2 / δ := by
        rw [div_le_div_iff₀ hmaxpos hδ]
        have := le_max_right (dist z w) (δ * ρw)
        nlinarith
      calc ENNReal.ofReal ((massRadiusM μ z / max (dist z w) (δ * ρw)) ^ m) ≤ a :=
            ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by positivity) hratio m)
        _ = g₀ z := by simp only [hg₀def, indicator_of_mem hz']
        _ ≤ g₀ z + ∑' n, g n z := le_self_add
    · rw [not_lt] at hdw
      have hdpos : 0 < dist z w := hρw.trans_le hdw
      have hq1 : 1 ≤ dist z w / ρw := (one_le_div hρw).2 hdw
      set L := Real.logb 2 (dist z w / ρw) with hLdef
      have hL0 : 0 ≤ L := Real.logb_nonneg one_lt_two hq1
      set n := ⌊L⌋₊ with hndef
      have h2L : (2 : ℝ) ^ L = dist z w / ρw := Real.rpow_logb (by norm_num) (by norm_num)
        (by positivity)
      have hn1 : 2 ^ n * ρw ≤ dist z w := by
        have : (2 : ℝ) ^ n ≤ dist z w / ρw := by
          calc (2 : ℝ) ^ n = 2 ^ (n : ℝ) := (Real.rpow_natCast 2 n).symm
            _ ≤ 2 ^ L := Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.floor_le hL0)
            _ = _ := h2L
        rwa [le_div_iff₀ hρw] at this
      have hn2 : dist z w < 2 ^ (n + 1) * ρw := by
        have : dist z w / ρw < 2 ^ (n + 1) := by
          calc dist z w / ρw = 2 ^ L := h2L.symm
            _ < 2 ^ ((n + 1 : ℕ) : ℝ) := Real.rpow_lt_rpow_of_exponent_lt one_lt_two (by
                push_cast
                exact Nat.lt_floor_add_one L)
            _ = 2 ^ (n + 1) := Real.rpow_natCast 2 (n + 1)
        rwa [div_lt_iff₀ hρw] at this
      have hdec := hdecay w z n (by rw [dist_comm]; exact hn1) (by rw [dist_comm]; exact hz.le)
      rw [dist_comm] at hdec
      have hratio : massRadiusM μ z / max (dist z w) (δ * ρw) ≤ C * θ ^ n :=
        (div_le_div_of_nonneg_left hρz hdpos (le_max_left _ _)).trans hdec
      have hz' : z ∈ ball w (r n) := by
        rw [mem_ball]
        exact lt_min hn2 hz
      calc ENNReal.ofReal ((massRadiusM μ z / max (dist z w) (δ * ρw)) ^ m)
          ≤ ENNReal.ofReal ((C * θ ^ n) ^ m) :=
            ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by positivity) hratio m)
        _ = ENNReal.ofReal (C ^ m) * ENNReal.ofReal (θ ^ m) ^ n := by
            rw [mul_pow, ← pow_mul, mul_comm n m, pow_mul, ENNReal.ofReal_mul (by positivity),
              ENNReal.ofReal_pow (pow_nonneg hθ.le m) n]
        _ = g n z := by simp only [hgdef, indicator_of_mem hz']
        _ ≤ ∑' k, g k z := ENNReal.le_tsum (f := fun k ↦ g k z) n
        _ ≤ g₀ z + ∑' k, g k z := le_add_self
  have hmass : ∀ n : ℕ, μ (ball w (r n)) ≤ (D : ℝ≥0∞) ^ (n + 2) := by
    intro n
    have h := hD w w (r n) ρw (n + 1) hρw (min_le_right _ _)
      (by rw [dist_self]; exact le_min (by positivity) zero_le_one) (min_le_left _ _)
    calc μ (ball w (r n)) ≤ (D : ℝ≥0∞) ^ (n + 1 + 1) * μ (ball w ρw) := h
      _ ≤ (D : ℝ≥0∞) ^ (n + 1 + 1) * 1 := by
          gcongr
          exact measure_ball_massRadiusM_le_one μ w
      _ = (D : ℝ≥0∞) ^ (n + 2) := by rw [mul_one]
  calc ∫⁻ z in ball w 1, ENNReal.ofReal ((massRadiusM μ z / max (dist z w) (δ * ρw)) ^ m) ∂μ
      ≤ ∫⁻ z in ball w 1, (g₀ z + ∑' n, g n z) ∂μ := setLIntegral_mono' measurableSet_ball hpt
    _ ≤ ∫⁻ z, (g₀ z + ∑' n, g n z) ∂μ := setLIntegral_le_lintegral _ _
    _ = ∫⁻ z, g₀ z ∂μ + ∑' n, ∫⁻ z, g n z ∂μ := by
        rw [lintegral_add_left (measurable_const.indicator measurableSet_ball),
          lintegral_tsum fun n ↦ (measurable_const.indicator measurableSet_ball).aemeasurable]
    _ ≤ a * μ (ball w ρw) +
          ∑' n, (ENNReal.ofReal (C ^ m) * ENNReal.ofReal (θ ^ m) ^ n) * μ (ball w (r n)) := by
        gcongr with n
        · exact lintegral_indicator_const_le _ _
        · exact lintegral_indicator_const_le _ _
    _ ≤ a * 1 + ∑' n, (ENNReal.ofReal (C ^ m) * ENNReal.ofReal (θ ^ m) ^ n) *
          (D : ℝ≥0∞) ^ (n + 2) := by
        gcongr with n
        · exact measure_ball_massRadiusM_le_one μ w
        · exact hmass n
    _ = a + b * (1 - q)⁻¹ := by
        rw [mul_one, ← ENNReal.tsum_geometric, ← ENNReal.tsum_mul_left]
        congr 1
        congr 1
        ext n
        rw [hbdef, hqdef]
        ring

/-- **Lemma 3**, truncated form (contains the paper's statement on `δρ(w) ≤ d < R₁`). -/
theorem IsLocDoublingM.lemma3 [BallGeometry X] [TopologicalSpace.SeparableSpace X]
    {μ : Measure X} (hd : IsLocDoublingM μ) (hfin : ∀ x : X, ∀ r : ℝ, μ (ball x r) < ∞)
    (hm : ∃ R : ℝ, 0 < R ∧ ∀ x : X, 1 ≤ μ (ball x R)) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ δ R₁ : ℝ, 0 < δ → ∃ C : ℝ≥0, ∀ w : X,
      ∫⁻ z in ball w R₁,
        ENNReal.ofReal ((massRadiusM μ z / max (dist z w) (δ * massRadiusM μ w)) ^ m) ∂μ ≤ C := by
  obtain ⟨m₀, hfine⟩ := hd.lemma3_fine hfin hm
  obtain ⟨R, hR, hRm⟩ := hm
  have hne : ∀ x : X, ∃ r, 0 < r ∧ 1 ≤ μ (ball x r) := fun x ↦ ⟨R, hR, hRm x⟩
  have hρmeas : Measurable (massRadiusM μ) :=
    (lipschitzWith_massRadiusM hne).continuous.measurable
  have hFmeas : ∀ (y : X) (c : ℝ), Measurable fun z ↦
      ENNReal.ofReal ((massRadiusM μ z / max (dist z y) (c * massRadiusM μ y)) ^ m₀) := by
    intro y c
    exact ENNReal.measurable_ofReal.comp ((hρmeas.div
      ((continuous_id.dist continuous_const).measurable.max measurable_const)).pow_const _)
  refine ⟨m₀, fun m hm δ R₁ hδ ↦ ?_⟩
  have hFmeas' : ∀ (y : X) (c : ℝ), Measurable fun z ↦
      ENNReal.ofReal ((massRadiusM μ z / max (dist z y) (c * massRadiusM μ y)) ^ m) := by
    intro y c
    exact ENNReal.measurable_ofReal.comp ((hρmeas.div
      ((continuous_id.dist continuous_const).measurable.max measurable_const)).pow_const _)
  obtain ⟨CF, hCF, hCFw⟩ := hfine m hm δ hδ
  obtain ⟨CF', hCF', hCFw'⟩ := hfine m hm (1 / R) (by positivity)
  obtain ⟨K, hK⟩ := BallGeometry.covering (X := X) R₁ 1 one_pos
  have hfinC : CF + K * CF' ≠ ∞ :=
    ENNReal.add_ne_top.2 ⟨hCF, ENNReal.mul_ne_top (ENNReal.natCast_ne_top K) hCF'⟩
  refine ⟨(CF + K * CF').toNNReal, fun w ↦ ?_⟩
  rw [ENNReal.coe_toNNReal hfinC]
  obtain ⟨s, hs, hcov⟩ := hK w
  have hpt : ∀ z ∈ ball w R₁,
      ENNReal.ofReal ((massRadiusM μ z / max (dist z w) (δ * massRadiusM μ w)) ^ m) ≤
        (ball w 1).indicator (fun z ↦
          ENNReal.ofReal ((massRadiusM μ z / max (dist z w) (δ * massRadiusM μ w)) ^ m)) z +
        ∑ y ∈ s, (ball y 1).indicator (fun z ↦
          ENNReal.ofReal ((massRadiusM μ z / max (dist z y) (1 / R * massRadiusM μ y)) ^ m)) z := by
    intro z hz
    by_cases hz1 : z ∈ ball w 1
    · rw [indicator_of_mem hz1]
      exact le_self_add
    · rw [mem_ball, not_lt] at hz1
      obtain ⟨y, hy, hzy⟩ := mem_iUnion₂.1 (hcov hz)
      have hρz := massRadiusM_nonneg μ z
      have hρy : massRadiusM μ y ≤ R := massRadiusM_le hR (hRm y)
      have hρypos : 0 < massRadiusM μ y := hd.massRadiusM_pos hfin (hne y)
      have hM1 : 1 ≤ max (dist z w) (δ * massRadiusM μ w) := hz1.trans (le_max_left _ _)
      have hM2pos : 0 < max (dist z y) (1 / R * massRadiusM μ y) :=
        lt_max_of_lt_right (by positivity)
      have hM2 : max (dist z y) (1 / R * massRadiusM μ y) ≤ 1 := by
        refine max_le (mem_ball.1 hzy).le ?_
        rw [div_mul_eq_mul_div, one_mul, div_le_one hR]
        exact hρy
      have hratio : massRadiusM μ z / max (dist z w) (δ * massRadiusM μ w) ≤
          massRadiusM μ z / max (dist z y) (1 / R * massRadiusM μ y) :=
        div_le_div_of_nonneg_left hρz hM2pos (hM2.trans hM1)
      calc ENNReal.ofReal ((massRadiusM μ z / max (dist z w) (δ * massRadiusM μ w)) ^ m)
          ≤ ENNReal.ofReal ((massRadiusM μ z / max (dist z y) (1 / R * massRadiusM μ y)) ^ m) :=
            ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by positivity) hratio m)
        _ = (ball y 1).indicator (fun z ↦
              ENNReal.ofReal ((massRadiusM μ z / max (dist z y) (1 / R * massRadiusM μ y)) ^ m))
              z := by rw [indicator_of_mem hzy]
        _ ≤ ∑ y ∈ s, (ball y 1).indicator (fun z ↦
              ENNReal.ofReal ((massRadiusM μ z / max (dist z y) (1 / R * massRadiusM μ y)) ^ m))
              z :=
            Finset.single_le_sum (f := fun y ↦ (ball y 1).indicator (fun z ↦
              ENNReal.ofReal ((massRadiusM μ z / max (dist z y) (1 / R * massRadiusM μ y)) ^ m))
              z) (fun _ _ ↦ zero_le) hy
        _ ≤ _ := le_add_self
  calc ∫⁻ z in ball w R₁,
        ENNReal.ofReal ((massRadiusM μ z / max (dist z w) (δ * massRadiusM μ w)) ^ m) ∂μ
      ≤ ∫⁻ z in ball w R₁, ((ball w 1).indicator (fun z ↦
          ENNReal.ofReal ((massRadiusM μ z / max (dist z w) (δ * massRadiusM μ w)) ^ m)) z +
        ∑ y ∈ s, (ball y 1).indicator (fun z ↦
          ENNReal.ofReal ((massRadiusM μ z / max (dist z y) (1 / R * massRadiusM μ y)) ^ m)) z)
          ∂μ := setLIntegral_mono' measurableSet_ball hpt
    _ ≤ ∫⁻ z, ((ball w 1).indicator (fun z ↦
          ENNReal.ofReal ((massRadiusM μ z / max (dist z w) (δ * massRadiusM μ w)) ^ m)) z +
        ∑ y ∈ s, (ball y 1).indicator (fun z ↦
          ENNReal.ofReal ((massRadiusM μ z / max (dist z y) (1 / R * massRadiusM μ y)) ^ m)) z)
          ∂μ := setLIntegral_le_lintegral _ _
    _ = ∫⁻ z in ball w 1,
          ENNReal.ofReal ((massRadiusM μ z / max (dist z w) (δ * massRadiusM μ w)) ^ m) ∂μ +
        ∑ y ∈ s, ∫⁻ z in ball y 1,
          ENNReal.ofReal ((massRadiusM μ z / max (dist z y) (1 / R * massRadiusM μ y)) ^ m)
            ∂μ := by
        rw [lintegral_add_left ((hFmeas' w δ).indicator measurableSet_ball),
          lintegral_finsetSum _ (fun y _ ↦ (hFmeas' y _).indicator measurableSet_ball),
          lintegral_indicator measurableSet_ball]
        congr 1
        exact Finset.sum_congr rfl fun y _ ↦ lintegral_indicator measurableSet_ball _
    _ ≤ CF + ∑ _y ∈ s, CF' := by
        gcongr with y hy
        · exact hCFw w
        · exact hCFw' y
    _ = CF + s.card * CF' := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ CF + K * CF' := by gcongr

/-- **Lemma 3** as printed (region `δρ(w) ≤ d(z,w) < R₁`). -/
theorem IsLocDoublingM.lemma3_paper [BallGeometry X] [TopologicalSpace.SeparableSpace X]
    {μ : Measure X} (hd : IsLocDoublingM μ) (hfin : ∀ x : X, ∀ r : ℝ, μ (ball x r) < ∞)
    (hm : ∃ R : ℝ, 0 < R ∧ ∀ x : X, 1 ≤ μ (ball x R)) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ δ R₁ : ℝ, 0 < δ → ∃ C : ℝ≥0, ∀ w : X,
      ∫⁻ z in {z | δ * massRadiusM μ w ≤ dist z w ∧ dist z w < R₁},
        ENNReal.ofReal ((massRadiusM μ z / dist z w) ^ m) ∂μ ≤ C := by
  obtain ⟨m₀, h⟩ := hd.lemma3 hfin hm
  refine ⟨m₀, fun m hm δ R₁ hδ ↦ ?_⟩
  obtain ⟨C, hC⟩ := h m hm δ R₁ hδ
  refine ⟨C, fun w ↦ ?_⟩
  have hcont : Continuous fun z ↦ dist z w := continuous_id.dist continuous_const
  have hS : MeasurableSet {z | δ * massRadiusM μ w ≤ dist z w ∧ dist z w < R₁} :=
    (measurableSet_le measurable_const hcont.measurable).inter
      (measurableSet_lt hcont.measurable measurable_const)
  calc ∫⁻ z in {z | δ * massRadiusM μ w ≤ dist z w ∧ dist z w < R₁},
        ENNReal.ofReal ((massRadiusM μ z / dist z w) ^ m) ∂μ
      = ∫⁻ z in {z | δ * massRadiusM μ w ≤ dist z w ∧ dist z w < R₁},
          ENNReal.ofReal ((massRadiusM μ z / max (dist z w) (δ * massRadiusM μ w)) ^ m) ∂μ := by
        refine setLIntegral_congr_fun hS fun z hz ↦ ?_
        rw [max_eq_left hz.1]
    _ ≤ ∫⁻ z in ball w R₁,
          ENNReal.ofReal ((massRadiusM μ z / max (dist z w) (δ * massRadiusM μ w)) ^ m) ∂μ :=
        lintegral_mono_set fun z hz ↦ mem_ball.2 hz.2
    _ ≤ C := hC w

omit [MeasurableSpace X] [OpensMeasurableSpace X] in
/-- Pointwise dyadic bound behind [Chr91, Lemma 2.3]. -/
theorem ofReal_log_le_tsum_indicator (x y : X) {R : ℝ} (hR : 0 < R) :
    ENNReal.ofReal (Real.log (R / dist x y)) ≤
      ∑' k : ℕ, (ball x (R / 2 ^ k)).indicator (fun _ ↦ ENNReal.ofReal (Real.log 2)) y := by
  by_cases hd0 : dist x y = 0
  · rw [hd0, div_zero, Real.log_zero, ENNReal.ofReal_zero]
    exact zero_le
  have hdpos : 0 < dist x y := lt_of_le_of_ne dist_nonneg (Ne.symm hd0)
  by_cases hdR : R ≤ dist x y
  · rw [ENNReal.ofReal_of_nonpos (Real.log_nonpos (by positivity) ((div_le_one hdpos).2 hdR))]
    exact zero_le
  rw [not_le] at hdR
  have hq : 1 < R / dist x y := (one_lt_div hdpos).2 hdR
  set L := Real.logb 2 (R / dist x y) with hLdef
  have hL0 : 0 < L := Real.logb_pos one_lt_two hq
  set n := ⌈L⌉₊ with hndef
  have hmem : ∀ k < n, y ∈ ball x (R / 2 ^ k) := by
    intro k hk
    rw [mem_ball, dist_comm]
    have hkL : (k : ℝ) < L := Nat.lt_ceil.1 hk
    have h2 : (2 : ℝ) ^ k < R / dist x y := by
      calc (2 : ℝ) ^ k = 2 ^ (k : ℝ) := (Real.rpow_natCast 2 k).symm
        _ < 2 ^ L := Real.rpow_lt_rpow_of_exponent_lt one_lt_two hkL
        _ = R / dist x y := Real.rpow_logb (by norm_num) (by norm_num) (by positivity)
    rw [lt_div_iff₀ hdpos] at h2
    rw [lt_div_iff₀ (by positivity)]
    linarith
  calc ENNReal.ofReal (Real.log (R / dist x y)) = ENNReal.ofReal (L * Real.log 2) := by
        rw [hLdef, Real.logb, div_mul_cancel₀ _ (Real.log_pos one_lt_two).ne']
    _ ≤ ENNReal.ofReal (n * Real.log 2) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (Nat.le_ceil L)
          (Real.log_nonneg one_le_two))
    _ = ∑ k ∈ Finset.range n,
          (ball x (R / 2 ^ k)).indicator (fun _ ↦ ENNReal.ofReal (Real.log 2)) y := by
        rw [Finset.sum_congr rfl (fun k hk ↦ indicator_of_mem (hmem k (Finset.mem_range.1 hk)) _),
          Finset.sum_const, Finset.card_range, nsmul_eq_mul,
          ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    _ ≤ ∑' k : ℕ, (ball x (R / 2 ^ k)).indicator (fun _ ↦ ENNReal.ofReal (Real.log 2)) y :=
        ENNReal.sum_le_tsum _

/-- **[Chr91, Lemma 2.3]**. -/
theorem IsLocDoublingM.christ_lemma23 [BallGeometry X] {μ : Measure X}
    (hd : IsLocDoublingM μ) (R₁ : ℝ) :
    ∃ C : ℝ≥0, ∀ (x : X) (R : ℝ), 0 < R → R ≤ R₁ →
      ∫⁻ y in ball x R, ENNReal.ofReal (Real.log (R / dist x y)) ∂μ ≤ C * μ (ball x R) := by
  obtain ⟨η, hη, hη'⟩ := hd.reverse_doubling R₁
  set q : ℝ≥0∞ := (1 + (η : ℝ≥0∞))⁻¹ with hqdef
  have h1η0 : (1 + (η : ℝ≥0∞)) ≠ 0 := (lt_of_lt_of_le one_pos le_self_add).ne'
  have h1ηt : (1 + (η : ℝ≥0∞)) ≠ ∞ := by simp
  have hq1 : q < 1 := by
    refine ENNReal.inv_lt_one.mpr ?_
    have : (0 : ℝ≥0∞) < η := by exact_mod_cast hη
    exact ENNReal.lt_add_right ENNReal.one_ne_top this.ne'
  set c : ℝ≥0∞ := ENNReal.ofReal (Real.log 2) with hcdef
  have hCne : c * (1 - q)⁻¹ ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.inv_ne_top.2 (tsub_pos_iff_lt.2 hq1).ne')
  refine ⟨(c * (1 - q)⁻¹).toNNReal, fun x R hR hRR₁ ↦ ?_⟩
  rw [ENNReal.coe_toNNReal hCne]
  have hstep : ∀ k : ℕ, μ (ball x (R / 2 ^ k)) ≤ q ^ k * μ (ball x R) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have h := hη' x (R / 2 ^ (k + 1)) (by positivity)
        ((div_le_self hR.le (one_le_pow₀ one_le_two)).trans hRR₁)
      rw [show 2 * (R / 2 ^ (k + 1)) = R / 2 ^ k by rw [pow_succ]; field_simp] at h
      have h' : μ (ball x (R / 2 ^ (k + 1))) ≤ q * μ (ball x (R / 2 ^ k)) :=
        (ENNReal.mul_le_iff_le_inv h1η0 h1ηt).mp h
      calc μ (ball x (R / 2 ^ (k + 1))) ≤ q * μ (ball x (R / 2 ^ k)) := h'
        _ ≤ q * (q ^ k * μ (ball x R)) := by gcongr
        _ = q ^ (k + 1) * μ (ball x R) := by ring
  calc ∫⁻ y in ball x R, ENNReal.ofReal (Real.log (R / dist x y)) ∂μ
      ≤ ∫⁻ y in ball x R, ∑' k : ℕ, (ball x (R / 2 ^ k)).indicator (fun _ ↦ c) y ∂μ :=
        lintegral_mono fun y ↦ ofReal_log_le_tsum_indicator x y hR
    _ ≤ ∫⁻ y, ∑' k : ℕ, (ball x (R / 2 ^ k)).indicator (fun _ ↦ c) y ∂μ :=
        setLIntegral_le_lintegral _ _
    _ = ∑' k : ℕ, ∫⁻ y, (ball x (R / 2 ^ k)).indicator (fun _ ↦ c) y ∂μ :=
        lintegral_tsum fun k ↦ (measurable_const.indicator measurableSet_ball).aemeasurable
    _ ≤ ∑' k : ℕ, c * μ (ball x (R / 2 ^ k)) :=
        ENNReal.tsum_le_tsum fun k ↦ lintegral_indicator_const_le _ _
    _ ≤ ∑' k : ℕ, c * (q ^ k * μ (ball x R)) := ENNReal.tsum_le_tsum fun k ↦ by
        gcongr
        exact hstep k
    _ = c * (1 - q)⁻¹ * μ (ball x R) := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, ENNReal.tsum_geometric]
        ring

theorem IsLocDoublingM.integrableOn_log_dist [BallGeometry X] {μ : Measure X}
    (hd : IsLocDoublingM μ) (hfin : ∀ x : X, ∀ r : ℝ, μ (ball x r) < ∞) (x : X) (R : ℝ) :
    IntegrableOn (fun y ↦ Real.log (dist x y)) (ball x R) μ := by
  by_cases hR : R ≤ 0
  · rw [ball_eq_empty.2 hR]
    exact integrableOn_empty
  rw [not_le] at hR
  obtain ⟨C, hC⟩ := hd.christ_lemma23 R
  have hmeas : Measurable fun y ↦ Real.log (dist x y) :=
    Real.measurable_log.comp (continuous_const.dist continuous_id).measurable
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  show ∫⁻ y in ball x R, ‖Real.log (dist x y)‖ₑ ∂μ < ∞
  have hpt : ∀ y ∈ ball x R, ‖Real.log (dist x y)‖ₑ ≤
      ENNReal.ofReal (Real.log (R / dist x y)) + ENNReal.ofReal |Real.log R| := by
    intro y hy
    rw [mem_ball, dist_comm] at hy
    by_cases hd0 : dist x y = 0
    · rw [hd0, Real.log_zero, enorm_zero]
      exact zero_le
    have hdpos : 0 < dist x y := lt_of_le_of_ne dist_nonneg (Ne.symm hd0)
    have hlogq : 0 ≤ Real.log (R / dist x y) := Real.log_nonneg ((one_le_div hdpos).2 hy.le)
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_add hlogq (abs_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [Real.log_div hR.ne' hdpos.ne'] at hlogq ⊢
    rw [abs_le]
    constructor <;> linarith [le_abs_self (Real.log R), neg_abs_le (Real.log R)]
  calc ∫⁻ y in ball x R, ‖Real.log (dist x y)‖ₑ ∂μ
      ≤ ∫⁻ y in ball x R, (ENNReal.ofReal (Real.log (R / dist x y)) +
          ENNReal.ofReal |Real.log R|) ∂μ := setLIntegral_mono' measurableSet_ball hpt
    _ = ∫⁻ y in ball x R, ENNReal.ofReal (Real.log (R / dist x y)) ∂μ +
          ENNReal.ofReal |Real.log R| * μ (ball x R) := by
        rw [lintegral_add_right _ measurable_const, setLIntegral_const]
    _ ≤ C * μ (ball x R) + ENNReal.ofReal |Real.log R| * μ (ball x R) := by
        gcongr
        exact hC x R hR le_rfl
    _ < ∞ := ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.coe_lt_top (hfin x R),
        ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hfin x R)⟩

/-- **Growth**: balls of a fixed large radius have mass `> p`. No doubling needed. -/
theorem exists_radius_lt_measure_ball [BallGeometry X] {μ : Measure X}
    (hm : ∃ R : ℝ, 0 < R ∧ ∀ x : X, 1 ≤ μ (ball x R)) (p : ℝ≥0) :
    ∃ r : ℝ, 0 < r ∧ ∀ x : X, (p : ℝ≥0∞) < μ (ball x r) := by
  obtain ⟨R, hR, hRm⟩ := hm
  set k : ℕ := ⌊p⌋₊ + 1 with hkdef
  refine ⟨2 * k * R, by positivity, fun x ↦ ?_⟩
  have hy : ∀ i : ℕ, ∃ y, dist x y = 2 * i * R := fun i ↦ exists_dist_eq x (by positivity)
  choose y hy using hy
  have key : ∀ i j : ℕ, i < j → 2 * R ≤ dist (y i) (y j) := by
    intro i j hij
    have h1 := dist_triangle x (y i) (y j)
    rw [hy, hy] at h1
    have : (i : ℝ) + 1 ≤ j := by exact_mod_cast hij
    nlinarith
  have hdisj : Set.PairwiseDisjoint (↑(Finset.range k)) (fun i ↦ ball (y i) R) := by
    intro i _ j _ hij
    rw [Function.onFun, Set.disjoint_left]
    intro z hz1 hz2
    rw [mem_ball] at hz1 hz2
    have h1 := dist_triangle (y i) z (y j)
    rw [dist_comm (y i) z] at h1
    rcases lt_or_gt_of_ne hij with h | h
    · linarith [key i j h]
    · have := key j i h
      rw [dist_comm] at this
      linarith
  have hsub : ⋃ i ∈ Finset.range k, ball (y i) R ⊆ ball x (2 * k * R) := by
    intro z hz
    obtain ⟨i, hi, hz⟩ := mem_iUnion₂.1 hz
    rw [Finset.mem_range] at hi
    rw [mem_ball] at hz ⊢
    have h1 := dist_triangle z (y i) x
    rw [dist_comm (y i) x, hy] at h1
    have : (i : ℝ) + 1 ≤ k := by exact_mod_cast hi
    nlinarith
  have hpk : (p : ℝ≥0∞) < k := by
    have : p < (k : ℝ≥0) := by
      rw [hkdef]
      push_cast
      exact Nat.lt_floor_add_one p
    exact_mod_cast this
  calc (p : ℝ≥0∞) < k := hpk
    _ = ∑ _i ∈ Finset.range k, (1 : ℝ≥0∞) := by simp
    _ ≤ ∑ i ∈ Finset.range k, μ (ball (y i) R) := Finset.sum_le_sum fun i _ ↦ hRm (y i)
    _ = μ (⋃ i ∈ Finset.range k, ball (y i) R) :=
        (measure_biUnion_finset hdisj fun i _ ↦ measurableSet_ball).symm
    _ ≤ μ (ball x (2 * k * R)) := measure_mono hsub

omit [OpensMeasurableSpace X] in
theorem IsLocDoublingM.smul {μ : Measure X} (hd : IsLocDoublingM μ) (c : ℝ≥0∞) :
    IsLocDoublingM (c • μ) := by
  obtain ⟨C, hC⟩ := hd
  refine ⟨C, fun x r hr h2r ↦ ?_⟩
  simp only [Measure.smul_apply, smul_eq_mul]
  calc c * μ (ball x (2 * r)) ≤ c * (C * μ (ball x r)) := by gcongr; exact hC x r hr h2r
    _ = C * (c * μ (ball x r)) := by ring

/-- Mass radius for `N⁻¹ μ` versus `μ` (reduction of mass-`N` pieces to mass-`1` pieces). -/
theorem IsLocDoublingM.massRadiusM_inv_smul [BallGeometry X] {μ : Measure X}
    (hd : IsLocDoublingM μ) (hfin : ∀ x : X, ∀ r : ℝ, μ (ball x r) < ∞)
    (hm : ∃ R : ℝ, 0 < R ∧ ∀ x : X, 1 ≤ μ (ball x R)) (N : ℕ) (hN : 1 ≤ N) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ x : X, massRadiusM μ x ≤ massRadiusM ((N : ℝ≥0∞)⁻¹ • μ) x ∧
      massRadiusM ((N : ℝ≥0∞)⁻¹ • μ) x ≤ C * massRadiusM μ x := by
  obtain ⟨rN, hrN, hrNm⟩ := exists_radius_lt_measure_ball hm (N : ℝ≥0)
  obtain ⟨R, hR, hRm⟩ := hm
  obtain ⟨c, δ, hc, hδ, hlow⟩ := hd.rpow_le_measure_ball rN
  set C₀ := max 1 (((N : ℝ) / c) ^ (1 / δ)) with hC₀def
  have hC₀1 : 1 ≤ C₀ := le_max_left _ _
  refine ⟨2 * C₀, by linarith, fun x ↦ ?_⟩
  have hN0 : (N : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hNt : (N : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top N
  have hiff : ∀ s : Set X, 1 ≤ ((N : ℝ≥0∞)⁻¹ • μ) s ↔ (N : ℝ≥0∞) ≤ μ s := by
    intro s
    rw [Measure.smul_apply, smul_eq_mul, ← ENNReal.mul_le_iff_le_inv hN0 hNt, mul_one]
  have hNnn : ((N : ℝ≥0) : ℝ≥0∞) = (N : ℝ≥0∞) := by simp
  have hSν : ∃ r, 0 < r ∧ 1 ≤ ((N : ℝ≥0∞)⁻¹ • μ) (ball x r) :=
    ⟨rN, hrN, (hiff _).2 (by rw [← hNnn]; exact (hrNm x).le)⟩
  have hne : ∃ r, 0 < r ∧ 1 ≤ μ (ball x r) := ⟨R, hR, hRm x⟩
  have hρ := hd.massRadiusM_pos hfin hne
  constructor
  · refine le_csInf hSν ?_
    rintro r ⟨hr, hr1⟩
    refine massRadiusM_le hr ?_
    have h1 : (1 : ℝ≥0∞) ≤ N := by exact_mod_cast hN
    exact h1.trans ((hiff _).1 hr1)
  · set ρ := massRadiusM μ x with hρdef
    by_cases hcase : 2 * C₀ * ρ ≤ rN
    · refine massRadiusM_le (by positivity) ((hiff _).2 ?_)
      have h2 : 1 ≤ μ (ball x (2 * ρ)) := one_le_measure_ball_of_massRadiusM_lt hne (by linarith)
      have hL := hlow x x (2 * C₀ * ρ) (2 * ρ) (by positivity) (by nlinarith) hcase
        (by rw [dist_self]; positivity)
      have hratio : 2 * C₀ * ρ / (2 * ρ) = C₀ := by field_simp
      rw [hratio] at hL
      have hreal : (N : ℝ) ≤ c * C₀ ^ δ := by
        have h3 : ((N : ℝ) / c) ^ (1 / δ) ≤ C₀ := le_max_right _ _
        have h4 : (((N : ℝ) / c) ^ (1 / δ)) ^ δ ≤ C₀ ^ δ :=
          Real.rpow_le_rpow (by positivity) h3 hδ.le
        rw [← Real.rpow_mul (by positivity), one_div_mul_cancel hδ.ne', Real.rpow_one] at h4
        rw [div_le_iff₀ hc] at h4
        linarith
      calc (N : ℝ≥0∞) = ENNReal.ofReal N := (ENNReal.ofReal_natCast N).symm
        _ ≤ ENNReal.ofReal (c * C₀ ^ δ) := ENNReal.ofReal_le_ofReal hreal
        _ ≤ ENNReal.ofReal (c * C₀ ^ δ) * μ (ball x (2 * ρ)) := le_mul_of_one_le_right' h2
        _ ≤ μ (ball x (2 * C₀ * ρ)) := hL
    · rw [not_le] at hcase
      have h1 : massRadiusM ((N : ℝ≥0∞)⁻¹ • μ) x ≤ rN :=
        massRadiusM_le hrN ((hiff _).2 (by rw [← hNnn]; exact (hrNm x).le))
      linarith

/-- **Decay of `ρ(ζ)/d(z,ζ)`** (coordinator addition (1)), power form. -/
theorem IsLocDoublingM.massRadiusM_div_dist_le [BallGeometry X] {μ : Measure X}
    (hd : IsLocDoublingM μ) (hfin : ∀ x : X, ∀ r : ℝ, μ (ball x r) < ∞)
    (hm : ∃ R : ℝ, 0 < R ∧ ∀ x : X, 1 ≤ μ (ball x R)) (M₀ : ℝ) :
    ∃ C α : ℝ, 0 < C ∧ 0 < α ∧ α ≤ 1 ∧ ∀ z ζ : X, massRadiusM μ z ≤ dist z ζ → dist z ζ ≤ M₀ →
      massRadiusM μ ζ / dist z ζ ≤ C * (massRadiusM μ z / dist z ζ) ^ α :=
  hd.massRadiusM_div_dist_le_aux hfin hm M₀

/-- **Decay**, geometric form: `d(z,ζ) ≥ 2ⁿ ρ(z)`, `d ≤ M₀` ⟹ `ρ(ζ)/d(z,ζ) ≤ C θⁿ`. -/
theorem IsLocDoublingM.decay [BallGeometry X] {μ : Measure X}
    (hd : IsLocDoublingM μ) (hfin : ∀ x : X, ∀ r : ℝ, μ (ball x r) < ∞)
    (hm : ∃ R : ℝ, 0 < R ∧ ∀ x : X, 1 ≤ μ (ball x R)) (M₀ : ℝ) :
    ∃ C θ : ℝ, 0 < C ∧ 0 < θ ∧ θ < 1 ∧ ∀ (z ζ : X) (n : ℕ),
      2 ^ n * massRadiusM μ z ≤ dist z ζ → dist z ζ ≤ M₀ →
        massRadiusM μ ζ / dist z ζ ≤ C * θ ^ n :=
  hd.decay_aux hfin hm M₀

omit [MeasurableSpace X] [OpensMeasurableSpace X] in
/-- Disjoint open balls of radius `a` in a `BallGeometry` space have `2a`-separated centres. -/
theorem le_dist_of_disjoint_ball [BallGeometry X] {x y : X} {a : ℝ}
    (h : Disjoint (ball x a) (ball y a)) : 2 * a ≤ dist x y := by
  by_contra hlt
  rw [not_le] at hlt
  have h0 := dist_nonneg (x := x) (y := y)
  obtain ⟨m, hm1, hm2⟩ := BallGeometry.exists_between x y (dist x y / 2) (by positivity)
    (by linarith)
  refine Set.disjoint_left.1 h (show m ∈ ball x a by rw [mem_ball, dist_comm]; linarith)
    (show m ∈ ball y a by rw [mem_ball]; linarith)

omit [MeasurableSpace X] [OpensMeasurableSpace X] in
/-- **Bounded count** (coordinator addition (2)), abstract form: disjoint sets containing a ball
of radius `a` and contained in a ball of radius `D` around the same centre; at most `M` of them
meet a ball of radius `b`. -/
theorem BallGeometry.encard_le_of_disjoint [BallGeometry X] (a b D : ℝ) (ha : 0 < a) :
    ∃ M : ℕ, ∀ {ι : Type*} (E : ι → Set X) (c : ι → X) (z : X), Pairwise (Function.onFun Disjoint E) →
      (∀ i, ball (c i) a ⊆ E i) → (∀ i, E i ⊆ ball (c i) D) →
        {i | (E i ∩ ball z b).Nonempty}.encard ≤ M := by
  obtain ⟨K, hK⟩ := BallGeometry.covering (X := X) (b + D) a ha
  refine ⟨K, fun {ι} E c z hdisj hin hout ↦ ?_⟩
  obtain ⟨s, hs, hcov⟩ := hK z
  set I := {i | (E i ∩ ball z b).Nonempty} with hIdef
  have hcI : ∀ i ∈ I, c i ∈ ball z (b + D) := by
    rintro i ⟨p, hp1, hp2⟩
    have h1 := hout i hp1
    rw [mem_ball] at h1 hp2 ⊢
    have := dist_triangle (c i) p z
    rw [dist_comm (c i) p] at this
    linarith
  have hch : ∀ i ∈ I, ∃ y ∈ s, c i ∈ ball y a := fun i hi ↦ by
    simpa using hcov (hcI i hi)
  have : Nonempty X := ⟨z⟩
  choose! g hgs hgc using hch
  have hinj : InjOn g I := by
    intro i hi j hj hij
    by_contra hne
    have hsep := le_dist_of_disjoint_ball
      ((show Disjoint (E i) (E j) from hdisj hne).mono (hin i) (hin j))
    have h1 := hgc i hi
    have h2 := hgc j hj
    rw [hij] at h1
    rw [mem_ball] at h1 h2
    have := dist_triangle (c i) (g j) (c j)
    rw [dist_comm (g j) (c j)] at this
    linarith
  have hmaps : MapsTo g I (s : Set X) := fun i hi ↦ hgs i hi
  calc I.encard ≤ (s : Set X).encard := encard_le_encard_of_injOn hmaps hinj
    _ = s.card := encard_coe_eq_coe_finsetCard s
    _ ≤ K := by exact_mod_cast hs

end Abstract

end OC
