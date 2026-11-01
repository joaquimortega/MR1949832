import OrtegaCerdaMultipliers.Partition.Rectangles

/-!
# M05 (Partition) — Cayley coordinates and horocyclic boxes in `𝔻`

See `blueprint/M05_Partition.md` §2.2.  Scaffold: statements, proofs `sorry`; definitions are real.
-/

open MeasureTheory Metric Set Complex
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace OC

/-- The Cayley map `𝔻 → ℍ`, `z ↦ i(1+z)/(1-z)`. -/
def cayley (z : ℂ) : ℂ := I * (1 + z) / (1 - z)

/-- Its inverse `ℍ → 𝔻`, `w ↦ (w - i)/(w + i)`. -/
def cayleyInv (w : ℂ) : ℂ := (w - I) / (w + I)

/-- The preimage in `𝔻` of a set of the upper half-plane. -/
def cayleyPre (S : Set ℂ) : Set ℂ := {z | z ∈ 𝔻 ∧ cayley z ∈ S}

/-- A horocyclic box: two horocycles and two geodesics through `1`. -/
def discBox (x₁ x₂ y₁ y₂ : ℝ) : Set ℂ := cayleyPre (rect x₁ x₂ y₁ y₂)

theorem cay_re (z : ℂ) : (cayley z).re = -2 * z.im / Complex.normSq (1 - z) := by
  simp only [cayley, Complex.div_re, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im, Complex.sub_re,
    Complex.sub_im]
  ring

theorem cay_im (z : ℂ) : (cayley z).im = (1 - Complex.normSq z) / Complex.normSq (1 - z) := by
  simp only [cayley, Complex.div_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im, Complex.sub_re,
    Complex.sub_im, Complex.normSq_apply]
  ring

theorem cay_one_sub_ne_zero {z : ℂ} (hz : z ∈ 𝔻) : 1 - z ≠ 0 := by
  intro h
  have : z = 1 := by linear_combination -h
  rw [this, mem_ball_zero_iff, norm_one] at hz
  exact lt_irrefl _ hz

theorem cay_normSq_lt_one {z : ℂ} (hz : z ∈ 𝔻) : Complex.normSq z < 1 := by
  rw [Complex.normSq_eq_norm_sq]
  have h := mem_ball_zero_iff.1 hz
  nlinarith [norm_nonneg z]

theorem cayley_im_pos {z : ℂ} (hz : z ∈ 𝔻) : 0 < (cayley z).im := by
  rw [cay_im]
  exact div_pos (by linarith [cay_normSq_lt_one hz])
    (Complex.normSq_pos.2 (cay_one_sub_ne_zero hz))

theorem cayleyInv_cayley {z : ℂ} (hz : z ∈ 𝔻) : cayleyInv (cayley z) = z := by
  have h := cay_one_sub_ne_zero hz
  have hnum : I * (1 + z) / (1 - z) - I = 2 * I * z / (1 - z) := by field_simp; ring
  have hden : I * (1 + z) / (1 - z) + I = 2 * I / (1 - z) := by field_simp; ring
  unfold cayleyInv cayley
  rw [hnum, hden]
  field_simp

theorem cay_add_I_ne_zero {w : ℂ} (hw : 0 < w.im) : w + I ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  linarith

theorem cayley_cayleyInv {w : ℂ} (hw : 0 < w.im) : cayley (cayleyInv w) = w := by
  have h := cay_add_I_ne_zero hw
  unfold cayley cayleyInv
  have h1 : 1 - (w - I) / (w + I) = 2 * I / (w + I) := by field_simp; ring
  have h2 : 1 + (w - I) / (w + I) = 2 * w / (w + I) := by field_simp; ring
  rw [h1, h2]
  field_simp

theorem cayleyInv_mem {w : ℂ} (hw : 0 < w.im) : cayleyInv w ∈ 𝔻 := by
  have h := cay_add_I_ne_zero hw
  rw [mem_ball_zero_iff, cayleyInv, norm_div, div_lt_one (norm_pos_iff.2 h)]
  have hsq : ‖w - I‖ ^ 2 < ‖w + I‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.I_re,
      Complex.I_im]
    nlinarith
  exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) hsq

theorem measurable_cayley : Measurable cayley := by
  unfold cayley
  fun_prop

/-- The Cayley map is an isometry onto the half-plane metric. -/
theorem pseudoHyp_cayleyInv {w₁ w₂ : ℂ} (h₁ : 0 < w₁.im) (h₂ : 0 < w₂.im) :
    pseudoHyp (cayleyInv w₁) (cayleyInv w₂) = ‖w₁ - w₂‖ / ‖w₁ - conj w₂‖ := by
  have ha := cay_add_I_ne_zero h₁
  have hb := cay_add_I_ne_zero h₂
  have hac : conj w₁ - I ≠ 0 := by
    intro h; apply ha
    have := congrArg conj h
    simpa using this
  have hcw : w₁ - conj w₂ ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    linarith
  have hcw' : conj w₁ - w₂ ≠ 0 := by
    intro h; apply hcw
    have := congrArg conj h
    simpa using this
  have e1 : cayleyInv w₁ - cayleyInv w₂ = 2 * I * (w₁ - w₂) / ((w₁ + I) * (w₂ + I)) := by
    unfold cayleyInv; field_simp; ring
  have e2 : 1 - conj (cayleyInv w₁) * cayleyInv w₂ =
      2 * I * (conj w₁ - w₂) / ((conj w₁ - I) * (w₂ + I)) := by
    unfold cayleyInv
    rw [map_div₀, map_sub, map_add, Complex.conj_I]
    rw [show conj w₁ + -I = conj w₁ - I by ring]
    field_simp
    ring
  have n1 : ‖conj w₁ - I‖ = ‖w₁ + I‖ := by
    rw [← Complex.norm_conj (w₁ + I), map_add, Complex.conj_I]; ring_nf
  have n2 : ‖conj w₁ - w₂‖ = ‖w₁ - conj w₂‖ := by
    rw [← Complex.norm_conj (w₁ - conj w₂), map_sub, Complex.conj_conj]
  rw [pseudoHyp, e1, e2]
  simp only [norm_div, norm_mul]
  rw [n1, n2]
  have : ‖w₁ + I‖ ≠ 0 := norm_ne_zero_iff.2 ha
  have : ‖w₂ + I‖ ≠ 0 := norm_ne_zero_iff.2 hb
  have : ‖w₁ - conj w₂‖ ≠ 0 := norm_ne_zero_iff.2 hcw
  have : ‖2 * I‖ ≠ 0 := by simp
  field_simp

/-- Level sets of `Re ∘ cayley` and `Im ∘ cayley` lie on circles or lines, hence are porous. -/
theorem isPorous_cayley_re (x : ℝ) : IsPorous (cayleyPre {w | w.re = x}) := by
  by_cases hx : x = 0
  · refine IsPorous.mono (isPorous_line 0 1) ?_
    rintro z ⟨hz, hzx⟩
    simp only [mem_setOf_eq, cay_re, hx] at hzx
    have hn := Complex.normSq_pos.2 (cay_one_sub_ne_zero hz)
    rw [div_eq_zero_iff] at hzx
    have him : z.im = 0 := by
      rcases hzx with h | h
      · linarith
      · exact absurd h hn.ne'
    exact ⟨z.re, Complex.ext (by simp) (by simp [him])⟩
  · refine IsPorous.mono (isPorous_sphere (⟨1, -1 / x⟩ : ℂ) (1 / |x|)) ?_
    rintro z ⟨hz, hzx⟩
    simp only [mem_setOf_eq, cay_re] at hzx
    have hn := Complex.normSq_pos.2 (cay_one_sub_ne_zero hz)
    rw [div_eq_iff hn.ne', Complex.normSq_apply] at hzx
    simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im] at hzx
    rw [mem_sphere, Complex.dist_eq, ← sq_eq_sq₀ (norm_nonneg _) (by positivity),
      Complex.sq_norm, Complex.normSq_apply, div_pow, one_pow, sq_abs]
    simp only [Complex.sub_re, Complex.sub_im]
    field_simp
    linear_combination (-x) * hzx

theorem isPorous_cayley_im (y : ℝ) : IsPorous (cayleyPre {w | w.im = y}) := by
  by_cases hy : y = -1
  · refine IsPorous.mono (isPorous_line 1 I) ?_
    rintro z ⟨hz, hzy⟩
    simp only [mem_setOf_eq, cay_im, hy] at hzy
    have hn := Complex.normSq_pos.2 (cay_one_sub_ne_zero hz)
    rw [div_eq_iff hn.ne', Complex.normSq_apply, Complex.normSq_apply] at hzy
    simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im] at hzy
    have hre : z.re = 1 := by nlinarith
    exact ⟨z.im, Complex.ext (by simp [hre]) (by simp)⟩
  · have hy' : 1 + y ≠ 0 := fun h ↦ hy (by linarith)
    refine IsPorous.mono (isPorous_sphere (⟨y / (1 + y), 0⟩ : ℂ) (1 / |1 + y|)) ?_
    rintro z ⟨hz, hzy⟩
    simp only [mem_setOf_eq, cay_im] at hzy
    have hn := Complex.normSq_pos.2 (cay_one_sub_ne_zero hz)
    rw [div_eq_iff hn.ne', Complex.normSq_apply, Complex.normSq_apply] at hzy
    simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im] at hzy
    rw [mem_sphere, Complex.dist_eq, ← sq_eq_sq₀ (norm_nonneg _) (by positivity),
      Complex.sq_norm, Complex.normSq_apply, div_pow, one_pow, sq_abs]
    simp only [Complex.sub_re, Complex.sub_im]
    field_simp
    linear_combination (-(1 + y)) * hzy

/-- Inner/outer hyperbolic balls of an admissible box (`l ≤ Λ y₁`, side ratio `≤ L`). -/
theorem discBox_inner_outer (Λ L : ℝ) (hΛ : 0 < Λ) (hL : 1 ≤ L) :
    ∃ A D : ℝ, 1 ≤ A ∧ 0 < D ∧ ∀ x₁ x₂ y₁ y₂ : ℝ, IsRectLE L x₁ x₂ y₁ y₂ → 0 < y₁ →
      y₂ - y₁ ≤ Λ * y₁ → ∃ p ∈ 𝔻, ∃ β : ℝ, 0 < β ∧ A * β ≤ D ∧
        hypBall p β ⊆ cayleyPre (midThird x₁ x₂ y₁ y₂) ∧
        discBox x₁ x₂ y₁ y₂ ⊆ hypBall p (A * β) := sorry

/-- Euclidean doubling of the push-forward `cayley_* (μ|𝔻)` below the scale `Im w / 16`. -/
theorem euclid_doubling_cayley {μ : Measure ℂ} (hd : IsLocallyDoublingDisc μ) :
    ∃ C_E : ℝ, 0 < C_E ∧ ∀ w : ℂ, 0 < w.im → ∀ r : ℝ, 0 < r → r ≤ w.im / 16 →
      (μ.restrict 𝔻).map cayley (ball w (4 * r)) ≤
        ENNReal.ofReal C_E * (μ.restrict 𝔻).map cayley (ball w (r / 2)) := sorry

/-! ### Helpers consumed by `Lemma4.lean` (M05 §3.7–3.8) -/

/-- Masses of the push-forward `cayley_* (μ|𝔻)` are masses of `cayleyPre`. -/
theorem map_restrict_cayley_apply (μ : Measure ℂ) {S : Set ℂ} (hS : MeasurableSet S) :
    (μ.restrict 𝔻).map cayley S = μ (cayleyPre S) := sorry

/-- Uniform form of `euclid_doubling_cayley`: `C_E` depends only on the doubling constant `Cd`
(the hypothesis is `IsLocallyDoublingDiscWith μ Cd`, unfolded). -/
theorem euclid_doubling_cayley_quant (Cd : ℝ≥0) :
    ∃ C_E : ℝ, 0 < C_E ∧ ∀ μ : Measure ℂ,
      (∀ z ∈ 𝔻, ∀ r : ℝ, 0 < r → 2 * r < 1 → μ (hypBall z (2 * r)) ≤ Cd * μ (hypBall z r)) →
      ∀ w : ℂ, 0 < w.im → ∀ r : ℝ, 0 < r → r ≤ w.im / 16 →
        (μ.restrict 𝔻).map cayley (ball w (4 * r)) ≤
          ENNReal.ofReal C_E * (μ.restrict 𝔻).map cayley (ball w (r / 2)) := sorry

/-- Coarse rows (M05 §3.7): with `Λc = 64 e^{4R}`, every box
`[a, a + (Λc - 1) y₁) × [y₁, Λc y₁)` contains a hyperbolic ball of radius `R`. -/
theorem exists_hypBall_subset_discBox_row {R : ℝ} (hR : 0 < R) {y₁ : ℝ} (hy : 0 < y₁) (a : ℝ) :
    ∃ p ∈ 𝔻, hypBall p R ⊆
      discBox a (a + (64 * Real.exp (4 * R) - 1) * y₁) y₁ (64 * Real.exp (4 * R) * y₁) := sorry

/-- A horocyclic box with `0 < y₁` lies in a compact subset of `𝔻`. -/
theorem exists_isCompact_discBox_subset (x₁ x₂ : ℝ) {y₁ : ℝ} (hy : 0 < y₁) (y₂ : ℝ) :
    ∃ K : Set ℂ, IsCompact K ∧ K ⊆ 𝔻 ∧ discBox x₁ x₂ y₁ y₂ ⊆ K := sorry

end OC
