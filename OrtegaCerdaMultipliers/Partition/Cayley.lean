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

theorem cayley_im_pos {z : ℂ} (hz : z ∈ 𝔻) : 0 < (cayley z).im := sorry
theorem cayleyInv_cayley {z : ℂ} (hz : z ∈ 𝔻) : cayleyInv (cayley z) = z := sorry
theorem cayley_cayleyInv {w : ℂ} (hw : 0 < w.im) : cayley (cayleyInv w) = w := sorry
theorem cayleyInv_mem {w : ℂ} (hw : 0 < w.im) : cayleyInv w ∈ 𝔻 := sorry
theorem measurable_cayley : Measurable cayley := sorry

/-- The Cayley map is an isometry onto the half-plane metric. -/
theorem pseudoHyp_cayleyInv {w₁ w₂ : ℂ} (h₁ : 0 < w₁.im) (h₂ : 0 < w₂.im) :
    pseudoHyp (cayleyInv w₁) (cayleyInv w₂) = ‖w₁ - w₂‖ / ‖w₁ - conj w₂‖ := sorry

/-- Level sets of `Re ∘ cayley` and `Im ∘ cayley` lie on circles or lines, hence are porous. -/
theorem isPorous_cayley_re (x : ℝ) : IsPorous (cayleyPre {w | w.re = x}) := sorry
theorem isPorous_cayley_im (y : ℝ) : IsPorous (cayleyPre {w | w.im = y}) := sorry

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
