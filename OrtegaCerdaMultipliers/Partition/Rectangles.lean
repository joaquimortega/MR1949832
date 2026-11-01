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

theorem measurableSet_rect (x₁ x₂ y₁ y₂ : ℝ) : MeasurableSet (rect x₁ x₂ y₁ y₂) := sorry

/-- Continuity of the mass of a rectangle in its right edge. -/
theorem continuous_measure_rect_right {ν : Measure ℂ} (hre : ∀ x : ℝ, ν {w | w.re = x} = 0)
    {x₁ y₁ y₂ : ℝ} (hfin : ∀ x₂, ν (rect x₁ x₂ y₁ y₂) < ∞) :
    Continuous fun x₂ : ℝ ↦ ν (rect x₁ x₂ y₁ y₂) := sorry

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

theorem preimage_swapReIm_rect (x₁ x₂ y₁ y₂ : ℝ) :
    swapReIm ⁻¹' rect x₁ x₂ y₁ y₂ = rect y₁ y₂ x₁ x₂ := sorry

/-- Euclidean inner/outer balls of a rectangle of side ratio `≤ L`. -/
theorem rect_inner_outer {L : ℝ} (hL : 1 ≤ L) {x₁ x₂ y₁ y₂ : ℝ} (h : IsRectLE L x₁ x₂ y₁ y₂) :
    ∃ (p : ℂ) (r : ℝ), 0 < r ∧ 6 * r ≤ max (x₂ - x₁) (y₂ - y₁) ∧
      ball p r ⊆ midThird x₁ x₂ y₁ y₂ ∧ rect x₁ x₂ y₁ y₂ ⊆ ball p (6 * L * r) := sorry

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
