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

theorem exists_dist_eq [BallGeometry X] (x : X) {r : ℝ} (hr : 0 ≤ r) : ∃ y, dist x y = r := sorry

theorem IsLocDoublingM.exists_const_of_le [BallGeometry X] {μ : Measure X}
    (hd : IsLocDoublingM μ) (R₁ : ℝ) :
    ∃ C : ℝ≥0, 1 ≤ C ∧ ∀ x : X, ∀ r : ℝ, 0 < r → r ≤ R₁ →
      μ (ball x (2 * r)) ≤ C * μ (ball x r) := sorry

theorem IsLocDoublingM.measure_ball_le_of_dist_le [BallGeometry X] {μ : Measure X}
    (hd : IsLocDoublingM μ) (R₁ : ℝ) :
    ∃ C : ℝ≥0, ∀ x y : X, ∀ r : ℝ, 0 < r → r ≤ R₁ → dist x y ≤ r →
      μ (ball y r) ≤ C * μ (ball x r) := sorry

theorem IsLocDoublingM.measure_ball_le_pow [BallGeometry X] {μ : Measure X}
    (hd : IsLocDoublingM μ) (R₁ : ℝ) :
    ∃ C : ℝ≥0, 1 ≤ C ∧ ∀ (x x' : X) (r r' : ℝ) (k : ℕ), 0 < r' → r ≤ R₁ → dist x x' ≤ r →
      r ≤ 2 ^ k * r' → μ (ball x r) ≤ C ^ (k + 1) * μ (ball x' r') := sorry

theorem IsLocDoublingM.reverse_doubling [BallGeometry X] {μ : Measure X}
    (hd : IsLocDoublingM μ) (R₁ : ℝ) :
    ∃ η : ℝ≥0, 0 < η ∧ ∀ x : X, ∀ t : ℝ, 0 < t → t ≤ R₁ →
      (1 + η) * μ (ball x t) ≤ μ (ball x (2 * t)) := sorry

theorem IsLocDoublingM.measure_ball_le_rpow [BallGeometry X] {μ : Measure X}
    (hd : IsLocDoublingM μ) (R₁ : ℝ) :
    ∃ C s : ℝ, 0 < C ∧ 0 < s ∧ ∀ (x x' : X) (r r' : ℝ), 0 < r' → r' ≤ r → r ≤ R₁ →
      dist x x' ≤ r → μ (ball x r) ≤ ENNReal.ofReal (C * (r / r') ^ s) * μ (ball x' r') := sorry

theorem IsLocDoublingM.rpow_le_measure_ball [BallGeometry X] {μ : Measure X}
    (hd : IsLocDoublingM μ) (R₁ : ℝ) :
    ∃ c δ : ℝ, 0 < c ∧ 0 < δ ∧ ∀ (x x' : X) (r r' : ℝ), 0 < r' → r' ≤ r → r ≤ R₁ →
      dist x x' ≤ r → ENNReal.ofReal (c * (r / r') ^ δ) * μ (ball x' r') ≤ μ (ball x r) := sorry

/-- **Lemma 1** in the paper's form. -/
theorem IsLocDoublingM.lemma1 [BallGeometry X] {μ : Measure X}
    (hd : IsLocDoublingM μ) (R₁ : ℝ) :
    ∃ γ A : ℝ, 0 < γ ∧ γ ≤ 1 ∧ 0 < A ∧
      ∀ (x x' : X) (r r' : ℝ), 0 < r' → r ≤ R₁ → dist x x' + r' ≤ r →
        0 < μ (ball x' r') → μ (ball x r) < ∞ →
        ((μ (ball x r)).toReal / (μ (ball x' r')).toReal) ^ γ ≤ A * (r / r') ∧
        r / r' ≤ A * ((μ (ball x r)).toReal / (μ (ball x' r')).toReal) ^ (1 / γ) := sorry

theorem IsLocDoublingM.measure_singleton {μ : Measure X} (hd : IsLocDoublingM μ)
    [BallGeometry X] (hfin : ∀ x : X, ∀ r : ℝ, μ (ball x r) < ∞) (x : X) : μ {x} = 0 := sorry

theorem IsLocDoublingM.measure_ball_pos [BallGeometry X] {μ : Measure X}
    (hd : IsLocDoublingM μ) (hm : ∃ R : ℝ, 0 < R ∧ ∀ x : X, 1 ≤ μ (ball x R))
    (x : X) {r : ℝ} (hr : 0 < r) : 0 < μ (ball x r) := sorry

theorem IsPorous.mono {E F : Set X} (hF : IsPorous F) (hEF : E ⊆ F) : IsPorous E := sorry

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
