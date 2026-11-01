import OrtegaCerdaMultipliers.Line.Basic

/-!
# M13 (Theorem5) — The signed distribution function, the knots, the barycentres

See `blueprint/M13_Theorem5.md` §3.2–§3.4.  Scaffold: statements, proofs `sorry`; definitions are
real.
-/

open MeasureTheory Metric Set Complex
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace OC

/-- Signed distribution function of `σ_α = μ − 2α·dt`: `G_α(t) = σ_α((0,t])` (oriented). -/
def lineCDF (μ : Measure ℂ) (α t : ℝ) : ℝ :=
  (if 0 ≤ t then (linePull μ (Ioc 0 t)).toReal else -(linePull μ (Ioc t 0)).toReal)
    - 2 * α * t

/-- First hitting time of the level `s` by `G_α`. -/
def lineLevel (μ : Measure ℂ) (α s : ℝ) : ℝ := sInf {t : ℝ | lineCDF μ α t = s}

/-- Knots `e_k = T_α(4π k)`; the cells are `I_k = (e_k, e_{k+1}]`, with `σ_α(I_k) = 4π`. -/
def lineKnot (μ : Measure ℂ) (α : ℝ) (k : ℤ) : ℝ := lineLevel μ α (4 * Real.pi * k)

/-- Length `a_k = e_{k+1} − e_k` of the cell `I_k`. -/
def lineLength (μ : Measure ℂ) (α : ℝ) (k : ℤ) : ℝ := lineKnot μ α (k + 1) - lineKnot μ α k

/-- Signed barycentre `λ_k = (1/4π) ∫_{I_k} t dσ_α(t)`. -/
def lineCentre (μ : Measure ℂ) (α : ℝ) (k : ℤ) : ℝ :=
  ((∫ t in Ioc (lineKnot μ α k) (lineKnot μ α (k + 1)), t ∂linePull μ) -
    2 * α * ∫ t in lineKnot μ α k..lineKnot μ α (k + 1), t) / (4 * Real.pi)

/-- The two nodes `λ_k ± s a_k` of the cell `I_k` (`b = true` is `+`). -/
def lineNode (μ : Measure ℂ) (α s : ℝ) (k : ℤ) (b : Bool) : ℝ :=
  lineCentre μ α k + (if b then s else -s) * lineLength μ α k

/-! 13.2 the signed distribution function -/
theorem lineCDF_sub {μ : Measure ℂ} (hμ : IsLineMeasure μ) (α : ℝ) {a b : ℝ} (hab : a ≤ b) :
    lineCDF μ α b - lineCDF μ α a = (linePull μ (Ioc a b)).toReal - 2 * α * (b - a) := sorry
theorem continuous_lineCDF {μ : Measure ℂ} (hμ : IsLineMeasure μ) (α : ℝ) :
    Continuous (lineCDF μ α) := sorry
theorem lineCDF_add_ge {μ : Measure ℂ} (hμ : IsLineMeasure μ) {r α : ℝ} (hr : 0 < r)
    (hmr : ∀ x : ℝ, 1 < μ (lineInterval x r)) (hα : 0 ≤ α) (hαr : α * r ≤ 1 / 8) (t : ℝ) :
    lineCDF μ α t + 1 / 2 ≤ lineCDF μ α (t + 2 * r) := sorry

/-! 13.3 the knots -/
theorem lineCDF_lineKnot {μ : Measure ℂ} (hμ : IsLineMeasure μ) {r α : ℝ} (hr : 0 < r)
    (hmr : ∀ x : ℝ, 1 < μ (lineInterval x r)) (hα : 0 ≤ α) (hαr : α * r ≤ 1 / 8) (k : ℤ) :
    lineCDF μ α (lineKnot μ α k) = 4 * Real.pi * k := sorry
theorem lineKnot_strictMono {μ : Measure ℂ} (hμ : IsLineMeasure μ) {r α : ℝ} (hr : 0 < r)
    (hmr : ∀ x : ℝ, 1 < μ (lineInterval x r)) (hα : 0 ≤ α) (hαr : α * r ≤ 1 / 8) :
    StrictMono (lineKnot μ α) := sorry
theorem lineLength_le {μ : Measure ℂ} (hμ : IsLineMeasure μ) {r α : ℝ} (hr : 0 < r)
    (hmr : ∀ x : ℝ, 1 < μ (lineInterval x r)) (hα : 0 ≤ α) (hαr : α * r ≤ 1 / 8) (k : ℤ) :
    lineLength μ α k ≤ 52 * r := sorry
theorem existsUnique_lineKnot_mem {μ : Measure ℂ} (hμ : IsLineMeasure μ) {r α : ℝ} (hr : 0 < r)
    (hmr : ∀ x : ℝ, 1 < μ (lineInterval x r)) (hα : 0 ≤ α) (hαr : α * r ≤ 1 / 8) (t : ℝ) :
    ∃! k : ℤ, t ∈ Ioc (lineKnot μ α k) (lineKnot μ α (k + 1)) := sorry
theorem linePull_Ioc_lineKnot {μ : Measure ℂ} (hμ : IsLineMeasure μ) {r α : ℝ} (hr : 0 < r)
    (hmr : ∀ x : ℝ, 1 < μ (lineInterval x r)) (hα : 0 ≤ α) (hαr : α * r ≤ 1 / 8) (k : ℤ) :
    linePull μ (Ioc (lineKnot μ α k) (lineKnot μ α (k + 1))) =
      ENNReal.ofReal (4 * Real.pi + 2 * α * lineLength μ α k) := sorry

/-! 13.4 the barycentre stays in the middle of its cell; the nodes are separated -/
theorem IsLineMeasure.lineCentre_mem {μ : Measure ℂ} (hμ : IsLineMeasure μ) :
    ∃ α₁ c₀ : ℝ, 0 < α₁ ∧ 0 < c₀ ∧ c₀ ≤ 1 / 4 ∧ ∀ α : ℝ, 0 ≤ α → α ≤ α₁ → ∀ k : ℤ,
      lineKnot μ α k + c₀ * lineLength μ α k ≤ lineCentre μ α k ∧
      lineCentre μ α k ≤ lineKnot μ α (k + 1) - c₀ * lineLength μ α k := sorry
theorem IsLineMeasure.lineNode_separated {μ : Measure ℂ} (hμ : IsLineMeasure μ) :
    ∃ α₁ s₁ : ℝ, 0 < α₁ ∧ 0 < s₁ ∧ s₁ ≤ 1 / 8 ∧ ∀ α : ℝ, 0 ≤ α → α ≤ α₁ →
      ∀ s : ℝ, 0 < s → s ≤ s₁ →
      ∀ ν ∈ range (fun p : ℤ × Bool ↦ lineNode μ α 0 p.1 p.2) ∪
          range (fun p : ℤ × Bool ↦ lineNode μ α s p.1 p.2),
      ∀ ν' ∈ range (fun p : ℤ × Bool ↦ lineNode μ α 0 p.1 p.2) ∪
          range (fun p : ℤ × Bool ↦ lineNode μ α s p.1 p.2),
      ν ≠ ν' → s / 2 * (massRadiusLine μ ν + massRadiusLine μ ν') ≤ |ν - ν'| := sorry

end OC
