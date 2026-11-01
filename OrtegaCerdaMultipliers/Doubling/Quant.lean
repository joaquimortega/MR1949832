import OrtegaCerdaMultipliers.Doubling.Export
import OrtegaCerdaMultipliers.Doubling.Uniform

/-!
# M03 (Doubling) — Quantitative forms: constants depending only on `(C_d, R₀)`

See `blueprint/M03_Doubling.md` §4 and `blueprint/M08_Multiplier.md` §1.1, §4.1.  Scaffold:
statements, proofs `sorry`; definitions are real.

M08 and M09 prove Theorem 4 and Proposition 2 with constants depending only on the doubling
constant `C_d` and the mass radius `R₀` (README §3a.6).  The classes `MeasClassPlane`,
`MeasClassDisc`, the explicit-constant doubling predicates and the normalisation `lapNorm`
(written in the M08 doc) are defined here, because the quantitative M03 lemmas below and M05's
`lemma4_*_quant` are stated with them.  Each lemma is the uniform version of a qualitative
`Doubling/Export.lean` statement: `∀ Cd R₀, ∃ C, ∀ μ in the class, …`.
-/

open MeasureTheory Metric Set Complex
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace OC

/-- `Δψ/(2π)`.  With this normalisation a zero of `h` contributes exactly one unit of mass:
`Δ log|h| = 2π Σ δ_λ` and `Δψ = 2π · lapNorm μ`. -/
def lapNorm (μ : Measure ℂ) : Measure ℂ := (ENNReal.ofReal (2 * Real.pi))⁻¹ • μ

/-- Local doubling with an explicit constant (plane). -/
def IsLocallyDoublingWith (μ : Measure ℂ) (Cd : ℝ≥0) : Prop :=
  ∀ z : ℂ, ∀ r : ℝ, 0 < r → 2 * r < 1 → μ (ball z (2 * r)) ≤ Cd * μ (ball z r)

/-- Local doubling with an explicit constant (disc, hyperbolic balls). -/
def IsLocallyDoublingDiscWith (μ : Measure ℂ) (Cd : ℝ≥0) : Prop :=
  ∀ z ∈ 𝔻, ∀ r : ℝ, 0 < r → 2 * r < 1 → μ (hypBall z (2 * r)) ≤ Cd * μ (hypBall z r)

/-- The class of measures with parameters `(Cd, R₀)` (plane). -/
structure MeasClassPlane (ν : Measure ℂ) (Cd : ℝ≥0) (R₀ : ℝ) : Prop where
  doubling : IsLocallyDoublingWith ν Cd
  mass : ∀ z : ℂ, 1 < ν (ball z R₀)
  finite : ∀ K : Set ℂ, IsCompact K → ν K < ∞

/-- The class of measures with parameters `(Cd, R₀)` (disc). -/
structure MeasClassDisc (ν : Measure ℂ) (Cd : ℝ≥0) (R₀ : ℝ) : Prop where
  doubling : IsLocallyDoublingDiscWith ν Cd
  mass : ∀ z ∈ 𝔻, 1 < ν (hypBall z R₀)
  finite : ∀ K ⊆ 𝔻, IsCompact K → ν K < ∞

/-- Local doubling with an explicit constant (line; `μ` carried by `ℝ`). -/
def IsLocallyDoublingLineWith (μ : Measure ℂ) (Cd : ℝ≥0) : Prop :=
  μ {z : ℂ | z.im ≠ 0} = 0 ∧ ∀ x : ℝ, ∀ r : ℝ, 0 < r → 2 * r < 1 →
    μ (lineInterval x (2 * r)) ≤ Cd * μ (lineInterval x r)

/-- The class of measures with parameters `(Cd, R₀)` (line). -/
structure MeasClassLine (ν : Measure ℂ) (Cd : ℝ≥0) (R₀ : ℝ) : Prop where
  doubling : IsLocallyDoublingLineWith ν Cd
  mass : ∀ x : ℝ, 1 < ν (lineInterval x R₀)
  finite : ∀ K : Set ℂ, IsCompact K → ν K < ∞

/-! ### The abstract theory with explicit constants

Each lemma is the uniform version of the corresponding `Doubling/Abstract.lean` statement: the
constants are chosen after the doubling constant `Cd` and the mass radius `R₀` (and the displayed
auxiliary parameters), and before the measure.  The `ℂ`-level forms below are thin wrappers
through `ℂ` itself, `discPull` and `linePull` (`MeasClassPlane.measClassM`,
`MeasClassDisc.measClassM_discPull`, `MeasClassLine.measClassM_linePull`). -/

section AbstractQuant

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

/-- Local doubling on a metric space with an explicit constant. -/
def IsLocDoublingMWith (μ : Measure X) (Cd : ℝ≥0) : Prop :=
  ∀ x : X, ∀ r : ℝ, 0 < r → 2 * r < 1 → μ (ball x (2 * r)) ≤ Cd * μ (ball x r)

/-- The abstract class with parameters `(Cd, R₀)`: explicit doubling constant, every ball of
radius `R₀` has mass `≥ 1`, balls have finite mass. -/
structure MeasClassM (μ : Measure X) (Cd : ℝ≥0) (R₀ : ℝ) : Prop where
  doubling : IsLocDoublingMWith μ Cd
  mass : ∀ x : X, 1 ≤ μ (ball x R₀)
  finite : ∀ x : X, ∀ r : ℝ, μ (ball x r) < ∞

omit [OpensMeasurableSpace X] in
theorem IsLocDoublingMWith.isLocDoublingM {μ : Measure X} {Cd : ℝ≥0}
    (h : IsLocDoublingMWith μ Cd) : IsLocDoublingM μ :=
  ⟨Cd, h⟩

/-! #### Helpers (M03b) -/

section ClassHelpers

variable {μ : Measure X} {Cd : ℝ≥0} {R₀ : ℝ}

theorem MeasClassM.R₀_pos (h : MeasClassM μ Cd R₀) (x : X) : 0 < R₀ := by
  by_contra hR
  have h1 := h.mass x
  rw [ball_eq_empty.2 (not_lt.1 hR), measure_empty] at h1
  exact absurd h1 (by norm_num)

theorem MeasClassM.hne (h : MeasClassM μ Cd R₀) (x : X) : ∃ r, 0 < r ∧ 1 ≤ μ (ball x r) :=
  ⟨R₀, h.R₀_pos x, h.mass x⟩

theorem MeasClassM.hm (h : MeasClassM μ Cd R₀) : ∃ R : ℝ, 0 < R ∧ ∀ x : X, 1 ≤ μ (ball x R) :=
  ⟨max R₀ 1, lt_max_of_lt_right one_pos,
    fun x ↦ (h.mass x).trans (measure_mono (ball_subset_ball (le_max_left _ _)))⟩

theorem MeasClassM.massRadiusM_pos [BallGeometry X] (h : MeasClassM μ Cd R₀) (x : X) :
    0 < massRadiusM μ x :=
  IsLocDoublingM.massRadiusM_pos h.doubling.isLocDoublingM h.finite (h.hne x)

theorem MeasClassM.massRadiusM_le (h : MeasClassM μ Cd R₀) (x : X) : massRadiusM μ x ≤ R₀ :=
  OC.massRadiusM_le (h.R₀_pos x) (h.mass x)

theorem MeasClassM.one_le_two [BallGeometry X] (h : MeasClassM μ Cd R₀) (x : X) :
    1 ≤ μ (ball x (2 * massRadiusM μ x)) :=
  (one_le_measure_closedBall_massRadiusM (h.finite x) (h.hne x)).trans
    (measure_mono (closedBall_subset_ball (by linarith [h.massRadiusM_pos x])))

theorem MeasClassM.le_add_dist (h : MeasClassM μ Cd R₀) (x y : X) :
    massRadiusM μ y ≤ massRadiusM μ x + dist x y := by
  have := (lipschitzWith_massRadiusM (μ := μ) h.hne).dist_le_mul x y
  rw [NNReal.coe_one, one_mul, Real.dist_eq] at this
  linarith [(abs_sub_le_iff.1 this).2]

end ClassHelpers

/-- The real algebra of the decay estimate (§3.13). -/
theorem decay_algebra {c CU δ s a b : ℝ} (hc : 0 < c) (hCU : 0 < CU) (hδ : 0 < δ) (hs : 0 < s)
    (ha : 0 < a) (hb : 0 < b) (hb1 : b ≤ 1) (h : c * (3 / (2 * b)) ^ δ ≤ CU * (3 / a) ^ s) :
    a ≤ (CU * 3 ^ s / c) ^ (1 / s) * b ^ (min 1 (δ / s)) := by
  have h1 : (1 / b) ^ δ ≤ (3 / (2 * b)) ^ δ :=
    Real.rpow_le_rpow (by positivity)
      (by rw [div_le_div_iff₀ hb (by positivity)]; linarith) hδ.le
  rw [Real.div_rpow zero_le_one hb.le, Real.one_rpow] at h1
  rw [Real.div_rpow (by norm_num) ha.le] at h
  have hbδ : 0 < b ^ δ := Real.rpow_pos_of_pos hb δ
  have has : 0 < a ^ s := Real.rpow_pos_of_pos ha s
  have has' := has.ne'
  have h2 : c * (1 / b ^ δ) ≤ CU * (3 ^ s / a ^ s) :=
    (mul_le_mul_of_nonneg_left h1 hc.le).trans h
  have h3 : a ^ s ≤ CU * 3 ^ s / c * b ^ δ := by
    have e1 : c * (1 / b ^ δ) * (b ^ δ * a ^ s) = c * a ^ s := by field_simp
    have e2 : CU * (3 ^ s / a ^ s) * (b ^ δ * a ^ s) = CU * 3 ^ s * b ^ δ := by field_simp
    have := mul_le_mul_of_nonneg_right h2 (by positivity : (0 : ℝ) ≤ b ^ δ * a ^ s)
    rw [e1, e2] at this
    rw [div_mul_eq_mul_div, le_div_iff₀ hc]
    linarith
  have h4 := le_rpow_one_div_of_rpow_le ha.le hs h3
  rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hb.le] at h4
  refine h4.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  rw [mul_one_div]
  exact Real.rpow_le_rpow_of_exponent_ge hb hb1 (min_le_right _ _)

theorem doubling_upTo_quant [BallGeometry X] (Cd : ℝ≥0) (R₁ : ℝ) :
    ∃ C : ℝ≥0, 1 ≤ C ∧ ∀ μ : Measure X, IsLocDoublingMWith μ Cd → ∀ x : X, ∀ r : ℝ, 0 < r →
      r ≤ R₁ → μ (ball x (2 * r)) ≤ C * μ (ball x r) := by
  obtain ⟨C, hC, h⟩ := exists_doublingUpTo (X := X) Cd R₁
  exact ⟨C, hC, fun μ hμ ↦ h μ hμ⟩

theorem measure_ball_le_rpow_quant [BallGeometry X] (Cd : ℝ≥0) (R₁ : ℝ) :
    ∃ C s : ℝ, 0 < C ∧ 0 < s ∧ ∀ μ : Measure X, IsLocDoublingMWith μ Cd →
      ∀ (x x' : X) (r r' : ℝ), 0 < r' → r' ≤ r → r ≤ R₁ → dist x x' ≤ r →
        μ (ball x r) ≤ ENNReal.ofReal (C * (r / r') ^ s) * μ (ball x' r') := by
  obtain ⟨C₁, hC₁, hup⟩ := exists_doublingUpTo (X := X) Cd R₁
  obtain ⟨C', hC'1, hC'2⟩ : ∃ C' : ℝ≥0, C₁ ≤ C' ∧ 2 ≤ C' := ⟨max C₁ 2, le_max_left _ _,
    le_max_right _ _⟩
  have hC2 : (2 : ℝ) ≤ C' := by exact_mod_cast hC'2
  refine ⟨(C' : ℝ) ^ 2, Real.logb 2 C', pow_pos (by linarith) 2,
    Real.logb_pos (by norm_num) (by linarith), fun μ hμ x x' r r' hr' hrr hrR hxx' ↦ ?_⟩
  exact ((hup μ hμ).mono hC'1 le_rfl).measure_ball_le_rpow (le_trans (by norm_num) hC'2)
    x x' hr' hrr hrR hxx'

theorem rpow_le_measure_ball_quant [BallGeometry X] (Cd : ℝ≥0) (R₁ : ℝ) :
    ∃ c δ : ℝ, 0 < c ∧ 0 < δ ∧ ∀ μ : Measure X, IsLocDoublingMWith μ Cd →
      ∀ (x x' : X) (r r' : ℝ), 0 < r' → r' ≤ r → r ≤ R₁ → dist x x' ≤ r →
        ENNReal.ofReal (c * (r / r') ^ δ) * μ (ball x' r') ≤ μ (ball x r) := by
  obtain ⟨C₁, hC₁, hup⟩ := exists_doublingUpTo (X := X) Cd (2 * R₁)
  have hC0 : (0 : ℝ) < C₁ := by
    have : (1 : ℝ) ≤ C₁ := by exact_mod_cast hC₁
    linarith
  have hη : (0 : ℝ) < ((C₁ : ℝ) ^ 3)⁻¹ := inv_pos.2 (pow_pos hC0 3)
  refine ⟨1 / ((C₁ : ℝ) * (1 + ((C₁ : ℝ) ^ 3)⁻¹)), Real.logb 2 (1 + ((C₁ : ℝ) ^ 3)⁻¹),
    div_pos one_pos (mul_pos hC0 (by linarith)), Real.logb_pos (by norm_num) (by linarith),
    fun μ hμ x x' r r' hr' hrr hrR hxx' ↦
      (hup μ hμ).rpow_le_measure_ball hC₁ x x' hr' hrr hrR hxx'⟩

/-- **Lemma 1**, uniform form. -/
theorem lemma1_quant [BallGeometry X] (Cd : ℝ≥0) (R₁ : ℝ) :
    ∃ γ A : ℝ, 0 < γ ∧ γ ≤ 1 ∧ 0 < A ∧ ∀ μ : Measure X, IsLocDoublingMWith μ Cd →
      ∀ (x x' : X) (r r' : ℝ), 0 < r' → r ≤ R₁ → dist x x' + r' ≤ r →
        0 < μ (ball x' r') → μ (ball x r) < ∞ →
        ((μ (ball x r)).toReal / (μ (ball x' r')).toReal) ^ γ ≤ A * (r / r') ∧
        r / r' ≤ A * ((μ (ball x r)).toReal / (μ (ball x' r')).toReal) ^ (1 / γ) := by
  obtain ⟨CU, s, hCU, hs, hup⟩ := measure_ball_le_rpow_quant (X := X) Cd R₁
  obtain ⟨c, δ, hc, hδ, hlow⟩ := rpow_le_measure_ball_quant (X := X) Cd R₁
  set γ := min 1 (min (1 / s) δ) with hγ
  have hγpos : 0 < γ := lt_min one_pos (lt_min (by positivity) hδ)
  have hγ1 : γ ≤ 1 := min_le_left _ _
  have hγs : γ ≤ 1 / s := (min_le_right _ _).trans (min_le_left _ _)
  have hγδ : γ ≤ δ := (min_le_right _ _).trans (min_le_right _ _)
  set A := max (max CU 1) ((1 / c) ^ (1 / δ)) with hA
  have hA1 : 1 ≤ A := (le_max_right _ _).trans (le_max_left _ _)
  refine ⟨γ, A, hγpos, hγ1, by linarith, fun μ hμ x x' r r' hr' hrR hdist hpos hfin ↦ ?_⟩
  have hd0 := dist_nonneg (x := x) (y := x')
  have hxx' : dist x x' ≤ r := by linarith
  have hrr : r' ≤ r := by linarith
  have hsub : ball x' r' ⊆ ball x r := fun w hw ↦ by
    rw [mem_ball] at hw ⊢
    linarith [dist_triangle w x' x, dist_comm x x']
  have hfin' : μ (ball x' r') < ∞ := (measure_mono hsub).trans_lt hfin
  set a := (μ (ball x r)).toReal with ha
  set b := (μ (ball x' r')).toReal with hb
  have hb0 : 0 < b := ENNReal.toReal_pos hpos.ne' hfin'.ne
  have hba : b ≤ a := ENNReal.toReal_mono hfin.ne (measure_mono hsub)
  set q := r / r' with hq
  have hq1 : 1 ≤ q := (one_le_div hr').2 hrr
  have hQ1 : 1 ≤ a / b := (one_le_div hb0).2 hba
  have hU : a / b ≤ CU * q ^ s := by
    have h1 := hup μ hμ x x' r r' hr' hrr hrR hxx'
    have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin'.ne) h1
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at h2
    rw [div_le_iff₀ hb0]
    exact h2
  have hL : c * q ^ δ ≤ a / b := by
    have h1 := hlow μ hμ x x' r r' hr' hrr hrR hxx'
    have h2 := ENNReal.toReal_mono hfin.ne h1
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at h2
    rw [le_div_iff₀ hb0]
    exact h2
  have hM1 : (1 : ℝ) ≤ max CU 1 := le_max_right _ _
  constructor
  · calc (a / b) ^ γ ≤ (max CU 1 * q ^ s) ^ γ :=
          Real.rpow_le_rpow (by positivity)
            (hU.trans (by gcongr; exact le_max_left _ _)) hγpos.le
      _ = (max CU 1) ^ γ * q ^ (s * γ) := by
          rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul (by positivity)]
      _ ≤ max CU 1 * q := by
          have hsγ : s * γ ≤ 1 := by
            have := (le_div_iff₀ hs).1 hγs
            linarith
          gcongr
          · calc (max CU 1) ^ γ ≤ (max CU 1) ^ (1 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le hM1 hγ1
              _ = max CU 1 := Real.rpow_one _
          · calc q ^ (s * γ) ≤ q ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hq1 hsγ
              _ = q := Real.rpow_one _
      _ ≤ A * q := by gcongr; exact le_max_left _ _
  · have h1 : q ^ δ ≤ a / b / c := by rw [le_div_iff₀ hc]; linarith
    have h2 : q ≤ (a / b / c) ^ (1 / δ) := le_rpow_one_div_of_rpow_le (by positivity) hδ h1
    calc q ≤ (a / b / c) ^ (1 / δ) := h2
      _ = (1 / c) ^ (1 / δ) * (a / b) ^ (1 / δ) := by
          rw [div_eq_mul_one_div (a / b) c, Real.mul_rpow (by positivity) (by positivity),
            mul_comm]
      _ ≤ A * (a / b) ^ (1 / γ) := by
          gcongr
          exact le_max_right _ _

theorem measure_ball_massRadiusM_bounds_quant [BallGeometry X]
    [TopologicalSpace.SeparableSpace X] (Cd : ℝ≥0) (R₀ R₁ : ℝ) :
    ∃ c C δ s : ℝ, 0 < c ∧ 0 < C ∧ 0 < δ ∧ 0 < s ∧ ∀ μ : Measure X, MeasClassM μ Cd R₀ →
      ∀ (x : X) (r : ℝ), massRadiusM μ x ≤ r → r ≤ R₁ →
        ENNReal.ofReal (c * (r / massRadiusM μ x) ^ δ) ≤ μ (ball x r) ∧
        μ (ball x r) ≤ ENNReal.ofReal (C * (r / massRadiusM μ x) ^ s) := by
  obtain ⟨CU, s, hCU, hs, hup⟩ := measure_ball_le_rpow_quant (X := X) Cd R₁
  obtain ⟨c, δ, hc, hδ, hlow⟩ := rpow_le_measure_ball_quant (X := X) Cd R₁
  refine ⟨c, CU, δ, s, hc, hCU, hδ, hs, fun μ h x r h1 h2 ↦ ?_⟩
  have hρ := h.massRadiusM_pos x
  have h1' : μ (ball x (massRadiusM μ x)) = 1 :=
    IsLocDoublingM.measure_ball_massRadiusM h.doubling.isLocDoublingM h.finite (h.hne x)
  have hxx : dist x x ≤ r := by rw [dist_self]; linarith
  constructor
  · have := hlow μ h.doubling x x r (massRadiusM μ x) hρ h1 h2 hxx
    rwa [h1', mul_one] at this
  · have := hup μ h.doubling x x r (massRadiusM μ x) hρ h1 h2 hxx
    rwa [h1', mul_one] at this

theorem measure_ball_massRadiusM_quant [BallGeometry X] (Cd : ℝ≥0) (R₀ K : ℝ) :
    ∃ C : ℝ≥0, ∀ μ : Measure X, MeasClassM μ Cd R₀ → ∀ x : X,
      μ (ball x (K * massRadiusM μ x)) ≤ C := by
  obtain ⟨CU, s, hCU, hs, hup⟩ := measure_ball_le_rpow_quant (X := X) Cd (max K 1 * R₀)
  refine ⟨Real.toNNReal (CU * (max K 1) ^ s), fun μ h x ↦ ?_⟩
  have hρ := h.massRadiusM_pos x
  have hρR := h.massRadiusM_le x
  have hK' : (1 : ℝ) ≤ max K 1 := le_max_right _ _
  calc μ (ball x (K * massRadiusM μ x)) ≤ μ (ball x (max K 1 * massRadiusM μ x)) :=
        measure_mono (ball_subset_ball (mul_le_mul_of_nonneg_right (le_max_left _ _) hρ.le))
    _ ≤ ENNReal.ofReal (CU * (max K 1 * massRadiusM μ x / massRadiusM μ x) ^ s) *
          μ (ball x (massRadiusM μ x)) :=
        hup μ h.doubling x x _ _ hρ (by nlinarith)
          (mul_le_mul_of_nonneg_left hρR (by linarith)) (by rw [dist_self]; nlinarith)
    _ ≤ ENNReal.ofReal (CU * (max K 1) ^ s) * 1 := by
        rw [mul_div_assoc, div_self hρ.ne', mul_one]
        gcongr
        exact measure_ball_massRadiusM_le_one μ x
    _ = _ := by rw [mul_one]; rfl

/-- **Claim 1**, uniform form, with `0 < ρ ≤ R₀`. -/
theorem claim1_quant [BallGeometry X] (Cd : ℝ≥0) (R₀ K : ℝ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ μ : Measure X, MeasClassM μ Cd R₀ → ∀ x y : X,
      0 < massRadiusM μ x ∧ massRadiusM μ x ≤ R₀ ∧
      (dist x y ≤ K * max (massRadiusM μ x) (massRadiusM μ y) →
        massRadiusM μ x ≤ C * massRadiusM μ y) := by
  set K' := max K 0 with hK'def
  have hK'0 : 0 ≤ K' := le_max_right _ _
  obtain ⟨CU, s, hCU, hs, hup⟩ := measure_ball_le_rpow_quant (X := X) Cd ((K' + 2) * R₀)
  obtain ⟨c, δ, hc, hδ, hlow⟩ := rpow_le_measure_ball_quant (X := X) Cd ((K' + 2) * R₀)
  set B := (CU * (K' + 1) ^ s / c) ^ (1 / δ) with hB
  refine ⟨max 2 (2 * B), le_trans (by norm_num) (le_max_left _ _),
    fun μ h x y ↦ ⟨h.massRadiusM_pos x, h.massRadiusM_le x, fun hxy ↦ ?_⟩⟩
  have hρx := h.massRadiusM_pos x
  have hρy := h.massRadiusM_pos y
  have hR₀ := h.R₀_pos x
  have hρxR := h.massRadiusM_le x
  by_cases hcase : massRadiusM μ x ≤ 2 * massRadiusM μ y
  · exact hcase.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hρy.le)
  replace hcase := not_le.1 hcase
  have hmax : max (massRadiusM μ x) (massRadiusM μ y) = massRadiusM μ x :=
    max_eq_left (by linarith)
  have hd : dist x y ≤ K' * massRadiusM μ x := by
    rw [hmax] at hxy
    exact hxy.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hρx.le)
  have h1 := hlow μ h.doubling y y (massRadiusM μ x) (2 * massRadiusM μ y) (by linarith)
    hcase.le (by nlinarith) (by rw [dist_self]; linarith)
  have h2 : ball y (massRadiusM μ x) ⊆ ball x ((K' + 1) * massRadiusM μ x) := fun w hw ↦ by
    rw [mem_ball] at hw ⊢
    have := dist_triangle w y x
    rw [dist_comm y x] at this
    nlinarith
  have h3 := hup μ h.doubling x x ((K' + 1) * massRadiusM μ x) (massRadiusM μ x) hρx
    (by nlinarith) (by nlinarith) (by rw [dist_self]; positivity)
  rw [mul_div_assoc, div_self hρx.ne', mul_one] at h3
  have hchain : ENNReal.ofReal (c * (massRadiusM μ x / (2 * massRadiusM μ y)) ^ δ) ≤
      ENNReal.ofReal (CU * (K' + 1) ^ s) := by
    calc ENNReal.ofReal (c * (massRadiusM μ x / (2 * massRadiusM μ y)) ^ δ)
        = ENNReal.ofReal (c * (massRadiusM μ x / (2 * massRadiusM μ y)) ^ δ) * 1 :=
          (mul_one _).symm
      _ ≤ ENNReal.ofReal (c * (massRadiusM μ x / (2 * massRadiusM μ y)) ^ δ) *
            μ (ball y (2 * massRadiusM μ y)) := by gcongr; exact h.one_le_two y
      _ ≤ μ (ball y (massRadiusM μ x)) := h1
      _ ≤ μ (ball x ((K' + 1) * massRadiusM μ x)) := measure_mono h2
      _ ≤ ENNReal.ofReal (CU * (K' + 1) ^ s) * μ (ball x (massRadiusM μ x)) := h3
      _ ≤ ENNReal.ofReal (CU * (K' + 1) ^ s) * 1 := by
          gcongr; exact measure_ball_massRadiusM_le_one μ x
      _ = _ := mul_one _
  rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at hchain
  have hq : (massRadiusM μ x / (2 * massRadiusM μ y)) ^ δ ≤ CU * (K' + 1) ^ s / c := by
    rw [le_div_iff₀ hc]; linarith
  have hq' := le_rpow_one_div_of_rpow_le (by positivity) hδ hq
  rw [← hB, div_le_iff₀ (by positivity)] at hq'
  calc massRadiusM μ x ≤ B * (2 * massRadiusM μ y) := hq'
    _ = 2 * B * massRadiusM μ y := by ring
    _ ≤ max 2 (2 * B) * massRadiusM μ y :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) hρy.le

/-- **Decay**, power form, uniform. -/
theorem massRadiusM_div_dist_le_quant [BallGeometry X] (Cd : ℝ≥0) (R₀ M₀ : ℝ) :
    ∃ C α : ℝ, 0 < C ∧ 0 < α ∧ α ≤ 1 ∧ ∀ μ : Measure X, MeasClassM μ Cd R₀ → ∀ z ζ : X,
      massRadiusM μ z ≤ dist z ζ → dist z ζ ≤ M₀ →
        massRadiusM μ ζ / dist z ζ ≤ C * (massRadiusM μ z / dist z ζ) ^ α := by
  obtain ⟨CU, s, hCU, hs, hup⟩ := measure_ball_le_rpow_quant (X := X) Cd (3 * M₀)
  obtain ⟨c, δ, hc, hδ, hlow⟩ := rpow_le_measure_ball_quant (X := X) Cd (3 * M₀)
  refine ⟨(CU * 3 ^ s / c) ^ (1 / s), min 1 (δ / s), by positivity,
    lt_min one_pos (by positivity), min_le_left _ _, fun μ h z ζ h1 h2 ↦ ?_⟩
  set d := dist z ζ with hd
  have hρz := h.massRadiusM_pos z
  have hρζ := h.massRadiusM_pos ζ
  have hd0 : 0 < d := hρz.trans_le h1
  have hlip : massRadiusM μ ζ ≤ massRadiusM μ z + d := h.le_add_dist z ζ
  have hU := hup μ h.doubling z ζ (3 * d) (massRadiusM μ ζ) hρζ (by linarith) (by linarith)
    (by linarith)
  have hL := hlow μ h.doubling z z (3 * d) (2 * massRadiusM μ z) (by linarith) (by linarith)
    (by linarith) (by rw [dist_self]; linarith)
  have hchain : ENNReal.ofReal (c * (3 * d / (2 * massRadiusM μ z)) ^ δ) ≤
      ENNReal.ofReal (CU * (3 * d / massRadiusM μ ζ) ^ s) := by
    calc ENNReal.ofReal (c * (3 * d / (2 * massRadiusM μ z)) ^ δ)
        = ENNReal.ofReal (c * (3 * d / (2 * massRadiusM μ z)) ^ δ) * 1 := (mul_one _).symm
      _ ≤ ENNReal.ofReal (c * (3 * d / (2 * massRadiusM μ z)) ^ δ) *
            μ (ball z (2 * massRadiusM μ z)) := by gcongr; exact h.one_le_two z
      _ ≤ μ (ball z (3 * d)) := hL
      _ ≤ ENNReal.ofReal (CU * (3 * d / massRadiusM μ ζ) ^ s) * μ (ball ζ (massRadiusM μ ζ)) :=
          hU
      _ ≤ ENNReal.ofReal (CU * (3 * d / massRadiusM μ ζ) ^ s) * 1 := by
          gcongr; exact measure_ball_massRadiusM_le_one μ ζ
      _ = _ := mul_one _
  rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at hchain
  have e1 : 3 * d / (2 * massRadiusM μ z) = 3 / (2 * (massRadiusM μ z / d)) := by
    field_simp
  have e2 : 3 * d / massRadiusM μ ζ = 3 / (massRadiusM μ ζ / d) := by field_simp
  rw [e1, e2] at hchain
  exact decay_algebra hc hCU hδ hs (by positivity) (by positivity)
    ((div_le_one hd0).2 h1) hchain

/-- **Decay**, geometric form, uniform. -/
theorem decay_quant [BallGeometry X] (Cd : ℝ≥0) (R₀ M₀ : ℝ) :
    ∃ C θ : ℝ, 0 < C ∧ 0 < θ ∧ θ < 1 ∧ ∀ μ : Measure X, MeasClassM μ Cd R₀ →
      ∀ (z ζ : X) (n : ℕ), 2 ^ n * massRadiusM μ z ≤ dist z ζ → dist z ζ ≤ M₀ →
        massRadiusM μ ζ / dist z ζ ≤ C * θ ^ n := by
  obtain ⟨C, α, hC, hα, hα1, h⟩ := massRadiusM_div_dist_le_quant (X := X) Cd R₀ M₀
  refine ⟨C, (1 / 2) ^ α, hC, by positivity, Real.rpow_lt_one (by norm_num) (by norm_num) hα,
    fun μ hμ z ζ n h1 h2 ↦ ?_⟩
  have hρz := hμ.massRadiusM_pos z
  have h2n : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  have hρd : massRadiusM μ z ≤ dist z ζ := by nlinarith
  have hd : 0 < dist z ζ := hρz.trans_le hρd
  have key := h μ hμ z ζ hρd h2
  refine key.trans (mul_le_mul_of_nonneg_left ?_ hC.le)
  have hb : massRadiusM μ z / dist z ζ ≤ (1 / 2) ^ n := by
    rw [div_le_iff₀ hd]
    have e : (1 / 2 : ℝ) ^ n * 2 ^ n = 1 := by rw [← mul_pow]; norm_num
    nlinarith
  calc (massRadiusM μ z / dist z ζ) ^ α ≤ ((1 / 2 : ℝ) ^ n) ^ α :=
        Real.rpow_le_rpow (by positivity) hb hα.le
    _ = ((1 / 2 : ℝ) ^ α) ^ n := by
        rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
          ← Real.rpow_mul (by norm_num), mul_comm]

/-- **Lemma 3**, truncated form, uniform. -/
theorem lemma3_quant [BallGeometry X] [TopologicalSpace.SeparableSpace X] (Cd : ℝ≥0) (R₀ : ℝ) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ δ R₁ : ℝ, 0 < δ → ∃ C : ℝ≥0,
      ∀ μ : Measure X, MeasClassM μ Cd R₀ → ∀ w : X,
        ∫⁻ z in ball w R₁,
          ENNReal.ofReal ((massRadiusM μ z / max (dist z w) (δ * massRadiusM μ w)) ^ m) ∂μ ≤ C :=
  sorry

/-- **[Chr91, Lemma 2.3]**, uniform form. -/
theorem christ_lemma23_quant [BallGeometry X] (Cd : ℝ≥0) (R₁ : ℝ) :
    ∃ C : ℝ≥0, ∀ μ : Measure X, IsLocDoublingMWith μ Cd → ∀ (x : X) (R : ℝ), 0 < R → R ≤ R₁ →
      ∫⁻ y in ball x R, ENNReal.ofReal (Real.log (R / dist x y)) ∂μ ≤ C * μ (ball x R) := sorry

/-- Mass radius of `N⁻¹ μ` versus `μ`, uniform. -/
theorem massRadiusM_inv_smul_quant [BallGeometry X] (Cd : ℝ≥0) (R₀ : ℝ) (N : ℕ) (hN : 1 ≤ N) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ μ : Measure X, MeasClassM μ Cd R₀ → ∀ x : X,
      massRadiusM μ x ≤ massRadiusM ((N : ℝ≥0∞)⁻¹ • μ) x ∧
        massRadiusM ((N : ℝ≥0∞)⁻¹ • μ) x ≤ C * massRadiusM μ x := by
  obtain ⟨c, δ, hc, hδ, hlow⟩ := rpow_le_measure_ball_quant (X := X) Cd ((2 * N + 1) * R₀)
  refine ⟨max 4 (4 * ((N : ℝ) / c) ^ (1 / δ)), le_trans (by norm_num) (le_max_left _ _),
    fun μ h x ↦ ?_⟩
  have hR₀ := h.R₀_pos x
  have hN0 : (N : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hNt : (N : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top N
  have hsmul : ∀ s, ((N : ℝ≥0∞)⁻¹ • μ) s = (N : ℝ≥0∞)⁻¹ * μ s := fun s ↦ by
    rw [Measure.smul_apply, smul_eq_mul]
  have hRN : 0 < (2 * (N : ℝ) + 1) * R₀ := by positivity
  have hgrow : (N : ℝ≥0∞) ≤ μ (ball x ((2 * N + 1) * R₀)) := by
    refine le_trans ?_ (sum_le_measure_ball_of_le hR₀ h.mass x N)
    rw [mul_one]
    exact le_self_add
  have hneN : 1 ≤ ((N : ℝ≥0∞)⁻¹ • μ) (ball x ((2 * N + 1) * R₀)) := by
    rw [hsmul]
    calc (1 : ℝ≥0∞) = (N : ℝ≥0∞)⁻¹ * N := (ENNReal.inv_mul_cancel hN0 hNt).symm
      _ ≤ (N : ℝ≥0∞)⁻¹ * μ (ball x ((2 * N + 1) * R₀)) := by gcongr
  constructor
  · show sInf _ ≤ sInf _
    refine csInf_le_csInf ⟨0, fun r hr ↦ hr.1.le⟩ ⟨_, hRN, hneN⟩ ?_
    rintro r ⟨hr, h1⟩
    refine ⟨hr, ?_⟩
    rw [hsmul] at h1
    calc (1 : ℝ≥0∞) ≤ N := by exact_mod_cast hN
      _ = N * 1 := (mul_one _).symm
      _ ≤ N * ((N : ℝ≥0∞)⁻¹ * μ (ball x r)) := by gcongr
      _ = μ (ball x r) := by rw [← mul_assoc, ENNReal.mul_inv_cancel hN0 hNt, one_mul]
  · set ρ := massRadiusM μ x with hρdef
    set ρN := massRadiusM ((N : ℝ≥0∞)⁻¹ • μ) x with hρNdef
    have hρ : 0 < ρ := h.massRadiusM_pos x
    have hρN : ρN ≤ (2 * N + 1) * R₀ := massRadiusM_le hRN hneN
    by_cases hcase : ρN ≤ 4 * ρ
    · exact hcase.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hρ.le)
    replace hcase := not_le.1 hcase
    have hlt : μ (ball x (ρN / 2)) < N := by
      have h1 := measure_ball_lt_one_of_lt_massRadiusM (μ := (N : ℝ≥0∞)⁻¹ • μ) (x := x)
        (r := ρN / 2) (by linarith)
      rw [hsmul] at h1
      by_contra hge
      replace hge := not_lt.1 hge
      have : (1 : ℝ≥0∞) ≤ (N : ℝ≥0∞)⁻¹ * μ (ball x (ρN / 2)) := by
        calc (1 : ℝ≥0∞) = (N : ℝ≥0∞)⁻¹ * N := (ENNReal.inv_mul_cancel hN0 hNt).symm
          _ ≤ _ := by gcongr
      exact absurd h1 (not_lt.2 this)
    have key := hlow μ h.doubling x x (ρN / 2) (2 * ρ) (by linarith) (by linarith)
      (by linarith) (by rw [dist_self]; linarith)
    have hchain : ENNReal.ofReal (c * (ρN / 2 / (2 * ρ)) ^ δ) < ENNReal.ofReal N := by
      calc ENNReal.ofReal (c * (ρN / 2 / (2 * ρ)) ^ δ)
          = ENNReal.ofReal (c * (ρN / 2 / (2 * ρ)) ^ δ) * 1 := (mul_one _).symm
        _ ≤ ENNReal.ofReal (c * (ρN / 2 / (2 * ρ)) ^ δ) * μ (ball x (2 * ρ)) := by
            gcongr; exact h.one_le_two x
        _ ≤ μ (ball x (ρN / 2)) := key
        _ < N := hlt
        _ = ENNReal.ofReal N := (ENNReal.ofReal_natCast N).symm
    rw [ENNReal.ofReal_lt_ofReal_iff (by positivity)] at hchain
    have hq : (ρN / 2 / (2 * ρ)) ^ δ ≤ N / c := by rw [le_div_iff₀ hc]; linarith
    have hq' := le_rpow_one_div_of_rpow_le (div_nonneg (by linarith) (by linarith)) hδ hq
    rw [div_le_iff₀ (by linarith)] at hq'
    calc ρN ≤ 4 * ((N : ℝ) / c) ^ (1 / δ) * ρ := by linarith
      _ ≤ max 4 (4 * ((N : ℝ) / c) ^ (1 / δ)) * ρ :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hρ.le

end AbstractQuant

/-! ### Transfer of the classes to the abstract setting -/

theorem MeasClassPlane.measClassM {μ : Measure ℂ} {Cd : ℝ≥0} {R₀ : ℝ}
    (h : MeasClassPlane μ Cd R₀) : MeasClassM μ Cd R₀ :=
  ⟨h.doubling, fun z ↦ (h.mass z).le, fun z r ↦
    (measure_mono ball_subset_closedBall).trans_lt (h.finite _ (isCompact_closedBall z r))⟩

theorem MeasClassDisc.measClassM_discPull {μ : Measure ℂ} {Cd : ℝ≥0} {R₀ : ℝ}
    (h : MeasClassDisc μ Cd R₀) : MeasClassM (discPull μ) Cd R₀ := sorry

theorem MeasClassLine.measClassM_linePull {μ : Measure ℂ} {Cd : ℝ≥0} {R₀ : ℝ}
    (h : MeasClassLine μ Cd R₀) : MeasClassM (linePull μ) Cd R₀ := sorry

theorem MeasClassPlane.of_weight {φ : ℂ → ℝ} {μ : Measure ℂ} {Cd : ℝ≥0} {R₀ : ℝ}
    (hφ : IsSubharmonicWeight univ φ μ) (hd : IsLocallyDoublingWith μ Cd)
    (hm : ∀ z : ℂ, 1 < μ (ball z R₀)) : MeasClassPlane μ Cd R₀ :=
  ⟨hd, hm, fun K hK ↦ hφ.finite_of_compact K (subset_univ K) hK⟩

theorem MeasClassDisc.of_weight {φ : ℂ → ℝ} {μ : Measure ℂ} {Cd : ℝ≥0} {R₀ : ℝ}
    (hφ : IsSubharmonicWeight 𝔻 φ μ) (hd : IsLocallyDoublingDiscWith μ Cd)
    (hm : ∀ z ∈ 𝔻, 1 < μ (hypBall z R₀)) : MeasClassDisc μ Cd R₀ :=
  ⟨hd, hm, fun K hK hKc ↦ hφ.finite_of_compact K hK hKc⟩

/-! ### Quantitative lemmas (requested by M08 §4.1) -/

/-- (M03, growth + scaling) `lapNorm` stays in a class; `ρ` and `ρ̃` are comparable. -/
theorem MeasClassPlane.lapNorm {μ : Measure ℂ} {Cd : ℝ≥0} {R₀ : ℝ} (h : MeasClassPlane μ Cd R₀) :
    MeasClassPlane (lapNorm μ) Cd (15 * R₀) := sorry
theorem MeasClassDisc.lapNorm {μ : Measure ℂ} {Cd : ℝ≥0} {R₀ : ℝ} (h : MeasClassDisc μ Cd R₀) :
    MeasClassDisc (lapNorm μ) Cd (15 * R₀) := sorry
theorem massRadius_lapNorm_quant (Cd : ℝ≥0) (R₀ : ℝ) : ∃ C : ℝ, 1 ≤ C ∧
    ∀ μ : Measure ℂ, MeasClassPlane μ Cd R₀ → ∀ z,
      massRadius μ z ≤ massRadius (lapNorm μ) z ∧ massRadius (lapNorm μ) z ≤ C * massRadius μ z :=
  sorry
theorem massRadiusDisc_lapNorm_quant (Cd : ℝ≥0) (R₀ : ℝ) : ∃ C : ℝ, 1 ≤ C ∧
    ∀ μ : Measure ℂ, MeasClassDisc μ Cd R₀ → ∀ z ∈ 𝔻,
      massRadiusDisc μ z ≤ massRadiusDisc (lapNorm μ) z ∧
        massRadiusDisc (lapNorm μ) z ≤ C * massRadiusDisc μ z := sorry

/-- (M03, quantitative Claim 1 + positivity/upper bound of `ρ`). -/
theorem claim1_plane_quant (Cd : ℝ≥0) (R₀ K : ℝ) : ∃ C : ℝ, 1 ≤ C ∧
    ∀ ν : Measure ℂ, MeasClassPlane ν Cd R₀ → ∀ z w : ℂ,
      0 < massRadius ν z ∧ massRadius ν z ≤ R₀ ∧
      (dist z w ≤ K * max (massRadius ν z) (massRadius ν w) →
        massRadius ν z ≤ C * massRadius ν w) := sorry
theorem claim1_disc_quant (Cd : ℝ≥0) (R₀ K : ℝ) : ∃ C : ℝ, 1 ≤ C ∧
    ∀ ν : Measure ℂ, MeasClassDisc ν Cd R₀ → ∀ z ∈ 𝔻, ∀ w ∈ 𝔻,
      0 < massRadiusDisc ν z ∧ massRadiusDisc ν z ≤ R₀ ∧
      (hypDist z w ≤ K * max (massRadiusDisc ν z) (massRadiusDisc ν w) →
        massRadiusDisc ν z ≤ C * massRadiusDisc ν w) := sorry

/-- (M03, quantitative) mass of comparable balls. -/
theorem measure_ball_massRadius_quant (Cd : ℝ≥0) (R₀ K : ℝ) : ∃ C : ℝ≥0,
    ∀ ν : Measure ℂ, MeasClassPlane ν Cd R₀ → ∀ z, ν (ball z (K * massRadius ν z)) ≤ C := sorry
theorem measure_hypBall_massRadius_quant (Cd : ℝ≥0) (R₀ K : ℝ) : ∃ C : ℝ≥0,
    ∀ ν : Measure ℂ, MeasClassDisc ν Cd R₀ → ∀ z ∈ 𝔻,
      ν (hypBall z (K * massRadiusDisc ν z)) ≤ C := sorry

/-- (M03, quantitative decay; `massRadiusM_div_dist_le` with `M₀ = 1/4`). -/
theorem decay_plane_quant (Cd : ℝ≥0) (R₀ : ℝ) : ∃ C α : ℝ, 0 < C ∧ 0 < α ∧
    ∀ ν : Measure ℂ, MeasClassPlane ν Cd R₀ → ∀ z ζ : ℂ,
      massRadius ν z ≤ dist z ζ → dist z ζ ≤ 1 / 4 →
        massRadius ν ζ / dist z ζ ≤ C * (massRadius ν z / dist z ζ) ^ α := sorry
theorem decay_disc_quant (Cd : ℝ≥0) (R₀ : ℝ) : ∃ C α : ℝ, 0 < C ∧ 0 < α ∧
    ∀ ν : Measure ℂ, MeasClassDisc ν Cd R₀ → ∀ z ∈ 𝔻, ∀ ζ ∈ 𝔻,
      massRadiusDisc ν z ≤ hypDist z ζ → hypDist z ζ ≤ 1 / 4 →
        massRadiusDisc ν ζ / hypDist z ζ ≤ C * (massRadiusDisc ν z / hypDist z ζ) ^ α := sorry

/-- (M03, quantitative [Chr91, Lemma 2.3]). -/
theorem christ_plane_quant (Cd : ℝ≥0) (R₀ S : ℝ) : ∃ C : ℝ≥0,
    ∀ ν : Measure ℂ, MeasClassPlane ν Cd R₀ → ∀ z : ℂ, ∀ s : ℝ, 0 < s → s ≤ S →
      ∫⁻ ζ in ball z s, ENNReal.ofReal (Real.log (s / dist z ζ)) ∂ν ≤ C * ν (ball z s) := sorry
theorem christ_disc_quant (Cd : ℝ≥0) (R₀ S : ℝ) : ∃ C : ℝ≥0,
    ∀ ν : Measure ℂ, MeasClassDisc ν Cd R₀ → ∀ z ∈ 𝔻, ∀ s : ℝ, 0 < s → s ≤ S →
      ∫⁻ ζ in hypBall z s, ENNReal.ofReal (Real.log (s / hypDist z ζ)) ∂ν ≤
        C * ν (hypBall z s) := sorry


/-! ### Line forms (uniform) -/

theorem claim1_line_quant (Cd : ℝ≥0) (R₀ K : ℝ) : ∃ C : ℝ, 1 ≤ C ∧
    ∀ ν : Measure ℂ, MeasClassLine ν Cd R₀ → ∀ x y : ℝ,
      0 < massRadiusLine ν x ∧ massRadiusLine ν x ≤ R₀ ∧
      (|x - y| ≤ K * max (massRadiusLine ν x) (massRadiusLine ν y) →
        massRadiusLine ν x ≤ C * massRadiusLine ν y) := sorry

theorem decay_line_quant (Cd : ℝ≥0) (R₀ : ℝ) : ∃ C α : ℝ, 0 < C ∧ 0 < α ∧
    ∀ ν : Measure ℂ, MeasClassLine ν Cd R₀ → ∀ x y : ℝ,
      massRadiusLine ν x ≤ |x - y| → |x - y| ≤ 1 / 4 →
        massRadiusLine ν y / |x - y| ≤ C * (massRadiusLine ν x / |x - y|) ^ α := sorry

theorem christ_line_quant (Cd : ℝ≥0) (R₀ S : ℝ) : ∃ C : ℝ≥0,
    ∀ ν : Measure ℂ, MeasClassLine ν Cd R₀ → ∀ x : ℝ, ∀ s : ℝ, 0 < s → s ≤ S →
      ∫⁻ z in lineInterval x s, ENNReal.ofReal (Real.log (s / |z.re - x|)) ∂ν ≤
        C * ν (lineInterval x s) := sorry

end OC
