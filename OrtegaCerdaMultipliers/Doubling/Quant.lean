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

theorem MeasClassM.R₀_pos_m03b (h : MeasClassM μ Cd R₀) (x : X) : 0 < R₀ := by
  by_contra hR
  have h1 := h.mass x
  rw [ball_eq_empty.2 (not_lt.1 hR), measure_empty] at h1
  exact absurd h1 (by norm_num)

theorem MeasClassM.hne_m03b (h : MeasClassM μ Cd R₀) (x : X) : ∃ r, 0 < r ∧ 1 ≤ μ (ball x r) :=
  ⟨R₀, h.R₀_pos_m03b x, h.mass x⟩

theorem MeasClassM.hm_m03b (h : MeasClassM μ Cd R₀) : ∃ R : ℝ, 0 < R ∧ ∀ x : X, 1 ≤ μ (ball x R) :=
  ⟨max R₀ 1, lt_max_of_lt_right one_pos,
    fun x ↦ (h.mass x).trans (measure_mono (ball_subset_ball (le_max_left _ _)))⟩

theorem MeasClassM.massRadiusM_pos_m03b [BallGeometry X] (h : MeasClassM μ Cd R₀) (x : X) :
    0 < massRadiusM μ x :=
  IsLocDoublingM.massRadiusM_pos h.doubling.isLocDoublingM h.finite (h.hne_m03b x)

theorem MeasClassM.massRadiusM_le_m03b (h : MeasClassM μ Cd R₀) (x : X) : massRadiusM μ x ≤ R₀ :=
  OC.massRadiusM_le (h.R₀_pos_m03b x) (h.mass x)

theorem MeasClassM.one_le_two_m03b [BallGeometry X] (h : MeasClassM μ Cd R₀) (x : X) :
    1 ≤ μ (ball x (2 * massRadiusM μ x)) :=
  (one_le_measure_closedBall_massRadiusM (h.finite x) (h.hne_m03b x)).trans
    (measure_mono (closedBall_subset_ball (by linarith [h.massRadiusM_pos_m03b x])))

theorem MeasClassM.le_add_dist_m03b (h : MeasClassM μ Cd R₀) (x y : X) :
    massRadiusM μ y ≤ massRadiusM μ x + dist x y := by
  have := (lipschitzWith_massRadiusM (μ := μ) h.hne_m03b).dist_le_mul x y
  rw [NNReal.coe_one, one_mul, Real.dist_eq] at this
  linarith [(abs_sub_le_iff.1 this).2]

end ClassHelpers

/-- The real algebra of the decay estimate (§3.13). -/
theorem M03b.decay_algebra {c CU δ s a b : ℝ} (hc : 0 < c) (hCU : 0 < CU) (hδ : 0 < δ) (hs : 0 < s)
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
  have h4 := M03b.le_rpow_one_div_of_rpow_le ha.le hs h3
  rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hb.le] at h4
  refine h4.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  rw [mul_one_div]
  exact Real.rpow_le_rpow_of_exponent_ge hb hb1 (min_le_right _ _)

theorem doubling_upTo_quant [BallGeometry X] (Cd : ℝ≥0) (R₁ : ℝ) :
    ∃ C : ℝ≥0, 1 ≤ C ∧ ∀ μ : Measure X, IsLocDoublingMWith μ Cd → ∀ x : X, ∀ r : ℝ, 0 < r →
      r ≤ R₁ → μ (ball x (2 * r)) ≤ C * μ (ball x r) := by
  obtain ⟨C, hC, h⟩ := M03b.exists_doublingUpTo (X := X) Cd R₁
  exact ⟨C, hC, fun μ hμ ↦ h μ hμ⟩

theorem measure_ball_le_rpow_quant [BallGeometry X] (Cd : ℝ≥0) (R₁ : ℝ) :
    ∃ C s : ℝ, 0 < C ∧ 0 < s ∧ ∀ μ : Measure X, IsLocDoublingMWith μ Cd →
      ∀ (x x' : X) (r r' : ℝ), 0 < r' → r' ≤ r → r ≤ R₁ → dist x x' ≤ r →
        μ (ball x r) ≤ ENNReal.ofReal (C * (r / r') ^ s) * μ (ball x' r') := by
  obtain ⟨C₁, hC₁, hup⟩ := M03b.exists_doublingUpTo (X := X) Cd R₁
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
  obtain ⟨C₁, hC₁, hup⟩ := M03b.exists_doublingUpTo (X := X) Cd (2 * R₁)
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
    have h2 : q ≤ (a / b / c) ^ (1 / δ) := M03b.le_rpow_one_div_of_rpow_le (by positivity) hδ h1
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
  have hρ := h.massRadiusM_pos_m03b x
  have h1' : μ (ball x (massRadiusM μ x)) = 1 :=
    IsLocDoublingM.measure_ball_massRadiusM h.doubling.isLocDoublingM h.finite (h.hne_m03b x)
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
  have hρ := h.massRadiusM_pos_m03b x
  have hρR := h.massRadiusM_le_m03b x
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
    fun μ h x y ↦ ⟨h.massRadiusM_pos_m03b x, h.massRadiusM_le_m03b x, fun hxy ↦ ?_⟩⟩
  have hρx := h.massRadiusM_pos_m03b x
  have hρy := h.massRadiusM_pos_m03b y
  have hR₀ := h.R₀_pos_m03b x
  have hρxR := h.massRadiusM_le_m03b x
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
            μ (ball y (2 * massRadiusM μ y)) := by gcongr; exact h.one_le_two_m03b y
      _ ≤ μ (ball y (massRadiusM μ x)) := h1
      _ ≤ μ (ball x ((K' + 1) * massRadiusM μ x)) := measure_mono h2
      _ ≤ ENNReal.ofReal (CU * (K' + 1) ^ s) * μ (ball x (massRadiusM μ x)) := h3
      _ ≤ ENNReal.ofReal (CU * (K' + 1) ^ s) * 1 := by
          gcongr; exact measure_ball_massRadiusM_le_one μ x
      _ = _ := mul_one _
  rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at hchain
  have hq : (massRadiusM μ x / (2 * massRadiusM μ y)) ^ δ ≤ CU * (K' + 1) ^ s / c := by
    rw [le_div_iff₀ hc]; linarith
  have hq' := M03b.le_rpow_one_div_of_rpow_le (by positivity) hδ hq
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
  have hρz := h.massRadiusM_pos_m03b z
  have hρζ := h.massRadiusM_pos_m03b ζ
  have hd0 : 0 < d := hρz.trans_le h1
  have hlip : massRadiusM μ ζ ≤ massRadiusM μ z + d := h.le_add_dist_m03b z ζ
  have hU := hup μ h.doubling z ζ (3 * d) (massRadiusM μ ζ) hρζ (by linarith) (by linarith)
    (by linarith)
  have hL := hlow μ h.doubling z z (3 * d) (2 * massRadiusM μ z) (by linarith) (by linarith)
    (by linarith) (by rw [dist_self]; linarith)
  have hchain : ENNReal.ofReal (c * (3 * d / (2 * massRadiusM μ z)) ^ δ) ≤
      ENNReal.ofReal (CU * (3 * d / massRadiusM μ ζ) ^ s) := by
    calc ENNReal.ofReal (c * (3 * d / (2 * massRadiusM μ z)) ^ δ)
        = ENNReal.ofReal (c * (3 * d / (2 * massRadiusM μ z)) ^ δ) * 1 := (mul_one _).symm
      _ ≤ ENNReal.ofReal (c * (3 * d / (2 * massRadiusM μ z)) ^ δ) *
            μ (ball z (2 * massRadiusM μ z)) := by gcongr; exact h.one_le_two_m03b z
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
  exact M03b.decay_algebra hc hCU hδ hs (by positivity) (by positivity)
    ((div_le_one hd0).2 h1) hchain

/-- **Decay**, geometric form, uniform. -/
theorem decay_quant [BallGeometry X] (Cd : ℝ≥0) (R₀ M₀ : ℝ) :
    ∃ C θ : ℝ, 0 < C ∧ 0 < θ ∧ θ < 1 ∧ ∀ μ : Measure X, MeasClassM μ Cd R₀ →
      ∀ (z ζ : X) (n : ℕ), 2 ^ n * massRadiusM μ z ≤ dist z ζ → dist z ζ ≤ M₀ →
        massRadiusM μ ζ / dist z ζ ≤ C * θ ^ n := by
  obtain ⟨C, α, hC, hα, hα1, h⟩ := massRadiusM_div_dist_le_quant (X := X) Cd R₀ M₀
  refine ⟨C, (1 / 2) ^ α, hC, by positivity, Real.rpow_lt_one (by norm_num) (by norm_num) hα,
    fun μ hμ z ζ n h1 h2 ↦ ?_⟩
  have hρz := hμ.massRadiusM_pos_m03b z
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

/-! #### Lemma 3, uniform (§3.14): real algebra, fine part, coarse part -/

/-- Pointwise bound on an annulus (§3.14 (F), steps 1–2). -/
theorem M03b.lemma3_pt {ρz t D V CU s : ℝ} {m : ℕ} (hρz : 0 < ρz) (ht : 0 < t) (htD : t ≤ D)
    (hV : 0 < V) (hCU : 0 < CU) (hs : 0 < s) (hup : V ≤ CU * (5 * t / ρz) ^ s) :
    (ρz / D) ^ m ≤ 5 ^ m * (CU / V) ^ ((m : ℝ) / s) := by
  have hpos : 0 < (ρz / (5 * t)) ^ s := by positivity
  have h1 : (ρz / (5 * t)) ^ s ≤ CU / V := by
    have e : (5 * t / ρz) ^ s = ((ρz / (5 * t)) ^ s)⁻¹ := by
      rw [← Real.inv_rpow (by positivity), inv_div]
    rw [e, ← div_eq_mul_inv, le_div_iff₀ hpos] at hup
    rw [le_div_iff₀ hV]
    linarith [mul_comm V ((ρz / (5 * t)) ^ s)]
  have h2 : ρz / (5 * t) ≤ (CU / V) ^ (1 / s) :=
    M03b.le_rpow_one_div_of_rpow_le (by positivity) hs h1
  have h3 : ρz / D ≤ 5 * (CU / V) ^ (1 / s) := by
    calc ρz / D ≤ ρz / t := div_le_div_of_nonneg_left hρz.le ht htD
      _ = 5 * (ρz / (5 * t)) := by field_simp
      _ ≤ 5 * (CU / V) ^ (1 / s) := by gcongr
  calc (ρz / D) ^ m ≤ (5 * (CU / V) ^ (1 / s)) ^ m :=
        pow_le_pow_left₀ (div_nonneg hρz.le (ht.le.trans htD)) h3 m
    _ = 5 ^ m * (CU / V) ^ ((m : ℝ) / s) := by
        rw [mul_pow, ← Real.rpow_natCast ((CU / V) ^ (1 / s)), ← Real.rpow_mul (by positivity)]
        congr 2
        ring

/-- Summation bound on an annulus (§3.14 (F), steps 3–5). -/
theorem M03b.lemma3_sum {V CU c s δr : ℝ} {m n : ℕ} (hs : 0 < s) (hms : s < m) (hc : 0 < c)
    (hCU : 0 < CU) (hL : c * ((2 : ℝ) ^ n) ^ δr ≤ V) :
    5 ^ m * (CU / V) ^ ((m : ℝ) / s) * V ≤
      5 ^ m * CU ^ ((m : ℝ) / s) * c ^ (1 - (m : ℝ) / s) *
        ((2 : ℝ) ^ (δr * (1 - (m : ℝ) / s))) ^ n := by
  have hLpos : 0 < c * ((2 : ℝ) ^ n) ^ δr := by positivity
  have hV : 0 < V := hLpos.trans_le hL
  have he : 1 - (m : ℝ) / s ≤ 0 := by
    rw [sub_nonpos, le_div_iff₀ hs]; linarith
  have e1 : 5 ^ m * (CU / V) ^ ((m : ℝ) / s) * V =
      5 ^ m * CU ^ ((m : ℝ) / s) * V ^ (1 - (m : ℝ) / s) := by
    rw [Real.div_rpow hCU.le hV.le, Real.rpow_sub hV, Real.rpow_one]
    field_simp
  have h2 : V ^ (1 - (m : ℝ) / s) ≤ (c * ((2 : ℝ) ^ n) ^ δr) ^ (1 - (m : ℝ) / s) :=
    Real.rpow_le_rpow_of_nonpos hLpos hL he
  have e2 : (c * ((2 : ℝ) ^ n) ^ δr) ^ (1 - (m : ℝ) / s) =
      c ^ (1 - (m : ℝ) / s) * ((2 : ℝ) ^ (δr * (1 - (m : ℝ) / s))) ^ n := by
    rw [Real.mul_rpow hc.le (by positivity), ← Real.rpow_mul (by positivity),
      ← Real.rpow_natCast (2 : ℝ) n, ← Real.rpow_mul (by norm_num),
      ← Real.rpow_natCast ((2 : ℝ) ^ (δr * (1 - (m : ℝ) / s))) n, ← Real.rpow_mul (by norm_num)]
    congr 2
    ring
  rw [e1, mul_assoc (5 ^ m * CU ^ ((m : ℝ) / s)), ← e2]
  gcongr

/-- **Lemma 3, fine part** (§3.14 (F)), uniform: the integral over `B(w, 1/40)`. -/
theorem M03b.lemma3_fine [BallGeometry X] (Cd : ℝ≥0) (R₀ : ℝ) {m : ℕ}
    (hm : Real.logb 2 ((max Cd 2 : ℝ≥0) : ℝ) < m) {δ : ℝ} (hδ : 0 < δ) :
    ∃ B : ℝ≥0∞, B ≠ ∞ ∧ ∀ μ : Measure X, MeasClassM μ Cd R₀ → ∀ w : X,
      ∫⁻ z in ball w (1 / 40),
        ENNReal.ofReal ((massRadiusM μ z / max (dist z w) (δ * massRadiusM μ w)) ^ m) ∂μ ≤ B := by
  obtain ⟨C₀, hC₀def⟩ : ∃ C₀ : ℝ≥0, C₀ = max Cd 2 := ⟨_, rfl⟩
  rw [← hC₀def] at hm
  have hC₀1 : (1 : ℝ≥0) ≤ C₀ := by rw [hC₀def]; exact le_trans (by norm_num) (le_max_right _ _)
  have hC₀2 : (2 : ℝ) ≤ C₀ := by rw [hC₀def]; exact_mod_cast le_max_right Cd 2
  have hC₀pos : (0 : ℝ) < C₀ := by linarith
  obtain ⟨s, hsdef⟩ : ∃ s : ℝ, s = Real.logb 2 (C₀ : ℝ) := ⟨_, rfl⟩
  rw [← hsdef] at hm
  have hs : 0 < s := by rw [hsdef]; exact Real.logb_pos (by norm_num) (by linarith)
  obtain ⟨CU, hCUdef⟩ : ∃ CU : ℝ, CU = (C₀ : ℝ) ^ 2 := ⟨_, rfl⟩
  have hCU : 0 < CU := by rw [hCUdef]; positivity
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = 1 / ((C₀ : ℝ) * (1 + ((C₀ : ℝ) ^ 3)⁻¹)) := ⟨_, rfl⟩
  have hc : 0 < c := by rw [hcdef]; positivity
  obtain ⟨δr, hδrdef⟩ : ∃ δr : ℝ, δr = Real.logb 2 (1 + ((C₀ : ℝ) ^ 3)⁻¹) := ⟨_, rfl⟩
  have hδr : 0 < δr := by
    rw [hδrdef]
    exact Real.logb_pos (by norm_num) (by have := inv_pos.2 (pow_pos hC₀pos 3); linarith)
  obtain ⟨e, hedef⟩ : ∃ e : ℝ, e = 1 - (m : ℝ) / s := ⟨_, rfl⟩
  have he : e < 0 := by
    rw [hedef, sub_neg, lt_div_iff₀ hs]; linarith
  obtain ⟨q, hqdef⟩ : ∃ q : ℝ, q = (2 : ℝ) ^ (δr * e) := ⟨_, rfl⟩
  have hq0 : 0 ≤ q := by rw [hqdef]; positivity
  have hq1 : q < 1 := by
    rw [hqdef]; exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (mul_neg_of_pos_of_neg hδr he)
  obtain ⟨K₁, hK₁def⟩ : ∃ K₁ : ℝ, K₁ = 5 ^ m * CU ^ ((m : ℝ) / s) * c ^ e := ⟨_, rfl⟩
  have hK₁ : 0 ≤ K₁ := by rw [hK₁def]; positivity
  have hq1' : ENNReal.ofReal q < 1 := ENNReal.ofReal_lt_one.2 hq1
  refine ⟨ENNReal.ofReal ((2 / δ) ^ m) + ENNReal.ofReal K₁ * (1 - ENNReal.ofReal q)⁻¹,
    ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.inv_ne_top.2 (tsub_pos_iff_lt.2 hq1').ne')⟩, fun μ h w ↦ ?_⟩
  have hD : M03b.DoublingUpTo μ C₀ (1 / 4) := by
    rw [hC₀def]
    exact (M03b.doublingUpTo_of_local h.doubling (by norm_num)).mono
      (max_le_max le_rfl one_le_two) le_rfl
  have hD' : M03b.DoublingUpTo μ C₀ (2 * (1 / 8)) := hD.mono le_rfl (by norm_num)
  have hρw := h.massRadiusM_pos_m03b w
  -- inner part
  have hinner : ∫⁻ z in ball w (massRadiusM μ w),
      ENNReal.ofReal ((massRadiusM μ z / max (dist z w) (δ * massRadiusM μ w)) ^ m) ∂μ ≤
      ENNReal.ofReal ((2 / δ) ^ m) := by
    have hpt : ∀ z ∈ ball w (massRadiusM μ w),
        ENNReal.ofReal ((massRadiusM μ z / max (dist z w) (δ * massRadiusM μ w)) ^ m) ≤
          ENNReal.ofReal ((2 / δ) ^ m) := by
      intro z hz
      rw [mem_ball] at hz
      have hρz := h.massRadiusM_pos_m03b z
      have hlip := h.le_add_dist_m03b w z
      rw [dist_comm] at hlip
      have hδρ : 0 < δ * massRadiusM μ w := mul_pos hδ hρw
      apply ENNReal.ofReal_le_ofReal
      apply pow_le_pow_left₀ (div_nonneg hρz.le (hδρ.le.trans (le_max_right _ _)))
      calc massRadiusM μ z / max (dist z w) (δ * massRadiusM μ w)
          ≤ massRadiusM μ z / (δ * massRadiusM μ w) :=
            div_le_div_of_nonneg_left hρz.le hδρ (le_max_right _ _)
        _ ≤ 2 / δ := by
            rw [div_le_div_iff₀ hδρ hδ]
            nlinarith
    calc ∫⁻ z in ball w (massRadiusM μ w),
          ENNReal.ofReal ((massRadiusM μ z / max (dist z w) (δ * massRadiusM μ w)) ^ m) ∂μ
        ≤ ∫⁻ _z in ball w (massRadiusM μ w), ENNReal.ofReal ((2 / δ) ^ m) ∂μ :=
          setLIntegral_mono' measurableSet_ball hpt
      _ = ENNReal.ofReal ((2 / δ) ^ m) * μ (ball w (massRadiusM μ w)) := setLIntegral_const _ _
      _ ≤ ENNReal.ofReal ((2 / δ) ^ m) * 1 := by
          gcongr; exact measure_ball_massRadiusM_le_one μ w
      _ = _ := mul_one _
  -- annuli
  set A : ℕ → Set X := fun n ↦
    (ball w (2 ^ (n + 1) * massRadiusM μ w) ∩ ball w (1 / 40)) \
      ball w (2 ^ n * massRadiusM μ w) with hA
  have hcover : ball w (1 / 40) ⊆ ball w (massRadiusM μ w) ∪ ⋃ n, A n := by
    intro z hz
    by_cases hzw : dist z w < massRadiusM μ w
    · exact Or.inl hzw
    right
    replace hzw := not_lt.1 hzw
    have hex : ∃ n : ℕ, dist z w < 2 ^ (n + 1) * massRadiusM μ w := by
      obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (dist z w / massRadiusM μ w)
        (by norm_num : (1 : ℝ) < 2)
      refine ⟨k, ?_⟩
      rw [div_lt_iff₀ hρw] at hk
      have : (2 : ℝ) ^ k ≤ 2 ^ (k + 1) := pow_le_pow_right₀ (by norm_num) (Nat.le_succ k)
      nlinarith
    classical
    have hn1 := Nat.find_spec hex
    have hn2 : 2 ^ (Nat.find hex) * massRadiusM μ w ≤ dist z w := by
      rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
      · rw [h0, pow_zero, one_mul]; exact hzw
      · have := Nat.find_min hex (Nat.sub_lt hpos one_pos)
        rw [not_lt, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hpos.ne')] at this
        exact this
    exact mem_iUnion.2 ⟨Nat.find hex, ⟨mem_ball.2 hn1, hz⟩, fun h' ↦ not_lt.2 hn2 (mem_ball.1 h')⟩
  have hAn : ∀ n : ℕ, ∫⁻ z in A n,
      ENNReal.ofReal ((massRadiusM μ z / max (dist z w) (δ * massRadiusM μ w)) ^ m) ∂μ ≤
      ENNReal.ofReal (K₁ * q ^ n) := by
    intro n
    by_cases ht : 2 ^ n * massRadiusM μ w < 1 / 40
    swap
    · have hempty : A n = ∅ := by
        ext z
        simp only [mem_empty_iff_false, iff_false]
        intro hz
        have h1 : dist z w < 1 / 40 := hz.1.2
        have h2 : ¬ dist z w < 2 ^ n * massRadiusM μ w := hz.2
        exact h2 (by linarith [not_lt.1 ht])
      rw [hempty, Measure.restrict_empty, lintegral_zero_measure]
      positivity
    set t := 2 ^ n * massRadiusM μ w with htdef
    have ht0 : 0 < t := by positivity
    have h2n : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
    have hVfin := h.finite w (5 * t)
    set V := (μ (ball w (5 * t))).toReal with hVdef
    have hVlow : c * ((2 : ℝ) ^ n) ^ δr ≤ V := by
      have key := hD'.rpow_le_measure_ball hC₀1 w w (r := 5 * t) (r' := 2 * massRadiusM μ w)
        (by positivity) (by rw [htdef]; nlinarith) (by linarith) (by rw [dist_self]; positivity)
      rw [← hcdef, ← hδrdef] at key
      have h1 : ENNReal.ofReal (c * (5 * t / (2 * massRadiusM μ w)) ^ δr) ≤ μ (ball w (5 * t)) :=
        le_trans (by
          calc ENNReal.ofReal (c * (5 * t / (2 * massRadiusM μ w)) ^ δr)
              = ENNReal.ofReal (c * (5 * t / (2 * massRadiusM μ w)) ^ δr) * 1 := (mul_one _).symm
            _ ≤ _ := by gcongr; exact h.one_le_two_m03b w) key
      have h2 := (ENNReal.ofReal_le_iff_le_toReal hVfin.ne).1 h1
      have h3 : ((2 : ℝ) ^ n) ^ δr ≤ (5 * t / (2 * massRadiusM μ w)) ^ δr := by
        apply Real.rpow_le_rpow (by positivity) _ hδr.le
        rw [htdef, le_div_iff₀ (by positivity)]
        nlinarith
      calc c * ((2 : ℝ) ^ n) ^ δr ≤ c * (5 * t / (2 * massRadiusM μ w)) ^ δr := by gcongr
        _ ≤ V := h2
    have hV0 : 0 < V := lt_of_lt_of_le (by positivity) hVlow
    have hpt : ∀ z ∈ A n,
        ENNReal.ofReal ((massRadiusM μ z / max (dist z w) (δ * massRadiusM μ w)) ^ m) ≤
          ENNReal.ofReal (5 ^ m * (CU / V) ^ ((m : ℝ) / s)) := by
      intro z hz
      have hz1 : dist z w < 2 * t := by
        have := hz.1.1; rw [mem_ball, pow_succ] at this; rw [htdef]; linarith
      have hz2 : t ≤ dist z w := not_lt.1 fun h' ↦ hz.2 (mem_ball.2 h')
      have hρz := h.massRadiusM_pos_m03b z
      have hlip := h.le_add_dist_m03b w z
      rw [dist_comm] at hlip
      have hρwt : massRadiusM μ w ≤ t := by rw [htdef]; nlinarith
      have hup := hD.measure_ball_le_rpow hC₀1 w z (r := 5 * t) (r' := massRadiusM μ z) hρz
        (by linarith) (by linarith) (by rw [dist_comm]; linarith)
      rw [← hCUdef, ← hsdef] at hup
      have hup2 : μ (ball w (5 * t)) ≤ ENNReal.ofReal (CU * (5 * t / massRadiusM μ z) ^ s) := by
        calc μ (ball w (5 * t)) ≤ ENNReal.ofReal (CU * (5 * t / massRadiusM μ z) ^ s) *
              μ (ball z (massRadiusM μ z)) := hup
          _ ≤ ENNReal.ofReal (CU * (5 * t / massRadiusM μ z) ^ s) * 1 := by
              gcongr; exact measure_ball_massRadiusM_le_one μ z
          _ = _ := mul_one _
      have hup3 : V ≤ CU * (5 * t / massRadiusM μ z) ^ s :=
        ENNReal.toReal_le_of_le_ofReal (by positivity) hup2
      exact ENNReal.ofReal_le_ofReal
        (M03b.lemma3_pt hρz ht0 (le_max_of_le_left hz2) hV0 hCU hs hup3)
    have hμA : μ (A n) ≤ ENNReal.ofReal V := by
      rw [hVdef, ENNReal.ofReal_toReal hVfin.ne]
      refine measure_mono fun z hz ↦ ?_
      have := hz.1.1
      rw [mem_ball, pow_succ] at this
      rw [mem_ball, htdef]
      nlinarith
    have hmeasA : MeasurableSet (A n) :=
      (measurableSet_ball.inter measurableSet_ball).diff measurableSet_ball
    calc ∫⁻ z in A n,
          ENNReal.ofReal ((massRadiusM μ z / max (dist z w) (δ * massRadiusM μ w)) ^ m) ∂μ
        ≤ ∫⁻ _z in A n, ENNReal.ofReal (5 ^ m * (CU / V) ^ ((m : ℝ) / s)) ∂μ :=
          setLIntegral_mono' hmeasA hpt
      _ = ENNReal.ofReal (5 ^ m * (CU / V) ^ ((m : ℝ) / s)) * μ (A n) := setLIntegral_const _ _
      _ ≤ ENNReal.ofReal (5 ^ m * (CU / V) ^ ((m : ℝ) / s)) * ENNReal.ofReal V := by gcongr
      _ = ENNReal.ofReal (5 ^ m * (CU / V) ^ ((m : ℝ) / s) * V) :=
          (ENNReal.ofReal_mul (by positivity)).symm
      _ ≤ ENNReal.ofReal (K₁ * q ^ n) := by
          apply ENNReal.ofReal_le_ofReal
          rw [hK₁def, hqdef, hedef]
          exact M03b.lemma3_sum hs hm hc hCU hVlow
  calc ∫⁻ z in ball w (1 / 40),
        ENNReal.ofReal ((massRadiusM μ z / max (dist z w) (δ * massRadiusM μ w)) ^ m) ∂μ
      ≤ ∫⁻ z in ball w (massRadiusM μ w) ∪ ⋃ n, A n,
          ENNReal.ofReal ((massRadiusM μ z / max (dist z w) (δ * massRadiusM μ w)) ^ m) ∂μ :=
        lintegral_mono_set hcover
    _ ≤ ∫⁻ z in ball w (massRadiusM μ w),
          ENNReal.ofReal ((massRadiusM μ z / max (dist z w) (δ * massRadiusM μ w)) ^ m) ∂μ +
        ∫⁻ z in ⋃ n, A n,
          ENNReal.ofReal ((massRadiusM μ z / max (dist z w) (δ * massRadiusM μ w)) ^ m) ∂μ :=
        lintegral_union_le _ _ _
    _ ≤ ENNReal.ofReal ((2 / δ) ^ m) + ∑' n, ∫⁻ z in A n,
          ENNReal.ofReal ((massRadiusM μ z / max (dist z w) (δ * massRadiusM μ w)) ^ m) ∂μ :=
        add_le_add hinner (lintegral_iUnion_le _ _)
    _ ≤ ENNReal.ofReal ((2 / δ) ^ m) + ∑' n : ℕ, ENNReal.ofReal (K₁ * q ^ n) :=
        add_le_add le_rfl (ENNReal.tsum_le_tsum hAn)
    _ = ENNReal.ofReal ((2 / δ) ^ m) + ENNReal.ofReal K₁ * (1 - ENNReal.ofReal q)⁻¹ := by
        congr 1
        rw [← ENNReal.tsum_geometric, ← ENNReal.tsum_mul_left]
        congr 1
        funext n
        rw [ENNReal.ofReal_mul hK₁, ENNReal.ofReal_pow hq0]

/-- **Lemma 3**, truncated form, uniform. -/
theorem lemma3_quant [BallGeometry X] [TopologicalSpace.SeparableSpace X] (Cd : ℝ≥0) (R₀ : ℝ) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ δ R₁ : ℝ, 0 < δ → ∃ C : ℝ≥0,
      ∀ μ : Measure X, MeasClassM μ Cd R₀ → ∀ w : X,
        ∫⁻ z in ball w R₁,
          ENNReal.ofReal ((massRadiusM μ z / max (dist z w) (δ * massRadiusM μ w)) ^ m) ∂μ ≤ C := by
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = Real.logb 2 ((max Cd 2 : ℝ≥0) : ℝ) := ⟨_, rfl⟩
  refine ⟨⌊L⌋₊ + 1, fun m hm δ R₁ hδ ↦ ?_⟩
  have hms : L < m := by
    have h1 := Nat.lt_floor_add_one L
    have h2 : ((⌊L⌋₊ + 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast hm
    push_cast at h2
    linarith
  rw [hL] at hms
  set r₀ : ℝ := 1 / 40 with hr₀
  set δ' : ℝ := r₀ / max R₀ 1 with hδ'
  have hR1 : (0 : ℝ) < max R₀ 1 := lt_max_of_lt_right one_pos
  have hδ'0 : 0 < δ' := by positivity
  obtain ⟨B₁, hB₁, hfine₁⟩ := M03b.lemma3_fine (X := X) Cd R₀ hms hδ
  obtain ⟨B₂, hB₂, hfine₂⟩ := M03b.lemma3_fine (X := X) Cd R₀ hms hδ'0
  obtain ⟨K, hK⟩ := BallGeometry.covering (X := X) R₁ r₀ (by norm_num)
  have hfin : B₁ + K * B₂ ≠ ∞ :=
    ENNReal.add_ne_top.2 ⟨hB₁, ENNReal.mul_ne_top (ENNReal.natCast_ne_top K) hB₂⟩
  refine ⟨(B₁ + K * B₂).toNNReal, fun μ h w ↦ ?_⟩
  rw [ENNReal.coe_toNNReal hfin]
  obtain ⟨s, hs, hcov⟩ := hK w
  have hρw := h.massRadiusM_pos_m03b w
  have hcover : ball w R₁ ⊆ ball w r₀ ∪ ⋃ y : s, (ball (y : X) r₀ \ ball w r₀) := by
    intro z hz
    by_cases hzw : z ∈ ball w r₀
    · exact Or.inl hzw
    right
    obtain ⟨y, hy, hzy⟩ := mem_iUnion₂.1 (hcov hz)
    exact mem_iUnion.2 ⟨⟨y, hy⟩, hzy, hzw⟩
  have hcoarse : ∀ y : s, ∫⁻ z in ball (y : X) r₀ \ ball w r₀,
      ENNReal.ofReal ((massRadiusM μ z / max (dist z w) (δ * massRadiusM μ w)) ^ m) ∂μ ≤ B₂ := by
    intro y
    have hρy := h.massRadiusM_pos_m03b (y : X)
    have hρyR := h.massRadiusM_le_m03b (y : X)
    have hpt : ∀ z ∈ ball (y : X) r₀ \ ball w r₀,
        ENNReal.ofReal ((massRadiusM μ z / max (dist z w) (δ * massRadiusM μ w)) ^ m) ≤
          ENNReal.ofReal ((massRadiusM μ z / max (dist z y) (δ' * massRadiusM μ y)) ^ m) := by
      intro z hz
      have hz1 : dist z y < r₀ := hz.1
      have hz2 : r₀ ≤ dist z w := not_lt.1 fun h' ↦ hz.2 (mem_ball.2 h')
      have hρz := h.massRadiusM_pos_m03b z
      have hδρ : 0 < δ' * massRadiusM μ y := mul_pos hδ'0 hρy
      have hmax : max (dist z y) (δ' * massRadiusM μ y) ≤ r₀ := by
        refine max_le hz1.le ?_
        have : massRadiusM μ y ≤ max R₀ 1 := hρyR.trans (le_max_left _ _)
        calc δ' * massRadiusM μ y = r₀ * (massRadiusM μ y / max R₀ 1) := by rw [hδ']; ring
          _ ≤ r₀ * 1 := mul_le_mul_of_nonneg_left (by rw [div_le_one hR1]; exact this)
              (by rw [hr₀]; norm_num)
          _ = r₀ := mul_one _
      apply ENNReal.ofReal_le_ofReal
      apply pow_le_pow_left₀ (div_nonneg hρz.le
        ((mul_pos hδ hρw).le.trans (le_max_right _ _)))
      exact div_le_div_of_nonneg_left hρz.le (hδρ.trans_le (le_max_right _ _))
        (hmax.trans (hz2.trans (le_max_left _ _)))
    calc ∫⁻ z in ball (y : X) r₀ \ ball w r₀,
          ENNReal.ofReal ((massRadiusM μ z / max (dist z w) (δ * massRadiusM μ w)) ^ m) ∂μ
        ≤ ∫⁻ z in ball (y : X) r₀ \ ball w r₀,
          ENNReal.ofReal ((massRadiusM μ z / max (dist z y) (δ' * massRadiusM μ y)) ^ m) ∂μ :=
          setLIntegral_mono' (measurableSet_ball.diff measurableSet_ball) hpt
      _ ≤ ∫⁻ z in ball (y : X) r₀,
          ENNReal.ofReal ((massRadiusM μ z / max (dist z y) (δ' * massRadiusM μ y)) ^ m) ∂μ :=
          lintegral_mono_set sdiff_subset
      _ ≤ B₂ := hfine₂ μ h y
  calc ∫⁻ z in ball w R₁,
        ENNReal.ofReal ((massRadiusM μ z / max (dist z w) (δ * massRadiusM μ w)) ^ m) ∂μ
      ≤ ∫⁻ z in ball w r₀ ∪ ⋃ y : s, (ball (y : X) r₀ \ ball w r₀),
          ENNReal.ofReal ((massRadiusM μ z / max (dist z w) (δ * massRadiusM μ w)) ^ m) ∂μ :=
        lintegral_mono_set hcover
    _ ≤ ∫⁻ z in ball w r₀,
          ENNReal.ofReal ((massRadiusM μ z / max (dist z w) (δ * massRadiusM μ w)) ^ m) ∂μ +
        ∫⁻ z in ⋃ y : s, (ball (y : X) r₀ \ ball w r₀),
          ENNReal.ofReal ((massRadiusM μ z / max (dist z w) (δ * massRadiusM μ w)) ^ m) ∂μ :=
        lintegral_union_le _ _ _
    _ ≤ B₁ + ∑' y : s, ∫⁻ z in ball (y : X) r₀ \ ball w r₀,
          ENNReal.ofReal ((massRadiusM μ z / max (dist z w) (δ * massRadiusM μ w)) ^ m) ∂μ :=
        add_le_add (hfine₁ μ h w) (lintegral_iUnion_le _ _)
    _ ≤ B₁ + ∑' _y : s, B₂ := add_le_add le_rfl (ENNReal.tsum_le_tsum hcoarse)
    _ = B₁ + s.card * B₂ := by
        rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
    _ ≤ B₁ + K * B₂ := by gcongr

/-- **[Chr91, Lemma 2.3]**, uniform form. -/
theorem christ_lemma23_quant [BallGeometry X] (Cd : ℝ≥0) (R₁ : ℝ) :
    ∃ C : ℝ≥0, ∀ μ : Measure X, IsLocDoublingMWith μ Cd → ∀ (x : X) (R : ℝ), 0 < R → R ≤ R₁ →
      ∫⁻ y in ball x R, ENNReal.ofReal (Real.log (R / dist x y)) ∂μ ≤ C * μ (ball x R) := by
  obtain ⟨C₁, hC₁, hup⟩ := M03b.exists_doublingUpTo (X := X) Cd (2 * R₁)
  have hC0 : (0 : ℝ≥0) < C₁ := zero_lt_one.trans_le hC₁
  have hη : (0 : ℝ) < (((C₁ ^ 3)⁻¹ : ℝ≥0) : ℝ) :=
    NNReal.coe_pos.2 (inv_pos.2 (pow_pos hC0 3))
  obtain ⟨q, hqdef⟩ : ∃ q : ℝ, q = (1 + (((C₁ ^ 3)⁻¹ : ℝ≥0) : ℝ))⁻¹ := ⟨_, rfl⟩
  have hq0 : 0 ≤ q := by rw [hqdef]; positivity
  have hq1 : q < 1 := by rw [hqdef]; exact inv_lt_one_of_one_lt₀ (by linarith)
  have hsum : Summable (fun k : ℕ ↦ ((k : ℝ) + 1) * q ^ k) := by
    have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 (r := q)
      (by rw [Real.norm_eq_abs, abs_of_nonneg hq0]; exact hq1)
    have h2 := summable_geometric_of_lt_one hq0 hq1
    convert h1.add h2 using 1
    funext k
    simp only [pow_one]
    ring
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  refine ⟨Real.toNNReal (Real.log 2 * ∑' k : ℕ, ((k : ℝ) + 1) * q ^ k),
    fun μ hμ x R hR hR1 ↦ ?_⟩
  have hD := hup μ hμ
  set A : ℕ → Set X := fun k ↦ ball x (R / 2 ^ k) \ ball x (R / 2 ^ (k + 1)) with hA
  have hcover : ball x R ⊆ {x} ∪ ⋃ k, A k := by
    intro y hy
    by_cases hyx : y = x
    · left; exact hyx
    right
    have hd : 0 < dist y x := dist_pos.2 hyx
    rw [mem_ball] at hy
    have hex : ∃ k : ℕ, R / 2 ^ (k + 1) ≤ dist y x := by
      obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (R / dist y x) (by norm_num : (1 : ℝ) < 2)
      refine ⟨k, ?_⟩
      rw [div_le_iff₀ (by positivity)]
      rw [div_lt_iff₀ hd] at hk
      have : (2 : ℝ) ^ k ≤ 2 ^ (k + 1) := pow_le_pow_right₀ (by norm_num) (Nat.le_succ k)
      nlinarith
    classical
    have hk1 : R / 2 ^ (Nat.find hex + 1) ≤ dist y x := Nat.find_spec hex
    have hk2 : dist y x < R / 2 ^ (Nat.find hex) := by
      rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
      · rw [h0, pow_zero, div_one]; exact hy
      · have := Nat.find_min hex (Nat.sub_lt hpos one_pos)
        rw [not_le, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hpos.ne')] at this
        exact this
    exact mem_iUnion.2 ⟨Nat.find hex, mem_ball.2 hk2, fun h ↦ not_lt.2 hk1 (mem_ball.1 h)⟩
  have hsing : ∫⁻ y in {x}, ENNReal.ofReal (Real.log (R / dist x y)) ∂μ = 0 := by
    have : ∫⁻ y in {x}, ENNReal.ofReal (Real.log (R / dist x y)) ∂μ ≤ ∫⁻ _y in {x}, 0 ∂μ :=
      setLIntegral_mono' isClosed_singleton.measurableSet fun y hy ↦ by
        rw [mem_singleton_iff] at hy
        subst hy
        simp
    simpa using this
  have hAk : ∀ k : ℕ, ∫⁻ y in A k, ENNReal.ofReal (Real.log (R / dist x y)) ∂μ ≤
      ENNReal.ofReal (Real.log 2 * (((k : ℝ) + 1) * q ^ k)) * μ (ball x R) := by
    intro k
    have hpt : ∀ y ∈ A k, ENNReal.ofReal (Real.log (R / dist x y)) ≤
        ENNReal.ofReal (((k : ℝ) + 1) * Real.log 2) := by
      intro y hy
      have h1 : R / 2 ^ (k + 1) ≤ dist x y := by
        rw [dist_comm]; exact not_lt.1 fun h ↦ hy.2 (mem_ball.2 h)
      have hpos : 0 < dist x y := lt_of_lt_of_le (by positivity) h1
      apply ENNReal.ofReal_le_ofReal
      calc Real.log (R / dist x y) ≤ Real.log (2 ^ (k + 1)) := by
            apply Real.log_le_log (by positivity)
            rw [div_le_iff₀ hpos]
            rw [div_le_iff₀ (by positivity)] at h1
            linarith
        _ = ((k : ℝ) + 1) * Real.log 2 := by rw [Real.log_pow]; push_cast; ring
    have hmeas : MeasurableSet (A k) := measurableSet_ball.diff measurableSet_ball
    have hμA : μ (A k) ≤ ENNReal.ofReal (q ^ k) * μ (ball x R) := by
      have h2k : (2 : ℝ) ^ k * (R / 2 ^ k) = R := by field_simp
      have hrev := hD.reverse_pow hC₁ x (by positivity : 0 < R / 2 ^ k) k
        (by rw [h2k]; linarith)
      rw [h2k] at hrev
      have hne0 : ((1 + (((C₁ ^ 3)⁻¹ : ℝ≥0) : ℝ≥0∞)) ^ k) ≠ 0 :=
        pow_ne_zero _ (by positivity)
      have hnet : ((1 + (((C₁ ^ 3)⁻¹ : ℝ≥0) : ℝ≥0∞)) ^ k) ≠ ∞ :=
        ENNReal.pow_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.coe_ne_top⟩)
      have e : ENNReal.ofReal (q ^ k) = ((1 + (((C₁ ^ 3)⁻¹ : ℝ≥0) : ℝ≥0∞)) ^ k)⁻¹ := by
        rw [ENNReal.ofReal_pow hq0, hqdef, ENNReal.ofReal_inv_of_pos (by positivity),
          ENNReal.ofReal_add zero_le_one (NNReal.coe_nonneg _), ENNReal.ofReal_one,
          ENNReal.ofReal_coe_nnreal, ENNReal.inv_pow]
      rw [e]
      calc μ (A k) ≤ μ (ball x (R / 2 ^ k)) := measure_mono diff_subset
        _ ≤ ((1 + (((C₁ ^ 3)⁻¹ : ℝ≥0) : ℝ≥0∞)) ^ k)⁻¹ * μ (ball x R) :=
            (ENNReal.mul_le_iff_le_inv hne0 hnet).1 hrev
    calc ∫⁻ y in A k, ENNReal.ofReal (Real.log (R / dist x y)) ∂μ
        ≤ ∫⁻ _y in A k, ENNReal.ofReal (((k : ℝ) + 1) * Real.log 2) ∂μ :=
          setLIntegral_mono' hmeas hpt
      _ = ENNReal.ofReal (((k : ℝ) + 1) * Real.log 2) * μ (A k) := setLIntegral_const _ _
      _ ≤ ENNReal.ofReal (((k : ℝ) + 1) * Real.log 2) *
            (ENNReal.ofReal (q ^ k) * μ (ball x R)) := by gcongr
      _ = ENNReal.ofReal (Real.log 2 * (((k : ℝ) + 1) * q ^ k)) * μ (ball x R) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
          congr 2
          ring
  have hnn : ∀ k : ℕ, 0 ≤ Real.log 2 * (((k : ℝ) + 1) * q ^ k) := fun k ↦
    mul_nonneg hlog2 (mul_nonneg (by positivity) (pow_nonneg hq0 k))
  calc ∫⁻ y in ball x R, ENNReal.ofReal (Real.log (R / dist x y)) ∂μ
      ≤ ∫⁻ y in {x} ∪ ⋃ k, A k, ENNReal.ofReal (Real.log (R / dist x y)) ∂μ :=
        lintegral_mono_set hcover
    _ ≤ ∫⁻ y in {x}, ENNReal.ofReal (Real.log (R / dist x y)) ∂μ +
          ∫⁻ y in ⋃ k, A k, ENNReal.ofReal (Real.log (R / dist x y)) ∂μ :=
        lintegral_union_le _ _ _
    _ ≤ 0 + ∑' k, ∫⁻ y in A k, ENNReal.ofReal (Real.log (R / dist x y)) ∂μ := by
        rw [hsing]
        exact add_le_add le_rfl (lintegral_iUnion_le _ _)
    _ ≤ 0 + ∑' k : ℕ, ENNReal.ofReal (Real.log 2 * (((k : ℝ) + 1) * q ^ k)) * μ (ball x R) :=
        add_le_add le_rfl (ENNReal.tsum_le_tsum hAk)
    _ = ENNReal.ofReal (Real.log 2 * ∑' k : ℕ, ((k : ℝ) + 1) * q ^ k) * μ (ball x R) := by
        rw [zero_add, ENNReal.tsum_mul_right,
          ← ENNReal.ofReal_tsum_of_nonneg hnn (hsum.mul_left _), tsum_mul_left]
    _ = _ := rfl

/-- Mass radius of `N⁻¹ μ` versus `μ`, uniform. -/
theorem massRadiusM_inv_smul_quant [BallGeometry X] (Cd : ℝ≥0) (R₀ : ℝ) (N : ℕ) (hN : 1 ≤ N) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ μ : Measure X, MeasClassM μ Cd R₀ → ∀ x : X,
      massRadiusM μ x ≤ massRadiusM ((N : ℝ≥0∞)⁻¹ • μ) x ∧
        massRadiusM ((N : ℝ≥0∞)⁻¹ • μ) x ≤ C * massRadiusM μ x := by
  obtain ⟨c, δ, hc, hδ, hlow⟩ := rpow_le_measure_ball_quant (X := X) Cd ((2 * N + 1) * R₀)
  refine ⟨max 4 (4 * ((N : ℝ) / c) ^ (1 / δ)), le_trans (by norm_num) (le_max_left _ _),
    fun μ h x ↦ ?_⟩
  have hR₀ := h.R₀_pos_m03b x
  have hN0 : (N : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hNt : (N : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top N
  have hsmul : ∀ s, ((N : ℝ≥0∞)⁻¹ • μ) s = (N : ℝ≥0∞)⁻¹ * μ s := fun s ↦ by
    rw [Measure.smul_apply, smul_eq_mul]
  have hRN : 0 < (2 * (N : ℝ) + 1) * R₀ := by positivity
  have hgrow : (N : ℝ≥0∞) ≤ μ (ball x ((2 * N + 1) * R₀)) := by
    refine le_trans ?_ (M03b.sum_le_measure_ball_of_le hR₀ h.mass x N)
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
    have hρ : 0 < ρ := h.massRadiusM_pos_m03b x
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
            gcongr; exact h.one_le_two_m03b x
        _ ≤ μ (ball x (ρN / 2)) := key
        _ < N := hlt
        _ = ENNReal.ofReal N := (ENNReal.ofReal_natCast N).symm
    rw [ENNReal.ofReal_lt_ofReal_iff (by positivity)] at hchain
    have hq : (ρN / 2 / (2 * ρ)) ^ δ ≤ N / c := by rw [le_div_iff₀ hc]; linarith
    have hq' := M03b.le_rpow_one_div_of_rpow_le (div_nonneg (by linarith) (by linarith)) hδ hq
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
    (h : MeasClassDisc μ Cd R₀) : MeasClassM (discPull μ) Cd R₀ := by
  refine ⟨fun a r hr h2r ↦ ?_, fun a ↦ ?_, fun a r ↦ ?_⟩
  · rw [discPull_ball, discPull_ball]; exact h.doubling _ a.2 r hr h2r
  · rw [discPull_ball]; exact (h.mass _ a.2).le
  · rw [discPull_ball]
    exact (measure_mono (M03b.hypBall_subset_closedBall_tanh a.2 r)).trans_lt
      (h.finite _ (closedBall_subset_ball (Real.tanh_lt_one _)) (isCompact_closedBall _ _))

theorem MeasClassLine.measClassM_linePull {μ : Measure ℂ} {Cd : ℝ≥0} {R₀ : ℝ}
    (h : MeasClassLine μ Cd R₀) : MeasClassM (linePull μ) Cd R₀ := by
  refine ⟨fun x r hr h2r ↦ ?_, fun x ↦ ?_, fun x r ↦ ?_⟩
  · rw [linePull_ball, linePull_ball]; exact h.doubling.2 x r hr h2r
  · rw [linePull_ball]; exact (h.mass x).le
  · rw [linePull_ball, lineInterval_eq]
    exact (measure_mono (inter_subset_left.trans ball_subset_closedBall)).trans_lt
      (h.finite _ (isCompact_closedBall _ _))

theorem MeasClassPlane.of_weight {φ : ℂ → ℝ} {μ : Measure ℂ} {Cd : ℝ≥0} {R₀ : ℝ}
    (hφ : IsSubharmonicWeight univ φ μ) (hd : IsLocallyDoublingWith μ Cd)
    (hm : ∀ z : ℂ, 1 < μ (ball z R₀)) : MeasClassPlane μ Cd R₀ :=
  ⟨hd, hm, fun K hK ↦ hφ.finite_of_compact K (subset_univ K) hK⟩

theorem MeasClassDisc.of_weight {φ : ℂ → ℝ} {μ : Measure ℂ} {Cd : ℝ≥0} {R₀ : ℝ}
    (hφ : IsSubharmonicWeight 𝔻 φ μ) (hd : IsLocallyDoublingDiscWith μ Cd)
    (hm : ∀ z ∈ 𝔻, 1 < μ (hypBall z R₀)) : MeasClassDisc μ Cd R₀ :=
  ⟨hd, hm, fun K hK hKc ↦ hφ.finite_of_compact K hK hKc⟩

/-! #### Helpers for `lapNorm` and the growth of balls (M03b) -/

theorem M03b.massRadiusM_le_of_le {X : Type*} [MetricSpace X] [MeasurableSpace X] {μ ν : Measure X}
    {x : X} (hle : ∀ r, μ (ball x r) ≤ ν (ball x r)) (hne : ∃ r, 0 < r ∧ 1 ≤ μ (ball x r)) :
    massRadiusM ν x ≤ massRadiusM μ x :=
  csInf_le_csInf ⟨0, fun _ hr ↦ hr.1.le⟩ hne fun r hr ↦ ⟨hr.1, hr.2.trans (hle r)⟩

theorem M03b.eight_le_measure_ball_of_mass {X : Type*} [MetricSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [BallGeometry X] {μ : Measure X} {R₀ : ℝ} (hR₀ : 0 < R₀)
    (h : ∀ y, 1 ≤ μ (ball y R₀)) (x : X) : 8 ≤ μ (ball x (15 * R₀)) := by
  have := M03b.sum_le_measure_ball_of_le hR₀ h x 7
  norm_num at this
  exact this

theorem M03b.lapNorm_apply (μ : Measure ℂ) (s : Set ℂ) :
    lapNorm μ s = (ENNReal.ofReal (2 * Real.pi))⁻¹ * μ s := by
  rw [lapNorm, Measure.smul_apply, smul_eq_mul]

theorem M03b.ofReal_two_pi_ne_zero : ENNReal.ofReal (2 * Real.pi) ≠ 0 :=
  (ENNReal.ofReal_pos.2 (by positivity)).ne'

theorem M03b.inv_two_pi_ne_top : (ENNReal.ofReal (2 * Real.pi))⁻¹ ≠ ∞ :=
  ENNReal.inv_ne_top.2 M03b.ofReal_two_pi_ne_zero

theorem M03b.inv_two_pi_ne_zero : (ENNReal.ofReal (2 * Real.pi))⁻¹ ≠ 0 :=
  ENNReal.inv_ne_zero.2 ENNReal.ofReal_ne_top

theorem M03b.one_lt_inv_two_pi_mul {a : ℝ≥0∞} (ha : 8 ≤ a) :
    1 < (ENNReal.ofReal (2 * Real.pi))⁻¹ * a := by
  have h8 : ENNReal.ofReal (2 * Real.pi) < 8 := by
    rw [show (8 : ℝ≥0∞) = ENNReal.ofReal 8 by norm_num]
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2 (by linarith [Real.pi_lt_four])
  calc (1 : ℝ≥0∞) = (ENNReal.ofReal (2 * Real.pi))⁻¹ * ENNReal.ofReal (2 * Real.pi) :=
        (ENNReal.inv_mul_cancel M03b.ofReal_two_pi_ne_zero ENNReal.ofReal_ne_top).symm
    _ < (ENNReal.ofReal (2 * Real.pi))⁻¹ * 8 := by
        gcongr
        · exact M03b.inv_two_pi_ne_zero
        · exact M03b.inv_two_pi_ne_top
    _ ≤ _ := by gcongr

theorem M03b.lapNorm_le_self (μ : Measure ℂ) (s : Set ℂ) : lapNorm μ s ≤ μ s := by
  rw [M03b.lapNorm_apply]
  have : (ENNReal.ofReal (2 * Real.pi))⁻¹ ≤ 1 := by
    rw [ENNReal.inv_le_one, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith [Real.pi_gt_three])
  calc _ ≤ 1 * μ s := by gcongr
    _ = μ s := one_mul _

theorem M03b.inv_seven_mul_le_lapNorm (μ : Measure ℂ) (s : Set ℂ) :
    ((7 : ℕ) : ℝ≥0∞)⁻¹ * μ s ≤ lapNorm μ s := by
  rw [M03b.lapNorm_apply]
  refine mul_le_mul_left (ENNReal.inv_le_inv.2 ?_) _
  rw [show ((7 : ℕ) : ℝ≥0∞) = ENNReal.ofReal 7 by norm_num]
  exact ENNReal.ofReal_le_ofReal (by linarith [Real.pi_lt_d2])

theorem M03b.one_le_inv_seven_mul {a : ℝ≥0∞} (ha : 8 ≤ a) : 1 ≤ ((7 : ℕ) : ℝ≥0∞)⁻¹ * a := by
  calc (1 : ℝ≥0∞) = ((7 : ℕ) : ℝ≥0∞)⁻¹ * ((7 : ℕ) : ℝ≥0∞) :=
        (ENNReal.inv_mul_cancel (by norm_num) (by simp)).symm
    _ ≤ ((7 : ℕ) : ℝ≥0∞)⁻¹ * a := by gcongr; exact le_trans (by norm_num) ha

/-! ### Quantitative lemmas (requested by M08 §4.1) -/

/-- (M03, growth + scaling) `lapNorm` stays in a class; `ρ` and `ρ̃` are comparable. -/
theorem MeasClassPlane.lapNorm {μ : Measure ℂ} {Cd : ℝ≥0} {R₀ : ℝ} (h : MeasClassPlane μ Cd R₀) :
    MeasClassPlane (lapNorm μ) Cd (15 * R₀) := by
  have hR₀ : 0 < R₀ := h.measClassM.R₀_pos_m03b 0
  refine ⟨fun z r hr h2r ↦ ?_, fun z ↦ ?_, fun K hK ↦ ?_⟩
  · rw [M03b.lapNorm_apply, M03b.lapNorm_apply]
    calc (ENNReal.ofReal (2 * Real.pi))⁻¹ * μ (ball z (2 * r))
        ≤ (ENNReal.ofReal (2 * Real.pi))⁻¹ * (Cd * μ (ball z r)) := by
          gcongr; exact h.doubling z r hr h2r
      _ = Cd * ((ENNReal.ofReal (2 * Real.pi))⁻¹ * μ (ball z r)) := by ring
  · rw [M03b.lapNorm_apply]
    exact M03b.one_lt_inv_two_pi_mul (M03b.eight_le_measure_ball_of_mass hR₀ (fun y ↦ (h.mass
        y).le) z)
  · rw [M03b.lapNorm_apply]
    exact ENNReal.mul_lt_top M03b.inv_two_pi_ne_top.lt_top (h.finite K hK)
theorem MeasClassDisc.lapNorm {μ : Measure ℂ} {Cd : ℝ≥0} {R₀ : ℝ} (h : MeasClassDisc μ Cd R₀) :
    MeasClassDisc (lapNorm μ) Cd (15 * R₀) := by
  have hR₀ : 0 < R₀ := h.measClassM_discPull.R₀_pos_m03b (HDisc.mk 0 (mem_ball_self one_pos))
  refine ⟨fun z hz r hr h2r ↦ ?_, fun z hz ↦ ?_, fun K hK𝔻 hK ↦ ?_⟩
  · rw [M03b.lapNorm_apply, M03b.lapNorm_apply]
    calc (ENNReal.ofReal (2 * Real.pi))⁻¹ * μ (hypBall z (2 * r))
        ≤ (ENNReal.ofReal (2 * Real.pi))⁻¹ * (Cd * μ (hypBall z r)) := by
          gcongr; exact h.doubling z hz r hr h2r
      _ = Cd * ((ENNReal.ofReal (2 * Real.pi))⁻¹ * μ (hypBall z r)) := by ring
  · rw [M03b.lapNorm_apply]
    have := M03b.eight_le_measure_ball_of_mass (μ := discPull μ) hR₀
      (fun y ↦ h.measClassM_discPull.mass y) (HDisc.mk z hz)
    rw [discPull_ball, M03b.hdisc_val_mk] at this
    exact M03b.one_lt_inv_two_pi_mul this
  · rw [M03b.lapNorm_apply]
    exact ENNReal.mul_lt_top M03b.inv_two_pi_ne_top.lt_top (h.finite K hK𝔻 hK)
theorem massRadius_lapNorm_quant (Cd : ℝ≥0) (R₀ : ℝ) : ∃ C : ℝ, 1 ≤ C ∧
    ∀ μ : Measure ℂ, MeasClassPlane μ Cd R₀ → ∀ z,
      massRadius μ z ≤ massRadius (lapNorm μ) z ∧ massRadius (lapNorm μ) z ≤ C * massRadius μ z :=
  by
  obtain ⟨C, hC, hall⟩ := massRadiusM_inv_smul_quant (X := ℂ) Cd R₀ 7 (by norm_num)
  refine ⟨C, hC, fun μ h z ↦ ?_⟩
  simp only [massRadius_eq]
  have hM := h.measClassM
  have hR₀ : 0 < R₀ := hM.R₀_pos_m03b z
  have hL := h.lapNorm
  have h7 := hall μ hM z
  refine ⟨?_, ?_⟩
  · exact M03b.massRadiusM_le_of_le (fun r ↦ M03b.lapNorm_le_self μ _)
      ⟨15 * R₀, by positivity, (hL.mass z).le⟩
  · refine le_trans (M03b.massRadiusM_le_of_le (fun r ↦ by
      rw [Measure.smul_apply, smul_eq_mul]; exact M03b.inv_seven_mul_le_lapNorm μ _) ?_) h7.2
    refine ⟨15 * R₀, by positivity, ?_⟩
    rw [Measure.smul_apply, smul_eq_mul]
    exact M03b.one_le_inv_seven_mul (M03b.eight_le_measure_ball_of_mass hR₀ (fun y ↦ hM.mass y) z)
theorem massRadiusDisc_lapNorm_quant (Cd : ℝ≥0) (R₀ : ℝ) : ∃ C : ℝ, 1 ≤ C ∧
    ∀ μ : Measure ℂ, MeasClassDisc μ Cd R₀ → ∀ z ∈ 𝔻,
      massRadiusDisc μ z ≤ massRadiusDisc (lapNorm μ) z ∧
        massRadiusDisc (lapNorm μ) z ≤ C * massRadiusDisc μ z := by
  obtain ⟨C, hC, hall⟩ := massRadiusM_inv_smul_quant (X := HDisc) Cd R₀ 7 (by norm_num)
  refine ⟨C, hC, fun μ h z hz ↦ ?_⟩
  have hM := h.measClassM_discPull
  have hR₀ : 0 < R₀ := hM.R₀_pos_m03b (HDisc.mk z hz)
  have hLM := h.lapNorm.measClassM_discPull
  have h7 := hall (discPull μ) hM (HDisc.mk z hz)
  rw [M03b.massRadiusDisc_eq' hz, M03b.massRadiusDisc_eq' hz]
  refine ⟨?_, ?_⟩
  · refine M03b.massRadiusM_le_of_le (fun r ↦ ?_) ⟨15 * R₀, by positivity, hLM.mass _⟩
    rw [discPull_ball, discPull_ball]
    exact M03b.lapNorm_le_self μ _
  · refine le_trans (M03b.massRadiusM_le_of_le (fun r ↦ ?_) ?_) h7.2
    · rw [Measure.smul_apply, smul_eq_mul, discPull_ball, discPull_ball]
      exact M03b.inv_seven_mul_le_lapNorm μ _
    · refine ⟨15 * R₀, by positivity, ?_⟩
      rw [Measure.smul_apply, smul_eq_mul]
      exact M03b.one_le_inv_seven_mul (M03b.eight_le_measure_ball_of_mass hR₀ (fun y ↦ hM.mass y) _)

/-- (M03, quantitative Claim 1 + positivity/upper bound of `ρ`). -/
theorem claim1_plane_quant (Cd : ℝ≥0) (R₀ K : ℝ) : ∃ C : ℝ, 1 ≤ C ∧
    ∀ ν : Measure ℂ, MeasClassPlane ν Cd R₀ → ∀ z w : ℂ,
      0 < massRadius ν z ∧ massRadius ν z ≤ R₀ ∧
      (dist z w ≤ K * max (massRadius ν z) (massRadius ν w) →
        massRadius ν z ≤ C * massRadius ν w) := by
  obtain ⟨C, hC, hall⟩ := claim1_quant (X := ℂ) Cd R₀ K
  exact ⟨C, hC, fun ν h z w ↦ hall ν h.measClassM z w⟩
theorem claim1_disc_quant (Cd : ℝ≥0) (R₀ K : ℝ) : ∃ C : ℝ, 1 ≤ C ∧
    ∀ ν : Measure ℂ, MeasClassDisc ν Cd R₀ → ∀ z ∈ 𝔻, ∀ w ∈ 𝔻,
      0 < massRadiusDisc ν z ∧ massRadiusDisc ν z ≤ R₀ ∧
      (hypDist z w ≤ K * max (massRadiusDisc ν z) (massRadiusDisc ν w) →
        massRadiusDisc ν z ≤ C * massRadiusDisc ν w) := by
  obtain ⟨C, hC, hall⟩ := claim1_quant (X := HDisc) Cd R₀ K
  refine ⟨C, hC, fun ν h z hz w hw ↦ ?_⟩
  have := hall (discPull ν) h.measClassM_discPull (HDisc.mk z hz) (HDisc.mk w hw)
  rw [M03b.massRadiusDisc_eq' hz, M03b.massRadiusDisc_eq' hw]
  exact this

/-- (M03, quantitative) mass of comparable balls. -/
theorem measure_ball_massRadius_quant (Cd : ℝ≥0) (R₀ K : ℝ) : ∃ C : ℝ≥0,
    ∀ ν : Measure ℂ, MeasClassPlane ν Cd R₀ → ∀ z, ν (ball z (K * massRadius ν z)) ≤ C := by
  obtain ⟨C, hall⟩ := measure_ball_massRadiusM_quant (X := ℂ) Cd R₀ K
  exact ⟨C, fun ν h z ↦ hall ν h.measClassM z⟩
theorem measure_hypBall_massRadius_quant (Cd : ℝ≥0) (R₀ K : ℝ) : ∃ C : ℝ≥0,
    ∀ ν : Measure ℂ, MeasClassDisc ν Cd R₀ → ∀ z ∈ 𝔻,
      ν (hypBall z (K * massRadiusDisc ν z)) ≤ C := by
  obtain ⟨C, hall⟩ := measure_ball_massRadiusM_quant (X := HDisc) Cd R₀ K
  refine ⟨C, fun ν h z hz ↦ ?_⟩
  have := hall (discPull ν) h.measClassM_discPull (HDisc.mk z hz)
  rw [discPull_ball, M03b.hdisc_val_mk, ← M03b.massRadiusDisc_eq' hz] at this
  exact this

/-- (M03, quantitative decay; `massRadiusM_div_dist_le` with `M₀ = 1/4`). -/
theorem decay_plane_quant (Cd : ℝ≥0) (R₀ : ℝ) : ∃ C α : ℝ, 0 < C ∧ 0 < α ∧
    ∀ ν : Measure ℂ, MeasClassPlane ν Cd R₀ → ∀ z ζ : ℂ,
      massRadius ν z ≤ dist z ζ → dist z ζ ≤ 1 / 4 →
        massRadius ν ζ / dist z ζ ≤ C * (massRadius ν z / dist z ζ) ^ α := by
  obtain ⟨C, α, hC, hα, -, hall⟩ := massRadiusM_div_dist_le_quant (X := ℂ) Cd R₀ (1 / 4)
  exact ⟨C, α, hC, hα, fun ν h z ζ h1 h2 ↦ hall ν h.measClassM z ζ h1 h2⟩
theorem decay_disc_quant (Cd : ℝ≥0) (R₀ : ℝ) : ∃ C α : ℝ, 0 < C ∧ 0 < α ∧
    ∀ ν : Measure ℂ, MeasClassDisc ν Cd R₀ → ∀ z ∈ 𝔻, ∀ ζ ∈ 𝔻,
      massRadiusDisc ν z ≤ hypDist z ζ → hypDist z ζ ≤ 1 / 4 →
        massRadiusDisc ν ζ / hypDist z ζ ≤ C * (massRadiusDisc ν z / hypDist z ζ) ^ α := by
  obtain ⟨C, α, hC, hα, -, hall⟩ := massRadiusM_div_dist_le_quant (X := HDisc) Cd R₀ (1 / 4)
  refine ⟨C, α, hC, hα, fun ν h z hz ζ hζ h1 h2 ↦ ?_⟩
  rw [M03b.massRadiusDisc_eq' hz] at h1 ⊢
  rw [M03b.massRadiusDisc_eq' hζ]
  exact hall (discPull ν) h.measClassM_discPull (HDisc.mk z hz) (HDisc.mk ζ hζ) h1 h2

/-- (M03, quantitative [Chr91, Lemma 2.3]). -/
theorem christ_plane_quant (Cd : ℝ≥0) (R₀ S : ℝ) : ∃ C : ℝ≥0,
    ∀ ν : Measure ℂ, MeasClassPlane ν Cd R₀ → ∀ z : ℂ, ∀ s : ℝ, 0 < s → s ≤ S →
      ∫⁻ ζ in ball z s, ENNReal.ofReal (Real.log (s / dist z ζ)) ∂ν ≤ C * ν (ball z s) := by
  obtain ⟨C, hall⟩ := christ_lemma23_quant (X := ℂ) Cd S
  exact ⟨C, fun ν h z s hs hsS ↦ hall ν h.doubling z s hs hsS⟩
theorem christ_disc_quant (Cd : ℝ≥0) (R₀ S : ℝ) : ∃ C : ℝ≥0,
    ∀ ν : Measure ℂ, MeasClassDisc ν Cd R₀ → ∀ z ∈ 𝔻, ∀ s : ℝ, 0 < s → s ≤ S →
      ∫⁻ ζ in hypBall z s, ENNReal.ofReal (Real.log (s / hypDist z ζ)) ∂ν ≤
        C * ν (hypBall z s) := by
  obtain ⟨C, hall⟩ := christ_lemma23_quant (X := HDisc) Cd S
  refine ⟨C, fun ν h z hz s hs hsS ↦ ?_⟩
  have key := hall (discPull ν) h.measClassM_discPull.doubling (HDisc.mk z hz) s hs hsS
  rw [discPull_ball, M03b.hdisc_val_mk] at key
  rw [M03b.hypBall_eq_image_ball hz, ← M03b.lintegral_discPull, ← M03b.hypBall_eq_image_ball hz]
  convert key using 3 with b
  rw [HDisc.dist_eq, M03b.hdisc_val_mk]


/-! ### Line forms (uniform) -/

theorem claim1_line_quant (Cd : ℝ≥0) (R₀ K : ℝ) : ∃ C : ℝ, 1 ≤ C ∧
    ∀ ν : Measure ℂ, MeasClassLine ν Cd R₀ → ∀ x y : ℝ,
      0 < massRadiusLine ν x ∧ massRadiusLine ν x ≤ R₀ ∧
      (|x - y| ≤ K * max (massRadiusLine ν x) (massRadiusLine ν y) →
        massRadiusLine ν x ≤ C * massRadiusLine ν y) := by
  obtain ⟨C, hC, hall⟩ := claim1_quant (X := ℝ) Cd R₀ K
  refine ⟨C, hC, fun ν h x y ↦ ?_⟩
  have := hall (linePull ν) h.measClassM_linePull x y
  rw [massRadiusLine_eq, massRadiusLine_eq]
  rw [Real.dist_eq] at this
  exact this

theorem decay_line_quant (Cd : ℝ≥0) (R₀ : ℝ) : ∃ C α : ℝ, 0 < C ∧ 0 < α ∧
    ∀ ν : Measure ℂ, MeasClassLine ν Cd R₀ → ∀ x y : ℝ,
      massRadiusLine ν x ≤ |x - y| → |x - y| ≤ 1 / 4 →
        massRadiusLine ν y / |x - y| ≤ C * (massRadiusLine ν x / |x - y|) ^ α := by
  obtain ⟨C, α, hC, hα, -, hall⟩ := massRadiusM_div_dist_le_quant (X := ℝ) Cd R₀ (1 / 4)
  refine ⟨C, α, hC, hα, fun ν h x y h1 h2 ↦ ?_⟩
  rw [massRadiusLine_eq] at h1 ⊢
  rw [massRadiusLine_eq]
  have := hall (linePull ν) h.measClassM_linePull x y
  rw [Real.dist_eq] at this
  exact this h1 h2

theorem christ_line_quant (Cd : ℝ≥0) (R₀ S : ℝ) : ∃ C : ℝ≥0,
    ∀ ν : Measure ℂ, MeasClassLine ν Cd R₀ → ∀ x : ℝ, ∀ s : ℝ, 0 < s → s ≤ S →
      ∫⁻ z in lineInterval x s, ENNReal.ofReal (Real.log (s / |z.re - x|)) ∂ν ≤
        C * ν (lineInterval x s) := by
  obtain ⟨C, hall⟩ := christ_lemma23_quant (X := ℝ) Cd S
  refine ⟨C, fun ν h x s hs hsS ↦ ?_⟩
  have key := hall (linePull ν) h.measClassM_linePull.doubling x s hs hsS
  rw [linePull_ball] at key
  rw [M03b.lineInterval_eq_image_ball, ← M03b.lintegral_linePull, ← M03b.lineInterval_eq_image_ball]
  convert key using 3 with t
  rw [Complex.ofReal_re, Real.dist_eq, abs_sub_comm]

end OC
