import OrtegaCerdaMultipliers.Line.Partition

/-!
# M13 (Theorem5) — The correction potential `S = Σ_k T_k`

See `blueprint/M13_Theorem5.md` §3.5–§3.6.

* Integrability of `log |z − t|` on cells and the line form of (L8) are proved for any
  `IsLineMeasure`, and applied both to `μ` and to `lebLine` (Lebesgue measure), so that the two
  parts of the signed measure `μ − 2α dt` are handled by the same lemmas.
* Near field: `LineHyp.lineTerm_eq_R` writes `T_k` with the scale `R = 3a_k`; the bounds follow
  from (L8) and four doublings (`LineHyp.near_mass`).
* Far field: moment cancellation and `|log|1 − w| + Re w| ≤ |w|²`.
* Far sum: each far cell is bounded by the integral over the cell of an explicit majorant
  (`m13_majorant_aux`, using (L5), (L6), (L7)), whose integral over `ℝ` does not depend on `z`.
* Near count: disjoint cells of length `≳ ρ(x)` inside an interval of length `≲ ρ(x)`.
-/

open MeasureTheory Metric Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace OC

/-- `T_k(z) = (1/2π) ∫_{I_k} (½ log|z−ν₊| + ½ log|z−ν₋| − log|z−t|) dσ_α(t)`, using `σ_α(I_k) = 4π`. -/
def lineTerm (μ : Measure ℂ) (α s : ℝ) (k : ℤ) (z : ℂ) : ℝ :=
  Real.log ‖z - lineNode μ α s k true‖ + Real.log ‖z - lineNode μ α s k false‖ -
    (1 / (2 * Real.pi)) *
      ((∫ t in Ioc (lineKnot μ α k) (lineKnot μ α (k + 1)), Real.log ‖z - t‖ ∂linePull μ) -
        2 * α * ∫ t in lineKnot μ α k..lineKnot μ α (k + 1), Real.log ‖z - t‖)

/-- The correction potential `S = Σ_k T_k`. -/
def linePotential (μ : Measure ℂ) (α s : ℝ) (z : ℂ) : ℝ :=
  ∑' k : ℤ, lineTerm μ α s k z

/-- The nodes of sign `b`, as a subset of `ℂ`. -/
def lineNodeSet (μ : Measure ℂ) (α s : ℝ) (b : Bool) : Set ℂ :=
  range fun k : ℤ ↦ ((lineNode μ α s k b : ℝ) : ℂ)

/-- Zero set of the multiplier with offset `s`. -/
def lineZeroSet (μ : Measure ℂ) (α s : ℝ) : Set ℂ :=
  lineNodeSet μ α s true ∪ lineNodeSet μ α s false

/-- Its counting function: `2` at `λ_k` when `s = 0`, `1` at `λ_k ± s a_k` when `0 < s ≤ s₀`. -/
def lineZeroCount (μ : Measure ℂ) (α s : ℝ) (z : ℂ) : ℕ :=
  (lineNodeSet μ α s true).indicator 1 z + (lineNodeSet μ α s false).indicator 1 z


/-! ### Generic lemmas on the logarithmic kernel against a line measure -/

theorem m13_norm_sub_ofReal_ge (z : ℂ) (t : ℝ) : |t - z.re| ≤ ‖z - t‖ := by
  have := Complex.abs_re_le_norm (z - t)
  rw [sub_re, ofReal_re, abs_sub_comm] at this
  exact this

theorem m13_norm_ofReal_sub_ofReal (t x : ℝ) : ‖(t : ℂ) - (x : ℂ)‖ = |t - x| := by
  rw [← ofReal_sub, norm_real, Real.norm_eq_abs]

theorem IsLineMeasure.m13_linePull_singleton {μ : Measure ℂ} (hμ : IsLineMeasure μ) (x : ℝ) :
    linePull μ {x} = 0 := by
  rw [linePull_apply, image_singleton, hμ.measure_singleton]

theorem IsLineMeasure.m13_ae_ne {μ : Measure ℂ} (hμ : IsLineMeasure μ) (x : ℝ) :
    ∀ᵐ t ∂linePull μ, t ≠ x := by
  rw [ae_iff]
  simpa using hμ.m13_linePull_singleton x

/-- (L8) on the line, in terms of `linePull μ`. -/
theorem IsLineMeasure.m13_lintegral_log_line {μ : Measure ℂ} (hμ : IsLineMeasure μ) {A : ℝ}
    (hA : 0 < A) : ∃ C : ℝ≥0, ∀ x R : ℝ, 0 < R → R ≤ A →
      ∫⁻ t in Ioo (x - R) (x + R), ENNReal.ofReal (Real.log (R / |t - x|)) ∂linePull μ ≤
        C * μ (lineInterval x R) := by
  obtain ⟨C, hC⟩ := hμ.lintegral_log_le hA
  refine ⟨C, fun x R hR hRA ↦ ?_⟩
  have h1 := hC x R hR hRA
  have e : ∫⁻ ζ in lineInterval x R, ENNReal.ofReal (Real.log (R / ‖ζ - (x : ℂ)‖)) ∂μ =
      ∫⁻ t in Ioo (x - R) (x + R), ENNReal.ofReal (Real.log (R / |t - x|)) ∂linePull μ := by
    rw [lineInterval, hμ.m13_setLIntegral_image]
    simp_rw [m13_norm_ofReal_sub_ofReal]
  rw [e] at h1
  exact h1

theorem m13_measurable_log_norm_sub (z : ℂ) : Measurable fun t : ℝ ↦ Real.log ‖z - t‖ :=
  Real.measurable_log.comp (continuous_const.sub continuous_ofReal).norm.measurable

/-- `log |z − t|` is integrable on bounded intervals against a line measure. -/
theorem IsLineMeasure.m13_integrableOn_log {μ : Measure ℂ} (hμ : IsLineMeasure μ) (z : ℂ)
    (a b : ℝ) : IntegrableOn (fun t : ℝ ↦ Real.log ‖z - t‖) (Ioc a b) (linePull μ) := by
  obtain ⟨C, hC⟩ := hμ.m13_lintegral_log_line one_pos
  set x := z.re
  set B := Real.log (1 + ‖z‖ + |a| + |b|)
  refine ⟨(m13_measurable_log_norm_sub z).aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral]
  have hpt : ∀ᵐ t ∂linePull μ, t ∈ Ioc a b → ‖Real.log ‖z - t‖‖ₑ ≤
      (Ioo (x - 1) (x + 1)).indicator (fun t ↦ ENNReal.ofReal (Real.log (1 / |t - x|))) t +
        ENNReal.ofReal B := by
    filter_upwards [hμ.m13_ae_ne x] with t htx ht
    rw [Real.enorm_eq_ofReal_abs]
    set y := ‖z - t‖
    have hy0 : 0 ≤ y := norm_nonneg _
    have hxt : |t - x| ≤ y := m13_norm_sub_ofReal_ge z t
    have hxt0 : 0 < |t - x| := abs_pos.2 (sub_ne_zero.2 htx)
    rcases le_or_gt 1 y with hy1 | hy1
    · -- `|log y| = log y ≤ B`
      have hyB : y ≤ 1 + ‖z‖ + |a| + |b| := by
        have h1 : y ≤ ‖z‖ + ‖(t : ℂ)‖ := norm_sub_le _ _
        rw [norm_real, Real.norm_eq_abs] at h1
        have : |t| ≤ |a| + |b| := by
          rcases le_total 0 t with h | h
          · rw [abs_of_nonneg h]; linarith [ht.2, le_abs_self b, abs_nonneg a]
          · rw [abs_of_nonpos h]; linarith [ht.1, neg_abs_le a, abs_nonneg b]
        linarith
      have : |Real.log y| ≤ B := by
        rw [abs_of_nonneg (Real.log_nonneg hy1)]
        exact Real.log_le_log (by linarith) hyB
      exact le_trans (ENNReal.ofReal_le_ofReal this) le_add_self
    · -- `|log y| = log (1/y) ≤ log (1/|t-x|)`
      have hy0' : 0 < y := lt_of_lt_of_le hxt0 hxt
      have hmem : t ∈ Ioo (x - 1) (x + 1) := by
        have := abs_lt.1 (lt_of_le_of_lt hxt hy1)
        constructor <;> linarith [this.1, this.2]
      rw [indicator_of_mem hmem]
      refine le_trans (ENNReal.ofReal_le_ofReal ?_) le_self_add
      rw [abs_of_nonpos (Real.log_nonpos hy0 hy1.le), ← Real.log_inv, ← one_div]
      exact Real.log_le_log (by positivity) (one_div_le_one_div_of_le hxt0 hxt)
  calc ∫⁻ t in Ioc a b, ‖Real.log ‖z - t‖‖ₑ ∂linePull μ
      ≤ ∫⁻ t in Ioc a b, ((Ioo (x - 1) (x + 1)).indicator
          (fun t ↦ ENNReal.ofReal (Real.log (1 / |t - x|))) t + ENNReal.ofReal B) ∂linePull μ :=
        setLIntegral_mono_ae' measurableSet_Ioc hpt
    _ = ∫⁻ t in Ioc a b, (Ioo (x - 1) (x + 1)).indicator
          (fun t ↦ ENNReal.ofReal (Real.log (1 / |t - x|))) t ∂linePull μ +
          ENNReal.ofReal B * linePull μ (Ioc a b) := by
        rw [lintegral_add_right _ measurable_const, setLIntegral_const]
    _ ≤ ∫⁻ t in Ioo (x - 1) (x + 1), ENNReal.ofReal (Real.log (1 / |t - x|)) ∂linePull μ +
          ENNReal.ofReal B * linePull μ (Ioc a b) := by
        have := setLIntegral_le_lintegral (μ := linePull μ) (Ioc a b)
          ((Ioo (x - 1) (x + 1)).indicator (fun t ↦ ENNReal.ofReal (Real.log (1 / |t - x|))))
        exact add_le_add_left (this.trans (lintegral_indicator measurableSet_Ioo _).le) _
    _ ≤ C * μ (lineInterval x 1) + ENNReal.ofReal B * linePull μ (Ioc a b) := by
        gcongr; exact hC x 1 one_pos le_rfl
    _ < ∞ := ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.coe_lt_top
          (hμ.lineInterval_lt_top x 1), ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          (hμ.linePull_Ioc_lt_top a b)⟩

theorem m13_integrableOn_log_volume (z : ℂ) (a b : ℝ) :
    IntegrableOn (fun t : ℝ ↦ Real.log ‖z - t‖) (Ioc a b) volume := by
  have := isLineMeasure_lebLine.m13_integrableOn_log z a b
  rwa [linePull_lebLine] at this

/-- Two-sided bounds for `∫ (log R − log |z − t|)` over a piece of a line measure. -/
theorem IsLineMeasure.m13_setIntegral_logR_bounds {ν : Measure ℂ} (hν : IsLineMeasure ν) {A : ℝ}
    {C : ℝ≥0} (hC : ∀ x R : ℝ, 0 < R → R ≤ A →
      ∫⁻ t in Ioo (x - R) (x + R), ENNReal.ofReal (Real.log (R / |t - x|)) ∂linePull ν ≤
        C * ν (lineInterval x R))
    {z : ℂ} {a b R : ℝ} (hR : 0 < R) (hRA : R ≤ A) (hsub : ∀ t ∈ Ioc a b, ‖z - t‖ < R) :
    0 ≤ ∫ t in Ioc a b, (Real.log R - Real.log ‖z - t‖) ∂linePull ν ∧
      ∫ t in Ioc a b, (Real.log R - Real.log ‖z - t‖) ∂linePull ν ≤
        C * (ν (lineInterval z.re R)).toReal := by
  set x := z.re
  have hpos : ∀ᵐ t ∂linePull ν, t ∈ Ioc a b → 0 ≤ Real.log R - Real.log ‖z - t‖ := by
    filter_upwards [hν.m13_ae_ne x] with t htx ht
    have hxt : |t - x| ≤ ‖z - t‖ := m13_norm_sub_ofReal_ge z t
    have hxt0 : 0 < |t - x| := abs_pos.2 (sub_ne_zero.2 htx)
    have := Real.log_le_log (lt_of_lt_of_le hxt0 hxt) (hsub t ht).le
    linarith
  refine ⟨setIntegral_nonneg_ae measurableSet_Ioc hpos, ?_⟩
  have hint : IntegrableOn (fun t : ℝ ↦ Real.log R - Real.log ‖z - t‖) (Ioc a b) (linePull ν) :=
    (integrableOn_const (hν.linePull_Ioc_lt_top a b).ne).sub (hν.m13_integrableOn_log z a b)
  rw [integral_eq_lintegral_of_nonneg_ae ((ae_restrict_iff' measurableSet_Ioc).2 hpos)
    hint.aestronglyMeasurable]
  have hfin : C * ν (lineInterval x R) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top (hν.lineInterval_lt_top x R).ne
  rw [← ENNReal.coe_toReal C, ← ENNReal.toReal_mul]
  refine ENNReal.toReal_mono hfin ?_
  calc ∫⁻ t in Ioc a b, ENNReal.ofReal (Real.log R - Real.log ‖z - t‖) ∂linePull ν
      ≤ ∫⁻ t in Ioc a b, ENNReal.ofReal (Real.log (R / |t - x|)) ∂linePull ν := by
        refine setLIntegral_mono_ae' measurableSet_Ioc ?_
        filter_upwards [hν.m13_ae_ne x] with t htx ht
        have hxt : |t - x| ≤ ‖z - t‖ := m13_norm_sub_ofReal_ge z t
        have hxt0 : 0 < |t - x| := abs_pos.2 (sub_ne_zero.2 htx)
        apply ENNReal.ofReal_le_ofReal
        rw [Real.log_div hR.ne' hxt0.ne']
        have := Real.log_le_log hxt0 hxt
        linarith
    _ ≤ ∫⁻ t in Ioo (x - R) (x + R), ENNReal.ofReal (Real.log (R / |t - x|)) ∂linePull ν := by
        refine lintegral_mono_set (fun t ht ↦ ?_)
        have := abs_lt.1 (lt_of_le_of_lt (m13_norm_sub_ofReal_ge z t) (hsub t ht))
        constructor <;> linarith [this.1, this.2]
    _ ≤ C * ν (lineInterval x R) := hC x R hR hRA

/-! ### One term: the `R`-normalised form -/

namespace LineHyp

variable {μ : Measure ℂ} {r α : ℝ} (hl : LineHyp μ r α)
include hl

theorem lineKnot_le (k : ℤ) : lineKnot μ α k ≤ lineKnot μ α (k + 1) :=
  (hl.lineKnot_strictMono (lt_add_one k)).le

/-- `T_k = log(|z−ν₊|/R) + log(|z−ν₋|/R) + (1/2π) ∫_{I_k} log(R/|z−t|) dσ_α(t)`, written without
divisions (so that it holds at the nodes too). -/
theorem lineTerm_eq_R (s : ℝ) (k : ℤ) (z : ℂ) (R : ℝ) :
    lineTerm μ α s k z = (Real.log ‖z - lineNode μ α s k true‖ - Real.log R) +
      (Real.log ‖z - lineNode μ α s k false‖ - Real.log R) +
      (1 / (2 * Real.pi)) *
        ((∫ t in Ioc (lineKnot μ α k) (lineKnot μ α (k + 1)),
            (Real.log R - Real.log ‖z - t‖) ∂linePull μ) -
          2 * α * ∫ t in Ioc (lineKnot μ α k) (lineKnot μ α (k + 1)),
            (Real.log R - Real.log ‖z - t‖)) := by
  unfold lineTerm
  have hab := hl.lineKnot_le k
  rw [intervalIntegral.integral_of_le hab,
    integral_sub (integrableOn_const (hl.hμ.linePull_Ioc_lt_top _ _).ne)
      (hl.hμ.m13_integrableOn_log z _ _),
    integral_sub (integrableOn_const measure_Ioc_lt_top.ne) (m13_integrableOn_log_volume z _ _),
    setIntegral_const, setIntegral_const, measureReal_def, measureReal_def,
    hl.toReal_linePull_Ioc_lineKnot, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)]
  have hπ := Real.pi_pos
  unfold lineLength
  field_simp
  ring

/-- Geometry of a near cell. -/
theorem near_geom {c₀ : ℝ} (hc₀ : 0 ≤ c₀) (hcen : ∀ k : ℤ,
      lineKnot μ α k + c₀ * lineLength μ α k ≤ lineCentre μ α k ∧
      lineCentre μ α k ≤ lineKnot μ α (k + 1) - c₀ * lineLength μ α k)
    {s : ℝ} (hs : 0 ≤ s) (hs' : s ≤ 1 / 2) {k : ℤ} {z : ℂ}
    (hz : ‖z - lineCentre μ α k‖ < 2 * lineLength μ α k) :
    (∀ t ∈ Ioc (lineKnot μ α k) (lineKnot μ α (k + 1)), ‖z - t‖ < 3 * lineLength μ α k) ∧
    (∀ b : Bool, ‖z - lineNode μ α s k b‖ < 3 * lineLength μ α k) ∧
    |z.re - (lineKnot μ α k + lineKnot μ α (k + 1)) / 2| ≤ 5 * lineLength μ α k := by
  have hp := hl.lineLength_pos k
  obtain ⟨h1, h2⟩ := hcen k
  have hc0 : 0 ≤ c₀ * lineLength μ α k := by positivity
  unfold lineLength at *
  refine ⟨fun t ht ↦ ?_, fun b ↦ ?_, ?_⟩
  · calc ‖z - t‖ ≤ ‖z - lineCentre μ α k‖ + ‖((lineCentre μ α k : ℝ) : ℂ) - t‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < 2 * (lineKnot μ α (k + 1) - lineKnot μ α k) +
          (lineKnot μ α (k + 1) - lineKnot μ α k) := by
          rw [m13_norm_ofReal_sub_ofReal]
          refine add_lt_add_of_lt_of_le hz ?_
          rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
      _ = _ := by ring
  · obtain ⟨o, ho, he⟩ := lineNode_eq μ α s k b
    calc ‖z - lineNode μ α s k b‖ ≤ ‖z - lineCentre μ α k‖ +
          ‖((lineCentre μ α k : ℝ) : ℂ) - lineNode μ α s k b‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < 2 * (lineKnot μ α (k + 1) - lineKnot μ α k) +
          (lineKnot μ α (k + 1) - lineKnot μ α k) := by
          rw [m13_norm_ofReal_sub_ofReal, he, lineLength]
          refine add_lt_add_of_lt_of_le hz ?_
          rw [show lineCentre μ α k - (lineCentre μ α k + o * (lineKnot μ α (k + 1) -
            lineKnot μ α k)) = -(o * (lineKnot μ α (k + 1) - lineKnot μ α k)) by ring, abs_neg,
            abs_mul, abs_of_pos hp]
          have : |o| ≤ 1 := by rcases ho with rfl | rfl <;> simp [abs_of_nonneg hs] <;> linarith
          nlinarith [abs_nonneg o]
      _ = _ := by ring
  · have := m13_norm_sub_ofReal_ge z (lineCentre μ α k)
    rw [abs_sub_comm] at this
    rw [abs_le] at this ⊢
    constructor <;> nlinarith [this.1, this.2]

/-- The mass of `I(x, 3a_k)` for `x` near the cell is bounded (four doublings). -/
theorem near_mass {C : ℝ≥0}
    (hC : ∀ x ρ : ℝ, 0 < ρ → ρ ≤ 208 * r → μ (lineInterval x (2 * ρ)) ≤ C * μ (lineInterval x ρ))
    (k : ℤ) {x : ℝ} (hx : |x - (lineKnot μ α k + lineKnot μ α (k + 1)) / 2| ≤ 5 * lineLength μ α k) :
    μ (lineInterval x (3 * lineLength μ α k)) ≤ C ^ 4 * ENNReal.ofReal (4 * Real.pi + 13) := by
  set ℓ := lineLength μ α k
  have hp : 0 < ℓ := hl.lineLength_pos k
  have hle : ℓ ≤ 52 * r := hl.lineLength_le k
  set m := (lineKnot μ α k + lineKnot μ α (k + 1)) / 2
  have hsub : lineInterval x (3 * ℓ) ⊆ lineInterval m (2 * (2 * (2 * (2 * (ℓ / 2))))) := by
    apply image_mono
    have := abs_le.1 hx
    intro t ht
    constructor <;> linarith [ht.1, ht.2, this.1, this.2]
  have hbase : μ (lineInterval m (ℓ / 2)) ≤ ENNReal.ofReal (4 * Real.pi + 13) := by
    rw [← m13_linePull_Ioo]
    calc linePull μ (Ioo (m - ℓ / 2) (m + ℓ / 2))
        ≤ linePull μ (Ioc (lineKnot μ α k) (lineKnot μ α (k + 1))) := by
          apply measure_mono
          intro t ht
          simp only [m, ℓ, lineLength] at ht
          constructor <;> linarith [ht.1, ht.2]
      _ = ENNReal.ofReal (4 * Real.pi + 2 * α * ℓ) := hl.linePull_Ioc_lineKnot k
      _ ≤ _ := ENNReal.ofReal_le_ofReal (by nlinarith [hl.hα, hl.hαr, hl.hr])
  have d1 := hC m (2 * (2 * (2 * (ℓ / 2)))) (by positivity) (by linarith)
  have d2 := hC m (2 * (2 * (ℓ / 2))) (by positivity) (by linarith)
  have d3 := hC m (2 * (ℓ / 2)) (by positivity) (by linarith)
  have d4 := hC m (ℓ / 2) (by positivity) (by linarith)
  calc μ (lineInterval x (3 * ℓ)) ≤ μ (lineInterval m (2 * (2 * (2 * (2 * (ℓ / 2)))))) :=
        measure_mono hsub
    _ ≤ C * (C * (C * (C * μ (lineInterval m (ℓ / 2))))) := by
        refine d1.trans ?_
        gcongr
        refine d2.trans ?_
        gcongr
        refine d3.trans ?_
        gcongr
    _ = C ^ 4 * μ (lineInterval m (ℓ / 2)) := by ring
    _ ≤ C ^ 4 * ENNReal.ofReal (4 * Real.pi + 13) := by gcongr

end LineHyp

namespace LineConsts

variable {μ : Measure ℂ} {r C₂ c₀ α₁ : ℝ} (hc : LineConsts μ r C₂ c₀ α₁)
include hc

/-- Near field, upper bound (§3.5). -/
theorem near_upper : ∃ C : ℝ, ∀ α : ℝ, 0 ≤ α → α ≤ α₁ → ∀ s : ℝ, 0 ≤ s → s ≤ 1 / 2 →
    ∀ (k : ℤ) (z : ℂ), ‖z - lineCentre μ α k‖ < 2 * lineLength μ α k →
      (∀ b : Bool, z ≠ lineNode μ α s k b) → lineTerm μ α s k z ≤ C := by
  have hr := hc.hr
  obtain ⟨CD, -, hCD⟩ := hc.hμ.doubling_le (A := 208 * r) (by linarith)
  obtain ⟨CL, hCL⟩ := hc.hμ.m13_lintegral_log_line (A := 156 * r) (by linarith)
  obtain ⟨CB, hCB⟩ := isLineMeasure_lebLine.m13_lintegral_log_line (A := 156 * r) (by linarith)
  have hπ := Real.pi_pos
  refine ⟨1 / (2 * Real.pi) * (CL * ((CD : ℝ) ^ 4 * (4 * Real.pi + 13))),
    fun α hα hα' s hs hs' k z hz hnode ↦ ?_⟩
  have hl := hc.hyp hα hα'
  obtain ⟨g1, g2, g3⟩ := hl.near_geom hc.hc₀.le (hc.centre α hα hα') hs hs' hz
  set ℓ := lineLength μ α k
  have hp : 0 < ℓ := hl.lineLength_pos k
  have hR : 0 < 3 * ℓ := by positivity
  have hRA : 3 * ℓ ≤ 156 * r := by linarith [hl.lineLength_le k]
  rw [hl.lineTerm_eq_R s k z (3 * ℓ)]
  have t1 : ∀ b, Real.log ‖z - lineNode μ α s k b‖ - Real.log (3 * ℓ) ≤ 0 := fun b ↦ by
    have h0 : 0 < ‖z - lineNode μ α s k b‖ := norm_pos_iff.2 (sub_ne_zero.2 (hnode b))
    linarith [Real.log_le_log h0 (g2 b).le]
  obtain ⟨-, hμup⟩ := hc.hμ.m13_setIntegral_logR_bounds hCL hR hRA g1
  obtain ⟨hleb0, -⟩ := isLineMeasure_lebLine.m13_setIntegral_logR_bounds hCB hR hRA g1
  rw [linePull_lebLine] at hleb0
  have hmass := hl.near_mass hCD k g3
  have hmass' : (μ (lineInterval z.re (3 * ℓ))).toReal ≤ (CD : ℝ) ^ 4 * (4 * Real.pi + 13) := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top) hmass
    rwa [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.coe_toReal,
      ENNReal.toReal_ofReal (by positivity)] at this
  have hX := hμup.trans (mul_le_mul_of_nonneg_left hmass' CL.coe_nonneg)
  have hY : 0 ≤ 2 * α * ∫ t in Ioc (lineKnot μ α k) (lineKnot μ α (k + 1)),
      (Real.log (3 * ℓ) - Real.log ‖z - t‖) := mul_nonneg (by positivity) hleb0
  have := mul_le_mul_of_nonneg_left (show (∫ t in Ioc (lineKnot μ α k) (lineKnot μ α (k + 1)),
      (Real.log (3 * ℓ) - Real.log ‖z - t‖) ∂linePull μ) - 2 * α * ∫ t in Ioc (lineKnot μ α k)
      (lineKnot μ α (k + 1)), (Real.log (3 * ℓ) - Real.log ‖z - t‖) ≤
      CL * ((CD : ℝ) ^ 4 * (4 * Real.pi + 13)) by linarith)
    (by positivity : (0 : ℝ) ≤ 1 / (2 * Real.pi))
  linarith [t1 true, t1 false]

/-- Near field, lower bound (§3.5). -/
theorem near_lower : ∃ C : ℝ, ∀ α : ℝ, 0 ≤ α → α ≤ α₁ → ∀ s : ℝ, 0 ≤ s → s ≤ c₀ / 2 →
    ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ (k : ℤ) (z : ℂ),
      ‖z - lineCentre μ α k‖ < 2 * lineLength μ α k →
      (∀ b : Bool, η * massRadiusLine μ (lineNode μ α s k b) ≤ ‖z - lineNode μ α s k b‖) →
      2 * Real.log η - C ≤ lineTerm μ α s k z := by
  have hr := hc.hr
  obtain ⟨CL, hCL⟩ := hc.hμ.m13_lintegral_log_line (A := 156 * r) (by linarith)
  obtain ⟨CB, hCB⟩ := isLineMeasure_lebLine.m13_lintegral_log_line (A := 156 * r) (by linarith)
  have hπ := Real.pi_pos
  have hC₂ := hc.hC₂
  refine ⟨2 * Real.log (3 * C₂) + 39 / Real.pi * CB,
    fun α hα hα' s hs hs' η hη hη1 k z hz hnode ↦ ?_⟩
  have hl := hc.hyp hα hα'
  have hs'' : s ≤ 1 / 2 := by linarith [hc.hc₀']
  obtain ⟨g1, -, -⟩ := hl.near_geom hc.hc₀.le (hc.centre α hα hα') hs hs'' hz
  set ℓ := lineLength μ α k
  have hp : 0 < ℓ := hl.lineLength_pos k
  have hR : 0 < 3 * ℓ := by positivity
  have hRA : 3 * ℓ ≤ 156 * r := by linarith [hl.lineLength_le k]
  rw [hl.lineTerm_eq_R s k z (3 * ℓ)]
  have t1 : ∀ b, Real.log η - Real.log (3 * C₂) ≤
      Real.log ‖z - lineNode μ α s k b‖ - Real.log (3 * ℓ) := fun b ↦ by
    obtain ⟨o, ho, he⟩ := lineNode_eq μ α s k b
    have hob : |o| ≤ c₀ / 2 := by
      rcases ho with rfl | rfl <;> simp [abs_of_nonneg hs, hs']
    obtain ⟨m1, m2⟩ := hc.offset_mem hα hα' k hob
    have hc0 : 0 ≤ c₀ / 2 * ℓ := by have := hc.hc₀; positivity
    have hmem : lineNode μ α s k b ∈ Icc (lineKnot μ α k) (lineKnot μ α (k + 1)) := by
      rw [he]; constructor <;> linarith
    have hrho := (hc.rho α hα hα' k _ hmem).2
    have hρpos : 0 < massRadiusLine μ (lineNode μ α s k b) := by
      by_contra h0; push Not at h0; nlinarith
    have hlow : η * ℓ / C₂ ≤ ‖z - lineNode μ α s k b‖ := by
      refine le_trans ?_ (hnode b)
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    have hpos : 0 < η * ℓ / C₂ := by have : 0 < C₂ := by linarith
                                     positivity
    have := Real.log_le_log hpos hlow
    rw [Real.log_div (by positivity) (by linarith), Real.log_mul hη.ne' hp.ne'] at this
    rw [Real.log_mul (by norm_num) hp.ne', Real.log_mul (by norm_num) (by linarith)]
    linarith
  obtain ⟨hμ0, -⟩ := hc.hμ.m13_setIntegral_logR_bounds hCL hR hRA g1
  obtain ⟨-, hleb⟩ := isLineMeasure_lebLine.m13_setIntegral_logR_bounds hCB hR hRA g1
  rw [linePull_lebLine, lebLine_lineInterval, ENNReal.toReal_ofReal (by positivity)] at hleb
  have hαℓ : α * ℓ ≤ 13 / 2 := by
    have := hl.lineLength_le k
    nlinarith [hl.hαr, hl.hα]
  have hY : 2 * α * ∫ t in Ioc (lineKnot μ α k) (lineKnot μ α (k + 1)),
      (Real.log (3 * ℓ) - Real.log ‖z - t‖) ≤ 78 * CB := by
    have := mul_le_mul_of_nonneg_left hleb (by positivity : (0 : ℝ) ≤ 2 * α)
    have hCB0 : (0 : ℝ) ≤ CB := CB.coe_nonneg
    nlinarith
  have key : -(39 / Real.pi * CB) ≤ 1 / (2 * Real.pi) *
      ((∫ t in Ioc (lineKnot μ α k) (lineKnot μ α (k + 1)),
        (Real.log (3 * ℓ) - Real.log ‖z - t‖) ∂linePull μ) -
        2 * α * ∫ t in Ioc (lineKnot μ α k) (lineKnot μ α (k + 1)),
          (Real.log (3 * ℓ) - Real.log ‖z - t‖)) := by
    rw [show -(39 / Real.pi * CB) = 1 / (2 * Real.pi) * (-(78 * CB)) by field_simp; ring]
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  linarith [t1 true, t1 false]

end LineConsts

/-! ### Far field -/

/-- `|log|1 − w| + Re w| ≤ |w|²` for `|w| ≤ 1/2`. -/
theorem m13_abs_log_norm_one_sub_add_re_le {w : ℂ} (hw : ‖w‖ ≤ 1 / 2) :
    |Real.log ‖1 - w‖ + w.re| ≤ ‖w‖ ^ 2 := by
  have h1 : ‖-w‖ < 1 := by rw [norm_neg]; linarith
  have h := Complex.norm_log_one_add_sub_self_le h1
  have e : Real.log ‖1 - w‖ + w.re = (Complex.log (1 + -w) - -w).re := by
    rw [sub_re, Complex.log_re, neg_re, ← sub_eq_add_neg]; ring
  rw [e]
  refine (Complex.abs_re_le_norm _).trans (h.trans ?_)
  rw [norm_neg]
  have hw0 := norm_nonneg w
  have : (1 - ‖w‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  have := mul_le_mul_of_nonneg_left this (sq_nonneg ‖w‖)
  linarith

/-- The second-order remainder of `log |z − t|` around `t = λ`. -/
theorem m13_abs_log_norm_sub_remainder_le {z : ℂ} {lam t : ℝ} (hd : 0 < ‖z - lam‖)
    (ht : |t - lam| ≤ ‖z - lam‖ / 2) :
    |Real.log ‖z - t‖ - Real.log ‖z - lam‖ + ((z - lam)⁻¹).re * (t - lam)| ≤
      (|t - lam| / ‖z - lam‖) ^ 2 := by
  set d := ‖z - lam‖
  have hz0 : z - lam ≠ 0 := norm_pos_iff.1 hd
  set w : ℂ := ((t - lam : ℝ) : ℂ) * (z - lam)⁻¹
  have hwn : ‖w‖ = |t - lam| / d := by
    simp only [w, norm_mul, norm_inv, norm_real, Real.norm_eq_abs, d]; ring
  have hw : ‖w‖ ≤ 1 / 2 := by
    rw [hwn, div_le_iff₀ hd]; linarith
  have hzt : z - t = (z - lam) * (1 - w) := by
    simp only [w]; push_cast; field_simp; ring
  have h1w : 0 < ‖1 - w‖ := by
    have := norm_sub_norm_le (1 : ℂ) w
    rw [norm_one] at this; linarith
  have hlog : Real.log ‖z - t‖ = Real.log d + Real.log ‖1 - w‖ := by
    rw [hzt, norm_mul, Real.log_mul hd.ne' h1w.ne']
  have hre : w.re = ((z - lam)⁻¹).re * (t - lam) := by
    simp only [w, re_ofReal_mul]; ring
  rw [hlog, ← hwn, show Real.log d + Real.log ‖1 - w‖ - Real.log d + ((z - lam)⁻¹).re * (t - lam)
    = Real.log ‖1 - w‖ + w.re by rw [hre]; ring]
  exact m13_abs_log_norm_one_sub_add_re_le hw

namespace LineConsts

variable {μ : Measure ℂ} {r C₂ c₀ α₁ : ℝ} (hc : LineConsts μ r C₂ c₀ α₁)
include hc

/-- Far field (§3.5): moment cancellation. -/
theorem far_field {α : ℝ} (hα : 0 ≤ α) (hα' : α ≤ α₁) {s : ℝ} (hs : 0 ≤ s) (hs' : s ≤ 1 / 2)
    (k : ℤ) (z : ℂ) (hz : 2 * lineLength μ α k ≤ ‖z - lineCentre μ α k‖) :
    |lineTerm μ α s k z| ≤ 8 * (lineLength μ α k / ‖z - lineCentre μ α k‖) ^ 2 := by
  have hl := hc.hyp hα hα'
  set a := lineKnot μ α k
  set b := lineKnot μ α (k + 1)
  set lam := lineCentre μ α k
  set ℓ := lineLength μ α k
  have hp : 0 < ℓ := hl.lineLength_pos k
  have hab : a ≤ b := hl.lineKnot_le k
  have hℓ : ℓ = b - a := rfl
  set d := ‖z - lam‖
  have hd : 0 < d := by linarith
  set c := ((z - lam)⁻¹).re
  set q := (ℓ / d) ^ 2
  have hq0 : 0 ≤ q := sq_nonneg _
  obtain ⟨hc1, hc2⟩ := hc.centre α hα hα' k
  have hc0 : 0 ≤ c₀ * ℓ := by have := hc.hc₀; positivity
  let E : ℝ → ℝ := fun t ↦ Real.log ‖z - t‖ - Real.log d + c * (t - lam)
  have hE : ∀ t ∈ Ioc a b, |E t| ≤ q := by
    intro t ht
    have h1 : |t - lam| ≤ ℓ := by rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
    refine (m13_abs_log_norm_sub_remainder_le hd (by linarith)).trans ?_
    show (|t - lam| / d) ^ 2 ≤ (ℓ / d) ^ 2
    gcongr
  have hEν : ∀ bb : Bool, |E (lineNode μ α s k bb)| ≤ q / 4 := by
    intro bb
    obtain ⟨o, ho, he⟩ := lineNode_eq μ α s k bb
    have h1 : |lineNode μ α s k bb - lam| ≤ ℓ / 2 := by
      rw [he, show lam + o * ℓ - lam = o * ℓ by ring, abs_mul, abs_of_pos hp]
      have : |o| ≤ 1 / 2 := by
        rcases ho with rfl | rfl
        · rw [abs_of_nonneg hs]; exact hs'
        · rw [abs_neg, abs_of_nonneg hs]; exact hs'
      nlinarith [abs_nonneg o]
    refine (m13_abs_log_norm_sub_remainder_le hd (by linarith)).trans ?_
    calc (|lineNode μ α s k bb - lam| / d) ^ 2 ≤ (ℓ / 2 / d) ^ 2 := by gcongr
      _ = q / 4 := by simp only [q]; ring
  -- integrals
  have hmfin := hl.hμ.linePull_Ioc_lt_top a b
  have hint_log := hl.hμ.m13_integrableOn_log z a b
  have hint_id := hl.integrableOn_id a b
  have hint_logv := m13_integrableOn_log_volume z a b
  have hint_idv : IntegrableOn (fun t : ℝ ↦ t) (Ioc a b) volume :=
    (continuous_id.integrableOn_Icc (a := a) (b := b)).mono_set Ioc_subset_Icc_self
  have hEint : ∀ {m₀ : Measure ℝ}, m₀ (Ioc a b) < ∞ →
      IntegrableOn (fun t : ℝ ↦ Real.log ‖z - t‖) (Ioc a b) m₀ →
      IntegrableOn (fun t : ℝ ↦ t) (Ioc a b) m₀ →
      ∫ t in Ioc a b, E t ∂m₀ = (∫ t in Ioc a b, Real.log ‖z - t‖ ∂m₀) -
        Real.log d * (m₀ (Ioc a b)).toReal +
          c * ((∫ t in Ioc a b, t ∂m₀) - lam * (m₀ (Ioc a b)).toReal) := by
    intro m₀ hfin hl1 hl2
    simp only [E]
    have i1 : IntegrableOn (fun t : ℝ ↦ Real.log ‖z - t‖ - Real.log d) (Ioc a b) m₀ :=
      hl1.sub (integrableOn_const hfin.ne)
    have i2 : IntegrableOn (fun t : ℝ ↦ c * (t - lam)) (Ioc a b) m₀ :=
      (hl2.sub (integrableOn_const hfin.ne)).const_mul c
    rw [integral_add i1 i2, integral_sub hl1
      (integrableOn_const hfin.ne), integral_const_mul, integral_sub hl2
      (integrableOn_const hfin.ne), setIntegral_const, setIntegral_const, measureReal_def,
      smul_eq_mul, smul_eq_mul]
    ring
  have hEμ := hEint hmfin hint_log hint_id
  have hEv := hEint measure_Ioc_lt_top hint_logv hint_idv
  rw [Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)] at hEv
  have hm := hl.toReal_linePull_Ioc_lineKnot k
  have hlam : lam * (4 * Real.pi) = (∫ t in Ioc a b, t ∂linePull μ) -
      2 * α * ∫ t in Ioc a b, t := by
    have hπ := Real.pi_pos
    simp only [lam, lineCentre]
    rw [intervalIntegral.integral_of_le hab]
    field_simp
    rfl
  have hnode : ∀ bb : Bool, Real.log ‖z - lineNode μ α s k bb‖ =
      E (lineNode μ α s k bb) + Real.log d - c * (lineNode μ α s k bb - lam) := by
    intro bb; simp only [E]; ring
  have hsum : lineNode μ α s k true + lineNode μ α s k false = 2 * lam := by
    simp [lineNode]; ring
  have hT : lineTerm μ α s k z = E (lineNode μ α s k true) + E (lineNode μ α s k false) -
      (1 / (2 * Real.pi)) * ((∫ t in Ioc a b, E t ∂linePull μ) -
        2 * α * ∫ t in Ioc a b, E t) := by
    have hπ := Real.pi_pos
    unfold lineTerm
    rw [intervalIntegral.integral_of_le hab, hnode true, hnode false, hEμ, hEv, hm]
    rw [← hℓ] at hEv ⊢
    field_simp
    linear_combination (-(2 * Real.pi * c)) * hsum - c * hlam * 1
  -- bounds
  have bμ : |∫ t in Ioc a b, E t ∂linePull μ| ≤ q * (4 * Real.pi + 2 * α * ℓ) := by
    have := norm_setIntegral_le_of_norm_le_const hmfin (fun t ht ↦ (Real.norm_eq_abs _).trans_le
      (hE t ht))
    rwa [measureReal_def, hm, Real.norm_eq_abs] at this
  have bv : |∫ t in Ioc a b, E t| ≤ q * ℓ := by
    have := norm_setIntegral_le_of_norm_le_const (μ := volume) measure_Ioc_lt_top
      (fun t ht ↦ (Real.norm_eq_abs _).trans_le (hE t ht))
    rwa [measureReal_def, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith),
      Real.norm_eq_abs, ← hℓ] at this
  have hαℓ : α * ℓ ≤ 13 / 2 := by
    have := hl.lineLength_le k
    nlinarith [hl.hαr, hl.hα]
  have hπ := Real.pi_pos
  have hπ3 := Real.pi_gt_three
  rw [hT]
  have i1 : |(1 / (2 * Real.pi)) * ((∫ t in Ioc a b, E t ∂linePull μ) -
      2 * α * ∫ t in Ioc a b, E t)| ≤ (1 / (2 * Real.pi)) * (q * (4 * Real.pi + 4 * α * ℓ)) := by
    rw [abs_mul, abs_of_pos (by positivity)]
    gcongr
    calc |(∫ t in Ioc a b, E t ∂linePull μ) - 2 * α * ∫ t in Ioc a b, E t|
        ≤ |∫ t in Ioc a b, E t ∂linePull μ| + |2 * α * ∫ t in Ioc a b, E t| := abs_sub _ _
      _ ≤ q * (4 * Real.pi + 2 * α * ℓ) + 2 * α * (q * ℓ) := by
          rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * α)]
          gcongr
      _ = q * (4 * Real.pi + 4 * α * ℓ) := by ring
  have i2 : (1 / (2 * Real.pi)) * (q * (4 * Real.pi + 4 * α * ℓ)) ≤ 7 * q := by
    rw [show (1 / (2 * Real.pi)) * (q * (4 * Real.pi + 4 * α * ℓ)) =
      q * 2 + q * (α * ℓ) * (2 / Real.pi) by field_simp; ring]
    have : 2 / Real.pi ≤ 2 / 3 := by gcongr
    have := mul_le_mul (mul_le_mul_of_nonneg_left hαℓ hq0) this (by positivity)
      (by positivity)
    nlinarith
  calc |E (lineNode μ α s k true) + E (lineNode μ α s k false) -
        (1 / (2 * Real.pi)) * ((∫ t in Ioc a b, E t ∂linePull μ) - 2 * α * ∫ t in Ioc a b, E t)|
      ≤ |E (lineNode μ α s k true)| + |E (lineNode μ α s k false)| +
          |(1 / (2 * Real.pi)) * ((∫ t in Ioc a b, E t ∂linePull μ) -
            2 * α * ∫ t in Ioc a b, E t)| := by
        refine (abs_sub _ _).trans ?_
        gcongr
        exact abs_add_le _ _
    _ ≤ q / 4 + q / 4 + 7 * q := by linarith [hEν true, hEν false]
    _ ≤ 8 * q := by linarith

end LineConsts

/-! ### The far sum (§3.6(b)) -/

/-- The pointwise majorant of `a_k / |z − t|²` on far cells. -/
theorem m13_majorant_aux {ρ ρt ℓ u q A C₁ C₂ Cg γ : ℝ} (hρ : 0 < ρ) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hu : 0 ≤ u) (hqu : u ≤ q) (hqℓ : ℓ ≤ q) (hρt : 0 < ρt) (h1 : ρt ≤ ℓ) (h2 : ℓ ≤ C₂ * ρt)
    (hA : ℓ ≤ A) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hCg : 0 ≤ Cg)
    (hL5 : u < ρ → ρ ≤ C₁ * ρt) (hL6 : ρ ≤ u → u ≤ 1 → ρt ≤ Cg * ρ ^ γ * u ^ (1 - γ)) :
    ℓ / q ^ 2 ≤ 4 * (C₁ + C₂ * Cg) * (ρ ^ γ / (ρ + u) ^ (1 + γ)) + 4 * A / (1 + u) ^ 2 := by
  have hℓ : 0 < ℓ := hρt.trans_le h1
  have hq : 0 < q := hℓ.trans_le hqℓ
  have hA0 : 0 < A := hℓ.trans_le hA
  have hργ : 0 < ρ ^ γ := Real.rpow_pos_of_pos hρ γ
  have hT1 : 0 ≤ ρ ^ γ / (ρ + u) ^ (1 + γ) := by positivity
  have hT2 : 0 ≤ 4 * A / (1 + u) ^ 2 := by positivity
  have h4 : (2 : ℝ) ^ (1 + γ) ≤ 4 := by
    calc (2 : ℝ) ^ (1 + γ) ≤ 2 ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num)
          (by linarith)
      _ = 4 := by rw [Real.rpow_two]; norm_num
  rcases lt_or_ge u ρ with hlt | hge
  · -- `u < ρ`
    have hρC := hL5 hlt
    have e1 : ℓ / q ^ 2 ≤ C₁ / ρ := by
      calc ℓ / q ^ 2 ≤ ℓ / ℓ ^ 2 := by gcongr
        _ = 1 / ℓ := by field_simp
        _ ≤ 1 / ρt := by gcongr
        _ ≤ C₁ / ρ := by rw [div_le_div_iff₀ hρt hρ]; linarith
    have e2 : (ρ + u) ^ (1 + γ) ≤ 4 * ρ * ρ ^ γ := by
      calc (ρ + u) ^ (1 + γ) ≤ (2 * ρ) ^ (1 + γ) :=
            Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
        _ = 2 ^ (1 + γ) * (ρ * ρ ^ γ) := by
            rw [Real.mul_rpow (by norm_num) hρ.le, Real.rpow_add hρ, Real.rpow_one]
        _ ≤ 4 * (ρ * ρ ^ γ) := by gcongr
        _ = 4 * ρ * ρ ^ γ := by ring
    have e3 : C₁ / ρ ≤ 4 * C₁ * (ρ ^ γ / (ρ + u) ^ (1 + γ)) := by
      have hpos : 0 < (ρ + u) ^ (1 + γ) := by positivity
      rw [div_le_iff₀ hρ, mul_div_assoc', div_mul_eq_mul_div, le_div_iff₀ hpos]
      nlinarith [mul_le_mul_of_nonneg_left e2 hC₁]
    have e4 : 4 * C₁ * (ρ ^ γ / (ρ + u) ^ (1 + γ)) ≤
        4 * (C₁ + C₂ * Cg) * (ρ ^ γ / (ρ + u) ^ (1 + γ)) := by
      gcongr; nlinarith
    linarith
  · have hu0 : 0 < u := hρ.trans_le hge
    rcases le_or_gt u 1 with hu1 | hu1
    · have hρt' := hL6 hge hu1
      have e1 : ℓ / q ^ 2 ≤ C₂ * Cg * (ρ ^ γ / u ^ (1 + γ)) := by
        have hsplit : u ^ (1 - γ) * u ^ (1 + γ) = u ^ 2 := by
          rw [← Real.rpow_add hu0, show 1 - γ + (1 + γ) = (2 : ℝ) by ring, Real.rpow_two]
        have hpos : 0 < u ^ (1 + γ) := by positivity
        calc ℓ / q ^ 2 ≤ ℓ / u ^ 2 := by gcongr
          _ ≤ C₂ * (Cg * ρ ^ γ * u ^ (1 - γ)) / u ^ 2 := by
              gcongr; exact h2.trans (mul_le_mul_of_nonneg_left hρt' hC₂)
          _ = C₂ * Cg * (ρ ^ γ / u ^ (1 + γ)) := by
              rw [← hsplit]; field_simp
      have e2 : (ρ + u) ^ (1 + γ) ≤ 4 * u ^ (1 + γ) := by
        calc (ρ + u) ^ (1 + γ) ≤ (2 * u) ^ (1 + γ) :=
              Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
          _ = 2 ^ (1 + γ) * u ^ (1 + γ) := by rw [Real.mul_rpow (by norm_num) hu0.le]
          _ ≤ 4 * u ^ (1 + γ) := by gcongr
      have e3 : C₂ * Cg * (ρ ^ γ / u ^ (1 + γ)) ≤
          4 * (C₂ * Cg) * (ρ ^ γ / (ρ + u) ^ (1 + γ)) := by
        have hp1 : 0 < u ^ (1 + γ) := by positivity
        have hp2 : 0 < (ρ + u) ^ (1 + γ) := by positivity
        have : ρ ^ γ / u ^ (1 + γ) ≤ 4 * (ρ ^ γ / (ρ + u) ^ (1 + γ)) := by
          rw [div_le_iff₀ hp1, mul_div_assoc', div_mul_eq_mul_div, le_div_iff₀ hp2]
          nlinarith
        have h0 : 0 ≤ C₂ * Cg := by positivity
        nlinarith
      have e4 : 4 * (C₂ * Cg) * (ρ ^ γ / (ρ + u) ^ (1 + γ)) ≤
          4 * (C₁ + C₂ * Cg) * (ρ ^ γ / (ρ + u) ^ (1 + γ)) := by
        gcongr; linarith
      linarith
    · have e1 : ℓ / q ^ 2 ≤ A / u ^ 2 := by
        calc ℓ / q ^ 2 ≤ ℓ / u ^ 2 := by gcongr
          _ ≤ A / u ^ 2 := by gcongr
      have e2 : A / u ^ 2 ≤ 4 * A / (1 + u) ^ 2 := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have h' : (1 + u) ^ 2 ≤ 4 * u ^ 2 := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_left h' hA0.le]
      have : 0 ≤ 4 * (C₁ + C₂ * Cg) * (ρ ^ γ / (ρ + u) ^ (1 + γ)) := by positivity
      linarith

/-- The majorant `ρ^γ/(ρ + |t − x|)^{1+γ}` is integrable with integral independent of `x`. -/
theorem m13_integral_majorant {γ : ℝ} (hγ : 0 < γ) {ρ : ℝ} (hρ : 0 < ρ) (x : ℝ) :
    Integrable (fun t : ℝ ↦ ρ ^ γ / (ρ + |t - x|) ^ (1 + γ)) ∧
      ∫ t : ℝ, ρ ^ γ / (ρ + |t - x|) ^ (1 + γ) = ∫ v : ℝ, (1 + ‖v‖) ^ (-(1 + γ)) := by
  set g : ℝ → ℝ := fun v ↦ (1 + ‖v‖) ^ (-(1 + γ))
  have hg : Integrable g := integrable_one_add_norm (by simp; linarith)
  have heq : (fun t : ℝ ↦ ρ ^ γ / (ρ + |t - x|) ^ (1 + γ)) =
      fun t ↦ ρ⁻¹ * g ((t - x) / ρ) := by
    funext t
    simp only [g, Real.norm_eq_abs, abs_div, abs_of_pos hρ]
    have h1 : 1 + |t - x| / ρ = (ρ + |t - x|) / ρ := by field_simp
    have hpos : 0 < ρ + |t - x| := by positivity
    rw [h1, Real.rpow_neg (by positivity), Real.div_rpow hpos.le hρ.le, inv_div,
      Real.rpow_add hρ, Real.rpow_one]
    field_simp
  rw [heq]
  refine ⟨(hg.comp_div hρ.ne').comp_sub_right x |>.const_mul _, ?_⟩
  rw [integral_const_mul, integral_sub_right_eq_self (fun t ↦ g (t / ρ)) x,
    Measure.integral_comp_div, abs_of_pos hρ, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hρ.ne',
    one_mul]

theorem m13_integral_majorant₂ (A x : ℝ) :
    Integrable (fun t : ℝ ↦ 4 * A / (1 + |t - x|) ^ 2) ∧
      ∫ t : ℝ, 4 * A / (1 + |t - x|) ^ 2 = 4 * A * ∫ v : ℝ, (1 + ‖v‖) ^ (-(2 : ℝ)) := by
  set g : ℝ → ℝ := fun v ↦ (1 + ‖v‖) ^ (-(2 : ℝ))
  have hg : Integrable g := integrable_one_add_norm (by simp)
  have heq : (fun t : ℝ ↦ 4 * A / (1 + |t - x|) ^ 2) = fun t ↦ 4 * A * g (t - x) := by
    funext t
    simp only [g, Real.norm_eq_abs]
    rw [Real.rpow_neg (by positivity), Real.rpow_two, div_eq_mul_inv]
  rw [heq]
  exact ⟨(hg.comp_sub_right x).const_mul _, by
    rw [integral_const_mul, integral_sub_right_eq_self g x]⟩

theorem LineHyp.cells_disjoint {μ : Measure ℂ} {r α : ℝ} (hl : LineHyp μ r α) :
    Pairwise (Function.onFun Disjoint fun k : ℤ ↦ Ioc (lineKnot μ α k) (lineKnot μ α (k + 1))) := by
  intro k k' hkk'
  rcases lt_or_gt_of_ne hkk' with h | h
  · exact Ioc_disjoint_Ioc_of_le (hl.lineKnot_strictMono.monotone (by omega : k + 1 ≤ k'))
  · exact (Ioc_disjoint_Ioc_of_le (hl.lineKnot_strictMono.monotone (by omega : k' + 1 ≤ k))).symm

namespace LineConsts

variable {μ : Measure ℂ} {r C₂ c₀ α₁ : ℝ} (hc : LineConsts μ r C₂ c₀ α₁)
include hc

theorem centre_mem_Icc {α : ℝ} (hα : 0 ≤ α) (hα' : α ≤ α₁) (k : ℤ) :
    lineCentre μ α k ∈ Icc (lineKnot μ α k) (lineKnot μ α (k + 1)) := by
  obtain ⟨h1, h2⟩ := hc.centre α hα hα' k
  have := (hc.hyp hα hα').lineLength_pos k
  have := hc.hc₀
  constructor <;> nlinarith

/-- §3.6(b): the far sum is bounded uniformly in `z`. -/
theorem far_sum : ∃ Cf : ℝ, 0 ≤ Cf ∧ ∀ α : ℝ, 0 ≤ α → α ≤ α₁ → ∀ (z : ℂ) (F : Finset ℤ),
    (∀ k ∈ F, 2 * lineLength μ α k ≤ ‖z - lineCentre μ α k‖) →
    ∑ k ∈ F, (lineLength μ α k / ‖z - lineCentre μ α k‖) ^ 2 ≤ Cf := by
  obtain ⟨C₁, hC₁, hL5⟩ := hc.hμ.massRadiusLine_comparable (K := 1) one_pos
  obtain ⟨γ, Cg, hγ, hγ1, hCg, hL6⟩ := hc.hμ.massRadiusLine_le_rpow
  set K₁ := ∫ v : ℝ, (1 + ‖v‖) ^ (-(1 + γ))
  set K₂ := ∫ v : ℝ, (1 + ‖v‖) ^ (-(2 : ℝ))
  have hK₁ : 0 ≤ K₁ := integral_nonneg fun v ↦ by positivity
  have hK₂ : 0 ≤ K₂ := integral_nonneg fun v ↦ by positivity
  have hr := hc.hr
  have hC₂ := hc.hC₂
  set A := 52 * r
  set Ch := 4 * (C₁ + C₂ * Cg)
  have hCh : 0 ≤ Ch := by positivity
  refine ⟨9 / 4 * (Ch * K₁ + 4 * A * K₂), by positivity, fun α hα hα' z F hF ↦ ?_⟩
  have hl := hc.hyp hα hα'
  set x := z.re
  set ρ := massRadiusLine μ x
  have hρ : 0 < ρ := hc.hμ.massRadiusLine_pos x
  set h : ℝ → ℝ := fun t ↦ Ch * (ρ ^ γ / (ρ + |t - x|) ^ (1 + γ)) + 4 * A / (1 + |t - x|) ^ 2
  obtain ⟨hi1, he1⟩ := m13_integral_majorant hγ hρ x
  obtain ⟨hi2, he2⟩ := m13_integral_majorant₂ A x
  have hint : Integrable h := (hi1.const_mul Ch).add hi2
  have hval : ∫ t, h t = Ch * K₁ + 4 * A * K₂ := by
    simp only [h]
    rw [integral_add (hi1.const_mul Ch) hi2, integral_const_mul, he1, he2]
  have hh0 : ∀ t, 0 ≤ h t := fun t ↦ by simp only [h]; positivity
  have hcell : ∀ k ∈ F, (lineLength μ α k / ‖z - lineCentre μ α k‖) ^ 2 ≤
      9 / 4 * ∫ t in Ioc (lineKnot μ α k) (lineKnot μ α (k + 1)), h t := by
    intro k hk
    set ℓ := lineLength μ α k
    set lam := lineCentre μ α k
    set d := ‖z - lam‖
    have hp : 0 < ℓ := hl.lineLength_pos k
    have hdk : 2 * ℓ ≤ d := hF k hk
    have hd : 0 < d := by linarith
    have hab := hl.lineKnot_le k
    have hlamI := hc.centre_mem_Icc hα hα' k
    have e0 : (ℓ / d) ^ 2 = ∫ t in Ioc (lineKnot μ α k) (lineKnot μ α (k + 1)), ℓ / d ^ 2 := by
      rw [setIntegral_const, measureReal_def, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith),
        smul_eq_mul]
      simp only [ℓ, lineLength]
      field_simp
    rw [e0, ← integral_const_mul]
    refine setIntegral_mono_on (integrableOn_const measure_Ioc_lt_top.ne)
      (hint.integrableOn.const_mul _) measurableSet_Ioc (fun t ht ↦ ?_)
    set q := ‖z - t‖
    have hlt : |lam - t| ≤ ℓ := by
      rw [abs_le]; simp only [ℓ, lineLength]; constructor <;> linarith [ht.1, ht.2, hlamI.1, hlamI.2]
    have hq1 : q ≤ d + ℓ := by
      calc q ≤ ‖z - lam‖ + ‖((lam : ℝ) : ℂ) - t‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ = d + |lam - t| := by rw [m13_norm_ofReal_sub_ofReal]
        _ ≤ d + ℓ := by linarith
    have hq2 : d - ℓ ≤ q := by
      have := norm_sub_norm_le (z - lam) (z - t)
      rw [show z - lam - (z - t) = ((t : ℂ) - lam) by ring, m13_norm_ofReal_sub_ofReal,
        abs_sub_comm] at this
      linarith
    have hqu : |t - x| ≤ q := m13_norm_sub_ofReal_ge z t
    have htI : t ∈ Icc (lineKnot μ α k) (lineKnot μ α (k + 1)) := ⟨ht.1.le, ht.2⟩
    obtain ⟨hr1, hr2⟩ := hc.rho α hα hα' k t htI
    have hρt : 0 < massRadiusLine μ t := hc.hμ.massRadiusLine_pos t
    have hmaj := m13_majorant_aux (ρ := ρ) (ρt := massRadiusLine μ t) (ℓ := ℓ) (u := |t - x|)
      (q := q) (A := A) (C₁ := C₁) (C₂ := C₂) (Cg := Cg) hρ hγ hγ1 (abs_nonneg _) hqu
      (by linarith) hρt hr1 hr2 (hl.lineLength_le k) (by linarith) (by linarith) hCg.le
      (fun hlt ↦ hL5 t x (by rw [one_mul]; exact hlt.le.trans (le_max_right _ _)))
      (fun h1 h2 ↦ by rw [abs_sub_comm] at h1 h2 ⊢; exact hL6 x t h1 h2)
    have hq : 0 < q := by linarith
    have hqd : ℓ / d ^ 2 ≤ 9 / 4 * (ℓ / q ^ 2) := by
      rw [div_le_iff₀ (by positivity), mul_div_assoc', div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      have : q ^ 2 ≤ (9 / 4) * d ^ 2 := by nlinarith
      nlinarith
    calc ℓ / d ^ 2 ≤ 9 / 4 * (ℓ / q ^ 2) := hqd
      _ ≤ 9 / 4 * h t := by gcongr
  have hunion : ∑ k ∈ F, ∫ t in Ioc (lineKnot μ α k) (lineKnot μ α (k + 1)), h t =
      ∫ t in ⋃ k ∈ F, Ioc (lineKnot μ α k) (lineKnot μ α (k + 1)), h t :=
    (integral_biUnion_finset F (fun _ _ ↦ measurableSet_Ioc)
      (fun k _ k' _ hkk' ↦ hl.cells_disjoint hkk') (fun _ _ ↦ hint.integrableOn)).symm
  calc ∑ k ∈ F, (lineLength μ α k / ‖z - lineCentre μ α k‖) ^ 2
      ≤ ∑ k ∈ F, 9 / 4 * ∫ t in Ioc (lineKnot μ α k) (lineKnot μ α (k + 1)), h t :=
        Finset.sum_le_sum hcell
    _ = 9 / 4 * ∫ t in ⋃ k ∈ F, Ioc (lineKnot μ α k) (lineKnot μ α (k + 1)), h t := by
        rw [← Finset.mul_sum, hunion]
    _ ≤ 9 / 4 * ∫ t, h t :=
        mul_le_mul_of_nonneg_left (setIntegral_le_integral hint (Eventually.of_forall hh0))
          (by norm_num)
    _ = 9 / 4 * (Ch * K₁ + 4 * A * K₂) := by rw [hval]

end LineConsts

namespace LineConsts

variable {μ : Measure ℂ} {r C₂ c₀ α₁ : ℝ} (hc : LineConsts μ r C₂ c₀ α₁)
include hc

/-- §3.6(a): the number of near cells is bounded uniformly in `z`. -/
theorem near_count : ∃ N₀ : ℕ, ∀ α : ℝ, 0 ≤ α → α ≤ α₁ → ∀ (z : ℂ) (F : Finset ℤ),
    (∀ k ∈ F, ‖z - lineCentre μ α k‖ < 2 * lineLength μ α k) → F.card ≤ N₀ := by
  have hC₂ := hc.hC₂
  obtain ⟨C₅, hC₅, hL5⟩ := hc.hμ.massRadiusLine_comparable (K := 2 * C₂) (by linarith)
  refine ⟨⌈6 * C₂ * C₅ ^ 2⌉₊, fun α hα hα' z F hF ↦ ?_⟩
  have hl := hc.hyp hα hα'
  set x := z.re
  set ρ := massRadiusLine μ x
  have hρ : 0 < ρ := hc.hμ.massRadiusLine_pos x
  have hcell : ∀ k ∈ F, ρ / C₅ ≤ lineLength μ α k ∧
      Ioc (lineKnot μ α k) (lineKnot μ α (k + 1)) ⊆
        Ioo (x - 3 * C₂ * C₅ * ρ) (x + 3 * C₂ * C₅ * ρ) := by
    intro k hk
    set lam := lineCentre μ α k
    set ℓ := lineLength μ α k
    have hlamI := hc.centre_mem_Icc hα hα' k
    obtain ⟨hr1, hr2⟩ := hc.rho α hα hα' k lam hlamI
    have hxl : |x - lam| < 2 * ℓ := by
      have := m13_norm_sub_ofReal_ge z lam
      rw [abs_sub_comm]; linarith [hF k hk]
    have hK : |x - lam| ≤ 2 * C₂ * max ρ (massRadiusLine μ lam) := by
      have : 2 * ℓ ≤ 2 * C₂ * massRadiusLine μ lam := by linarith
      have h2 : massRadiusLine μ lam ≤ max ρ (massRadiusLine μ lam) := le_max_right _ _
      nlinarith
    have hK' : |lam - x| ≤ 2 * C₂ * max (massRadiusLine μ lam) ρ := by
      rw [abs_sub_comm, max_comm]; exact hK
    have c1 := hL5 x lam hK
    have c2 := hL5 lam x hK'
    have hC5 : 0 < C₅ := by linarith
    refine ⟨?_, fun t ht ↦ ?_⟩
    · rw [div_le_iff₀ hC5]; nlinarith
    · have hlt : |t - lam| ≤ ℓ := by
        rw [abs_le]; simp only [ℓ, lineLength]; constructor <;> linarith [ht.1, ht.2, hlamI.1, hlamI.2]
      have hℓ : ℓ ≤ C₂ * C₅ * ρ := by nlinarith
      have : |t - x| < 3 * C₂ * C₅ * ρ := by
        calc |t - x| ≤ |t - lam| + |lam - x| := abs_sub_le _ _ _
          _ < ℓ + 2 * ℓ := by rw [abs_sub_comm lam x]; linarith
          _ ≤ 3 * C₂ * C₅ * ρ := by linarith
      rw [abs_lt] at this
      constructor <;> linarith [this.1, this.2]
  -- Lebesgue measure of the union of the cells
  have hsum : ∑ k ∈ F, lineLength μ α k ≤ 6 * C₂ * C₅ * ρ := by
    have hU : ⋃ k ∈ F, Ioc (lineKnot μ α k) (lineKnot μ α (k + 1)) ⊆
        Ioo (x - 3 * C₂ * C₅ * ρ) (x + 3 * C₂ * C₅ * ρ) :=
      iUnion₂_subset fun k hk ↦ (hcell k hk).2
    have hm := measure_mono (μ := volume) hU
    rw [measure_biUnion_finset (fun k _ k' _ hkk' ↦ hl.cells_disjoint hkk')
      (fun _ _ ↦ measurableSet_Ioc), Real.volume_Ioo] at hm
    simp_rw [Real.volume_Ioc] at hm
    rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ ↦ by linarith [hl.lineKnot_le k])] at hm
    have hpos : 0 ≤ 3 * C₂ * C₅ * ρ := by
      have : (0 : ℝ) < C₅ := by linarith
      have : (0 : ℝ) < C₂ := by linarith
      positivity
    have := (ENNReal.ofReal_le_ofReal_iff (by linarith)).1 hm
    simp only [lineLength]
    linarith
  have hlow : (F.card : ℝ) * (ρ / C₅) ≤ ∑ k ∈ F, lineLength μ α k := by
    have := Finset.card_nsmul_le_sum F (fun k ↦ lineLength μ α k) (ρ / C₅)
      (fun k hk ↦ (hcell k hk).1)
    rwa [nsmul_eq_mul] at this
  have hC5 : 0 < C₅ := by linarith
  have : (F.card : ℝ) ≤ 6 * C₂ * C₅ ^ 2 := by
    have h1 : (F.card : ℝ) * (ρ / C₅) ≤ 6 * C₂ * C₅ * ρ := hlow.trans hsum
    rw [mul_div_assoc', div_le_iff₀ hC5] at h1
    have : (F.card : ℝ) * ρ ≤ 6 * C₂ * C₅ ^ 2 * ρ := by nlinarith
    exact le_of_mul_le_mul_right this hρ
  exact_mod_cast this.trans (Nat.le_ceil _)

/-- The near set is finite. -/
theorem near_finite {α : ℝ} (hα : 0 ≤ α) (hα' : α ≤ α₁) (z : ℂ) :
    {k : ℤ | ‖z - lineCentre μ α k‖ < 2 * lineLength μ α k}.Finite := by
  have hl := hc.hyp hα hα'
  obtain ⟨K₀, K₁, hK⟩ := hl.cells_meeting_subset (z.re - 104 * r) (z.re + 104 * r)
  refine (Set.finite_Icc K₀ K₁).subset fun k hk ↦ ?_
  have hlamI := hc.centre_mem_Icc hα hα' k
  have hle := hl.lineLength_le k
  have : |z.re - lineCentre μ α k| < 2 * lineLength μ α k := by
    have := m13_norm_sub_ofReal_ge z (lineCentre μ α k)
    rw [abs_sub_comm]; exact this.trans_lt hk
  rw [abs_lt] at this
  exact hK k (by linarith [hlamI.2]) (by linarith [hlamI.1])

omit hc in
/-- The far part of the series, as a summable nonnegative majorant. -/
theorem far_summable {Cf : ℝ} (hCf : ∀ α : ℝ, 0 ≤ α → α ≤ α₁ → ∀ (z : ℂ) (F : Finset ℤ),
      (∀ k ∈ F, 2 * lineLength μ α k ≤ ‖z - lineCentre μ α k‖) →
      ∑ k ∈ F, (lineLength μ α k / ‖z - lineCentre μ α k‖) ^ 2 ≤ Cf)
    {α : ℝ} (hα : 0 ≤ α) (hα' : α ≤ α₁) (z : ℂ) :
    let f : ℤ → ℝ := fun k ↦ if 2 * lineLength μ α k ≤ ‖z - lineCentre μ α k‖ then
      (lineLength μ α k / ‖z - lineCentre μ α k‖) ^ 2 else 0
    Summable f ∧ ∑' k, f k ≤ Cf ∧ 0 ≤ f := by
  intro f
  have hf0 : 0 ≤ f := fun k ↦ by simp only [f]; split_ifs <;> positivity
  have hsum : ∀ u : Finset ℤ, ∑ k ∈ u, f k ≤ Cf := by
    intro u
    classical
    have e : ∑ k ∈ u, f k = ∑ k ∈ u.filter (fun k ↦ 2 * lineLength μ α k ≤
        ‖z - lineCentre μ α k‖), (lineLength μ α k / ‖z - lineCentre μ α k‖) ^ 2 := by
      rw [Finset.sum_filter]
    rw [e]
    exact hCf α hα hα' z _ (fun k hk ↦ (Finset.mem_filter.1 hk).2)
  exact ⟨summable_of_sum_le hf0 hsum, Real.tsum_le_of_sum_le hf0 hsum, hf0⟩

end LineConsts

namespace LineConsts

variable {μ : Measure ℂ} {r C₂ c₀ α₁ : ℝ} (hc : LineConsts μ r C₂ c₀ α₁)
include hc

/-- Splitting the series into far and near cells. -/
theorem lineTerm_split {Cf : ℝ} (hCf : ∀ α : ℝ, 0 ≤ α → α ≤ α₁ → ∀ (z : ℂ) (F : Finset ℤ),
      (∀ k ∈ F, 2 * lineLength μ α k ≤ ‖z - lineCentre μ α k‖) →
      ∑ k ∈ F, (lineLength μ α k / ‖z - lineCentre μ α k‖) ^ 2 ≤ Cf)
    {α : ℝ} (hα : 0 ≤ α) (hα' : α ≤ α₁) {s : ℝ} (hs : 0 ≤ s) (hs' : s ≤ 1 / 2) (z : ℂ) :
    Summable (fun k ↦ lineTerm μ α s k z) ∧
      |∑' k, (if 2 * lineLength μ α k ≤ ‖z - lineCentre μ α k‖ then lineTerm μ α s k z
        else 0)| ≤ 8 * Cf ∧
      linePotential μ α s z = ∑' k, (if 2 * lineLength μ α k ≤ ‖z - lineCentre μ α k‖ then
        lineTerm μ α s k z else 0) + ∑ k ∈ (hc.near_finite hα hα' z).toFinset, lineTerm μ α s k z := by
  obtain ⟨hf, hfle, hf0⟩ := far_summable hCf hα hα' z
  set f : ℤ → ℝ := fun k ↦ if 2 * lineLength μ α k ≤ ‖z - lineCentre μ α k‖ then
      (lineLength μ α k / ‖z - lineCentre μ α k‖) ^ 2 else 0
  set g : ℤ → ℝ := fun k ↦ if 2 * lineLength μ α k ≤ ‖z - lineCentre μ α k‖ then
      lineTerm μ α s k z else 0
  set N := (hc.near_finite hα hα' z).toFinset
  have hgb : ∀ k, ‖g k‖ ≤ 8 * f k := by
    intro k
    simp only [g, f]
    split_ifs with h
    · rw [Real.norm_eq_abs]; exact hc.far_field hα hα' hs hs' k z h
    · simp
  have hg : Summable g := (hf.mul_left 8).of_norm_bounded hgb
  have hres : Summable (fun k ↦ lineTerm μ α s k z - g k) := by
    refine summable_of_ne_finset_zero (s := N) (fun k hk ↦ ?_)
    have : 2 * lineLength μ α k ≤ ‖z - lineCentre μ α k‖ := by
      by_contra h
      exact hk ((hc.near_finite hα hα' z).mem_toFinset.2 (not_le.1 h))
    simp [g, this]
  have hT : Summable (fun k ↦ lineTerm μ α s k z) := (hg.add hres).congr (fun k ↦ by ring)
  refine ⟨hT, ?_, ?_⟩
  · have h8 : ∑' k, 8 * f k ≤ 8 * Cf := by rw [tsum_mul_left]; linarith
    rw [abs_le]
    constructor
    · have := (hg.neg).tsum_le_tsum (fun k ↦ (neg_le_abs (g k)).trans
        ((Real.norm_eq_abs _).symm.le.trans (hgb k))) (hf.mul_left 8)
      rw [tsum_neg] at this
      linarith
    · have := hg.tsum_le_tsum (fun k ↦ (le_abs_self (g k)).trans
        ((Real.norm_eq_abs _).symm.le.trans (hgb k))) (hf.mul_left 8)
      linarith
  · unfold linePotential
    rw [show (fun k ↦ lineTerm μ α s k z) = fun k ↦ g k + (lineTerm μ α s k z - g k) from
      funext fun k ↦ by ring, hg.tsum_add hres]
    congr 1
    rw [tsum_eq_sum (s := N)]
    · refine Finset.sum_congr rfl fun k hk ↦ ?_
      have : ¬ 2 * lineLength μ α k ≤ ‖z - lineCentre μ α k‖ :=
        not_le.2 ((hc.near_finite hα hα' z).mem_toFinset.1 hk)
      simp [g, this]
    · intro k hk
      have : 2 * lineLength μ α k ≤ ‖z - lineCentre μ α k‖ := by
        by_contra h
        exact hk ((hc.near_finite hα hα' z).mem_toFinset.2 (not_le.1 h))
      simp [g, this]

end LineConsts

/-! 13.5 far-field and near-field estimates of a single term -/
theorem IsLineMeasure.abs_lineTerm_le_of_far {μ : Measure ℂ} (hμ : IsLineMeasure μ) :
    ∃ α₁ : ℝ, 0 < α₁ ∧ ∀ α : ℝ, 0 ≤ α → α ≤ α₁ → ∀ s : ℝ, 0 ≤ s → s ≤ 1 / 2 → ∀ (k : ℤ) (z : ℂ),
      2 * lineLength μ α k ≤ ‖z - lineCentre μ α k‖ →
      |lineTerm μ α s k z| ≤ 8 * (lineLength μ α k / ‖z - lineCentre μ α k‖) ^ 2 := by
  obtain ⟨r, C₂, c₀, α₁, hc⟩ := hμ.exists_lineConsts
  exact ⟨α₁, hc.hα₁, fun α hα hα' s hs hs' k z hz ↦ hc.far_field hα hα' hs hs' k z hz⟩

theorem IsLineMeasure.lineTerm_le_of_near {μ : Measure ℂ} (hμ : IsLineMeasure μ) :
    ∃ α₁ C : ℝ, 0 < α₁ ∧ ∀ α : ℝ, 0 ≤ α → α ≤ α₁ → ∀ s : ℝ, 0 ≤ s → s ≤ 1 / 2 →
      ∀ (k : ℤ) (z : ℂ), ‖z - lineCentre μ α k‖ < 2 * lineLength μ α k →
      (∀ b : Bool, z ≠ lineNode μ α s k b) → lineTerm μ α s k z ≤ C := by
  obtain ⟨r, C₂, c₀, α₁, hc⟩ := hμ.exists_lineConsts
  obtain ⟨C, hC⟩ := hc.near_upper
  exact ⟨α₁, C, hc.hα₁, hC⟩

theorem IsLineMeasure.le_lineTerm_of_near {μ : Measure ℂ} (hμ : IsLineMeasure μ) :
    ∃ α₁ s₁ C : ℝ, 0 < α₁ ∧ 0 < s₁ ∧ s₁ ≤ 1 / 8 ∧ ∀ α : ℝ, 0 ≤ α → α ≤ α₁ →
      ∀ s : ℝ, 0 ≤ s → s ≤ s₁ →
      ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ (k : ℤ) (z : ℂ),
      ‖z - lineCentre μ α k‖ < 2 * lineLength μ α k →
      (∀ b : Bool, η * massRadiusLine μ (lineNode μ α s k b) ≤ ‖z - lineNode μ α s k b‖) →
      2 * Real.log η - C ≤ lineTerm μ α s k z := by
  obtain ⟨r, C₂, c₀, α₁, hc⟩ := hμ.exists_lineConsts
  obtain ⟨C, hC⟩ := hc.near_lower
  exact ⟨α₁, c₀ / 2, C, hc.hα₁, by linarith [hc.hc₀], by linarith [hc.hc₀'], hC⟩

/-! 13.6 the potential: summability and two-sided bounds -/
theorem IsLineMeasure.summable_lineTerm {μ : Measure ℂ} (hμ : IsLineMeasure μ) :
    ∃ α₁ : ℝ, 0 < α₁ ∧ ∀ α : ℝ, 0 ≤ α → α ≤ α₁ → ∀ s : ℝ, 0 ≤ s → s ≤ 1 / 2 → ∀ z : ℂ,
      Summable fun k : ℤ ↦ lineTerm μ α s k z := by
  obtain ⟨r, C₂, c₀, α₁, hc⟩ := hμ.exists_lineConsts
  obtain ⟨Cf, -, hCf⟩ := hc.far_sum
  exact ⟨α₁, hc.hα₁, fun α hα hα' s hs hs' z ↦ (hc.lineTerm_split hCf hα hα' hs hs' z).1⟩

theorem IsLineMeasure.linePotential_bounds {μ : Measure ℂ} (hμ : IsLineMeasure μ) :
    ∃ α₁ s₁ C : ℝ, 0 < α₁ ∧ 0 < s₁ ∧ s₁ ≤ 1 / 8 ∧ ∀ α : ℝ, 0 ≤ α → α ≤ α₁ →
      ∀ s : ℝ, 0 ≤ s → s ≤ s₁ →
      (∀ z, z ∉ lineZeroSet μ α s → linePotential μ α s z ≤ C) ∧
      ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ z : ℂ,
        (∀ ν ∈ lineZeroSet μ α s, η * massRadiusLine μ ν.re ≤ ‖z - ν‖) →
        -C * (1 + |Real.log η|) ≤ linePotential μ α s z := by
  obtain ⟨r, C₂, c₀, α₁, hc⟩ := hμ.exists_lineConsts
  obtain ⟨Cf, hCf0, hCf⟩ := hc.far_sum
  obtain ⟨N₀, hN₀⟩ := hc.near_count
  obtain ⟨Cu, hCu⟩ := hc.near_upper
  obtain ⟨Cl, hCl⟩ := hc.near_lower
  set Cu' := max Cu 0
  set Cl' := max Cl 0
  have hCu' : 0 ≤ Cu' := le_max_right _ _
  have hCl' : 0 ≤ Cl' := le_max_right _ _
  have hN0 : (0 : ℝ) ≤ N₀ := Nat.cast_nonneg _
  refine ⟨α₁, c₀ / 2, 8 * Cf + N₀ * (Cu' + Cl') + 2 * N₀, hc.hα₁, by linarith [hc.hc₀],
    by linarith [hc.hc₀'], fun α hα hα' s hs hs' ↦ ⟨fun z hz ↦ ?_, fun η hη hη1 z hz ↦ ?_⟩⟩
  · have hs'' : s ≤ 1 / 2 := by linarith [hc.hc₀']
    obtain ⟨-, hG, hS⟩ := hc.lineTerm_split hCf hα hα' hs hs'' z
    set N := (hc.near_finite hα hα' z).toFinset
    have hcard : (N.card : ℝ) ≤ N₀ := by
      exact_mod_cast hN₀ α hα hα' z N (fun k hk ↦ (hc.near_finite hα hα' z).mem_toFinset.1 hk)
    have hnear : ∑ k ∈ N, lineTerm μ α s k z ≤ N₀ * Cu' := by
      calc ∑ k ∈ N, lineTerm μ α s k z ≤ ∑ k ∈ N, Cu' := by
            refine Finset.sum_le_sum fun k hk ↦ (hCu α hα hα' s hs hs'' k z
              ((hc.near_finite hα hα' z).mem_toFinset.1 hk) (fun b hb ↦ hz ?_)).trans
              (le_max_left _ _)
            rw [hb]
            cases b
            · exact Or.inr ⟨k, rfl⟩
            · exact Or.inl ⟨k, rfl⟩
        _ = N.card * Cu' := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ N₀ * Cu' := by gcongr
    rw [hS]
    have := (abs_le.1 hG).2
    nlinarith
  · have hs'' : s ≤ 1 / 2 := by linarith [hc.hc₀']
    obtain ⟨-, hG, hS⟩ := hc.lineTerm_split hCf hα hα' hs hs'' z
    set N := (hc.near_finite hα hα' z).toFinset
    have hcard : (N.card : ℝ) ≤ N₀ := by
      exact_mod_cast hN₀ α hα hα' z N (fun k hk ↦ (hc.near_finite hα hα' z).mem_toFinset.1 hk)
    have hlog : Real.log η ≤ 0 := Real.log_nonpos hη.le hη1
    have hm : 2 * Real.log η - Cl' ≤ 0 := by linarith
    have hnear : N₀ * (2 * Real.log η - Cl') ≤ ∑ k ∈ N, lineTerm μ α s k z := by
      calc (N₀ : ℝ) * (2 * Real.log η - Cl') ≤ N.card * (2 * Real.log η - Cl') :=
            mul_le_mul_of_nonpos_right hcard hm
        _ = ∑ k ∈ N, (2 * Real.log η - Cl') := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ k ∈ N, lineTerm μ α s k z := by
            refine Finset.sum_le_sum fun k hk ↦ le_trans ?_ (hCl α hα hα' s hs hs' η hη hη1 k z
              ((hc.near_finite hα hα' z).mem_toFinset.1 hk) (fun b ↦ ?_))
            · linarith [le_max_left Cl 0]
            · have hmem : ((lineNode μ α s k b : ℝ) : ℂ) ∈ lineZeroSet μ α s := by
                cases b
                · exact Or.inr ⟨k, rfl⟩
                · exact Or.inl ⟨k, rfl⟩
              have := hz _ hmem
              simpa using this
    rw [hS]
    have := (abs_le.1 hG).1
    rw [abs_of_nonpos hlog]
    have hC0 : 0 ≤ 8 * Cf + N₀ * (Cu' + Cl') := by positivity
    have hp := mul_nonpos_of_nonneg_of_nonpos hC0 hlog
    have hp2 : 0 ≤ (N₀ : ℝ) * Cu' := by positivity
    linarith

end OC
