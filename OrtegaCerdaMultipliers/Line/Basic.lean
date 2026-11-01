import OrtegaCerdaMultipliers.Doubling.LineMeasure

/-!
# M13 (Theorem5) — Bridge between `μ` on `ℂ` and its pull-back to `ℝ`

See `blueprint/M13_Theorem5.md` §3.1.

Reconciliation: M13's `lineMeasure μ = μ.comap ofReal` is M03's `linePull μ` (same definition),
so M13 uses `linePull`; `lineMeasure_apply` is M03's `linePull_apply` (no measurability
hypothesis needed).  `IsLineMeasure` and the line forms L1–L8 of M03 lemmas are in M03
(`Doubling/LineMeasure.lean`).

Besides the two exported lemmas, this file provides:
* `lebLine`, the push-forward of Lebesgue measure on `ℝ` to `ℂ`, which is itself an
  `IsLineMeasure` (`isLineMeasure_lebLine`) with `linePull lebLine = volume`; this lets the
  Lebesgue part of the signed measure `μ − 2α dt` be treated by the same M03 lemmas as `μ`;
* the transfer of (set) integrals between `μ` and `linePull μ`.
-/

open MeasureTheory Metric Set Complex
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace OC

theorem m13_range_ofReal_compl : (range fun x : ℝ ↦ (x : ℂ))ᶜ = {z : ℂ | z.im ≠ 0} := by
  ext z
  simp only [mem_compl_iff, mem_range, not_exists]
  constructor
  · intro hz him
    exact hz z.re (Complex.ext (by simp) (by simp [him]))
  · intro him x hx
    apply him
    rw [← hx]
    simp

theorem map_linePull {μ : Measure ℂ} (hμ : μ {z : ℂ | z.im ≠ 0} = 0) :
    (linePull μ).map (fun t : ℝ ↦ (t : ℂ)) = μ := by
  rw [linePull, measurableEmbedding_ofReal'.map_comap]
  apply Measure.restrict_eq_self_of_ae_mem
  rw [ae_iff]
  have : {a : ℂ | a ∉ range fun x : ℝ ↦ (x : ℂ)} = {z : ℂ | z.im ≠ 0} := m13_range_ofReal_compl
  rw [this]
  exact hμ

theorem IsLineMeasure.linePull_Ioc_lt_top {μ : Measure ℂ} (hμ : IsLineMeasure μ) (a b : ℝ) :
    linePull μ (Ioc a b) < ∞ := by
  rw [linePull_apply]
  refine lt_of_le_of_lt (measure_mono (image_mono Ioc_subset_Icc_self)) ?_
  exact hμ.finite_of_compact _ (isCompact_Icc.image continuous_ofReal)

/-! ### Helpers -/

theorem IsLineMeasure.m13_linePull_compact_lt_top {μ : Measure ℂ} (hμ : IsLineMeasure μ) {K : Set ℝ}
    (hK : IsCompact K) : linePull μ K < ∞ := by
  rw [linePull_apply]
  exact hμ.finite_of_compact _ (hK.image continuous_ofReal)

theorem IsLineMeasure.m13_isFiniteMeasureOnCompacts' {μ : Measure ℂ} (hμ : IsLineMeasure μ) :
    IsFiniteMeasureOnCompacts (linePull μ) :=
  ⟨fun _ hK ↦ hμ.m13_linePull_compact_lt_top hK⟩

theorem IsLineMeasure.m13_isFiniteMeasure_restrict_Ioc {μ : Measure ℂ} (hμ : IsLineMeasure μ)
    (a b : ℝ) : IsFiniteMeasure ((linePull μ).restrict (Ioc a b)) :=
  ⟨by rw [Measure.restrict_apply_univ]; exact hμ.linePull_Ioc_lt_top a b⟩

theorem IsLineMeasure.m13_map_linePull {μ : Measure ℂ} (hμ : IsLineMeasure μ) :
    (linePull μ).map (fun t : ℝ ↦ (t : ℂ)) = μ :=
  OC.map_linePull hμ.doubling.1

theorem m13_linePull_Ioo (μ : Measure ℂ) (x r : ℝ) :
    linePull μ (Ioo (x - r) (x + r)) = μ (lineInterval x r) := by
  rw [linePull_apply]; rfl

/-- Integrals against `μ` (carried by `ℝ`) are integrals against `linePull μ`. -/
theorem IsLineMeasure.m13_integral_eq {μ : Measure ℂ} (hμ : IsLineMeasure μ) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ℂ → E) :
    ∫ z, f z ∂μ = ∫ t, f t ∂linePull μ := by
  conv_lhs => rw [← hμ.m13_map_linePull]
  exact measurableEmbedding_ofReal'.integral_map f

/-- Set lintegrals over images of real sets. -/
theorem IsLineMeasure.m13_setLIntegral_image {μ : Measure ℂ} (hμ : IsLineMeasure μ) (f : ℂ → ℝ≥0∞)
    (s : Set ℝ) :
    ∫⁻ z in (fun t : ℝ ↦ (t : ℂ)) '' s, f z ∂μ = ∫⁻ t in s, f t ∂linePull μ := by
  conv_lhs => rw [← hμ.m13_map_linePull]
  rw [measurableEmbedding_ofReal'.restrict_map, measurableEmbedding_ofReal'.lintegral_map,
    preimage_image_eq _ ofReal_injective]

/-! ### Lebesgue measure on the line, as a measure on `ℂ` -/

/-- Lebesgue measure on `ℝ`, pushed to `ℂ`. -/
def lebLine : Measure ℂ := Measure.map (fun t : ℝ ↦ (t : ℂ)) volume

theorem lebLine_apply (s : Set ℂ) :
    lebLine s = volume ((fun t : ℝ ↦ (t : ℂ)) ⁻¹' s) :=
  measurableEmbedding_ofReal'.map_apply _ _

theorem linePull_lebLine : linePull lebLine = volume :=
  measurableEmbedding_ofReal'.comap_map _

theorem lebLine_lineInterval (x r : ℝ) :
    lebLine (lineInterval x r) = ENNReal.ofReal (2 * r) := by
  rw [lebLine_apply, lineInterval, preimage_image_eq _ ofReal_injective, Real.volume_Ioo]
  congr 1; ring

theorem isLineMeasure_lebLine : IsLineMeasure lebLine where
  finite_of_compact K hK := by
    rw [lebLine_apply]
    exact (Complex.isometry_ofReal.isClosedEmbedding.isCompact_preimage hK).measure_lt_top
  doubling := by
    refine ⟨?_, 2, fun x r hr _ ↦ ?_⟩
    · rw [lebLine_apply]
      convert measure_empty (μ := (volume : Measure ℝ))
      ext t; simp
    · rw [lebLine_lineInterval, lebLine_lineInterval]
      rw [show (2 : ℝ) * (2 * r) = 2 * (2 * r) from rfl, ENNReal.ofReal_mul (by norm_num)]
      simp
  mass := ⟨1, one_pos, fun x ↦ by
    rw [lebLine_lineInterval]; norm_num⟩

end OC
