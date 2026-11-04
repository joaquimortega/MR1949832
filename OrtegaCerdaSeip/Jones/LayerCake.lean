module

public import Mathlib

/-!
# M04 (Jones) — the layer-cake lemma `∫ e^{-F} dm ≤ 1`

See `blueprint/M04_Jones.md` (§1.1).

For a finite measure `m` and a measurable `h : α → ℝ`, put `F(a) = m{b : h b ≤ h a}` (the
distribution function of `h_* m` evaluated at `h a`).  Then `∫ e^{-F} dm ≤ 1`.  This is the heart of
Jones' `L^∞` estimate ("`∫ e^{-P} dP ≤ 1`"), which the paper quotes from [J] on p. 410.

Proof: `m{a : F(a) ≤ s} ≤ s` for every `s` (the set is `h⁻¹` of a half-line on which the
distribution function is `≤ s`), and `e^{-F} = ∫_F^∞ e^{-s} ds`, so by Tonelli
`∫ e^{-F} dm = ∫_0^∞ e^{-s} m{F < s} ds ≤ ∫_0^∞ s e^{-s} ds = Γ(2) = 1`.
-/

open MeasureTheory Set Filter
open scoped ENNReal NNReal

@[expose] public noncomputable section

namespace OCS

/-- The distribution function evaluated along `h` is "sub-uniform":
`m{a : m{b : h b ≤ h a} ≤ s} ≤ s`. -/
theorem measure_setOf_measure_le_le {α : Type*} [MeasurableSpace α] (m : Measure α)
    [IsFiniteMeasure m] {h : α → ℝ} (hh : Measurable h) (s : ℝ≥0∞) :
    m {a | m {b | h b ≤ h a} ≤ s} ≤ s := by
  set μ : Measure ℝ := m.map h with hμ
  have hF : ∀ a, m {b | h b ≤ h a} = μ (Iic (h a)) := fun a ↦ by
    rw [hμ, Measure.map_apply hh measurableSet_Iic]; rfl
  set D : Set ℝ := {t | μ (Iic t) ≤ s} with hD
  have hDl : IsLowerSet D := fun t t' htt' ht ↦ (measure_mono (Iic_subset_Iic.2 htt')).trans ht
  have hDm : MeasurableSet D := hDl.ordConnected.measurableSet
  have hpre : {a | m {b | h b ≤ h a} ≤ s} = h ⁻¹' D := by
    ext a; simp [hF, hD]
  rw [hpre]
  refine (Measure.le_map_apply hh.aemeasurable D).trans ?_
  rw [hDm.measure_eq_iSup_isCompact_of_ne_top (measure_ne_top _ _)]
  refine iSup₂_le fun K hKD ↦ iSup_le fun hK ↦ ?_
  rcases K.eq_empty_or_nonempty with rfl | hne
  · simp
  · have hmem := hK.sSup_mem hne
    exact (measure_mono fun x hx ↦ (mem_Iic.2 (le_csSup hK.bddAbove hx))).trans (hKD hmem)

/-- `e^{-x} = ∫_x^∞ e^{-s} ds`. -/
theorem ofReal_exp_neg_eq_lintegral (x : ℝ) :
    ENNReal.ofReal (Real.exp (-x)) = ∫⁻ s in Ioi x, ENNReal.ofReal (Real.exp (-s)) := by
  rw [← integral_exp_neg_Ioi x, ofReal_integral_eq_lintegral_ofReal]
  · exact integrableOn_exp_neg_Ioi x
  · exact Eventually.of_forall fun s ↦ (Real.exp_pos _).le

/-- `∫_0^∞ s e^{-s} ds = 1`. -/
theorem lintegral_Ioi_mul_exp_neg :
    ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal s * ENNReal.ofReal (Real.exp (-s)) = 1 := by
  have hG := Real.Gamma_eq_integral (s := 2) two_pos
  rw [Real.Gamma_two] at hG
  have hint : IntegrableOn (fun x : ℝ ↦ Real.exp (-x) * x ^ ((2 : ℝ) - 1)) (Ioi 0) :=
    Real.GammaIntegral_convergent two_pos
  calc ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal s * ENNReal.ofReal (Real.exp (-s))
      = ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-s) * s ^ ((2 : ℝ) - 1)) := by
        refine setLIntegral_congr_fun measurableSet_Ioi fun s hs ↦ ?_
        rw [← ENNReal.ofReal_mul (le_of_lt hs)]
        norm_num [mul_comm]
    _ = ENNReal.ofReal (∫ s in Ioi (0 : ℝ), Real.exp (-s) * s ^ ((2 : ℝ) - 1)) := by
        rw [ofReal_integral_eq_lintegral_ofReal hint]
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
        exact mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (le_of_lt hs) _)
    _ = 1 := by rw [← hG, ENNReal.ofReal_one]

/-- **Layer-cake lemma.**  `∫ exp(-m{b : h b ≤ h a}) dm(a) ≤ 1` for a finite measure `m`. -/
theorem lintegral_exp_neg_measure_le_le_one {α : Type*} [MeasurableSpace α] (m : Measure α)
    [IsFiniteMeasure m] {h : α → ℝ} (hh : Measurable h) :
    ∫⁻ a, ENNReal.ofReal (Real.exp (-(m {b | h b ≤ h a}).toReal)) ∂m ≤ 1 := by
  set F : α → ℝ≥0∞ := fun a ↦ m {b | h b ≤ h a} with hFdef
  set f : α → ℝ := fun a ↦ (F a).toReal with hfdef
  have hFm : Measurable F := by
    have hG : Monotone fun t ↦ (m.map h) (Iic t) := fun t t' htt' ↦
      measure_mono (Iic_subset_Iic.2 htt')
    have : F = (fun t ↦ (m.map h) (Iic t)) ∘ h := by
      ext a; simp only [hFdef, Function.comp_apply, Measure.map_apply hh measurableSet_Iic]; rfl
    rw [this]
    exact hG.measurable.comp hh
  have hfm : Measurable f := hFm.ennreal_toReal
  set g : α × ℝ → ℝ≥0∞ := {p | f p.1 < p.2}.indicator fun p ↦ ENNReal.ofReal (Real.exp (-p.2))
    with hgdef
  have hgm : Measurable g :=
    (Measurable.ennreal_ofReal (Real.continuous_exp.measurable.comp measurable_snd.neg)).indicator
      (measurableSet_lt (hfm.comp measurable_fst) measurable_snd)
  have hslice : ∀ a, ENNReal.ofReal (Real.exp (-f a)) = ∫⁻ s, g (a, s) := by
    intro a
    rw [ofReal_exp_neg_eq_lintegral, ← lintegral_indicator measurableSet_Ioi]
    rfl
  have hslice' : ∀ s, ∫⁻ a, g (a, s) ∂m ≤
      (Ioi (0 : ℝ)).indicator (fun s ↦ ENNReal.ofReal s * ENNReal.ofReal (Real.exp (-s))) s := by
    intro s
    have : (fun a ↦ g (a, s)) = {a | f a < s}.indicator fun _ ↦ ENNReal.ofReal (Real.exp (-s)) := by
      ext a; simp only [hgdef, indicator, mem_ofPred_eq]
    rw [this, lintegral_indicator_const (measurableSet_lt hfm measurable_const)]
    by_cases hs : 0 < s
    · rw [indicator_of_mem (mem_Ioi.2 hs), mul_comm]
      gcongr
      calc m {a | f a < s} ≤ m {a | F a ≤ ENNReal.ofReal s} := by
            refine measure_mono fun a ha ↦ ?_
            simp only [mem_ofPred_eq] at ha ⊢
            exact (ENNReal.ofReal_toReal (measure_ne_top m _)).symm.le.trans
              (ENNReal.ofReal_le_ofReal ha.le)
        _ ≤ ENNReal.ofReal s := measure_setOf_measure_le_le m hh _
    · have : {a | f a < s} = ∅ := by
        ext a; simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt]
        exact (not_lt.1 hs).trans ENNReal.toReal_nonneg
      simp [this]
  calc ∫⁻ a, ENNReal.ofReal (Real.exp (-(m {b | h b ≤ h a}).toReal)) ∂m
      = ∫⁻ a, ∫⁻ s, g (a, s) ∂volume ∂m := lintegral_congr fun a ↦ hslice a
    _ = ∫⁻ s, ∫⁻ a, g (a, s) ∂m := lintegral_lintegral_swap hgm.aemeasurable
    _ ≤ ∫⁻ s, (Ioi (0 : ℝ)).indicator
          (fun s ↦ ENNReal.ofReal s * ENNReal.ofReal (Real.exp (-s))) s := lintegral_mono hslice'
    _ = 1 := by rw [lintegral_indicator measurableSet_Ioi, lintegral_Ioi_mul_exp_neg]

end OCS
