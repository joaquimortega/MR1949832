import OrtegaCerdaMultipliers.Theorem5
import OrtegaCerdaMultipliers.Foundations.Weyl

/-!
# M14 (Theorem3) — Theorem 3 (degenerate weights), from Theorem 5 and [OCS99]

See `blueprint/M14_Theorem3.md`.  Scaffold: statements, proofs `sorry`; definitions are real.

`theorem3_weighted` is the corrected Theorem 3 (proposed main statement): hypothesis
`TheoremOCS`, conclusion with the weighted integral `∫_{|z-x|<1} e^{-φ(z)} d|μ|(z) / |x − z|`.
The printed `theorem3` of `comparator/statements.lean` is false (`not_theorem3_printed`); it is
kept below only as a comment.
-/

open MeasureTheory Metric Set Complex
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace OC

/-- The measure `|χ_Ω ν / f|`. -/
def divMeasure (ν : Measure ℂ) (Ω : Set ℂ) (f : ℂ → ℂ) : Measure ℂ :=
  (ν.restrict Ω).withDensity fun z ↦ ENNReal.ofReal (1 / ‖f z‖)

/-- The phase of `σ / f` (junk value `1` at the zeros of `f`). -/
def divPhase (σ f : ℂ → ℂ) (z : ℂ) : ℂ :=
  if f z = 0 then 1 else σ z * ((‖f z‖ : ℂ) / f z)

theorem norm_divPhase (σ f : ℂ → ℂ) (hσ : ∀ z, ‖σ z‖ = 1) (z : ℂ) : ‖divPhase σ f z‖ = 1 := by
  unfold divPhase
  split_ifs with h
  · simp
  · rw [norm_mul, hσ, norm_div, Complex.norm_real, norm_norm,
      div_self (norm_ne_zero_iff.2 h), one_mul]

theorem measurable_divPhase {σ f : ℂ → ℂ} (hσ : Measurable σ) (hf : Continuous f) :
    Measurable (divPhase σ f) := by
  unfold divPhase
  refine Measurable.ite ?_ measurable_const ?_
  · exact (isClosed_eq hf continuous_const).measurableSet
  · exact hσ.mul ((Complex.measurable_ofReal.comp hf.measurable.norm).div hf.measurable)

/-- The density `ofReal (1 / ‖f‖)` of `divMeasure` is measurable. -/
theorem measurable_ofReal_one_div_norm {f : ℂ → ℂ} (hf : Continuous f) :
    Measurable fun z ↦ ENNReal.ofReal (1 / ‖f z‖) :=
  (measurable_const.div hf.measurable.norm).ennreal_ofReal

/-- Pointwise core of the Carleson transfer: `1/‖f‖ ≤ c⁻¹ e^{-φ} e^{α|y|}` where
`‖f‖ ≥ c e^{φ - α|y|}`. -/
theorem one_div_norm_le_of_lowerBound {f : ℂ → ℂ} {φ : ℂ → ℝ} {α c : ℝ} (hc : 0 < c) {z : ℂ}
    (h : c * Real.exp (φ z - α * |z.im|) ≤ ‖f z‖) :
    1 / ‖f z‖ ≤ c⁻¹ * Real.exp (-φ z) * Real.exp (α * |z.im|) := by
  have hpos : 0 < c * Real.exp (φ z - α * |z.im|) := by positivity
  calc 1 / ‖f z‖ ≤ 1 / (c * Real.exp (φ z - α * |z.im|)) := one_div_le_one_div_of_le hpos h
    _ = c⁻¹ * Real.exp (-φ z) * Real.exp (α * |z.im|) := by
      rw [one_div, mul_inv, ← Real.exp_neg, mul_assoc, ← Real.exp_add]
      ring_nf

/-! 14.1 finiteness and Carleson transfer -/
theorem isFiniteMeasure_divMeasure {ν : Measure ℂ} [IsFiniteMeasure ν] {L Ω : Set ℂ}
    (hL : IsCompact L) (hνL : ν Lᶜ = 0) {f : ℂ → ℂ} {g : ℂ → ℝ} (hg : Continuous g)
    (hfg : ∀ z ∈ Ω, g z ≤ ‖f z‖) (hg0 : ∀ z, 0 < g z) :
    IsFiniteMeasure (divMeasure ν Ω f) := by
  obtain ⟨M, hM⟩ := hL.exists_bound_of_continuousOn
    ((continuous_const.div hg fun z ↦ (hg0 z).ne').continuousOn (f := fun z ↦ 1 / g z))
  have hmg : Measurable fun z ↦ ENNReal.ofReal (1 / g z) :=
    (measurable_const.div hg.measurable).ennreal_ofReal
  constructor
  rw [divMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  -- neither `f` nor `Ω` is measurable: pass to a measurable minorant with the same integral
  obtain ⟨h, hhm, hhle, hheq⟩ :=
    exists_measurable_le_lintegral_eq (ν.restrict Ω) fun z ↦ ENNReal.ofReal (1 / ‖f z‖)
  rw [hheq]
  -- on `Ω`, `h ≤ 1/‖f‖ ≤ 1/g`; the bad set is measurable, so this holds `ν.restrict Ω`-a.e.
  have hae : ∀ᵐ z ∂ν.restrict Ω, h z ≤ ENNReal.ofReal (1 / g z) := by
    rw [ae_restrict_iff (measurableSet_le hhm hmg)]
    exact ae_of_all _ fun z hz ↦ (hhle z).trans
      (ENNReal.ofReal_le_ofReal (one_div_le_one_div_of_le (hg0 z) (hfg z hz)))
  have hL' : ∀ᵐ z ∂ν, ENNReal.ofReal (1 / g z) ≤ ENNReal.ofReal M := by
    have : ∀ᵐ z ∂ν, z ∈ L := ae_iff.2 hνL
    filter_upwards [this] with z hz
    refine ENNReal.ofReal_le_ofReal ?_
    have := hM z hz
    rwa [Real.norm_of_nonneg (one_div_pos.2 (hg0 z)).le] at this
  calc ∫⁻ z, h z ∂ν.restrict Ω
      ≤ ∫⁻ z, ENNReal.ofReal (1 / g z) ∂ν.restrict Ω := lintegral_mono_ae hae
    _ ≤ ∫⁻ z, ENNReal.ofReal (1 / g z) ∂ν := lintegral_mono' Measure.restrict_le_self le_rfl
    _ ≤ ∫⁻ _, ENNReal.ofReal M ∂ν := lintegral_mono_ae hL'
    _ < ∞ := by rw [lintegral_const]; exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
                  (measure_lt_top ν univ)
theorem divMeasure_withDensity_le {ν : Measure ℂ} {Ω : Set ℂ} (hΩ : MeasurableSet Ω)
    {f : ℂ → ℂ} {φ : ℂ → ℝ} {α c : ℝ} (hf : Continuous f) (hφ : Continuous φ) (hc : 0 < c)
    (hlow : ∀ z ∈ Ω, c * Real.exp (φ z - α * |z.im|) ≤ ‖f z‖) (s : Set ℂ) (hs : MeasurableSet s) :
    ((divMeasure ν Ω f).withDensity fun z ↦ ENNReal.ofReal (Real.exp (-α * |z.im|))) s ≤
      ENNReal.ofReal c⁻¹ * (ν.withDensity fun z ↦ ENNReal.ofReal (Real.exp (-φ z))) s := by
  have hm1 := measurable_ofReal_one_div_norm hf
  have hm2 : Measurable fun z : ℂ ↦ ENNReal.ofReal (Real.exp (-α * |z.im|)) := by fun_prop
  have hm3 : Measurable fun z : ℂ ↦ ENNReal.ofReal (Real.exp (-φ z)) :=
    (hφ.measurable.neg.exp).ennreal_ofReal
  rw [divMeasure, ← withDensity_mul _ hm1 hm2, withDensity_apply _ hs,
    Measure.restrict_restrict hs, withDensity_apply _ hs, ← lintegral_const_mul' _ _
      ENNReal.ofReal_ne_top]
  calc ∫⁻ z in s ∩ Ω, ((fun z ↦ ENNReal.ofReal (1 / ‖f z‖)) *
        fun z : ℂ ↦ ENNReal.ofReal (Real.exp (-α * |z.im|))) z ∂ν
      ≤ ∫⁻ z in s ∩ Ω, ENNReal.ofReal c⁻¹ * ENNReal.ofReal (Real.exp (-φ z)) ∂ν := by
        refine setLIntegral_mono' (hs.inter hΩ) fun z hz ↦ ?_
        simp only [Pi.mul_apply]
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 := one_div_norm_le_of_lowerBound hc (hlow z hz.2)
        calc 1 / ‖f z‖ * Real.exp (-α * |z.im|)
            ≤ c⁻¹ * Real.exp (-φ z) * Real.exp (α * |z.im|) * Real.exp (-α * |z.im|) :=
              mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
          _ = c⁻¹ * Real.exp (-φ z) := by
              rw [mul_assoc, ← Real.exp_add]; ring_nf; simp
    _ ≤ ∫⁻ z in s, ENNReal.ofReal c⁻¹ * ENNReal.ofReal (Real.exp (-φ z)) ∂ν :=
        lintegral_mono_set inter_subset_left
theorem lintegral_ball_divMeasure_le {ν : Measure ℂ} {Ω : Set ℂ} (hΩ : MeasurableSet Ω)
    {f : ℂ → ℂ} {φ : ℂ → ℝ} {α c : ℝ} (hf : Continuous f) (hφ : Continuous φ) (hc : 0 < c)
    (hα : 0 ≤ α)
    (hlow : ∀ z ∈ Ω, c * Real.exp (φ z - α * |z.im|) ≤ ‖f z‖) (x : ℝ) :
    ∫⁻ z in ball (x : ℂ) 1, ENNReal.ofReal (1 / ‖(x : ℂ) - z‖) ∂divMeasure ν Ω f ≤
      ENNReal.ofReal (c⁻¹ * Real.exp α) *
        ∫⁻ z in ball (x : ℂ) 1, ENNReal.ofReal (Real.exp (-φ z) / ‖(x : ℂ) - z‖) ∂ν := by
  have hm1 := measurable_ofReal_one_div_norm hf
  have hk : Measurable fun z : ℂ ↦ ENNReal.ofReal (1 / ‖(x : ℂ) - z‖) := by fun_prop
  rw [divMeasure, restrict_withDensity measurableSet_ball,
    lintegral_withDensity_eq_lintegral_mul _ hm1 hk, Measure.restrict_restrict measurableSet_ball,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  calc ∫⁻ z in ball (x : ℂ) 1 ∩ Ω, ((fun z ↦ ENNReal.ofReal (1 / ‖f z‖)) *
        fun z ↦ ENNReal.ofReal (1 / ‖(x : ℂ) - z‖)) z ∂ν
      ≤ ∫⁻ z in ball (x : ℂ) 1 ∩ Ω, ENNReal.ofReal (c⁻¹ * Real.exp α) *
          ENNReal.ofReal (Real.exp (-φ z) / ‖(x : ℂ) - z‖) ∂ν := by
        refine setLIntegral_mono' (measurableSet_ball.inter hΩ) fun z hz ↦ ?_
        simp only [Pi.mul_apply]
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 := one_div_norm_le_of_lowerBound hc (hlow z hz.2)
        have hy : |z.im| ≤ 1 := by
          have := abs_im_le_norm (z - x)
          rw [sub_im, Complex.ofReal_im, sub_zero] at this
          have h2 : ‖z - x‖ < 1 := by rw [← dist_eq]; exact hz.1
          linarith
        have h3 : Real.exp (α * |z.im|) ≤ Real.exp α :=
          Real.exp_le_exp.2 (by nlinarith [abs_nonneg z.im])
        have h4 : 1 / ‖f z‖ ≤ c⁻¹ * Real.exp α * Real.exp (-φ z) := by
          calc 1 / ‖f z‖ ≤ c⁻¹ * Real.exp (-φ z) * Real.exp (α * |z.im|) := h1
            _ ≤ c⁻¹ * Real.exp (-φ z) * Real.exp α :=
                mul_le_mul_of_nonneg_left h3 (by positivity)
            _ = c⁻¹ * Real.exp α * Real.exp (-φ z) := by ring
        calc 1 / ‖f z‖ * (1 / ‖(x : ℂ) - z‖)
            ≤ c⁻¹ * Real.exp α * Real.exp (-φ z) * (1 / ‖(x : ℂ) - z‖) :=
              mul_le_mul_of_nonneg_right h4 (by positivity)
          _ = c⁻¹ * Real.exp α * (Real.exp (-φ z) / ‖(x : ℂ) - z‖) := by ring
    _ ≤ ∫⁻ z in ball (x : ℂ) 1, ENNReal.ofReal (c⁻¹ * Real.exp α) *
          ENNReal.ofReal (Real.exp (-φ z) / ‖(x : ℂ) - z‖) ∂ν :=
        lintegral_mono_set inter_subset_left

/-! 14.2 gluing: `u = Σ f_i v_i` solves `∂̄u = σν` -/
theorem isWeakDbarSolMeasure_sum_mul {ι : Type*} [Fintype ι] {ν : Measure ℂ}
    [IsFiniteMeasure ν] {σ : ℂ → ℂ} (hσ : Measurable σ) (hσ1 : ∀ z, ‖σ z‖ = 1)
    (Ω : ι → Set ℂ) (hΩm : ∀ i, MeasurableSet (Ω i)) (hΩd : Pairwise (Function.onFun Disjoint Ω))
    (hΩc : ⋃ i, Ω i = univ) (f : ι → ℂ → ℂ) (hf : ∀ i, Differentiable ℂ (f i))
    (hf0 : ∀ i, ∀ z ∈ Ω i, f i z ≠ 0) (hfin : ∀ i, IsFiniteMeasure (divMeasure ν (Ω i) (f i)))
    (v : ι → ℂ → ℂ) (hv : ∀ i, IsWeakDbarSolMeasure (v i) (divMeasure ν (Ω i) (f i))
      (divPhase σ (f i))) :
    IsWeakDbarSolMeasure (fun z ↦ ∑ i, f i z * v i z) ν σ := by
  refine ⟨?_, fun χ hχ hc ↦ ?_⟩
  · exact locallyIntegrable_finsetSum _ fun i _ ↦ (hv i).1.continuous_mul (hf i).continuous
  have hχ1 := contDiff_one_of_top hχ
  -- the test functions `β_i = f_i χ`, with `∂̄β_i = f_i ∂̄χ`
  have hβ : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun z ↦ f i z * χ z) := fun i ↦
    ((hf i).contDiff.restrict_scalars ℝ).mul hχ
  have hβc : ∀ i, HasCompactSupport (fun z ↦ f i z * χ z) := fun i ↦ hc.mul_left
  have hdβ : ∀ i z, dbar (fun z ↦ f i z * χ z) z = f i z * dbar χ z := by
    intro i z
    rw [dbar_mul (((hf i) z).restrictScalars ℝ) (hχ1.differentiable one_ne_zero z),
      dbar_eq_zero_of_differentiableAt ((hf i) z), zero_mul, zero_add]
  -- each piece: `∫ v_i f_i ∂̄χ = -∫_{Ω_i} χ σ dν`
  have hpiece : ∀ i, ∫ z, v i z * (f i z * dbar χ z) = -∫ z in Ω i, χ z * σ z ∂ν := by
    intro i
    have h := (hv i).2 _ (hβ i) (hβc i)
    simp_rw [hdβ] at h
    rw [h, divMeasure, integral_withDensity_eq_integral_toReal_smul
      (measurable_ofReal_one_div_norm (hf i).continuous)
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
    congr 1
    refine setIntegral_congr_fun (hΩm i) fun z hz ↦ ?_
    have h0 := hf0 i z hz
    have hn : (‖f i z‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 h0
    simp only [divPhase, h0, ↓reduceIte]
    rw [ENNReal.toReal_ofReal (by positivity), Complex.real_smul]
    push_cast
    field_simp
  have hint : ∀ i, Integrable (fun z ↦ v i z * (f i z * dbar χ z)) := fun i ↦
    integrable_mul_of_locallyIntegrableOn ((hv i).1.locallyIntegrableOn univ)
      ((hf i).continuous.mul (continuous_dbar hχ1)) ((hasCompactSupport_dbar hc).mul_left)
      (subset_univ _)
  have hχσ : Integrable (fun z ↦ χ z * σ z) ν := by
    obtain ⟨B, hB⟩ := hχ.continuous.bounded_above_of_compact_support hc
    refine Integrable.mono' (integrable_const B)
      (hχ.continuous.measurable.mul hσ).aestronglyMeasurable (ae_of_all _ fun z ↦ ?_)
    rw [norm_mul, hσ1, mul_one]
    exact hB z
  calc ∫ z, (∑ i, f i z * v i z) * dbar χ z = ∫ z, ∑ i, v i z * (f i z * dbar χ z) := by
        congr 1; ext z; rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun i _ ↦ ?_; ring
    _ = ∑ i, ∫ z, v i z * (f i z * dbar χ z) := integral_finsetSum _ fun i _ ↦ hint i
    _ = ∑ i, -∫ z in Ω i, χ z * σ z ∂ν := Finset.sum_congr rfl fun i _ ↦ hpiece i
    _ = -∫ z in ⋃ i, Ω i, χ z * σ z ∂ν := by
        rw [integral_iUnion_fintype hΩm hΩd fun i ↦ hχσ.integrableOn, Finset.sum_neg_distrib]
    _ = -∫ z, χ z * σ z ∂ν := by rw [hΩc, Measure.restrict_univ]

/-! 14.3 helpers: the partition `ℂ = G ⊔ Gᶜ` and the pointwise bounds -/

/-- The exceptional-set complement `{z | ∀ x ∈ ℝ, f x = 0 → ε ρ(x) ≤ |z - x|}` is closed. -/
theorem isClosed_setOf_forall_zero_le (f : ℂ → ℂ) (μ : Measure ℂ) (ε : ℝ) :
    IsClosed {z : ℂ | ∀ x : ℝ, f x = 0 → ε * massRadiusLine μ x ≤ ‖z - x‖} := by
  simp only [ofPred_forall]
  refine isClosed_iInter fun x ↦ isClosed_iInter fun _ ↦ ?_
  exact isClosed_le continuous_const (continuous_id.sub continuous_const).norm

theorem measurableSet_fin_two_partition {G : Set ℂ} (hG : MeasurableSet G) (i : Fin 2) :
    MeasurableSet (![G, Gᶜ] i) := by
  fin_cases i
  exacts [hG, hG.compl]

theorem pairwise_disjoint_fin_two_partition (G : Set ℂ) :
    Pairwise (Function.onFun Disjoint ![G, Gᶜ]) := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · exact disjoint_compl_right
  · exact disjoint_compl_left
  · exact absurd rfl hij

theorem iUnion_fin_two_partition (G : Set ℂ) : ⋃ i, ![G, Gᶜ] i = univ := by
  rw [iUnion_eq_univ_iff]
  intro z
  by_cases hz : z ∈ G
  · exact ⟨0, hz⟩
  · exact ⟨1, hz⟩

/-- `‖Σ f_i v_i‖ e^{-φ} ≤ Σ C (‖v_i‖ e^{-α|y|})` from `‖f_i‖ e^{-φ} ≤ C e^{-α|y|}`. -/
theorem norm_sum_mul_mul_exp_le {ι : Type*} [Fintype ι] {f v : ι → ℂ → ℂ} {φ : ℂ → ℝ}
    {C α : ℝ} (hfu : ∀ i z, ‖f i z‖ * Real.exp (-φ z) ≤ C * Real.exp (-α * |z.im|)) (z : ℂ) :
    ‖∑ i, f i z * v i z‖ * Real.exp (-φ z) ≤
      ∑ i, C * (‖v i z‖ * Real.exp (-α * |z.im|)) := by
  calc ‖∑ i, f i z * v i z‖ * Real.exp (-φ z)
      ≤ (∑ i, ‖f i z‖ * ‖v i z‖) * Real.exp (-φ z) := by
        gcongr
        exact (norm_sum_le _ _).trans (le_of_eq (by simp only [norm_mul]))
    _ = ∑ i, (‖f i z‖ * Real.exp (-φ z)) * ‖v i z‖ := by
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ ↦ by ring
    _ ≤ ∑ i, (C * Real.exp (-α * |z.im|)) * ‖v i z‖ :=
        Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_right (hfu i z) (norm_nonneg _)
    _ = ∑ i, C * (‖v i z‖ * Real.exp (-α * |z.im|)) :=
        Finset.sum_congr rfl fun i _ ↦ by ring

/-- `1 + M J ≤ (1 + M)(1 + J)` in `ℝ≥0∞`. -/
theorem one_add_mul_le_mul_one_add (M J : ℝ≥0∞) : 1 + M * J ≤ (1 + M) * (1 + J) := by
  calc 1 + M * J ≤ 1 + M * J + (J + M) := le_self_add
    _ = (1 + M) * (1 + J) := by ring

/-! 14.3 Theorem 3, corrected (weight inside the integral) -/
theorem theorem3_weighted (hOCS : TheoremOCS) (φ : ℂ → ℝ) (μ : Measure ℂ)
    (hφ : IsSubharmonicWeight univ φ μ) (hd : IsLocallyDoublingLine μ)
    (hm : ∃ r : ℝ, 0 < r ∧ ∀ x : ℝ, 1 < μ (lineInterval x r)) (K : ℝ≥0) :
    ∃ C : ℝ≥0, ∀ (ν : Measure ℂ) (σ : ℂ → ℂ) (L : Set ℂ),
      IsFiniteMeasure ν → IsCompact L → ν Lᶜ = 0 → Measurable σ → (∀ z, ‖σ z‖ = 1) →
      (∀ x : ℝ, ∀ r : ℝ, 0 < r →
        (ν.withDensity fun z ↦ ENNReal.ofReal (Real.exp (-φ z))) (ball (x : ℂ) r) ≤
          K * ENNReal.ofReal r) →
      ∃ u : ℂ → ℂ, IsWeakDbarSolMeasure u ν σ ∧ DifferentiableOn ℂ u Lᶜ ∧
        Filter.Tendsto (fun z ↦ ‖u z‖ * Real.exp (-φ z)) (Filter.cocompact ℂ) (nhds 0) ∧
        ∀ x : ℝ, (x : ℂ) ∉ L →
          ENNReal.ofReal (‖u x‖ * Real.exp (-φ x)) ≤
            C * (1 + ∫⁻ z in ball (x : ℂ) 1,
              ENNReal.ofReal (Real.exp (-φ z) / ‖(x : ℂ) - z‖) ∂ν) := by
  -- the multipliers for `φ - α|Im z|` (M13), with `α = α₀ > 0`
  obtain ⟨α, hα, hmult⟩ := lineMultipliers φ μ hφ hd hm
  obtain ⟨f, ε, Cu, hε, hCu, hfd, -, -, hup, hcover, hlowall⟩ := hmult α hα.le le_rfl
  obtain ⟨c, hc, hlow⟩ := hlowall ε hε
  have hφc : Continuous φ := continuousOn_univ.1 hφ.continuousOn
  -- the partition `ℂ = G ⊔ Gᶜ`, with `f i` bounded below on the `i`-th piece
  set G : Set ℂ := {z | ∀ x : ℝ, f 0 x = 0 → ε * massRadiusLine μ x ≤ ‖z - x‖} with hG
  set Ω : Fin 2 → Set ℂ := ![G, Gᶜ] with hΩ
  have hGm : MeasurableSet G := (isClosed_setOf_forall_zero_le (f 0) μ ε).measurableSet
  have hΩm : ∀ i, MeasurableSet (Ω i) := measurableSet_fin_two_partition hGm
  have hΩlow : ∀ i, ∀ z ∈ Ω i, c * Real.exp (φ z - α * |z.im|) ≤ ‖f i z‖ := by
    intro i z hz
    fin_cases i
    · exact hlow 0 z hz
    · obtain ⟨j, hj⟩ := hcover z
      fin_cases j
      · exact absurd hj hz
      · exact hlow 1 z hj
  have hf0 : ∀ i, ∀ z ∈ Ω i, f i z ≠ 0 := fun i z hz h ↦ by
    have h1 := hΩlow i z hz
    rw [h, norm_zero] at h1
    exact absurd h1 (not_le.2 (by positivity))
  have hfu : ∀ i z, ‖f i z‖ * Real.exp (-φ z) ≤ Cu * Real.exp (-α * |z.im|) := by
    intro i z
    calc ‖f i z‖ * Real.exp (-φ z) ≤ Cu * Real.exp (φ z - α * |z.im|) * Real.exp (-φ z) :=
          mul_le_mul_of_nonneg_right (hup i z) (Real.exp_pos _).le
      _ = Cu * Real.exp (-α * |z.im|) := by
          rw [mul_assoc, ← Real.exp_add]; ring_nf
  -- the Ortega-Cerdà–Seip constant for the weight `α|Im z|` and Carleson constant `c⁻¹ K`
  obtain ⟨CO, hCO⟩ := hOCS α hα ((c⁻¹).toNNReal * K)
  set m : ℝ := c⁻¹ * Real.exp α with hm_def
  refine ⟨2 * Cu.toNNReal * CO * (1 + m.toNNReal), fun ν σ L hν hL hνL hσ hσ1 hcar ↦ ?_⟩
  have := hν
  have hfin : ∀ i, IsFiniteMeasure (divMeasure ν (Ω i) (f i)) := fun i ↦
    isFiniteMeasure_divMeasure hL hνL (g := fun z ↦ c * Real.exp (φ z - α * |z.im|))
      (by fun_prop) (hΩlow i) (fun z ↦ by positivity)
  have hex : ∀ i, ∃ v : ℂ → ℂ,
      IsWeakDbarSolMeasure v (divMeasure ν (Ω i) (f i)) (divPhase σ (f i)) ∧
      DifferentiableOn ℂ v Lᶜ ∧
      Filter.Tendsto (fun z ↦ ‖v z‖ * Real.exp (-α * |z.im|)) (Filter.cocompact ℂ) (nhds 0) ∧
      ∀ x : ℝ, (x : ℂ) ∉ L →
        ENNReal.ofReal ‖v x‖ ≤ CO * (1 + ∫⁻ z in ball (x : ℂ) 1,
          ENNReal.ofReal (1 / ‖(x : ℂ) - z‖) ∂divMeasure ν (Ω i) (f i)) := by
    intro i
    refine hCO _ _ L (hfin i) hL ?_ (measurable_divPhase hσ (hfd i).continuous)
      (norm_divPhase σ (f i) hσ1) ?_
    · refine withDensity_absolutelyContinuous _ _ ?_
      rw [Measure.restrict_apply hL.isClosed.measurableSet.compl]
      exact measure_mono_null inter_subset_left hνL
    · intro x r hr
      calc _ ≤ ENNReal.ofReal c⁻¹ *
              (ν.withDensity fun z ↦ ENNReal.ofReal (Real.exp (-φ z))) (ball (x : ℂ) r) :=
            divMeasure_withDensity_le (hΩm i) (hfd i).continuous hφc hc (hΩlow i) _
              measurableSet_ball
        _ ≤ ENNReal.ofReal c⁻¹ * (K * ENNReal.ofReal r) := by gcongr; exact hcar x r hr
        _ = ((c⁻¹.toNNReal * K : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal r := by
            rw [ENNReal.coe_mul, mul_assoc]; rfl
  choose v hv1 hv2 hv3 hv4 using hex
  refine ⟨fun z ↦ ∑ i, f i z * v i z,
    isWeakDbarSolMeasure_sum_mul hσ hσ1 Ω hΩm (pairwise_disjoint_fin_two_partition G)
      (iUnion_fin_two_partition G) f hfd hf0 hfin v hv1, ?_, ?_, ?_⟩
  · exact DifferentiableOn.fun_sum fun i _ ↦ (hfd i).differentiableOn.mul (hv2 i)
  · -- decay: `‖u‖ e^{-φ} ≤ Σ C_up ‖v_i‖ e^{-α|y|} → 0`
    have hlim : Filter.Tendsto (fun z ↦ ∑ i, Cu * (‖v i z‖ * Real.exp (-α * |z.im|)))
        (Filter.cocompact ℂ) (nhds 0) := by
      simpa using tendsto_finsetSum (Finset.univ : Finset (Fin 2))
        fun i _ ↦ (hv3 i).const_mul Cu
    exact squeeze_zero (fun z ↦ by positivity) (norm_sum_mul_mul_exp_le hfu) hlim
  · -- the pointwise bound at real `x ∉ L`
    intro x hx
    set J := ∫⁻ z in ball (x : ℂ) 1, ENNReal.ofReal (Real.exp (-φ z) / ‖(x : ℂ) - z‖) ∂ν
    have hJ : ∀ i, ∫⁻ z in ball (x : ℂ) 1, ENNReal.ofReal (1 / ‖(x : ℂ) - z‖)
        ∂divMeasure ν (Ω i) (f i) ≤ ENNReal.ofReal m * J := fun i ↦
      lintegral_ball_divMeasure_le (hΩm i) (hfd i).continuous hφc hc hα.le (hΩlow i) x
    have h1 : ENNReal.ofReal (‖∑ i, f i x * v i x‖ * Real.exp (-φ x)) ≤
        ∑ i, ENNReal.ofReal Cu * ENNReal.ofReal ‖v i x‖ := by
      have h2 := norm_sum_mul_mul_exp_le (v := v) hfu (x : ℂ)
      simp only [Complex.ofReal_im, abs_zero, mul_zero, Real.exp_zero, mul_one] at h2
      refine (ENNReal.ofReal_le_ofReal h2).trans (le_of_eq ?_)
      rw [ENNReal.ofReal_sum_of_nonneg fun i _ ↦ by positivity]
      exact Finset.sum_congr rfl fun i _ ↦ ENNReal.ofReal_mul hCu.le
    calc ENNReal.ofReal (‖∑ i, f i x * v i x‖ * Real.exp (-φ x))
        ≤ ∑ i, ENNReal.ofReal Cu * ENNReal.ofReal ‖v i x‖ := h1
      _ ≤ ∑ _i : Fin 2, ENNReal.ofReal Cu * (CO * (1 + ENNReal.ofReal m * J)) := by
          gcongr with i
          exact (hv4 i x hx).trans (by gcongr; exact hJ i)
      _ = 2 * ENNReal.ofReal Cu * CO * (1 + ENNReal.ofReal m * J) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; push_cast; ring
      _ ≤ 2 * ENNReal.ofReal Cu * CO * ((1 + ENNReal.ofReal m) * (1 + J)) := by
          gcongr; exact one_add_mul_le_mul_one_add _ _
      _ = ((2 * Cu.toNNReal * CO * (1 + m.toNNReal) : ℝ≥0) : ℝ≥0∞) * (1 + J) := by
          push_cast; rw [ENNReal.ofReal, ENNReal.ofReal]; ring

/-! 14.4 the printed form, under a lower bound for `φ` on the strip `|Im z| < 1` -/
theorem theorem3_of_lowerBound (hOCS : TheoremOCS) (φ : ℂ → ℝ) (μ : Measure ℂ)
    (hφ : IsSubharmonicWeight univ φ μ) (hd : IsLocallyDoublingLine μ)
    (hm : ∃ r : ℝ, 0 < r ∧ ∀ x : ℝ, 1 < μ (lineInterval x r))
    (hlow : ∃ B : ℝ, ∀ z : ℂ, |z.im| < 1 → -B ≤ φ z) (K : ℝ≥0) :
    ∃ C : ℝ≥0, ∀ (ν : Measure ℂ) (σ : ℂ → ℂ) (L : Set ℂ),
      IsFiniteMeasure ν → IsCompact L → ν Lᶜ = 0 → Measurable σ → (∀ z, ‖σ z‖ = 1) →
      (∀ x : ℝ, ∀ r : ℝ, 0 < r →
        (ν.withDensity fun z ↦ ENNReal.ofReal (Real.exp (-φ z))) (ball (x : ℂ) r) ≤
          K * ENNReal.ofReal r) →
      ∃ u : ℂ → ℂ, IsWeakDbarSolMeasure u ν σ ∧ DifferentiableOn ℂ u Lᶜ ∧
        Filter.Tendsto (fun z ↦ ‖u z‖ * Real.exp (-φ z)) (Filter.cocompact ℂ) (nhds 0) ∧
        ∀ x : ℝ, (x : ℂ) ∉ L →
          ENNReal.ofReal (‖u x‖ * Real.exp (-φ x)) ≤
            C * (1 + ∫⁻ z in ball (x : ℂ) 1, ENNReal.ofReal (1 / ‖(x : ℂ) - z‖) ∂ν) := by
  obtain ⟨B, hB⟩ := hlow
  obtain ⟨C, hC⟩ := theorem3_weighted hOCS φ μ hφ hd hm K
  refine ⟨C * (1 + (Real.exp B).toNNReal), fun ν σ L hν hL hνL hσ hσ1 hcar ↦ ?_⟩
  obtain ⟨u, hu1, hu2, hu3, hu4⟩ := hC ν σ L hν hL hνL hσ hσ1 hcar
  refine ⟨u, hu1, hu2, hu3, fun x hx ↦ ?_⟩
  set I := ∫⁻ z in ball (x : ℂ) 1, ENNReal.ofReal (1 / ‖(x : ℂ) - z‖) ∂ν
  -- on `ball x 1`, `|Im z| < 1`, so `e^{-φ(z)} ≤ e^B`
  have hJ : ∫⁻ z in ball (x : ℂ) 1, ENNReal.ofReal (Real.exp (-φ z) / ‖(x : ℂ) - z‖) ∂ν ≤
      ENNReal.ofReal (Real.exp B) * I := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_mono' measurableSet_ball fun z hz ↦ ?_
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    refine ENNReal.ofReal_le_ofReal ?_
    have hy : |z.im| < 1 := by
      have := abs_im_le_norm (z - x)
      rw [sub_im, Complex.ofReal_im, sub_zero] at this
      have h2 : ‖z - x‖ < 1 := by rw [← dist_eq]; exact hz
      linarith
    have h3 : Real.exp (-φ z) ≤ Real.exp B := Real.exp_le_exp.2 (by linarith [hB z hy])
    rw [div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_right h3 (by positivity)
  calc ENNReal.ofReal (‖u x‖ * Real.exp (-φ x))
      ≤ C * (1 + ∫⁻ z in ball (x : ℂ) 1,
          ENNReal.ofReal (Real.exp (-φ z) / ‖(x : ℂ) - z‖) ∂ν) := hu4 x hx
    _ ≤ C * (1 + ENNReal.ofReal (Real.exp B) * I) := by gcongr
    _ ≤ C * ((1 + ENNReal.ofReal (Real.exp B)) * (1 + I)) := by
        gcongr; exact one_add_mul_le_mul_one_add _ _
    _ = ((C * (1 + (Real.exp B).toNNReal) : ℝ≥0) : ℝ≥0∞) * (1 + I) := by
        push_cast; rw [ENNReal.ofReal]; ring

/-! 14.5 the counterexample to the printed Theorem 3 (documentation; optional) -/
/-- `φ₀(z) = |Im z| + Re z · Im z`. -/
def cexWeight (z : ℂ) : ℝ := |z.im| + z.re * z.im
/-- `μ₀ = 2 · (Lebesgue measure on ℝ)`. -/
def cexMeasure : Measure ℂ := (2 : ℝ≥0∞) • (volume : Measure ℝ).map (fun t : ℝ ↦ (t : ℂ))

theorem measurableEmbedding_ofReal_complex : MeasurableEmbedding ((↑) : ℝ → ℂ) :=
  Complex.isometry_ofReal.isClosedEmbedding.measurableEmbedding

theorem cexMeasure_apply (s : Set ℂ) : cexMeasure s = 2 * volume (((↑) : ℝ → ℂ) ⁻¹' s) := by
  rw [cexMeasure, Measure.smul_apply, measurableEmbedding_ofReal_complex.map_apply, smul_eq_mul]

theorem cexMeasure_lineInterval (x r : ℝ) :
    cexMeasure (lineInterval x r) = 2 * ENNReal.ofReal (2 * r) := by
  rw [cexMeasure_apply, lineInterval, preimage_image_eq _ Complex.ofReal_injective,
    Real.volume_Ioo]
  congr 2
  ring

/-- `|Im z|` is a subharmonic weight with Laplacian `2 dx` on `ℝ` (M13, 13.7). -/
theorem isSubharmonicWeight_abs_im : IsSubharmonicWeight univ (fun z : ℂ ↦ |z.im|) cexMeasure := by
  refine ⟨(continuous_abs.comp continuous_im).continuousOn, fun K _ hK ↦ ?_, by simp,
    fun χ hχ hc _ ↦ ?_⟩
  · rw [cexMeasure_apply]
    exact ENNReal.mul_lt_top (by simp)
      (Complex.isometry_ofReal.isClosedEmbedding.isCompact_preimage hK).measure_lt_top
  · rw [integral_abs_im_mul_laplacian χ hχ hc, cexMeasure, integral_smul_measure,
      measurableEmbedding_ofReal_complex.integral_map]
    simp

/-- `Re z · Im z = Im (z²/2)` is harmonic. -/
theorem harmonicOnNhd_re_mul_im :
    InnerProductSpace.HarmonicOnNhd (fun z : ℂ ↦ z.re * z.im) univ := by
  intro z _
  have hd : Differentiable ℂ fun w : ℂ ↦ w ^ 2 / 2 := by fun_prop
  have h := (hd.analyticAt z).harmonicAt_im
  have he : (fun w : ℂ ↦ (w ^ 2 / 2).im) = fun w : ℂ ↦ w.re * w.im := by
    ext w
    simp only [sq, Complex.div_ofNat_im, Complex.mul_im]
    ring
  rwa [he] at h

theorem cex_isSubharmonicWeight : IsSubharmonicWeight univ cexWeight cexMeasure :=
  isSubharmonicWeight_abs_im.add_harmonic isOpen_univ harmonicOnNhd_re_mul_im

theorem cex_doubling : IsLocallyDoublingLine cexMeasure := by
  refine ⟨?_, 2, fun x r hr _ ↦ ?_⟩
  · have : ((↑) : ℝ → ℂ) ⁻¹' {z : ℂ | z.im ≠ 0} = ∅ := by ext t; simp
    rw [cexMeasure_apply, this, measure_empty, mul_zero]
  · rw [cexMeasure_lineInterval, cexMeasure_lineInterval,
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
    exact le_of_eq (by push_cast; rfl)

theorem cex_mass : ∃ r : ℝ, 0 < r ∧ ∀ x : ℝ, 1 < cexMeasure (lineInterval x r) := by
  refine ⟨1, one_pos, fun x ↦ ?_⟩
  rw [cexMeasure_lineInterval, mul_one, ENNReal.ofReal_ofNat]
  norm_num

/-! 14.6 analytic tools for `not_theorem3_printed` (Phragmén–Lindelöf replaces Bernstein) -/

/-- **Half-plane step.** For an entire `G` with `‖G z‖ e^{-|Im z|} → 0` and `‖G‖ ≤ M` on `ℝ`,
and `ζ = ±i`: `‖G (ζ w) e^{-w}‖ ≤ M` for `Re w ≥ 0` (Phragmén–Lindelöf in the right half-plane). -/
theorem norm_mul_exp_neg_le_of_entire {G : ℂ → ℂ} (hG : Differentiable ℂ G) {M : ℝ}
    (hM : ∀ x : ℝ, ‖G x‖ ≤ M)
    (hdec : Filter.Tendsto (fun z ↦ ‖G z‖ * Real.exp (-|z.im|)) (Filter.cocompact ℂ) (nhds 0))
    {ζ : ℂ} (hζ : ζ = I ∨ ζ = -I) {w : ℂ} (hw : 0 ≤ w.re) :
    ‖G (ζ * w) * Complex.exp (-w)‖ ≤ M := by
  set F : ℂ → ℂ := fun w ↦ G (ζ * w) * Complex.exp (-w) with hF
  have hζn : ‖ζ‖ = 1 := by rcases hζ with rfl | rfl <;> simp
  have hζim : ∀ w : ℂ, |(ζ * w).im| = |w.re| := by
    intro w; rcases hζ with rfl | rfl <;> simp
  have hFn : ∀ w : ℂ, 0 ≤ w.re → ‖F w‖ = ‖G (ζ * w)‖ * Real.exp (-|(ζ * w).im|) := by
    intro w hw
    rw [hF, norm_mul, Complex.norm_exp, neg_re, hζim, abs_of_nonneg hw]
  have hFd : Differentiable ℂ F :=
    (hG.comp (differentiable_const _ |>.mul differentiable_id)).mul
      (Complex.differentiable_exp.comp differentiable_neg)
  -- `w ↦ ζ w` maps `cobounded` to `cobounded`
  have hζc : Filter.Tendsto (fun w : ℂ ↦ ζ * w) (Bornology.cobounded ℂ) (Bornology.cobounded ℂ) := by
    rw [← tendsto_norm_atTop_iff_cobounded]
    simpa [norm_mul, hζn] using tendsto_norm_cobounded_atTop (E := ℂ)
  have hlim : Filter.Tendsto F (Bornology.cobounded ℂ ⊓ Filter.principal {z | 0 < z.re})
      (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have h1 : Filter.Tendsto (fun w ↦ ‖G (ζ * w)‖ * Real.exp (-|(ζ * w).im|))
        (Bornology.cobounded ℂ) (nhds 0) := by
      rw [Metric.cobounded_eq_cocompact] at hζc ⊢
      exact hdec.comp hζc
    refine (h1.mono_left inf_le_left).congr' ?_
    filter_upwards [Filter.mem_inf_of_right (Filter.mem_principal_self _)] with w hw
    exact (hFn w (le_of_lt hw)).symm
  have hreal : Filter.Tendsto (fun x : ℝ ↦ F x) Filter.atTop (nhds 0) := by
    refine hlim.comp (Filter.tendsto_inf.2 ⟨?_, Filter.tendsto_principal.2 ?_⟩)
    · rw [← tendsto_norm_atTop_iff_cobounded]
      simpa using Filter.tendsto_abs_atTop_atTop
    · filter_upwards [Filter.eventually_gt_atTop 0] with x hx
      simpa using hx
  have him : ∀ x : ℝ, ‖F (x * I)‖ ≤ M := by
    intro x
    have hr : ζ * (x * I) = ((if ζ = I then -x else x : ℝ) : ℂ) := by
      rcases hζ with rfl | rfl
      · simp only [ite_true]; push_cast; ring_nf; simp
      · have : (-I : ℂ) ≠ I := by
          intro h; have := congrArg Complex.im h; simp at this; norm_num at this
        simp only [this, ite_false]; ring_nf; simp
    show ‖G (ζ * (x * I)) * Complex.exp (-(x * I))‖ ≤ M
    rw [hr, norm_mul, Complex.norm_exp]
    simp only [neg_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      neg_zero, Real.exp_zero]
    exact hM _
  show ‖F w‖ ≤ M
  refine PhragmenLindelof.right_half_plane_of_tendsto_zero_on_real hFd.diffContOnCl
    ⟨0, by norm_num, 0, ?_⟩ hreal him hw
  simp only [zero_mul, Real.exp_zero]
  exact hlim.isBigO_one ℝ

/-- **Phragmén–Lindelöf on `ℂ`.** An entire `G` with `‖G z‖ e^{-|Im z|} → 0` at `∞` and
`‖G‖ ≤ M` on `ℝ` satisfies `‖G z‖ ≤ M e^{|Im z|}`. -/
theorem norm_le_mul_exp_abs_im_of_entire {G : ℂ → ℂ} (hG : Differentiable ℂ G) {M : ℝ}
    (hM : ∀ x : ℝ, ‖G x‖ ≤ M)
    (hdec : Filter.Tendsto (fun z ↦ ‖G z‖ * Real.exp (-|z.im|)) (Filter.cocompact ℂ) (nhds 0))
    (z : ℂ) : ‖G z‖ ≤ M * Real.exp |z.im| := by
  rcases le_or_gt 0 z.im with h | h
  · have := norm_mul_exp_neg_le_of_entire hG hM hdec (Or.inl rfl) (w := -I * z)
      (by simpa using h)
    have e : I * (-I * z) = z := by ring_nf; simp
    rw [e, norm_mul, Complex.norm_exp] at this
    simp only [mul_re, I_re, I_im, zero_mul, zero_sub, neg_mul, one_mul, neg_neg] at this
    rw [abs_of_nonneg h]
    have hpos := Real.exp_pos z.im
    calc ‖G z‖ = ‖G z‖ * Real.exp (-z.im) * Real.exp z.im := by
          rw [mul_assoc, ← Real.exp_add]; simp
      _ ≤ M * Real.exp z.im := by gcongr
  · have := norm_mul_exp_neg_le_of_entire hG hM hdec (Or.inr rfl) (w := I * z)
      (by simpa using h.le)
    have e : -I * (I * z) = z := by ring_nf; simp
    rw [e, norm_mul, Complex.norm_exp] at this
    simp only [neg_re, mul_re, I_re, I_im, zero_mul, one_mul, zero_sub, neg_neg] at this
    rw [abs_of_neg h]
    calc ‖G z‖ = ‖G z‖ * Real.exp z.im * Real.exp (-z.im) := by
          rw [mul_assoc, ← Real.exp_add]; simp
      _ ≤ M * Real.exp (-z.im) := by gcongr

/-- **Cauchy estimate + mean value theorem** on `ℝ`, from `‖G z‖ ≤ M e^{|Im z|}`. -/
theorem norm_sub_le_of_norm_le_mul_exp {G : ℂ → ℂ} (hG : Differentiable ℂ G) {M : ℝ}
    (hb : ∀ z, ‖G z‖ ≤ M * Real.exp |z.im|) (a b : ℝ) :
    ‖G b - G a‖ ≤ M * Real.exp 1 * |b - a| := by
  have hM : 0 ≤ M := by
    have := hb 0; simp only [zero_im, abs_zero, Real.exp_zero, mul_one] at this
    exact (norm_nonneg _).trans this
  have hder : ∀ z : ℂ, z.im = 0 → ‖deriv G z‖ ≤ M * Real.exp 1 := by
    intro z hz
    have := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le one_pos hG.diffContOnCl
      (C := M * Real.exp 1) fun y hy ↦ by
        refine (hb y).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hM)
        have h1 := abs_im_le_norm (y - z)
        rw [sub_im, hz, sub_zero, ← dist_eq, mem_sphere.1 hy] at h1
        exact h1
    simpa using this
  have := Convex.norm_image_sub_le_of_norm_deriv_le (s := segment ℝ (a : ℂ) b)
    (fun z _ ↦ hG z) (fun z hz ↦ hder z ?_) (convex_segment _ _)
    (left_mem_segment ℝ _ _) (right_mem_segment ℝ _ _)
  · rwa [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at this
  · rw [segment_eq_image] at hz
    obtain ⟨t, -, rfl⟩ := hz
    simp

/-- The conclusion of the printed Theorem 3 fails for `(φ₀, μ₀, K = 2)`; hence `theorem3` in
`comparator/statements.lean` is equivalent to `¬ TheoremOCS`. -/
theorem not_theorem3_printed :
    ¬ ∃ C : ℝ≥0, ∀ (ν : Measure ℂ) (σ : ℂ → ℂ) (L : Set ℂ),
      IsFiniteMeasure ν → IsCompact L → ν Lᶜ = 0 → Measurable σ → (∀ z, ‖σ z‖ = 1) →
      (∀ x : ℝ, ∀ r : ℝ, 0 < r →
        (ν.withDensity fun z ↦ ENNReal.ofReal (Real.exp (-cexWeight z))) (ball (x : ℂ) r) ≤
          (2 : ℝ≥0) * ENNReal.ofReal r) →
      ∃ u : ℂ → ℂ, IsWeakDbarSolMeasure u ν σ ∧ DifferentiableOn ℂ u Lᶜ ∧
        Filter.Tendsto (fun z ↦ ‖u z‖ * Real.exp (-cexWeight z)) (Filter.cocompact ℂ) (nhds 0) ∧
        ∀ x : ℝ, (x : ℂ) ∉ L →
          ENNReal.ofReal (‖u x‖ * Real.exp (-cexWeight x)) ≤
            C * (1 + ∫⁻ z in ball (x : ℂ) 1, ENNReal.ofReal (1 / ‖(x : ℂ) - z‖) ∂ν) := sorry

/-! ### The printed Theorem 3 (comparator statement `theorem3`): FALSE, kept out of the build

The printed statement (paper, p. 358), as in `comparator/statements.lean`, is false: for the
weight `cexWeight` and `cexMeasure` (§4 of `blueprint/M14_Theorem3.md`) its conclusion fails
(`not_theorem3_printed`), so `theorem3` is equivalent to `¬ TheoremOCS`.  The corrected
statement is `theorem3_weighted` above (weight `e^{-φ}` inside the integral).  The printed form
is recorded here as a comment only, so that no known-false `sorry` theorem is in the build:

```
/-- **Theorem 3** (paper, p. 358), conditional on the Ortega-Cerdà–Seip theorem [OCS99]
(`TheoremOCS`), which the paper uses as a black box. -/
theorem theorem3 (hOCS : TheoremOCS) (φ : ℂ → ℝ) (μ : Measure ℂ)
    (hφ : IsSubharmonicWeight univ φ μ) (hd : IsLocallyDoublingLine μ)
    (hm : ∃ r : ℝ, 0 < r ∧ ∀ x : ℝ, 1 < μ (lineInterval x r)) (K : ℝ≥0) :
    ∃ C : ℝ≥0, ∀ (ν : Measure ℂ) (σ : ℂ → ℂ) (L : Set ℂ),
      IsFiniteMeasure ν → IsCompact L → ν Lᶜ = 0 → Measurable σ → (∀ z, ‖σ z‖ = 1) →
      (∀ x : ℝ, ∀ r : ℝ, 0 < r →
        (ν.withDensity fun z ↦ ENNReal.ofReal (Real.exp (-φ z))) (ball (x : ℂ) r) ≤
          K * ENNReal.ofReal r) →
      ∃ u : ℂ → ℂ, IsWeakDbarSolMeasure u ν σ ∧ DifferentiableOn ℂ u Lᶜ ∧
        Filter.Tendsto (fun z ↦ ‖u z‖ * Real.exp (-φ z)) (Filter.cocompact ℂ) (nhds 0) ∧
        ∀ x : ℝ, (x : ℂ) ∉ L →
          ENNReal.ofReal (‖u x‖ * Real.exp (-φ x)) ≤
            C * (1 + ∫⁻ z in ball (x : ℂ) 1, ENNReal.ofReal (1 / ‖(x : ℂ) - z‖) ∂ν) := sorry
```
-/

end OC
