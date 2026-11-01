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

/-- The normalised Cauchy kernel `1/(π(z - w))`, the fundamental solution of `∂̄`. -/
def cexPole (w z : ℂ) : ℂ := (Real.pi : ℂ)⁻¹ * (z - w)⁻¹

theorem cexPole_mul_dbar_eq {α : ℂ → ℂ} (w z : ℂ) :
    cexPole w z * dbar α z = -(Real.pi : ℂ)⁻¹ * (dbar α z / (w - z)) := by
  rw [cexPole, ← neg_sub w z, inv_neg]
  ring

theorem integrable_cexPole_mul_dbar {α : ℂ → ℂ} (hα : ContDiff ℝ 1 α) (hc : HasCompactSupport α)
    (w : ℂ) : Integrable (fun z ↦ cexPole w z * dbar α z) := by
  simp_rw [cexPole_mul_dbar_eq]
  exact (integrable_div_sub (continuous_dbar hα) (hasCompactSupport_dbar hc) w).const_mul _

/-- `∂̄ (1/(π(z - w))) = δ_w` weakly: `∫ ∂̄α /(π(z - w)) = -α(w)`. -/
theorem integral_cexPole_mul_dbar {α : ℂ → ℂ} (hα : ContDiff ℝ 1 α) (hc : HasCompactSupport α)
    (w : ℂ) : ∫ z, cexPole w z * dbar α z = -α w := by
  simp_rw [cexPole_mul_dbar_eq]
  rw [integral_const_mul, integral_dbar_div_eq hα hc w]
  have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp

theorem locallyIntegrable_const_mul_cexPole (c w : ℂ) :
    LocallyIntegrable (fun z ↦ c * cexPole w z) := by
  have h := (locallyIntegrable_inv_sub w).continuous_mul
    (continuous_const (y := c * (Real.pi : ℂ)⁻¹))
  refine h.congr (Filter.Eventually.of_forall fun z ↦ ?_)
  simp only [cexPole]; ring

/-- **Point masses.** If `∂̄u = σ ν` with `ν = Σ m_k δ_{w_k}` and `E` is entire, then
`E u - Σ_k E(w_k) σ(w_k) m_k / (π(z - w_k))` is weakly holomorphic on `ℂ`. -/
theorem isWeakDbarSol_mul_sub_poles {ι : Type*} [Fintype ι] (w : ι → ℂ) (m : ι → ℝ)
    (hm : ∀ k, 0 ≤ m k) {σ E u : ℂ → ℂ} (hE : Differentiable ℂ E)
    (hu : IsWeakDbarSolMeasure u (∑ k, ENNReal.ofReal (m k) • Measure.dirac (w k)) σ) :
    IsWeakDbarSol univ
      (fun z ↦ E z * u z - ∑ k, E (w k) * σ (w k) * (m k : ℂ) * cexPole (w k) z) 0 := by
  refine ⟨?_, locallyIntegrable_zero.locallyIntegrableOn _, fun α hα hc _ ↦ ?_⟩
  · rw [locallyIntegrableOn_univ]
    exact (hu.1.continuous_mul hE.continuous).sub
      (locallyIntegrable_finsetSum _ fun k _ ↦ locallyIntegrable_const_mul_cexPole _ _)
  have hα1 := contDiff_one_of_top hα
  -- `∂̄(Eα) = E ∂̄α`
  have hβ : ContDiff ℝ (⊤ : ℕ∞) (fun z ↦ E z * α z) := (hE.contDiff.restrict_scalars ℝ).mul hα
  have hβc : HasCompactSupport (fun z ↦ E z * α z) := hc.mul_left
  have hdβ : ∀ z, dbar (fun z ↦ E z * α z) z = E z * dbar α z := by
    intro z
    rw [dbar_mul ((hE z).restrictScalars ℝ) (hα1.differentiable one_ne_zero z),
      dbar_eq_zero_of_differentiableAt (hE z), zero_mul, zero_add]
  have h1 := hu.2 _ hβ hβc
  simp_rw [hdβ] at h1
  -- the integral against `ν`
  have hν : ∫ z, E z * α z * σ z ∂(∑ k, ENNReal.ofReal (m k) • Measure.dirac (w k)) =
      ∑ k, (m k : ℂ) * (E (w k) * α (w k) * σ (w k)) := by
    rw [integral_finsetSum_measure fun k _ ↦
      (integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hm k), Complex.real_smul]
  have hint1 : Integrable (fun z ↦ u z * (E z * dbar α z)) :=
    integrable_mul_of_locallyIntegrableOn (hu.1.locallyIntegrableOn univ)
      (hE.continuous.mul (continuous_dbar hα1)) ((hasCompactSupport_dbar hc).mul_left)
      (subset_univ _)
  have hint2 : ∀ k, Integrable (fun z ↦ E (w k) * σ (w k) * (m k : ℂ) * cexPole (w k) z *
      dbar α z) := fun k ↦
    ((integrable_cexPole_mul_dbar hα1 hc (w k)).const_mul (E (w k) * σ (w k) * (m k : ℂ))).congr
      (Filter.Eventually.of_forall fun z ↦ by ring)
  calc ∫ z, (E z * u z - ∑ k, E (w k) * σ (w k) * (m k : ℂ) * cexPole (w k) z) * dbar α z
      = ∫ z, (u z * (E z * dbar α z) -
          ∑ k, E (w k) * σ (w k) * (m k : ℂ) * cexPole (w k) z * dbar α z) := by
        congr 1; ext z; rw [sub_mul, Finset.sum_mul]; ring
    _ = (∫ z, u z * (E z * dbar α z)) -
          ∑ k, ∫ z, E (w k) * σ (w k) * (m k : ℂ) * cexPole (w k) z * dbar α z := by
        rw [integral_sub hint1 (integrable_finsetSum _ fun k _ ↦ hint2 k),
          integral_finsetSum _ fun k _ ↦ hint2 k]
    _ = -∑ k, (m k : ℂ) * (E (w k) * α (w k) * σ (w k)) -
          ∑ k, E (w k) * σ (w k) * (m k : ℂ) * -α (w k) := by
        rw [h1, hν]
        congr 1
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        simp_rw [mul_assoc]
        rw [integral_const_mul, integral_const_mul, integral_const_mul,
          integral_cexPole_mul_dbar hα1 hc]
    _ = -∫ z, (0 : ℂ → ℂ) z * α z := by
        simp only [Pi.zero_apply, zero_mul, integral_zero, neg_zero]
        rw [neg_sub_left, ← Finset.sum_add_distrib, neg_eq_zero]
        exact Finset.sum_eq_zero fun k _ ↦ by ring

/-- Weak holomorphy on `ℂ` plus continuity off a closed set `L`: an entire representative that
agrees with `g` on `Lᶜ` (Weyl). -/
theorem exists_entire_eqOn_compl {g : ℂ → ℂ} {L : Set ℂ} (hL : IsClosed L)
    (hg : IsWeakDbarSol univ g 0) (hgc : ContinuousOn g Lᶜ) :
    ∃ G : ℂ → ℂ, Differentiable ℂ G ∧ EqOn g G Lᶜ := by
  obtain ⟨G, hGd, hae⟩ := hg.exists_holomorphic isOpen_univ
  have hGd' : Differentiable ℂ G := fun z ↦ (hGd z trivial).differentiableAt Filter.univ_mem
  refine ⟨G, hGd', ?_⟩
  rw [Measure.restrict_univ] at hae
  exact Measure.eqOn_open_of_ae_eq (ae_restrict_of_ae hae) hL.isOpen_compl hgc
    hGd'.continuous.continuousOn

/-- A dyadic tail bound: `Σ_{k ∈ S, a 2^{-k} < r} a 2^{-k} ≤ 2r`. -/
theorem sum_filter_geom_le (S : Finset ℕ) {a r : ℝ} (ha : 0 ≤ a) (hr : 0 < r) :
    ∑ k ∈ S.filter (fun k ↦ a * (1 / 2 : ℝ) ^ k < r), a * (1 / 2 : ℝ) ^ k ≤ 2 * r := by
  set T := S.filter (fun k ↦ a * (1 / 2 : ℝ) ^ k < r) with hTdef
  rcases T.eq_empty_or_nonempty with hT | hT
  · rw [hT, Finset.sum_empty]; positivity
  set k₀ := T.min' hT
  have hk₀ : a * (1 / 2 : ℝ) ^ k₀ < r := (Finset.mem_filter.1 (T.min'_mem hT)).2
  set K := T.max' hT + 1
  have hsub : T ⊆ Finset.Ico k₀ K := fun k hk ↦
    Finset.mem_Ico.2 ⟨T.min'_le k hk, Nat.lt_succ_of_le (T.le_max' k hk)⟩
  calc ∑ k ∈ T, a * (1 / 2 : ℝ) ^ k ≤ ∑ k ∈ Finset.Ico k₀ K, a * (1 / 2 : ℝ) ^ k :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ ↦ by positivity
    _ = ∑ i ∈ Finset.range (K - k₀), a * (1 / 2 : ℝ) ^ (k₀ + i) :=
        Finset.sum_Ico_eq_sum_range _ _ _
    _ = a * (1 / 2 : ℝ) ^ k₀ * ∑ i ∈ Finset.range (K - k₀), (1 / 2 : ℝ) ^ i := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ ↦ by rw [pow_add]; ring
    _ ≤ a * (1 / 2 : ℝ) ^ k₀ * 2 :=
        mul_le_mul_of_nonneg_left (sum_geometric_two_le _) (by positivity)
    _ ≤ 2 * r := by linarith

/-! The data of the counterexample: `N` point masses at `w_k = x₀ - i 2^{-(k+6)}`. -/

/-- The heights `s_k = 2^{-(k+6)}`. -/
def cexS (k : ℕ) : ℝ := (1 / 2 : ℝ) ^ 6 * (1 / 2 : ℝ) ^ k
/-- The abscissa `x₀ = 1 + N 2^{N+6}`. -/
def cexX0 (N : ℕ) : ℝ := 1 + N * 2 ^ (N + 6)
/-- The points `w_k = x₀ - i s_k`. -/
def cexW (N k : ℕ) : ℂ := (cexX0 N : ℂ) - (cexS k : ℂ) * I
/-- The masses `m_k = s_k e^{φ₀(w_k)}`, so that `e^{-φ₀} m_k = s_k`. -/
def cexM (N k : ℕ) : ℝ := cexS k * Real.exp (cexWeight (cexW N k))
/-- `ν = Σ_k m_k δ_{w_k}`. -/
def cexNu (N : ℕ) : Measure ℂ :=
  ∑ k : Fin N, ENNReal.ofReal (cexM N k) • Measure.dirac (cexW N k)
/-- The support `L = {w_k}`. -/
def cexL (N : ℕ) : Set ℂ := Set.range fun k : Fin N ↦ cexW N k
/-- `H(z) = -(i/2) z²`, with `Re H = Re z · Im z`. -/
def cexH (z : ℂ) : ℂ := -(I / 2) * z ^ 2
/-- The phase `σ = e^{i Im H}`. -/
def cexSigma (z : ℂ) : ℂ := Complex.exp (((cexH z).im : ℂ) * I)
/-- The entire factor `E = e^{-H}`. -/
def cexE (z : ℂ) : ℂ := Complex.exp (-cexH z)

theorem cexS_pos (k : ℕ) : 0 < cexS k := by unfold cexS; positivity

theorem cexS_le (k : ℕ) : cexS k ≤ 1 / 64 := by
  unfold cexS
  have : (1 / 2 : ℝ) ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  nlinarith

theorem cexH_re (z : ℂ) : (cexH z).re = z.re * z.im := by
  simp [cexH, sq]; ring

theorem cexWeight_eq (z : ℂ) : cexWeight z = |z.im| + (cexH z).re := by
  rw [cexH_re]; rfl

theorem norm_cexE (z : ℂ) : ‖cexE z‖ = Real.exp (-(z.re * z.im)) := by
  rw [cexE, Complex.norm_exp, neg_re, cexH_re]

theorem norm_cexSigma (z : ℂ) : ‖cexSigma z‖ = 1 := Complex.norm_exp_ofReal_mul_I _

theorem continuous_cexH : Continuous cexH := by unfold cexH; fun_prop

theorem continuous_cexSigma : Continuous cexSigma := by
  unfold cexSigma
  exact Complex.continuous_exp.comp
    ((Complex.continuous_ofReal.comp (continuous_im.comp continuous_cexH)).mul continuous_const)

theorem differentiable_cexE : Differentiable ℂ cexE := by unfold cexE cexH; fun_prop

theorem cexE_mul_cexSigma (z : ℂ) :
    cexE z * cexSigma z = (Real.exp (-(z.re * z.im)) : ℂ) := by
  rw [cexE, cexSigma, ← Complex.exp_add, Complex.ofReal_exp, ← cexH_re]
  congr 1
  apply Complex.ext <;> simp

theorem cexW_re (N k : ℕ) : (cexW N k).re = cexX0 N := by simp [cexW]
theorem cexW_im (N k : ℕ) : (cexW N k).im = -cexS k := by simp [cexW]

theorem cexWeight_cexW (N k : ℕ) : cexWeight (cexW N k) = cexS k * (1 - cexX0 N) := by
  rw [cexWeight, cexW_re, cexW_im, abs_neg, abs_of_pos (cexS_pos k)]; ring

theorem cexM_pos (N k : ℕ) : 0 < cexM N k := by unfold cexM; have := cexS_pos k; positivity

/-- The residues `E(w_k) σ(w_k) m_k = s_k e^{s_k}` are real and positive. -/
theorem cexE_mul_cexSigma_mul_cexM (N k : ℕ) :
    cexE (cexW N k) * cexSigma (cexW N k) * (cexM N k : ℂ) =
      ((cexS k * Real.exp (cexS k) : ℝ) : ℂ) := by
  rw [cexE_mul_cexSigma, cexM, cexWeight_cexW, cexW_re, cexW_im, ← Complex.ofReal_mul]
  congr 1
  rw [mul_comm (Real.exp _), mul_assoc, ← Real.exp_add]
  congr 2; ring

theorem isFiniteMeasure_cexNu (N : ℕ) : IsFiniteMeasure (cexNu N) := by
  constructor
  simp only [cexNu, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (mem_univ _), smul_eq_mul, mul_one]
  exact ENNReal.sum_lt_top.2 fun k _ ↦ ENNReal.ofReal_lt_top

theorem isCompact_cexL (N : ℕ) : IsCompact (cexL N) := (Set.finite_range _).isCompact

theorem cexNu_compl_cexL (N : ℕ) : cexNu N (cexL N)ᶜ = 0 := by
  have hm : MeasurableSet (cexL N)ᶜ := (isCompact_cexL N).isClosed.measurableSet.compl
  simp only [cexNu, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
    Measure.dirac_apply' _ hm, smul_eq_mul]
  refine Finset.sum_eq_zero fun k _ ↦ ?_
  rw [indicator_of_notMem (by simp [cexL]), mul_zero]

/-- `∫⁻ f dν = Σ_k m_k f(w_k)`. -/
theorem lintegral_cexNu (N : ℕ) (f : ℂ → ℝ≥0∞) :
    ∫⁻ z, f z ∂cexNu N = ∑ k : Fin N, ENNReal.ofReal (cexM N k) * f (cexW N k) := by
  rw [cexNu, lintegral_finsetSum_measure]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]

/-- **Carleson** for `e^{-φ₀} ν` with constant `2`. -/
theorem cexNu_carleson (N : ℕ) (x : ℝ) (r : ℝ) (hr : 0 < r) :
    ((cexNu N).withDensity fun z ↦ ENNReal.ofReal (Real.exp (-cexWeight z))) (ball (x : ℂ) r) ≤
      (2 : ℝ≥0) * ENNReal.ofReal r := by
  rw [withDensity_apply _ measurableSet_ball, ← lintegral_indicator measurableSet_ball,
    lintegral_cexNu]
  have hk : ∀ k : Fin N, ENNReal.ofReal (cexM N k) * (ball (x : ℂ) r).indicator
      (fun z ↦ ENNReal.ofReal (Real.exp (-cexWeight z))) (cexW N k) ≤
      ENNReal.ofReal (if (1 / 2 : ℝ) ^ 6 * (1 / 2 : ℝ) ^ (k : ℕ) < r then cexS k else 0) := by
    intro k
    by_cases hw : cexW N k ∈ ball (x : ℂ) r
    · rw [indicator_of_mem hw, ← ENNReal.ofReal_mul (cexM_pos N k).le]
      have hs : cexS k < r := by
        have h1 := abs_im_le_norm (cexW N k - x)
        rw [sub_im, Complex.ofReal_im, sub_zero, cexW_im, abs_neg, abs_of_pos (cexS_pos k),
          ← dist_eq] at h1
        exact h1.trans_lt hw
      have hs' : (1 / 2 : ℝ) ^ 6 * (1 / 2 : ℝ) ^ (k : ℕ) < r := by simpa [cexS] using hs
      simp only [hs', ↓reduceIte]
      rw [cexM, mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
    · rw [indicator_of_notMem hw, mul_zero]; exact zero_le
  calc ∑ k : Fin N, ENNReal.ofReal (cexM N k) * (ball (x : ℂ) r).indicator
        (fun z ↦ ENNReal.ofReal (Real.exp (-cexWeight z))) (cexW N k)
      ≤ ∑ k : Fin N, ENNReal.ofReal
          (if (1 / 2 : ℝ) ^ 6 * (1 / 2 : ℝ) ^ (k : ℕ) < r then cexS k else 0) :=
        Finset.sum_le_sum fun k _ ↦ hk k
    _ = ENNReal.ofReal (∑ k ∈ (Finset.range N).filter
          (fun k ↦ (1 / 2 : ℝ) ^ 6 * (1 / 2 : ℝ) ^ k < r), (1 / 2 : ℝ) ^ 6 * (1 / 2 : ℝ) ^ k) := by
        rw [← ENNReal.ofReal_sum_of_nonneg fun k _ ↦ by
          split_ifs <;> [exact (cexS_pos k).le; exact le_rfl]]
        congr 1
        rw [Finset.sum_filter, ← Fin.sum_univ_eq_sum_range
          (fun k ↦ if (1 / 2 : ℝ) ^ 6 * (1 / 2 : ℝ) ^ k < r then
            (1 / 2 : ℝ) ^ 6 * (1 / 2 : ℝ) ^ k else 0)]
        rfl
    _ ≤ ENNReal.ofReal (2 * r) :=
        ENNReal.ofReal_le_ofReal (sum_filter_geom_le _ (by positivity) hr)
    _ = (2 : ℝ≥0) * ENNReal.ofReal r := by
        rw [ENNReal.ofReal_mul (by norm_num)]; simp

/-- The right-hand side of the printed bound is at most `1` on `ℝ`. -/
theorem lintegral_cexNu_le_one (N : ℕ) (x : ℝ) :
    ∫⁻ z in ball (x : ℂ) 1, ENNReal.ofReal (1 / ‖(x : ℂ) - z‖) ∂cexNu N ≤ 1 := by
  refine (setLIntegral_le_lintegral _ _).trans ?_
  rw [lintegral_cexNu]
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp
  have hk : ∀ k : Fin N, ENNReal.ofReal (cexM N k) * ENNReal.ofReal (1 / ‖(x : ℂ) - cexW N k‖) ≤
      ENNReal.ofReal (1 / N) := by
    intro k
    rw [← ENNReal.ofReal_mul (cexM_pos N k).le]
    refine ENNReal.ofReal_le_ofReal ?_
    have hs := cexS_pos k
    have h1 : cexS k ≤ ‖(x : ℂ) - cexW N k‖ := by
      have := abs_im_le_norm ((x : ℂ) - cexW N k)
      rwa [sub_im, Complex.ofReal_im, zero_sub, cexW_im, neg_neg, abs_of_pos hs] at this
    have h2 : cexM N k * (1 / ‖(x : ℂ) - cexW N k‖) ≤ Real.exp (cexWeight (cexW N k)) := by
      calc cexM N k * (1 / ‖(x : ℂ) - cexW N k‖) ≤ cexM N k * (1 / cexS k) :=
            mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le hs h1) (cexM_pos N k).le
        _ = Real.exp (cexWeight (cexW N k)) := by rw [cexM]; field_simp
    refine h2.trans ?_
    -- `s_k (x₀ - 1) ≥ N`, and `e^{-N} ≤ 1/N`
    have hkN : (k : ℕ) ≤ N := k.isLt.le
    have h3 : (N : ℝ) ≤ cexS k * (cexX0 N - 1) := by
      rw [cexX0, cexS, add_sub_cancel_left]
      have h4 : (1 : ℝ) ≤ (1 / 2 : ℝ) ^ 6 * (1 / 2 : ℝ) ^ (k : ℕ) * 2 ^ (N + 6) := by
        have e : (2 : ℝ) ^ (N + 6) = 2 ^ 6 * 2 ^ (k : ℕ) * 2 ^ (N - k) := by
          rw [← pow_add, ← pow_add]; congr 1; omega
        rw [e, show (1 / 2 : ℝ) ^ 6 * (1 / 2 : ℝ) ^ (k : ℕ) * (2 ^ 6 * 2 ^ (k : ℕ) * 2 ^ (N - k)) =
          ((1 / 2 : ℝ) * 2) ^ 6 * ((1 / 2 : ℝ) * 2) ^ (k : ℕ) * 2 ^ (N - k) by
            rw [mul_pow, mul_pow]; ring]
        norm_num
        exact one_le_pow₀ (by norm_num)
      nlinarith [show (0 : ℝ) ≤ N from N.cast_nonneg]
    rw [cexWeight_cexW]
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    calc Real.exp (cexS k * (1 - cexX0 N)) ≤ Real.exp (-N) := Real.exp_le_exp.2 (by linarith)
      _ ≤ 1 / N := by
          rw [Real.exp_neg, ← one_div]
          exact one_div_le_one_div_of_le hNpos (by linarith [Real.add_one_le_exp (N : ℝ)])
  calc ∑ k : Fin N, ENNReal.ofReal (cexM N k) * ENNReal.ofReal (1 / ‖(x : ℂ) - cexW N k‖)
      ≤ ∑ _k : Fin N, ENNReal.ofReal (1 / N) := Finset.sum_le_sum fun k _ ↦ hk k
    _ = 1 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
        rw [mul_one_div_cancel (by exact_mod_cast hN.ne'), ENNReal.ofReal_one]

/-- The Cauchy transform `𝒞₀ = Σ_k s_k e^{s_k} / (π(z - w_k))` of `e^{-H} σ ν`. -/
def cexP (N : ℕ) (z : ℂ) : ℂ :=
  ∑ k : Fin N, ((cexS k * Real.exp (cexS k) : ℝ) : ℂ) * cexPole (cexW N k) z

theorem im_cexPole_sub (x₀ s τ : ℝ) (hs : 0 < s) (hτ : 0 < τ) :
    (cexPole ((x₀ : ℂ) - (s : ℂ) * I) x₀ - cexPole ((x₀ : ℂ) - (s : ℂ) * I) ((x₀ + τ : ℝ) : ℂ)).im =
      -(Real.pi⁻¹ * (1 / s - s / (τ ^ 2 + s ^ 2))) := by
  have e1 : (x₀ : ℂ) - ((x₀ : ℂ) - (s : ℂ) * I) = (s : ℂ) * I := by ring
  have e2 : ((x₀ + τ : ℝ) : ℂ) - ((x₀ : ℂ) - (s : ℂ) * I) = (τ : ℂ) + (s : ℂ) * I := by
    push_cast; ring
  rw [cexPole, cexPole, e1, e2, ← mul_sub, ← Complex.ofReal_inv, Complex.im_ofReal_mul,
    sub_im, Complex.inv_im, Complex.inv_im]
  simp only [mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero, add_im,
    Complex.normSq_apply, mul_re, sub_zero, zero_add, add_re]
  have hs' : s ≠ 0 := hs.ne'
  have h2 : τ ^ 2 + s ^ 2 ≠ 0 := by positivity
  field_simp
  ring

/-- **Oscillation of `𝒞₀`**: `|𝒞₀(x₀) - 𝒞₀(x₀ + 1/64)| ≥ N/(2π)`, because each pole
contributes `≥ 1/(2π)` to the imaginary part, all with the same sign. -/
theorem cexP_oscillation (N : ℕ) :
    (N : ℝ) / (2 * Real.pi) ≤ ‖cexP N (cexX0 N) - cexP N ((cexX0 N + 1 / 64 : ℝ) : ℂ)‖ := by
  set τ : ℝ := 1 / 64
  have hτ : (0 : ℝ) < τ := by norm_num
  have hπ := Real.pi_pos
  have hterm : ∀ k : Fin N, 1 / (2 * Real.pi) ≤
      -(((cexS k * Real.exp (cexS k) : ℝ) : ℂ) * (cexPole (cexW N k) (cexX0 N) -
        cexPole (cexW N k) ((cexX0 N + τ : ℝ) : ℂ))).im := by
    intro k
    have hs := cexS_pos k
    have hsτ : cexS k ≤ τ := cexS_le k
    rw [Complex.im_ofReal_mul, cexW, im_cexPole_sub _ _ _ hs hτ]
    -- `s e^s π⁻¹ (1/s - s/(τ²+s²)) ≥ π⁻¹ τ²/(τ²+s²) ≥ 1/(2π)`
    set s := cexS k
    have hX : 0 ≤ 1 / s - s / (τ ^ 2 + s ^ 2) := by
      rw [sub_nonneg]
      rw [div_le_div_iff₀ (by positivity) hs]
      nlinarith [sq_nonneg τ]
    have hes : s ≤ s * Real.exp s := le_mul_of_one_le_right hs.le (Real.one_le_exp hs.le)
    have h1 : s * (1 / s - s / (τ ^ 2 + s ^ 2)) = τ ^ 2 / (τ ^ 2 + s ^ 2) := by
      field_simp; ring
    have h2 : 1 / 2 ≤ τ ^ 2 / (τ ^ 2 + s ^ 2) := by
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]
      nlinarith
    calc 1 / (2 * Real.pi) = Real.pi⁻¹ * (1 / 2) := by field_simp
      _ ≤ Real.pi⁻¹ * (s * (1 / s - s / (τ ^ 2 + s ^ 2))) := by
          rw [h1]; exact mul_le_mul_of_nonneg_left h2 (by positivity)
      _ ≤ Real.pi⁻¹ * (s * Real.exp s * (1 / s - s / (τ ^ 2 + s ^ 2))) := by
          gcongr
      _ = -(s * Real.exp s * -(Real.pi⁻¹ * (1 / s - s / (τ ^ 2 + s ^ 2)))) := by ring
  have hdiff : cexP N (cexX0 N) - cexP N ((cexX0 N + τ : ℝ) : ℂ) =
      ∑ k : Fin N, ((cexS k * Real.exp (cexS k) : ℝ) : ℂ) * (cexPole (cexW N k) (cexX0 N) -
        cexPole (cexW N k) ((cexX0 N + τ : ℝ) : ℂ)) := by
    rw [cexP, cexP, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ ↦ by ring
  calc (N : ℝ) / (2 * Real.pi) = ∑ _k : Fin N, 1 / (2 * Real.pi) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
    _ ≤ ∑ k : Fin N, -(((cexS k * Real.exp (cexS k) : ℝ) : ℂ) *
          (cexPole (cexW N k) (cexX0 N) - cexPole (cexW N k) ((cexX0 N + τ : ℝ) : ℂ))).im :=
        Finset.sum_le_sum fun k _ ↦ hterm k
    _ = -(cexP N (cexX0 N) - cexP N ((cexX0 N + τ : ℝ) : ℂ)).im := by
        rw [hdiff, Complex.im_sum, Finset.sum_neg_distrib]
    _ ≤ |(cexP N (cexX0 N) - cexP N ((cexX0 N + τ : ℝ) : ℂ)).im| := neg_le_abs _
    _ ≤ ‖cexP N (cexX0 N) - cexP N ((cexX0 N + τ : ℝ) : ℂ)‖ := abs_im_le_norm _

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
            C * (1 + ∫⁻ z in ball (x : ℂ) 1, ENNReal.ofReal (1 / ‖(x : ℂ) - z‖) ∂ν) := by
  rintro ⟨C, hC⟩
  -- `N` point masses, with `N > 52.4 C`
  set N : ℕ := ⌈(53 : ℝ) * C⌉₊ + 1 with hNdef
  have hNC : (53 : ℝ) * C + 1 ≤ N := by
    rw [hNdef]; push_cast; linarith [Nat.le_ceil ((53 : ℝ) * C)]
  obtain ⟨u, hu1, hu2, hu3, hu4⟩ := hC (cexNu N) cexSigma (cexL N) (isFiniteMeasure_cexNu N)
    (isCompact_cexL N) (cexNu_compl_cexL N) continuous_cexSigma.measurable norm_cexSigma
    (cexNu_carleson N)
  -- real points are off `L`
  have hreal : ∀ x : ℝ, (x : ℂ) ∉ cexL N := by
    rintro x ⟨k, hk⟩
    have h := congrArg Complex.im hk
    rw [cexW_im, Complex.ofReal_im] at h
    linarith [cexS_pos k]
  have hEx : ∀ x : ℝ, ‖cexE x‖ = 1 := fun x ↦ by rw [norm_cexE]; simp
  -- `|u| ≤ 2C` on `ℝ`
  have hub : ∀ x : ℝ, ‖u x‖ ≤ 2 * C := by
    intro x
    have h := hu4 x (hreal x)
    have hφ : cexWeight (x : ℂ) = 0 := by simp [cexWeight]
    rw [hφ, neg_zero, Real.exp_zero, mul_one] at h
    have h2 : (C : ℝ≥0∞) * (1 + ∫⁻ z in ball (x : ℂ) 1, ENNReal.ofReal (1 / ‖(x : ℂ) - z‖)
        ∂cexNu N) ≤ ENNReal.ofReal (2 * C) := by
      calc _ ≤ (C : ℝ≥0∞) * (1 + 1) := by gcongr; exact lintegral_cexNu_le_one N x
        _ = ENNReal.ofReal (2 * C) := by
            rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_ofNat,
              one_add_one_eq_two, mul_comm]
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 (h.trans h2)
  -- `g = e^{-H} u - 𝒞₀` is weakly holomorphic; its entire representative `G`
  have hg := isWeakDbarSol_mul_sub_poles (fun k : Fin N ↦ cexW N k) (fun k ↦ cexM N k)
    (fun k ↦ (cexM_pos N k).le) differentiable_cexE (σ := cexSigma) hu1
  simp_rw [cexE_mul_cexSigma_mul_cexM] at hg
  have hg' : IsWeakDbarSol univ (fun z ↦ cexE z * u z - cexP N z) 0 := hg
  have hgc : ContinuousOn (fun z ↦ cexE z * u z - cexP N z) (cexL N)ᶜ := by
    refine (differentiable_cexE.continuous.continuousOn.mul hu2.continuousOn).sub ?_
    unfold cexP cexPole
    refine continuousOn_finsetSum _ fun k _ ↦ continuousOn_const.mul
      (continuousOn_const.mul (ContinuousOn.inv₀ (continuousOn_id.sub continuousOn_const)
        fun z hz ↦ ?_))
    exact sub_ne_zero.2 fun h ↦ hz ⟨k, h.symm⟩
  obtain ⟨G, hGd, hGeq⟩ := exists_entire_eqOn_compl (isCompact_cexL N).isClosed hg' hgc
  have hGx : ∀ z ∉ cexL N, G z = cexE z * u z - cexP N z := fun z hz ↦ (hGeq hz).symm
  -- `|𝒞₀| ≤ N` on `ℝ`
  have hPb : ∀ x : ℝ, ‖cexP N x‖ ≤ N := by
    intro x
    unfold cexP
    refine (norm_sum_le _ _).trans ?_
    calc ∑ k : Fin N, ‖((cexS k * Real.exp (cexS k) : ℝ) : ℂ) * cexPole (cexW N k) x‖
        ≤ ∑ _k : Fin N, (1 : ℝ) := Finset.sum_le_sum fun k _ ↦ ?_
      _ = N := by simp
    have hs := cexS_pos k
    have h1 : cexS k ≤ ‖(x : ℂ) - cexW N k‖ := by
      have := abs_im_le_norm ((x : ℂ) - cexW N k)
      rwa [sub_im, Complex.ofReal_im, zero_sub, cexW_im, neg_neg, abs_of_pos hs] at this
    rw [norm_mul, cexPole, norm_mul, norm_inv, norm_inv, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg Real.pi_pos.le]
    have hexp : Real.exp (cexS k) ≤ Real.pi :=
      (Real.exp_le_exp.2 (by linarith [cexS_le k])).trans
        (Real.exp_one_lt_three.le.trans Real.pi_gt_three.le)
    calc cexS k * Real.exp (cexS k) * (Real.pi⁻¹ * ‖(x : ℂ) - cexW N k‖⁻¹)
        ≤ cexS k * Real.exp (cexS k) * (Real.pi⁻¹ * (cexS k)⁻¹) := by gcongr
      _ = Real.exp (cexS k) * Real.pi⁻¹ := by field_simp
      _ ≤ 1 := by rw [mul_inv_le_iff₀ Real.pi_pos]; linarith
  -- `|G| ≤ 2C + N` on `ℝ`
  have hGb : ∀ x : ℝ, ‖G x‖ ≤ 2 * C + N := by
    intro x
    rw [hGx _ (hreal x)]
    calc ‖cexE x * u x - cexP N x‖ ≤ ‖cexE x * u x‖ + ‖cexP N x‖ := norm_sub_le _ _
      _ ≤ 2 * C + N := by rw [norm_mul, hEx, one_mul]; linarith [hub x, hPb x]
  -- decay of `G`
  have hP0 : Filter.Tendsto (cexP N) (Filter.cocompact ℂ) (nhds 0) := by
    rw [← Metric.cobounded_eq_cocompact]
    have h := tendsto_finsetSum (Finset.univ : Finset (Fin N)) fun k _ ↦
      ((Filter.tendsto_inv₀_cobounded.comp (tendsto_sub_const_cobounded (cexW N k))).const_mul
        (((cexS k * Real.exp (cexS k) : ℝ) : ℂ) * (Real.pi : ℂ)⁻¹))
    simp only [mul_zero, Finset.sum_const_zero] at h
    refine h.congr fun z ↦ ?_
    simp only [cexP, cexPole, Function.comp]
    exact Finset.sum_congr rfl fun k _ ↦ by ring
  have hGdec : Filter.Tendsto (fun z ↦ ‖G z‖ * Real.exp (-|z.im|)) (Filter.cocompact ℂ)
      (nhds 0) := by
    have hlim : Filter.Tendsto (fun z ↦ ‖u z‖ * Real.exp (-cexWeight z) + ‖cexP N z‖)
        (Filter.cocompact ℂ) (nhds 0) := by
      simpa using hu3.add hP0.norm
    refine squeeze_zero' (Filter.Eventually.of_forall fun z ↦ by positivity) ?_ hlim
    filter_upwards [(isCompact_cexL N).compl_mem_cocompact] with z hz
    rw [hGx z hz]
    have hE : ‖cexE z‖ * Real.exp (-|z.im|) = Real.exp (-cexWeight z) := by
      rw [norm_cexE, ← Real.exp_add, cexWeight]; congr 1; ring
    calc ‖cexE z * u z - cexP N z‖ * Real.exp (-|z.im|)
        ≤ (‖cexE z‖ * ‖u z‖ + ‖cexP N z‖) * Real.exp (-|z.im|) := by
          gcongr; exact (norm_sub_le _ _).trans (le_of_eq (by rw [norm_mul]))
      _ = ‖u z‖ * (‖cexE z‖ * Real.exp (-|z.im|)) + ‖cexP N z‖ * Real.exp (-|z.im|) := by ring
      _ ≤ ‖u z‖ * Real.exp (-cexWeight z) + ‖cexP N z‖ := by
          rw [hE]
          gcongr
          exact mul_le_of_le_one_right (norm_nonneg _)
            (Real.exp_le_one_iff.2 (neg_nonpos.2 (abs_nonneg _)))
  -- Phragmén–Lindelöf, Cauchy estimate, mean value theorem
  have hGexp := norm_le_mul_exp_abs_im_of_entire hGd hGb hGdec
  have hGosc := norm_sub_le_of_norm_le_mul_exp hGd hGexp (cexX0 N) (cexX0 N + 1 / 64)
  rw [add_sub_cancel_left, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 64)] at hGosc
  -- the oscillation of `𝒞₀ = e^{-H} u - G` on `ℝ`
  have hosc := cexP_oscillation N
  set x₀ : ℝ := cexX0 N
  set x₁ : ℝ := cexX0 N + 1 / 64
  have hP0x : cexP N x₀ = cexE x₀ * u x₀ - G x₀ := by rw [hGx _ (hreal x₀)]; ring
  have hP1x : cexP N x₁ = cexE x₁ * u x₁ - G x₁ := by rw [hGx _ (hreal x₁)]; ring
  have hupper : ‖cexP N x₀ - cexP N x₁‖ ≤ 4 * C + (2 * C + N) * Real.exp 1 * (1 / 64) := by
    rw [hP0x, hP1x]
    calc ‖cexE x₀ * u x₀ - G x₀ - (cexE x₁ * u x₁ - G x₁)‖
        = ‖cexE x₀ * u x₀ - cexE x₁ * u x₁ + (G x₁ - G x₀)‖ := by ring_nf
      _ ≤ ‖cexE x₀ * u x₀‖ + ‖cexE x₁ * u x₁‖ + ‖G x₁ - G x₀‖ :=
          (norm_add_le _ _).trans (by gcongr; exact norm_sub_le _ _)
      _ ≤ 2 * C + 2 * C + (2 * C + N) * Real.exp 1 * (1 / 64) := by
          rw [norm_mul, norm_mul, hEx, hEx, one_mul, one_mul]
          gcongr
          all_goals exact hub _
      _ = 4 * C + (2 * C + N) * Real.exp 1 * (1 / 64) := by ring
  -- arithmetic: `N/8 ≤ N/(2π) ≤ 4C + (2C + N) e/64` contradicts `N ≥ 53 C + 1`
  have h1 : (N : ℝ) / 8 ≤ (N : ℝ) / (2 * Real.pi) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith [Real.pi_le_four])
  have h2 := h1.trans (hosc.trans hupper)
  have he := Real.exp_one_lt_three
  have hC0 : (0 : ℝ) ≤ C := C.coe_nonneg
  have hN0 : (0 : ℝ) ≤ N := N.cast_nonneg
  nlinarith

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
