import OrtegaCerdaSeip.Lemma4.Kernel
import OrtegaCerdaSeip.Jones.Weak

/-!
# M05 (Lemma 4) — the part of `μ` in `Im z ≥ 10`: `u₂ - u₃`

See `blueprint/M05_Lemma4.md` (§1.3).

For `ν` carried by a compact set in `{Im z ≥ 10}` (the paper's `μ₂` restricted to `ℂ⁺`):
* `ρ = e^{-ε|Im w|} ν` (`expImMeasure ε ν`) and `θ(w) = e^{iε Re w} σ(w)`, so that
  `θ ρ = e^{iεw} σ ν` (the paper's `dσ = e^{iεz} dμ₂`, p. 409);
* `v₁ = jonesSol ρ θ` (Jones' solution of `∂̄v₁ = e^{iεz} dμ₂` in `ℂ⁺`);
* `u₂ = φ e^{-iεz} v₁` with the cut-off `φ(z) = χ(Im z - 1)`, `χ = Real.smoothTransition`
  (`φ = 0` for `Im z ≤ 1`, `φ = 1` for `Im z ≥ 2`); the paper prints `e^{iεz} v₁` (typo);
* `g = ∂̄u₂ - μ₂ = (∂̄φ) e^{-iεz} v₁`, supported in `1 ≤ Im z ≤ 2` and bounded there by Jones'
  strip estimate;
* `u₃ = k * g` (`kerSol ε volume g`), and `upperSol = u₂ - u₃`.

On `ℝ`, `upperSol = -u₃` is bounded by a constant depending only on `ε` and the Carleson constant.
-/

open MeasureTheory Metric Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace OCS

/-! ## The cut-off -/

/-- The cut-off `φ(z) = χ(Im z - 1)`: `0` for `Im z ≤ 1`, `1` for `Im z ≥ 2`, smooth. -/
def cutoff (z : ℂ) : ℝ :=
  Real.smoothTransition (z.im - 1)

theorem cutoff_eq_zero {z : ℂ} (hz : z.im ≤ 1) : cutoff z = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem cutoff_eq_one {z : ℂ} (hz : 2 ≤ z.im) : cutoff z = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem contDiff_cutoff : ContDiff ℝ (⊤ : ℕ∞) (fun z ↦ (cutoff z : ℂ)) := by
  have h : ContDiff ℝ (⊤ : ℕ∞) cutoff :=
    Real.smoothTransition.contDiff.comp (Complex.imCLM.contDiff.sub contDiff_const)
  exact Complex.ofRealCLM.contDiff.comp h

theorem dbar_cutoff_eq_zero {z : ℂ} (hz : z.im < 1 ∨ 2 < z.im) :
    dbar (fun z ↦ (cutoff z : ℂ)) z = 0 := by
  rcases hz with hz | hz
  · have h : (fun z ↦ (cutoff z : ℂ)) =ᶠ[𝓝 z] fun _ ↦ (0 : ℂ) := by
      filter_upwards [(isOpen_lt continuous_im continuous_const).mem_nhds hz] with w hw
      simp [cutoff_eq_zero (le_of_lt hw)]
    rw [dbar_congr h]
    simp [dbar]
  · have h : (fun z ↦ (cutoff z : ℂ)) =ᶠ[𝓝 z] fun _ ↦ (1 : ℂ) := by
      filter_upwards [(isOpen_lt continuous_const continuous_im).mem_nhds hz] with w hw
      simp [cutoff_eq_one (le_of_lt hw)]
    rw [dbar_congr h]
    simp [dbar]

theorem continuous_dbar_cutoff : Continuous (dbar (fun z ↦ (cutoff z : ℂ))) :=
  continuous_dbar (contDiff_one_of_top contDiff_cutoff)

/-- `∂̄φ` only depends on `Im z`: `φ` is invariant under real translations. -/
theorem dbar_cutoff_eq_im (z : ℂ) :
    dbar (fun z ↦ (cutoff z : ℂ)) z = dbar (fun z ↦ (cutoff z : ℂ)) ((z.im : ℂ) * I) := by
  have h1 : (fun w ↦ (cutoff (w - (z.re : ℂ)) : ℂ)) = fun w ↦ (cutoff w : ℂ) := by
    funext w
    simp [cutoff]
  have h2 := dbar_comp_sub (fun z ↦ (cutoff z : ℂ)) (z.re : ℂ) z
  simp only [h1] at h2
  rw [h2]
  congr 1
  apply Complex.ext <;> simp

theorem exists_norm_dbar_cutoff_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ z, ‖dbar (fun z ↦ (cutoff z : ℂ)) z‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (1 : ℝ)) (b := 2)).exists_bound_of_continuousOn
    ((continuous_dbar_cutoff.comp (continuous_ofReal.mul continuous_const)).continuousOn)
  refine ⟨max C 0, le_max_right _ _, fun z ↦ ?_⟩
  by_cases hz : z.im < 1 ∨ 2 < z.im
  · rw [dbar_cutoff_eq_zero hz, norm_zero]
    exact le_max_right _ _
  · simp only [not_or, not_lt] at hz
    rw [dbar_cutoff_eq_im z]
    exact (hC z.im ⟨hz.1, hz.2⟩).trans (le_max_left _ _)

/-! ## The data of the upper part -/

/-- `θ(w) = e^{iε Re w} σ(w)`, so that `θ · e^{-ε Im w} = e^{iεw} σ(w)`. -/
def upperTheta (ε : ℝ) (σ : ℂ → ℂ) (w : ℂ) : ℂ :=
  Complex.exp ((ε * w.re : ℝ) * I) * σ w

/-- The density `g = (∂̄φ) e^{-iεz} v₁` of the correction `u₃` (supported in `1 ≤ Im z ≤ 2`). -/
def upperG (ε : ℝ) (ν : Measure ℂ) (σ : ℂ → ℂ) (z : ℂ) : ℂ :=
  dbar (fun z ↦ (cutoff z : ℂ)) z * Complex.exp (-(I * ε * z)) *
    jonesSol (expImMeasure ε ν) (upperTheta ε σ) z

/-- The solution for the part of the measure in `Im z ≥ 10`: `u₂ - u₃`. -/
def upperSol (ε : ℝ) (ν : Measure ℂ) (σ : ℂ → ℂ) (z : ℂ) : ℂ :=
  (cutoff z : ℂ) * Complex.exp (-(I * ε * z)) * jonesSol (expImMeasure ε ν) (upperTheta ε σ) z -
    kerSol ε volume (upperG ε ν σ) z

theorem norm_upperTheta_le {ε : ℝ} {σ : ℂ → ℂ} (hσ1 : ∀ z, ‖σ z‖ ≤ 1) (w : ℂ) :
    ‖upperTheta ε σ w‖ ≤ 1 := by
  rw [upperTheta, norm_mul, norm_exp_ofReal_mul_I, one_mul]
  exact hσ1 w

theorem upperG_eq_zero (ε : ℝ) (ν : Measure ℂ) (σ : ℂ → ℂ) {z : ℂ}
    (hz : z.im < 1 ∨ 2 < z.im) : upperG ε ν σ z = 0 := by
  simp [upperG, dbar_cutoff_eq_zero hz]

theorem norm_cutoff_le_one (z : ℂ) : ‖(cutoff z : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs, cutoff, abs_of_nonneg (Real.smoothTransition.nonneg _)]
  exact Real.smoothTransition.le_one _

/-- `|e^{-iεz}| = e^{ε Im z}`. -/
theorem norm_exp_neg_I_mul (ε : ℝ) (z : ℂ) :
    ‖Complex.exp (-(I * ε * z))‖ = Real.exp (ε * z.im) := by
  rw [Complex.norm_exp]
  congr 1
  simp

theorem continuous_exp_neg_I_mul (ε : ℝ) : Continuous fun z : ℂ ↦ Complex.exp (-(I * ε * z)) := by
  fun_prop

theorem measurable_upperTheta (ε : ℝ) {σ : ℂ → ℂ} (hσ : Measurable σ) :
    Measurable (upperTheta ε σ) := by
  unfold upperTheta
  fun_prop

theorem ae_mem_of_measure_compl {ν : Measure ℂ} {L : Set ℂ} (hνL : ν Lᶜ = 0) :
    ∀ᵐ w ∂ν, w ∈ L :=
  mem_ae_iff.2 hνL

/-- The strip `1 ≤ Im z ≤ 2` carrying `∂̄φ`. -/
theorem measurableSet_strip_one_two : MeasurableSet {z : ℂ | 1 ≤ z.im ∧ z.im ≤ 2} :=
  (measurableSet_le measurable_const measurable_im).inter
    (measurableSet_le measurable_im measurable_const)

theorem upperG_eq_zero_of_notMem (ε : ℝ) (ν : Measure ℂ) (σ : ℂ → ℂ) {z : ℂ}
    (hz : z ∉ {z : ℂ | 1 ≤ z.im ∧ z.im ≤ 2}) : upperG ε ν σ z = 0 := by
  apply upperG_eq_zero
  have hz' : ¬(1 ≤ z.im ∧ z.im ≤ 2) := hz
  rwa [not_and_or, not_le, not_le] at hz'

theorem abs_im_le_of_upperG_ne_zero (ε : ℝ) (ν : Measure ℂ) (σ : ℂ → ℂ) {z : ℂ}
    (hz : upperG ε ν σ z ≠ 0) : |z.im| ≤ 2 := by
  by_contra h
  apply hz
  apply upperG_eq_zero
  rcases le_or_gt 1 z.im with h1 | h1
  · right
    rw [abs_of_nonneg (by linarith)] at h
    linarith
  · left; exact h1

/-! ## The test function `β = φ e^{-iεz} α` -/

theorem contDiff_exp_neg_I_mul (ε : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) fun z : ℂ ↦ Complex.exp (-(I * ε * z)) :=
  Complex.contDiff_exp.comp (contDiff_const.mul contDiff_id).neg

theorem contDiff_upperTest (ε : ℝ) {α : ℂ → ℂ} (hα : ContDiff ℝ (⊤ : ℕ∞) α) :
    ContDiff ℝ (⊤ : ℕ∞) fun w ↦ (cutoff w : ℂ) * Complex.exp (-(I * ε * w)) * α w :=
  (contDiff_cutoff.mul (contDiff_exp_neg_I_mul ε)).mul hα

theorem tsupport_cutoff_subset : tsupport (fun z ↦ (cutoff z : ℂ)) ⊆ {z | 1 ≤ z.im} := by
  refine closure_minimal (fun z hz ↦ ?_) (isClosed_le continuous_const continuous_im)
  by_contra h
  exact hz (by simp [cutoff_eq_zero (not_le.1 h).le])

theorem tsupport_upperTest_subset (ε : ℝ) (α : ℂ → ℂ) :
    tsupport (fun w ↦ (cutoff w : ℂ) * Complex.exp (-(I * ε * w)) * α w) ⊆ {z | 0 < z.im} :=
  tsupport_mul_subset_left.trans (tsupport_mul_subset_left.trans
    (tsupport_cutoff_subset.trans fun z (hz : 1 ≤ z.im) ↦ show 0 < z.im by linarith))

/-- `∂̄(φ e α) = (∂̄φ) e α + φ e ∂̄α` (`e = e^{-iεz}` is holomorphic). -/
theorem dbar_upperTest (ε : ℝ) {α : ℂ → ℂ} (hα : ContDiff ℝ (⊤ : ℕ∞) α) (z : ℂ) :
    dbar (fun w ↦ (cutoff w : ℂ) * Complex.exp (-(I * ε * w)) * α w) z =
      dbar (fun w ↦ (cutoff w : ℂ)) z * Complex.exp (-(I * ε * z)) * α z +
        (cutoff z : ℂ) * Complex.exp (-(I * ε * z)) * dbar α z := by
  have hΦ : DifferentiableAt ℝ (fun w ↦ (cutoff w : ℂ)) z :=
    contDiff_cutoff.differentiable (by simp) z
  have he : DifferentiableAt ℝ (fun w : ℂ ↦ Complex.exp (-(I * ε * w))) z :=
    (contDiff_exp_neg_I_mul ε).differentiable (by simp) z
  have hαd : DifferentiableAt ℝ α z := hα.differentiable (by simp) z
  have hde : dbar (fun w : ℂ ↦ Complex.exp (-(I * ε * w))) z = 0 :=
    dbar_eq_zero_of_differentiableAt (by fun_prop)
  have h1 : dbar (fun w ↦ (cutoff w : ℂ) * Complex.exp (-(I * ε * w))) z =
      dbar (fun w ↦ (cutoff w : ℂ)) z * Complex.exp (-(I * ε * z)) := by
    rw [dbar_mul hΦ he, hde, mul_zero, add_zero]
  rw [dbar_mul (f := fun w ↦ (cutoff w : ℂ) * Complex.exp (-(I * ε * w))) (hΦ.mul he) hαd, h1]

/-- `φ e^{-iεz} f` is locally integrable on `ℂ` if `f` is locally integrable on `ℂ⁺`. -/
theorem locallyIntegrable_cutoff_mul (ε : ℝ) {f : ℂ → ℂ}
    (hf : LocallyIntegrableOn f {z | 0 < z.im}) :
    LocallyIntegrable fun z ↦ (cutoff z : ℂ) * Complex.exp (-(I * ε * z)) * f z := by
  have h1 : LocallyIntegrableOn (fun z ↦ (cutoff z : ℂ) * Complex.exp (-(I * ε * z)) * f z)
      {z | 0 < z.im} :=
    hf.continuousOn_mul
      ((contDiff_cutoff.continuous.mul (continuous_exp_neg_I_mul ε)).continuousOn)
      (isOpen_lt continuous_const continuous_im).isLocallyClosed
  rw [locallyIntegrable_iff]
  intro k hk
  have hk1 : IsCompact (k ∩ {z | 1 ≤ z.im}) :=
    hk.inter_right (isClosed_le continuous_const continuous_im)
  have hsub : k ⊆ (k ∩ {z | 1 ≤ z.im}) ∪ {z | z.im ≤ 1} := fun z hz ↦
    (le_total 1 z.im).elim (fun h ↦ Or.inl ⟨hz, h⟩) Or.inr
  refine IntegrableOn.mono_set (IntegrableOn.union ?_ ?_) hsub
  · exact h1.integrableOn_compact_subset
      (fun z hz ↦ show 0 < z.im by linarith [show (1 : ℝ) ≤ z.im from hz.2]) hk1
  · refine integrableOn_zero.congr_fun (fun z (hz : z.im ≤ 1) ↦ ?_)
      (measurableSet_le measurable_im measurable_const)
    simp [cutoff_eq_zero hz]

/-- `|φ e^{-iεz} f| e^{-ε|Im z|} ≤ |f|`. -/
theorem norm_cutoff_mul_le (ε : ℝ) (f : ℂ → ℂ) (z : ℂ) :
    ‖(cutoff z : ℂ) * Complex.exp (-(I * ε * z)) * f z‖ * Real.exp (-ε * |z.im|) ≤ ‖f z‖ := by
  rcases le_or_gt z.im 1 with hz | hz
  · simp [cutoff_eq_zero hz]
  · rw [norm_mul, norm_mul, norm_exp_neg_I_mul, abs_of_pos (by linarith : 0 < z.im)]
    calc ‖(cutoff z : ℂ)‖ * Real.exp (ε * z.im) * ‖f z‖ * Real.exp (-ε * z.im)
        = ‖(cutoff z : ℂ)‖ * ‖f z‖ * (Real.exp (ε * z.im) * Real.exp (-ε * z.im)) := by ring
      _ = ‖(cutoff z : ℂ)‖ * ‖f z‖ := by rw [← Real.exp_add]; simp
      _ ≤ 1 * ‖f z‖ := by gcongr; exact norm_cutoff_le_one z
      _ = ‖f z‖ := one_mul _

section Hyp

variable {ε : ℝ} {ν : Measure ℂ} {σ : ℂ → ℂ} {L : Set ℂ}

theorem ae_ten_le_im_expImMeasure (hνL : ν Lᶜ = 0) (hL10 : ∀ w ∈ L, 10 ≤ w.im) :
    ∀ᵐ w ∂(expImMeasure ε ν), 10 ≤ w.im :=
  Filter.Eventually.mono
    ((expImMeasure_absolutelyContinuous ε ν).ae_le (ae_mem_of_measure_compl hνL))
    fun w hw ↦ hL10 w hw

/-- `∫ β θ dρ = ∫ β e^{iεw} σ dν`: the Jones datum is `e^{iεz} dμ₂`. -/
theorem integral_upperTheta (hνL : ν Lᶜ = 0) (hL10 : ∀ w ∈ L, 10 ≤ w.im) (β : ℂ → ℂ) :
    ∫ w, β w * upperTheta ε σ w ∂(expImMeasure ε ν) =
      ∫ w, β w * Complex.exp (I * ε * w) * σ w ∂ν := by
  have hmeas : Measurable fun z : ℂ ↦ ENNReal.ofReal (Real.exp (-ε * |z.im|)) := by fun_prop
  rw [expImMeasure, integral_withDensity_eq_integral_toReal_smul hmeas
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  refine integral_congr_ae ?_
  filter_upwards [ae_mem_of_measure_compl hνL] with w hw
  have him : |w.im| = w.im := abs_of_nonneg (by linarith [hL10 w hw])
  have hexp : Complex.exp (I * ε * w) =
      (Real.exp (-ε * w.im) : ℂ) * Complex.exp ((ε * w.re : ℝ) * I) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    apply Complex.ext <;> simp
  rw [ENNReal.toReal_ofReal (Real.exp_pos _).le, him, upperTheta, Complex.real_smul, hexp]
  ring

variable [IsFiniteMeasure ν]

/-- **Uniform bound for `g = ∂̄u₂ - μ₂`**, from Jones' strip estimate. -/
theorem norm_upperG_le (hε : 0 < ε) :
    ∃ C₀ : ℝ, ∀ (K : ℝ≥0) (ν : Measure ℂ) (σ : ℂ → ℂ) (L : Set ℂ), IsFiniteMeasure ν →
      ν Lᶜ = 0 → (∀ w ∈ L, 10 ≤ w.im) → (∀ z, ‖σ z‖ ≤ 1) →
      IsCarlesonLarge (expImMeasure ε ν) K →
      ∀ z, ‖upperG ε ν σ z‖ ≤ C₀ * Real.exp (12 * K) := by
  obtain ⟨Cφ, hCφ0, hCφ⟩ := exists_norm_dbar_cutoff_le
  refine ⟨Cφ * Real.exp (2 * ε) * (3 / Real.pi), fun K ν σ L hν hνL hL10 hσ1 hC z ↦ ?_⟩
  have := isFiniteMeasure_expImMeasure hε.le ν
  by_cases hz : z.im < 1 ∨ 2 < z.im
  · rw [upperG_eq_zero ε ν σ hz, norm_zero]
    positivity
  · simp only [not_or, not_lt] at hz
    rw [upperG, norm_mul, norm_mul, norm_exp_neg_I_mul]
    have h2 : Real.exp (ε * z.im) ≤ Real.exp (2 * ε) := Real.exp_le_exp.2 (by nlinarith)
    have h3 := norm_jonesSol_le_strip (ae_ten_le_im_expImMeasure hνL hL10) hC
      (norm_upperTheta_le (ε := ε) hσ1) (z := z) (by linarith) hz.2
    calc ‖dbar (fun z ↦ (cutoff z : ℂ)) z‖ * Real.exp (ε * z.im) *
          ‖jonesSol (expImMeasure ε ν) (upperTheta ε σ) z‖
        ≤ Cφ * Real.exp (2 * ε) * (3 / Real.pi * Real.exp (12 * K)) := by
          gcongr
          exact hCφ z
      _ = Cφ * Real.exp (2 * ε) * (3 / Real.pi) * Real.exp (12 * K) := by ring

theorem continuous_upperG (hε : 0 < ε) (hL : IsCompact L) (hνL : ν Lᶜ = 0)
    (hL10 : ∀ w ∈ L, 10 ≤ w.im) (hσ : Measurable σ) (hσ1 : ∀ z, ‖σ z‖ ≤ 1) :
    Continuous (upperG ε ν σ) := by
  have := isFiniteMeasure_expImMeasure hε.le ν
  have hv : ContinuousOn (jonesSol (expImMeasure ε ν) (upperTheta ε σ)) ({z | 0 < z.im} ∩ Lᶜ) :=
    continuousOn_jonesSol (ae_ten_le_im_expImMeasure hνL hL10) hL.isClosed
      (expImMeasure_absolutelyContinuous ε ν hνL) (measurable_upperTheta ε hσ)
      (norm_upperTheta_le hσ1)
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : z.im < 1 ∨ 2 < z.im
  · have h0 : (fun _ ↦ (0 : ℂ)) =ᶠ[𝓝 z] upperG ε ν σ := by
      rcases hz with hz | hz
      · filter_upwards [(isOpen_lt continuous_im continuous_const).mem_nhds hz] with w hw
        exact (upperG_eq_zero ε ν σ (Or.inl hw)).symm
      · filter_upwards [(isOpen_lt continuous_const continuous_im).mem_nhds hz] with w hw
        exact (upperG_eq_zero ε ν σ (Or.inr hw)).symm
    exact continuousAt_const.congr h0
  · simp only [not_or, not_lt] at hz
    have hmem : {w : ℂ | 0 < w.im} ∩ Lᶜ ∈ 𝓝 z := by
      refine inter_mem ((isOpen_lt continuous_const continuous_im).mem_nhds ?_)
        (hL.isClosed.isOpen_compl.mem_nhds fun hzL ↦ ?_)
      · show 0 < z.im
        linarith
      · linarith [hL10 z hzL]
    exact (continuous_dbar_cutoff.continuousAt.mul
      (continuous_exp_neg_I_mul ε).continuousAt).mul (hv.continuousAt hmem)

/-- Decay of `g`: `|g(z)| ≤ D/|z|²` for `|z| ≥ R` (from the decay of Jones' solution). -/
theorem upperG_decay (hε : 0 < ε) (hL : IsCompact L) (hνL : ν Lᶜ = 0)
    (hL10 : ∀ w ∈ L, 10 ≤ w.im) (hσ1 : ∀ z, ‖σ z‖ ≤ 1) :
    ∃ D R : ℝ, 0 ≤ D ∧ 1 ≤ R ∧ ∀ z : ℂ, R ≤ ‖z‖ → ‖upperG ε ν σ z‖ ≤ D / ‖z‖ ^ 2 := by
  have := isFiniteMeasure_expImMeasure hε.le ν
  obtain ⟨Cφ, hCφ0, hCφ⟩ := exists_norm_dbar_cutoff_le
  obtain ⟨C, R, hCR⟩ := jonesSol_decay hL (expImMeasure_absolutelyContinuous ε ν hνL) hL10
    (θ := upperTheta ε σ) (norm_upperTheta_le hσ1)
  refine ⟨Cφ * Real.exp (2 * ε) * max C 0, max R 1, by positivity, le_max_right _ _,
    fun z hz ↦ ?_⟩
  have hz0 : 0 < ‖z‖ := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hz)
  by_cases hz' : z.im < 1 ∨ 2 < z.im
  · rw [upperG_eq_zero ε ν σ hz', norm_zero]
    positivity
  · simp only [not_or, not_lt] at hz'
    rw [upperG, norm_mul, norm_mul, norm_exp_neg_I_mul]
    have h2 : Real.exp (ε * z.im) ≤ Real.exp (2 * ε) := Real.exp_le_exp.2 (by nlinarith)
    have h3 : ‖jonesSol (expImMeasure ε ν) (upperTheta ε σ) z‖ ≤ max C 0 / ‖z‖ ^ 2 :=
      (hCR z (by linarith) ((le_max_left _ _).trans hz)).trans
        (div_le_div_of_nonneg_right (le_max_left _ _) (by positivity))
    calc ‖dbar (fun z ↦ (cutoff z : ℂ)) z‖ * Real.exp (ε * z.im) *
          ‖jonesSol (expImMeasure ε ν) (upperTheta ε σ) z‖
        ≤ Cφ * Real.exp (2 * ε) * (max C 0 / ‖z‖ ^ 2) := by
          gcongr
          exact hCφ z
      _ = Cφ * Real.exp (2 * ε) * max C 0 / ‖z‖ ^ 2 := by ring

theorem tendsto_upperG (hε : 0 < ε) (hL : IsCompact L) (hνL : ν Lᶜ = 0)
    (hL10 : ∀ w ∈ L, 10 ≤ w.im) (hσ1 : ∀ z, ‖σ z‖ ≤ 1) :
    Tendsto (upperG ε ν σ) (cocompact ℂ) (𝓝 0) := by
  obtain ⟨D, R, -, -, hDR⟩ := upperG_decay hε hL hνL hL10 hσ1
  have hlim : Tendsto (fun z : ℂ ↦ D / ‖z‖ ^ 2) (cocompact ℂ) (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_pow_atTop two_ne_zero).comp tendsto_norm_cocompact_atTop)
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [tendsto_norm_cocompact_atTop.eventually_ge_atTop R] with z hz using hDR z hz

theorem upperG_bounded (hε : 0 < ε) (hνL : ν Lᶜ = 0) (hL10 : ∀ w ∈ L, 10 ≤ w.im)
    (hσ1 : ∀ z, ‖σ z‖ ≤ 1) : ∃ M : ℝ, ∀ z, ‖upperG ε ν σ z‖ ≤ M := by
  have := isFiniteMeasure_expImMeasure hε.le ν
  obtain ⟨C₀, hC₀⟩ := norm_upperG_le hε
  exact ⟨_, hC₀ _ ν σ L inferInstance hνL hL10 hσ1 (isCarlesonLarge_of_isFiniteMeasure _)⟩

/-- `∫_{1 ≤ Im ≤ 2} dm/(1 + |z|²) < ∞` (Poisson bound for the Carleson measure `m|_S`). -/
theorem integrableOn_strip_inv_one_add_sq (A : ℝ) :
    IntegrableOn (fun z : ℂ ↦ A / (1 + ‖z‖ ^ 2)) {z : ℂ | 1 ≤ z.im ∧ z.im ≤ 2} := by
  have hc : Continuous fun z : ℂ ↦ A / (1 + ‖z‖ ^ 2) :=
    continuous_const.div (by fun_prop) fun z ↦ by positivity
  refine ⟨hc.aestronglyMeasurable, ?_⟩
  have hP := (isCarlesonWith_volume_strip (a := 1) (b := 2) (by norm_num)).isCarlesonLarge.lintegral_poisson_le 0 le_rfl
  simp only [Complex.ofReal_zero, sub_zero, one_pow] at hP
  have heq : ∀ z : ℂ, ‖A / (1 + ‖z‖ ^ 2)‖ₑ =
      ‖A‖ₑ * ENNReal.ofReal (1 / (‖z‖ ^ 2 + 1)) := by
    intro z
    rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _),
      norm_div, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 1 + ‖z‖ ^ 2)]
    congr 1
    rw [add_comm]
    ring
  rw [HasFiniteIntegral]
  simp_rw [heq]
  rw [lintegral_const_mul _ (by fun_prop)]
  exact ENNReal.mul_lt_top enorm_lt_top (hP.trans_lt (by simp [ENNReal.mul_lt_top]))

theorem integrable_upperG (hε : 0 < ε) (hL : IsCompact L) (hνL : ν Lᶜ = 0)
    (hL10 : ∀ w ∈ L, 10 ≤ w.im) (hσ : Measurable σ) (hσ1 : ∀ z, ‖σ z‖ ≤ 1) :
    Integrable (upperG ε ν σ) := by
  obtain ⟨B, hB⟩ := upperG_bounded hε hνL hL10 hσ1
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  obtain ⟨D, R, hD0, hR1, hDR⟩ := upperG_decay hε hL hνL hL10 hσ1
  set A := max (B * (1 + R ^ 2)) (2 * D) with hA
  have hdom : ∀ z, ‖upperG ε ν σ z‖ ≤
      {z : ℂ | 1 ≤ z.im ∧ z.im ≤ 2}.indicator (fun z ↦ A / (1 + ‖z‖ ^ 2)) z := by
    intro z
    by_cases hz : z ∈ {z : ℂ | 1 ≤ z.im ∧ z.im ≤ 2}
    · rw [indicator_of_mem hz]
      rcases le_or_gt R ‖z‖ with hzR | hzR
      · have h1 : 1 ≤ ‖z‖ := hR1.trans hzR
        calc ‖upperG ε ν σ z‖ ≤ D / ‖z‖ ^ 2 := hDR z hzR
          _ ≤ 2 * D / (1 + ‖z‖ ^ 2) := by
            have h2 : 1 ≤ ‖z‖ ^ 2 := one_le_pow₀ h1
            rw [div_le_div_iff₀ (by positivity) (by positivity)]
            nlinarith [mul_nonneg hD0 (sub_nonneg.2 h2)]
          _ ≤ A / (1 + ‖z‖ ^ 2) := by gcongr; exact le_max_right _ _
      · have hz2 : ‖z‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hzR.le 2
        calc ‖upperG ε ν σ z‖ ≤ B := hB z
          _ = B * (1 + R ^ 2) / (1 + R ^ 2) := by field_simp
          _ ≤ B * (1 + R ^ 2) / (1 + ‖z‖ ^ 2) := by gcongr
          _ ≤ A / (1 + ‖z‖ ^ 2) := by gcongr; exact le_max_left _ _
    · rw [indicator_of_notMem hz, upperG_eq_zero_of_notMem ε ν σ hz, norm_zero]
  have hint : Integrable ({z : ℂ | 1 ≤ z.im ∧ z.im ≤ 2}.indicator fun z ↦ A / (1 + ‖z‖ ^ 2)) :=
    (integrable_indicator_iff measurableSet_strip_one_two).2
      (integrableOn_strip_inv_one_add_sq A)
  exact hint.mono' (continuous_upperG hε hL hνL hL10 hσ hσ1).aestronglyMeasurable
    (ae_of_all _ hdom)

/-- **`∂̄(u₂ - u₃) = μ₂`** (p. 410, "the function `u = u₁ + u₂ - u₃` satisfies `∂̄u = μ`"). -/
theorem upperSol_isWeakDbarSolMeasure (hε : 0 < ε) (hL : IsCompact L) (hνL : ν Lᶜ = 0)
    (hL10 : ∀ w ∈ L, 10 ≤ w.im) (hσ : Measurable σ) (hσ1 : ∀ z, ‖σ z‖ ≤ 1) :
    IsWeakDbarSolMeasure (upperSol ε ν σ) ν σ := by
  have := isFiniteMeasure_expImMeasure hε.le ν
  have h10 := ae_ten_le_im_expImMeasure (ε := ε) hνL hL10
  obtain ⟨hv_loc, hv_eq⟩ := jonesSol_isWeakDbarSol h10 (measurable_upperTheta ε hσ)
    (norm_upperTheta_le (ε := ε) hσ1)
  have hg_cont := continuous_upperG hε hL hνL hL10 hσ hσ1
  -- `u₃ = k * g` solves `∂̄u₃ = g`
  have hu₃ := kerSol_isWeakDbarSolMeasure hε (integrable_upperG hε hL hνL hL10 hσ hσ1) (b := 2)
    (ae_of_all _ fun z hz ↦ abs_im_le_of_upperG_ne_zero ε ν σ hz)
  refine ⟨(locallyIntegrable_cutoff_mul ε hv_loc).sub hu₃.1, fun α hα hαc ↦ ?_⟩
  -- the test function `β = φ e^{-iεz} α`, supported in `ℂ⁺`
  have hβ := contDiff_upperTest ε hα
  have hβc : HasCompactSupport fun w ↦ (cutoff w : ℂ) * Complex.exp (-(I * ε * w)) * α w :=
    hαc.mul_left
  have hβs := tsupport_upperTest_subset ε α
  -- Jones: `∫ v₁ ∂̄β = -∫ β θ dρ = -∫ α σ dν`
  have hJ := hv_eq _ hβ hβc hβs
  have hθ : ∫ w, (cutoff w : ℂ) * Complex.exp (-(I * ε * w)) * α w * upperTheta ε σ w
      ∂(expImMeasure ε ν) = ∫ w, α w * σ w ∂ν := by
    rw [integral_upperTheta hνL hL10]
    refine integral_congr_ae ?_
    filter_upwards [ae_mem_of_measure_compl hνL] with w hw
    have hΦ1 : (cutoff w : ℂ) = 1 := by
      rw [cutoff_eq_one (by linarith [hL10 w hw] : 2 ≤ w.im), Complex.ofReal_one]
    have hee : Complex.exp (-(I * ε * w)) * Complex.exp (I * ε * w) = 1 := by
      rw [← Complex.exp_add]; simp
    rw [hΦ1]
    linear_combination (α w * σ w) * hee
  -- integrability of the three pieces
  have i1 : Integrable fun z ↦ jonesSol (expImMeasure ε ν) (upperTheta ε σ) z *
      dbar (fun w ↦ (cutoff w : ℂ) * Complex.exp (-(I * ε * w)) * α w) z :=
    integrable_mul_dbar_of_locallyIntegrableOn hv_loc (contDiff_one_of_top hβ) hβc hβs
  have i2 : Integrable fun z ↦ upperG ε ν σ z * α z :=
    (hg_cont.mul hα.continuous).integrable_of_hasCompactSupport hαc.mul_left
  have i3 : Integrable fun z ↦ kerSol ε volume (upperG ε ν σ) z * dbar α z :=
    integrable_mul_dbar_of_locallyIntegrableOn (Ω := univ) (hu₃.1.locallyIntegrableOn univ)
      (contDiff_one_of_top hα) hαc (subset_univ _)
  -- pointwise: `(u₂ - u₃) ∂̄α = v₁ ∂̄β - g α - u₃ ∂̄α`
  have hpt : ∀ z, upperSol ε ν σ z * dbar α z =
      (jonesSol (expImMeasure ε ν) (upperTheta ε σ) z *
          dbar (fun w ↦ (cutoff w : ℂ) * Complex.exp (-(I * ε * w)) * α w) z -
        upperG ε ν σ z * α z) - kerSol ε volume (upperG ε ν σ) z * dbar α z := by
    intro z
    rw [dbar_upperTest ε hα z]
    simp only [upperSol, upperG]
    ring
  have i12 : Integrable fun z ↦ jonesSol (expImMeasure ε ν) (upperTheta ε σ) z *
      dbar (fun w ↦ (cutoff w : ℂ) * Complex.exp (-(I * ε * w)) * α w) z -
        upperG ε ν σ z * α z := i1.sub i2
  simp_rw [hpt]
  rw [integral_sub i12 i3, integral_sub i1 i2, hJ, hθ, hu₃.2 α hα hαc]
  have hcomm : ∫ z, upperG ε ν σ z * α z = ∫ z, α z * upperG ε ν σ z := by
    simp_rw [mul_comm]
  rw [hcomm]
  ring

theorem continuousOn_upperSol (hε : 0 < ε) (hL : IsCompact L) (hνL : ν Lᶜ = 0)
    (hL10 : ∀ w ∈ L, 10 ≤ w.im) (hσ : Measurable σ) (hσ1 : ∀ z, ‖σ z‖ ≤ 1) :
    ContinuousOn (upperSol ε ν σ) Lᶜ := by
  have := isFiniteMeasure_expImMeasure hε.le ν
  have hv : ContinuousOn (jonesSol (expImMeasure ε ν) (upperTheta ε σ)) ({z | 0 < z.im} ∩ Lᶜ) :=
    continuousOn_jonesSol (ae_ten_le_im_expImMeasure hνL hL10) hL.isClosed
      (expImMeasure_absolutelyContinuous ε ν hνL) (measurable_upperTheta ε hσ)
      (norm_upperTheta_le hσ1)
  obtain ⟨M, hM⟩ := upperG_bounded hε hνL hL10 hσ1
  have hu₃ : Continuous (kerSol ε volume (upperG ε ν σ)) :=
    continuous_kerSol_volume hε (continuous_upperG hε hL hνL hL10 hσ hσ1) hM
      (fun z hz ↦ abs_im_le_of_upperG_ne_zero ε ν σ hz)
  refine continuousOn_of_forall_continuousAt fun z hz ↦ ?_
  refine ContinuousAt.sub ?_ hu₃.continuousAt
  rcases lt_or_ge z.im 1 with hz1 | hz1
  · -- `u₂ = 0` near `z`
    have h0 : (fun _ ↦ (0 : ℂ)) =ᶠ[𝓝 z] fun z ↦ (cutoff z : ℂ) * Complex.exp (-(I * ε * z)) *
        jonesSol (expImMeasure ε ν) (upperTheta ε σ) z := by
      filter_upwards [(isOpen_lt continuous_im continuous_const).mem_nhds hz1] with w hw
      simp [cutoff_eq_zero (le_of_lt hw)]
    exact continuousAt_const.congr h0
  · have hmem : {w : ℂ | 0 < w.im} ∩ Lᶜ ∈ 𝓝 z :=
      inter_mem ((isOpen_lt continuous_const continuous_im).mem_nhds
        (show 0 < z.im by linarith)) (hL.isClosed.isOpen_compl.mem_nhds hz)
    exact (contDiff_cutoff.continuous.continuousAt.mul
      (continuous_exp_neg_I_mul ε).continuousAt).mul (hv.continuousAt hmem)

theorem tendsto_upperSol (hε : 0 < ε) (hL : IsCompact L) (hνL : ν Lᶜ = 0)
    (hL10 : ∀ w ∈ L, 10 ≤ w.im) (hσ : Measurable σ) (hσ1 : ∀ z, ‖σ z‖ ≤ 1) :
    Tendsto (fun z ↦ ‖upperSol ε ν σ z‖ * Real.exp (-ε * |z.im|)) (cocompact ℂ) (𝓝 0) := by
  have := isFiniteMeasure_expImMeasure hε.le ν
  -- `u₂`: bounded by `|v₁| = O(|z|⁻²)`
  obtain ⟨C, R, hCR⟩ := jonesSol_decay hL (expImMeasure_absolutelyContinuous ε ν hνL) hL10
    (θ := upperTheta ε σ) (norm_upperTheta_le hσ1)
  have h₂ : Tendsto (fun z ↦ ‖(cutoff z : ℂ) * Complex.exp (-(I * ε * z)) *
      jonesSol (expImMeasure ε ν) (upperTheta ε σ) z‖ * Real.exp (-ε * |z.im|))
      (cocompact ℂ) (𝓝 0) := by
    have hlim : Tendsto (fun z : ℂ ↦ max C 0 / ‖z‖ ^ 2) (cocompact ℂ) (𝓝 0) :=
      tendsto_const_nhds.div_atTop
        ((tendsto_pow_atTop two_ne_zero).comp tendsto_norm_cocompact_atTop)
    refine squeeze_zero' (Eventually.of_forall fun z ↦ by positivity) ?_ hlim
    filter_upwards [tendsto_norm_cocompact_atTop.eventually_ge_atTop (max R 1)] with z hz
    have hz0 : 0 < ‖z‖ := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hz)
    rcases le_or_gt z.im 0 with hzi | hzi
    · simp [cutoff_eq_zero (hzi.trans zero_le_one)]
      positivity
    · exact (norm_cutoff_mul_le ε _ z).trans ((hCR z hzi.le ((le_max_left _ _).trans hz)).trans
        (div_le_div_of_nonneg_right (le_max_left _ _) (by positivity)))
  -- `u₃ = k * g`
  obtain ⟨M, hM⟩ := upperG_bounded hε hνL hL10 hσ1
  have h₃ := tendsto_kerSol_volume hε (continuous_upperG hε hL hνL hL10 hσ hσ1).aestronglyMeasurable
    hM (fun z hz ↦ abs_im_le_of_upperG_ne_zero ε ν σ hz) (tendsto_upperG hε hL hνL hL10 hσ1)
  have hsum := h₂.add h₃
  rw [add_zero] at hsum
  refine squeeze_zero (fun z ↦ by positivity) (fun z ↦ ?_) hsum
  rw [← add_mul]
  gcongr
  exact norm_sub_le _ _

end Hyp

/-- **The estimate on `ℝ`** for the upper part: `|u₂(x) - u₃(x)| = |u₃(x)| ≤ C(ε, K)`. -/
theorem norm_upperSol_real_le {ε : ℝ} (hε : 0 < ε) (K : ℝ≥0) :
    ∃ C : ℝ, ∀ (ν : Measure ℂ) (σ : ℂ → ℂ) (L : Set ℂ), IsFiniteMeasure ν → ν Lᶜ = 0 →
      (∀ w ∈ L, 10 ≤ w.im) → (∀ z, ‖σ z‖ ≤ 1) → IsCarlesonLarge (expImMeasure ε ν) K →
      ∀ x : ℝ, ‖upperSol ε ν σ x‖ ≤ C := by
  obtain ⟨C₀, hC₀⟩ := norm_upperG_le hε
  set M : ℝ≥0 := (C₀ * Real.exp (12 * K)).toNNReal
  set Kv : ℝ≥0 := Real.toNNReal (2 * (2 - 1))
  refine ⟨M * (6 * Real.exp (ε * 2) / (Real.pi * ε)) * Kv,
    fun ν σ L hν hνL hL10 hσ1 hC x ↦ ?_⟩
  have hgM : ∀ z, ‖upperG ε ν σ z‖ ≤ M := fun z ↦
    (hC₀ K ν σ L hν hνL hL10 hσ1 hC z).trans (Real.le_coe_toNNReal _)
  -- on `ℝ`, `φ = 0`, so `upperSol = -u₃`
  have hx : upperSol ε ν σ x = -kerSol ε (volume.restrict {z : ℂ | 1 ≤ z.im ∧ z.im ≤ 2})
      (upperG ε ν σ) x := by
    rw [upperSol, cutoff_eq_zero (by simp), ← kerSol_volume_eq_restrict ε
      fun z hz ↦ upperG_eq_zero_of_notMem ε ν σ hz]
    simp
  have hCv : IsCarlesonLarge (volume.restrict {z : ℂ | 1 ≤ z.im ∧ z.im ≤ 2}) Kv :=
    (isCarlesonWith_volume_strip (a := 1) (b := 2) (by norm_num)).isCarlesonLarge
  have hE := enorm_kerSol_real_le hε hCv hgM (b := 2)
    (ae_of_all _ fun z hz ↦ abs_im_le_of_upperG_ne_zero ε ν σ hz) x
  -- the disc `D(x, 1)` does not meet the strip
  have hball : ∫⁻ ζ in ball (x : ℂ) 1, (‖(x : ℂ) - ζ‖₊ : ℝ≥0∞)⁻¹
      ∂(volume.restrict {z : ℂ | 1 ≤ z.im ∧ z.im ≤ 2}) = 0 := by
    rw [Measure.restrict_restrict measurableSet_ball]
    have hempty : ball (x : ℂ) 1 ∩ {z : ℂ | 1 ≤ z.im ∧ z.im ≤ 2} = ∅ := by
      ext z
      simp only [mem_inter_iff, mem_ball, mem_empty_iff_false, iff_false, not_and]
      intro hz h1
      have h1' : 1 ≤ z.im := h1.1
      have : |z.im| < 1 := by
        calc |z.im| = |(z - x).im| := by simp
          _ ≤ ‖z - x‖ := abs_im_le_norm _
          _ < 1 := by rwa [dist_eq_norm] at hz
      rw [abs_lt] at this
      linarith [this.2, h1']
    rw [hempty, Measure.restrict_empty, lintegral_zero_measure]
  rw [hball, mul_zero, zero_add] at hE
  rw [hx, norm_neg]
  have hpos : 0 ≤ (M : ℝ) * (6 * Real.exp (ε * 2) / (Real.pi * ε)) * Kv := by positivity
  rw [← ENNReal.ofReal_le_ofReal_iff hpos, ofReal_norm]
  refine hE.trans (le_of_eq ?_)
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_coe_nnreal]
  ring

end OCS
