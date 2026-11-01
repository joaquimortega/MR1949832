import OrtegaCerdaSeip.Lemma4.Upper
import OrtegaCerdaSeip.Lemma4.Weak

/-!
# M05 (Lemma 4) — assembly: `lemma4`, `theoremOCS`

See `blueprint/M05_Lemma4.md` (§1.5–§1.6).

`lemma4Sol ε ν σ = u₁ + (u₂ - u₃)⁺ + (u₂ - u₃)⁻`, where (with `μ = σν`)
* `u₁ = kerSol ε (ν|_{|Im| < 10}) σ` (p. 409);
* `(u₂ - u₃)⁺ = upperSol ε (ν|_{Im ≥ 10}) σ` (p. 410, Jones' solution `v₁` in `ℂ⁺`);
* `(u₂ - u₃)⁻` is obtained from `upperSol` by the reflection `z ↦ z̄` applied to `ν|_{Im ≤ -10}`
  (the paper's `v₂` in the lower half-plane).

`lemma4_strong` is the master statement: large-scale Carleson hypothesis (needed for the application
on p. 410, see `blueprint/M03_Carleson.md` §3), `|σ| ≤ 1`, and all four conclusions of
`TheoremOCS` together with the estimate of Lemma 4 at every `x ∈ ℝ`.  `lemma4` and `theoremOCS`
(statements of `comparator/statements.lean`) follow.
-/

open MeasureTheory Metric Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace OCS

/-- `|σ ∘ conj| ≤ 1` when `|σ| ≤ 1` (helper for the lower half-plane piece). -/
theorem norm_reflectFun_le_one_aux {σ : ℂ → ℂ} (hσ1 : ∀ z, ‖σ z‖ ≤ 1) (z : ℂ) :
    ‖reflectFun σ z‖ ≤ 1 := by
  rw [norm_reflectFun]
  exact hσ1 _

/-- The solution of Lemma 4: `u₁ + (u₂ - u₃)` on the three pieces `|Im| < 10`, `Im ≥ 10`,
`Im ≤ -10` of the measure. -/
def lemma4Sol (ε : ℝ) (ν : Measure ℂ) (σ : ℂ → ℂ) (z : ℂ) : ℂ :=
  kerSol ε (ν.restrict {w | |w.im| < 10}) σ z + upperSol ε (ν.restrict {w | 10 ≤ w.im}) σ z +
    reflectFun (upperSol ε ((ν.restrict {w | w.im ≤ -10}).map (starRingEnd ℂ)) (reflectFun σ)) z

/-! ## The three pieces of the measure -/

theorem measurableSet_abs_im_lt : MeasurableSet {w : ℂ | |w.im| < 10} :=
  measurableSet_lt (by fun_prop) measurable_const

theorem measurableSet_ten_le_im : MeasurableSet {w : ℂ | 10 ≤ w.im} :=
  measurableSet_le measurable_const measurable_im

theorem measurableSet_im_le_neg_ten : MeasurableSet {w : ℂ | w.im ≤ -10} :=
  measurableSet_le measurable_im measurable_const

theorem isClosed_ten_le_im : IsClosed {w : ℂ | 10 ≤ w.im} :=
  isClosed_le continuous_const continuous_im

theorem isClosed_im_le_neg_ten : IsClosed {w : ℂ | w.im ≤ -10} :=
  isClosed_le continuous_im continuous_const

theorem map_conj_map_conj (μ : Measure ℂ) :
    (μ.map (starRingEnd ℂ)).map (starRingEnd ℂ) = μ := by
  rw [Measure.map_map continuous_conj.measurable continuous_conj.measurable]
  have h : (starRingEnd ℂ) ∘ (starRingEnd ℂ) = id := by
    funext z
    simp
  rw [h, Measure.map_id]

/-- The three pieces of `ν`. -/
theorem restrict_add_restrict_add_restrict (ν : Measure ℂ) :
    ν.restrict {w | |w.im| < 10} + ν.restrict {w | 10 ≤ w.im} +
      ((ν.restrict {w | w.im ≤ -10}).map (starRingEnd ℂ)).map (starRingEnd ℂ) = ν := by
  rw [map_conj_map_conj, ← Measure.restrict_union _ measurableSet_ten_le_im,
    ← Measure.restrict_union _ measurableSet_im_le_neg_ten]
  · have h : {w : ℂ | |w.im| < 10} ∪ {w | 10 ≤ w.im} ∪ {w | w.im ≤ -10} = univ := by
      ext w
      simp only [mem_union, mem_univ, iff_true]
      rcases lt_or_ge w.im 10 with h1 | h1
      · rcases le_or_gt w.im (-10) with h2 | h2
        · exact Or.inr h2
        · exact Or.inl (Or.inl (abs_lt.2 ⟨h2, h1⟩))
      · exact Or.inl (Or.inr h1)
    rw [h, Measure.restrict_univ]
  · refine Set.disjoint_left.2 fun w hw (h2 : w.im ≤ -10) ↦ ?_
    rcases hw with (h1 : |w.im| < 10) | (h1 : 10 ≤ w.im)
    · linarith [(abs_lt.1 h1).1]
    · linarith
  · exact Set.disjoint_left.2 fun w (h1 : |w.im| < 10) (h2 : 10 ≤ w.im) ↦ by
      linarith [(abs_lt.1 h1).2]

/-- The compact set carrying the reflected lower piece `conj_*(ν|_{Im ≤ -10})`. -/
theorem isCompact_lowerSet {L : Set ℂ} (hL : IsCompact L) :
    IsCompact (starRingEnd ℂ ⁻¹' (L ∩ {w | w.im ≤ -10})) := by
  rw [← Set.image_eq_preimage_of_inverse (f := starRingEnd ℂ) (fun z ↦ by simp)
    (fun z ↦ by simp)]
  exact (hL.inter_right isClosed_im_le_neg_ten).image continuous_conj

theorem ten_le_im_of_mem_lowerSet {L : Set ℂ} {w : ℂ}
    (hw : w ∈ starRingEnd ℂ ⁻¹' (L ∩ {w | w.im ≤ -10})) : 10 ≤ w.im := by
  have h : (conj w).im ≤ -10 := hw.2
  rw [Complex.conj_im] at h
  linarith

theorem restrict_upper_compl_eq_zero {ν : Measure ℂ} {L : Set ℂ} (hνL : ν Lᶜ = 0) :
    ν.restrict {w | 10 ≤ w.im} (L ∩ {w | 10 ≤ w.im})ᶜ = 0 := by
  rw [Measure.restrict_apply' measurableSet_ten_le_im]
  exact measure_mono_null (fun z hz hzL ↦ hz.1 ⟨hzL, hz.2⟩) hνL

theorem map_lower_compl_eq_zero {ν : Measure ℂ} {L : Set ℂ} (hL : IsCompact L) (hνL : ν Lᶜ = 0) :
    (ν.restrict {w | w.im ≤ -10}).map (starRingEnd ℂ)
      (starRingEnd ℂ ⁻¹' (L ∩ {w | w.im ≤ -10}))ᶜ = 0 := by
  rw [Measure.map_apply continuous_conj.measurable
    (isCompact_lowerSet hL).isClosed.measurableSet.compl,
    Measure.restrict_apply' measurableSet_im_le_neg_ten]
  refine measure_mono_null (fun z hz ↦ ?_) hνL
  show z ∉ L
  intro hzL
  apply hz.1
  simp only [mem_preimage, Complex.conj_conj]
  exact ⟨hzL, hz.2⟩

/-- The Carleson hypothesis passes to the upper piece. -/
theorem isCarlesonLarge_upper {ε : ℝ} {ν : Measure ℂ} {K : ℝ≥0}
    (hC : IsCarlesonLarge (expImMeasure ε ν) K) :
    IsCarlesonLarge (expImMeasure ε (ν.restrict {w | 10 ≤ w.im})) K := by
  rw [expImMeasure_restrict ε ν measurableSet_ten_le_im]
  exact hC.mono Measure.restrict_le_self

/-- The Carleson hypothesis passes to the reflected lower piece. -/
theorem isCarlesonLarge_lower {ε : ℝ} {ν : Measure ℂ} {K : ℝ≥0}
    (hC : IsCarlesonLarge (expImMeasure ε ν) K) :
    IsCarlesonLarge (expImMeasure ε ((ν.restrict {w | w.im ≤ -10}).map (starRingEnd ℂ))) K := by
  rw [expImMeasure_map_conj, expImMeasure_restrict ε ν measurableSet_im_le_neg_ten]
  exact (hC.mono Measure.restrict_le_self).map_conj

theorem measure_mono_null_restrict {ν : Measure ℂ} {L s : Set ℂ} (hνL : ν Lᶜ = 0) :
    ν.restrict s Lᶜ = 0 :=
  nonpos_iff_eq_zero.1 ((Measure.restrict_apply_le s Lᶜ).trans hνL.le)

section Hyp

variable {ε : ℝ} {ν : Measure ℂ} [IsFiniteMeasure ν] {σ : ℂ → ℂ} {L : Set ℂ}

theorem lemma4Sol_isWeakDbarSolMeasure (hε : 0 < ε) (hL : IsCompact L) (hνL : ν Lᶜ = 0)
    (hσ : Measurable σ) (hσ1 : ∀ z, ‖σ z‖ ≤ 1) :
    IsWeakDbarSolMeasure (lemma4Sol ε ν σ) ν σ := by
  -- `u₁`: the strip `|Im| < 10`
  have h₁ : IsWeakDbarSolMeasure (kerSol ε (ν.restrict {w | |w.im| < 10}) σ)
      (ν.restrict {w | |w.im| < 10}) σ :=
    kerSol_isWeakDbarSolMeasure hε (Integrable.of_bound hσ.aestronglyMeasurable 1
      (ae_of_all _ hσ1)) (b := 10)
      ((ae_restrict_mem measurableSet_abs_im_lt).mono fun z hz _ ↦ le_of_lt hz)
  -- `u₂ - u₃` for `Im ≥ 10`
  have h₂ := upperSol_isWeakDbarSolMeasure (ν := ν.restrict {w | 10 ≤ w.im}) hε
    (hL.inter_right isClosed_ten_le_im) (restrict_upper_compl_eq_zero hνL) (fun w hw ↦ hw.2)
    hσ hσ1
  -- the reflection of `u₂ - u₃` for `Im ≤ -10`
  have h₃ := (upperSol_isWeakDbarSolMeasure hε (isCompact_lowerSet hL)
    (map_lower_compl_eq_zero hL hνL) (fun w hw ↦ ten_le_im_of_mem_lowerSet hw)
    (measurable_reflectFun hσ) (norm_reflectFun_le_one_aux hσ1)).reflect
  rw [reflectFun_reflectFun] at h₃
  have h := (h₁.add hσ hσ1 h₂).add hσ hσ1 h₃
  rw [restrict_add_restrict_add_restrict] at h
  exact h

theorem continuousOn_lemma4Sol (hε : 0 < ε) (hL : IsCompact L) (hνL : ν Lᶜ = 0)
    (hσ : Measurable σ) (hσ1 : ∀ z, ‖σ z‖ ≤ 1) :
    ContinuousOn (lemma4Sol ε ν σ) Lᶜ := by
  have c₁ : ContinuousOn (kerSol ε (ν.restrict {w | |w.im| < 10}) σ) Lᶜ :=
    continuousOn_kerSol hε hL (measure_mono_null_restrict hνL) hσ.aestronglyMeasurable hσ1
  have c₂ : ContinuousOn (upperSol ε (ν.restrict {w | 10 ≤ w.im}) σ) Lᶜ :=
    (continuousOn_upperSol hε (hL.inter_right isClosed_ten_le_im)
      (restrict_upper_compl_eq_zero hνL) (fun w hw ↦ hw.2) hσ hσ1).mono
      (compl_subset_compl.2 inter_subset_left)
  have c₃ : ContinuousOn
      (reflectFun (upperSol ε ((ν.restrict {w | w.im ≤ -10}).map (starRingEnd ℂ))
        (reflectFun σ))) Lᶜ := by
    refine (continuousOn_reflectFun (continuousOn_upperSol hε (isCompact_lowerSet hL)
      (map_lower_compl_eq_zero hL hνL) (fun w hw ↦ ten_le_im_of_mem_lowerSet hw)
      (measurable_reflectFun hσ) (norm_reflectFun_le_one_aux hσ1))).mono fun z hz hz' ↦ ?_
    simp only [mem_preimage, Complex.conj_conj] at hz'
    exact hz hz'.1
  exact (c₁.add c₂).add c₃

theorem tendsto_lemma4Sol (hε : 0 < ε) (hL : IsCompact L) (hνL : ν Lᶜ = 0)
    (hσ : Measurable σ) (hσ1 : ∀ z, ‖σ z‖ ≤ 1) :
    Tendsto (fun z ↦ ‖lemma4Sol ε ν σ z‖ * Real.exp (-ε * |z.im|)) (cocompact ℂ) (𝓝 0) := by
  have t₁ := tendsto_kerSol hε (ν := ν.restrict {w | |w.im| < 10}) hL
    (measure_mono_null_restrict hνL) hσ.aestronglyMeasurable hσ1
  have t₂ := tendsto_upperSol (ν := ν.restrict {w | 10 ≤ w.im}) hε
    (hL.inter_right isClosed_ten_le_im) (restrict_upper_compl_eq_zero hνL) (fun w hw ↦ hw.2)
    hσ hσ1
  have t₃ := tendsto_reflectFun (tendsto_upperSol hε (isCompact_lowerSet hL)
    (map_lower_compl_eq_zero hL hνL) (fun w hw ↦ ten_le_im_of_mem_lowerSet hw)
    (measurable_reflectFun hσ) (norm_reflectFun_le_one_aux hσ1))
  have hsum := (t₁.add t₂).add t₃
  rw [add_zero, add_zero] at hsum
  refine squeeze_zero (fun z ↦ by positivity) (fun z ↦ ?_) hsum
  simp only [← add_mul]
  gcongr
  exact norm_add₃_le

end Hyp

/-- The estimate of Lemma 4 on `ℝ`, with a constant depending only on `ε` and `K`. -/
theorem lemma4Sol_real_le {ε : ℝ} (hε : 0 < ε) (K : ℝ≥0) :
    ∃ C : ℝ≥0, ∀ (ν : Measure ℂ) (σ : ℂ → ℂ) (L : Set ℂ), IsFiniteMeasure ν → IsCompact L →
      ν Lᶜ = 0 → (∀ z, ‖σ z‖ ≤ 1) → IsCarlesonLarge (expImMeasure ε ν) K →
      ∀ x : ℝ, ENNReal.ofReal ‖lemma4Sol ε ν σ x‖ ≤
        C * (1 + ∫⁻ z in ball (x : ℂ) 1, (‖(x : ℂ) - z‖₊ : ℝ≥0∞)⁻¹ ∂ν) := by
  obtain ⟨Cp, hCp⟩ := norm_upperSol_real_le hε K
  -- constants of `u₁` (kernel bound with `b = 10`, Carleson constant `e^{10ε} K` of `ν₁`)
  set a : ℝ≥0 := (Real.exp (ε * 10) / Real.pi).toNNReal with ha
  set b : ℝ≥0 := (6 * Real.exp (ε * 10) / (Real.pi * ε)).toNNReal *
    ((Real.exp (ε * 10)).toNNReal * K) + 2 * Cp.toNNReal with hb
  refine ⟨max a b, fun ν σ L hν hL hνL hσ1 hC x ↦ ?_⟩
  set I := ∫⁻ z in ball (x : ℂ) 1, (‖(x : ℂ) - z‖₊ : ℝ≥0∞)⁻¹ ∂ν
  -- `u₁`
  have hb₁ : ∀ᵐ z ∂ν.restrict {w | |w.im| < 10}, |z.im| ≤ 10 :=
    (ae_restrict_mem measurableSet_abs_im_lt).mono fun z hz ↦ le_of_lt hz
  have hC₁ : IsCarlesonLarge (ν.restrict {w | |w.im| < 10})
      ((Real.exp (ε * 10)).toNNReal * K) := by
    refine IsCarlesonLarge.of_expImMeasure hε.le ?_ hb₁
    rw [expImMeasure_restrict ε ν measurableSet_abs_im_lt]
    exact hC.mono Measure.restrict_le_self
  have h₁ := enorm_kerSol_real_le hε hC₁ (M := 1) (θ := σ) (fun ζ ↦ by simpa using hσ1 ζ)
    (hb₁.mono fun z hz _ ↦ hz) x
  have hI : ∫⁻ ζ in ball (x : ℂ) 1, (‖(x : ℂ) - ζ‖₊ : ℝ≥0∞)⁻¹ ∂ν.restrict {w | |w.im| < 10} ≤ I :=
    lintegral_mono' (Measure.restrict_mono subset_rfl Measure.restrict_le_self) le_rfl
  -- `u₂ - u₃` and its reflection
  have h₂ : ‖upperSol ε (ν.restrict {w | 10 ≤ w.im}) σ x‖ ≤ Cp :=
    hCp _ σ _ inferInstance (restrict_upper_compl_eq_zero hνL) (fun w hw ↦ hw.2) hσ1
      (isCarlesonLarge_upper hC) x
  have h₃ : ‖reflectFun (upperSol ε ((ν.restrict {w | w.im ≤ -10}).map (starRingEnd ℂ))
      (reflectFun σ)) x‖ ≤ Cp := by
    rw [norm_reflectFun, Complex.conj_ofReal]
    exact hCp _ _ _ inferInstance (map_lower_compl_eq_zero hL hνL)
      (fun w hw ↦ ten_le_im_of_mem_lowerSet hw) (norm_reflectFun_le_one_aux hσ1)
      (isCarlesonLarge_lower hC) x
  -- assembly
  have hmax_a : (a : ℝ≥0∞) ≤ max a b := by exact_mod_cast le_max_left a b
  have hmax_b : (b : ℝ≥0∞) ≤ max a b := by exact_mod_cast le_max_right a b
  have hb' : (b : ℝ≥0∞) = ENNReal.ofReal (6 * Real.exp (ε * 10) / (Real.pi * ε)) *
      ((Real.exp (ε * 10)).toNNReal * K : ℝ≥0) + ENNReal.ofReal Cp + ENNReal.ofReal Cp := by
    rw [hb]
    push_cast
    rw [ENNReal.ofReal, ENNReal.ofReal]
    ring
  calc ENNReal.ofReal ‖lemma4Sol ε ν σ x‖
      ≤ ENNReal.ofReal (‖kerSol ε (ν.restrict {w | |w.im| < 10}) σ x‖ +
          ‖upperSol ε (ν.restrict {w | 10 ≤ w.im}) σ x‖ +
          ‖reflectFun (upperSol ε ((ν.restrict {w | w.im ≤ -10}).map (starRingEnd ℂ))
            (reflectFun σ)) x‖) := ENNReal.ofReal_le_ofReal norm_add₃_le
    _ ≤ ‖kerSol ε (ν.restrict {w | |w.im| < 10}) σ x‖ₑ + ENNReal.ofReal Cp +
          ENNReal.ofReal Cp := by
        rw [ENNReal.ofReal_add (by positivity) (norm_nonneg _),
          ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _), ofReal_norm]
        gcongr
    _ ≤ (ENNReal.ofReal (Real.exp (ε * 10) / Real.pi) * I +
          ENNReal.ofReal (6 * Real.exp (ε * 10) / (Real.pi * ε)) *
            ((Real.exp (ε * 10)).toNNReal * K : ℝ≥0)) + ENNReal.ofReal Cp +
          ENNReal.ofReal Cp := by
        gcongr
        refine h₁.trans ?_
        rw [ENNReal.coe_one, one_mul]
        gcongr
    _ = a * I + b := by
        rw [hb', ha, ENNReal.ofReal]
        ring
    _ ≤ max a b * I + max a b := by gcongr
    _ = max a b * (1 + I) := by ring

/-- **Lemma 4, strong form** (master statement).  Large-scale Carleson hypothesis, `|σ| ≤ 1`;
conclusions: weak equation, holomorphy off `L`, `|u(z)| e^{-ε|Im z|} → 0`, and the estimate on `ℝ`
with `C = C(ε, K)`. -/
theorem lemma4_strong {ε : ℝ} (hε : 0 < ε) (K : ℝ≥0) :
    ∃ C : ℝ≥0, ∀ (ν : Measure ℂ) (σ : ℂ → ℂ) (L : Set ℂ),
      IsFiniteMeasure ν → IsCompact L → ν Lᶜ = 0 → Measurable σ → (∀ z, ‖σ z‖ ≤ 1) →
      IsCarlesonLarge (expImMeasure ε ν) K →
      IsWeakDbarSolMeasure (lemma4Sol ε ν σ) ν σ ∧ DifferentiableOn ℂ (lemma4Sol ε ν σ) Lᶜ ∧
        Tendsto (fun z ↦ ‖lemma4Sol ε ν σ z‖ * Real.exp (-ε * |z.im|)) (cocompact ℂ) (𝓝 0) ∧
        ∀ x : ℝ, ENNReal.ofReal ‖lemma4Sol ε ν σ x‖ ≤
          C * (1 + ∫⁻ z in ball (x : ℂ) 1, (‖(x : ℂ) - z‖₊ : ℝ≥0∞)⁻¹ ∂ν) := by
  obtain ⟨C, hC⟩ := lemma4Sol_real_le hε K
  refine ⟨C, fun ν σ L hν hL hνL hσ hσ1 hCar ↦ ?_⟩
  have hw := lemma4Sol_isWeakDbarSolMeasure hε hL hνL hσ hσ1
  exact ⟨hw, hw.differentiableOn hL.isClosed hνL (continuousOn_lemma4Sol hε hL hνL hσ hσ1),
    tendsto_lemma4Sol hε hL hνL hσ hσ1, hC ν σ L hν hL hνL hσ1 hCar⟩

/-- **Lemma 4** (p. 409), as printed: the complex measure `μ` is `σ ν` with `ν = |μ|`. -/
theorem lemma4 {ε : ℝ} (hε : 0 < ε) (K : ℝ≥0) :
    ∃ C : ℝ≥0, ∀ (ν : Measure ℂ) (σ : ℂ → ℂ), IsFiniteMeasure ν →
      (∃ L : Set ℂ, IsCompact L ∧ ν Lᶜ = 0) → Measurable σ → (∀ z, ‖σ z‖ = 1) →
      (∀ x : ℝ, ∀ r : ℝ, 0 < r →
        (ν.withDensity fun z ↦ ENNReal.ofReal (Real.exp (-ε * |z.im|))) (ball (x : ℂ) r) ≤
          K * ENNReal.ofReal r) →
      ∃ u : ℂ → ℂ, IsWeakDbarSolMeasure u ν σ ∧
        (∃ M R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ → ‖u z‖ * Real.exp (-ε * |z.im|) ≤ M) ∧
        ∀ x : ℝ, ENNReal.ofReal ‖u x‖ ≤
          C * (1 + ∫⁻ z in ball (x : ℂ) 1, (‖(x : ℂ) - z‖₊ : ℝ≥0∞)⁻¹ ∂ν) := by
  obtain ⟨C, hC⟩ := lemma4_strong hε K
  refine ⟨C, fun ν σ hν ⟨L, hL, hνL⟩ hσ hσ1 hCar ↦ ?_⟩
  have hCL : IsCarlesonLarge (expImMeasure ε ν) K := fun x r hr ↦
    hCar x r (zero_lt_one.trans_le hr)
  obtain ⟨hw, -, ht, hx⟩ := hC ν σ L hν hL hνL hσ (fun z ↦ (hσ1 z).le) hCL
  refine ⟨lemma4Sol ε ν σ, hw, ?_, hx⟩
  -- `|u(z)| e^{-ε|Im z|} → 0`, so it is `≤ 1` for `|z| ≥ R`
  have hev : ∀ᶠ z in cocompact ℂ, ‖lemma4Sol ε ν σ z‖ * Real.exp (-ε * |z.im|) ≤ 1 :=
    ht.eventually (Iic_mem_nhds one_pos)
  rw [← Metric.cobounded_eq_cocompact, ← comap_norm_atTop, Filter.eventually_comap,
    Filter.eventually_atTop] at hev
  obtain ⟨R, hR⟩ := hev
  exact ⟨1, R, fun z hz ↦ hR ‖z‖ hz z rfl⟩

/-- **Lemma 4 in the form quoted in MR1949832** (`OC.TheoremOCS`): `limsup = 0`, and `u` is
holomorphic off the support. -/
theorem theoremOCS : TheoremOCS := by
  intro α hα K
  obtain ⟨C, hC⟩ := lemma4_strong hα K
  refine ⟨C, fun ν σ L hν hL hνL hσ hσ1 hCar ↦ ?_⟩
  have hCL : IsCarlesonLarge (expImMeasure α ν) K := fun x r hr ↦
    hCar x r (zero_lt_one.trans_le hr)
  obtain ⟨hw, hd, ht, hx⟩ := hC ν σ L hν hL hνL hσ (fun z ↦ (hσ1 z).le) hCL
  refine ⟨lemma4Sol α ν σ, hw, hd, ht, fun x hxL ↦ (hx x).trans ?_⟩
  -- off `L`, `ν{x} = 0`, so the two integrands agree `ν`-a.e.
  have hx0 : ∀ᵐ z ∂ν, z ≠ (x : ℂ) :=
    measure_mono_null (fun z (hz : ¬z ≠ (x : ℂ)) ↦ by rwa [not_not.1 hz]) hνL
  gcongr _ * (1 + ?_)
  refine lintegral_mono_ae ?_
  filter_upwards [ae_restrict_of_ae hx0] with z hz
  have hpos : 0 < ‖(x : ℂ) - z‖ := norm_pos_iff.2 (sub_ne_zero.2 hz.symm)
  rw [one_div, ENNReal.ofReal_inv_of_pos hpos, ofReal_norm, enorm_eq_nnnorm]

end OCS
