import OrtegaCerdaSeip.Foundations.Weyl

/-!
# M05 (Lemma 4) — generic facts on `IsWeakDbarSolMeasure`: sums, reflection, holomorphy

See `blueprint/M05_Lemma4.md` (§1.4).

* `IsWeakDbarSolMeasure.add`: `∂̄u₁ = σν₁`, `∂̄u₂ = σν₂` ⇒ `∂̄(u₁ + u₂) = σ(ν₁ + ν₂)`;
* `IsWeakDbarSolMeasure.reflect`: if `∂̄u = σν` then
  `∂̄(conj ∘ u ∘ conj) = (conj ∘ σ ∘ conj) · conj_*ν`.
  This turns the solution for the part of `μ` in `Im z ≥ 10` into the one for `Im z ≤ -10`
  (the paper's `v₂`, "analogously", p. 410);
* `IsWeakDbarSolMeasure.differentiableOn`: a solution that is continuous off a closed set `L`
  carrying `ν` is holomorphic off `L` (Weyl's lemma, `differentiableOn_of_isWeakDbarSol_zero`).
-/

open MeasureTheory Metric Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace OCS

/-- `z ↦ conj (f (conj z))`. -/
def reflectFun (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  conj (f (conj z))

theorem reflectFun_reflectFun (f : ℂ → ℂ) : reflectFun (reflectFun f) = f := by
  funext z
  simp [reflectFun]

theorem norm_reflectFun (f : ℂ → ℂ) (z : ℂ) : ‖reflectFun f z‖ = ‖f (conj z)‖ := by
  simp [reflectFun]

theorem reflectFun_ofReal (f : ℂ → ℂ) (x : ℝ) : reflectFun f x = conj (f x) := by
  simp [reflectFun]

theorem measurable_reflectFun {f : ℂ → ℂ} (hf : Measurable f) : Measurable (reflectFun f) :=
  Complex.continuous_conj.measurable.comp (hf.comp Complex.continuous_conj.measurable)

theorem continuousOn_reflectFun {f : ℂ → ℂ} {s : Set ℂ} (hf : ContinuousOn f s) :
    ContinuousOn (reflectFun f) (starRingEnd ℂ ⁻¹' s) :=
  Complex.continuous_conj.comp_continuousOn
    (hf.comp Complex.continuous_conj.continuousOn (mapsTo_preimage _ _))

theorem dbar_reflectFun {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f (conj z)) :
    dbar (reflectFun f) z = conj (dbar f (conj z)) := by
  have hc : HasFDerivAt (fun w : ℂ ↦ conj w) (conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap z :=
    (conjCLE : ℂ ≃L[ℝ] ℂ).hasFDerivAt
  have hcomp : HasFDerivAt (fun w ↦ f (conj w))
      ((fderiv ℝ f (conj z)).comp (conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap) z :=
    hf.hasFDerivAt.comp z hc
  have h1 : ∀ v, fderiv ℝ (reflectFun f) z v = conj (fderiv ℝ f (conj z) (conj v)) := by
    intro v
    rw [show reflectFun f = fun w ↦ conj ((fun w ↦ f (conj w)) w) from rfl,
      fderiv_conj_apply hcomp.differentiableAt, hcomp.fderiv]
    simp
  simp only [dbar, h1, map_one, Complex.conj_I, map_neg, map_add, map_mul, map_div₀, map_ofNat]
  ring

/-- `conj` maps `cocompact ℂ` to itself. -/
theorem tendsto_starRingEnd_cocompact : Tendsto (starRingEnd ℂ) (cocompact ℂ) (cocompact ℂ) :=
  Complex.conjLIE.toHomeomorph.map_cocompact.le

theorem tendsto_reflectFun {f : ℂ → ℂ} {ε : ℝ}
    (h : Tendsto (fun z ↦ ‖f z‖ * Real.exp (-ε * |z.im|)) (cocompact ℂ) (𝓝 0)) :
    Tendsto (fun z ↦ ‖reflectFun f z‖ * Real.exp (-ε * |z.im|)) (cocompact ℂ) (𝓝 0) :=
  Tendsto.congr (fun z ↦ by simp [reflectFun, Complex.conj_im])
    (h.comp tendsto_starRingEnd_cocompact)

theorem volume_preserving_conj : MeasurePreserving (starRingEnd ℂ) (volume : Measure ℂ) volume :=
  Complex.conjLIE.measurePreserving

theorem measurableEmbedding_starRingEnd : MeasurableEmbedding (starRingEnd ℂ) :=
  Complex.conjLIE.toHomeomorph.measurableEmbedding

theorem reflectFun_locallyIntegrable {u : ℂ → ℂ} (hu : LocallyIntegrable u) :
    LocallyIntegrable (reflectFun u) := by
  rw [locallyIntegrable_iff] at hu ⊢
  intro K hK
  have hK' : IsCompact (starRingEnd ℂ ⁻¹' K) := by
    have h := hK.image Complex.continuous_conj
    convert h using 1
    ext z
    simp only [mem_preimage, mem_image]
    exact ⟨fun hz ↦ ⟨conj z, hz, by simp⟩, fun ⟨w, hw, hwz⟩ ↦ by rw [← hwz]; simpa using hw⟩
  have hpre : starRingEnd ℂ ⁻¹' (starRingEnd ℂ ⁻¹' K) = K := by
    ext z; simp
  have h1 : IntegrableOn (u ∘ starRingEnd ℂ) K := by
    rw [← hpre]
    exact (volume_preserving_conj.integrableOn_comp_preimage
      measurableEmbedding_starRingEnd).2 (hu _ hK')
  exact h1.congr' (Complex.continuous_conj.comp_aestronglyMeasurable h1.1)
    (Eventually.of_forall fun z ↦ by simp [OCS.reflectFun])

/-- **Reflection of weak solutions.** -/
theorem IsWeakDbarSolMeasure.reflect {u : ℂ → ℂ} {ν : Measure ℂ} {σ : ℂ → ℂ}
    (h : IsWeakDbarSolMeasure u ν σ) :
    IsWeakDbarSolMeasure (reflectFun u) (ν.map (starRingEnd ℂ)) (reflectFun σ) := by
  obtain ⟨hloc, hweak⟩ := h
  refine ⟨reflectFun_locallyIntegrable hloc, fun β hβ hβc ↦ ?_⟩
  set α := reflectFun β with hα_def
  have hα : ContDiff ℝ (⊤ : ℕ∞) α :=
    (conjCLE : ℂ ≃L[ℝ] ℂ).contDiff.comp (hβ.comp (conjCLE : ℂ ≃L[ℝ] ℂ).contDiff)
  have hαc : HasCompactSupport α :=
    (hβc.comp_homeomorph Complex.conjLIE.toHomeomorph).comp_left (map_zero (starRingEnd ℂ))
  have hβd : Differentiable ℝ β := hβ.differentiable (by simp)
  have hdb : ∀ z, dbar β z = conj (dbar α (conj z)) := by
    intro z
    rw [hα_def, dbar_reflectFun (by simpa using hβd (conj (conj z))), Complex.conj_conj,
      Complex.conj_conj]
  have hL : ∫ z, reflectFun u z * dbar β z = conj (∫ w, u w * dbar α w) := by
    have h1 := volume_preserving_conj.integral_comp measurableEmbedding_starRingEnd
      (fun w ↦ u w * dbar α w)
    rw [← h1, ← integral_conj]
    congr 1
    ext z
    rw [hdb z, reflectFun, map_mul]
  have hR : ∫ z, β z * reflectFun σ z ∂(ν.map (starRingEnd ℂ)) = conj (∫ w, α w * σ w ∂ν) := by
    rw [measurableEmbedding_starRingEnd.integral_map, ← integral_conj]
    congr 1
    ext w
    simp [hα_def, reflectFun, map_mul]
  rw [hL, hR, hweak α hα hαc, map_neg]

/-- **Sum of weak solutions.** -/
theorem IsWeakDbarSolMeasure.add {u₁ u₂ : ℂ → ℂ} {ν₁ ν₂ : Measure ℂ} [IsFiniteMeasure ν₁]
    [IsFiniteMeasure ν₂] {σ : ℂ → ℂ} (hσ : Measurable σ) {M : ℝ} (hσM : ∀ z, ‖σ z‖ ≤ M)
    (h₁ : IsWeakDbarSolMeasure u₁ ν₁ σ) (h₂ : IsWeakDbarSolMeasure u₂ ν₂ σ) :
    IsWeakDbarSolMeasure (u₁ + u₂) (ν₁ + ν₂) σ := by
  obtain ⟨hl₁, hw₁⟩ := h₁
  obtain ⟨hl₂, hw₂⟩ := h₂
  refine ⟨hl₁.add hl₂, fun α hα hαc ↦ ?_⟩
  have hα1 := contDiff_one_of_top hα
  have hi₁ : Integrable (fun z ↦ u₁ z * dbar α z) :=
    integrable_mul_dbar_of_locallyIntegrableOn (hl₁.locallyIntegrableOn univ) hα1 hαc
      (subset_univ _)
  have hi₂ : Integrable (fun z ↦ u₂ z * dbar α z) :=
    integrable_mul_dbar_of_locallyIntegrableOn (hl₂.locallyIntegrableOn univ) hα1 hαc
      (subset_univ _)
  obtain ⟨C, hC⟩ := hα.continuous.bounded_above_of_compact_support hαc
  have hασ : ∀ (μ : Measure ℂ) [IsFiniteMeasure μ], Integrable (fun z ↦ α z * σ z) μ :=
    fun μ _ ↦ Integrable.mono' (integrable_const (C * M))
      (hα.continuous.measurable.mul hσ).aestronglyMeasurable
      (Eventually.of_forall fun z ↦ by
        rw [norm_mul]
        exact mul_le_mul (hC z) (hσM z) (norm_nonneg _) ((norm_nonneg _).trans (hC z)))
  simp only [Pi.add_apply, add_mul]
  rw [integral_add hi₁ hi₂, hw₁ α hα hαc, hw₂ α hα hαc,
    integral_add_measure (hασ ν₁) (hασ ν₂)]
  ring

/-- **Holomorphy off the support.**  A weak solution of `∂̄u = σν` that is continuous off a closed
set `L` with `ν(Lᶜ) = 0` is holomorphic off `L`. -/
theorem IsWeakDbarSolMeasure.differentiableOn {u : ℂ → ℂ} {ν : Measure ℂ} {σ : ℂ → ℂ}
    {L : Set ℂ} (h : IsWeakDbarSolMeasure u ν σ) (hL : IsClosed L) (hνL : ν Lᶜ = 0)
    (hc : ContinuousOn u Lᶜ) : DifferentiableOn ℂ u Lᶜ := by
  refine differentiableOn_of_isWeakDbarSol_zero hL.isOpen_compl hc
    ⟨h.1.locallyIntegrableOn _, locallyIntegrable_zero.locallyIntegrableOn _,
      fun α hα hαc hαs ↦ ?_⟩
  have h0 : ∫ z, α z * σ z ∂ν = 0 := by
    refine integral_eq_zero_of_ae ?_
    filter_upwards [mem_ae_iff.2 hνL] with z hz
    rw [image_eq_zero_of_notMem_tsupport (fun h' ↦ hαs h' hz), zero_mul]
    rfl
  rw [h.2 α hα hαc, h0]
  simp

end OCS
