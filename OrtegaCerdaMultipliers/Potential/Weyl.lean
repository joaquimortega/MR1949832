import OrtegaCerdaMultipliers.Potential.Radial
import OrtegaCerdaMultipliers.Potential.Fundamental

/-!
# M02 (Potentials) §2–§3 — Weyl's lemma for `Δ`; weights up to harmonic functions

See `blueprint/M02_Potentials.md` §2–§3.  Scaffold: statements, proofs `sorry`.

The `bumpKernel` API (stated in the doc's §4.1) is placed here, next to the definition, because
the proof of Weyl's lemma uses it.  The a.e. (`L¹_loc`) form of Weyl's lemma,
`exists_harmonicOnNhd_ae_eq_of_weakHarmonic`, is added for M07's `WeylLaplacianStmt`
(consumed by M08 and M13 through `LogModulusWeak.lean`).
-/

open MeasureTheory Metric Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace OC

/-- Smooth radial probability density supported in `ball 0 s` (BOC `kernel` with
`a = s²/4`, `b = s²`). -/
def bumpKernel (s : ℝ) (x : ℂ) : ℝ := kernel (s ^ 2 / 4) (s ^ 2) x

/-! ### `bumpKernel` API (doc §4.1) -/

theorem contDiff_bumpKernel {s : ℝ} (hs : 0 < s) : ContDiff ℝ (⊤ : ℕ∞) (bumpKernel s) :=
  contDiff_kernel (bump_pos hs) (bump_lt hs)

theorem bumpKernel_nonneg {s : ℝ} (hs : 0 < s) (x : ℂ) : 0 ≤ bumpKernel s x :=
  kernel_nonneg (bump_pos hs) (bump_lt hs) x

theorem bumpKernel_eq_zero {s : ℝ} (hs : 0 < s) {x : ℂ} (hx : s ≤ ‖x‖) :
    bumpKernel s x = 0 :=
  kernel_bump_eq_zero hs hx

theorem integral_bumpKernel {s : ℝ} (hs : 0 < s) : ∫ x, bumpKernel s x = 1 :=
  integral_kernel (bump_pos hs) (bump_lt hs)

theorem bumpKernel_le {s : ℝ} (hs : 0 < s) (x : ℂ) :
    bumpKernel s x ≤ 4 / (Real.pi * s ^ 2) * (ball (0 : ℂ) s).indicator 1 x := by
  have h := kernel_le_indicator (bump_pos hs) (bump_lt hs) x
  rw [Real.sqrt_sq hs.le] at h
  have e : (Real.pi * (s ^ 2 / 4))⁻¹ = 4 / (Real.pi * s ^ 2) := by field_simp
  rw [e] at h
  exact h

theorem le_bumpKernel {s : ℝ} (hs : 0 < s) (x : ℂ) :
    1 / (Real.pi * s ^ 2) * (ball (0 : ℂ) (s / 2)).indicator 1 x ≤ bumpKernel s x := by
  have h := indicator_le_kernel (bump_pos hs) (bump_lt hs) x
  have e : Real.sqrt (s ^ 2 / 4) = s / 2 := by
    rw [show s ^ 2 / 4 = (s / 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  rw [e, ← one_div] at h
  exact h

/-- `profMass (s²/4) s² = s² · profMass (1/4) 1` for every `s` (both sides vanish at `0`). -/
theorem profMass_bump (s : ℝ) :
    profMass (s ^ 2 / 4) (s ^ 2) = s ^ 2 * profMass (1 / 4) 1 := by
  rcases eq_or_ne s 0 with rfl | hs
  · simp [profMass]
  · have h := profMass_scale (a := 1 / 4) (b := 1) (by norm_num) (abs_pos.2 hs)
    rw [sq_abs] at h
    rw [show s ^ 2 / 4 = s ^ 2 * (1 / 4) by ring, ← h, mul_one]

theorem measurable_bumpKernel : Measurable (Function.uncurry bumpKernel) := by
  have h : Function.uncurry bumpKernel = fun p : ℝ × ℂ ↦
      (1 - Real.smoothTransition ((‖p.2‖ ^ 2 - p.1 ^ 2 / 4) / (p.1 ^ 2 - p.1 ^ 2 / 4))) /
        (p.1 ^ 2 * profMass (1 / 4) 1) / Real.pi := by
    ext p
    simp only [Function.uncurry, bumpKernel, kernel_eq, cutProfile, profMass_bump]
  rw [h]
  have hst : Measurable Real.smoothTransition := Real.smoothTransition.continuous.measurable
  fun_prop

/-- Radial symmetry: `bumpKernel s (w - y) = bumpKernel s (y - w)`. -/
theorem bumpKernel_sub_comm (s : ℝ) (w y : ℂ) : bumpKernel s (w - y) = bumpKernel s (y - w) := by
  simp only [bumpKernel, kernel_eq, norm_sub_rev]

/-! ### Weyl's lemma -/

/-! #### The two-radii test function -/

/-- `Δ (S_s(‖· − y‖²)) = −4π k_s(· − y)`. -/
theorem laplacian_sFun_normSq_sub {s : ℝ} (hs : 0 < s) (y w : ℂ) :
    Laplacian.laplacian (fun w : ℂ ↦ sFun (s ^ 2 / 4) (s ^ 2) (‖w - y‖ ^ 2)) w =
      -(4 * Real.pi) * bumpKernel s (w - y) := by
  rw [laplacian_eq_four_mul_lap,
    lap_comp_sub (fun w : ℂ ↦ sFun (s ^ 2 / 4) (s ^ 2) (‖w‖ ^ 2)) y w,
    lap_sFun_normSq (bump_pos hs) (bump_lt hs)]
  simp only [bumpKernel]
  ring

theorem contDiff_sFun_normSq_sub {s : ℝ} (hs : 0 < s) (y : ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun w : ℂ ↦ sFun (s ^ 2 / 4) (s ^ 2) (‖w - y‖ ^ 2)) :=
  (contDiff_sFun (bump_pos hs) (bump_lt hs)).comp
    ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const))

/-- The test function `S_{s₂}(‖w − y‖²) − S_{s₁}(‖w − y‖²)`, smooth, supported in
`closedBall y s₂`, with Laplacian `4π (k_{s₁} − k_{s₂})(· − y)`. -/
def twoRadiiTest (s₁ s₂ : ℝ) (y w : ℂ) : ℝ :=
  sFun (s₂ ^ 2 / 4) (s₂ ^ 2) (‖w - y‖ ^ 2) - sFun (s₁ ^ 2 / 4) (s₁ ^ 2) (‖w - y‖ ^ 2)

section twoRadii

variable {s₁ s₂ : ℝ} {y : ℂ}

theorem contDiff_twoRadiiTest (hs₁ : 0 < s₁) (hs₂ : 0 < s₂) :
    ContDiff ℝ (⊤ : ℕ∞) (twoRadiiTest s₁ s₂ y) :=
  (contDiff_sFun_normSq_sub hs₂ y).sub (contDiff_sFun_normSq_sub hs₁ y)

theorem twoRadiiTest_eq_zero (hs₁ : 0 < s₁) (h12 : s₁ ≤ s₂) {w : ℂ} (hw : s₂ ≤ ‖w - y‖) :
    twoRadiiTest s₁ s₂ y w = 0 := by
  have hs₂ : 0 < s₂ := hs₁.trans_le h12
  have h2 : s₂ ^ 2 ≤ ‖w - y‖ ^ 2 := pow_le_pow_left₀ hs₂.le hw 2
  have h1 : s₁ ^ 2 ≤ ‖w - y‖ ^ 2 := (pow_le_pow_left₀ hs₁.le h12 2).trans h2
  unfold twoRadiiTest
  rw [sFun_of_ge (bump_pos hs₂) (bump_lt hs₂) h2, sFun_of_ge (bump_pos hs₁) (bump_lt hs₁) h1,
    sub_self]

theorem tsupport_twoRadiiTest_subset (hs₁ : 0 < s₁) (h12 : s₁ ≤ s₂) :
    tsupport (twoRadiiTest s₁ s₂ y) ⊆ closedBall y s₂ := by
  refine closure_minimal (fun w hw ↦ ?_) isClosed_closedBall
  by_contra hcon
  rw [mem_closedBall, dist_eq_norm, not_le] at hcon
  exact hw (twoRadiiTest_eq_zero hs₁ h12 hcon.le)

theorem hasCompactSupport_twoRadiiTest (hs₁ : 0 < s₁) (h12 : s₁ ≤ s₂) :
    HasCompactSupport (twoRadiiTest s₁ s₂ y) :=
  (isCompact_closedBall y s₂).of_isClosed_subset (isClosed_tsupport _)
    (tsupport_twoRadiiTest_subset hs₁ h12)

theorem laplacian_twoRadiiTest (hs₁ : 0 < s₁) (hs₂ : 0 < s₂) (w : ℂ) :
    Laplacian.laplacian (twoRadiiTest s₁ s₂ y) w =
      4 * Real.pi * (bumpKernel s₁ (w - y) - bumpKernel s₂ (w - y)) := by
  have e : twoRadiiTest s₁ s₂ y = (fun w : ℂ ↦ sFun (s₂ ^ 2 / 4) (s₂ ^ 2) (‖w - y‖ ^ 2)) -
      (fun w : ℂ ↦ sFun (s₁ ^ 2 / 4) (s₁ ^ 2) (‖w - y‖ ^ 2)) := rfl
  rw [e, ((contDiff_sFun_normSq_sub hs₂ y).of_le (WithTop.coe_le_coe.2 le_top)).contDiffAt.laplacian_sub
    ((contDiff_sFun_normSq_sub hs₁ y).of_le (WithTop.coe_le_coe.2 le_top)).contDiffAt,
    laplacian_sFun_normSq_sub hs₂, laplacian_sFun_normSq_sub hs₁]
  ring

end twoRadii

/-- **Two radii give the same average** (Weyl, Step 1), for a locally integrable weakly
harmonic function. -/
theorem integral_bumpKernel_mul_eq_of_weakHarmonic {U : Set ℂ} {f : ℂ → ℝ}
    (hf : LocallyIntegrableOn f U)
    (h : ∀ χ : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ → tsupport χ ⊆ U →
      ∫ z, f z * Laplacian.laplacian χ z = 0)
    {y : ℂ} {s₁ s₂ : ℝ} (hs₁ : 0 < s₁) (h12 : s₁ < s₂) (hsub : closedBall y s₂ ⊆ U) :
    ∫ w, bumpKernel s₁ (w - y) * f w = ∫ w, bumpKernel s₂ (w - y) * f w := by
  have hs₂ : 0 < s₂ := hs₁.trans h12
  have hfi : IntegrableOn f (closedBall y s₂) :=
    hf.integrableOn_compact_subset hsub (isCompact_closedBall y s₂)
  have i1 : Integrable (fun w ↦ bumpKernel s₁ (w - y) * f w) :=
    integrable_kernel_bump_mul hs₁ h12.le hfi
  have i2 : Integrable (fun w ↦ bumpKernel s₂ (w - y) * f w) :=
    integrable_kernel_bump_mul hs₂ le_rfl hfi
  have hχ := h (twoRadiiTest s₁ s₂ y) (contDiff_twoRadiiTest hs₁ hs₂)
    (hasCompactSupport_twoRadiiTest hs₁ h12.le)
    ((tsupport_twoRadiiTest_subset hs₁ h12.le).trans hsub)
  simp_rw [laplacian_twoRadiiTest hs₁ hs₂] at hχ
  have e : ∫ z, f z * (4 * Real.pi * (bumpKernel s₁ (z - y) - bumpKernel s₂ (z - y))) =
      4 * Real.pi * ((∫ w, bumpKernel s₁ (w - y) * f w) - ∫ w, bumpKernel s₂ (w - y) * f w) := by
    rw [← integral_sub i1 i2, ← integral_const_mul]
    congr 1; ext z; ring
  rw [e] at hχ
  have hπ : 4 * Real.pi ≠ 0 := by positivity
  have := (mul_eq_zero.1 hχ).resolve_left hπ
  linarith

/-- Two admissible radii (in any order) give the same average. -/
theorem integral_bumpKernel_mul_eq_of_weakHarmonic' {U : Set ℂ} {f : ℂ → ℝ}
    (hf : LocallyIntegrableOn f U)
    (h : ∀ χ : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ → tsupport χ ⊆ U →
      ∫ z, f z * Laplacian.laplacian χ z = 0)
    {y : ℂ} {s₁ s₂ : ℝ} (hs₁ : 0 < s₁) (hs₂ : 0 < s₂) (h1 : closedBall y s₁ ⊆ U)
    (h2 : closedBall y s₂ ⊆ U) :
    ∫ w, bumpKernel s₁ (w - y) * f w = ∫ w, bumpKernel s₂ (w - y) * f w := by
  rcases lt_trichotomy s₁ s₂ with h12 | rfl | h12
  · exact integral_bumpKernel_mul_eq_of_weakHarmonic hf h hs₁ h12 h2
  · rfl
  · exact (integral_bumpKernel_mul_eq_of_weakHarmonic hf h hs₂ h12 h1).symm

/-- **Lebesgue points.** For a locally integrable `g`, `∫ k_s(w − x) g(w) dw → g(x)` for a.e. `x`. -/
theorem ae_tendsto_integral_bumpKernel_mul {g : ℂ → ℝ} (hg : LocallyIntegrable g) :
    ∀ᵐ x₀, Tendsto (fun s ↦ ∫ w, bumpKernel s (w - x₀) * g w) (𝓝[>] 0) (𝓝 (g x₀)) := by
  filter_upwards [(Besicovitch.vitaliFamily (volume : Measure ℂ)).ae_tendsto_average_norm_sub hg]
    with x₀ h₀
  have hlim := h₀.comp (Besicovitch.tendsto_filterAt volume x₀)
  have := tendsto_integral_smul_of_tendsto_average_norm_sub (μ := volume)
    (a := fun s ↦ closedBall x₀ s) (g := fun s w ↦ bumpKernel s (w - x₀)) (f := g) 4 hlim
    (Eventually.of_forall fun s ↦ hg.integrableOn_isCompact (isCompact_closedBall _ _)) ?_ ?_ ?_
  · simpa [smul_eq_mul] using this
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (integral_kernel_bump_sub hs x₀).symm
  · filter_upwards [self_mem_nhdsWithin] with s hs
    intro w hw
    by_contra hcon
    rw [mem_closedBall, dist_eq_norm, not_le] at hcon
    exact hw (bumpKernel_eq_zero hs hcon.le)
  · filter_upwards [self_mem_nhdsWithin] with s hs w
    have hs' : (0 : ℝ) < s := hs
    rw [abs_of_nonneg (bumpKernel_nonneg hs' _), Measure.real, Complex.volume_closedBall,
      ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hs'.le, ENNReal.coe_toReal,
      NNReal.coe_real_pi]
    refine (bumpKernel_le hs' (w - x₀)).trans ?_
    have hind : (ball (0 : ℂ) s).indicator (1 : ℂ → ℝ) (w - x₀) ≤ 1 :=
      indicator_le_self' (fun _ _ ↦ zero_le_one) _ |>.trans (le_refl _)
    calc 4 / (Real.pi * s ^ 2) * (ball (0 : ℂ) s).indicator 1 (w - x₀)
        ≤ 4 / (Real.pi * s ^ 2) * 1 := by gcongr
      _ = 4 / (s ^ 2 * Real.pi) := by ring

/-- **Mean-value form of Weyl.** A continuous weakly harmonic function equals its
`bumpKernel`-averages. -/
theorem eq_integral_bumpKernel_of_weakHarmonic {Ω : Set ℂ} (hΩ : IsOpen Ω) {φ : ℂ → ℝ}
    (hφ : ContinuousOn φ Ω)
    (h : ∀ χ : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ → tsupport χ ⊆ Ω →
      ∫ z, φ z * Laplacian.laplacian χ z = 0)
    {z : ℂ} {s : ℝ} (hs : 0 < s) (hzs : closedBall z s ⊆ Ω) :
    φ z = ∫ w, bumpKernel s (w - z) * φ w := by
  have hz : z ∈ Ω := hzs (mem_closedBall_self hs.le)
  have hfi : LocallyIntegrableOn φ Ω := hφ.locallyIntegrableOn hΩ.measurableSet
  have hlim := tendsto_integral_kernel_bump_mul hs
    ((hφ.mono hzs).integrableOn_compact (isCompact_closedBall z s))
    (hφ.continuousAt (hΩ.mem_nhds hz))
  have hev : (fun s₁ ↦ ∫ w, kernel (s₁ ^ 2 / 4) (s₁ ^ 2) (w - z) * φ w) =ᶠ[𝓝[>] 0]
      fun _ ↦ ∫ w, bumpKernel s (w - z) * φ w := by
    filter_upwards [Ioo_mem_nhdsGT hs] with s₁ hs₁
    exact integral_bumpKernel_mul_eq_of_weakHarmonic hfi h hs₁.1 hs₁.2 hzs
  exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' hev.symm)

/-- **Weyl's lemma for `Δ`.** A continuous weakly harmonic function is harmonic. -/
theorem harmonicOnNhd_of_weakHarmonic {Ω : Set ℂ} (hΩ : IsOpen Ω) {φ : ℂ → ℝ}
    (hφ : ContinuousOn φ Ω)
    (h : ∀ χ : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ → tsupport χ ⊆ Ω →
      ∫ z, φ z * Laplacian.laplacian χ z = 0) :
    InnerProductSpace.HarmonicOnNhd φ Ω := sorry

/-- **Weyl's lemma for `Δ`, `L¹_loc` form** (the body of M07's `WeylLaplacianStmt`): a locally
integrable weakly harmonic function is a.e. equal to a harmonic function.  (Mollify:
`φ * bumpKernel s` is smooth and weakly, hence classically, harmonic, and equals its own
`bumpKernel`-averages; let `s → 0`.) -/
theorem exists_harmonicOnNhd_ae_eq_of_weakHarmonic {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℝ}
    (hf : LocallyIntegrableOn f U)
    (h : ∀ χ : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ → tsupport χ ⊆ U →
      ∫ z, f z * Laplacian.laplacian χ z = 0) :
    ∃ u : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd u U ∧ ∀ᵐ z ∂(volume.restrict U), f z = u z :=
  sorry

/-! ### Weights up to harmonic functions; calculus of weights (§3) -/

theorem IsSubharmonicWeight.integrable_mul {Ω : Set ℂ} (hΩ : IsOpen Ω) {φ : ℂ → ℝ}
    {μ : Measure ℂ} (h : IsSubharmonicWeight Ω φ μ) {f : ℂ → ℝ} (hf : Continuous f)
    (hc : HasCompactSupport f) (hs : tsupport f ⊆ Ω) :
    Integrable (fun z ↦ φ z * f z) := sorry

theorem IsSubharmonicWeight.sigmaFinite {Ω : Set ℂ} (hΩ : IsOpen Ω) {φ : ℂ → ℝ}
    {μ : Measure ℂ} (h : IsSubharmonicWeight Ω φ μ) : SigmaFinite μ := sorry

/-- **Uniqueness.** Two weights with the same Laplacian differ by a harmonic function. -/
theorem IsSubharmonicWeight.harmonicOnNhd_sub {Ω : Set ℂ} (hΩ : IsOpen Ω) {φ₁ φ₂ : ℂ → ℝ}
    {μ : Measure ℂ} (h₁ : IsSubharmonicWeight Ω φ₁ μ) (h₂ : IsSubharmonicWeight Ω φ₂ μ) :
    InnerProductSpace.HarmonicOnNhd (fun z ↦ φ₁ z - φ₂ z) Ω := sorry

theorem IsSubharmonicWeight.add_harmonic {Ω : Set ℂ} (hΩ : IsOpen Ω) {φ H : ℂ → ℝ}
    {μ : Measure ℂ} (h : IsSubharmonicWeight Ω φ μ) (hH : InnerProductSpace.HarmonicOnNhd H Ω) :
    IsSubharmonicWeight Ω (fun z ↦ φ z + H z) μ := sorry

/-- A `C²` function with `Δu ≥ 0` is a weight, with Laplacian `Δu dm` on `Ω`. -/
theorem isSubharmonicWeight_of_contDiffOn {Ω : Set ℂ} (hΩ : IsOpen Ω) {u : ℂ → ℝ}
    (hu : ContDiffOn ℝ 2 u Ω) (hpos : ∀ z ∈ Ω, 0 ≤ Laplacian.laplacian u z) :
    IsSubharmonicWeight Ω u
      (volume.withDensity (Ω.indicator fun z ↦ ENNReal.ofReal (Laplacian.laplacian u z))) :=
  sorry

/-- Subtracting a `C²` function whose Laplacian is dominated by the absolutely continuous part
of the Laplacian (used for `ψ + c log(1−|z|²)` in M11 and `ψ − c|z|²` in M12). -/
theorem IsSubharmonicWeight.sub_contDiffOn {Ω : Set ℂ} (hΩ : IsOpen Ω) {ψ u : ℂ → ℝ}
    {ν₀ : Measure ℂ} {g : ℂ → ℝ≥0∞} (hg : Measurable g)
    (h : IsSubharmonicWeight Ω ψ (ν₀ + volume.withDensity g)) (hu : ContDiffOn ℝ 2 u Ω)
    (hΔ : ∀ z ∈ Ω, 0 ≤ Laplacian.laplacian u z ∧
      ENNReal.ofReal (Laplacian.laplacian u z) ≤ g z) :
    IsSubharmonicWeight Ω (fun z ↦ ψ z - u z)
      (ν₀ + volume.withDensity
        (fun z ↦ g z - Ω.indicator (fun z ↦ ENNReal.ofReal (Laplacian.laplacian u z)) z)) :=
  sorry

end OC
