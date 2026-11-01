import OrtegaCerdaMultipliers.Foundations.Basic
import OrtegaCerdaMultipliers.Foundations.Wirtinger
import OrtegaCerdaMultipliers.Foundations.Polar
import OrtegaCerdaMultipliers.Foundations.LocalEstimates
import OrtegaCerdaMultipliers.Foundations.Pompeiu

/-!
# M01 (Foundations) — Weyl's lemma for `∂̄` and an L² removable-singularity theorem

See `blueprint/M01_Foundations.md`.

**Provenance.** Copied from `BerndtssonOrtegaCerda/Complex/Weyl.lean`
(BOC module M06, blueprint `M06_Weyl.md`) of the companion project
`../1995ReineAngewMath` at commit `22104d9` (same author, Apache-2.0).  Changes: namespace
`BOC` → `OC`, imports adjusted; the BOC definitions not in `OrtegaCerdaMultipliers/Defs.lean`
are in `Foundations/Basic.lean`.
-/

open MeasureTheory Metric Set Complex
open scoped ENNReal NNReal ComplexConjugate Topology

noncomputable section

namespace OC

/-! ### Auxiliary integrability facts -/

/-- A function locally integrable on `Ω`, times a continuous compactly supported function whose
support lies in `Ω`, is integrable. -/
lemma integrable_mul_of_locallyIntegrableOn {Ω : Set ℂ} {u φ : ℂ → ℂ}
    (hu : LocallyIntegrableOn u Ω) (hφ : Continuous φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ Ω) : Integrable (fun z ↦ u z * φ z) := by
  have hK : IsCompact (tsupport φ) := hc.isCompact
  have h1 : IntegrableOn u (tsupport φ) := hu.integrableOn_compact_subset hs hK
  have h2 : IntegrableOn (fun z ↦ u z * φ z) (tsupport φ) := h1.mul_continuousOn hφ.continuousOn hK
  exact h2.integrable_of_forall_notMem_eq_zero
    (fun z hz ↦ by simp [image_eq_zero_of_notMem_tsupport hz])

/-- The `∂̄` of a smooth test function on `Ω`, multiplied by `u ∈ L¹_loc(Ω)`, is integrable. -/
lemma integrable_mul_dbar_of_locallyIntegrableOn {Ω : Set ℂ} {u α : ℂ → ℂ}
    (hu : LocallyIntegrableOn u Ω) (hα : ContDiff ℝ 1 α) (hc : HasCompactSupport α)
    (hs : tsupport α ⊆ Ω) : Integrable (fun z ↦ u z * dbar α z) :=
  integrable_mul_of_locallyIntegrableOn hu (continuous_dbar hα) (hasCompactSupport_dbar hc)
    ((tsupport_dbar_subset α).trans hs)

lemma contDiff_one_of_top {α : ℂ → ℂ} (hα : ContDiff ℝ (⊤ : ℕ∞) α) : ContDiff ℝ 1 α :=
  hα.of_le (by exact_mod_cast le_top)

/-! ### Weyl's lemma: the local step -/

/-- **Local Weyl lemma.**  If `∫ u ∂̄α = 0` for all test functions `α` on `Ω` and
`closedBall a R ⊆ Ω`, then `u` agrees a.e. on `ball a (R/2)` with the holomorphic function
`C[u ∂̄χ]`, where `χ` is a cut-off equal to `1` on `closedBall a (R/2)`. -/
lemma weyl_local {Ω : Set ℂ} {u : ℂ → ℂ} (hu : LocallyIntegrableOn u Ω)
    (h : ∀ α : ℂ → ℂ, ContDiff ℝ (⊤ : ℕ∞) α → HasCompactSupport α → tsupport α ⊆ Ω →
      ∫ z, u z * dbar α z = 0)
    {a : ℂ} {R : ℝ} (hR : 0 < R) (hball : closedBall a R ⊆ Ω) :
    ∃ H : ℂ → ℂ, DifferentiableOn ℂ H (ball a (R / 2)) ∧
      ∀ᵐ z ∂(volume.restrict (ball a (R / 2))), u z = H z := by
  -- the cut-off `χ`
  let φ : ContDiffBump a := ⟨R / 2, R, half_pos hR, half_lt_self hR⟩
  set χ : ℂ → ℂ := fun z ↦ ((φ z : ℝ) : ℂ) with hχdef
  have hχs : ContDiff ℝ (⊤ : ℕ∞) χ := Complex.ofRealCLM.contDiff.comp φ.contDiff
  have hχ1 : ContDiff ℝ 1 χ := contDiff_one_of_top hχs
  have hχc : HasCompactSupport χ := φ.hasCompactSupport.comp_left Complex.ofReal_zero
  have hχt : tsupport χ ⊆ closedBall a R := by
    have : tsupport χ ⊆ tsupport φ := tsupport_comp_subset Complex.ofReal_zero _
    rw [φ.tsupport_eq] at this
    exact this
  have hχ_one : ∀ z ∈ closedBall a (R / 2), χ z = 1 := fun z hz ↦ by
    simp [χ, φ.one_of_mem_closedBall hz]
  have hdχ_zero : ∀ z ∈ ball a (R / 2), dbar χ z = 0 := by
    intro z hz
    have : χ =ᶠ[𝓝 z] fun _ ↦ (1 : ℂ) := by
      filter_upwards [isOpen_ball.mem_nhds hz] with y hy using hχ_one y (ball_subset_closedBall hy)
    rw [dbar_congr this]
    simp [dbar]
  have hsub : ball a (R / 2) ⊆ Ω :=
    (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))).trans hball
  -- the function `g = u ∂̄χ` and `H = C[g]`
  set g : ℂ → ℂ := fun z ↦ u z * dbar χ z with hg
  have hgi : Integrable g :=
    integrable_mul_dbar_of_locallyIntegrableOn hu hχ1 hχc (hχt.trans hball)
  have hgc : HasCompactSupport g := (hasCompactSupport_dbar hχc).mul_left
  have hgt : tsupport g ⊆ (ball a (R / 2))ᶜ := by
    refine closure_minimal ?_ isOpen_ball.isClosed_compl
    intro z hz hzb
    apply hz
    simp [g, hdχ_zero z hzb]
  set H := cauchyTransform g with hHdef
  have hH : DifferentiableOn ℂ H (ball a (R / 2)) :=
    differentiableOn_cauchyTransform hgi hgc isOpen_ball
      (Set.subset_compl_iff_disjoint_right.mp hgt)
  refine ⟨H, hH, ?_⟩
  -- a.e. equality via the fundamental lemma of the calculus of variations
  have hloc : LocallyIntegrableOn (fun z ↦ u z - H z) (ball a (R / 2)) :=
    (hu.mono_set hsub).sub (hH.continuousOn.locallyIntegrableOn measurableSet_ball)
  have key := isOpen_ball.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc ?_
  · rw [ae_restrict_iff' measurableSet_ball]
    filter_upwards [key] with z hz hzb
    exact sub_eq_zero.mp (hz hzb)
  intro ψ hψ hψc hψs
  set β : ℂ → ℂ := fun z ↦ ((ψ z : ℝ) : ℂ) with hβdef
  have hβs : ContDiff ℝ (⊤ : ℕ∞) β := Complex.ofRealCLM.contDiff.comp hψ
  have hβ1 := contDiff_one_of_top hβs
  have hβc : HasCompactSupport β := hψc.comp_left Complex.ofReal_zero
  have hβt : tsupport β ⊆ ball a (R / 2) :=
    (tsupport_comp_subset Complex.ofReal_zero ψ).trans hψs
  set B := cauchyTransform β with hBdef
  have hBs : ContDiff ℝ (⊤ : ℕ∞) B := contDiff_cauchyTransform hβs hβc
  have hdB : ∀ z, dbar B z = β z := dbar_cauchyTransform hβs hβc
  -- the test function `χ B`
  set α : ℂ → ℂ := fun z ↦ χ z * B z with hαdef
  have hαs : ContDiff ℝ (⊤ : ℕ∞) α := hχs.mul hBs
  have hαc : HasCompactSupport α := hχc.mul_right
  have hαt : tsupport α ⊆ Ω := (tsupport_mul_subset_left).trans (hχt.trans hball)
  have h0 := h α hαs hαc hαt
  have hdα : ∀ z, dbar α z = dbar χ z * B z + β z := by
    intro z
    rw [dbar_mul (hχ1.differentiable one_ne_zero z)
      ((contDiff_one_of_top hBs).differentiable one_ne_zero z), hdB]
    congr 1
    by_cases hz : β z = 0
    · simp [hz]
    · have : z ∈ ball a (R / 2) := hβt (subset_tsupport _ hz)
      rw [hχ_one z (ball_subset_closedBall this), one_mul]
  -- integrability
  have i_udα := integrable_mul_dbar_of_locallyIntegrableOn hu (contDiff_one_of_top hαs) hαc hαt
  have i_uβ : Integrable (fun z ↦ u z * β z) :=
    integrable_mul_of_locallyIntegrableOn hu hβ1.continuous hβc (hβt.trans hsub)
  have hgB : (fun z ↦ g z * B z) = fun z ↦ u z * dbar α z - u z * β z := by
    ext z; rw [hdα]; simp only [g]; ring
  have i_gB : Integrable (fun z ↦ g z * B z) := by
    rw [hgB]; exact i_udα.sub i_uβ
  have i_Hβ : Integrable (fun z ↦ H z * β z) :=
    integrable_mul_of_tsupport_subset isOpen_ball hH.continuousOn hβ1.continuous hβc hβt
  -- the identity
  have e1 : ∫ z, u z * dbar α z = (∫ z, g z * B z) + ∫ z, u z * β z := by
    rw [← integral_add i_gB i_uβ]
    congr 1
    ext z
    rw [hdα]; simp only [g]; ring
  have e2 : ∫ z, g z * B z = -∫ z, H z * β z := by
    have := integral_mul_cauchyTransform_comm hgi hβ1.continuous hβc
    rw [← hHdef, ← hBdef] at this
    have e : ∫ z, H z * β z = ∫ z, β z * H z := by congr 1; ext z; ring
    rw [e, this, neg_neg]
  have e3 : (fun x ↦ ψ x • (u x - H x)) = fun x ↦ u x * β x - H x * β x := by
    ext x; simp only [β, Complex.real_smul]; ring
  rw [e1, e2] at h0
  show ∫ x, ψ x • (u x - H x) = 0
  rw [e3, integral_sub i_uβ i_Hβ]
  linear_combination h0

theorem weyl_dbar {Ω : Set ℂ} (hΩ : IsOpen Ω) {u : ℂ → ℂ} (hu : LocallyIntegrableOn u Ω)
    (h : ∀ α : ℂ → ℂ, ContDiff ℝ (⊤ : ℕ∞) α → HasCompactSupport α → tsupport α ⊆ Ω →
      ∫ z, u z * dbar α z = 0) :
    ∃ H : ℂ → ℂ, DifferentiableOn ℂ H Ω ∧ ∀ᵐ z ∂(volume.restrict Ω), u z = H z := by
  -- local holomorphic representatives
  have hloc : ∀ x ∈ Ω, ∃ r > 0, ball x r ⊆ Ω ∧ ∃ H : ℂ → ℂ, DifferentiableOn ℂ H (ball x r) ∧
      ∀ᵐ z ∂(volume.restrict (ball x r)), u z = H z := by
    intro x hx
    obtain ⟨R, hR, hRΩ⟩ := Metric.isOpen_iff.mp hΩ x hx
    obtain ⟨H, hH, hae⟩ := weyl_local hu h (half_pos hR)
      ((closedBall_subset_ball (half_lt_self hR)).trans hRΩ)
    exact ⟨R / 2 / 2, by positivity, (ball_subset_ball (by linarith)).trans hRΩ, H, hH, hae⟩
  choose! r hr hrΩ H hH hae using hloc
  -- two local representatives agree on the overlap of their balls
  have hagree : ∀ x ∈ Ω, ∀ y ∈ ball x (r x), H y y = H x y := by
    intro x hx y hy
    have hyΩ : y ∈ Ω := hrΩ x hx hy
    have hV : IsOpen (ball x (r x) ∩ ball y (r y)) := isOpen_ball.inter isOpen_ball
    have hyV : y ∈ ball x (r x) ∩ ball y (r y) := ⟨hy, mem_ball_self (hr y hyΩ)⟩
    have e1 : H x =ᵐ[volume.restrict (ball x (r x) ∩ ball y (r y))] H y := by
      have a1 := ae_restrict_of_ae_restrict_of_subset
        (inter_subset_left (s := ball x (r x)) (t := ball y (r y))) (hae x hx)
      have a2 := ae_restrict_of_ae_restrict_of_subset
        (inter_subset_right (s := ball x (r x)) (t := ball y (r y))) (hae y hyΩ)
      filter_upwards [a1, a2] with z h1 h2
      rw [← h1, ← h2]
    have := Measure.eqOn_open_of_ae_eq e1 hV ((hH x hx).continuousOn.mono inter_subset_left)
      ((hH y hyΩ).continuousOn.mono inter_subset_right)
    exact (this hyV).symm
  refine ⟨fun x ↦ H x x, ?_, ?_⟩
  · intro x hx
    have hd : DifferentiableAt ℂ (H x) x := (hH x hx).differentiableAt (ball_mem_nhds x (hr x hx))
    have heq : (fun y ↦ H y y) =ᶠ[𝓝 x] H x := by
      filter_upwards [ball_mem_nhds x (hr x hx)] with y hy using hagree x hx y hy
    exact (hd.congr_of_eventuallyEq heq).differentiableWithinAt
  · obtain ⟨T, hTΩ, hTc, hcover⟩ := TopologicalSpace.countable_cover_nhdsWithin
      (f := fun x ↦ ball x (r x)) (s := Ω)
      (fun x hx ↦ mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x (hr x hx)))
    refine ae_restrict_of_ae_restrict_of_subset hcover ?_
    rw [ae_restrict_biUnion_iff _ hTc]
    intro x hxT
    have hx := hTΩ hxT
    filter_upwards [hae x hx, ae_restrict_mem measurableSet_ball] with z hz hzb
    rw [hz]
    exact (hagree x hx z hzb).symm

theorem IsWeakDbarSol.exists_holomorphic {Ω : Set ℂ} (hΩ : IsOpen Ω) {u : ℂ → ℂ}
    (h : IsWeakDbarSol Ω u 0) :
    ∃ H : ℂ → ℂ, DifferentiableOn ℂ H Ω ∧ ∀ᵐ z ∂(volume.restrict Ω), u z = H z :=
  weyl_dbar hΩ h.1 (fun α hα hc hs ↦ by rw [h.2.2 α hα hc hs]; simp)

theorem IsWeakDbarSol.sub {Ω : Set ℂ} {u₁ u₂ g₁ g₂ : ℂ → ℂ} (h₁ : IsWeakDbarSol Ω u₁ g₁)
    (h₂ : IsWeakDbarSol Ω u₂ g₂) : IsWeakDbarSol Ω (u₁ - u₂) (g₁ - g₂) := by
  obtain ⟨hu1, hg1, h1⟩ := h₁
  obtain ⟨hu2, hg2, h2⟩ := h₂
  refine ⟨hu1.sub hu2, hg1.sub hg2, fun α hα hc hs ↦ ?_⟩
  have hα1 := contDiff_one_of_top hα
  have i1 := integrable_mul_dbar_of_locallyIntegrableOn hu1 hα1 hc hs
  have i2 := integrable_mul_dbar_of_locallyIntegrableOn hu2 hα1 hc hs
  have j1 := integrable_mul_of_locallyIntegrableOn hg1 hα1.continuous hc hs
  have j2 := integrable_mul_of_locallyIntegrableOn hg2 hα1.continuous hc hs
  simp only [Pi.sub_apply, sub_mul]
  rw [integral_sub i1 i2, integral_sub j1 j2, h1 α hα hc hs, h2 α hα hc hs]
  ring

theorem IsWeakDbarSol.mono {Ω Ω' : Set ℂ} {u g : ℂ → ℂ} (h : IsWeakDbarSol Ω u g)
    (hΩ : Ω' ⊆ Ω) : IsWeakDbarSol Ω' u g :=
  ⟨h.1.mono_set hΩ, h.2.1.mono_set hΩ, fun α hα hc hs ↦ h.2.2 α hα hc (hs.trans hΩ)⟩

/-- Change the right-hand side on `Ω` (it only matters there). -/
theorem IsWeakDbarSol.congr {Ω : Set ℂ} (hΩ : IsOpen Ω) {u g g' : ℂ → ℂ}
    (h : IsWeakDbarSol Ω u g) (hg : Set.EqOn g g' Ω) : IsWeakDbarSol Ω u g' := by
  refine ⟨h.1, h.2.1.congr (ae_restrict_of_forall_mem hΩ.measurableSet hg),
    fun α hα hc hs ↦ ?_⟩
  rw [h.2.2 α hα hc hs]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun z ↦ ?_)
  by_cases hz : z ∈ Ω
  · simp only [hg hz]
  · have : α z = 0 := image_eq_zero_of_notMem_tsupport (fun h ↦ hz (hs h))
    simp [this]

theorem differentiableOn_of_isWeakDbarSol_zero {Ω : Set ℂ} (hΩ : IsOpen Ω) {u : ℂ → ℂ}
    (hc : ContinuousOn u Ω) (h : IsWeakDbarSol Ω u 0) : DifferentiableOn ℂ u Ω := by
  obtain ⟨H, hH, hae⟩ := h.exists_holomorphic hΩ
  have heq := Measure.eqOn_open_of_ae_eq hae hΩ hc hH.continuousOn
  exact hH.congr (fun z hz ↦ heq hz)

/-! ### Removable singularities under an L² condition -/

/-- The pointwise bound `π |u(z)|² ≤ 9 ∫_{B(a,R)} |u|²/|w-a|²` for `0 < |z - a| < R/3`. -/
lemma pi_mul_norm_sq_le_of_lintegral_div_normSq {u : ℂ → ℂ} {a : ℂ} {R : ℝ}
    (hu : DifferentiableOn ℂ u (Metric.ball a R \ {a}))
    (hL2 : ∫⁻ z in Metric.ball a R, ENNReal.ofReal (‖u z‖ ^ 2 / ‖z - a‖ ^ 2) < ∞)
    {z : ℂ} (hz : z ∈ ball a (R / 3)) (hza : z ≠ a) :
    Real.pi * ‖u z‖ ^ 2 ≤
      9 * (∫⁻ w in Metric.ball a R, ENNReal.ofReal (‖u w‖ ^ 2 / ‖w - a‖ ^ 2)).toReal := by
  set I := ∫⁻ w in Metric.ball a R, ENNReal.ofReal (‖u w‖ ^ 2 / ‖w - a‖ ^ 2) with hI
  set d := ‖z - a‖ with hd_def
  have hd : 0 < d := norm_pos_iff.mpr (sub_ne_zero.mpr hza)
  have hdR : d < R / 3 := by rw [hd_def, ← dist_eq_norm]; exact hz
  have hfar : ∀ w ∈ ball z (d / 2), d / 2 < ‖w - a‖ ∧ ‖w - a‖ < 3 * d / 2 := by
    intro w hw
    have hw' : ‖w - z‖ < d / 2 := by rw [← dist_eq_norm]; exact hw
    have t1 : ‖z - a‖ ≤ ‖z - w‖ + ‖w - a‖ := norm_sub_le_norm_sub_add_norm_sub z w a
    have t2 : ‖w - a‖ ≤ ‖w - z‖ + ‖z - a‖ := norm_sub_le_norm_sub_add_norm_sub w z a
    rw [norm_sub_rev z w] at t1
    constructor <;> linarith
  have hsub : ball z (d / 2) ⊆ Metric.ball a R \ {a} := by
    intro w hw
    obtain ⟨h1, h2⟩ := hfar w hw
    refine ⟨?_, ?_⟩
    · rw [mem_ball, dist_eq_norm]; linarith
    · intro hwa
      rw [mem_singleton_iff] at hwa
      rw [hwa, sub_self, norm_zero] at h1
      linarith
  have h1 := norm_sq_le_lintegral_ball (half_pos hd) (hu.mono hsub)
  have h2 : ∫⁻ w in ball z (d / 2), ENNReal.ofReal (‖u w‖ ^ 2) ≤
      ENNReal.ofReal (9 * d ^ 2 / 4) * I := by
    calc ∫⁻ w in ball z (d / 2), ENNReal.ofReal (‖u w‖ ^ 2)
        ≤ ∫⁻ w in ball z (d / 2),
            ENNReal.ofReal (9 * d ^ 2 / 4) * ENNReal.ofReal (‖u w‖ ^ 2 / ‖w - a‖ ^ 2) := by
          refine lintegral_mono_ae ((ae_restrict_iff' measurableSet_ball).mpr
            (Filter.Eventually.of_forall fun w hw ↦ ?_))
          obtain ⟨hw1, hw2⟩ := hfar w hw
          have hpos : 0 < ‖w - a‖ := by linarith
          rw [← ENNReal.ofReal_mul (by positivity)]
          apply ENNReal.ofReal_le_ofReal
          have hsq : ‖w - a‖ ^ 2 ≤ 9 * d ^ 2 / 4 := by nlinarith
          calc ‖u w‖ ^ 2 = ‖u w‖ ^ 2 / ‖w - a‖ ^ 2 * ‖w - a‖ ^ 2 := by field_simp
            _ ≤ ‖u w‖ ^ 2 / ‖w - a‖ ^ 2 * (9 * d ^ 2 / 4) := by gcongr
            _ = _ := by ring
      _ = ENNReal.ofReal (9 * d ^ 2 / 4) *
            ∫⁻ w in ball z (d / 2), ENNReal.ofReal (‖u w‖ ^ 2 / ‖w - a‖ ^ 2) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (9 * d ^ 2 / 4) * I := by
          gcongr
          exact lintegral_mono_set (fun w hw ↦ (hsub hw).1)
  have h3 : ENNReal.ofReal (Real.pi * (d / 2) ^ 2 * ‖u z‖ ^ 2) ≤
      ENNReal.ofReal (9 * d ^ 2 / 4 * I.toReal) := by
    calc ENNReal.ofReal (Real.pi * (d / 2) ^ 2 * ‖u z‖ ^ 2)
        ≤ ENNReal.ofReal (9 * d ^ 2 / 4) * I := h1.trans h2
      _ = ENNReal.ofReal (9 * d ^ 2 / 4 * I.toReal) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hL2.ne]
  rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at h3
  have h4 : d ^ 2 / 4 * (Real.pi * ‖u z‖ ^ 2) ≤ d ^ 2 / 4 * (9 * I.toReal) := by
    nlinarith
  exact le_of_mul_le_mul_left h4 (by positivity)

theorem removable_of_lintegral_div_normSq {u : ℂ → ℂ} {a : ℂ} {R : ℝ} (hR : 0 < R)
    (hu : DifferentiableOn ℂ u (Metric.ball a R \ {a}))
    (hL2 : ∫⁻ z in Metric.ball a R, ENNReal.ofReal (‖u z‖ ^ 2 / ‖z - a‖ ^ 2) < ∞) :
    ∃ U : ℂ → ℂ, DifferentiableOn ℂ U (Metric.ball a R) ∧ U a = 0 ∧
      ∀ z ∈ Metric.ball a R \ {a}, U z = u z := by
  set I := ∫⁻ z in Metric.ball a R, ENNReal.ofReal (‖u z‖ ^ 2 / ‖z - a‖ ^ 2) with hI
  have hR3 : 0 < R / 3 := by positivity
  have hbdd : BddAbove (norm ∘ u '' (ball a (R / 3) \ {a})) := by
    refine ⟨1 + 9 * I.toReal / Real.pi, ?_⟩
    rintro _ ⟨z, ⟨hz, hza⟩, rfl⟩
    have hb := pi_mul_norm_sq_le_of_lintegral_div_normSq hu hL2 hz hza
    have hb' : ‖u z‖ ^ 2 ≤ 9 * I.toReal / Real.pi := by
      rw [le_div_iff₀ Real.pi_pos]; linarith
    simp only [Function.comp_apply]
    nlinarith [norm_nonneg (u z)]
  have hsmall := Complex.differentiableOn_update_limUnder_of_bddAbove (ball_mem_nhds a hR3)
    (hu.mono (sdiff_subset_sdiff_left (ball_subset_ball (by linarith)))) hbdd
  set L := (𝓝[≠] a).limUnder u with hL
  set U := Function.update u a L with hU
  have hUu : ∀ z ∈ Metric.ball a R \ {a}, U z = u z := fun z hz ↦
    Function.update_of_ne hz.2 _ _
  have hUd : DifferentiableOn ℂ U (Metric.ball a R) := by
    intro z hz
    apply DifferentiableAt.differentiableWithinAt
    by_cases hza : z = a
    · subst hza
      exact hsmall.differentiableAt (ball_mem_nhds z hR3)
    · have hopen : IsOpen (Metric.ball a R \ {a}) := isOpen_ball.sdiff isClosed_singleton
      have hmem : z ∈ Metric.ball a R \ {a} := ⟨hz, hza⟩
      have hdu : DifferentiableAt ℂ u z := hu.differentiableAt (hopen.mem_nhds hmem)
      refine hdu.congr_of_eventuallyEq ?_
      filter_upwards [hopen.mem_nhds hmem] with w hw using hUu w hw
  refine ⟨U, hUd, ?_, hUu⟩
  -- `U a = 0`, otherwise `∫ |u|²/|z-a|² = ∞`
  by_contra hne
  have hUa : U a = L := Function.update_self _ _ _
  have hLne : L ≠ 0 := hUa ▸ hne
  have hLpos : 0 < ‖L‖ := norm_pos_iff.mpr hLne
  have hcont : ContinuousAt U a := (hUd.differentiableAt (ball_mem_nhds a hR)).continuousAt
  obtain ⟨δ, hδ, hδU⟩ := Metric.continuousAt_iff.mp hcont (‖L‖ / 2) (half_pos hLpos)
  set ρ := min δ R with hρ
  have hρpos : 0 < ρ := lt_min hδ hR
  have hlow : ∀ z ∈ ball a ρ,
      ENNReal.ofReal (‖L‖ ^ 2 / 4 * ‖z - a‖⁻¹ ^ 2) ≤ ENNReal.ofReal (‖u z‖ ^ 2 / ‖z - a‖ ^ 2) := by
    intro z hz
    by_cases hza : z = a
    · subst hza; simp
    apply ENNReal.ofReal_le_ofReal
    have hzR : z ∈ Metric.ball a R := ball_subset_ball (min_le_right _ _) hz
    have hzδ : dist z a < δ := lt_of_lt_of_le hz (min_le_left _ _)
    have h1 := hδU hzδ
    rw [hUa, dist_eq_norm] at h1
    have h2 : ‖L‖ / 2 ≤ ‖u z‖ := by
      rw [← hUu z ⟨hzR, hza⟩]
      have := norm_sub_norm_le L (U z)
      rw [norm_sub_rev] at this
      linarith
    have h3 : ‖L‖ ^ 2 / 4 ≤ ‖u z‖ ^ 2 := by nlinarith
    rw [div_eq_mul_inv (‖u z‖ ^ 2), ← inv_pow]
    gcongr
  have htop := lintegral_inv_normSq_sub_ball_eq_top a hρpos
  have hinf : ∫⁻ z in ball a ρ, ENNReal.ofReal (‖L‖ ^ 2 / 4 * ‖z - a‖⁻¹ ^ 2) = ∞ := by
    have e : ∀ z : ℂ, ENNReal.ofReal (‖L‖ ^ 2 / 4 * ‖z - a‖⁻¹ ^ 2) =
        ENNReal.ofReal (‖L‖ ^ 2 / 4) * ENNReal.ofReal (‖z - a‖⁻¹ ^ 2) := fun z ↦
      ENNReal.ofReal_mul (by positivity)
    simp_rw [e]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, htop]
    exact ENNReal.mul_top (by simp; positivity)
  have : ∞ ≤ I := by
    rw [← hinf]
    calc ∫⁻ z in ball a ρ, ENNReal.ofReal (‖L‖ ^ 2 / 4 * ‖z - a‖⁻¹ ^ 2)
        ≤ ∫⁻ z in ball a ρ, ENNReal.ofReal (‖u z‖ ^ 2 / ‖z - a‖ ^ 2) :=
          lintegral_mono_ae ((ae_restrict_iff' measurableSet_ball).mpr
            (Filter.Eventually.of_forall hlow))
      _ ≤ I := lintegral_mono_set (ball_subset_ball (min_le_right _ _))
  exact absurd hL2 (not_lt.mpr this)

end OC
