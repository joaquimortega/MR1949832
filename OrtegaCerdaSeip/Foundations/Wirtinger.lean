import OrtegaCerdaSeip.Foundations.Basic

/-!
# M01 (Foundations) — Wirtinger calculus and integration by parts on `ℂ`

See `blueprint/M01_Foundations.md`.

**Copy (MR1682065).** Copied verbatim from `OrtegaCerdaMultipliers/Foundations/Wirtinger.lean` of the companion
project `../MR1949832` (github.com/joaquimortega/MR1949832, commit `4aa833e`, same author, Apache-2.0).
Changes: namespace `OC` → `OCS`, imports.  The provenance note below refers to the earlier copy
from MR1340337 into MR1949832.

**Provenance.** Copied from `BerndtssonOrtegaCerda/Calculus/Wirtinger.lean`
(BOC module M01, blueprint `M01_Wirtinger.md`) of the companion project
`../MR1340337` at commit `22104d9` (same author, Apache-2.0).  Changes: namespace
`BOC` → `OC`, imports adjusted; the BOC definitions not in `OrtegaCerdaMultipliers/Defs.lean`
are in `Foundations/Basic.lean`.
-/

open MeasureTheory Metric Set Complex
open scoped ENNReal NNReal ComplexConjugate Topology

noncomputable section

namespace OCS
/-- `∂f/∂z = ½ (∂f/∂x − i ∂f/∂y)`. -/
def dz (f : ℂ → ℂ) (z : ℂ) : ℂ := (1 / 2 : ℂ) * (fderiv ℝ f z 1 - I * fderiv ℝ f z I)

/-- The complexification of a real function. -/
def cplx (φ : ℂ → ℝ) : ℂ → ℂ := fun z ↦ (φ z : ℂ)

/-- Every real-linear map `L : ℂ → ℂ` is `w ↦ A w + B w̄` with `A = ½(L1 − iLi)`,
`B = ½(L1 + iLi)`. -/
theorem clm_apply_eq_wirtinger (L : ℂ →L[ℝ] ℂ) (w : ℂ) :
    L w = (1 / 2 : ℂ) * (L 1 - I * L I) * w + (1 / 2 : ℂ) * (L 1 + I * L I) * conj w := by
  have hw : w = (w.re : ℝ) • (1 : ℂ) + (w.im : ℝ) • I := by
    apply Complex.ext <;> simp
  conv_lhs => rw [hw]
  rw [map_add, map_smul, map_smul]
  conv_rhs => rw [← Complex.re_add_im w]
  simp only [Complex.real_smul, map_add, map_mul, conj_ofReal, conj_I]
  linear_combination ((w.im : ℂ) * L I) * I_sq

theorem fderiv_apply_eq_dz_dbar {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z) (w : ℂ) :
    fderiv ℝ f z w = dz f z * w + dbar f z * conj w := by
  -- the identity holds for every real-linear map, so `hf` is not needed
  exact clm_apply_eq_wirtinger _ w

theorem differentiableAt_iff_dbar_eq_zero {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z) :
    DifferentiableAt ℂ f z ↔ dbar f z = 0 := by
  rw [differentiableAt_complex_iff_differentiableAt_real, smul_eq_mul]
  simp only [hf, true_and, dbar]
  constructor
  · intro h
    linear_combination (1 / 2 * I) * h + (1 / 2 * fderiv ℝ f z 1) * I_sq
  · intro h
    have h' : fderiv ℝ f z 1 + I * fderiv ℝ f z I = 0 :=
      (mul_eq_zero.mp h).resolve_left (by norm_num)
    linear_combination (-I) * h' + (fderiv ℝ f z I) * I_sq

theorem dbar_eq_zero_of_differentiableAt {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℂ f z) :
    dbar f z = 0 :=
  (differentiableAt_iff_dbar_eq_zero (hf.restrictScalars ℝ)).1 hf

theorem dz_eq_deriv {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℂ f z) : dz f z = deriv f z := by
  have h := (hf.hasDerivAt.hasFDerivAt.restrictScalars ℝ).fderiv
  simp only [dz, h]
  simp
  linear_combination (-(1/2) * deriv f z) * I_sq

theorem dbar_add {f g : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z)
    (hg : DifferentiableAt ℝ g z) :
    dbar (fun w ↦ f w + g w) z = dbar f z + dbar g z := by
  simp only [dbar, fderiv_fun_add hf hg, _root_.add_apply]; ring

theorem dbar_sub {f g : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z)
    (hg : DifferentiableAt ℝ g z) :
    dbar (fun w ↦ f w - g w) z = dbar f z - dbar g z := by
  simp only [dbar, fderiv_fun_sub hf hg, _root_.sub_apply]; ring

theorem dz_add {f g : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z)
    (hg : DifferentiableAt ℝ g z) :
    dz (fun w ↦ f w + g w) z = dz f z + dz g z := by
  simp only [dz, fderiv_fun_add hf hg, _root_.add_apply]; ring

theorem dz_sub {f g : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z)
    (hg : DifferentiableAt ℝ g z) :
    dz (fun w ↦ f w - g w) z = dz f z - dz g z := by
  simp only [dz, fderiv_fun_sub hf hg, _root_.sub_apply]; ring

theorem dbar_mul {f g : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z)
    (hg : DifferentiableAt ℝ g z) :
    dbar (fun w ↦ f w * g w) z = dbar f z * g z + f z * dbar g z := by
  simp only [dbar, fderiv_fun_mul hf hg, _root_.add_apply,
    _root_.smul_apply, smul_eq_mul]; ring

theorem dz_mul {f g : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z)
    (hg : DifferentiableAt ℝ g z) :
    dz (fun w ↦ f w * g w) z = dz f z * g z + f z * dz g z := by
  simp only [dz, fderiv_fun_mul hf hg, _root_.add_apply,
    _root_.smul_apply, smul_eq_mul]; ring

theorem dbar_const_mul (c : ℂ) {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z) :
    dbar (fun w ↦ c * f w) z = c * dbar f z := by
  simp only [dbar, fderiv_const_mul hf, _root_.smul_apply, smul_eq_mul]; ring

theorem fderiv_conj_apply {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z) (v : ℂ) :
    fderiv ℝ (fun w ↦ conj (f w)) z v = conj (fderiv ℝ f z v) := by
  have h : HasFDerivAt (fun w ↦ conj (f w))
      ((conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap.comp (fderiv ℝ f z)) z :=
    (conjCLE : ℂ ≃L[ℝ] ℂ).hasFDerivAt.comp z hf.hasFDerivAt
  rw [h.fderiv]
  simp

theorem dbar_conj {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z) :
    dbar (fun w ↦ conj (f w)) z = conj (dz f z) := by
  simp only [dbar, dz, fderiv_conj_apply hf, map_mul, map_sub, conj_I, map_div₀, map_one,
    map_ofNat]
  ring

theorem dz_conj {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z) :
    dz (fun w ↦ conj (f w)) z = conj (dbar f z) := by
  simp only [dbar, dz, fderiv_conj_apply hf, map_mul, map_add, conj_I, map_div₀, map_one,
    map_ofNat]
  ring

/-- The real derivative of `cplx φ` is the complexification of that of `φ` (unconditionally:
both sides vanish when `φ` is not differentiable). -/
theorem fderiv_cplx (φ : ℂ → ℝ) (z : ℂ) :
    fderiv ℝ (cplx φ) z = ofRealCLM.comp (fderiv ℝ φ z) := by
  by_cases hφ : DifferentiableAt ℝ φ z
  · exact (ofRealCLM.hasFDerivAt.comp z hφ.hasFDerivAt).fderiv
  · have h : ¬ DifferentiableAt ℝ (cplx φ) z := by
      intro h
      apply hφ
      have := (reCLM.differentiableAt (x := cplx φ z)).comp z h
      simpa [Function.comp_def, cplx] using this
    rw [fderiv_zero_of_not_differentiableAt h, fderiv_zero_of_not_differentiableAt hφ]
    simp

theorem dbar_cplx_eq_conj_dz (φ : ℂ → ℝ) (z : ℂ) : dbar (cplx φ) z = conj (dz (cplx φ) z) := by
  simp only [dbar, dz, fderiv_cplx, ContinuousLinearMap.comp_apply, ofRealCLM_apply, map_mul,
    map_sub, conj_I, map_div₀, map_one, map_ofNat, conj_ofReal]
  ring

theorem dz_const_mul (c : ℂ) {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z) :
    dz (fun w ↦ c * f w) z = c * dz f z := by
  simp only [dz, fderiv_const_mul hf, _root_.smul_apply, smul_eq_mul]; ring

theorem dbar_cexp {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z) :
    dbar (fun w ↦ Complex.exp (f w)) z = Complex.exp (f z) * dbar f z := by
  simp only [dbar, hf.hasFDerivAt.cexp.fderiv, _root_.smul_apply, smul_eq_mul]; ring

theorem fderiv_real_eq_two_re_dz {φ : ℂ → ℝ} {z : ℂ} (hφ : DifferentiableAt ℝ φ z) (w : ℂ) :
    fderiv ℝ φ z w = 2 * (dz (cplx φ) z * w).re := by
  -- `fderiv_cplx` holds unconditionally, so `hφ` is not needed
  have hw : w = (w.re : ℝ) • (1 : ℂ) + (w.im : ℝ) • I := by
    apply Complex.ext <;> simp
  simp only [dz, fderiv_cplx, ContinuousLinearMap.comp_apply, ofRealCLM_apply]
  conv_lhs => rw [hw]
  rw [map_add, map_smul, map_smul]
  simp [Complex.mul_re, Complex.mul_im]
  ring

theorem dbar_comp_sub (f : ℂ → ℂ) (a z : ℂ) : dbar (fun w ↦ f (w - a)) z = dbar f (z - a) := by
  simp only [dbar, fderiv_comp_sub]

theorem dz_comp_sub (f : ℂ → ℂ) (a z : ℂ) : dz (fun w ↦ f (w - a)) z = dz f (z - a) := by
  simp only [dz, fderiv_comp_sub]

theorem lap_comp_sub (φ : ℂ → ℝ) (a z : ℂ) : lap (fun w ↦ φ (w - a)) z = lap φ (z - a) := by
  simp only [lap, InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane,
    iteratedFDeriv_comp_sub]

theorem lap_add {φ ψ : ℂ → ℝ} {z : ℂ} (hφ : ContDiffAt ℝ 2 φ z) (hψ : ContDiffAt ℝ 2 ψ z) :
    lap (fun w ↦ φ w + ψ w) z = lap φ z + lap ψ z := by
  simp only [lap]
  rw [show (fun w ↦ φ w + ψ w) = φ + ψ from rfl, hφ.laplacian_add hψ]
  ring

theorem lap_const_mul (c : ℝ) {φ : ℂ → ℝ} {z : ℂ} (hφ : ContDiffAt ℝ 2 φ z) :
    lap (fun w ↦ c * φ w) z = c * lap φ z := by
  simp only [lap]
  rw [show (fun w ↦ c * φ w) = c • φ from rfl, InnerProductSpace.laplacian_smul c hφ,
    smul_eq_mul]
  ring

theorem lap_congr {φ ψ : ℂ → ℝ} {z : ℂ} (h : φ =ᶠ[𝓝 z] ψ) : lap φ z = lap ψ z := by
  simp only [lap, (InnerProductSpace.laplacian_congr_nhds h).eq_of_nhds]

theorem continuousOn_lap {φ : ℂ → ℝ} {Ω : Set ℂ} (hΩ : IsOpen Ω) (hφ : ContDiffOn ℝ 2 φ Ω) :
    ContinuousOn (lap φ) Ω := by
  have h1 : ContinuousOn (iteratedFDeriv ℝ 2 φ) Ω := by
    have := hφ.continuousOn_iteratedFDerivWithin (m := 2) le_rfl hΩ.uniqueDiffOn
    exact this.congr (fun x hx ↦ (iteratedFDerivWithin_of_isOpen 2 hΩ hx).symm)
  have : lap φ = fun x ↦ (1 / 4 : ℝ) *
      (iteratedFDeriv ℝ 2 φ x ![1, 1] + iteratedFDeriv ℝ 2 φ x ![I, I]) := by
    ext x
    simp only [lap, InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
  rw [this]
  have hc : ∀ m : Fin 2 → ℂ, ContinuousOn (fun x ↦ iteratedFDeriv ℝ 2 φ x m) Ω := fun m ↦
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 ↦ ℂ) ℝ m).continuous.comp_continuousOn h1
  exact continuousOn_const.mul ((hc _).add (hc _))


theorem dz_cexp' {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z) :
    dz (fun w ↦ Complex.exp (f w)) z = Complex.exp (f z) * dz f z := by
  simp only [dz, hf.hasFDerivAt.cexp.fderiv, _root_.smul_apply, smul_eq_mul]; ring

/-! ### Second-order Wirtinger calculus -/

section SecondOrder

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Derivative of `w ↦ Df(w) u` in the direction `v` is `D²f(z)(v, u)`. -/
theorem fderiv_fderiv_apply_const {f : ℂ → F} {z : ℂ}
    (hf : DifferentiableAt ℝ (fderiv ℝ f) z) (u v : ℂ) :
    fderiv ℝ (fun w ↦ fderiv ℝ f w u) z v = fderiv ℝ (fderiv ℝ f) z v u := by
  rw [fderiv_clm_apply hf (differentiableAt_const u)]
  simp

end SecondOrder

theorem differentiableAt_dbar {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ (fderiv ℝ f) z) :
    DifferentiableAt ℝ (dbar f) z := by
  have h1 : DifferentiableAt ℝ (fun w ↦ fderiv ℝ f w 1) z :=
    hf.clm_apply (differentiableAt_const _)
  have hI : DifferentiableAt ℝ (fun w ↦ fderiv ℝ f w I) z :=
    hf.clm_apply (differentiableAt_const _)
  exact (h1.add (hI.const_mul I)).const_mul _

theorem differentiableAt_dz {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ (fderiv ℝ f) z) :
    DifferentiableAt ℝ (dz f) z := by
  have h1 : DifferentiableAt ℝ (fun w ↦ fderiv ℝ f w 1) z :=
    hf.clm_apply (differentiableAt_const _)
  have hI : DifferentiableAt ℝ (fun w ↦ fderiv ℝ f w I) z :=
    hf.clm_apply (differentiableAt_const _)
  exact (h1.sub (hI.const_mul I)).const_mul _

theorem fderiv_dbar_apply {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ (fderiv ℝ f) z)
    (v : ℂ) :
    fderiv ℝ (dbar f) z v = (1 / 2 : ℂ) *
      (fderiv ℝ (fderiv ℝ f) z v 1 + I * fderiv ℝ (fderiv ℝ f) z v I) := by
  have h1 : DifferentiableAt ℝ (fun w ↦ fderiv ℝ f w 1) z :=
    hf.clm_apply (differentiableAt_const _)
  have hI : DifferentiableAt ℝ (fun w ↦ fderiv ℝ f w I) z :=
    hf.clm_apply (differentiableAt_const _)
  have h2 : DifferentiableAt ℝ (fun w ↦ fderiv ℝ f w 1 + I * fderiv ℝ f w I) z :=
    h1.add (hI.const_mul I)
  have : dbar f = fun w ↦ (1 / 2 : ℂ) * (fderiv ℝ f w 1 + I * fderiv ℝ f w I) := rfl
  rw [this, fderiv_const_mul h2, fderiv_fun_add h1 (hI.const_mul I),
    fderiv_const_mul hI]
  simp [fderiv_fderiv_apply_const hf]
  ring

theorem fderiv_dz_apply {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ (fderiv ℝ f) z)
    (v : ℂ) :
    fderiv ℝ (dz f) z v = (1 / 2 : ℂ) *
      (fderiv ℝ (fderiv ℝ f) z v 1 - I * fderiv ℝ (fderiv ℝ f) z v I) := by
  have h1 : DifferentiableAt ℝ (fun w ↦ fderiv ℝ f w 1) z :=
    hf.clm_apply (differentiableAt_const _)
  have hI : DifferentiableAt ℝ (fun w ↦ fderiv ℝ f w I) z :=
    hf.clm_apply (differentiableAt_const _)
  have h2 : DifferentiableAt ℝ (fun w ↦ fderiv ℝ f w 1 - I * fderiv ℝ f w I) z :=
    h1.sub (hI.const_mul I)
  have : dz f = fun w ↦ (1 / 2 : ℂ) * (fderiv ℝ f w 1 - I * fderiv ℝ f w I) := rfl
  rw [this, fderiv_const_mul h2, fderiv_fun_sub h1 (hI.const_mul I),
    fderiv_const_mul hI]
  simp [fderiv_fderiv_apply_const hf]

theorem differentiableAt_fderiv_of_contDiffAt {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : ℂ → F} {z : ℂ} (hf : ContDiffAt ℝ 2 f z) :
    DifferentiableAt ℝ (fderiv ℝ f) z :=
  (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)

/-- `∂∂̄ f = ¼ Δ_std f` for complex-valued `C²` functions. -/
theorem dz_dbar_eq_laplacian {f : ℂ → ℂ} {z : ℂ} (hf : ContDiffAt ℝ 2 f z) :
    dz (dbar f) z = (1 / 4 : ℂ) * Laplacian.laplacian f z := by
  have hd := differentiableAt_fderiv_of_contDiffAt hf
  have hs := hf.isSymmSndFDerivAt (by simp)
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  simp only [dz, fderiv_dbar_apply hd]
  linear_combination (1 / 4 * I) * hs 1 I - (1 / 4 * fderiv ℝ (fderiv ℝ f) z I I) * I_sq

/-- `∂̄∂ f = ¼ Δ_std f` for complex-valued `C²` functions. -/
theorem dbar_dz_eq_laplacian {f : ℂ → ℂ} {z : ℂ} (hf : ContDiffAt ℝ 2 f z) :
    dbar (dz f) z = (1 / 4 : ℂ) * Laplacian.laplacian f z := by
  have hd := differentiableAt_fderiv_of_contDiffAt hf
  have hs := hf.isSymmSndFDerivAt (by simp)
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  simp only [dbar, fderiv_dz_apply hd]
  linear_combination (-(1 / 4) * I) * hs 1 I - (1 / 4 * fderiv ℝ (fderiv ℝ f) z I I) * I_sq

theorem contDiffAt_cplx {n : WithTop ℕ∞} {φ : ℂ → ℝ} {z : ℂ} (hφ : ContDiffAt ℝ n φ z) :
    ContDiffAt ℝ n (cplx φ) z :=
  ofRealCLM.contDiff.contDiffAt.comp z hφ

/-- The (standard) Laplacian commutes with complexification. -/
theorem laplacian_cplx {φ : ℂ → ℝ} {z : ℂ} (hφ : ContDiffAt ℝ 2 φ z) :
    Laplacian.laplacian (cplx φ) z = (Laplacian.laplacian φ z : ℂ) := by
  have : cplx φ = ofRealCLM ∘ φ := rfl
  rw [this, hφ.laplacian_CLM_comp_left]
  simp

theorem dz_dbar_cplx {φ : ℂ → ℝ} {z : ℂ} (hφ : ContDiffAt ℝ 2 φ z) :
    dz (dbar (cplx φ)) z = (lap φ z : ℂ) := by
  rw [dz_dbar_eq_laplacian (contDiffAt_cplx hφ), laplacian_cplx hφ, lap]
  push_cast; ring

theorem dbar_dz_cplx {φ : ℂ → ℝ} {z : ℂ} (hφ : ContDiffAt ℝ 2 φ z) :
    dbar (dz (cplx φ)) z = (lap φ z : ℂ) := by
  rw [dbar_dz_eq_laplacian (contDiffAt_cplx hφ), laplacian_cplx hφ, lap]
  push_cast; ring

/-! ### Radial functions -/

theorem dz_congr {f g : ℂ → ℂ} {z : ℂ} (h : f =ᶠ[𝓝 z] g) : dz f z = dz g z := by
  simp only [dz, h.fderiv_eq]

theorem dbar_congr {f g : ℂ → ℂ} {z : ℂ} (h : f =ᶠ[𝓝 z] g) : dbar f z = dbar g z := by
  simp only [dbar, h.fderiv_eq]

theorem dz_id (z : ℂ) : dz (fun w ↦ w) z = 1 := by
  simp only [dz, fderiv_fun_id, ContinuousLinearMap.coe_id', id_eq]
  linear_combination (-(1 / 2 : ℂ)) * I_sq

theorem dz_cplx_eq_conj_dbar (φ : ℂ → ℝ) (z : ℂ) : dz (cplx φ) z = conj (dbar (cplx φ) z) := by
  rw [dbar_cplx_eq_conj_dz, conj_conj]

/-- `∂̄ G(|w|²) = G'(|w|²) w`. -/
theorem dbar_cplx_comp_normSq {G : ℝ → ℝ} {w : ℂ} (hG : DifferentiableAt ℝ G (‖w‖ ^ 2)) :
    dbar (cplx (fun u ↦ G (‖u‖ ^ 2))) w = ((deriv G (‖w‖ ^ 2) : ℝ) : ℂ) * w := by
  have h : HasFDerivAt (fun u : ℂ ↦ G (‖u‖ ^ 2))
      (deriv G (‖w‖ ^ 2) • (2 • innerSL ℝ w : ℂ →L[ℝ] ℝ)) w :=
    hG.hasDerivAt.comp_hasFDerivAt w (hasStrictFDerivAt_norm_sq w).hasFDerivAt
  simp only [dbar, fderiv_cplx, h.fderiv]
  apply Complex.ext <;> simp [Complex.inner] <;> ring

theorem lap_comp_normSq {F : ℝ → ℝ} {z : ℂ} (hF : ContDiffAt ℝ 2 F (‖z‖ ^ 2)) :
    lap (fun w ↦ F (‖w‖ ^ 2)) z = deriv F (‖z‖ ^ 2) + ‖z‖ ^ 2 * deriv (deriv F) (‖z‖ ^ 2) := by
  have hns : ContDiff ℝ 2 (fun w : ℂ ↦ ‖w‖ ^ 2) := contDiff_norm_sq ℝ
  have hfC2 : ContDiffAt ℝ 2 (fun w ↦ F (‖w‖ ^ 2)) z := hF.comp z hns.contDiffAt
  have hFev : ∀ᶠ s in 𝓝 (‖z‖ ^ 2), DifferentiableAt ℝ F s :=
    (hF.eventually (by simp)).mono fun s hs ↦ hs.differentiableAt (by norm_num)
  have hev : ∀ᶠ w in 𝓝 z, DifferentiableAt ℝ F (‖w‖ ^ 2) :=
    Filter.Tendsto.eventually hns.continuous.continuousAt hFev
  have hF' : DifferentiableAt ℝ (deriv F) (‖z‖ ^ 2) :=
    ((hF.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt
      (by norm_num)
  have hdbar : dbar (cplx (fun w ↦ F (‖w‖ ^ 2))) =ᶠ[𝓝 z]
      fun w ↦ cplx (fun u ↦ deriv F (‖u‖ ^ 2)) w * w :=
    hev.mono fun w hw ↦ dbar_cplx_comp_normSq hw
  have hg0 : DifferentiableAt ℝ (fun u : ℂ ↦ deriv F (‖u‖ ^ 2)) z := by
    have h2 : DifferentiableAt ℝ (fun w : ℂ ↦ ‖w‖ ^ 2) z := hns.differentiable (by norm_num) z
    exact hF'.comp z h2
  have hg : DifferentiableAt ℝ (cplx (fun u ↦ deriv F (‖u‖ ^ 2))) z :=
    ofRealCLM.differentiableAt.comp z hg0
  apply Complex.ofReal_injective
  rw [← dz_dbar_cplx hfC2, dz_congr hdbar, dz_mul hg differentiableAt_fun_id, dz_id,
    dz_cplx_eq_conj_dbar, dbar_cplx_comp_normSq hF']
  simp only [map_mul, conj_ofReal, cplx]
  rw [mul_assoc, conj_mul']
  push_cast
  ring

theorem lap_log_normSq {z : ℂ} (hz : z ≠ 0) : lap (fun w ↦ Real.log (‖w‖ ^ 2)) z = 0 := by
  have ht : ‖z‖ ^ 2 ≠ 0 := by positivity
  rw [lap_comp_normSq (Real.contDiffAt_log.2 ht), Real.deriv_log', deriv_inv]
  field_simp
  ring

theorem lap_const_mul_normSq (α : ℝ) (z : ℂ) : lap (fun w ↦ α * ‖w‖ ^ 2) z = α := by
  have h := lap_comp_normSq (F := fun t ↦ α * t) (z := z) (contDiff_const.mul contDiff_id).contDiffAt
  rw [h]
  have : deriv (fun t : ℝ ↦ α * t) = fun _ ↦ α := by
    ext t; simp
  rw [this]
  simp

/-! ### Regularity and support of Wirtinger derivatives -/

/-- `∂̄u` is continuous on an open set where `u` is `C¹`. -/
theorem continuousOn_dbar {Ω : Set ℂ} (hΩ : IsOpen Ω) {u : ℂ → ℂ} (hu : ContDiffOn ℝ 1 u Ω) :
    ContinuousOn (dbar u) Ω := by
  have h := hu.continuousOn_fderiv_of_isOpen hΩ le_rfl
  have h1 : ContinuousOn (fun z ↦ fderiv ℝ u z 1) Ω := h.clm_apply continuousOn_const
  have hI : ContinuousOn (fun z ↦ fderiv ℝ u z I) Ω := h.clm_apply continuousOn_const
  exact continuousOn_const.mul (h1.add (continuousOn_const.mul hI))

theorem continuousOn_dz {Ω : Set ℂ} (hΩ : IsOpen Ω) {u : ℂ → ℂ} (hu : ContDiffOn ℝ 1 u Ω) :
    ContinuousOn (dz u) Ω := by
  have h := hu.continuousOn_fderiv_of_isOpen hΩ le_rfl
  have h1 : ContinuousOn (fun z ↦ fderiv ℝ u z 1) Ω := h.clm_apply continuousOn_const
  have hI : ContinuousOn (fun z ↦ fderiv ℝ u z I) Ω := h.clm_apply continuousOn_const
  exact continuousOn_const.mul (h1.sub (continuousOn_const.mul hI))

theorem contDiff_dbar {f : ℂ → ℂ} (hf : ContDiff ℝ 2 f) : ContDiff ℝ 1 (dbar f) := by
  have h : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have h1 : ContDiff ℝ 1 (fun z ↦ fderiv ℝ f z 1) := h.clm_apply contDiff_const
  have hI : ContDiff ℝ 1 (fun z ↦ fderiv ℝ f z I) := h.clm_apply contDiff_const
  exact contDiff_const.mul (h1.add (contDiff_const.mul hI))

theorem contDiff_dz {f : ℂ → ℂ} (hf : ContDiff ℝ 2 f) : ContDiff ℝ 1 (dz f) := by
  have h : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have h1 : ContDiff ℝ 1 (fun z ↦ fderiv ℝ f z 1) := h.clm_apply contDiff_const
  have hI : ContDiff ℝ 1 (fun z ↦ fderiv ℝ f z I) := h.clm_apply contDiff_const
  exact contDiff_const.mul (h1.sub (contDiff_const.mul hI))

/-- `∂̄f` is compactly supported when `f` is. -/
theorem hasCompactSupport_dbar {f : ℂ → ℂ} (hf : HasCompactSupport f) :
    HasCompactSupport (dbar f) := by
  refine (hf.fderiv (𝕜 := ℝ)).mono ?_
  intro z hz
  rw [Function.mem_support] at hz ⊢
  contrapose! hz
  simp [dbar, hz]

theorem hasCompactSupport_dz {f : ℂ → ℂ} (hf : HasCompactSupport f) :
    HasCompactSupport (dz f) := by
  refine (hf.fderiv (𝕜 := ℝ)).mono ?_
  intro z hz
  rw [Function.mem_support] at hz ⊢
  contrapose! hz
  simp [dz, hz]

theorem contDiff_cplx {n : WithTop ℕ∞} {φ : ℂ → ℝ} (hφ : ContDiff ℝ n φ) :
    ContDiff ℝ n (cplx φ) :=
  ofRealCLM.contDiff.comp hφ

theorem hasCompactSupport_cplx {φ : ℂ → ℝ} (hφ : HasCompactSupport φ) :
    HasCompactSupport (cplx φ) :=
  hφ.comp_left (g := ((↑) : ℝ → ℂ)) Complex.ofReal_zero

/-! ### Integration by parts -/

/-- A function continuous on an open set `Ω`, times a continuous function whose topological support
lies in `Ω`, is continuous on all of `ℂ`. -/
theorem continuous_mul_of_tsupport_subset {Ω : Set ℂ} (hΩ : IsOpen Ω) {h β : ℂ → ℂ}
    (hh : ContinuousOn h Ω) (hβ : Continuous β) (hs : tsupport β ⊆ Ω) :
    Continuous (fun x ↦ h x * β x) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x ∈ Ω
  · exact (hh.continuousAt (hΩ.mem_nhds hx)).mul hβ.continuousAt
  · have hx' : x ∉ tsupport β := fun h' ↦ hx (hs h')
    rw [notMem_tsupport_iff_eventuallyEq] at hx'
    have : (fun _ ↦ (0 : ℂ)) =ᶠ[𝓝 x] fun x ↦ h x * β x := by
      filter_upwards [hx'] with y hy
      simp [hy]
    exact continuousAt_const.congr this

theorem integrable_mul_of_tsupport_subset {Ω : Set ℂ} (hΩ : IsOpen Ω) {h β : ℂ → ℂ}
    (hh : ContinuousOn h Ω) (hβ : Continuous β) (hc : HasCompactSupport β)
    (hs : tsupport β ⊆ Ω) : Integrable (fun x ↦ h x * β x) :=
  (continuous_mul_of_tsupport_subset hΩ hh hβ hs).integrable_of_hasCompactSupport
    (hc.mul_left (f := h))

theorem integrable_mul_of_tsupport_subset' {Ω : Set ℂ} (hΩ : IsOpen Ω) {h β : ℂ → ℂ}
    (hh : ContinuousOn h Ω) (hβ : Continuous β) (hc : HasCompactSupport β)
    (hs : tsupport β ⊆ Ω) : Integrable (fun x ↦ β x * h x) := by
  simpa only [mul_comm] using integrable_mul_of_tsupport_subset hΩ hh hβ hc hs

/-- Integration by parts in a fixed real direction `v`. -/
theorem integral_mul_fderiv_eq_neg {Ω : Set ℂ} (hΩ : IsOpen Ω) {u α : ℂ → ℂ}
    (hu : ContDiffOn ℝ 1 u Ω) (hα : ContDiff ℝ 1 α) (hc : HasCompactSupport α)
    (hs : tsupport α ⊆ Ω) (v : ℂ) :
    ∫ z, u z * fderiv ℝ α z v = -∫ z, fderiv ℝ u z v * α z := by
  have hdu : ContinuousOn (fun z ↦ fderiv ℝ u z v) Ω :=
    (hu.continuousOn_fderiv_of_isOpen hΩ le_rfl).clm_apply continuousOn_const
  have hdα : Continuous (fun z ↦ fderiv ℝ α z v) :=
    (hα.continuous_fderiv one_ne_zero).clm_apply continuous_const
  refine integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable ?_ ?_ ?_ ?_ ?_
  · exact integrable_mul_of_tsupport_subset hΩ hdu hα.continuous hc hs
  · exact integrable_mul_of_tsupport_subset hΩ hu.continuousOn hdα (hc.fderiv_apply (𝕜 := ℝ) v)
      ((tsupport_fderiv_apply_subset ℝ v).trans hs)
  · exact integrable_mul_of_tsupport_subset hΩ hu.continuousOn hα.continuous hc hs
  · intro x hx
    exact (hu.differentiableOn one_ne_zero x (hs hx)).differentiableAt (hΩ.mem_nhds (hs hx))
  · intro x _
    exact hα.differentiable one_ne_zero x

/-- Integration by parts for a combination `a ∂_x + b ∂_y`. -/
theorem integral_mul_comb_eq_neg {Ω : Set ℂ} (hΩ : IsOpen Ω) {u α : ℂ → ℂ}
    (hu : ContDiffOn ℝ 1 u Ω) (hα : ContDiff ℝ 1 α) (hc : HasCompactSupport α)
    (hs : tsupport α ⊆ Ω) (a b : ℂ) :
    ∫ z, u z * (a * fderiv ℝ α z 1 + b * fderiv ℝ α z I) =
      -∫ z, (a * fderiv ℝ u z 1 + b * fderiv ℝ u z I) * α z := by
  have hdu : ∀ v, ContinuousOn (fun z ↦ fderiv ℝ u z v) Ω := fun v ↦
    (hu.continuousOn_fderiv_of_isOpen hΩ le_rfl).clm_apply continuousOn_const
  have hdα : ∀ v, Continuous (fun z ↦ fderiv ℝ α z v) := fun v ↦
    (hα.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have i : ∀ v, Integrable (fun z ↦ u z * fderiv ℝ α z v) := fun v ↦
    integrable_mul_of_tsupport_subset hΩ hu.continuousOn (hdα v) (hc.fderiv_apply (𝕜 := ℝ) v)
      ((tsupport_fderiv_apply_subset ℝ v).trans hs)
  have j : ∀ v, Integrable (fun z ↦ fderiv ℝ u z v * α z) := fun v ↦
    integrable_mul_of_tsupport_subset hΩ (hdu v) hα.continuous hc hs
  calc ∫ z, u z * (a * fderiv ℝ α z 1 + b * fderiv ℝ α z I)
      = ∫ z, (a * (u z * fderiv ℝ α z 1) + b * (u z * fderiv ℝ α z I)) := by
        congr 1; ext z; ring
    _ = a * (∫ z, u z * fderiv ℝ α z 1) + b * (∫ z, u z * fderiv ℝ α z I) := by
        rw [integral_add ((i 1).const_mul a) ((i I).const_mul b), integral_const_mul,
          integral_const_mul]
    _ = -(a * (∫ z, fderiv ℝ u z 1 * α z) + b * (∫ z, fderiv ℝ u z I * α z)) := by
        rw [integral_mul_fderiv_eq_neg hΩ hu hα hc hs 1,
          integral_mul_fderiv_eq_neg hΩ hu hα hc hs I]
        ring
    _ = -∫ z, (a * fderiv ℝ u z 1 + b * fderiv ℝ u z I) * α z := by
        rw [← integral_const_mul, ← integral_const_mul,
          ← integral_add ((j 1).const_mul a) ((j I).const_mul b)]
        congr 2; ext z; ring

theorem integral_mul_dbar' {Ω : Set ℂ} (hΩ : IsOpen Ω) {u α : ℂ → ℂ} (hu : ContDiffOn ℝ 1 u Ω)
    (hα : ContDiff ℝ 1 α) (hc : HasCompactSupport α) (hs : tsupport α ⊆ Ω) :
    ∫ z, u z * dbar α z = -∫ z, dbar u z * α z := by
  have h := integral_mul_comb_eq_neg hΩ hu hα hc hs (1 / 2) (1 / 2 * I)
  have e1 : (fun z ↦ u z * dbar α z) =
      fun z ↦ u z * ((1 / 2) * fderiv ℝ α z 1 + (1 / 2 * I) * fderiv ℝ α z I) := by
    ext z; simp only [dbar]; ring
  have e2 : (fun z ↦ dbar u z * α z) =
      fun z ↦ ((1 / 2) * fderiv ℝ u z 1 + (1 / 2 * I) * fderiv ℝ u z I) * α z := by
    ext z; simp only [dbar]; ring
  rw [e1, e2]
  exact h

theorem integral_mul_dz' {Ω : Set ℂ} (hΩ : IsOpen Ω) {u α : ℂ → ℂ} (hu : ContDiffOn ℝ 1 u Ω)
    (hα : ContDiff ℝ 1 α) (hc : HasCompactSupport α) (hs : tsupport α ⊆ Ω) :
    ∫ z, u z * dz α z = -∫ z, dz u z * α z := by
  have h := integral_mul_comb_eq_neg hΩ hu hα hc hs (1 / 2) (-(1 / 2) * I)
  have e1 : (fun z ↦ u z * dz α z) =
      fun z ↦ u z * ((1 / 2) * fderiv ℝ α z 1 + (-(1 / 2) * I) * fderiv ℝ α z I) := by
    ext z; simp only [dz]; ring
  have e2 : (fun z ↦ dz u z * α z) =
      fun z ↦ ((1 / 2) * fderiv ℝ u z 1 + (-(1 / 2) * I) * fderiv ℝ u z I) * α z := by
    ext z; simp only [dz]; ring
  rw [e1, e2]
  exact h

theorem integral_dbar_eq_zero {A : ℂ → ℂ} (hA : ContDiff ℝ 1 A) (hc : HasCompactSupport A) :
    ∫ z, dbar A z = 0 := by
  have h := integral_mul_dbar' isOpen_univ (u := fun _ ↦ (1 : ℂ)) contDiffOn_const hA hc
    (subset_univ _)
  simpa [dbar] using h

theorem integral_dz_eq_zero {A : ℂ → ℂ} (hA : ContDiff ℝ 1 A) (hc : HasCompactSupport A) :
    ∫ z, dz A z = 0 := by
  have h := integral_mul_dz' isOpen_univ (u := fun _ ↦ (1 : ℂ)) contDiffOn_const hA hc
    (subset_univ _)
  simpa [dz] using h

theorem integral_mul_dbar {Ω : Set ℂ} (hΩ : IsOpen Ω) {u α : ℂ → ℂ} (hu : ContDiffOn ℝ 1 u Ω)
    (hα : ContDiff ℝ 1 α) (hc : HasCompactSupport α) (hs : tsupport α ⊆ Ω) :
    ∫ z, u z * dbar α z = -∫ z, dbar u z * α z :=
  integral_mul_dbar' hΩ hu hα hc hs

theorem isWeakDbarSol_of_contDiffOn {Ω : Set ℂ} (hΩ : IsOpen Ω) {u : ℂ → ℂ}
    (hu : ContDiffOn ℝ 1 u Ω) : IsWeakDbarSol Ω u (dbar u) := by
  refine ⟨hu.continuousOn.locallyIntegrableOn hΩ.measurableSet,
    (continuousOn_dbar hΩ hu).locallyIntegrableOn hΩ.measurableSet, ?_⟩
  intro α hα hc hs
  exact integral_mul_dbar hΩ hu (hα.of_le (by exact_mod_cast le_top)) hc hs

theorem integral_mul_lap {g U : ℂ → ℝ} (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hU : ContDiff ℝ 2 U) : ∫ z, g z * lap U z = ∫ z, lap g z * U z := by
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal, ← integral_complex_ofReal]
  push_cast
  have hU2 : ∀ z, (lap U z : ℂ) = dbar (dz (cplx U)) z := fun z ↦
    (dbar_dz_cplx hU.contDiffAt).symm
  have hg2 : ∀ z, (lap g z : ℂ) = dz (dbar (cplx g)) z := fun z ↦
    (dz_dbar_cplx hg.contDiffAt).symm
  simp_rw [hU2, hg2]
  have hgC : ContDiff ℝ 2 (cplx g) := contDiff_cplx hg
  have hUC : ContDiff ℝ 2 (cplx U) := contDiff_cplx hU
  have hgcC : HasCompactSupport (cplx g) := hasCompactSupport_cplx hgc
  -- first integration by parts (`∂̄`)
  have h1 := integral_mul_dbar isOpen_univ (u := dz (cplx U)) (α := cplx g)
    (contDiff_dz hUC).contDiffOn (hgC.of_le (by norm_num)) hgcC (subset_univ _)
  -- second integration by parts (`∂`)
  have h2 := integral_mul_dz' isOpen_univ (u := cplx U) (α := dbar (cplx g))
    (hUC.of_le (by norm_num)).contDiffOn (contDiff_dbar hgC) (hasCompactSupport_dbar hgcC)
    (subset_univ _)
  calc ∫ z, (g z : ℂ) * dbar (dz (cplx U)) z = ∫ z, dbar (dz (cplx U)) z * cplx g z := by
        congr 1; ext z; simp only [cplx]; ring
    _ = -∫ z, dz (cplx U) z * dbar (cplx g) z := by rw [h1, neg_neg]
    _ = ∫ z, cplx U z * dz (dbar (cplx g)) z := h2.symm
    _ = ∫ z, dz (dbar (cplx g)) z * (U z : ℂ) := by
        congr 1; ext z; simp only [cplx]; ring

/-! ### The key identity (W14) -/

theorem dbar_neg (f : ℂ → ℂ) (z : ℂ) : dbar (fun w ↦ -f w) z = -dbar f z := by
  simp only [dbar, fderiv_fun_neg, _root_.neg_apply]; ring

theorem dz_neg (f : ℂ → ℂ) (z : ℂ) : dz (fun w ↦ -f w) z = -dz f z := by
  simp only [dz, fderiv_fun_neg, _root_.neg_apply]; ring

theorem differentiableAt_conj {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z) :
    DifferentiableAt ℝ (fun w ↦ conj (f w)) z :=
  ((conjCLE : ℂ ≃L[ℝ] ℂ).hasFDerivAt.comp z hf.hasFDerivAt).differentiableAt

/-- `∂̄` of `|h|² e^{-ψ}` for `h` entire, at a point where `ψ` is differentiable. -/
theorem dbar_normSq_mul_exp {h : ℂ → ℂ} {ψ : ℂ → ℝ} {w : ℂ} (hh : Differentiable ℂ h)
    (hψ : DifferentiableAt ℝ ψ w) :
    dbar (cplx (fun w ↦ ‖h w‖ ^ 2 * Real.exp (-ψ w))) w =
      h w * Complex.exp (-(cplx ψ w)) * conj (deriv h w - h w * dz (cplx ψ) w) := by
  have hhR : DifferentiableAt ℝ h w := (hh w).restrictScalars ℝ
  have hcψ : DifferentiableAt ℝ (cplx ψ) w := ofRealCLM.differentiableAt.comp w hψ
  have hncψ : DifferentiableAt ℝ (fun w ↦ -(cplx ψ w)) w := hcψ.neg
  have hEw : DifferentiableAt ℝ (fun w ↦ Complex.exp (-(cplx ψ w))) w := hncψ.cexp
  have e : cplx (fun w ↦ ‖h w‖ ^ 2 * Real.exp (-ψ w)) =
      fun w ↦ h w * (conj (h w) * Complex.exp (-(cplx ψ w))) := by
    ext w
    simp only [cplx]
    push_cast
    rw [← mul_assoc, mul_conj']
  have hcE : DifferentiableAt ℝ (fun w ↦ conj (h w) * Complex.exp (-(cplx ψ w))) w :=
    (differentiableAt_conj hhR).mul hEw
  rw [e, dbar_mul hhR hcE,
    dbar_mul (differentiableAt_conj hhR) hEw, dbar_conj hhR, dz_eq_deriv (hh w),
    dbar_eq_zero_of_differentiableAt (hh w), dbar_cexp hncψ, dbar_neg,
    dbar_cplx_eq_conj_dz]
  simp only [map_sub, map_mul]
  ring

theorem lap_normSq_mul_exp {h : ℂ → ℂ} {ψ : ℂ → ℝ} {z : ℂ} (hh : Differentiable ℂ h)
    (hψ : ContDiffAt ℝ 2 ψ z) :
    lap (fun w ↦ ‖h w‖ ^ 2 * Real.exp (-ψ w)) z =
      ‖deriv h z - h z * dz (cplx ψ) z‖ ^ 2 * Real.exp (-ψ z)
        - ‖h z‖ ^ 2 * Real.exp (-ψ z) * lap ψ z := by
  have hhR : ∀ w, DifferentiableAt ℝ h w := fun w ↦ (hh w).restrictScalars ℝ
  have hh' : Differentiable ℂ (deriv h) := fun w ↦ (hh.analyticAt w).deriv.differentiableAt
  have hh'R : ∀ w, DifferentiableAt ℝ (deriv h) w := fun w ↦ (hh' w).restrictScalars ℝ
  have hhC : ContDiff ℝ 2 h := (hh.contDiff (n := 2)).restrict_scalars ℝ
  have hU : ContDiffAt ℝ 2 (fun w ↦ ‖h w‖ ^ 2 * Real.exp (-ψ w)) z :=
    ((contDiff_norm_sq ℝ).comp hhC).contDiffAt.mul
      (Real.contDiff_exp.contDiffAt.comp z hψ.neg)
  have hψev : ∀ᶠ w in 𝓝 z, DifferentiableAt ℝ ψ w :=
    (hψ.eventually (by simp)).mono fun w hw ↦ hw.differentiableAt (by norm_num)
  have hev : dbar (cplx (fun w ↦ ‖h w‖ ^ 2 * Real.exp (-ψ w))) =ᶠ[𝓝 z]
      fun w ↦ h w * Complex.exp (-(cplx ψ w)) * conj (deriv h w - h w * dz (cplx ψ) w) :=
    hψev.mono fun w hw ↦ dbar_normSq_mul_exp hh hw
  have hcψC2 : ContDiffAt ℝ 2 (cplx ψ) z := contDiffAt_cplx hψ
  have hcψ : DifferentiableAt ℝ (cplx ψ) z := hcψC2.differentiableAt (by norm_num)
  have hncψ : DifferentiableAt ℝ (fun w ↦ -(cplx ψ w)) z := hcψ.neg
  have hEz : DifferentiableAt ℝ (fun w ↦ Complex.exp (-(cplx ψ w))) z := hncψ.cexp
  have hdzψ : DifferentiableAt ℝ (dz (cplx ψ)) z :=
    differentiableAt_dz (differentiableAt_fderiv_of_contDiffAt hcψC2)
  have hGz : DifferentiableAt ℝ (fun w ↦ deriv h w - h w * dz (cplx ψ) w) z :=
    (hh'R z).sub ((hhR z).mul hdzψ)
  have hhdz : DifferentiableAt ℝ (fun w ↦ h w * dz (cplx ψ) w) z := (hhR z).mul hdzψ
  have hhE : DifferentiableAt ℝ (fun w ↦ h w * Complex.exp (-(cplx ψ w))) z := (hhR z).mul hEz
  have hdbarG : dbar (fun w ↦ deriv h w - h w * dz (cplx ψ) w) z = -(h z * (lap ψ z : ℂ)) := by
    rw [dbar_sub (hh'R z) hhdz, dbar_mul (hhR z) hdzψ,
      dbar_eq_zero_of_differentiableAt (hh' z), dbar_eq_zero_of_differentiableAt (hh z),
      dbar_dz_cplx hψ]
    ring
  apply Complex.ofReal_injective
  rw [← dz_dbar_cplx hU, dz_congr hev, dz_mul hhE (differentiableAt_conj hGz),
    dz_mul (hhR z) hEz, dz_conj hGz, dz_eq_deriv (hh z), dz_cexp' hncψ, dz_neg, hdbarG]
  push_cast
  rw [← mul_conj', ← mul_conj' (h z)]
  simp only [cplx, map_neg, map_mul, conj_ofReal]
  ring

/-- `∂/∂z` of `exp ∘ f`. -/
theorem dz_cexp {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z) :
    dz (fun w ↦ Complex.exp (f w)) z = Complex.exp (f z) * dz f z :=
  dz_cexp' hf

/-- The Wirtinger derivatives commute on `C²` functions. -/
theorem dz_dbar_comm {f : ℂ → ℂ} {z : ℂ} (hf : ContDiffAt ℝ 2 f z) :
    dz (dbar f) z = dbar (dz f) z := by
  rw [dz_dbar_eq_laplacian hf, dbar_dz_eq_laplacian hf]

/-- Integration by parts for `∂/∂z` (companion of `integral_mul_dbar`). -/
theorem integral_mul_dz {Ω : Set ℂ} (hΩ : IsOpen Ω) {u α : ℂ → ℂ} (hu : ContDiffOn ℝ 1 u Ω)
    (hα : ContDiff ℝ 1 α) (hc : HasCompactSupport α) (hs : tsupport α ⊆ Ω) :
    ∫ z, u z * dz α z = -∫ z, dz u z * α z :=
  integral_mul_dz' hΩ hu hα hc hs

end OCS
