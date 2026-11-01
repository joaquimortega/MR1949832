import OrtegaCerdaMultipliers.Foundations.Basic
import OrtegaCerdaMultipliers.Foundations.Wirtinger
import OrtegaCerdaMultipliers.Foundations.Polar
import OrtegaCerdaMultipliers.Foundations.Separated

/-!
# M01 (Foundations) — Geometry of the unit disc: Möbius maps, invariant Laplacian, separated sets

See `blueprint/M01_Foundations.md`.

**Provenance.** Copied from `BerndtssonOrtegaCerda/Disc/Geometry.lean`
(BOC module M15, blueprint `M15_DiscGeometry.md`) of the companion project
`../1995ReineAngewMath` at commit `22104d9` (same author, Apache-2.0).  Changes: namespace
`BOC` → `OC`, imports adjusted; the BOC definitions not in `OrtegaCerdaMultipliers/Defs.lean`
are in `Foundations/Basic.lean`.
The proofs that unfolded BOC's `pseudoHyp z ζ = ‖mobius z ζ‖` now rewrite with
`pseudoHyp_eq_norm_mobius` (RMI defines `pseudoHyp z w = ‖z - w‖ / ‖1 - z̄ w‖`).
-/

open MeasureTheory Metric Set Complex
open scoped ENNReal NNReal ComplexConjugate Topology

noncomputable section

namespace OC

/-! ### Elementary facts about the disc and Möbius maps -/

theorem norm_lt_one_of_mem_disc {z : ℂ} (hz : z ∈ 𝔻) : ‖z‖ < 1 := by
  simpa using hz

theorem mem_disc_iff_norm_lt_one {z : ℂ} : z ∈ 𝔻 ↔ ‖z‖ < 1 := by
  simp

theorem one_sub_normSq_pos {z : ℂ} (hz : z ∈ 𝔻) : 0 < 1 - ‖z‖ ^ 2 := by
  have h := norm_lt_one_of_mem_disc hz
  nlinarith [norm_nonneg z]

/-- `‖1 - ā ζ‖ ≥ 1 - ‖a‖ ‖ζ‖`. -/
theorem one_sub_mul_le_norm_one_sub_conj_mul (a ζ : ℂ) :
    1 - ‖a‖ * ‖ζ‖ ≤ ‖1 - conj a * ζ‖ := by
  have h := norm_sub_norm_le (1 : ℂ) (conj a * ζ)
  simpa [norm_mul, Complex.norm_conj] using h

/-- `‖1 - ā ζ‖ ≤ 1 + ‖a‖ ‖ζ‖`. -/
theorem norm_one_sub_conj_mul_le (a ζ : ℂ) : ‖1 - conj a * ζ‖ ≤ 1 + ‖a‖ * ‖ζ‖ := by
  have h := norm_sub_le (1 : ℂ) (conj a * ζ)
  simpa [norm_mul, Complex.norm_conj] using h

theorem one_sub_conj_mul_ne_zero {a ζ : ℂ} (h : ‖a‖ * ‖ζ‖ < 1) : 1 - conj a * ζ ≠ 0 := by
  intro h0
  have := one_sub_mul_le_norm_one_sub_conj_mul a ζ
  rw [h0, norm_zero] at this
  linarith

theorem norm_mul_lt_one {a ζ : ℂ} (ha : a ∈ 𝔻) (hζ : ζ ∈ 𝔻) : ‖a‖ * ‖ζ‖ < 1 := by
  have h1 := norm_lt_one_of_mem_disc ha
  have h2 := norm_lt_one_of_mem_disc hζ
  nlinarith [norm_nonneg a, norm_nonneg ζ]

theorem one_sub_conj_mul_ne_zero_of_mem {a ζ : ℂ} (ha : a ∈ 𝔻) (hζ : ζ ∈ 𝔻) :
    1 - conj a * ζ ≠ 0 :=
  one_sub_conj_mul_ne_zero (norm_mul_lt_one ha hζ)

theorem norm_one_sub_conj_mul_pos {a ζ : ℂ} (ha : a ∈ 𝔻) (hζ : ζ ∈ 𝔻) :
    0 < ‖1 - conj a * ζ‖ :=
  norm_pos_iff.2 (one_sub_conj_mul_ne_zero_of_mem ha hζ)

/-- The key real identity `|1 - āζ|² - |a - ζ|² = (1 - |a|²)(1 - |ζ|²)`. -/
theorem norm_one_sub_conj_mul_sq_sub (a ζ : ℂ) :
    ‖1 - conj a * ζ‖ ^ 2 - ‖a - ζ‖ ^ 2 = (1 - ‖a‖ ^ 2) * (1 - ‖ζ‖ ^ 2) := by
  simp only [Complex.sq_norm, Complex.normSq_apply, sub_re, sub_im, mul_re, mul_im, conj_re,
    conj_im, one_re, one_im]
  ring

theorem one_sub_conj_mul_self_ne_zero {a : ℂ} (ha : a ∈ 𝔻) : 1 - conj a * a ≠ 0 :=
  one_sub_conj_mul_ne_zero_of_mem ha ha

/-- `1 - ā a = 1 - |a|²` as complex numbers. -/
theorem one_sub_conj_mul_self (a : ℂ) : 1 - conj a * a = ((1 - ‖a‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.conj_mul']
  push_cast
  ring

theorem norm_one_sub_conj_mul_self {a : ℂ} (ha : a ∈ 𝔻) : ‖1 - conj a * a‖ = 1 - ‖a‖ ^ 2 := by
  rw [one_sub_conj_mul_self, Complex.norm_of_nonneg (one_sub_normSq_pos ha).le]

theorem one_sub_normSq_mobius {a ζ : ℂ} (ha : a ∈ 𝔻) (hζ : ζ ∈ 𝔻) :
    1 - ‖mobius a ζ‖ ^ 2 = (1 - ‖a‖ ^ 2) * (1 - ‖ζ‖ ^ 2) / ‖1 - conj a * ζ‖ ^ 2 := by
  have hD := norm_one_sub_conj_mul_pos ha hζ
  rw [mobius, norm_div, div_pow, ← norm_one_sub_conj_mul_sq_sub, sub_div,
    div_self (by positivity)]

theorem mobius_mem_disc {a ζ : ℂ} (ha : a ∈ 𝔻) (hζ : ζ ∈ 𝔻) : mobius a ζ ∈ 𝔻 := by
  have h := one_sub_normSq_mobius ha hζ
  have hpos : 0 < (1 - ‖a‖ ^ 2) * (1 - ‖ζ‖ ^ 2) / ‖1 - conj a * ζ‖ ^ 2 := by
    have := norm_one_sub_conj_mul_pos ha hζ
    have := one_sub_normSq_pos ha
    have := one_sub_normSq_pos hζ
    positivity
  rw [mem_disc_iff_norm_lt_one]
  have h2 : ‖mobius a ζ‖ ^ 2 < 1 := by linarith
  nlinarith [norm_nonneg (mobius a ζ)]

theorem mobius_self (a : ℂ) : mobius a a = 0 := by
  simp [mobius]

theorem mobius_zero (a : ℂ) : mobius a 0 = a := by
  simp [mobius]

theorem zero_mobius (ζ : ℂ) : mobius 0 ζ = -ζ := by
  simp [mobius]

theorem sub_mobius {a ζ : ℂ} (hζ : 1 - conj a * ζ ≠ 0) :
    a - mobius a ζ = ζ * (1 - conj a * a) / (1 - conj a * ζ) := by
  unfold mobius
  rw [eq_div_iff hζ, sub_mul, div_mul_cancel₀ _ hζ]
  ring

theorem mobius_sub_self {a ζ : ℂ} (hζ : 1 - conj a * ζ ≠ 0) :
    mobius a ζ - a = -(ζ * (1 - conj a * a)) / (1 - conj a * ζ) := by
  rw [← neg_sub, sub_mobius hζ, neg_div]

theorem one_sub_conj_mul_mobius {a ζ : ℂ} (hζ : 1 - conj a * ζ ≠ 0) :
    1 - conj a * mobius a ζ = (1 - conj a * a) / (1 - conj a * ζ) := by
  unfold mobius
  rw [eq_div_iff hζ, sub_mul, mul_assoc, div_mul_cancel₀ _ hζ]
  ring

theorem mobius_mobius {a ζ : ℂ} (ha : a ∈ 𝔻) (hζ : ζ ∈ 𝔻) : mobius a (mobius a ζ) = ζ := by
  have h1 := one_sub_conj_mul_ne_zero_of_mem ha hζ
  have h2 := one_sub_conj_mul_self_ne_zero ha
  rw [mobius, sub_mobius h1, one_sub_conj_mul_mobius h1, div_div_div_cancel_right₀ h1,
    mul_div_cancel_right₀ _ h2]

theorem injOn_mobius {a : ℂ} (ha : a ∈ 𝔻) : InjOn (mobius a) 𝔻 := by
  intro x hx y hy hxy
  rw [← mobius_mobius ha hx, hxy, mobius_mobius ha hy]

theorem mobius_image_disc {a : ℂ} (ha : a ∈ 𝔻) : mobius a '' 𝔻 = 𝔻 := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact mobius_mem_disc ha hw
  · intro hz
    exact ⟨mobius a z, mobius_mem_disc ha hz, mobius_mobius ha hz⟩

/-! ### Derivative of the Möbius map -/

theorem hasDerivAt_mobius {a ζ : ℂ} (h : 1 - conj a * ζ ≠ 0) :
    HasDerivAt (mobius a) (-(1 - conj a * a) / (1 - conj a * ζ) ^ 2) ζ := by
  have h1 : HasDerivAt (fun w ↦ a - w) (-1) ζ := (hasDerivAt_id ζ).const_sub a
  have h2 : HasDerivAt (fun w ↦ 1 - conj a * w) (-(conj a * 1)) ζ :=
    ((hasDerivAt_id ζ).const_mul (conj a)).const_sub 1
  have := h1.div h2 h
  have e : ((fun w ↦ a - w) / fun w ↦ 1 - conj a * w) = mobius a := rfl
  rw [e] at this
  convert this using 1
  ring

theorem differentiableOn_mobius {a : ℂ} (ha : a ∈ 𝔻) : DifferentiableOn ℂ (mobius a) 𝔻 :=
  fun _ hζ ↦ (hasDerivAt_mobius (one_sub_conj_mul_ne_zero_of_mem ha hζ)).differentiableAt
    |>.differentiableWithinAt

theorem differentiableAt_mobius {a ζ : ℂ} (ha : a ∈ 𝔻) (hζ : ζ ∈ 𝔻) :
    DifferentiableAt ℂ (mobius a) ζ :=
  (hasDerivAt_mobius (one_sub_conj_mul_ne_zero_of_mem ha hζ)).differentiableAt

theorem eventually_differentiableAt_mobius {a ζ : ℂ} (ha : a ∈ 𝔻) (hζ : ζ ∈ 𝔻) :
    ∀ᶠ w in 𝓝 ζ, DifferentiableAt ℂ (mobius a) w :=
  Filter.eventually_of_mem (isOpen_ball.mem_nhds hζ) fun _ hw ↦ differentiableAt_mobius ha hw

theorem deriv_mobius {a ζ : ℂ} (ha : a ∈ 𝔻) (hζ : ζ ∈ 𝔻) :
    deriv (mobius a) ζ = -(1 - ‖a‖ ^ 2 : ℂ) / (1 - conj a * ζ) ^ 2 := by
  rw [(hasDerivAt_mobius (one_sub_conj_mul_ne_zero_of_mem ha hζ)).deriv, Complex.conj_mul']

theorem norm_deriv_mobius {a ζ : ℂ} (ha : a ∈ 𝔻) (hζ : ζ ∈ 𝔻) :
    ‖deriv (mobius a) ζ‖ = (1 - ‖mobius a ζ‖ ^ 2) / (1 - ‖ζ‖ ^ 2) := by
  have hD := norm_one_sub_conj_mul_pos ha hζ
  have hζ' := one_sub_normSq_pos hζ
  have ha' := one_sub_normSq_pos ha
  rw [deriv_mobius ha hζ, one_sub_normSq_mobius ha hζ, norm_div, norm_neg, norm_pow]
  have : (1 - (‖a‖ : ℂ) ^ 2) = ((1 - ‖a‖ ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [this, Complex.norm_of_nonneg ha'.le]
  field_simp

/-! ### Möbius invariance of the pseudo-hyperbolic distance -/

theorem pseudoHyp_comm (z ζ : ℂ) : pseudoHyp z ζ = pseudoHyp ζ z := by
  rw [pseudoHyp_eq_norm_mobius, pseudoHyp_eq_norm_mobius]
  unfold mobius
  rw [norm_div, norm_div, norm_sub_rev z ζ]
  congr 1
  rw [← Complex.norm_conj (1 - conj z * ζ)]
  simp [mul_comm]

theorem pseudoHyp_self (z : ℂ) : pseudoHyp z z = 0 := by
  simp [pseudoHyp_eq_norm_mobius, mobius_self]

theorem pseudoHyp_zero_left (ζ : ℂ) : pseudoHyp 0 ζ = ‖ζ‖ := by
  simp [pseudoHyp_eq_norm_mobius, zero_mobius]

theorem pseudoHyp_zero_right (z : ℂ) : pseudoHyp z 0 = ‖z‖ := by
  simp [pseudoHyp_eq_norm_mobius, mobius_zero]

theorem pseudoHyp_nonneg (z ζ : ℂ) : 0 ≤ pseudoHyp z ζ :=
  (pseudoHyp_eq_norm_mobius z ζ).symm ▸ norm_nonneg _

theorem pseudoHyp_lt_one {z ζ : ℂ} (hz : z ∈ 𝔻) (hζ : ζ ∈ 𝔻) : pseudoHyp z ζ < 1 :=
  (pseudoHyp_eq_norm_mobius z ζ).symm ▸ norm_lt_one_of_mem_disc (mobius_mem_disc hz hζ)

theorem mobius_sub_mobius {a u v : ℂ} (hu : 1 - conj a * u ≠ 0) (hv : 1 - conj a * v ≠ 0) :
    mobius a u - mobius a v =
      (1 - conj a * a) * (v - u) / ((1 - conj a * u) * (1 - conj a * v)) := by
  unfold mobius
  rw [div_sub_div _ _ hu hv]
  ring

theorem one_sub_conj_mobius_mul_mobius {a u v : ℂ} (hu : 1 - conj a * u ≠ 0)
    (hv : 1 - conj a * v ≠ 0) :
    1 - conj (mobius a u) * mobius a v =
      (1 - conj a * a) * (1 - conj u * v) / ((1 - a * conj u) * (1 - conj a * v)) := by
  have hu' : 1 - a * conj u ≠ 0 := by
    intro h
    apply hu
    have := congrArg conj h
    simpa using this
  unfold mobius
  simp only [map_div₀, map_sub, map_mul, conj_conj, map_one]
  rw [div_mul_div_comm, one_sub_div (mul_ne_zero hu' hv)]
  ring

theorem mobius_mobius_mobius {a u v : ℂ} (ha : a ∈ 𝔻) (hu : u ∈ 𝔻) (hv : v ∈ 𝔻) :
    mobius (mobius a u) (mobius a v) = -((1 - a * conj u) / (1 - conj a * u)) * mobius u v := by
  have h1 := one_sub_conj_mul_ne_zero_of_mem ha hu
  have h2 := one_sub_conj_mul_ne_zero_of_mem ha hv
  have h3 := one_sub_conj_mul_ne_zero_of_mem hu hv
  have h4 := one_sub_conj_mul_self_ne_zero ha
  have h5 : 1 - a * conj u ≠ 0 := by
    intro h
    apply h1
    have := congrArg conj h
    simpa using this
  have h6 : 1 - conj u * v ≠ 0 := h3
  rw [show mobius (mobius a u) (mobius a v) =
      (mobius a u - mobius a v) / (1 - conj (mobius a u) * mobius a v) from rfl,
    mobius_sub_mobius h1 h2, one_sub_conj_mobius_mul_mobius h1 h2, div_div_div_eq, mobius,
    neg_mul, div_mul_div_comm, ← neg_div, eq_div_iff (mul_ne_zero h1 h6), div_mul_eq_mul_div,
    div_eq_iff (mul_ne_zero (mul_ne_zero h1 h2) (mul_ne_zero h4 h6))]
  ring

theorem pseudoHyp_mobius {a u v : ℂ} (ha : a ∈ 𝔻) (hu : u ∈ 𝔻) (hv : v ∈ 𝔻) :
    pseudoHyp (mobius a u) (mobius a v) = pseudoHyp u v := by
  have h1 := one_sub_conj_mul_ne_zero_of_mem ha hu
  rw [pseudoHyp_eq_norm_mobius, pseudoHyp_eq_norm_mobius]
  rw [mobius_mobius_mobius ha hu hv, norm_mul, norm_neg, norm_div]
  have : ‖1 - a * conj u‖ = ‖1 - conj a * u‖ := by
    rw [← Complex.norm_conj (1 - conj a * u)]
    simp [mul_comm]
  rw [this, div_self (norm_ne_zero_iff.2 h1), one_mul]

/-- The core estimate behind the triangle inequality: `ρ(p, q) ≤ |p| + |q|`. -/
theorem pseudoHyp_le_norm_add_norm {p q : ℂ} (hp : p ∈ 𝔻) (hq : q ∈ 𝔻) :
    pseudoHyp p q ≤ ‖p‖ + ‖q‖ := by
  have h := one_sub_normSq_mobius hp hq
  have hD := norm_one_sub_conj_mul_pos hp hq
  have hDle := norm_one_sub_conj_mul_le p q
  have hp1 := norm_lt_one_of_mem_disc hp
  have hq1 := norm_lt_one_of_mem_disc hq
  have hp0 := norm_nonneg p
  have hq0 := norm_nonneg q
  set x := ‖p‖
  set y := ‖q‖
  set D := ‖1 - conj p * q‖
  have hnum : 0 ≤ (1 - x ^ 2) * (1 - y ^ 2) := by
    apply mul_nonneg <;> nlinarith
  have hD2 : D ^ 2 ≤ (1 + x * y) ^ 2 := by
    apply pow_le_pow_left₀ hD.le hDle
  have hle : (1 - x ^ 2) * (1 - y ^ 2) / (1 + x * y) ^ 2 ≤ (1 - x ^ 2) * (1 - y ^ 2) / D ^ 2 :=
    div_le_div_of_nonneg_left hnum (by positivity) hD2
  have hxy : 0 < 1 + x * y := by positivity
  have hid : 1 - (1 - x ^ 2) * (1 - y ^ 2) / (1 + x * y) ^ 2 = (x + y) ^ 2 / (1 + x * y) ^ 2 := by
    field_simp
    ring
  have hρ2 : pseudoHyp p q ^ 2 ≤ (x + y) ^ 2 := by
    have h1 : pseudoHyp p q ^ 2 ≤ (x + y) ^ 2 / (1 + x * y) ^ 2 := by
      rw [pseudoHyp_eq_norm_mobius]
      linarith
    have h2 : (x + y) ^ 2 / (1 + x * y) ^ 2 ≤ (x + y) ^ 2 := by
      apply div_le_self (by positivity)
      nlinarith [mul_nonneg hp0 hq0]
    linarith
  exact (pow_le_pow_iff_left₀ (pseudoHyp_nonneg p q) (by positivity) two_ne_zero).1 hρ2

theorem pseudoHyp_triangle {u v w : ℂ} (hu : u ∈ 𝔻) (hv : v ∈ 𝔻) (hw : w ∈ 𝔻) :
    pseudoHyp u w ≤ pseudoHyp u v + pseudoHyp v w := by
  have e1 : pseudoHyp u w = pseudoHyp (mobius v u) (mobius v w) := (pseudoHyp_mobius hv hu hw).symm
  have e2 : pseudoHyp u v = ‖mobius v u‖ := by
    rw [← pseudoHyp_mobius hv hu hv, mobius_self, pseudoHyp_zero_right]
  have e3 : pseudoHyp v w = ‖mobius v w‖ := by
    rw [← pseudoHyp_mobius hv hv hw, mobius_self, pseudoHyp_zero_left]
  rw [e1, e2, e3]
  exact pseudoHyp_le_norm_add_norm (mobius_mem_disc hv hu) (mobius_mem_disc hv hw)

/-! ### Chain rule for the Laplacian under holomorphic maps -/

/-- The real derivative of `g ∘ F` for holomorphic `F`: `D(g∘F)(z) v = Dg(F z)(F'(z) v)`. -/
theorem fderiv_comp_holomorphic_apply {g F : ℂ → ℂ} {z : ℂ} (hg : DifferentiableAt ℝ g (F z))
    (hF : DifferentiableAt ℂ F z) (v : ℂ) :
    fderiv ℝ (g ∘ F) z v = fderiv ℝ g (F z) (deriv F z * v) := by
  have hF' : HasFDerivAt F
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (deriv F z)).restrictScalars ℝ) z :=
    hF.hasDerivAt.hasFDerivAt.restrictScalars ℝ
  rw [(hg.hasFDerivAt.comp z hF').fderiv]
  simp [mul_comm]

/-- `∂(g ∘ F) = (∂g ∘ F) F'` for holomorphic `F`. -/
theorem dz_comp_holomorphic {g F : ℂ → ℂ} {z : ℂ} (hg : DifferentiableAt ℝ g (F z))
    (hF : DifferentiableAt ℂ F z) : dz (g ∘ F) z = dz g (F z) * deriv F z := by
  have h1 := fderiv_comp_holomorphic_apply hg hF 1
  have hI := fderiv_comp_holomorphic_apply hg hF I
  rw [fderiv_apply_eq_dz_dbar hg] at h1 hI
  rw [dz, h1, hI]
  simp only [map_mul, conj_I, mul_one]
  linear_combination (-(1 / 2) * dz g (F z) * deriv F z +
    1 / 2 * dbar g (F z) * conj (deriv F z)) * I_sq

/-- `∂̄(g ∘ F) = (∂̄g ∘ F) conj F'` for holomorphic `F`. -/
theorem dbar_comp_holomorphic {g F : ℂ → ℂ} {z : ℂ} (hg : DifferentiableAt ℝ g (F z))
    (hF : DifferentiableAt ℂ F z) : dbar (g ∘ F) z = dbar g (F z) * conj (deriv F z) := by
  have h1 := fderiv_comp_holomorphic_apply hg hF 1
  have hI := fderiv_comp_holomorphic_apply hg hF I
  rw [fderiv_apply_eq_dz_dbar hg] at h1 hI
  rw [dbar, h1, hI]
  simp only [map_mul, conj_I, mul_one]
  linear_combination (1 / 2 * dz g (F z) * deriv F z -
    1 / 2 * dbar g (F z) * conj (deriv F z)) * I_sq

theorem lap_comp_holomorphic {u : ℂ → ℝ} {F : ℂ → ℂ} {z : ℂ}
    (hF : ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ F w)
    (hu : ContDiffAt ℝ 2 u (F z)) (hF2 : ContDiffAt ℝ 2 F z) :
    lap (u ∘ F) z = lap u (F z) * ‖deriv F z‖ ^ 2 := by
  have hUF : ContDiffAt ℝ 2 (u ∘ F) z := hu.comp z hF2
  have hFz : DifferentiableAt ℂ F z := hF.self_of_nhds
  have hF'd : DifferentiableAt ℂ (deriv F) z :=
    (Complex.analyticAt_iff_eventually_differentiableAt.2 hF).deriv.differentiableAt
  have hUev : ∀ᶠ y in 𝓝 (F z), DifferentiableAt ℝ (cplx u) y :=
    ((contDiffAt_cplx hu).eventually (by simp)).mono fun y hy ↦ hy.differentiableAt (by simp)
  have hev : ∀ᶠ w in 𝓝 z, DifferentiableAt ℝ (cplx u) (F w) ∧ DifferentiableAt ℂ F w :=
    (hFz.continuousAt.eventually hUev).and hF
  have hdbar : dbar (cplx (u ∘ F)) =ᶠ[𝓝 z]
      fun w ↦ dbar (cplx u) (F w) * conj (deriv F w) :=
    hev.mono fun w hw ↦ dbar_comp_holomorphic hw.1 hw.2
  have hA : DifferentiableAt ℝ (dbar (cplx u)) (F z) :=
    differentiableAt_dbar (differentiableAt_fderiv_of_contDiffAt (contDiffAt_cplx hu))
  have hB : DifferentiableAt ℝ (fun w ↦ dbar (cplx u) (F w)) z :=
    hA.comp z (hFz.restrictScalars ℝ)
  have hC : DifferentiableAt ℝ (fun w ↦ conj (deriv F w)) z :=
    (conjCLE : ℂ ≃L[ℝ] ℂ).differentiableAt.comp z (hF'd.restrictScalars ℝ)
  apply Complex.ofReal_injective
  rw [← dz_dbar_cplx hUF, dz_congr hdbar, dz_mul hB hC,
    dz_conj (hF'd.restrictScalars ℝ), dbar_eq_zero_of_differentiableAt hF'd,
    show (fun w ↦ dbar (cplx u) (F w)) = dbar (cplx u) ∘ F from rfl,
    dz_comp_holomorphic hA hFz, dz_dbar_cplx hu]
  rw [map_zero, mul_zero, add_zero, mul_assoc, Complex.mul_conj']
  push_cast
  ring

theorem contDiffAt_mobius {a z : ℂ} (ha : a ∈ 𝔻) (hz : z ∈ 𝔻) :
    ContDiffAt ℝ 2 (mobius a) z :=
  ((Complex.analyticAt_iff_eventually_differentiableAt.2
    (eventually_differentiableAt_mobius ha hz)).contDiffAt).restrict_scalars ℝ

theorem invLap_comp_mobius {u : ℂ → ℝ} {a z : ℂ} (ha : a ∈ 𝔻) (hz : z ∈ 𝔻)
    (hu : ContDiffAt ℝ 2 u (mobius a z)) :
    invLap (u ∘ mobius a) z = invLap u (mobius a z) := by
  have hz' := one_sub_normSq_pos hz
  unfold invLap
  rw [lap_comp_holomorphic (eventually_differentiableAt_mobius ha hz) hu (contDiffAt_mobius ha hz),
    norm_deriv_mobius ha hz]
  field_simp

/-! ### Pseudo-hyperbolic versus Euclidean discs -/

theorem ball_subset_pseudoBall {a : ℂ} (ha : a ∈ 𝔻) {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    Metric.ball a (s * (1 - ‖a‖ ^ 2) / 2) ⊆ {z ∈ 𝔻 | pseudoHyp a z < s} := by
  intro z hz
  rw [mem_ball, dist_eq_norm] at hz
  have hr := norm_lt_one_of_mem_disc ha
  have hr0 := norm_nonneg a
  have hd0 := norm_nonneg (z - a)
  have hzle : ‖z‖ ≤ ‖a‖ + ‖z - a‖ := by
    calc ‖z‖ = ‖a + (z - a)‖ := by ring_nf
    _ ≤ ‖a‖ + ‖z - a‖ := norm_add_le _ _
  set r := ‖a‖
  set d := ‖z - a‖
  have h1r : 0 < 1 - r ^ 2 := one_sub_normSq_pos ha
  have hd1 : d < (1 - r ^ 2) / 2 := by
    have : s * (1 - r ^ 2) / 2 < (1 - r ^ 2) / 2 := by
      have := mul_lt_mul_of_pos_right hs1 h1r
      linarith
    linarith
  have hz1 : ‖z‖ < 1 := by nlinarith
  refine ⟨mem_disc_iff_norm_lt_one.2 hz1, ?_⟩
  have hD := one_sub_mul_le_norm_one_sub_conj_mul a z
  have hrz : r * ‖z‖ ≤ r * (r + d) := mul_le_mul_of_nonneg_left hzle hr0
  have hDlo : (1 - r ^ 2) - r * d ≤ ‖1 - conj a * z‖ := by nlinarith
  have hDpos : 0 < ‖1 - conj a * z‖ := by nlinarith
  have hsD : s * ((1 - r ^ 2) - r * d) ≤ s * ‖1 - conj a * z‖ :=
    mul_le_mul_of_nonneg_left hDlo hs.le
  have hsr : s * r ≤ 1 := by nlinarith
  have hsrd : s * r * d ≤ d := mul_le_of_le_one_left hd0 hsr
  unfold pseudoHyp
  rw [div_lt_iff₀ hDpos, norm_sub_rev]
  nlinarith

theorem pseudoBall_subset_ball {a : ℂ} (ha : a ∈ 𝔻) {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    {z ∈ 𝔻 | pseudoHyp a z < s} ⊆ Metric.ball a (s * (1 - ‖a‖ ^ 2) / (1 - s)) := by
  rintro z ⟨hz, hρ⟩
  obtain ⟨w, hw_def⟩ : ∃ w, w = mobius a z := ⟨_, rfl⟩
  have hw : w ∈ 𝔻 := hw_def ▸ mobius_mem_disc ha hz
  have hwn : ‖w‖ < s := by rw [hw_def, ← pseudoHyp_eq_norm_mobius]; exact hρ
  have hzw : z = mobius a w := by rw [hw_def, mobius_mobius ha hz]
  have hDw := one_sub_conj_mul_ne_zero_of_mem ha hw
  have e : ‖z - a‖ * ‖1 - conj a * w‖ = ‖w‖ * (1 - ‖a‖ ^ 2) := by
    rw [hzw, mobius_sub_self hDw, norm_div, norm_neg, norm_mul, norm_one_sub_conj_mul_self ha,
      div_mul_cancel₀ _ (norm_ne_zero_iff.2 hDw)]
  have hD := one_sub_mul_le_norm_one_sub_conj_mul a w
  have ha1 := norm_lt_one_of_mem_disc ha
  have haw : ‖a‖ * ‖w‖ ≤ ‖w‖ := mul_le_of_le_one_left (norm_nonneg w) ha1.le
  have hD' : 1 - s < ‖1 - conj a * w‖ := by linarith
  have h1r := one_sub_normSq_pos ha
  rw [mem_ball, dist_eq_norm, lt_div_iff₀ (by linarith)]
  calc ‖z - a‖ * (1 - s) ≤ ‖z - a‖ * ‖1 - conj a * w‖ :=
        mul_le_mul_of_nonneg_left hD'.le (norm_nonneg _)
    _ = ‖w‖ * (1 - ‖a‖ ^ 2) := e
    _ < s * (1 - ‖a‖ ^ 2) := mul_lt_mul_of_pos_right hwn h1r

theorem one_sub_normSq_comparable {a z : ℂ} (ha : a ∈ 𝔻) (hz : z ∈ 𝔻) {s : ℝ} (hs1 : s < 1)
    (hρ : pseudoHyp a z < s) :
    (1 - s) / (1 + s) * (1 - ‖a‖ ^ 2) ≤ 1 - ‖z‖ ^ 2 ∧
      1 - ‖z‖ ^ 2 ≤ (1 + s) / (1 - s) * (1 - ‖a‖ ^ 2) := by
  have hs0 : 0 < s := lt_of_le_of_lt (pseudoHyp_nonneg a z) hρ
  obtain ⟨w, hw_def⟩ : ∃ w, w = mobius a z := ⟨_, rfl⟩
  have hw : w ∈ 𝔻 := hw_def ▸ mobius_mem_disc ha hz
  have hwn : ‖w‖ < s := by rw [hw_def, ← pseudoHyp_eq_norm_mobius]; exact hρ
  have hzw : z = mobius a w := by rw [hw_def, mobius_mobius ha hz]
  have key : 1 - ‖z‖ ^ 2 = (1 - ‖a‖ ^ 2) * (1 - ‖w‖ ^ 2) / ‖1 - conj a * w‖ ^ 2 := by
    rw [hzw]; exact one_sub_normSq_mobius ha hw
  have hD1 := one_sub_mul_le_norm_one_sub_conj_mul a w
  have hD2 := norm_one_sub_conj_mul_le a w
  have hDpos := norm_one_sub_conj_mul_pos ha hw
  have ha1 := norm_lt_one_of_mem_disc ha
  have hApos := one_sub_normSq_pos ha
  have hw0 := norm_nonneg w
  have haw : ‖a‖ * ‖w‖ ≤ ‖w‖ := mul_le_of_le_one_left hw0 ha1.le
  rw [key]
  set t := ‖w‖
  set D := ‖1 - conj a * w‖
  set A := 1 - ‖a‖ ^ 2
  have hDlo : 1 - t ≤ D := by linarith
  have hDhi : D ≤ 1 + t := by linarith
  have ht1 : 0 < 1 - t := by linarith
  constructor
  · rw [div_mul_eq_mul_div, div_le_div_iff₀ (by linarith) (by positivity)]
    have h1 : D ^ 2 ≤ (1 + t) ^ 2 := pow_le_pow_left₀ hDpos.le hDhi 2
    have h2 : (1 - s) * (1 + t) ≤ (1 - t) * (1 + s) := by nlinarith
    have h3 : (1 - s) * D ^ 2 ≤ (1 - t ^ 2) * (1 + s) := by
      have := mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ 1 - s)
      have := mul_le_mul_of_nonneg_left h2 (by linarith : (0 : ℝ) ≤ 1 + t)
      nlinarith
    have := mul_le_mul_of_nonneg_left h3 hApos.le
    nlinarith
  · rw [div_le_iff₀ (by positivity), div_mul_eq_mul_div, div_mul_eq_mul_div,
      le_div_iff₀ (by linarith)]
    have h1 : (1 - t) ^ 2 ≤ D ^ 2 := pow_le_pow_left₀ ht1.le hDlo 2
    have h2 : (1 + t) * (1 - s) ≤ (1 + s) * (1 - t) := by nlinarith
    have h3 : (1 - t ^ 2) * (1 - s) ≤ (1 + s) * D ^ 2 := by
      have := mul_le_mul_of_nonneg_left h2 ht1.le
      have := mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ 1 + s)
      nlinarith
    have := mul_le_mul_of_nonneg_left h3 hApos.le
    nlinarith

/-! ### Invariance of the measure `dλ` -/

/-- The real determinant of multiplication by `c` is `|c|²`. -/
theorem det_smulRight_restrictScalars (c : ℂ) :
    ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) c).restrictScalars ℝ).det = ‖c‖ ^ 2 := by
  simp [ContinuousLinearMap.det, LinearMap.det_restrictScalars,
      Algebra.norm_complex_eq, Complex.normSq_eq_norm_sq]

/-- The Jacobian identity `invDensity (φ_a ζ) |φ_a'(ζ)|² = invDensity ζ`. -/
theorem invDensity_mobius_mul_norm_deriv_sq {a ζ : ℂ} (ha : a ∈ 𝔻) (hζ : ζ ∈ 𝔻) :
    ‖deriv (mobius a) ζ‖ ^ 2 * invDensity (mobius a ζ) = invDensity ζ := by
  have h1 := one_sub_normSq_pos hζ
  have h2 := one_sub_normSq_pos (mobius_mem_disc ha hζ)
  rw [norm_deriv_mobius ha hζ]
  unfold invDensity
  field_simp

theorem integral_comp_mobius {f : ℂ → ℝ} {a : ℂ} (ha : a ∈ 𝔻) :
    ∫ ζ in 𝔻, f (mobius a ζ) * invDensity ζ = ∫ ζ in 𝔻, f ζ * invDensity ζ := by
  have hderiv : ∀ x ∈ 𝔻, HasFDerivWithinAt (mobius a)
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (deriv (mobius a) x)).restrictScalars ℝ)
      𝔻 x := fun x hx ↦
    ((differentiableAt_mobius ha hx).hasDerivAt.hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  have h := integral_image_eq_integral_abs_det_fderiv_smul volume measurableSet_ball hderiv
    (injOn_mobius ha) (fun ζ ↦ f ζ * invDensity ζ)
  rw [mobius_image_disc ha] at h
  rw [h]
  refine setIntegral_congr_fun measurableSet_ball fun x hx ↦ ?_
  simp only [smul_eq_mul, det_smulRight_restrictScalars]
  rw [abs_of_nonneg (by positivity), ← invDensity_mobius_mul_norm_deriv_sq ha hx]
  ring

/-! ### Separated sequences in the disc -/

/-- Pseudo-hyperbolic separation gives Euclidean separation at scale `1 - |w|²`. -/
theorem norm_sub_ge_of_le_pseudoHyp {w w' : ℂ} (hw : w ∈ 𝔻) (hw' : w' ∈ 𝔻) {ε : ℝ}
    (h : ε ≤ pseudoHyp w w') : ε * (1 - ‖w‖ ^ 2) / 2 ≤ ‖w - w'‖ := by
  have hD := norm_one_sub_conj_mul_pos hw hw'
  have e : ‖w - w'‖ = pseudoHyp w w' * ‖1 - conj w * w'‖ := by
    unfold pseudoHyp
    rw [div_mul_cancel₀ _ hD.ne']
  have h1 := one_sub_mul_le_norm_one_sub_conj_mul w w'
  have hw1 := norm_lt_one_of_mem_disc hw
  have hw'1 := norm_lt_one_of_mem_disc hw'
  have hww' : ‖w‖ * ‖w'‖ ≤ ‖w‖ := mul_le_of_le_one_right (norm_nonneg w) hw'1.le
  have h2 : (1 - ‖w‖ ^ 2) / 2 ≤ ‖1 - conj w * w'‖ := by nlinarith [norm_nonneg w]
  have h3 : 0 ≤ (1 - ‖w‖ ^ 2) / 2 := by have := one_sub_normSq_pos hw; positivity
  rw [e]
  calc ε * (1 - ‖w‖ ^ 2) / 2 = ε * ((1 - ‖w‖ ^ 2) / 2) := by ring
    _ ≤ pseudoHyp w w' * ‖1 - conj w * w'‖ := mul_le_mul h h2 h3 (pseudoHyp_nonneg _ _)

/-- The counting lemma for `0 < s < 1`: the points of an `ε`-separated `Γ ⊆ 𝔻` in a
pseudo-hyperbolic disc of radius `s` are finitely many, with an explicit bound independent of the
centre. -/
theorem finite_and_ncard_pseudoBall_le {Γ : Set ℂ} {ε : ℝ} (hΓ𝔻 : Γ ⊆ 𝔻) (hε0 : 0 < ε)
    (hε : ∀ a ∈ Γ, ∀ b ∈ Γ, a ≠ b → ε ≤ pseudoHyp a b) {s : ℝ} (hs : 0 < s) (hs1 : s < 1)
    {z : ℂ} (hz : z ∈ 𝔻) :
    {w ∈ Γ | pseudoHyp z w < s}.Finite ∧
      {w ∈ Γ | pseudoHyp z w < s}.ncard ≤ ⌊(4 * s * (1 + s) / (ε * (1 - s) ^ 2) + 1) ^ 2⌋₊ := by
  have hz' := one_sub_normSq_pos hz
  have hs1' : 0 < 1 - s := by linarith
  have hδ : 0 < ε * ((1 - s) / (1 + s) * (1 - ‖z‖ ^ 2)) / 2 := by positivity
  have hsep : ∀ a ∈ {w ∈ Γ | pseudoHyp z w < s}, ∀ b ∈ {w ∈ Γ | pseudoHyp z w < s}, a ≠ b →
      ε * ((1 - s) / (1 + s) * (1 - ‖z‖ ^ 2)) / 2 ≤ dist a b := by
    rintro a ⟨haΓ, haρ⟩ b ⟨hbΓ, hbρ⟩ hab
    have ha𝔻 := hΓ𝔻 haΓ
    have hb𝔻 := hΓ𝔻 hbΓ
    have hcomp := (one_sub_normSq_comparable hz ha𝔻 hs1 haρ).1
    have := norm_sub_ge_of_le_pseudoHyp ha𝔻 hb𝔻 (hε a haΓ b hbΓ hab)
    rw [dist_eq_norm]
    refine le_trans ?_ this
    gcongr
  have hSsub : {w ∈ Γ | pseudoHyp z w < s} =
      {w ∈ Γ | pseudoHyp z w < s} ∩ ball z (s * (1 - ‖z‖ ^ 2) / (1 - s)) := by
    refine (inter_eq_left.2 ?_).symm
    rintro w ⟨hwΓ, hwρ⟩
    exact pseudoBall_subset_ball hz hs hs1 ⟨hΓ𝔻 hwΓ, hwρ⟩
  have hfin := finite_inter_ball_of_sep hδ hsep z (s * (1 - ‖z‖ ^ 2) / (1 - s))
  have hcard := ncard_inter_ball_le_of_sep hδ hsep z (s * (1 - ‖z‖ ^ 2) / (1 - s))
  have heq : 2 * (s * (1 - ‖z‖ ^ 2) / (1 - s)) / (ε * ((1 - s) / (1 + s) * (1 - ‖z‖ ^ 2)) / 2) =
      4 * s * (1 + s) / (ε * (1 - s) ^ 2) := by
    field_simp
    ring
  rw [← hSsub] at hfin hcard
  rw [heq] at hcard
  exact ⟨hfin, hcard⟩

theorem IsDiskSeparated.exists_ncard_le {Γ : Set ℂ} (hΓ : IsDiskSeparated Γ) {s : ℝ}
    (hs1 : s < 1) : ∃ N : ℕ, ∀ z ∈ 𝔻, {w ∈ Γ | pseudoHyp z w < s}.ncard ≤ N := by
  obtain ⟨hΓ𝔻, ε, hε0, hε⟩ := hΓ
  have hs' : (0 : ℝ) < max s (1 / 2) := lt_max_of_lt_right (by norm_num)
  have hs'1 : max s (1 / 2) < 1 := max_lt hs1 (by norm_num)
  refine ⟨⌊(4 * max s (1 / 2) * (1 + max s (1 / 2)) / (ε * (1 - max s (1 / 2)) ^ 2) + 1) ^ 2⌋₊,
    fun z hz ↦ ?_⟩
  obtain ⟨hfin, hcard⟩ := finite_and_ncard_pseudoBall_le hΓ𝔻 hε0 hε hs' hs'1 hz
  refine le_trans (Set.ncard_le_ncard ?_ hfin) hcard
  exact fun w ⟨hwΓ, hwρ⟩ ↦ ⟨hwΓ, lt_of_lt_of_le hwρ (le_max_left _ _)⟩

theorem IsDiskSeparated.finite_pseudoBall {Γ : Set ℂ} (hΓ : IsDiskSeparated Γ) {s : ℝ}
    (hs1 : s < 1) (z : ℂ) (hz : z ∈ 𝔻) : {w ∈ Γ | pseudoHyp z w < s}.Finite := by
  obtain ⟨hΓ𝔻, ε, hε0, hε⟩ := hΓ
  have hs' : (0 : ℝ) < max s (1 / 2) := lt_max_of_lt_right (by norm_num)
  have hs'1 : max s (1 / 2) < 1 := max_lt hs1 (by norm_num)
  refine (finite_and_ncard_pseudoBall_le hΓ𝔻 hε0 hε hs' hs'1 hz).1.subset ?_
  exact fun w ⟨hwΓ, hwρ⟩ ↦ ⟨hwΓ, lt_of_lt_of_le hwρ (le_max_left _ _)⟩

theorem IsDiskSeparated.countable {Γ : Set ℂ} (hΓ : IsDiskSeparated Γ) : Γ.Countable := by
  have hsub : Γ ⊆ ⋃ n : ℕ, {w ∈ Γ | pseudoHyp 0 w < 1 - 1 / ((n : ℝ) + 2)} := by
    intro w hw
    have hw1 := norm_lt_one_of_mem_disc (hΓ.1 hw)
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hw1)
    refine mem_iUnion.2 ⟨n, hw, ?_⟩
    rw [pseudoHyp_zero_left]
    have : 1 / ((n : ℝ) + 2) ≤ 1 / ((n : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    linarith
  refine Set.Countable.mono hsub (Set.countable_iUnion fun n ↦ ?_)
  have : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
  exact (hΓ.finite_pseudoBall (by linarith) 0 (by simp)).countable

theorem IsDiskSeparated.isOpen_diff {Γ : Set ℂ} (hΓ : IsDiskSeparated Γ) : IsOpen (𝔻 \ Γ) := by
  rw [isOpen_iff_mem_nhds]
  rintro x ⟨hx𝔻, hxΓ⟩
  have hx' := one_sub_normSq_pos hx𝔻
  have hsub := ball_subset_pseudoBall hx𝔻 (s := 1 / 2) (by norm_num) (by norm_num)
  have hfin : (Γ ∩ ball x (1 / 2 * (1 - ‖x‖ ^ 2) / 2)).Finite :=
    (hΓ.finite_pseudoBall (s := 1 / 2) (by norm_num) x hx𝔻).subset
      fun w hw ↦ ⟨hw.1, (hsub hw.2).2⟩
  have h1 : (Γ ∩ ball x (1 / 2 * (1 - ‖x‖ ^ 2) / 2))ᶜ ∈ 𝓝 x :=
    hfin.isClosed.isOpen_compl.mem_nhds fun h ↦ hxΓ h.1
  have h2 : ball x (1 / 2 * (1 - ‖x‖ ^ 2) / 2) ∈ 𝓝 x := ball_mem_nhds x (by positivity)
  filter_upwards [h1, h2] with y hy1 hy2
  exact ⟨(hsub hy2).1, fun hyΓ ↦ hy1 ⟨hyΓ, hy2⟩⟩

theorem IsDiskSeparated.volume_eq_zero {Γ : Set ℂ} (hΓ : IsDiskSeparated Γ) : volume Γ = 0 :=
  hΓ.countable.measure_zero volume

theorem measurableSet_pseudoBall (w : ℂ) (s : ℝ) :
    MeasurableSet {z ∈ 𝔻 | pseudoHyp w z < s} := by
  have hm : Measurable (pseudoHyp w) := by
    unfold pseudoHyp
    fun_prop
  exact measurableSet_ball.inter (measurableSet_lt hm measurable_const)

theorem IsDiskSeparated.exists_tsum_lintegral_le {Γ : Set ℂ} (hΓ : IsDiskSeparated Γ) {s : ℝ}
    (hs1 : s < 1) : ∃ N : ℕ, ∀ F : ℂ → ℝ≥0∞, Measurable F →
      ∑' w : Γ, ∫⁻ z in {z ∈ 𝔻 | pseudoHyp w z < s}, F z ≤ (N : ℝ≥0∞) * ∫⁻ z in 𝔻, F z := by
  obtain ⟨N, hN⟩ := hΓ.exists_ncard_le hs1
  have : Countable Γ := hΓ.countable.to_subtype
  refine ⟨N, fun F hF ↦ ?_⟩
  simp_rw [← lintegral_indicator (measurableSet_pseudoBall _ s)]
  rw [← lintegral_tsum fun w ↦ (hF.indicator (measurableSet_pseudoBall _ s)).aemeasurable,
    ← lintegral_indicator measurableSet_ball,
    ← lintegral_const_mul _ (hF.indicator measurableSet_ball)]
  refine lintegral_mono fun z ↦ ?_
  by_cases hz : z ∈ 𝔻
  · rw [indicator_of_mem hz]
    refine ENNReal.summable.tsum_le_of_sum_le fun t ↦ ?_
    classical
    simp only [Set.indicator_apply]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    gcongr
    have hfin := hΓ.finite_pseudoBall hs1 z hz
    rw [← Finset.card_map (Function.Embedding.subtype _)]
    calc _ ≤ {w ∈ Γ | pseudoHyp z w < s}.ncard := by
          rw [← Set.ncard_coe_finset]
          refine Set.ncard_le_ncard ?_ hfin
          intro w hw
          simp only [Finset.coe_map, Function.Embedding.coe_subtype, Finset.coe_filter,
            mem_image, mem_ofPred_eq] at hw
          obtain ⟨a, ⟨_, _, ha⟩, rfl⟩ := hw
          exact ⟨a.2, by rw [pseudoHyp_comm]; exact ha⟩
      _ ≤ N := hN z hz
  · have h0 : ∀ w : Γ, {z ∈ 𝔻 | pseudoHyp (w : ℂ) z < s}.indicator F z = 0 :=
      fun w ↦ indicator_of_notMem (fun h ↦ hz h.1) _
    rw [indicator_of_notMem hz, mul_zero]
    simp only [h0, tsum_zero, le_refl]

/-! ### The weight `log 1/(1 - |z|²)` -/

theorem lap_neg_log_one_sub_normSq {z : ℂ} (hz : z ∈ 𝔻) :
    lap (fun w ↦ -Real.log (1 - ‖w‖ ^ 2)) z = (1 - ‖z‖ ^ 2)⁻¹ ^ 2 := by
  have hz' := one_sub_normSq_pos hz
  have hF : ContDiffAt ℝ 2 (fun t : ℝ ↦ -Real.log (1 - t)) (‖z‖ ^ 2) :=
    ((Real.contDiffAt_log.2 hz'.ne').comp _ (contDiffAt_const.sub contDiffAt_id)).neg
  have hderiv : ∀ t : ℝ, t < 1 → HasDerivAt (fun t : ℝ ↦ -Real.log (1 - t)) (1 - t)⁻¹ t := by
    intro t ht
    have h1 : HasDerivAt (fun t : ℝ ↦ 1 - t) (-1) t := (hasDerivAt_id t).const_sub 1
    have := (h1.log (by linarith)).neg
    convert this using 1
    field_simp
  have hev : deriv (fun t : ℝ ↦ -Real.log (1 - t)) =ᶠ[𝓝 (‖z‖ ^ 2)] fun t ↦ (1 - t)⁻¹ := by
    filter_upwards [Iio_mem_nhds (by linarith : ‖z‖ ^ 2 < 1)] with t ht
    exact (hderiv t ht).deriv
  have h2 : HasDerivAt (fun t : ℝ ↦ (1 - t)⁻¹) (-(-1) / (1 - ‖z‖ ^ 2) ^ 2) (‖z‖ ^ 2) :=
    ((hasDerivAt_id _).const_sub 1).inv hz'.ne'
  rw [show (fun w : ℂ ↦ -Real.log (1 - ‖w‖ ^ 2)) =
      fun w ↦ (fun t : ℝ ↦ -Real.log (1 - t)) (‖w‖ ^ 2) from rfl, lap_comp_normSq hF,
    hev.deriv_eq, h2.deriv, (hderiv _ (by linarith)).deriv]
  field_simp
  ring

theorem invLap_log_bergman (α : ℝ) {z : ℂ} (hz : z ∈ 𝔻) :
    invLap (fun w ↦ α * Real.log (1 / (1 - ‖w‖ ^ 2))) z = α := by
  have hz' := one_sub_normSq_pos hz
  have hfun : (fun w : ℂ ↦ α * Real.log (1 / (1 - ‖w‖ ^ 2))) =
      fun w ↦ α * (fun w : ℂ ↦ -Real.log (1 - ‖w‖ ^ 2)) w := by
    funext w
    rw [one_div, Real.log_inv]
  have hC : ContDiffAt ℝ 2 (fun w : ℂ ↦ -Real.log (1 - ‖w‖ ^ 2)) z := by
    have h1 : ContDiffAt ℝ 2 (fun w : ℂ ↦ 1 - ‖w‖ ^ 2) z :=
      contDiffAt_const.sub (contDiff_norm_sq ℝ).contDiffAt
    have h2 : ContDiffAt ℝ 2 Real.log (1 - ‖z‖ ^ 2) := Real.contDiffAt_log.2 hz'.ne'
    exact (h2.comp z h1).neg
  unfold invLap
  rw [hfun, lap_const_mul α hC, lap_neg_log_one_sub_normSq hz]
  field_simp

end OC
