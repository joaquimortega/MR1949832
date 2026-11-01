import OrtegaCerdaSeip.Jones.Basic
import OrtegaCerdaSeip.Jones.LayerCake

/-!
# M04 (Jones) — the bound on the strip `0 ≤ Im z ≤ 2` and the decay `O(|z|⁻²)`

See `blueprint/M04_Jones.md` (§1.5–§1.6).

The paper (p. 410) quotes from [J]: Jones' solution "decays as `|z|⁻²` when `|z| → ∞`, and it is
bounded in a strip of width 2 along the real axis with a bound depending only on the Carleson
constant".  Both are proved here for `ρ` carried by `{Im ≥ 10}`:

* `norm_jonesSol_le_strip`: `|v(z)| ≤ (3/π) e^{12K}` for `0 ≤ Im z ≤ 2`, where `K` is a
  (large-scale) Carleson constant of `ρ`; the proof is `|kernel| ≤ (3/π) e^{12K} · dρ_z/dρ · e^{-P}`
  followed by the layer-cake lemma `∫ e^{-P} dP ≤ 1` (`lintegral_exp_neg_measure_le_le_one`);
* `jonesSol_decay`: `|v(z)| ≤ C/|z|²` for `Im z ≥ 0`, `|z| ≥ R`, if `ρ` has compact support
  (`C`, `R` depend on `ρ`).
-/

open MeasureTheory Metric Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace OCS

/-- Geometry of the strip: for `0 ≤ Im z ≤ 2` and `Im ζ ≥ 10`, `|z - ζ| ≥ (2/3)|z - ζ̄|`, hence
`Im ζ / (|z - ζ| |z - ζ̄|) ≤ (3/2) (Im z + Im ζ)/|z - ζ̄|²`. -/
theorem im_div_norm_mul_norm_le {z ζ : ℂ} (hz0 : 0 ≤ z.im) (hz2 : z.im ≤ 2) (hζ : 10 ≤ ζ.im) :
    ζ.im / (‖z - ζ‖ * ‖z - conj ζ‖) ≤ 3 / 2 * jonesWeight z ζ := by
  set a := ‖z - ζ‖
  set b := ‖z - conj ζ‖
  have hb : 10 ≤ b := by linarith [add_im_le_norm_sub_conj z ζ]
  have ha2 : a ^ 2 = (z.re - ζ.re) ^ 2 + (z.im - ζ.im) ^ 2 := by
    simp only [a, Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]; ring
  have hb2 : b ^ 2 = (z.re - ζ.re) ^ 2 + (z.im + ζ.im) ^ 2 := by
    simp only [b, Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.conj_re, Complex.conj_im]; ring
  have ha : 2 / 3 * b ≤ a := by
    refine (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).1 ?_
    rw [mul_pow, ha2, hb2]
    nlinarith [sq_nonneg (z.re - ζ.re)]
  have hb0 : 0 < b := by linarith
  calc ζ.im / (a * b) ≤ ζ.im / ((2 / 3 * b) * b) :=
        div_le_div_of_nonneg_left (by linarith) (by positivity)
          (mul_le_mul_of_nonneg_right ha hb0.le)
    _ = 3 / 2 * (ζ.im / b ^ 2) := by field_simp
    _ ≤ 3 / 2 * jonesWeight z ζ := by
        rw [jonesWeight]; gcongr; linarith

section Measure

variable {ρ : Measure ℂ} [IsFiniteMeasure ρ]

/-- `|k(z, ζ)| = (2/π) · Im ζ/(|z - ζ| |z - ζ̄|) · e^{A(ζ) - P(z, Im ζ)}`. -/
theorem norm_jonesKernel_eq (h10 : ∀ᵐ w ∂ρ, 10 ≤ w.im) {z ζ : ℂ} (hz : 0 ≤ z.im)
    (hζ : 0 ≤ ζ.im) :
    ‖jonesKernel ρ z ζ‖ = 2 / Real.pi * (ζ.im / (‖z - ζ‖ * ‖z - conj ζ‖)) *
      Real.exp (jonesPot ρ ζ ζ.im - jonesPot ρ z ζ.im) := by
  rw [jonesKernel, norm_mul, norm_mul, norm_exp_jonesExponent h10 hz, norm_div, norm_div,
    norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_I,
    Real.norm_of_nonneg hζ, Real.norm_of_nonneg Real.pi_pos.le]
  norm_num

/-- `e^{A(ζ) - P(z, Im ζ)} ≤ e^{ρ(ℂ)/20}`. -/
theorem exp_jonesPot_sub_le (h10 : ∀ᵐ w ∂ρ, 10 ≤ w.im) {z : ℂ} (hz : 0 ≤ z.im) (ζ : ℂ) :
    Real.exp (jonesPot ρ ζ ζ.im - jonesPot ρ z ζ.im) ≤ Real.exp ((ρ univ).toReal / 20) :=
  Real.exp_le_exp.2 (by linarith [jonesPot_self_le_mass h10 ζ, jonesPot_nonneg h10 hz ζ.im])

/-- Pointwise bound of Jones' kernel on the strip `0 ≤ Im z ≤ 2`. -/
theorem norm_jonesKernel_le_strip (h10 : ∀ᵐ w ∂ρ, 10 ≤ w.im) {K : ℝ≥0}
    (hC : IsCarlesonLarge ρ K) {z ζ : ℂ} (hz0 : 0 ≤ z.im) (hz2 : z.im ≤ 2) (hζ : 10 ≤ ζ.im) :
    ‖jonesKernel ρ z ζ‖ ≤
      3 / Real.pi * Real.exp (12 * K) * (jonesWeight z ζ * Real.exp (-jonesPot ρ z ζ.im)) := by
  rw [norm_jonesKernel_eq h10 hz0 (by linarith)]
  have h1 := im_div_norm_mul_norm_le hz0 hz2 hζ
  have h2 : Real.exp (jonesPot ρ ζ ζ.im - jonesPot ρ z ζ.im) ≤
      Real.exp (12 * K) * Real.exp (-jonesPot ρ z ζ.im) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith [jonesPot_self_le h10 hC ζ])
  calc 2 / Real.pi * (ζ.im / (‖z - ζ‖ * ‖z - conj ζ‖)) *
        Real.exp (jonesPot ρ ζ ζ.im - jonesPot ρ z ζ.im)
      ≤ 2 / Real.pi * (3 / 2 * jonesWeight z ζ) *
        (Real.exp (12 * K) * Real.exp (-jonesPot ρ z ζ.im)) := by
        have h0 : 0 ≤ ζ.im / (‖z - ζ‖ * ‖z - conj ζ‖) := div_nonneg (by linarith) (by positivity)
        exact mul_le_mul (mul_le_mul_of_nonneg_left h1 (by positivity)) h2 (Real.exp_pos _).le
          (mul_nonneg (by positivity) (h0.trans h1))
    _ = _ := by field_simp

/-- **Jones' estimate on the strip** (quoted from [J] on p. 410, proved here):
`|v(z)| ≤ (3/π) e^{12K}` for `0 ≤ Im z ≤ 2`. -/
theorem norm_jonesSol_le_strip (h10 : ∀ᵐ w ∂ρ, 10 ≤ w.im) {K : ℝ≥0} (hC : IsCarlesonLarge ρ K)
    {θ : ℂ → ℂ} (hθ : ∀ z, ‖θ z‖ ≤ 1) {z : ℂ} (hz0 : 0 ≤ z.im) (hz2 : z.im ≤ 2) :
    ‖jonesSol ρ θ z‖ ≤ 3 / Real.pi * Real.exp (12 * K) := by
  set C := 3 / Real.pi * Real.exp (12 * K) with hCdef
  have hC0 : 0 ≤ C := by positivity
  have hρz := isFiniteMeasure_withDensity_jonesWeight h10 hz0
  have hpt : ∀ᵐ ζ ∂ρ, ‖jonesKernel ρ z ζ * θ ζ‖ₑ ≤ ENNReal.ofReal C *
      (ENNReal.ofReal (jonesWeight z ζ) * ENNReal.ofReal (Real.exp (-jonesPot ρ z ζ.im))) := by
    filter_upwards [h10] with ζ hζ
    rw [enorm_mul, ← ENNReal.ofReal_mul (jonesWeight_nonneg hz0 (by linarith)),
      ← ENNReal.ofReal_mul hC0, ← ofReal_norm, ← ofReal_norm]
    calc ENNReal.ofReal ‖jonesKernel ρ z ζ‖ * ENNReal.ofReal ‖θ ζ‖
        ≤ ENNReal.ofReal ‖jonesKernel ρ z ζ‖ * ENNReal.ofReal 1 := by gcongr; exact hθ ζ
      _ ≤ _ := by
        rw [ENNReal.ofReal_one, mul_one]
        exact ENNReal.ofReal_le_ofReal (norm_jonesKernel_le_strip h10 hC hz0 hz2 hζ)
  have hlc := lintegral_exp_neg_measure_le_le_one
    (ρ.withDensity fun w ↦ ENNReal.ofReal (jonesWeight z w)) Complex.measurable_im
  simp_rw [← jonesPot_eq_toReal h10 hz0] at hlc
  have hfm : Measurable fun w ↦ ENNReal.ofReal (jonesWeight z w) :=
    (measurable_jonesWeight z).ennreal_ofReal
  have key : ‖jonesSol ρ θ z‖ₑ ≤ ENNReal.ofReal C :=
    calc ‖jonesSol ρ θ z‖ₑ ≤ ∫⁻ ζ, ‖jonesKernel ρ z ζ * θ ζ‖ₑ ∂ρ :=
          enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ ζ, ENNReal.ofReal C * (ENNReal.ofReal (jonesWeight z ζ) *
            ENNReal.ofReal (Real.exp (-jonesPot ρ z ζ.im))) ∂ρ := lintegral_mono_ae hpt
      _ = ENNReal.ofReal C * ∫⁻ ζ, ENNReal.ofReal (Real.exp (-jonesPot ρ z ζ.im))
            ∂(ρ.withDensity fun w ↦ ENNReal.ofReal (jonesWeight z w)) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_withDensity_eq_lintegral_mul_non_measurable ρ hfm
              (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
          rfl
      _ ≤ ENNReal.ofReal C * 1 := by gcongr
      _ = ENNReal.ofReal C := mul_one _
  rw [← ofReal_norm] at key
  exact (ENNReal.ofReal_le_ofReal_iff hC0).1 key

/-- Bound of the kernel in the closed upper half-plane, without Carleson condition:
`|kernel(z, ζ)| ≤ (2/π) e^{ρ(ℂ)/20} / |z - ζ|`. -/
theorem norm_jonesKernel_le_inv (h10 : ∀ᵐ w ∂ρ, 10 ≤ w.im) {z ζ : ℂ} (hz : 0 ≤ z.im)
    (hζ : 0 ≤ ζ.im) :
    ‖jonesKernel ρ z ζ‖ ≤ 2 / Real.pi * Real.exp ((ρ univ).toReal / 20) / ‖z - ζ‖ := by
  rw [norm_jonesKernel_eq h10 hz hζ]
  have hb : ζ.im ≤ ‖z - conj ζ‖ := by linarith [add_im_le_norm_sub_conj z ζ]
  have h1 : ζ.im / (‖z - ζ‖ * ‖z - conj ζ‖) ≤ 1 / ‖z - ζ‖ := by
    rw [mul_comm, ← div_div]
    exact div_le_div_of_nonneg_right (div_le_one_of_le₀ hb (norm_nonneg _)) (norm_nonneg _)
  calc 2 / Real.pi * (ζ.im / (‖z - ζ‖ * ‖z - conj ζ‖)) *
        Real.exp (jonesPot ρ ζ ζ.im - jonesPot ρ z ζ.im)
      ≤ 2 / Real.pi * (1 / ‖z - ζ‖) * Real.exp ((ρ univ).toReal / 20) := by
        gcongr ?_ * ?_
        · gcongr
        · exact exp_jonesPot_sub_le h10 hz ζ
    _ = _ := by ring

/-- **Decay** (quoted from [J] on p. 410, proved here): `|v(z)| = O(|z|⁻²)` in the closed upper
half-plane, for `ρ` with compact support. -/
theorem jonesSol_decay {L : Set ℂ} (hL : IsCompact L) (hρL : ρ Lᶜ = 0)
    (hL10 : ∀ w ∈ L, 10 ≤ w.im) {θ : ℂ → ℂ} (hθ : ∀ z, ‖θ z‖ ≤ 1) :
    ∃ C R : ℝ, ∀ z : ℂ, 0 ≤ z.im → R ≤ ‖z‖ → ‖jonesSol ρ θ z‖ ≤ C / ‖z‖ ^ 2 := by
  have hL' : ∀ᵐ w ∂ρ, w ∈ L := by
    have : Lᶜᶜ ∈ ae ρ := compl_mem_ae_iff.2 hρL
    rwa [compl_compl] at this
  have h10 : ∀ᵐ w ∂ρ, 10 ≤ w.im := hL'.mono fun w hw ↦ hL10 w hw
  obtain ⟨R₀, hR₀⟩ := hL.isBounded.subset_closedBall 0
  set R₁ := max R₀ 0
  have hR₁ : ∀ w ∈ L, ‖w‖ ≤ R₁ := fun w hw ↦ by
    have := hR₀ hw
    rw [mem_closedBall, dist_zero_right] at this
    exact this.trans (le_max_left _ _)
  set M := Real.exp ((ρ univ).toReal / 20)
  refine ⟨8 / Real.pi * R₁ * M * ρ.real univ, 2 * R₁ + 1, fun z hz hzR ↦ ?_⟩
  have hR1 : 0 ≤ R₁ := le_max_right _ _
  have hzpos : 0 < ‖z‖ := by linarith
  have hk : ∀ᵐ ζ ∂ρ, ‖jonesKernel ρ z ζ * θ ζ‖ ≤ 8 / Real.pi * R₁ * M / ‖z‖ ^ 2 := by
    filter_upwards [hL'] with ζ hζ
    have hζR := hR₁ ζ hζ
    have hζ10 := hL10 ζ hζ
    have ha : ‖z‖ / 2 ≤ ‖z - ζ‖ := by
      have := norm_sub_norm_le z ζ; linarith
    have hb : ‖z‖ / 2 ≤ ‖z - conj ζ‖ := by
      have := norm_sub_norm_le z (conj ζ); rw [Complex.norm_conj] at this; linarith
    have hi : ζ.im ≤ R₁ := (Complex.im_le_norm ζ).trans hζR
    have hq : ζ.im / (‖z - ζ‖ * ‖z - conj ζ‖) ≤ 4 * R₁ / ‖z‖ ^ 2 := by
      calc ζ.im / (‖z - ζ‖ * ‖z - conj ζ‖) ≤ R₁ / ((‖z‖ / 2) * (‖z‖ / 2)) := by
            gcongr
        _ = 4 * R₁ / ‖z‖ ^ 2 := by field_simp; ring
    rw [norm_mul]
    calc ‖jonesKernel ρ z ζ‖ * ‖θ ζ‖ ≤ ‖jonesKernel ρ z ζ‖ * 1 := by
          gcongr; exact hθ ζ
      _ = 2 / Real.pi * (ζ.im / (‖z - ζ‖ * ‖z - conj ζ‖)) *
          Real.exp (jonesPot ρ ζ ζ.im - jonesPot ρ z ζ.im) := by
          rw [mul_one, norm_jonesKernel_eq h10 hz (by linarith)]
      _ ≤ 2 / Real.pi * (4 * R₁ / ‖z‖ ^ 2) * M := by
          gcongr ?_ * ?_
          · gcongr
          · exact exp_jonesPot_sub_le h10 hz ζ
      _ = 8 / Real.pi * R₁ * M / ‖z‖ ^ 2 := by ring
  calc ‖jonesSol ρ θ z‖ ≤ 8 / Real.pi * R₁ * M / ‖z‖ ^ 2 * ρ.real univ :=
        norm_integral_le_of_norm_le_const hk
    _ = 8 / Real.pi * R₁ * M * ρ.real univ / ‖z‖ ^ 2 := by ring

end Measure

end OCS
