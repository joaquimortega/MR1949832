import OrtegaCerdaMultipliers.Potential.Fundamental

/-!
# M02 (Potentials) Appendix A — The paper's global kernels (documentation; not used)

See `blueprint/M02_Potentials.md`, Appendix A.  Scaffold: statements, proofs `sorry`.  These
kernels are not used by the formal proof of Lemma 6 (which uses local potentials, §4); they
document the paper's construction (p. 371) and its sign error in the plane.
-/

open MeasureTheory Metric Set Complex
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace OC

/-- Plane kernel of Lemma 6, sign of the quadratic term corrected. -/
def kPlane (z ζ : ℂ) : ℝ :=
  (4 * Real.pi)⁻¹ * Real.log (‖z - ζ‖ ^ 2) -
    (2 * Real.pi)⁻¹ * (if 1 ≤ ‖ζ‖ then
      Real.log ‖ζ‖ - (z / ζ).re - (z ^ 2 / (2 * ζ ^ 2)).re else 0)

/-- Disc kernel of Lemma 6. -/
def kDisc (z ζ : ℂ) : ℝ :=
  (4 * Real.pi)⁻¹ * (Real.log (pseudoHyp ζ z ^ 2) +
    (1 - ‖ζ‖ ^ 2) * (1 / (1 - conj z * ζ) + 1 / (1 - z * conj ζ) - 1).re)

theorem kDisc_eq {z ζ : ℂ} (hz : z ∈ 𝔻) (hζ : ζ ∈ 𝔻) :
    kDisc z ζ = (4 * Real.pi)⁻¹ * (Real.log (pseudoHyp ζ z ^ 2) + (1 - pseudoHyp ζ z ^ 2) +
      ‖z‖ ^ 2 * (1 - ‖ζ‖ ^ 2) ^ 2 / ‖1 - conj ζ * z‖ ^ 2) := by
  have hD : 1 - conj ζ * z ≠ 0 := one_sub_conj_mul_ne_zero_of_mem hζ hz
  set v : ℂ := z * conj ζ with hv
  have hu : 1 - conj ζ * z = 1 - v := by rw [hv, mul_comm]
  have hu' : 1 - conj z * ζ = conj (1 - v) := by rw [hv]; simp [mul_comm]
  have hDv : 1 - v ≠ 0 := hu ▸ hD
  have hN : Complex.normSq (1 - v) ≠ 0 := (Complex.normSq_pos.2 hDv).ne'
  have hX : (1 / (1 - conj z * ζ) + 1 / (1 - z * conj ζ) - 1).re =
      (1 - Complex.normSq v) / Complex.normSq (1 - v) := by
    rw [hu', ← hv]
    have e : 1 / conj (1 - v) = conj (1 / (1 - v)) := by simp
    rw [e, Complex.sub_re, Complex.add_re, Complex.conj_re, Complex.one_re, one_div,
      Complex.inv_re]
    have hn2 : Complex.normSq (1 - v) = (1 - v.re) ^ 2 + v.im ^ 2 := by
      rw [Complex.normSq_apply]; simp; ring
    rw [hn2] at hN ⊢
    rw [Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.one_re]
    field_simp
    ring
  have hvn : Complex.normSq v = ‖z‖ ^ 2 * ‖ζ‖ ^ 2 := by
    rw [hv, ← Complex.sq_norm, norm_mul, Complex.norm_conj, mul_pow]
  have hNn : Complex.normSq (1 - v) = ‖1 - conj ζ * z‖ ^ 2 := by
    rw [hu, Complex.sq_norm]
  have key := norm_one_sub_conj_mul_sq_sub ζ z
  unfold kDisc
  rw [add_assoc]
  congr 2
  rw [pseudoHyp, div_pow, hX, hvn, hNn]
  have hN' : ‖1 - conj ζ * z‖ ^ 2 ≠ 0 := by rw [← hNn]; exact hN
  field_simp
  linear_combination -key

/-- **Andersson–Pascuas estimate** with explicit constant `4/π`. -/
theorem abs_kDisc_le {z ζ : ℂ} (hz : z ∈ 𝔻) (hζ : ζ ∈ 𝔻) (hne : z ≠ ζ) :
    |kDisc z ζ| ≤ 4 / Real.pi * ((1 - ‖ζ‖ ^ 2) / ‖1 - conj ζ * z‖) ^ 2 *
      (1 + Real.log (1 / pseudoHyp ζ z)) := by
  rw [kDisc_eq hz hζ]
  set ρ := pseudoHyp ζ z with hρdef
  set D := ‖1 - conj ζ * z‖ with hDdef
  set A := (1 - ‖ζ‖ ^ 2) / D with hAdef
  set L := Real.log (1 / ρ) with hLdef
  have hD : 0 < D := norm_one_sub_conj_mul_pos hζ hz
  have hz1 := norm_lt_one_of_mem_disc hz
  have hζ1 := norm_lt_one_of_mem_disc hζ
  have hz0 := norm_nonneg z
  have hζ0 := norm_nonneg ζ
  have hρ0 : 0 < ρ := lt_of_le_of_ne (pseudoHyp_nonneg _ _)
    (fun h ↦ hne ((pseudoHyp_eq_zero_iff hζ hz).1 h.symm).symm)
  have hρ1 : ρ < 1 := pseudoHyp_lt_one hζ hz
  have hL : 0 ≤ L := Real.log_nonneg (by rw [le_div_iff₀ hρ0, one_mul]; exact hρ1.le)
  have hlog : Real.log (ρ ^ 2) = -2 * L := by
    rw [hLdef, one_div, Real.log_inv, Real.log_pow]; push_cast; ring
  have hA0 : 0 ≤ A := div_nonneg (by nlinarith) hD.le
  -- `1 - ρ² = A (1 - |z|²) / D ≤ 2A`
  have key := norm_one_sub_conj_mul_sq_sub ζ z
  have hρ2 : ρ ^ 2 = ‖ζ - z‖ ^ 2 / D ^ 2 := by rw [hρdef, pseudoHyp, div_pow]
  have hu : 1 - ρ ^ 2 = A * ((1 - ‖z‖ ^ 2) / D) := by
    rw [hρ2, hAdef]
    field_simp
    linear_combination key
  have hDz : 1 - ‖z‖ ≤ D := by
    have h1 := one_sub_mul_le_norm_one_sub_conj_mul ζ z
    have h2 : ‖ζ‖ * ‖z‖ ≤ ‖z‖ := mul_le_of_le_one_left hz0 hζ1.le
    linarith
  have hB : (1 - ‖z‖ ^ 2) / D ≤ 2 := by
    rw [div_le_iff₀ hD]
    have : 1 - ‖z‖ ^ 2 ≤ 2 * (1 - ‖z‖) := by nlinarith
    linarith
  have hu2A : 1 - ρ ^ 2 ≤ 2 * A := by
    rw [hu]; exact mul_le_mul_of_nonneg_left hB hA0 |>.trans_eq (mul_comm _ _)
  have hρsq1 : ρ ^ 2 < 1 := pow_lt_one₀ hρ0.le hρ1 two_ne_zero
  have hρsq0 : 0 < ρ ^ 2 := by positivity
  have hu0 : 0 ≤ 1 - ρ ^ 2 := by linarith
  have hR : ‖z‖ ^ 2 * (1 - ‖ζ‖ ^ 2) ^ 2 / D ^ 2 = ‖z‖ ^ 2 * A ^ 2 := by
    rw [hAdef, div_pow, mul_div_assoc]
  have hRle : ‖z‖ ^ 2 * A ^ 2 ≤ A ^ 2 :=
    mul_le_of_le_one_left (sq_nonneg A) (pow_le_one₀ hz0 hz1.le)
  have hR0 : 0 ≤ ‖z‖ ^ 2 * A ^ 2 := by positivity
  -- the main estimate `|E| ≤ 16 A² (1 + L)`
  have hE : |Real.log (ρ ^ 2) + (1 - ρ ^ 2) + ‖z‖ ^ 2 * (1 - ‖ζ‖ ^ 2) ^ 2 / D ^ 2| ≤
      16 * A ^ 2 * (1 + L) := by
    rw [hR]
    rcases le_or_gt (7 / 25) (ρ ^ 2) with hρ7 | hρ7
    · -- `ρ` not small: `|log(1 - u) + u| ≤ u² / (1 - u)`
      set u := 1 - ρ ^ 2 with hudef
      have hu1 : |u| < 1 := by rw [abs_of_nonneg hu0]; linarith
      have hser := Real.abs_log_sub_add_sum_range_le hu1 1
      simp only [Finset.range_one, Finset.sum_singleton, zero_add, pow_one, Nat.cast_zero,
        div_one] at hser
      rw [abs_of_nonneg hu0, show 1 - u = ρ ^ 2 by rw [hudef]; ring] at hser
      have hser' : |Real.log (ρ ^ 2) + u| ≤ u ^ 2 / ρ ^ 2 := by
        rw [add_comm]; exact hser
      have hu2 : u ^ 2 ≤ 4 * A ^ 2 := by
        have := pow_le_pow_left₀ hu0 hu2A 2
        rw [mul_pow] at this; norm_num at this; linarith
      have hdiv : u ^ 2 / ρ ^ 2 ≤ 100 / 7 * A ^ 2 := by
        rw [div_le_iff₀ hρsq0]
        have := mul_le_mul_of_nonneg_left hρ7 (by positivity : (0 : ℝ) ≤ 100 / 7 * A ^ 2)
        linarith
      calc |Real.log (ρ ^ 2) + u + ‖z‖ ^ 2 * A ^ 2|
          ≤ |Real.log (ρ ^ 2) + u| + |‖z‖ ^ 2 * A ^ 2| := abs_add_le _ _
        _ ≤ 100 / 7 * A ^ 2 + A ^ 2 := by
            rw [abs_of_nonneg hR0]; linarith
        _ ≤ 16 * A ^ 2 * (1 + L) := by
            have e : 16 * A ^ 2 * (1 + L) = 16 * A ^ 2 + 16 * (A ^ 2 * L) := by ring
            rw [e]
            linarith [sq_nonneg A, mul_nonneg (sq_nonneg A) hL]
    · -- `ρ` small: then `A` is bounded below
      have hA : 9 / 25 < A := by linarith
      have hA2 : 81 / 625 < A ^ 2 := by
        have := pow_lt_pow_left₀ hA (by norm_num) two_ne_zero
        norm_num at this; linarith
      calc |Real.log (ρ ^ 2) + (1 - ρ ^ 2) + ‖z‖ ^ 2 * A ^ 2|
          ≤ |Real.log (ρ ^ 2)| + |1 - ρ ^ 2| + |‖z‖ ^ 2 * A ^ 2| := abs_add_three _ _ _
        _ ≤ 2 * L + 1 + A ^ 2 := by
            rw [hlog, abs_of_nonneg hu0, abs_of_nonneg hR0,
              abs_of_nonpos (by linarith)]
            linarith
        _ ≤ 16 * A ^ 2 * (1 + L) := by
            have h1 : 2 * L ≤ 16 * A ^ 2 * L := mul_le_mul_of_nonneg_right (by linarith) hL
            have e : 16 * A ^ 2 * (1 + L) = 16 * A ^ 2 + 16 * A ^ 2 * L := by ring
            rw [e]
            linarith
  have hπ : 0 < Real.pi := Real.pi_pos
  rw [abs_mul, abs_of_pos (by positivity)]
  calc (4 * Real.pi)⁻¹ * |Real.log (ρ ^ 2) + (1 - ρ ^ 2) +
        ‖z‖ ^ 2 * (1 - ‖ζ‖ ^ 2) ^ 2 / D ^ 2|
      ≤ (4 * Real.pi)⁻¹ * (16 * A ^ 2 * (1 + L)) := by gcongr
    _ = 4 / Real.pi * A ^ 2 * (1 + L) := by field_simp; ring

/-- Sharp tail of the logarithmic series: `|log(1 − w) + w + w²/2| ≤ |w|³ / (3 (1 − |w|))`. -/
theorem norm_log_one_sub_add_le {w : ℂ} (hw : ‖w‖ < 1) :
    ‖Complex.log (1 - w) + w + w ^ 2 / 2‖ ≤ ‖w‖ ^ 3 / (3 * (1 - ‖w‖)) := by
  have h := Complex.hasSum_taylorSeries_neg_log hw
  have h3 := (hasSum_nat_add_iff' 3).2 h
  have hsum : ∑ i ∈ Finset.range 3, w ^ i / (i : ℂ) = w + w ^ 2 / 2 := by
    simp [Finset.sum_range_succ]
  rw [hsum] at h3
  have hw0 := norm_nonneg w
  have hg : HasSum (fun n : ℕ ↦ ‖w‖ ^ 3 / 3 * ‖w‖ ^ n) (‖w‖ ^ 3 / 3 * (1 - ‖w‖)⁻¹) :=
    (hasSum_geometric_of_lt_one hw0 hw).mul_left _
  have hle := h3.norm_le_of_bounded hg fun n ↦ by
    rw [norm_div, norm_pow]
    have hn : ‖((n + 3 : ℕ) : ℂ)‖ = (n : ℝ) + 3 := by
      rw [Complex.norm_natCast]; push_cast; ring
    rw [hn, div_le_iff₀ (by positivity), pow_add]
    have : (0 : ℝ) ≤ ‖w‖ ^ n * ‖w‖ ^ 3 := by positivity
    nlinarith [show (0 : ℝ) ≤ n from n.cast_nonneg]
  have e : Complex.log (1 - w) + w + w ^ 2 / 2 = -(-Complex.log (1 - w) - (w + w ^ 2 / 2)) := by
    ring
  rw [e, norm_neg]
  refine hle.trans (le_of_eq ?_)
  field_simp

theorem abs_kPlane_le {z ζ : ℂ} (hζ : 1 ≤ ‖ζ‖) (hzζ : 2 * ‖z‖ ≤ ‖ζ‖) :
    |kPlane z ζ| ≤ (3 * Real.pi)⁻¹ * (‖z‖ / ‖ζ‖) ^ 3 := by
  have hζ0 : ζ ≠ 0 := by intro h; rw [h, norm_zero] at hζ; linarith
  have hζn : 0 < ‖ζ‖ := norm_pos_iff.2 hζ0
  set w := z / ζ with hw
  have hwn : ‖w‖ = ‖z‖ / ‖ζ‖ := norm_div z ζ
  have hw2 : ‖w‖ ≤ 1 / 2 := by
    rw [hwn, div_le_iff₀ hζn]; linarith
  have hw1 : ‖w‖ < 1 := by linarith
  have h1w : (1 - w) ≠ 0 := by
    intro h
    have : w = 1 := by linear_combination -h
    rw [this, norm_one] at hw1
    exact lt_irrefl _ hw1
  have hzζe : z - ζ = -ζ * (1 - w) := by
    rw [hw]; field_simp; ring
  have hnorm : ‖z - ζ‖ = ‖ζ‖ * ‖1 - w‖ := by rw [hzζe, norm_mul, norm_neg]
  have hk : kPlane z ζ = (2 * Real.pi)⁻¹ * (Complex.log (1 - w) + w + w ^ 2 / 2).re := by
    unfold kPlane
    rw [ite_eq_left_iff.2 (fun h ↦ absurd hζ h), hnorm, mul_pow, Real.log_mul (by positivity) (by positivity), Real.log_pow,
      Real.log_pow]
    have e2 : z ^ 2 / (2 * ζ ^ 2) = w ^ 2 / 2 := by rw [hw]; field_simp
    rw [e2, ← hw]
    simp only [Complex.add_re, Complex.log_re]
    have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp
    ring
  rw [hk, abs_mul, abs_of_pos (by positivity), ← hwn]
  have hre := Complex.abs_re_le_norm (Complex.log (1 - w) + w + w ^ 2 / 2)
  have htail := norm_log_one_sub_add_le hw1
  have h3 : ‖w‖ ^ 3 / (3 * (1 - ‖w‖)) ≤ 2 / 3 * ‖w‖ ^ 3 := by
    rw [div_le_iff₀ (by linarith)]
    have : 0 ≤ ‖w‖ ^ 3 := by positivity
    nlinarith
  calc (2 * Real.pi)⁻¹ * |(Complex.log (1 - w) + w + w ^ 2 / 2).re|
      ≤ (2 * Real.pi)⁻¹ * (2 / 3 * ‖w‖ ^ 3) := by
        gcongr
        exact hre.trans (htail.trans h3)
    _ = (3 * Real.pi)⁻¹ * ‖w‖ ^ 3 := by
        have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
        field_simp

end OC
