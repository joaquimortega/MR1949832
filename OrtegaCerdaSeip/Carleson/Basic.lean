import OrtegaCerdaSeip.Defs

/-!
# M03 (Carleson) — Carleson measures: definitions and transfer lemmas

See `blueprint/M03_Carleson.md` (§1.1–§1.4).

* `IsCarlesonWith ν K`: `ν(D(x,r)) ≤ K r` for every disc centred on `ℝ` (the paper's two-sided
  Carleson measure, p. 409; `IsTwoSidedCarleson ν ↔ ∃ K, IsCarlesonWith ν K`).
* `IsCarlesonLarge ν K`: the same bound for radii `r ≥ 1` only.  Every estimate of M03–M05 needs
  only this weaker property, and it is what the application of Lemma 4 on p. 410 (M14) provides:
  a measure with atoms near `ℝ` is never Carleson at small scales (blueprint M03 §3, G1).
* `expImMeasure ε ν = e^{-ε|Im z|} dν(z)`, the measure in the hypothesis of Lemma 4.
* `isCarlesonWith_volume_strip`: Lebesgue measure on a horizontal strip (§1.4).
-/

open MeasureTheory Metric Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace OCS

/-! ## Definitions -/

/-- `ν` is a *two-sided Carleson measure with constant `K`* (p. 409): `ν(D(x, r)) ≤ K r` for every
disc `D(x, r)` centred on the real axis. -/
def IsCarlesonWith (ν : Measure ℂ) (K : ℝ≥0) : Prop :=
  ∀ x : ℝ, ∀ r : ℝ, 0 < r → ν (ball (x : ℂ) r) ≤ K * ENNReal.ofReal r

/-- *Large-scale* Carleson condition: `ν(D(x, r)) ≤ K r` for every disc centred on the real axis
with radius `r ≥ 1`.  Equivalently `ν(D(x, r)) ≤ K max(r, 1)` for all `r`. -/
def IsCarlesonLarge (ν : Measure ℂ) (K : ℝ≥0) : Prop :=
  ∀ x : ℝ, ∀ r : ℝ, 1 ≤ r → ν (ball (x : ℂ) r) ≤ K * ENNReal.ofReal r

/-- The measure `e^{-ε|Im z|} dν(z)` of the hypothesis of Lemma 4. -/
def expImMeasure (ε : ℝ) (ν : Measure ℂ) : Measure ℂ :=
  ν.withDensity fun z ↦ ENNReal.ofReal (Real.exp (-ε * |z.im|))

/-! ## Elementary properties -/

/-- Discs centred on the real axis are invariant under `z ↦ z̄`. -/
theorem preimage_conj_ball_ofReal (x r : ℝ) :
    (starRingEnd ℂ) ⁻¹' ball (x : ℂ) r = ball (x : ℂ) r := by
  ext z
  have h := Complex.dist_conj_conj z x
  rw [Complex.conj_ofReal] at h
  simp only [mem_preimage, mem_ball, h]

theorem isTwoSidedCarleson_iff {ν : Measure ℂ} :
    IsTwoSidedCarleson ν ↔ ∃ K, IsCarlesonWith ν K :=
  Iff.rfl

theorem IsCarlesonWith.isCarlesonLarge {ν : Measure ℂ} {K : ℝ≥0} (h : IsCarlesonWith ν K) :
    IsCarlesonLarge ν K :=
  fun x r hr ↦ h x r (zero_lt_one.trans_le hr)

theorem IsCarlesonLarge.mono {ν ν' : Measure ℂ} {K : ℝ≥0} (h : IsCarlesonLarge ν K)
    (h' : ν' ≤ ν) : IsCarlesonLarge ν' K := by
  intro x r hr
  exact (h' _).trans (h x r hr)

theorem IsCarlesonLarge.mono_const {ν : Measure ℂ} {K K' : ℝ≥0} (h : IsCarlesonLarge ν K)
    (hK : K ≤ K') : IsCarlesonLarge ν K' := by
  intro x r hr
  exact (h x r hr).trans (mul_le_mul_left (by exact_mod_cast hK) _)

/-- For radii `r < 1` the large-scale condition still gives `ν(D(x, r)) ≤ K`. -/
theorem IsCarlesonLarge.measure_ball_le {ν : Measure ℂ} {K : ℝ≥0} (h : IsCarlesonLarge ν K)
    (x : ℝ) (r : ℝ) : ν (ball (x : ℂ) r) ≤ K * ENNReal.ofReal (max r 1) := by
  rcases le_total 1 r with hr | hr
  · rw [max_eq_left hr]
    exact h x r hr
  · rw [max_eq_right hr]
    exact (measure_mono (ball_subset_ball hr)).trans (h x 1 le_rfl)

/-- A finite measure is large-scale Carleson, with constant its total mass. -/
theorem isCarlesonLarge_of_isFiniteMeasure (ν : Measure ℂ) [IsFiniteMeasure ν] :
    IsCarlesonLarge ν (ν univ).toNNReal := by
  intro x r hr
  rw [ENNReal.coe_toNNReal (measure_ne_top _ _)]
  calc ν (ball (x : ℂ) r) ≤ ν univ := measure_mono (subset_univ _)
    _ ≤ ν univ * ENNReal.ofReal r :=
      le_mul_of_one_le_right' (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hr)

theorem IsCarlesonLarge.withDensity_le_one {ν : Measure ℂ} {K : ℝ≥0} (h : IsCarlesonLarge ν K)
    {f : ℂ → ℝ≥0∞} (hf : ∀ z, f z ≤ 1) : IsCarlesonLarge (ν.withDensity f) K := by
  intro x r hr
  rw [withDensity_apply _ measurableSet_ball]
  calc ∫⁻ z in ball (x : ℂ) r, f z ∂ν ≤ ∫⁻ _ in ball (x : ℂ) r, 1 ∂ν := lintegral_mono hf
    _ = ν (ball (x : ℂ) r) := setLIntegral_one _
    _ ≤ K * ENNReal.ofReal r := h x r hr

/-- The reflection `z ↦ z̄` preserves the discs centred on `ℝ`. -/
theorem IsCarlesonLarge.map_conj {ν : Measure ℂ} {K : ℝ≥0} (h : IsCarlesonLarge ν K) :
    IsCarlesonLarge (ν.map (starRingEnd ℂ)) K := by
  intro x r hr
  rw [Measure.map_apply Complex.continuous_conj.measurable measurableSet_ball,
    preimage_conj_ball_ofReal]
  exact h x r hr

/-! ## The measure `e^{-ε|Im z|} dν` -/

theorem expImMeasure_absolutelyContinuous (ε : ℝ) (ν : Measure ℂ) : expImMeasure ε ν ≪ ν :=
  withDensity_absolutelyContinuous _ _

/-- The density `e^{-ε|Im z|}` is at most `1` for `ε ≥ 0`. -/
theorem expIm_density_le_one {ε : ℝ} (hε : 0 ≤ ε) (z : ℂ) :
    ENNReal.ofReal (Real.exp (-ε * |z.im|)) ≤ 1 :=
  ENNReal.ofReal_le_one.2 (Real.exp_le_one_iff.2
    (by have := abs_nonneg z.im; nlinarith))

/-- The density `e^{-ε|Im z|}` is measurable. -/
theorem measurable_expIm_density (ε : ℝ) :
    Measurable fun z : ℂ ↦ ENNReal.ofReal (Real.exp (-ε * |z.im|)) := by
  fun_prop

theorem isFiniteMeasure_expImMeasure {ε : ℝ} (hε : 0 ≤ ε) (ν : Measure ℂ) [IsFiniteMeasure ν] :
    IsFiniteMeasure (expImMeasure ε ν) := by
  unfold expImMeasure
  refine ⟨?_⟩
  rw [withDensity_apply _ MeasurableSet.univ]
  calc ∫⁻ z in univ, ENNReal.ofReal (Real.exp (-ε * |z.im|)) ∂ν
      ≤ ∫⁻ _ in univ, 1 ∂ν := lintegral_mono fun z ↦ expIm_density_le_one hε z
    _ = ν univ := setLIntegral_one _
    _ < ∞ := measure_lt_top _ _

theorem expImMeasure_restrict (ε : ℝ) (ν : Measure ℂ) {s : Set ℂ} (hs : MeasurableSet s) :
    expImMeasure ε (ν.restrict s) = (expImMeasure ε ν).restrict s := by
  exact (restrict_withDensity hs _).symm

theorem expImMeasure_map_conj (ε : ℝ) (ν : Measure ℂ) :
    expImMeasure ε (ν.map (starRingEnd ℂ)) = (expImMeasure ε ν).map (starRingEnd ℂ) := by
  have hc : Measurable (starRingEnd ℂ) := Complex.continuous_conj.measurable
  ext s hs
  rw [expImMeasure, withDensity_apply _ hs, setLIntegral_map hs (measurable_expIm_density ε) hc,
    Measure.map_apply hc hs, expImMeasure, withDensity_apply _ (hc hs)]
  simp only [Complex.conj_im, abs_neg]

/-- Damping by `e^{-ε|Im z|}` (`ε ≥ 0`) preserves the Carleson property. -/
theorem IsCarlesonLarge.to_expImMeasure {ε : ℝ} (hε : 0 ≤ ε) {ν : Measure ℂ} {K : ℝ≥0}
    (h : IsCarlesonLarge ν K) : IsCarlesonLarge (expImMeasure ε ν) K := by
  exact h.withDensity_le_one (expIm_density_le_one hε)

/-- **Transfer on strips.**  If `ν` is carried by the strip `|Im z| ≤ b` and `e^{-ε|Im z|} dν` is
Carleson with constant `K`, then `ν` is Carleson with constant `e^{εb} K`. -/
theorem IsCarlesonLarge.of_expImMeasure {ε b : ℝ} (hε : 0 ≤ ε) {ν : Measure ℂ} {K : ℝ≥0}
    (h : IsCarlesonLarge (expImMeasure ε ν) K) (hb : ∀ᵐ z ∂ν, |z.im| ≤ b) :
    IsCarlesonLarge ν (Real.toNNReal (Real.exp (ε * b)) * K) := by
  intro x r hr
  have key : ν (ball (x : ℂ) r) ≤
      ENNReal.ofReal (Real.exp (ε * b)) * expImMeasure ε ν (ball (x : ℂ) r) := by
    rw [expImMeasure, withDensity_apply _ measurableSet_ball,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← setLIntegral_one]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_of_ae hb] with z hz
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (Real.one_le_exp (by nlinarith))
  calc ν (ball (x : ℂ) r)
      ≤ ENNReal.ofReal (Real.exp (ε * b)) * expImMeasure ε ν (ball (x : ℂ) r) := key
    _ ≤ ENNReal.ofReal (Real.exp (ε * b)) * (K * ENNReal.ofReal r) := by gcongr; exact h x r hr
    _ = ((Real.toNNReal (Real.exp (ε * b)) * K : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal r := by
      rw [ENNReal.coe_mul, mul_assoc]; rfl

/-! ## Lebesgue measure on horizontal strips -/

/-- Area of the rectangle `(a, b) × [c, d]`. -/
theorem volume_reIoo_imIcc (a b c d : ℝ) :
    volume {z : ℂ | a < z.re ∧ z.re < b ∧ c ≤ z.im ∧ z.im ≤ d} =
      ENNReal.ofReal (b - a) * ENNReal.ofReal (d - c) := by
  have hset : {z : ℂ | a < z.re ∧ z.re < b ∧ c ≤ z.im ∧ z.im ≤ d} =
      Complex.measurableEquivRealProd ⁻¹' (Ioo a b ×ˢ Icc c d) := by
    ext z
    simp [Complex.measurableEquivRealProd, and_assoc]
  rw [hset, Complex.volume_preserving_equiv_real_prod.measure_preimage_equiv,
    Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ioo, Real.volume_Icc]

/-- Lebesgue measure on a horizontal strip `a ≤ Im z ≤ b` is a two-sided Carleson measure with
constant `2(b - a)`: the disc `D(x, r)` meets the strip inside a rectangle of area `2r(b - a)`. -/
theorem isCarlesonWith_volume_strip {a b : ℝ} (hab : a ≤ b) :
    IsCarlesonWith (volume.restrict {z : ℂ | a ≤ z.im ∧ z.im ≤ b})
      (Real.toNNReal (2 * (b - a))) := by
  intro x r hr
  rw [Measure.restrict_apply measurableSet_ball]
  have hsub : ball (x : ℂ) r ∩ {z : ℂ | a ≤ z.im ∧ z.im ≤ b} ⊆
      {z : ℂ | x - r < z.re ∧ z.re < x + r ∧ a ≤ z.im ∧ z.im ≤ b} := by
    rintro z ⟨hz, hab⟩
    rw [mem_ball, dist_eq_norm] at hz
    have h1 := (Complex.abs_re_le_norm (z - x)).trans_lt hz
    rw [Complex.sub_re, Complex.ofReal_re, abs_lt] at h1
    exact ⟨by linarith, by linarith, hab.1, hab.2⟩
  calc volume (ball (x : ℂ) r ∩ {z : ℂ | a ≤ z.im ∧ z.im ≤ b})
      ≤ volume {z : ℂ | x - r < z.re ∧ z.re < x + r ∧ a ≤ z.im ∧ z.im ≤ b} := measure_mono hsub
    _ = ENNReal.ofReal (x + r - (x - r)) * ENNReal.ofReal (b - a) := volume_reIoo_imIcc _ _ _ _
    _ = ((Real.toNNReal (2 * (b - a)) : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal r := by
      change _ = ENNReal.ofReal (2 * (b - a)) * ENNReal.ofReal r
      rw [← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_mul (by linarith)]
      congr 1
      ring

end OCS
