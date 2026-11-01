import OrtegaCerdaMultipliers.Foundations.Hyperbolic

/-!
# M01 (Foundations) — Hyperbolic geometry: lemmas requested by later modules

See `blueprint/M01_Foundations.md`.

These are the M01-type statements that the later module docs assume but that
`Foundations/Hyperbolic.lean` does not contain.  All statements are proved.

* `hypArea`, the hyperbolic area measure `dm / (1 - |z|²)²` on `𝔻` (the one shared definition,
  with M11's name and formula; used by M08, M09, M11) and `hypArea_hypBall` (M08 §4.1);
* `hypDist_radial`, `hypBall_zero`, `continuousOn_hypDist` (assumed by M03 §4.2);
* `ball_subset_hypBall_tanh`, `hypBall_subset_ball_tanh`: the `tanh` forms of the inclusions
  assumed by M03 §4.2 (the names `ball_subset_hypBall`, `hypBall_subset_ball` are taken in
  `Hyperbolic.lean` by the forms with `r ≤ 1` and explicit constants);
* the disc geometry lemmas of M08 §2.2: `norm_sub_le_of_hypDist_le`,
  `norm_one_sub_conj_mul_comparable`, `convex_closedHypBall`.
-/

open MeasureTheory Metric Set Complex
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace OC

/-! ## The hyperbolic area measure -/

/-- The hyperbolic area measure `dm(z) / (1 - |z|²)²` on `𝔻` (shared definition; M11's form). -/
def hypArea : Measure ℂ :=
  (volume.restrict 𝔻).withDensity fun z ↦ ENNReal.ofReal ((1 - ‖z‖ ^ 2)⁻¹ ^ 2)

/-- Hyperbolic area of a hyperbolic disc: `hypArea (D(z, r)) = π sinh² r` (Möbius invariance and
the computation at `0`: `∫_{|w|<t} dm/(1-|w|²)² = π t²/(1 - t²)` with `t = tanh r`). -/
theorem hypArea_apply_of_subset {S : Set ℂ} (hS : MeasurableSet S) (hS𝔻 : S ⊆ 𝔻) :
    hypArea S = ∫⁻ w in S, ENNReal.ofReal ((1 - ‖w‖ ^ 2)⁻¹ ^ 2) := by
  rw [hypArea, withDensity_apply _ hS, Measure.restrict_restrict hS, inter_eq_left.2 hS𝔻]

/-- Möbius invariance of the hyperbolic area density, in lower-integral form. -/
theorem lintegral_hypBall_eq_lintegral_ball {z : ℂ} (hz : z ∈ 𝔻) (r : ℝ) :
    ∫⁻ w in hypBall z r, ENNReal.ofReal ((1 - ‖w‖ ^ 2)⁻¹ ^ 2) =
      ∫⁻ w in ball (0 : ℂ) (Real.tanh r), ENNReal.ofReal ((1 - ‖w‖ ^ 2)⁻¹ ^ 2) := by
  set t := Real.tanh r
  have hsub : ball (0 : ℂ) t ⊆ 𝔻 := ball_subset_ball (Real.tanh_lt_one r).le
  have hderiv : ∀ x ∈ ball (0 : ℂ) t, HasFDerivWithinAt (mobius z)
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (deriv (mobius z) x)).restrictScalars ℝ)
      (ball 0 t) x := fun x hx ↦
    ((differentiableAt_mobius hz (hsub hx)).hasDerivAt.hasFDerivAt.restrictScalars
      ℝ).hasFDerivWithinAt
  have h := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume measurableSet_ball hderiv
    ((injOn_mobius hz).mono hsub) (fun w ↦ ENNReal.ofReal ((1 - ‖w‖ ^ 2)⁻¹ ^ 2))
  rw [← hypBall_eq_image_mobius hz] at h
  rw [h]
  refine setLIntegral_congr_fun measurableSet_ball fun x hx ↦ ?_
  have hx𝔻 := hsub hx
  simp only [det_smulRight_restrictScalars]
  rw [abs_of_nonneg (by positivity), ← ENNReal.ofReal_mul (by positivity), norm_deriv_mobius hz hx𝔻]
  have h1 := one_sub_normSq_pos hx𝔻
  have h2 := one_sub_normSq_pos (mobius_mem_disc hz hx𝔻)
  congr 1
  field_simp

/-- `∫_{|w| < t} dm / (1 - |w|²)² = π t² / (1 - t²)`. -/
theorem lintegral_ball_zero_hypDensity {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    ∫⁻ w in ball (0 : ℂ) t, ENNReal.ofReal ((1 - ‖w‖ ^ 2)⁻¹ ^ 2) =
      ENNReal.ofReal (Real.pi * (t ^ 2 / (1 - t ^ 2))) := by
  set T := t ^ 2 with hT
  have hT0 : 0 ≤ T := by positivity
  have hT1 : T < 1 := by nlinarith
  set F : ℝ → ℝ≥0∞ := (Iio T).indicator fun u ↦ ENNReal.ofReal ((1 - u)⁻¹ ^ 2) with hF
  have hFm : Measurable F := by
    refine Measurable.indicator ?_ measurableSet_Iio
    exact ENNReal.measurable_ofReal.comp (by fun_prop)
  have h := lintegral_comp_normSq_sub 0 hFm
  have e1 : ∫⁻ z : ℂ, F (‖z - 0‖ ^ 2) =
      ∫⁻ w in ball (0 : ℂ) t, ENNReal.ofReal ((1 - ‖w‖ ^ 2)⁻¹ ^ 2) := by
    rw [← lintegral_indicator measurableSet_ball]
    refine lintegral_congr fun z ↦ ?_
    simp only [sub_zero, hF]
    by_cases hz : z ∈ ball (0 : ℂ) t
    · have hz' : ‖z‖ ^ 2 < T := by
        rw [mem_ball_zero_iff] at hz
        exact pow_lt_pow_left₀ hz (norm_nonneg _) two_ne_zero
      rw [indicator_of_mem hz, indicator_of_mem (show ‖z‖ ^ 2 ∈ Iio T from hz')]
    · have hz' : ¬ ‖z‖ ^ 2 < T := by
        rw [mem_ball_zero_iff, not_lt] at hz
        exact not_lt.2 (pow_le_pow_left₀ ht0 hz 2)
      rw [indicator_of_notMem hz, indicator_of_notMem (show ‖z‖ ^ 2 ∉ Iio T from hz')]
  have e2 : ∫⁻ u in Ioi (0 : ℝ), F u = ENNReal.ofReal (T / (1 - T)) := by
    rw [hF, lintegral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio,
      show Iio T ∩ Ioi 0 = Ioo 0 T from by ext u; simp [and_comm]]
    have hcont : ContinuousOn (fun u : ℝ ↦ (1 - u)⁻¹ ^ 2) (Icc 0 T) :=
      ((continuousOn_const.sub continuousOn_id).inv₀ fun u hu ↦ by
        have := hu.2; simp only [Pi.sub_apply, id]; intro h; linarith).pow 2
    have hint : IntegrableOn (fun u : ℝ ↦ (1 - u)⁻¹ ^ 2) (Ioo 0 T) :=
      (hcont.integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun u ↦ by positivity)]
    congr 1
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hT0]
    have hderiv : ∀ u ∈ uIcc 0 T, HasDerivAt (fun u : ℝ ↦ (1 - u)⁻¹) ((1 - u)⁻¹ ^ 2) u := by
      intro u hu
      rw [uIcc_of_le hT0] at hu
      have hne : (1 - u) ≠ 0 := by have := hu.2; intro h; linarith
      have := ((hasDerivAt_id u).const_sub 1).inv hne
      simp only [id] at this
      convert this using 1
      field_simp
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      (hcont.intervalIntegrable_of_Icc hT0)]
    have : (1 - T) ≠ 0 := by linarith
    field_simp
    ring
  rw [← e1, h, e2, ← ENNReal.ofReal_mul Real.pi_pos.le]

/-- `tanh² r / (1 - tanh² r) = sinh² r`. -/
theorem tanh_sq_div_one_sub_tanh_sq (r : ℝ) :
    Real.tanh r ^ 2 / (1 - Real.tanh r ^ 2) = Real.sinh r ^ 2 := by
  have hc := Real.cosh_pos r
  have hcs := Real.cosh_sq r
  rw [Real.tanh_eq_sinh_div_cosh]
  have : Real.cosh r ^ 2 - Real.sinh r ^ 2 = 1 := by linarith
  field_simp
  rw [this]
  ring

theorem hypArea_hypBall {z : ℂ} (hz : z ∈ 𝔻) {r : ℝ} (hr : 0 ≤ r) :
    hypArea (hypBall z r) = ENNReal.ofReal (Real.pi * Real.sinh r ^ 2) := by
  rw [hypArea_apply_of_subset (isOpen_hypBall z r).measurableSet (hypBall_subset_disc z r),
    lintegral_hypBall_eq_lintegral_ball hz r,
    lintegral_ball_zero_hypDensity (tanh_nonneg_of_nonneg hr) (Real.tanh_lt_one r),
    tanh_sq_div_one_sub_tanh_sq]

/-! ## Radial distances, the disc at `0`, continuity -/

/-- `artanh` is odd on `(-1, 1)`. -/
theorem artanh_neg_eq {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) : Real.artanh (-x) = -Real.artanh x := by
  conv_lhs => rw [← Real.tanh_artanh hx, ← Real.tanh_neg, Real.artanh_tanh]

/-- `tanh r > 0` for `r > 0`. -/
theorem tanh_pos_of_pos {r : ℝ} (hr : 0 < r) : 0 < Real.tanh r := by
  rw [tanh_eq_exp_two_mul]
  have h1 : 1 < Real.exp (2 * r) := Real.one_lt_exp_iff.2 (by linarith)
  exact div_pos (by linarith) (by linarith)

theorem hypDist_radial {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t < 1) {u : ℂ} (hu : ‖u‖ = 1) :
    hypDist (s * u) (t * u) = Real.artanh t - Real.artanh s := by
  have hs1 : s < 1 := lt_of_le_of_lt hst ht
  have hst1 : 0 < 1 - s * t := by nlinarith
  have hρ : pseudoHyp (s * u) (t * u) = (t - s) / (1 - s * t) := by
    have e1 : (s : ℂ) * u - t * u = ((s - t : ℝ) : ℂ) * u := by push_cast; ring
    have e2 : 1 - conj ((s : ℂ) * u) * (t * u) = ((1 - s * t : ℝ) : ℂ) := by
      rw [map_mul, Complex.conj_ofReal]
      have : conj u * u = ((‖u‖ ^ 2 : ℝ) : ℂ) := by
        rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      calc 1 - (s : ℂ) * conj u * (t * u) = 1 - s * t * (conj u * u) := by ring
        _ = _ := by rw [this, hu]; push_cast; ring_nf
    rw [pseudoHyp, e1, e2, norm_mul, hu, mul_one, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonpos (by linarith), abs_of_pos hst1]
    ring
  have key := artanh_add_artanh (x := t) (y := -s) ⟨by linarith, ht⟩ ⟨by linarith, by linarith⟩
  rw [artanh_neg_eq ⟨by linarith, hs1⟩] at key
  rw [hypDist, hρ, sub_eq_add_neg (Real.artanh t), key]
  congr 1
  ring

theorem hypBall_zero {r : ℝ} (hr : 0 < r) : hypBall 0 r = ball 0 (Real.tanh r) := by
  have h0 : (0 : ℂ) ∈ 𝔻 := mem_ball_self one_pos
  rw [hypBall_eq_pseudoBall h0]
  ext w
  simp only [pseudoHyp_zero_left, Set.mem_ofPred_eq, mem_ball_zero_iff]
  constructor
  · exact fun h ↦ h.2
  · intro h
    exact ⟨h.trans (Real.tanh_lt_one r), h⟩

/-- `artanh` is continuous on `(-1, 1)`. -/
theorem continuousOn_artanh : ContinuousOn Real.artanh (Ioo (-1 : ℝ) 1) := by
  have h : ContinuousOn (fun x : ℝ ↦ (1 + x) / (1 - x)) (Ioo (-1 : ℝ) 1) :=
    ContinuousOn.div (by fun_prop) (by fun_prop) fun x hx ↦ by linarith [hx.2]
  have h2 : ContinuousOn (fun x : ℝ ↦ Real.sqrt ((1 + x) / (1 - x))) (Ioo (-1 : ℝ) 1) :=
    h.sqrt
  refine h2.log fun x hx ↦ ?_
  have : 0 < (1 + x) / (1 - x) := div_pos (by linarith [hx.1]) (by linarith [hx.2])
  exact (Real.sqrt_pos.2 this).ne'

theorem continuousOn_hypDist : ContinuousOn (fun p : ℂ × ℂ ↦ hypDist p.1 p.2) (𝔻 ×ˢ 𝔻) := by
  have hρ : ContinuousOn (fun p : ℂ × ℂ ↦ pseudoHyp p.1 p.2) (𝔻 ×ˢ 𝔻) := by
    have : ContinuousOn (fun p : ℂ × ℂ ↦ ‖p.1 - p.2‖ / ‖1 - conj p.1 * p.2‖) (𝔻 ×ˢ 𝔻) :=
      ContinuousOn.div (by fun_prop) (by fun_prop)
        fun p hp ↦ (norm_one_sub_conj_mul_pos hp.1 hp.2).ne'
    exact this
  exact continuousOn_artanh.comp hρ fun p hp ↦ pseudoHyp_mem_Ioo hp.1 hp.2

/-! ## Euclidean size of hyperbolic discs, `tanh` form -/

theorem ball_subset_hypBall_tanh {z : ℂ} (hz : z ∈ 𝔻) {r : ℝ} (hr : 0 < r) :
    ball z (Real.tanh r * (1 - ‖z‖ ^ 2) / 2) ⊆ hypBall z r := by
  rw [hypBall_eq_pseudoBall hz]
  exact ball_subset_pseudoBall hz (tanh_pos_of_pos hr) (Real.tanh_lt_one r)

theorem hypBall_subset_ball_tanh {z : ℂ} (hz : z ∈ 𝔻) {r : ℝ} (hr : 0 < r) :
    hypBall z r ⊆ ball z (Real.tanh r * (1 - ‖z‖ ^ 2) / (1 - Real.tanh r)) := by
  rw [hypBall_eq_pseudoBall hz]
  exact pseudoBall_subset_ball hz (tanh_pos_of_pos hr) (Real.tanh_lt_one r)

/-! ## Disc geometry used by M08 (§2.2) -/

theorem norm_sub_le_of_hypDist_le {c w : ℂ} (hc : c ∈ 𝔻) (hw : w ∈ 𝔻) {s : ℝ}
    (hs : hypDist c w ≤ s) (hs1 : Real.tanh s < 1) :
    ‖w - c‖ ≤ Real.tanh s / (1 - Real.tanh s) * (1 - ‖c‖ ^ 2) := by
  have hρ : pseudoHyp c w ≤ Real.tanh s := (hypDist_le_iff hc hw s).1 hs
  set t := Real.tanh s
  obtain ⟨v, hv_def⟩ : ∃ v, v = mobius c w := ⟨_, rfl⟩
  have hv : v ∈ 𝔻 := hv_def ▸ mobius_mem_disc hc hw
  have hvn : ‖v‖ ≤ t := by rw [hv_def, ← pseudoHyp_eq_norm_mobius]; exact hρ
  have hwv : w = mobius c v := by rw [hv_def, mobius_mobius hc hw]
  have hDv := one_sub_conj_mul_ne_zero_of_mem hc hv
  have e : ‖w - c‖ * ‖1 - conj c * v‖ = ‖v‖ * (1 - ‖c‖ ^ 2) := by
    rw [hwv, mobius_sub_self hDv, norm_div, norm_neg, norm_mul, norm_one_sub_conj_mul_self hc,
      div_mul_cancel₀ _ (norm_ne_zero_iff.2 hDv)]
  have hD := one_sub_mul_le_norm_one_sub_conj_mul c v
  have hc1 := norm_lt_one_of_mem_disc hc
  have hcv : ‖c‖ * ‖v‖ ≤ ‖v‖ := mul_le_of_le_one_left (norm_nonneg v) hc1.le
  have hD' : 1 - t ≤ ‖1 - conj c * v‖ := by linarith
  have h1r := one_sub_normSq_pos hc
  have ht1 : 0 < 1 - t := by linarith
  rw [div_mul_eq_mul_div, le_div_iff₀ ht1]
  calc ‖w - c‖ * (1 - t) ≤ ‖w - c‖ * ‖1 - conj c * v‖ :=
        mul_le_mul_of_nonneg_left hD' (norm_nonneg _)
    _ = ‖v‖ * (1 - ‖c‖ ^ 2) := e
    _ ≤ t * (1 - ‖c‖ ^ 2) := mul_le_mul_of_nonneg_right hvn h1r.le

/-- `(1 + tanh s) / (1 - tanh s) = e^{2s}`. -/
theorem one_add_tanh_div_one_sub_tanh (s : ℝ) :
    (1 + Real.tanh s) / (1 - Real.tanh s) = Real.exp (2 * s) := by
  have hE := Real.exp_pos (2 * s)
  rw [tanh_eq_exp_two_mul]
  field_simp
  ring

/-- One half of `norm_one_sub_conj_mul_comparable`. -/
theorem norm_one_sub_conj_mul_le_exp {z a b : ℂ} (hz : z ∈ 𝔻) (ha : a ∈ 𝔻) (hb : b ∈ 𝔻)
    {s : ℝ} (hs : hypDist a b ≤ s) :
    ‖1 - conj z * b‖ ≤ Real.exp (2 * s) * ‖1 - conj z * a‖ := by
  have ht1 := Real.tanh_lt_one s
  set t := Real.tanh s
  have hba := norm_sub_le_of_hypDist_le ha hb hs ht1
  have hs0 : 0 ≤ s := (hypDist_nonneg a b).trans hs
  have ht0 : 0 ≤ t := tanh_nonneg_of_nonneg hs0
  have hz1 := norm_lt_one_of_mem_disc hz
  have ha1 := norm_lt_one_of_mem_disc ha
  have hza : ‖z‖ * ‖a‖ ≤ ‖a‖ := mul_le_of_le_one_left (norm_nonneg a) hz1.le
  have hDa := one_sub_mul_le_norm_one_sub_conj_mul z a
  have hA : 1 - ‖a‖ ^ 2 ≤ 2 * ‖1 - conj z * a‖ := by nlinarith [norm_nonneg a]
  have htri : ‖1 - conj z * b‖ ≤ ‖1 - conj z * a‖ + ‖b - a‖ := by
    calc ‖1 - conj z * b‖ = ‖(1 - conj z * a) - conj z * (b - a)‖ := by ring_nf
      _ ≤ ‖1 - conj z * a‖ + ‖conj z * (b - a)‖ := norm_sub_le _ _
      _ ≤ ‖1 - conj z * a‖ + ‖b - a‖ := by
        rw [norm_mul, Complex.norm_conj]
        gcongr
        exact mul_le_of_le_one_left (norm_nonneg _) hz1.le
  have ht1' : 0 < 1 - t := by linarith
  have hq : 0 ≤ t / (1 - t) := div_nonneg ht0 ht1'.le
  rw [← one_add_tanh_div_one_sub_tanh]
  have e : (1 + t) / (1 - t) = 1 + 2 * (t / (1 - t)) := by field_simp; ring
  rw [e]
  calc ‖1 - conj z * b‖ ≤ ‖1 - conj z * a‖ + t / (1 - t) * (1 - ‖a‖ ^ 2) := by linarith
    _ ≤ ‖1 - conj z * a‖ + t / (1 - t) * (2 * ‖1 - conj z * a‖) := by gcongr
    _ = (1 + 2 * (t / (1 - t))) * ‖1 - conj z * a‖ := by ring

theorem norm_one_sub_conj_mul_comparable {z c ξ : ℂ} (hz : z ∈ 𝔻) (hc : c ∈ 𝔻) (hξ : ξ ∈ 𝔻)
    {s : ℝ} (hs : hypDist c ξ ≤ s) :
    ‖1 - conj z * ξ‖ ≤ Real.exp (2 * s) * ‖1 - conj z * c‖ ∧
      ‖1 - conj z * c‖ ≤ Real.exp (2 * s) * ‖1 - conj z * ξ‖ :=
  ⟨norm_one_sub_conj_mul_le_exp hz hc hξ hs,
    norm_one_sub_conj_mul_le_exp hz hξ hc (by rwa [hypDist_comm])⟩

theorem convex_closedHypBall {c : ℂ} (hc : c ∈ 𝔻) (s : ℝ) :
    Convex ℝ {w | w ∈ 𝔻 ∧ hypDist c w ≤ s} := by
  rcases lt_or_ge s 0 with hs | hs
  · convert convex_empty (𝕜 := ℝ) (E := ℂ)
    ext w
    simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and, not_le]
    exact fun _ ↦ hs.trans_le (hypDist_nonneg c w)
  have ht0 : 0 ≤ Real.tanh s := tanh_nonneg_of_nonneg hs
  have ht1 := Real.tanh_lt_one s
  set t := Real.tanh s
  have hc1 := norm_lt_one_of_mem_disc hc
  have hA : 0 < 1 - t ^ 2 * ‖c‖ ^ 2 := by
    have h1 : t ^ 2 < 1 := by nlinarith
    have h2 : ‖c‖ ^ 2 < 1 := by nlinarith [norm_nonneg c]
    have : t ^ 2 * ‖c‖ ^ 2 < 1 := by
      calc t ^ 2 * ‖c‖ ^ 2 ≤ 1 * ‖c‖ ^ 2 := by gcongr
        _ < 1 := by linarith
    linarith
  set c₀ : ℂ := (((1 - t ^ 2) / (1 - t ^ 2 * ‖c‖ ^ 2) : ℝ) : ℂ) * c
  set R : ℝ := t * (1 - ‖c‖ ^ 2) / (1 - t ^ 2 * ‖c‖ ^ 2)
  have hR0 : 0 ≤ R := by
    have := one_sub_normSq_pos hc
    positivity
  have key := fun w ↦ norm_sub_sq_sub_sq_mul_norm_one_sub_sq c w t hA.ne'
  have hset : {w | w ∈ 𝔻 ∧ hypDist c w ≤ s} = 𝔻 ∩ closedBall c₀ R := by
    ext w
    simp only [mem_ofPred_eq, mem_inter_iff, mem_closedBall, dist_eq_norm]
    constructor
    · rintro ⟨hw, h⟩
      refine ⟨hw, ?_⟩
      have h' := (hypDist_le_iff hc hw s).1 h
      have hD := norm_one_sub_conj_mul_pos hc hw
      rw [pseudoHyp, div_le_iff₀ hD, norm_sub_rev] at h'
      have h2 : ‖w - c‖ ^ 2 ≤ (t * ‖1 - conj c * w‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h' 2
      have h3 : (1 - t ^ 2 * ‖c‖ ^ 2) * (‖w - c₀‖ ^ 2 - R ^ 2) ≤ 0 := by
        rw [← key w]; nlinarith
      have h4 : ‖w - c₀‖ ^ 2 ≤ R ^ 2 := by
        by_contra hcon
        exact absurd h3 (not_le.2 (mul_pos hA (by linarith)))
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) hR0 two_ne_zero).1 h4
    · rintro ⟨hw, h⟩
      refine ⟨hw, (hypDist_le_iff hc hw s).2 ?_⟩
      have hD := norm_one_sub_conj_mul_pos hc hw
      rw [pseudoHyp, div_le_iff₀ hD, norm_sub_rev]
      have h2 : ‖w - c₀‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
      have h3 : ‖w - c‖ ^ 2 - t ^ 2 * ‖1 - conj c * w‖ ^ 2 ≤ 0 := by
        rw [key w]
        exact mul_nonpos_of_nonneg_of_nonpos hA.le (by linarith)
      have h4 : ‖w - c‖ ^ 2 ≤ (t * ‖1 - conj c * w‖) ^ 2 := by nlinarith
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h4
  rw [hset]
  exact (convex_ball 0 1).inter (convex_closedBall c₀ R)

end OC
