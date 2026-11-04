import OrtegaCerdaMultipliers.Multiplier.Basic
import OrtegaCerdaMultipliers.Multiplier.Cells
import OrtegaCerdaMultipliers.Quadrature

/-!
# M08 (Multiplier) — Node configurations from M06 (Lemma 5)

See `blueprint/M08_Multiplier.md` §2.7, §3.10.
-/

open MeasureTheory Metric Set Complex
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace OC

/-- Nodes from Lemma 5 with `m = 3`, `k = 4`, `N = 12`; on cells with `sel i = true` the
alternative set `κ` (distance `≥ B·A·ρ(c i)` from the centre). -/
theorem exists_nodes_plane {ν : Measure ℂ} {η A : ℝ} {R : ℕ → Set ℂ} {c : ℕ → ℂ}
    (hC : IsCells univ dist (massRadius ν) ν 12 η A R c) (hA : 0 ≤ A) (B : ℝ) (hB : 0 ≤ B)
    (sel : ℕ → Bool) :
    ∃ Λ : ℕ → Multiset ℂ, IsNodes univ dist (massRadius ν) ν 12 ((B + 12) * A) R c (fun _ ↦ 3) Λ ∧
      (∀ i, sel i = false → ∀ w ∈ Λ i, dist (c i) w ≤ 6 * A * massRadius ν (c i)) ∧
      ∀ i, sel i = true → ∀ w ∈ Λ i, B * A * massRadius ν (c i) ≤ dist (c i) w := by
  have hρ : ∀ i, 0 ≤ massRadius ν (c i) := fun i ↦ Real.sInf_nonneg fun x hx ↦ hx.1.le
  have hex : ∀ i, ∃ L : Multiset ℂ, Multiset.card L = 12 ∧
      (∀ j < 3, ∫ ζ in R i, ζ ^ j ∂ν = (L.map (· ^ j)).sum) ∧
      (∀ w ∈ L, dist (c i) w ≤ (B + 12) * A * massRadius ν (c i)) ∧
      (sel i = false → ∀ w ∈ L, dist (c i) w ≤ 6 * A * massRadius ν (c i)) ∧
      (sel i = true → ∀ w ∈ L, B * A * massRadius ν (c i) ≤ dist (c i) w) := by
    intro i
    set r := A * massRadius ν (c i) with hr
    have hr0 : 0 ≤ r := mul_nonneg hA (hρ i)
    have hsupp : ν.restrict (R i) (closedBall (c i) r)ᶜ = 0 := by
      rw [Measure.restrict_apply isClosed_closedBall.isOpen_compl.measurableSet]
      convert measure_empty (μ := ν)
      ext w
      simp only [mem_inter_iff, mem_compl_iff, mem_closedBall, mem_empty_iff_false, iff_false,
        not_and]
      intro h1 h2
      exact h1 (by rw [dist_comm]; exact hC.subset i w h2)
    have hmass : ν.restrict (R i) univ = ((3 * 4 : ℕ) : ℝ≥0∞) := by
      rw [Measure.restrict_apply MeasurableSet.univ, univ_inter, hC.measure_eq i]
    obtain ⟨L, K, hL, hK, hLn, hKn, hmom⟩ :=
      lemma5_moments 3 4 (by norm_num) (by norm_num) (ν.restrict (R i)) (c i) r hr0 hsupp hmass
        B hB
    have hmL : ∀ j < 3, ∫ ζ in R i, ζ ^ j ∂ν = (L.map (· ^ j)).sum := fun j hj ↦ (hmom j hj).1
    have hmK : ∀ j < 3, ∫ ζ in R i, ζ ^ j ∂ν = (K.map (· ^ j)).sum := fun j hj ↦ (hmom j hj).2
    have hLd : ∀ w ∈ L, dist (c i) w ≤ 6 * r := fun w hw ↦ by
      rw [dist_comm, dist_eq_norm]; have := hLn w hw; push_cast at this; linarith
    have hKd : ∀ w ∈ K, B * r ≤ dist (c i) w ∧ dist (c i) w ≤ (B + 12) * r := fun w hw ↦ by
      rw [dist_comm, dist_eq_norm]; have := hKn w hw; push_cast at this
      constructor <;> linarith [this.1, this.2]
    cases hsel : sel i
    · refine ⟨L, by rw [hL], hmL, fun w hw ↦ ?_, fun _ ↦ fun w hw ↦ ?_, fun h ↦ by simp at h⟩
      · calc dist (c i) w ≤ 6 * r := hLd w hw
          _ ≤ (B + 12) * A * massRadius ν (c i) := by rw [hr]; nlinarith [mul_nonneg hA (hρ i)]
      · calc dist (c i) w ≤ 6 * r := hLd w hw
          _ = 6 * A * massRadius ν (c i) := by rw [hr]; ring
    · refine ⟨K, by rw [hK], hmK, fun w hw ↦ ?_, fun h ↦ by simp at h, fun _ ↦ fun w hw ↦ ?_⟩
      · calc dist (c i) w ≤ (B + 12) * r := (hKd w hw).2
          _ = (B + 12) * A * massRadius ν (c i) := by rw [hr]; ring
      · calc B * A * massRadius ν (c i) = B * r := by rw [hr]; ring
          _ ≤ dist (c i) w := (hKd w hw).1
  choose Λ hcard hmom hnear hfalse htrue using hex
  exact ⟨Λ, ⟨hcard, fun _ _ _ ↦ mem_univ _, hnear, hmom⟩, hfalse, htrue⟩

/-! ### Disc helpers -/

/-- `artanh p ≤ 5 p` for `0 ≤ p ≤ 1/5`. -/
theorem artanh_le_five_mul {p : ℝ} (hp0 : 0 ≤ p) (hp : p ≤ 1 / 5) : Real.artanh p ≤ 5 * p := by
  have h1 : p ≤ Real.tanh (5 * p) := by
    have := mul_le_tanh (S := 1) one_pos (by linarith : (0:ℝ) ≤ 5 * p) (by linarith)
    have hm : min (1 / 5) (Real.tanh 1 / 1) = 1 / 5 := by
      rw [div_one]; apply min_eq_left
      have := div_five_le_tanh (r := 1) zero_le_one le_rfl
      linarith
    rw [hm] at this; linarith
  have := Real.artanh_le_artanh (by linarith) (Real.tanh_lt_one _) h1
  rwa [Real.artanh_tanh] at this

/-- `p ≤ artanh p` for `0 ≤ p < 1`. -/
theorem le_artanh_self {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1) : p ≤ Real.artanh p := by
  have h := tanh_le_self (Real.artanh_nonneg hp0)
  rwa [Real.tanh_artanh ⟨by linarith, hp1⟩] at h

/-- Euclidean-to-hyperbolic: a point Euclidean-close to `c` (relative to `1 - |c|²`) is in `𝔻`
and hyperbolically close. -/
theorem mem_disc_and_hypDist_le {c w : ℂ} (hc : c ∈ 𝔻) {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ : τ ≤ 1 / 6)
    (hw : ‖w - c‖ ≤ τ * (1 - ‖c‖ ^ 2)) : w ∈ 𝔻 ∧ hypDist c w ≤ 6 * τ := by
  have hc1 := norm_lt_one_of_mem_disc hc
  have hcpos := one_sub_normSq_pos hc
  have hw𝔻 : w ∈ 𝔻 := by
    rw [mem_disc_iff_norm_lt_one]
    have := norm_le_norm_add_norm_sub' w c
    have h1 : 1 - ‖c‖ ^ 2 ≤ 2 * (1 - ‖c‖) := by nlinarith [norm_nonneg c]
    have h2 : τ * (1 - ‖c‖ ^ 2) ≤ 2 * τ * (1 - ‖c‖) := by
      calc τ * (1 - ‖c‖ ^ 2) ≤ τ * (2 * (1 - ‖c‖)) := mul_le_mul_of_nonneg_left h1 hτ0
        _ = 2 * τ * (1 - ‖c‖) := by ring
    have h3 : 2 * τ * (1 - ‖c‖) < 1 - ‖c‖ := by nlinarith
    linarith
  refine ⟨hw𝔻, ?_⟩
  have hden : (1 - τ) * (1 - ‖c‖ ^ 2) ≤ ‖1 - conj c * w‖ := by
    have e : 1 - conj c * w = ((1 - ‖c‖ ^ 2 : ℝ) : ℂ) - conj c * (w - c) := by
      rw [one_sub_conj_mul_self c |>.symm]; ring
    rw [e]
    have := norm_sub_norm_le (((1 - ‖c‖ ^ 2 : ℝ) : ℂ)) (conj c * (w - c))
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hcpos, norm_mul,
      Complex.norm_conj] at this
    have h3 : ‖c‖ * ‖w - c‖ ≤ τ * (1 - ‖c‖ ^ 2) := by
      calc ‖c‖ * ‖w - c‖ ≤ 1 * ‖w - c‖ := by gcongr
        _ ≤ τ * (1 - ‖c‖ ^ 2) := by linarith
    linarith
  have hp : pseudoHyp c w ≤ 6 / 5 * τ := by
    rw [pseudoHyp, norm_sub_rev, div_le_iff₀ (by nlinarith)]
    calc ‖w - c‖ ≤ τ * (1 - ‖c‖ ^ 2) := hw
      _ ≤ 6 / 5 * τ * ((1 - τ) * (1 - ‖c‖ ^ 2)) := by
          have h1 : 1 ≤ 6 / 5 * (1 - τ) := by linarith
          have := mul_le_mul_of_nonneg_left h1 (mul_nonneg hτ0 hcpos.le)
          linarith
      _ ≤ 6 / 5 * τ * ‖1 - conj c * w‖ := by gcongr
  rw [hypDist]
  calc Real.artanh (pseudoHyp c w) ≤ 5 * pseudoHyp c w :=
        artanh_le_five_mul (pseudoHyp_nonneg c w) (by linarith)
    _ ≤ 6 * τ := by linarith

/-- Hyperbolic lower bound from a Euclidean lower bound. -/
theorem le_hypDist_of_norm {c w : ℂ} (hc : c ∈ 𝔻) (hw : w ∈ 𝔻) {τ : ℝ}
    (hwτ : ‖w - c‖ ≤ τ * (1 - ‖c‖ ^ 2)) :
    ‖w - c‖ / ((1 + τ) * (1 - ‖c‖ ^ 2)) ≤ hypDist c w := by
  have hcpos := one_sub_normSq_pos hc
  have hc1 := norm_lt_one_of_mem_disc hc
  have hD := norm_one_sub_conj_mul_pos hc hw
  have hnum : ‖1 - conj c * w‖ ≤ (1 + τ) * (1 - ‖c‖ ^ 2) := by
    have e : 1 - conj c * w = ((1 - ‖c‖ ^ 2 : ℝ) : ℂ) - conj c * (w - c) := by
      rw [one_sub_conj_mul_self c |>.symm]; ring
    rw [e]
    refine (norm_sub_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hcpos, norm_mul, Complex.norm_conj]
    have : ‖c‖ * ‖w - c‖ ≤ τ * (1 - ‖c‖ ^ 2) := by
      calc ‖c‖ * ‖w - c‖ ≤ 1 * ‖w - c‖ := by gcongr
        _ ≤ τ * (1 - ‖c‖ ^ 2) := by linarith
    linarith
  have hp : ‖w - c‖ / ((1 + τ) * (1 - ‖c‖ ^ 2)) ≤ pseudoHyp c w := by
    rw [pseudoHyp, norm_sub_rev]
    exact div_le_div_of_nonneg_left (norm_nonneg _) hD hnum
  exact hp.trans (le_artanh_self (pseudoHyp_nonneg c w) (pseudoHyp_lt_one hc hw))

/-- A unit vector `u` with `b̄ u = i |b|` (tangential direction at `b`). -/
theorem exists_tangent_unit (b : ℂ) : ∃ u : ℂ, ‖u‖ = 1 ∧ conj b * u = I * (‖b‖ : ℂ) := by
  by_cases hb : b = 0
  · exact ⟨1, by simp, by simp [hb]⟩
  · have hb' : (‖b‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_pos_iff.2 hb).ne'
    refine ⟨I * b / ‖b‖, ?_, ?_⟩
    · rw [norm_div, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (norm_pos_iff.2 hb), one_mul, div_self (norm_pos_iff.2 hb).ne']
    · have : conj b * b = (‖b‖ : ℂ) ^ 2 := by
        rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
      rw [mul_div_assoc', div_eq_iff hb']
      linear_combination I * this

/-- Two points `b ± v` at prescribed hyperbolic distance `d` from `b`. -/
theorem exists_tangent_pair {b : ℂ} (hb : b ∈ 𝔻) {d : ℝ} (hd : 0 ≤ d) :
    ∃ v : ℂ, b + v ∈ 𝔻 ∧ b - v ∈ 𝔻 ∧ hypDist b (b + v) = d ∧ hypDist b (b - v) = d := by
  obtain ⟨u, hu, hbu⟩ := exists_tangent_unit b
  set T := Real.tanh d with hT
  have hT0 : 0 ≤ T := tanh_nonneg_of_nonneg hd
  have hT1 : T < 1 := Real.tanh_lt_one d
  set q := ‖b‖ with hq
  have hq1 : q < 1 := norm_lt_one_of_mem_disc hb
  have hq0 : 0 ≤ q := norm_nonneg b
  set a := 1 - q ^ 2 with ha
  have ha0 : 0 < a := by nlinarith
  have hden : 0 < 1 - T ^ 2 * q ^ 2 := by nlinarith
  set τ := T * a / Real.sqrt (1 - T ^ 2 * q ^ 2) with hτ
  have hsq := Real.sq_sqrt hden.le
  have hspos := Real.sqrt_pos.2 hden
  have hτ0 : 0 ≤ τ := by positivity
  have hτ2 : τ ^ 2 = T ^ 2 * a ^ 2 / (1 - T ^ 2 * q ^ 2) := by
    rw [hτ, div_pow, hsq]; ring
  refine ⟨τ * u, ?_⟩
  -- the two signs at once
  have key : ∀ σ : ℝ, σ ^ 2 = 1 → b + (σ : ℂ) * (τ * u) ∈ 𝔻 ∧
      hypDist b (b + (σ : ℂ) * (τ * u)) = d := by
    intro σ hσ
    set w := b + (σ : ℂ) * (τ * u) with hw
    have hwb : ‖b - w‖ = τ := by
      rw [hw, sub_add_cancel_left, norm_neg, norm_mul, norm_mul, hu, Complex.norm_real,
        Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hτ0]
      have : |σ| = 1 := by
        have := abs_mul_abs_self σ; rw [← sq] at this
        nlinarith [abs_nonneg σ, sq_abs σ]
      rw [this]; ring
    have hD : 1 - conj b * w = ((a : ℝ) : ℂ) - (σ * τ * q : ℝ) * I := by
      rw [hw, mul_add, show conj b * ((σ : ℂ) * (τ * u)) = (σ : ℂ) * τ * (conj b * u) by ring,
        hbu, ha]
      have : conj b * b = ((q ^ 2 : ℝ) : ℂ) := by
        rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      rw [this]; push_cast; ring
    have hDn : ‖1 - conj b * w‖ ^ 2 = a ^ 2 + τ ^ 2 * q ^ 2 := by
      rw [hD, Complex.sq_norm, Complex.normSq_apply]
      simp only [sub_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, sub_im, mul_im]
      ring_nf
      rw [hσ]; ring
    have hwn : ‖w‖ ^ 2 = q ^ 2 + τ ^ 2 := by
      have e : w = b + (σ * τ : ℝ) * u := by rw [hw]; push_cast; ring
      rw [e, Complex.sq_norm, Complex.normSq_add, Complex.normSq_eq_norm_sq,
        Complex.normSq_eq_norm_sq, norm_mul, hu, Complex.norm_real, Real.norm_eq_abs, mul_one,
        sq_abs]
      have hre : (b * conj ((σ * τ : ℝ) * u)).re = 0 := by
        have : b * conj ((σ * τ : ℝ) * u) = (σ * τ : ℝ) * conj (conj b * u) := by
          simp [map_mul]; ring
        rw [this, hbu]
        simp
      rw [hre]
      have : (σ * τ) ^ 2 = τ ^ 2 := by rw [mul_pow, hσ, one_mul]
      rw [this]; ring
    have hw𝔻 : w ∈ 𝔻 := by
      rw [mem_disc_iff_norm_lt_one]
      have h1 : ‖w‖ ^ 2 < 1 := by
        rw [hwn, hτ2]
        rw [← sub_pos]
        have : 1 - (q ^ 2 + T ^ 2 * a ^ 2 / (1 - T ^ 2 * q ^ 2)) =
            a * (1 - T ^ 2) / (1 - T ^ 2 * q ^ 2) := by
          rw [eq_div_iff hden.ne', sub_mul, add_mul, div_mul_cancel₀ _ hden.ne', ha]
          ring
        rw [this]
        apply div_pos (mul_pos ha0 (by nlinarith)) hden
      nlinarith [norm_nonneg w]
    refine ⟨hw𝔻, ?_⟩
    have hDpos := norm_one_sub_conj_mul_pos hb hw𝔻
    have hp : pseudoHyp b w = T := by
      rw [pseudoHyp, hwb]
      have hDsq : ‖1 - conj b * w‖ ^ 2 = (a / Real.sqrt (1 - T ^ 2 * q ^ 2)) ^ 2 := by
        rw [hDn, hτ2, div_pow, hsq]; field_simp; ring
      have hDeq : ‖1 - conj b * w‖ = a / Real.sqrt (1 - T ^ 2 * q ^ 2) := by
        have := (sq_eq_sq₀ hDpos.le (by positivity)).1 hDsq
        exact this
      rw [hDeq, hτ]; field_simp
    rw [hypDist, hp, hT, Real.artanh_tanh]
  obtain ⟨h1, h2⟩ := key 1 (by norm_num)
  obtain ⟨h3, h4⟩ := key (-1) (by norm_num)
  simp only [ofReal_one, one_mul, ofReal_neg, neg_mul, ← sub_eq_add_neg] at h1 h2 h3 h4
  exact ⟨h1, h3, h2, h4⟩

/-- The barycentre of a cell lies in the closed hyperbolic ball of radius `A ρ` around the
centre. -/
theorem barycentre_mem {ν : Measure ℂ} {R : Set ℂ} {c : ℂ} (hc : c ∈ 𝔻) {s : ℝ}
    (hR : MeasurableSet R) (hR𝔻 : R ⊆ 𝔻) (hRs : ∀ w ∈ R, hypDist c w ≤ s) (hmass : ν R = 12) :
    (12 : ℂ)⁻¹ * ∫ ζ in R, ζ ∂ν ∈ 𝔻 ∧ hypDist c ((12 : ℂ)⁻¹ * ∫ ζ in R, ζ ∂ν) ≤ s := by
  set r' := Real.tanh (Real.artanh ‖c‖ + s)
  set Bc := closedBall (0 : ℂ) r' ∩ {w | hypDist c w ≤ s}
  have hBc_eq : Bc = {w | w ∈ 𝔻 ∧ hypDist c w ≤ s} := by
    ext w
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨closedBall_tanh_subset_disc _ h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨closedHypBall_subset_closedBall hc s ⟨h1, h2⟩, h2⟩
  have hconv : Convex ℝ Bc := by rw [hBc_eq]; exact convex_closedHypBall hc s
  have hcont : ContinuousOn (hypDist c) (closedBall 0 r') := by
    have := continuousOn_hypDist.comp (continuous_const.prodMk continuous_id).continuousOn
      (s := closedBall 0 r') (fun w hw ↦ ⟨hc, closedBall_tanh_subset_disc _ hw⟩)
    exact this
  have hclosed : IsClosed Bc := hcont.preimage_isClosed_of_isClosed isClosed_closedBall isClosed_Iic
  have hfin : ν R ≠ ∞ := by rw [hmass]; exact ENNReal.ofNat_ne_top
  have h0 : ν R ≠ 0 := by rw [hmass]; norm_num
  have hint : IntegrableOn (fun ζ : ℂ ↦ ζ) R ν := by
    refine IntegrableOn.of_bound hfin.lt_top continuous_id.aestronglyMeasurable 1 ?_
    exact (ae_restrict_iff' hR).2 (Filter.Eventually.of_forall fun ζ hζ ↦
      (norm_lt_one_of_mem_disc (hR𝔻 hζ)).le)
  have hmem := hconv.set_average_mem hclosed h0 hfin
    ((ae_restrict_iff' hR).2 (Filter.Eventually.of_forall fun ζ hζ ↦
      (hBc_eq ▸ (⟨hR𝔻 hζ, hRs ζ hζ⟩ : ζ ∈ {w | w ∈ 𝔻 ∧ hypDist c w ≤ s}) : ζ ∈ Bc))) hint
  rw [setAverage_eq] at hmem
  have hreal : ν.real R = 12 := by simp [Measure.real, hmass]
  rw [hreal] at hmem
  have e : ((12 : ℝ)⁻¹ • ∫ ζ in R, ζ ∂ν) = (12 : ℂ)⁻¹ * ∫ ζ in R, ζ ∂ν := by
    rw [Complex.real_smul]; push_cast; ring
  rw [e, hBc_eq] at hmem
  exact hmem


/-- Disc: small cells (`ρ(c i) ≤ ρ₀`) use Lemma 5 (order 3); large cells use `N` copies of the
barycentre (order 2), or, if selected, `6` copies each of `b ± v` (`v` tangential). -/
theorem exists_nodes_disc (A : ℝ) (hA : 0 < A) :
    ∃ Bl : ℝ, 0 ≤ Bl ∧ ∀ B : ℝ, 0 ≤ B → ∃ ρ₀ B' : ℝ, 0 < ρ₀ ∧ 0 ≤ B' ∧
      ∀ (ν : Measure ℂ) (η : ℝ) (R : ℕ → Set ℂ) (c : ℕ → ℂ),
      IsCells 𝔻 hypDist (massRadiusDisc ν) ν 12 η A R c → (∀ i, 0 < massRadiusDisc ν (c i)) →
      ∀ sel : ℕ → Bool, ∃ (m : ℕ → ℕ) (Λ : ℕ → Multiset ℂ),
        IsNodes 𝔻 hypDist (massRadiusDisc ν) ν 12 B' R c m Λ ∧ (∀ i, 2 ≤ m i) ∧
        (∀ i, massRadiusDisc ν (c i) ≤ ρ₀ → 3 ≤ m i) ∧
        (∀ i, sel i = false → ∀ w ∈ Λ i, hypDist (c i) w ≤ Bl * massRadiusDisc ν (c i)) ∧
        ∀ i, sel i = true → ∀ w ∈ Λ i, B * A * massRadiusDisc ν (c i) ≤ hypDist (c i) w := by
  refine ⟨72 * A, by positivity, fun B hB ↦ ?_⟩
  set ρ₀ := 1 / (100 * (B + 6) * (A + 1)) with hρ₀
  set B' := max (72 * A) (max (24 * (B + 6) * A) ((B + 2) * A)) with hB'
  have hB'1 : 72 * A ≤ B' := le_max_left _ _
  have hB'2 : 24 * (B + 6) * A ≤ B' := (le_max_left _ _).trans (le_max_right _ _)
  have hB'3 : (B + 2) * A ≤ B' := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨ρ₀, B', by positivity, le_trans (by positivity) hB'1, fun ν η R c hC hρ sel ↦ ?_⟩
  have hci := hC.center_mem'
  have hex : ∀ i, ∃ (mi : ℕ) (L : Multiset ℂ), Multiset.card L = 12 ∧ 2 ≤ mi ∧
      (massRadiusDisc ν (c i) ≤ ρ₀ → 3 ≤ mi) ∧
      (∀ j < mi, ∫ ζ in R i, ζ ^ j ∂ν = (L.map (· ^ j)).sum) ∧ (∀ w ∈ L, w ∈ 𝔻) ∧
      (∀ w ∈ L, hypDist (c i) w ≤ B' * massRadiusDisc ν (c i)) ∧
      (sel i = false → ∀ w ∈ L, hypDist (c i) w ≤ 72 * A * massRadiusDisc ν (c i)) ∧
      (sel i = true → ∀ w ∈ L, B * A * massRadiusDisc ν (c i) ≤ hypDist (c i) w) := by
    intro i
    set ρi := massRadiusDisc ν (c i) with hρi
    have hρi0 := hρ i
    set sr := A * ρi with hsr
    have hsr0 : 0 < sr := by positivity
    have hc := hci i
    have hcpos := one_sub_normSq_pos hc
    have hRs : ∀ w ∈ R i, hypDist (c i) w ≤ sr := fun w hw ↦ hC.subset i w hw
    have hR𝔻 : R i ⊆ 𝔻 := hC.subset_univ i
    by_cases hsmall : ρi ≤ ρ₀
    · -- small cell: Lemma 5 with order 3
      set re := sr * Real.exp (2 * sr) * (1 - ‖c i‖ ^ 2) with hre
      have hre0 : 0 ≤ re := by positivity
      have hsupp : ν.restrict (R i) (closedBall (c i) re)ᶜ = 0 := by
        rw [Measure.restrict_apply isClosed_closedBall.isOpen_compl.measurableSet]
        convert measure_empty (μ := ν)
        ext w
        simp only [mem_inter_iff, mem_compl_iff, mem_closedBall, mem_empty_iff_false, iff_false,
          not_and]
        intro h1 h2
        exact h1 (by rw [dist_eq_norm]; exact norm_sub_le_mul_exp hc (hR𝔻 h2) (hRs w h2))
      have hmass : ν.restrict (R i) univ = ((3 * 4 : ℕ) : ℝ≥0∞) := by
        rw [Measure.restrict_apply MeasurableSet.univ, univ_inter, hC.measure_eq i]
      obtain ⟨L, K, hL, hK, hLn, hKn, hmom⟩ :=
        lemma5_moments 3 4 (by norm_num) (by norm_num) (ν.restrict (R i)) (c i) re hre0 hsupp
          hmass (2 * B) (by positivity)
      -- size of `sr`
      have hsr_small : sr ≤ 1 / (100 * (B + 6)) := by
        rw [hsr]
        calc A * ρi ≤ A * ρ₀ := by gcongr
          _ = A / (A + 1) * (1 / (100 * (B + 6))) := by rw [hρ₀]; field_simp
          _ ≤ 1 * (1 / (100 * (B + 6))) := by
              gcongr; rw [div_le_one (by positivity)]; linarith
          _ = 1 / (100 * (B + 6)) := one_mul _
      have hB6 : 6 ≤ B + 6 := by linarith
      have hsr600 : sr ≤ 1 / 600 := hsr_small.trans (by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith)
      have hexp : Real.exp (2 * sr) ≤ 4 / 3 :=
        (Real.exp_le_exp.2 (by linarith)).trans exp_quarter_le
      have hexp1 : 1 ≤ Real.exp (2 * sr) := Real.one_le_exp (by positivity)
      set τo := 6 * sr * Real.exp (2 * sr) with hτo
      set τk := (2 * B + 12) * sr * Real.exp (2 * sr) with hτk
      have hτo0 : 0 ≤ τo := by positivity
      have hτk0 : 0 ≤ τk := by positivity
      have hτo1 : τo ≤ 8 * sr := by rw [hτo]; nlinarith
      have hτk1 : τk ≤ 16 * (B + 6) * sr := by rw [hτk]; nlinarith
      have hτk6 : τk ≤ 1 / 6 := by
        refine hτk1.trans ?_
        have : (B + 6) * sr ≤ 1 / 100 := by
          rw [le_div_iff₀ (by norm_num)]
          have := hsr_small; rw [le_div_iff₀ (by positivity)] at this; nlinarith
        nlinarith
      have hτo6 : τo ≤ 1 / 6 := by linarith
      have hLd : ∀ w ∈ L, w ∈ 𝔻 ∧ hypDist (c i) w ≤ 72 * A * ρi := by
        intro w hw
        have h1 : ‖w - c i‖ ≤ τo * (1 - ‖c i‖ ^ 2) := by
          have := hLn w hw; push_cast at this; rw [hτo]; rw [hre] at this; linarith
        obtain ⟨hw𝔻, hd⟩ := mem_disc_and_hypDist_le hc hτo0 hτo6 h1
        exact ⟨hw𝔻, hd.trans (by nlinarith)⟩
      have hKd : ∀ w ∈ K, w ∈ 𝔻 ∧ hypDist (c i) w ≤ 24 * (B + 6) * A * ρi ∧
          B * A * ρi ≤ hypDist (c i) w := by
        intro w hw
        have hk := hKn w hw
        push_cast at hk
        have h1 : ‖w - c i‖ ≤ τk * (1 - ‖c i‖ ^ 2) := by
          rw [hτk]; rw [hre] at hk; nlinarith [hk.2]
        obtain ⟨hw𝔻, hd⟩ := mem_disc_and_hypDist_le hc hτk0 hτk6 h1
        refine ⟨hw𝔻, hd.trans (by nlinarith), ?_⟩
        have hlow := le_hypDist_of_norm hc hw𝔻 h1
        refine le_trans ?_ hlow
        rw [le_div_iff₀ (by positivity)]
        have h2 : 2 * B * re ≤ ‖w - c i‖ := hk.1
        rw [hre] at h2
        have : B * sr * ((1 + τk) * (1 - ‖c i‖ ^ 2)) ≤ 2 * B * (sr * Real.exp (2 * sr) *
            (1 - ‖c i‖ ^ 2)) := by
          have h3 : (1 + τk) ≤ 2 * Real.exp (2 * sr) := by linarith
          have := mul_le_mul_of_nonneg_left h3 (mul_nonneg (mul_nonneg hB hsr0.le) hcpos.le)
          nlinarith
        have e : B * A * ρi = B * sr := by rw [hsr]; ring
        rw [e]
        linarith
      have hmomL : ∀ j < 3, ∫ ζ in R i, ζ ^ j ∂ν = (L.map (· ^ j)).sum := fun j hj ↦ (hmom j hj).1
      have hmomK : ∀ j < 3, ∫ ζ in R i, ζ ^ j ∂ν = (K.map (· ^ j)).sum := fun j hj ↦ (hmom j hj).2
      cases hsel : sel i
      · refine ⟨3, L, by rw [hL], by norm_num, fun _ ↦ le_rfl, hmomL, fun w hw ↦ (hLd w hw).1,
          fun w hw ↦ ?_, fun _ w hw ↦ (hLd w hw).2, fun h ↦ by simp at h⟩
        exact (hLd w hw).2.trans (by nlinarith)
      · refine ⟨3, K, by rw [hK], by norm_num, fun _ ↦ le_rfl, hmomK, fun w hw ↦ (hKd w hw).1,
          fun w hw ↦ ?_, fun h ↦ by simp at h, fun _ w hw ↦ (hKd w hw).2.2⟩
        exact (hKd w hw).2.1.trans (by nlinarith)
    · -- large cell: barycentre, order 2
      obtain ⟨hb𝔻, hbd⟩ := barycentre_mem hc (hC.measurableSet i) hR𝔻 hRs
        (by rw [hC.measure_eq i]; norm_num)
      set b := (12 : ℂ)⁻¹ * ∫ ζ in R i, ζ ∂ν with hb
      have hint1 : ∫ ζ in R i, ζ ∂ν = 12 * b := by rw [hb]; ring
      have hreal : ν.real (R i) = 12 := by simp [Measure.real, hC.measure_eq i]
      have hint0 : ∫ ζ in R i, ζ ^ 0 ∂ν = 12 := by
        simp only [pow_zero, setIntegral_const, hreal]; norm_num
      cases hsel : sel i
      · refine ⟨2, Multiset.replicate 12 b, by simp, le_rfl, fun h ↦ absurd h hsmall, ?_,
          fun w hw ↦ by rw [Multiset.eq_of_mem_replicate hw]; exact hb𝔻, fun w hw ↦ ?_,
          fun _ w hw ↦ ?_, fun h ↦ by simp at h⟩
        · intro j hj
          interval_cases j
          · rw [hint0]; simp; norm_num
          · simp only [pow_one, Multiset.map_replicate, Multiset.sum_replicate, hint1]
            norm_num
        · rw [Multiset.eq_of_mem_replicate hw]
          refine hbd.trans ?_
          rw [hsr]; nlinarith
        · rw [Multiset.eq_of_mem_replicate hw]
          refine hbd.trans ?_
          rw [hsr]; nlinarith
      · obtain ⟨v, hv1, hv2, hd1, hd2⟩ := exists_tangent_pair hb𝔻 (d := (B + 1) * sr)
          (by positivity)
        have hdist : ∀ w ∈ Multiset.replicate 6 (b + v) + Multiset.replicate 6 (b - v),
            w ∈ 𝔻 ∧ hypDist b w = (B + 1) * sr := by
          intro w hw
          rcases Multiset.mem_add.1 hw with h | h
          · rw [Multiset.eq_of_mem_replicate h]; exact ⟨hv1, hd1⟩
          · rw [Multiset.eq_of_mem_replicate h]; exact ⟨hv2, hd2⟩
        refine ⟨2, Multiset.replicate 6 (b + v) + Multiset.replicate 6 (b - v), by simp,
          le_rfl, fun h ↦ absurd h hsmall, ?_, fun w hw ↦ (hdist w hw).1, fun w hw ↦ ?_,
          fun h ↦ by simp at h, fun _ w hw ↦ ?_⟩
        · intro j hj
          interval_cases j
          · rw [hint0]; simp; norm_num
          · simp only [pow_one, Multiset.map_add, Multiset.map_replicate, Multiset.sum_add,
              Multiset.sum_replicate, hint1, nsmul_eq_mul]
            push_cast; ring
        · obtain ⟨hw𝔻, hdw⟩ := hdist w hw
          have := hypDist_triangle hc hb𝔻 hw𝔻
          calc hypDist (c i) w ≤ sr + (B + 1) * sr := by linarith
            _ = (B + 2) * A * ρi := by rw [hsr]; ring
            _ ≤ B' * ρi := by gcongr
        · obtain ⟨hw𝔻, hdw⟩ := hdist w hw
          have := hypDist_triangle hb𝔻 hc hw𝔻
          have h3 : hypDist b (c i) = hypDist (c i) b := hypDist_comm _ _
          calc B * A * ρi = (B + 1) * sr - sr := by rw [hsr]; ring
            _ ≤ hypDist (c i) w := by linarith
  choose m Λ hcard hm2 hm3 hmom hmem hnear hfalse htrue using hex
  exact ⟨m, Λ, ⟨hcard, hmem, hnear, hmom⟩, hm2, hm3, hfalse, htrue⟩

end OC
