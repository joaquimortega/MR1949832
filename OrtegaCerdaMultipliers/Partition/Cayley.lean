import OrtegaCerdaMultipliers.Partition.Rectangles

/-!
# M05 (Partition) — Cayley coordinates and horocyclic boxes in `𝔻`

See `blueprint/M05_Partition.md` §2.2.  Scaffold: statements, proofs `sorry`; definitions are real.
-/

open MeasureTheory Metric Set Complex
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace OC

/-- The Cayley map `𝔻 → ℍ`, `z ↦ i(1+z)/(1-z)`. -/
def cayley (z : ℂ) : ℂ := I * (1 + z) / (1 - z)

/-- Its inverse `ℍ → 𝔻`, `w ↦ (w - i)/(w + i)`. -/
def cayleyInv (w : ℂ) : ℂ := (w - I) / (w + I)

/-- The preimage in `𝔻` of a set of the upper half-plane. -/
def cayleyPre (S : Set ℂ) : Set ℂ := {z | z ∈ 𝔻 ∧ cayley z ∈ S}

/-- A horocyclic box: two horocycles and two geodesics through `1`. -/
def discBox (x₁ x₂ y₁ y₂ : ℝ) : Set ℂ := cayleyPre (rect x₁ x₂ y₁ y₂)

theorem cay_re (z : ℂ) : (cayley z).re = -2 * z.im / Complex.normSq (1 - z) := by
  simp only [cayley, Complex.div_re, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im, Complex.sub_re,
    Complex.sub_im]
  ring

theorem cay_im (z : ℂ) : (cayley z).im = (1 - Complex.normSq z) / Complex.normSq (1 - z) := by
  simp only [cayley, Complex.div_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im, Complex.sub_re,
    Complex.sub_im, Complex.normSq_apply]
  ring

theorem cay_one_sub_ne_zero {z : ℂ} (hz : z ∈ 𝔻) : 1 - z ≠ 0 := by
  intro h
  have : z = 1 := by linear_combination -h
  rw [this, mem_ball_zero_iff, norm_one] at hz
  exact lt_irrefl _ hz

theorem cay_normSq_lt_one {z : ℂ} (hz : z ∈ 𝔻) : Complex.normSq z < 1 := by
  rw [Complex.normSq_eq_norm_sq]
  have h := mem_ball_zero_iff.1 hz
  nlinarith [norm_nonneg z]

theorem cayley_im_pos {z : ℂ} (hz : z ∈ 𝔻) : 0 < (cayley z).im := by
  rw [cay_im]
  exact div_pos (by linarith [cay_normSq_lt_one hz])
    (Complex.normSq_pos.2 (cay_one_sub_ne_zero hz))

theorem cayleyInv_cayley {z : ℂ} (hz : z ∈ 𝔻) : cayleyInv (cayley z) = z := by
  have h := cay_one_sub_ne_zero hz
  have hnum : I * (1 + z) / (1 - z) - I = 2 * I * z / (1 - z) := by field_simp; ring
  have hden : I * (1 + z) / (1 - z) + I = 2 * I / (1 - z) := by field_simp; ring
  unfold cayleyInv cayley
  rw [hnum, hden]
  field_simp

theorem cay_add_I_ne_zero {w : ℂ} (hw : 0 < w.im) : w + I ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  linarith

theorem cayley_cayleyInv {w : ℂ} (hw : 0 < w.im) : cayley (cayleyInv w) = w := by
  have h := cay_add_I_ne_zero hw
  unfold cayley cayleyInv
  have h1 : 1 - (w - I) / (w + I) = 2 * I / (w + I) := by field_simp; ring
  have h2 : 1 + (w - I) / (w + I) = 2 * w / (w + I) := by field_simp; ring
  rw [h1, h2]
  field_simp

theorem cayleyInv_mem {w : ℂ} (hw : 0 < w.im) : cayleyInv w ∈ 𝔻 := by
  have h := cay_add_I_ne_zero hw
  rw [mem_ball_zero_iff, cayleyInv, norm_div, div_lt_one (norm_pos_iff.2 h)]
  have hsq : ‖w - I‖ ^ 2 < ‖w + I‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.I_re,
      Complex.I_im]
    nlinarith
  exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) hsq

theorem measurable_cayley : Measurable cayley := by
  unfold cayley
  fun_prop

/-- The Cayley map is an isometry onto the half-plane metric. -/
theorem pseudoHyp_cayleyInv {w₁ w₂ : ℂ} (h₁ : 0 < w₁.im) (h₂ : 0 < w₂.im) :
    pseudoHyp (cayleyInv w₁) (cayleyInv w₂) = ‖w₁ - w₂‖ / ‖w₁ - conj w₂‖ := by
  have ha := cay_add_I_ne_zero h₁
  have hb := cay_add_I_ne_zero h₂
  have hac : conj w₁ - I ≠ 0 := by
    intro h; apply ha
    have := congrArg conj h
    simpa using this
  have hcw : w₁ - conj w₂ ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    linarith
  have hcw' : conj w₁ - w₂ ≠ 0 := by
    intro h; apply hcw
    have := congrArg conj h
    simpa using this
  have e1 : cayleyInv w₁ - cayleyInv w₂ = 2 * I * (w₁ - w₂) / ((w₁ + I) * (w₂ + I)) := by
    unfold cayleyInv; field_simp; ring
  have e2 : 1 - conj (cayleyInv w₁) * cayleyInv w₂ =
      2 * I * (conj w₁ - w₂) / ((conj w₁ - I) * (w₂ + I)) := by
    unfold cayleyInv
    rw [map_div₀, map_sub, map_add, Complex.conj_I]
    rw [show conj w₁ + -I = conj w₁ - I by ring]
    field_simp
    ring
  have n1 : ‖conj w₁ - I‖ = ‖w₁ + I‖ := by
    rw [← Complex.norm_conj (w₁ + I), map_add, Complex.conj_I]; ring_nf
  have n2 : ‖conj w₁ - w₂‖ = ‖w₁ - conj w₂‖ := by
    rw [← Complex.norm_conj (w₁ - conj w₂), map_sub, Complex.conj_conj]
  rw [pseudoHyp, e1, e2]
  simp only [norm_div, norm_mul]
  rw [n1, n2]
  have : ‖w₁ + I‖ ≠ 0 := norm_ne_zero_iff.2 ha
  have : ‖w₂ + I‖ ≠ 0 := norm_ne_zero_iff.2 hb
  have : ‖w₁ - conj w₂‖ ≠ 0 := norm_ne_zero_iff.2 hcw
  have : ‖2 * I‖ ≠ 0 := by simp
  field_simp

/-- Level sets of `Re ∘ cayley` and `Im ∘ cayley` lie on circles or lines, hence are porous. -/
theorem isPorous_cayley_re (x : ℝ) : IsPorous (cayleyPre {w | w.re = x}) := by
  by_cases hx : x = 0
  · refine IsPorous.mono (isPorous_line 0 1) ?_
    rintro z ⟨hz, hzx⟩
    simp only [mem_setOf_eq, cay_re, hx] at hzx
    have hn := Complex.normSq_pos.2 (cay_one_sub_ne_zero hz)
    rw [div_eq_zero_iff] at hzx
    have him : z.im = 0 := by
      rcases hzx with h | h
      · linarith
      · exact absurd h hn.ne'
    exact ⟨z.re, Complex.ext (by simp) (by simp [him])⟩
  · refine IsPorous.mono (isPorous_sphere (⟨1, -1 / x⟩ : ℂ) (1 / |x|)) ?_
    rintro z ⟨hz, hzx⟩
    simp only [mem_setOf_eq, cay_re] at hzx
    have hn := Complex.normSq_pos.2 (cay_one_sub_ne_zero hz)
    rw [div_eq_iff hn.ne', Complex.normSq_apply] at hzx
    simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im] at hzx
    rw [mem_sphere, Complex.dist_eq, ← sq_eq_sq₀ (norm_nonneg _) (by positivity),
      Complex.sq_norm, Complex.normSq_apply, div_pow, one_pow, sq_abs]
    simp only [Complex.sub_re, Complex.sub_im]
    field_simp
    linear_combination (-x) * hzx

theorem isPorous_cayley_im (y : ℝ) : IsPorous (cayleyPre {w | w.im = y}) := by
  by_cases hy : y = -1
  · refine IsPorous.mono (isPorous_line 1 I) ?_
    rintro z ⟨hz, hzy⟩
    simp only [mem_setOf_eq, cay_im, hy] at hzy
    have hn := Complex.normSq_pos.2 (cay_one_sub_ne_zero hz)
    rw [div_eq_iff hn.ne', Complex.normSq_apply, Complex.normSq_apply] at hzy
    simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im] at hzy
    have hre : z.re = 1 := by nlinarith
    exact ⟨z.im, Complex.ext (by simp [hre]) (by simp)⟩
  · have hy' : 1 + y ≠ 0 := fun h ↦ hy (by linarith)
    refine IsPorous.mono (isPorous_sphere (⟨y / (1 + y), 0⟩ : ℂ) (1 / |1 + y|)) ?_
    rintro z ⟨hz, hzy⟩
    simp only [mem_setOf_eq, cay_im] at hzy
    have hn := Complex.normSq_pos.2 (cay_one_sub_ne_zero hz)
    rw [div_eq_iff hn.ne', Complex.normSq_apply, Complex.normSq_apply] at hzy
    simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im] at hzy
    rw [mem_sphere, Complex.dist_eq, ← sq_eq_sq₀ (norm_nonneg _) (by positivity),
      Complex.sq_norm, Complex.normSq_apply, div_pow, one_pow, sq_abs]
    simp only [Complex.sub_re, Complex.sub_im]
    field_simp
    linear_combination (-(1 + y)) * hzy

/-! ### Geometry of `τ(c, v) = |c - v| / |c - v̄|` in the upper half-plane -/

theorem cay_sq_norm_sub (c v : ℂ) : ‖c - v‖ ^ 2 = (c.re - v.re) ^ 2 + (c.im - v.im) ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; simp only [Complex.sub_re, Complex.sub_im]; ring

theorem cay_sq_norm_sub_conj (c v : ℂ) :
    ‖c - conj v‖ ^ 2 = (c.re - v.re) ^ 2 + (c.im + v.im) ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im]; ring

theorem cay_norm_sub_conj_self (c : ℂ) : ‖c - conj c‖ = 2 * |c.im| := by
  rw [Complex.sub_conj, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_mul, abs_two]

theorem cay_norm_sub_conj_le (c v : ℂ) : ‖c - conj v‖ ≤ ‖c - v‖ + 2 * |c.im| := by
  have h1 : ‖c - conj v‖ = ‖conj c - v‖ := by
    rw [← Complex.norm_conj (c - conj v), map_sub, Complex.conj_conj]
  have h2 : conj c - v = (c - v) - (c - conj c) := by ring
  rw [h1, h2, ← cay_norm_sub_conj_self]
  exact norm_sub_le _ _

theorem cay_two_im_sub_le (c v : ℂ) : 2 * c.im - ‖c - v‖ ≤ ‖c - conj v‖ := by
  have h1 : ‖v - conj c‖ = ‖c - conj v‖ := by
    rw [← Complex.norm_conj (v - conj c), map_sub, Complex.conj_conj, norm_sub_rev]
  have h2 : c - conj c = (c - v) + (v - conj c) := by ring
  have h3 := norm_add_le (c - v) (v - conj c)
  rw [← h2, cay_norm_sub_conj_self, h1] at h3
  linarith [le_abs_self c.im]

/-- `τ(c, v) < t` forces `v` into a Euclidean ball around `c`. -/
theorem cay_norm_lt_of_tau_lt {c v : ℂ} (hc : 0 < c.im) {t : ℝ} (ht : t < 1)
    (h : ‖c - v‖ < t * ‖c - conj v‖) : ‖v - c‖ < 2 * t * c.im / (1 - t) := by
  have h1 := cay_norm_sub_conj_le c v
  rw [abs_of_pos hc] at h1
  have ht0 : 0 < t := by
    by_contra h0
    push_neg at h0
    have := mul_nonpos_of_nonpos_of_nonneg h0 (norm_nonneg (c - conj v))
    linarith [norm_nonneg (c - v)]
  rw [norm_sub_rev, lt_div_iff₀ (by linarith)]
  nlinarith

/-- A small Euclidean ball around `c` lies in `{τ(c, ·) < t}`. -/
theorem cay_tau_lt_of_norm_lt {c v : ℂ} {t : ℝ} (ht : 0 < t)
    (h : ‖v - c‖ < t * (2 * c.im - ‖v - c‖)) : ‖c - v‖ < t * ‖c - conj v‖ := by
  have h1 := cay_two_im_sub_le c v
  rw [norm_sub_rev] at h
  exact h.trans_le (mul_le_mul_of_nonneg_left h1 ht.le)

/-- `τ(c, v) < t` controls the heights. -/
theorem cay_im_bound {c v : ℂ} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hc : 0 < c.im)
    (hv : 0 < v.im) (h : ‖c - v‖ < t * ‖c - conj v‖) : |v.im - c.im| < t * (v.im + c.im) := by
  have hsq : ‖c - v‖ ^ 2 < (t * ‖c - conj v‖) ^ 2 :=
    pow_lt_pow_left₀ h (norm_nonneg _) two_ne_zero
  rw [mul_pow, cay_sq_norm_sub, cay_sq_norm_sub_conj] at hsq
  apply abs_lt_of_sq_lt_sq _ (by positivity)
  have ht2 : t ^ 2 ≤ 1 := by nlinarith
  nlinarith [sq_nonneg (c.re - v.re)]

theorem cay_hypDist_lt_iff {c : ℂ} (hc : 0 < c.im) {z : ℂ} (hz : z ∈ 𝔻) (β : ℝ) :
    hypDist (cayleyInv c) z < β ↔ ‖c - cayley z‖ < Real.tanh β * ‖c - conj (cayley z)‖ := by
  have hv := cayley_im_pos hz
  have hpos : 0 < ‖c - conj (cayley z)‖ := by
    apply norm_pos_iff.2
    intro h
    have := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.conj_im, Complex.zero_im] at this
    linarith
  have e : hypDist (cayleyInv c) z = hypDist (cayleyInv c) (cayleyInv (cayley z)) := by
    rw [cayleyInv_cayley hz]
  rw [e, hypDist_lt_iff (cayleyInv_mem hc) (cayleyInv_mem hv), pseudoHyp_cayleyInv hc hv,
    div_lt_iff₀ hpos]

theorem cay_artanh_le {t : ℝ} (h0 : 0 ≤ t) (h1 : t < 1) : Real.artanh t ≤ t / (1 - t) := by
  rw [Real.artanh_eq_half_log ⟨by linarith, h1.le⟩]
  have hx : 0 < (1 + t) / (1 - t) := by apply div_pos <;> linarith
  have := Real.log_le_sub_one_of_pos hx
  have e : (1 + t) / (1 - t) - 1 = 2 * (t / (1 - t)) := by field_simp; ring
  linarith

theorem cay_le_artanh {t : ℝ} (h0 : 0 ≤ t) (h1 : t < 1) : t / (1 + t) ≤ Real.artanh t := by
  rw [Real.artanh_eq_half_log ⟨by linarith, h1.le⟩]
  have hx : 0 < (1 + t) / (1 - t) := by apply div_pos <;> linarith
  have := Real.one_sub_inv_le_log_of_pos hx
  have e : 1 - ((1 + t) / (1 - t))⁻¹ = 2 * (t / (1 + t)) := by
    rw [inv_div]; field_simp; ring
  linarith

theorem cay_map_apply (μ : Measure ℂ) {S : Set ℂ} (hS : MeasurableSet S) :
    (μ.restrict 𝔻).map cayley S = μ (cayleyPre S) := by
  rw [Measure.map_apply measurable_cayley hS, Measure.restrict_apply (measurable_cayley hS)]
  congr 1
  ext z
  simp only [mem_inter_iff, mem_preimage, cayleyPre, mem_setOf_eq]
  exact and_comm

theorem cay_ball_subset_midThird {x₁ x₂ y₁ y₂ : ℝ} :
    ball (⟨(x₁ + x₂) / 2, (y₁ + y₂) / 2⟩ : ℂ) (min (x₂ - x₁) (y₂ - y₁) / 6) ⊆
      midThird x₁ x₂ y₁ y₂ := by
  intro z hz
  obtain ⟨hre, him⟩ := rect_abs_lt_of_mem_ball hz
  have hmw := min_le_left (x₂ - x₁) (y₂ - y₁)
  have hml := min_le_right (x₂ - x₁) (y₂ - y₁)
  rw [abs_lt] at hre him
  unfold midThird
  split_ifs <;> refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> linarith

/-- Uniform Euclidean doubling of `cayley_*(μ|𝔻)` (M05 §3.7). -/
theorem cay_euclid_doubling (Cd : ℝ≥0) :
    ∃ C_E : ℝ, 0 < C_E ∧ ∀ μ : Measure ℂ,
      (∀ z ∈ 𝔻, ∀ r : ℝ, 0 < r → 2 * r < 1 → μ (hypBall z (2 * r)) ≤ Cd * μ (hypBall z r)) →
      ∀ w : ℂ, 0 < w.im → ∀ r : ℝ, 0 < r → r ≤ w.im / 16 →
        (μ.restrict 𝔻).map cayley (ball w (4 * r)) ≤
          ENNReal.ofReal C_E * (μ.restrict 𝔻).map cayley (ball w (r / 2)) := by
  set C' : ℝ≥0 := max Cd 1 with hC'
  refine ⟨(C' : ℝ) ^ 4, by positivity, fun μ hd w hw r hr hrw ↦ ?_⟩
  set y := w.im with hy
  have hden : 0 < 2 * y - 4 * r := by linarith
  have hden8 : 0 < 2 * y - 8 * r := by linarith
  set tO := 4 * r / (2 * y - 4 * r) with htO
  have htO0 : 0 < tO := by positivity
  have htO1 : tO ≤ 1 / 7 := by rw [htO, div_le_iff₀ hden]; linarith
  set βo := Real.artanh tO with hβo
  have hβo0 : 0 < βo := Real.artanh_pos ⟨htO0, by linarith⟩
  have htanh : Real.tanh βo = tO := Real.tanh_artanh ⟨by linarith, by linarith⟩
  have hβo_le : βo ≤ tO / (1 - tO) := cay_artanh_le htO0.le (by linarith)
  have hβo_small : βo < 1 / 2 := by
    have : tO / (1 - tO) ≤ 1 / 6 := by rw [div_le_iff₀ (by linarith)]; linarith
    linarith
  set βi := βo / 16 with hβi
  set ti := r / (4 * y + r) with hti
  have hti0 : 0 < ti := by positivity
  have hti1 : ti < 1 := by rw [hti, div_lt_one (by positivity)]; linarith
  have hβi_le : βi ≤ Real.artanh ti := by
    have e1 : tO / (1 - tO) = 4 * r / (2 * y - 8 * r) := by
      rw [htO]; field_simp; ring
    have e2 : ti / (1 + ti) = r / (4 * y + 2 * r) := by
      rw [hti]; field_simp; ring
    calc βi ≤ tO / (1 - tO) / 16 := by rw [hβi]; gcongr
      _ = 4 * r / (2 * y - 8 * r) / 16 := by rw [e1]
      _ ≤ r / (4 * y + 2 * r) := by
          rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
      _ = ti / (1 + ti) := e2.symm
      _ ≤ Real.artanh ti := cay_le_artanh hti0.le hti1
  have htanhi : Real.tanh βi ≤ ti := by
    rw [← Real.artanh_le_artanh_iff ⟨Real.neg_one_lt_tanh _, Real.tanh_lt_one _⟩
      ⟨by linarith, hti1⟩, Real.artanh_tanh]
    exact hβi_le
  set p := cayleyInv w with hp
  have hpD : p ∈ 𝔻 := cayleyInv_mem hw
  rw [cay_map_apply μ measurableSet_ball, cay_map_apply μ measurableSet_ball]
  have hout : cayleyPre (ball w (4 * r)) ⊆ hypBall p βo := by
    rintro z ⟨hz, hzb⟩
    refine ⟨hz, (cay_hypDist_lt_iff hw hz βo).2 ?_⟩
    rw [htanh]
    apply cay_tau_lt_of_norm_lt htO0
    rw [mem_ball, Complex.dist_eq] at hzb
    have e : tO * (2 * y - 4 * r) = 4 * r := by rw [htO]; field_simp
    have h4 : 0 ≤ tO * (4 * r - ‖cayley z - w‖) := mul_nonneg htO0.le (by linarith)
    nlinarith
  have hin : hypBall p βi ⊆ cayleyPre (ball w (r / 2)) := by
    rintro z ⟨hz, hzd⟩
    refine ⟨hz, ?_⟩
    have h1 := (cay_hypDist_lt_iff hw hz βi).1 hzd
    have h2 : ‖w - cayley z‖ < ti * ‖w - conj (cayley z)‖ :=
      h1.trans_le (mul_le_mul_of_nonneg_right htanhi (norm_nonneg _))
    have h3 := cay_norm_lt_of_tau_lt hw hti1 h2
    rw [mem_ball, Complex.dist_eq]
    calc ‖cayley z - w‖ < 2 * ti * w.im / (1 - ti) := h3
      _ = r / 2 := by rw [hti, ← hy]; field_simp; ring
  have hdC : ∀ ρ, 0 < ρ → 2 * ρ < 1 → μ (hypBall p (2 * ρ)) ≤ C' * μ (hypBall p ρ) :=
    fun ρ h1 h2 ↦ (hd p hpD ρ h1 h2).trans
      (by gcongr; exact le_max_left _ _)
  have hβi0 : 0 < βi := by positivity
  calc μ (cayleyPre (ball w (4 * r))) ≤ μ (hypBall p βo) := measure_mono hout
    _ = μ (hypBall p (2 * (2 * (2 * (2 * βi))))) := by congr 2; rw [hβi]; ring
    _ ≤ C' * μ (hypBall p (2 * (2 * (2 * βi)))) := hdC _ (by positivity) (by linarith)
    _ ≤ C' * (C' * μ (hypBall p (2 * (2 * βi)))) := by
        gcongr; exact hdC _ (by positivity) (by linarith)
    _ ≤ C' * (C' * (C' * μ (hypBall p (2 * βi)))) := by
        gcongr; exact hdC _ (by positivity) (by linarith)
    _ ≤ C' * (C' * (C' * (C' * μ (hypBall p βi)))) := by
        gcongr; exact hdC _ (by positivity) (by linarith)
    _ ≤ C' * (C' * (C' * (C' * μ (cayleyPre (ball w (r / 2)))))) := by
        gcongr
    _ = ENNReal.ofReal ((C' : ℝ) ^ 4) * μ (cayleyPre (ball w (r / 2))) := by
        rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_coe_nnreal]; ring

/-- Inner/outer hyperbolic balls of an admissible box (`l ≤ Λ y₁`, side ratio `≤ L`). -/
theorem discBox_inner_outer (Λ L : ℝ) (hΛ : 0 < Λ) (hL : 1 ≤ L) :
    ∃ A D : ℝ, 1 ≤ A ∧ 0 < D ∧ ∀ x₁ x₂ y₁ y₂ : ℝ, IsRectLE L x₁ x₂ y₁ y₂ → 0 < y₁ →
      y₂ - y₁ ≤ Λ * y₁ → ∃ p ∈ 𝔻, ∃ β : ℝ, 0 < β ∧ A * β ≤ D ∧
        hypBall p β ⊆ cayleyPre (midThird x₁ x₂ y₁ y₂) ∧
        discBox x₁ x₂ y₁ y₂ ⊆ hypBall p (A * β) := sorry

/-- Euclidean doubling of the push-forward `cayley_* (μ|𝔻)` below the scale `Im w / 16`. -/
theorem euclid_doubling_cayley {μ : Measure ℂ} (hd : IsLocallyDoublingDisc μ) :
    ∃ C_E : ℝ, 0 < C_E ∧ ∀ w : ℂ, 0 < w.im → ∀ r : ℝ, 0 < r → r ≤ w.im / 16 →
      (μ.restrict 𝔻).map cayley (ball w (4 * r)) ≤
        ENNReal.ofReal C_E * (μ.restrict 𝔻).map cayley (ball w (r / 2)) := by
  obtain ⟨Cd, hCd⟩ := hd
  obtain ⟨C_E, hC_E, h⟩ := cay_euclid_doubling Cd
  exact ⟨C_E, hC_E, h μ hCd⟩

/-! ### Helpers consumed by `Lemma4.lean` (M05 §3.7–3.8) -/

/-- Masses of the push-forward `cayley_* (μ|𝔻)` are masses of `cayleyPre`. -/
theorem map_restrict_cayley_apply (μ : Measure ℂ) {S : Set ℂ} (hS : MeasurableSet S) :
    (μ.restrict 𝔻).map cayley S = μ (cayleyPre S) := cay_map_apply μ hS

/-- Uniform form of `euclid_doubling_cayley`: `C_E` depends only on the doubling constant `Cd`
(the hypothesis is `IsLocallyDoublingDiscWith μ Cd`, unfolded). -/
theorem euclid_doubling_cayley_quant (Cd : ℝ≥0) :
    ∃ C_E : ℝ, 0 < C_E ∧ ∀ μ : Measure ℂ,
      (∀ z ∈ 𝔻, ∀ r : ℝ, 0 < r → 2 * r < 1 → μ (hypBall z (2 * r)) ≤ Cd * μ (hypBall z r)) →
      ∀ w : ℂ, 0 < w.im → ∀ r : ℝ, 0 < r → r ≤ w.im / 16 →
        (μ.restrict 𝔻).map cayley (ball w (4 * r)) ≤
          ENNReal.ofReal C_E * (μ.restrict 𝔻).map cayley (ball w (r / 2)) :=
  cay_euclid_doubling Cd

/-- Coarse rows (M05 §3.7): with `Λc = 64 e^{4R}`, every box
`[a, a + (Λc - 1) y₁) × [y₁, Λc y₁)` contains a hyperbolic ball of radius `R`. -/
theorem exists_hypBall_subset_discBox_row {R : ℝ} (hR : 0 < R) {y₁ : ℝ} (hy : 0 < y₁) (a : ℝ) :
    ∃ p ∈ 𝔻, hypBall p R ⊆
      discBox a (a + (64 * Real.exp (4 * R) - 1) * y₁) y₁ (64 * Real.exp (4 * R) * y₁) := sorry

/-- A horocyclic box with `0 < y₁` lies in a compact subset of `𝔻`. -/
theorem exists_isCompact_discBox_subset (x₁ x₂ : ℝ) {y₁ : ℝ} (hy : 0 < y₁) (y₂ : ℝ) :
    ∃ K : Set ℂ, IsCompact K ∧ K ⊆ 𝔻 ∧ discBox x₁ x₂ y₁ y₂ ⊆ K := sorry

end OC
