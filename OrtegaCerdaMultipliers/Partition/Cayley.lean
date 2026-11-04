import OrtegaCerdaMultipliers.Partition.Rectangles

/-!
# M05 (Partition) — Cayley coordinates and horocyclic boxes in `𝔻`

See `blueprint/M05_Partition.md` §2.2.  Proofs complete (they use the upstream M01/M03 interfaces).
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
    simp only [mem_ofPred_eq, cay_re, hx] at hzx
    have hn := Complex.normSq_pos.2 (cay_one_sub_ne_zero hz)
    rw [div_eq_zero_iff] at hzx
    have him : z.im = 0 := by
      rcases hzx with h | h
      · linarith
      · exact absurd h hn.ne'
    exact ⟨z.re, Complex.ext (by simp) (by simp [him])⟩
  · refine IsPorous.mono (isPorous_sphere (⟨1, -1 / x⟩ : ℂ) (1 / |x|)) ?_
    rintro z ⟨hz, hzx⟩
    simp only [mem_ofPred_eq, cay_re] at hzx
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
    simp only [mem_ofPred_eq, cay_im, hy] at hzy
    have hn := Complex.normSq_pos.2 (cay_one_sub_ne_zero hz)
    rw [div_eq_iff hn.ne', Complex.normSq_apply, Complex.normSq_apply] at hzy
    simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im] at hzy
    have hre : z.re = 1 := by nlinarith
    exact ⟨z.im, Complex.ext (by simp [hre]) (by simp)⟩
  · have hy' : 1 + y ≠ 0 := fun h ↦ hy (by linarith)
    refine IsPorous.mono (isPorous_sphere (⟨y / (1 + y), 0⟩ : ℂ) (1 / |1 + y|)) ?_
    rintro z ⟨hz, hzy⟩
    simp only [mem_ofPred_eq, cay_im] at hzy
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
    push Not at h0
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
  simp only [mem_inter_iff, mem_preimage, cayleyPre, mem_ofPred_eq]
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

theorem cay_ratio_arith {P Q K y : ℝ} (hy : 0 < y) (hP : 0 ≤ P) (hQ : 0 < Q) (hK : 0 < K)
    (hQsq : Q ^ 2 ≤ K * y ^ 2) (hdiff : 4 * y ^ 2 ≤ Q ^ 2 - P ^ 2) :
    P < Q ∧ 2 / K ≤ 1 - P / Q := by
  have hy2 : 0 < y ^ 2 := by positivity
  have hsq : P ^ 2 < Q ^ 2 := by linarith
  have hPQ : P < Q := lt_of_pow_lt_pow_left₀ 2 hQ.le hsq
  refine ⟨hPQ, ?_⟩
  have e1 : 1 - P / Q = (Q - P) / Q := by field_simp
  rw [e1, div_le_div_iff₀ hK hQ]
  have e2 : 4 * y ^ 2 ≤ (Q - P) * (2 * Q) := by nlinarith
  have e3 : (Q - P) * Q ^ 2 ≤ (Q - P) * (K * y ^ 2) :=
    mul_le_mul_of_nonneg_left hQsq (by linarith)
  have e4 : 2 * y ^ 2 * Q ≤ (Q - P) * Q ^ 2 := by nlinarith
  by_contra hcon
  push Not at hcon
  nlinarith

theorem cay_outer_arith {τ M K y₁ m L Λ A₀ β : ℝ} (hy₁ : 0 < y₁) (hK : 0 < K) (hτ0 : 0 ≤ τ)
    (hτ1 : τ < 1) (hτM : τ ≤ M / (2 * y₁)) (h1τ : 2 / K ≤ 1 - τ) (hMm : M ≤ L * m)
    (hm0 : 0 < m) (hL : 1 ≤ L) (hΛ : 0 < Λ) (hA₀ : A₀ = L * K * (12 + 8 * Λ) / 4)
    (hβlow : m / ((12 + 8 * Λ) * y₁) ≤ β) (hβ0 : 0 < β) :
    Real.artanh τ < (2 * A₀ + 1) * β := by
  have hM0 : 0 ≤ M := by
    have := hτ0.trans hτM
    rwa [le_div_iff₀ (by positivity), zero_mul] at this
  have hA₀0 : 0 < A₀ := by rw [hA₀]; positivity
  calc Real.artanh τ ≤ τ / (1 - τ) := cay_artanh_le hτ0 hτ1
    _ ≤ (M / (2 * y₁)) / (2 / K) := div_le_div₀ (by positivity) hτM (by positivity) h1τ
    _ = M * K / (4 * y₁) := by field_simp; ring
    _ ≤ L * m * K / (4 * y₁) := by gcongr
    _ = A₀ * (m / ((12 + 8 * Λ) * y₁)) := by rw [hA₀]; field_simp
    _ ≤ A₀ * β := by gcongr
    _ < (2 * A₀ + 1) * β := by
        have := mul_pos (by linarith : (0 : ℝ) < A₀ + 1) hβ0
        linarith

/-- Inner/outer hyperbolic balls of an admissible box (`l ≤ Λ y₁`, side ratio `≤ L`). -/
theorem discBox_inner_outer (Λ L : ℝ) (hΛ : 0 < Λ) (hL : 1 ≤ L) :
    ∃ A D : ℝ, 1 ≤ A ∧ 0 < D ∧ ∀ x₁ x₂ y₁ y₂ : ℝ, IsRectLE L x₁ x₂ y₁ y₂ → 0 < y₁ →
      y₂ - y₁ ≤ Λ * y₁ → ∃ p ∈ 𝔻, ∃ β : ℝ, 0 < β ∧ A * β ≤ D ∧
        hypBall p β ⊆ cayleyPre (midThird x₁ x₂ y₁ y₂) ∧
        discBox x₁ x₂ y₁ y₂ ⊆ hypBall p (A * β) := by
  set K : ℝ := (L * Λ / 2) ^ 2 + (2 + 3 * Λ / 2) ^ 2 with hK
  have hK0 : 0 < K := by positivity
  set A₀ : ℝ := L * K * (12 + 8 * Λ) / 4 with hA₀
  have hA₀0 : 0 < A₀ := by positivity
  refine ⟨2 * A₀ + 1, (2 * A₀ + 1) * Λ / 12, by linarith, by positivity,
    fun x₁ x₂ y₁ y₂ hR hy₁ hl ↦ ?_⟩
  obtain ⟨hx, hy, hwL, hlL⟩ := hR
  have hw0 : 0 < x₂ - x₁ := sub_pos.2 hx
  have hl0 : 0 < y₂ - y₁ := sub_pos.2 hy
  set m := min (x₂ - x₁) (y₂ - y₁) with hm
  have hm0 : 0 < m := lt_min hw0 hl0
  have hmw : m ≤ x₂ - x₁ := min_le_left _ _
  have hml : m ≤ y₂ - y₁ := min_le_right _ _
  set M := max (x₂ - x₁) (y₂ - y₁) with hMdef
  have hMm : M ≤ L * m := by
    rcases le_total (x₂ - x₁) (y₂ - y₁) with h | h
    · rw [hMdef, max_eq_right h, hm, min_eq_left h]; exact hlL
    · rw [hMdef, max_eq_left h, hm, min_eq_right h]; exact hwL
  set yc := (y₁ + y₂) / 2 with hyc
  set c : ℂ := ⟨(x₁ + x₂) / 2, yc⟩ with hc_def
  have hc : 0 < c.im := by simp only [hc_def]; linarith
  have hcim : c.im = yc := rfl
  have hyc0 : 0 < yc := by rw [hyc]; linarith
  have hden : 12 * yc + m ≠ 0 := by positivity
  set t₁ := m / (12 * yc + m) with ht₁
  have ht₁0 : 0 < t₁ := by positivity
  have h1t : 1 - t₁ = 12 * yc / (12 * yc + m) := by rw [ht₁]; field_simp; ring
  have ht₁1 : t₁ < 1 := by rw [ht₁, div_lt_one (by positivity)]; linarith
  set β := Real.artanh t₁ with hβ
  have hβ0 : 0 < β := Real.artanh_pos ⟨ht₁0, ht₁1⟩
  have htanh : Real.tanh β = t₁ := Real.tanh_artanh ⟨by linarith, ht₁1⟩
  refine ⟨cayleyInv c, cayleyInv_mem hc, β, hβ0, ?_, ?_, ?_⟩
  · -- `A β ≤ D`
    have h1 : β ≤ t₁ / (1 - t₁) := cay_artanh_le ht₁0.le ht₁1
    have h2 : t₁ / (1 - t₁) = m / (12 * yc) := by
      rw [h1t, ht₁, div_div_div_cancel_right₀ hden]
    have h3 : m / (12 * yc) ≤ Λ / 12 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    calc (2 * A₀ + 1) * β ≤ (2 * A₀ + 1) * (Λ / 12) := by gcongr; linarith
      _ = (2 * A₀ + 1) * Λ / 12 := by ring
  · -- inner ball
    rintro z ⟨hz, hzd⟩
    refine ⟨hz, cay_ball_subset_midThird ?_⟩
    have h1 := (cay_hypDist_lt_iff hc hz β).1 hzd
    rw [htanh] at h1
    have h2 := cay_norm_lt_of_tau_lt hc ht₁1 h1
    rw [mem_ball, Complex.dist_eq]
    calc ‖cayley z - c‖ < 2 * t₁ * c.im / (1 - t₁) := h2
      _ = m / 6 := by
          rw [hcim, h1t, ht₁]; field_simp; ring
  · -- outer ball
    rintro z ⟨hz, hzQ⟩
    refine ⟨hz, ?_⟩
    have hv : 0 < (cayley z).im := cayley_im_pos hz
    obtain ⟨⟨hv1, hv2⟩, ⟨hv3, hv4⟩⟩ := hzQ
    set v := cayley z with hv_def
    set P := ‖c - v‖ with hP_def
    set Q := ‖c - conj v‖ with hQ_def
    have hP0 : 0 ≤ P := norm_nonneg _
    have hPM : P ≤ M := by
      have h0 := Complex.norm_le_abs_re_add_abs_im (c - v)
      simp only [Complex.sub_re, Complex.sub_im] at h0
      have : |c.re - v.re| ≤ (x₂ - x₁) / 2 := by
        rw [abs_le]; simp only [hc_def]; constructor <;> linarith
      have : |c.im - v.im| ≤ (y₂ - y₁) / 2 := by
        rw [abs_le, hcim]; constructor <;> linarith
      linarith [le_max_left (x₂ - x₁) (y₂ - y₁), le_max_right (x₂ - x₁) (y₂ - y₁)]
    have hQ2 : 2 * y₁ ≤ Q := by
      have h0 := Complex.abs_im_le_norm (c - conj v)
      simp only [Complex.sub_im, Complex.conj_im, sub_neg_eq_add] at h0
      have : c.im + v.im = |c.im + v.im| := (abs_of_pos (by linarith)).symm
      linarith
    have hQ0 : 0 < Q := by linarith
    have hsqP := cay_sq_norm_sub c v
    have hsqQ := cay_sq_norm_sub_conj c v
    have hQsq : Q ^ 2 ≤ K * y₁ ^ 2 := by
      rw [hsqQ]
      have hre : |c.re - v.re| ≤ L * Λ * y₁ / 2 := by
        have : |c.re - v.re| ≤ (x₂ - x₁) / 2 := by
          rw [abs_le]; simp only [hc_def]; constructor <;> linarith
        have : x₂ - x₁ ≤ L * Λ * y₁ := by nlinarith
        linarith
      have him0 : 0 ≤ c.im + v.im := by linarith
      have him : c.im + v.im ≤ (2 + 3 * Λ / 2) * y₁ := by rw [hcim]; linarith
      have e1 : (c.re - v.re) ^ 2 ≤ (L * Λ * y₁ / 2) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hre 2
      have e2 : (c.im + v.im) ^ 2 ≤ ((2 + 3 * Λ / 2) * y₁) ^ 2 :=
        pow_le_pow_left₀ him0 him 2
      calc (c.re - v.re) ^ 2 + (c.im + v.im) ^ 2
          ≤ (L * Λ * y₁ / 2) ^ 2 + ((2 + 3 * Λ / 2) * y₁) ^ 2 := add_le_add e1 e2
        _ = K * y₁ ^ 2 := by rw [hK]; ring
    have hdiff : 4 * y₁ ^ 2 ≤ Q ^ 2 - P ^ 2 := by
      rw [hsqP, hsqQ, hcim]
      have e : (c.re - v.re) ^ 2 + (yc + v.im) ^ 2 - ((c.re - v.re) ^ 2 + (yc - v.im) ^ 2) =
          4 * (yc * v.im) := by ring
      rw [e]
      have hyc1 : y₁ ≤ yc := by rw [hyc]; linarith
      have h1 : y₁ * y₁ ≤ yc * v.im := mul_le_mul hyc1 hv3 hy₁.le hyc0.le
      rw [sq]; linarith
    obtain ⟨hPQ, h1τ'⟩ := cay_ratio_arith hy₁ hP0 hQ0 hK0 hQsq hdiff
    set τ := P / Q with hτ
    have hτ0 : 0 ≤ τ := by positivity
    have hτ1 : τ < 1 := by rw [hτ, div_lt_one hQ0]; exact hPQ
    have h1τ : 2 / K ≤ 1 - τ := h1τ'
    have hτM : τ ≤ M / (2 * y₁) := by
      rw [hτ]
      calc P / Q ≤ M / Q := by gcongr
        _ ≤ M / (2 * y₁) := by
            apply div_le_div_of_nonneg_left (by linarith [hPM, hP0]) (by positivity) hQ2
    have hd : hypDist (cayleyInv c) z = Real.artanh τ := by
      have e : z = cayleyInv v := (cayleyInv_cayley hz).symm
      rw [e, hypDist, pseudoHyp_cayleyInv hc (by rw [hv_def]; exact hv)]
    rw [hd]
    have hβlow : m / ((12 + 8 * Λ) * y₁) ≤ β := by
      have h1 := cay_le_artanh ht₁0.le ht₁1
      have h2 : t₁ / (1 + t₁) = m / (12 * yc + 2 * m) := by
        have h1p : 1 + t₁ = (12 * yc + 2 * m) / (12 * yc + m) := by
          rw [ht₁]; field_simp; ring
        rw [h1p, ht₁, div_div_div_cancel_right₀ hden]
      have h3 : 12 * yc + 2 * m ≤ (12 + 8 * Λ) * y₁ := by
        have e : (12 + 8 * Λ) * y₁ = 12 * y₁ + 8 * (Λ * y₁) := by ring
        rw [hyc, e]; linarith
      calc m / ((12 + 8 * Λ) * y₁) ≤ m / (12 * yc + 2 * m) :=
            div_le_div_of_nonneg_left hm0.le (by positivity) h3
        _ = t₁ / (1 + t₁) := h2.symm
        _ ≤ β := h1
    exact cay_outer_arith hy₁ hK0 hτ0 hτ1 hτM h1τ hMm hm0 hL hΛ hA₀ hβlow hβ0

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
      discBox a (a + (64 * Real.exp (4 * R) - 1) * y₁) y₁ (64 * Real.exp (4 * R) * y₁) := by
  set u := Real.exp (2 * R) with hu
  have hu1 : 1 < u := by rw [hu]; exact Real.one_lt_exp_iff.2 (by positivity)
  have he4 : Real.exp (4 * R) = u ^ 2 := by
    rw [hu, sq, ← Real.exp_add]; ring_nf
  rw [he4]
  set yc := 8 * u * y₁ with hyc
  set h := (64 * u ^ 2 - 1) * y₁ with hh
  set c : ℂ := ⟨a + h / 2, yc⟩ with hc_def
  have hc : 0 < c.im := by simp only [hc_def]; positivity
  set t := Real.tanh R with ht
  have htu : t = (u - 1) / (u + 1) := by rw [ht, hu]; exact tanh_eq_exp_two_mul R
  have ht0 : 0 ≤ t := by rw [htu]; apply div_nonneg <;> linarith
  have ht1 : t < 1 := Real.tanh_lt_one R
  refine ⟨cayleyInv c, cayleyInv_mem hc, fun z hz ↦ ⟨hz.1, ?_⟩⟩
  obtain ⟨hzD, hzd⟩ := hz
  have h1 := (cay_hypDist_lt_iff hc hzD R).1 hzd
  rw [← ht] at h1
  set v := cayley z with hv_def
  have hv : 0 < v.im := cayley_im_pos hzD
  have hvert := cay_im_bound ht0 ht1.le hc hv h1
  have hhor := cay_norm_lt_of_tau_lt hc ht1 h1
  rw [abs_lt] at hvert
  have hcim : c.im = yc := rfl
  rw [hcim] at hvert hhor
  have hre := (Complex.abs_re_le_norm (v - c)).trans_lt hhor
  simp only [Complex.sub_re, hc_def] at hre
  rw [abs_lt] at hre
  -- `2t/(1-t) = u - 1` and `(1+t)/(1-t) = u`
  have hk : 2 * t * yc / (1 - t) = (u - 1) * yc := by
    rw [htu]; field_simp; ring
  rw [hk] at hre
  have hvim1 : v.im * (1 - t) < yc * (1 + t) := by linarith
  have hvim2 : yc * (1 - t) < v.im * (1 + t) := by linarith
  rw [htu] at hvim1 hvim2
  have hu0 : 0 < u + 1 := by linarith
  have hv1 : v.im < u * yc := by
    have : v.im * 2 < yc * (2 * u) := by
      have := hvim1; field_simp at this; nlinarith
    nlinarith
  have hv2 : yc < u * v.im := by
    have : yc * 2 < v.im * (2 * u) := by
      have := hvim2; field_simp at this; nlinarith
    nlinarith
  have hy₁yc : y₁ ≤ v.im := by
    by_contra hcon
    push Not at hcon
    have : u * v.im < u * y₁ := by nlinarith
    rw [hyc] at hv2
    nlinarith
  refine ⟨⟨?_, ?_⟩, ⟨hy₁yc, ?_⟩⟩
  · have : (u - 1) * yc < h / 2 := by rw [hh, hyc]; nlinarith
    linarith
  · have : (u - 1) * yc < h / 2 := by rw [hh, hyc]; nlinarith
    linarith
  · rw [hyc] at hv1; nlinarith

/-- A horocyclic box with `0 < y₁` lies in a compact subset of `𝔻`. -/
theorem exists_isCompact_discBox_subset (x₁ x₂ : ℝ) {y₁ : ℝ} (hy : 0 < y₁) (y₂ : ℝ) :
    ∃ K : Set ℂ, IsCompact K ∧ K ⊆ 𝔻 ∧ discBox x₁ x₂ y₁ y₂ ⊆ K := by
  set K₀ : Set ℂ := {w | w.re ∈ Icc x₁ x₂ ∧ w.im ∈ Icc y₁ y₂} with hK₀
  have hK₀c : IsCompact K₀ := by
    refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
    · exact (isClosed_Icc.preimage Complex.continuous_re).inter
        (isClosed_Icc.preimage Complex.continuous_im)
    · refine (Metric.isBounded_closedBall (x := (0 : ℂ))
        (r := |x₁| + |x₂| + |y₁| + |y₂|)).subset fun w hw ↦ ?_
      rw [mem_closedBall_zero_iff]
      have h0 := Complex.norm_le_abs_re_add_abs_im w
      have : |w.re| ≤ |x₁| + |x₂| := by
        rw [abs_le]; constructor <;>
          linarith [hw.1.1, hw.1.2, neg_abs_le x₁, le_abs_self x₂, abs_nonneg x₁, abs_nonneg x₂]
      have : |w.im| ≤ |y₁| + |y₂| := by
        rw [abs_le]; constructor <;>
          linarith [hw.2.1, hw.2.2, neg_abs_le y₁, le_abs_self y₂, abs_nonneg y₁, abs_nonneg y₂]
      linarith
  have hcont : ContinuousOn cayleyInv K₀ := by
    unfold cayleyInv
    exact (continuous_id.sub continuous_const).continuousOn.div
      (continuous_id.add continuous_const).continuousOn
      fun w hw ↦ cay_add_I_ne_zero (by linarith [hw.2.1])
  refine ⟨cayleyInv '' K₀, hK₀c.image_of_continuousOn hcont, ?_, ?_⟩
  · rintro _ ⟨w, hw, rfl⟩
    exact cayleyInv_mem (by linarith [hw.2.1])
  · rintro z ⟨hz, ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩⟩
    exact ⟨cayley z, ⟨⟨h1, h2.le⟩, ⟨h3, h4.le⟩⟩, cayleyInv_cayley hz⟩

end OC
