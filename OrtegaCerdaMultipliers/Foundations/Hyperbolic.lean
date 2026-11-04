import OrtegaCerdaMultipliers.Foundations.DiscGeometry

/-!
# M01 (Foundations) — The hyperbolic distance `β = artanh ρ` on `𝔻`

See `blueprint/M01_Foundations.md`, §3.  New material, not copied from BOC.

For the hyperbolic distance `hypDist z w = artanh (pseudoHyp z w)` and the hyperbolic disc
`hypBall z r = {w ∈ 𝔻 | hypDist z w < r}` of `OrtegaCerdaMultipliers/Defs.lean`:

* `pseudoHyp` takes values in `[0, 1)` on `𝔻 × 𝔻` and satisfies the *strong* triangle inequality
  `ρ(u, w) ≤ (ρ(u, v) + ρ(v, w)) / (1 + ρ(u, v) ρ(v, w))` (`pseudoHyp_triangle_strong`);
* `tanh (a + b) = (tanh a + tanh b) / (1 + tanh a tanh b)` (`tanh_add`), hence
  `artanh x + artanh y = artanh ((x + y) / (1 + x y))` (`artanh_add_artanh`);
* `hypDist` is a metric on `𝔻` (`hypDist_nonneg`, `hypDist_comm`, `hypDist_self`,
  `hypDist_eq_zero_iff`, `hypDist_triangle`), invariant under the Möbius maps (`hypDist_mobius`);
* `hypDist z w < r ↔ pseudoHyp z w < tanh r` (`hypDist_lt_iff`);
* `hypBall z r` is open (`isOpen_hypBall`), contained in `𝔻`, equal to the image of the Euclidean
  disc `ball 0 (tanh r)` under `mobius z` (`hypBall_eq_image_mobius`), and is the Euclidean disc
  with explicit centre and radius (`hypBall_eq_ball`);
* for `0 < r ≤ 1`, `ball z (r (1 - |z|) / 10) ⊆ hypBall z r ⊆ ball z (18 r (1 - |z|))`
  (`ball_subset_hypBall`, `hypBall_subset_ball`).
-/

open Metric Set Complex
open scoped ComplexConjugate Topology

noncomputable section

namespace OC

/-! ### `tanh` and `artanh` addition formulas -/

/-- The addition formula `tanh (a + b) = (tanh a + tanh b) / (1 + tanh a tanh b)`. -/
theorem tanh_add (a b : ℝ) :
    Real.tanh (a + b) = (Real.tanh a + Real.tanh b) / (1 + Real.tanh a * Real.tanh b) := by
  have ha := Real.cosh_pos a
  have hb := Real.cosh_pos b
  have hab : 0 < Real.cosh a * Real.cosh b + Real.sinh a * Real.sinh b := by
    rw [← Real.cosh_add]; exact Real.cosh_pos _
  rw [Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh,
    Real.sinh_add, Real.cosh_add]
  field_simp

/-- `tanh r = (e^{2r} - 1) / (e^{2r} + 1)`. -/
theorem tanh_eq_exp_two_mul (r : ℝ) :
    Real.tanh r = (Real.exp (2 * r) - 1) / (Real.exp (2 * r) + 1) := by
  have h1 : Real.exp (2 * r) = Real.exp r * Real.exp r := by
    rw [← Real.exp_add]; ring_nf
  have h2 : Real.exp r * Real.exp (-r) = 1 := by
    rw [← Real.exp_add]; simp
  have hp := Real.exp_pos r
  have hn := Real.exp_pos (-r)
  rw [Real.tanh_eq, h1, div_eq_div_iff (by positivity) (by positivity)]
  nlinarith [h2]

theorem tanh_nonneg_of_nonneg {r : ℝ} (hr : 0 ≤ r) : 0 ≤ Real.tanh r := by
  rw [tanh_eq_exp_two_mul]
  have := Real.add_one_le_exp (2 * r)
  apply div_nonneg <;> linarith

/-- The addition formula `artanh x + artanh y = artanh ((x + y) / (1 + x y))` for
`x, y ∈ (-1, 1)`. -/
theorem artanh_add_artanh {x y : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) (hy : y ∈ Ioo (-1 : ℝ) 1) :
    Real.artanh x + Real.artanh y = Real.artanh ((x + y) / (1 + x * y)) := by
  have h := tanh_add (Real.artanh x) (Real.artanh y)
  rw [Real.tanh_artanh hx, Real.tanh_artanh hy] at h
  rw [← h, Real.artanh_tanh]

/-! ### The pseudo-hyperbolic distance -/

theorem pseudoHyp_mem_Ioo {z w : ℂ} (hz : z ∈ 𝔻) (hw : w ∈ 𝔻) :
    pseudoHyp z w ∈ Ioo (-1 : ℝ) 1 :=
  ⟨by linarith [pseudoHyp_nonneg z w], pseudoHyp_lt_one hz hw⟩

theorem pseudoHyp_eq_zero_iff {z w : ℂ} (hz : z ∈ 𝔻) (hw : w ∈ 𝔻) :
    pseudoHyp z w = 0 ↔ z = w := by
  rw [pseudoHyp, div_eq_zero_iff, norm_eq_zero, norm_eq_zero, sub_eq_zero, sub_eq_zero]
  refine ⟨fun h ↦ h.resolve_right fun h' ↦ ?_, Or.inl⟩
  exact one_sub_conj_mul_ne_zero_of_mem hz hw (sub_eq_zero.2 h')

/-- The sharp form of the bound `ρ(p, q) ≤ |p| + |q|` of `pseudoHyp_le_norm_add_norm`:
`ρ(p, q) ≤ (|p| + |q|) / (1 + |p| |q|)`.  The proof is the one of BOC's
`pseudoHyp_le_norm_add_norm`, stopped before the final (lossy) step. -/
theorem pseudoHyp_le_norm_add_norm_div {p q : ℂ} (hp : p ∈ 𝔻) (hq : q ∈ 𝔻) :
    pseudoHyp p q ≤ (‖p‖ + ‖q‖) / (1 + ‖p‖ * ‖q‖) := by
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
  have hD2 : D ^ 2 ≤ (1 + x * y) ^ 2 := pow_le_pow_left₀ hD.le hDle 2
  have hle : (1 - x ^ 2) * (1 - y ^ 2) / (1 + x * y) ^ 2 ≤ (1 - x ^ 2) * (1 - y ^ 2) / D ^ 2 :=
    div_le_div_of_nonneg_left hnum (by positivity) hD2
  have hxy : 0 < 1 + x * y := by positivity
  have hid : 1 - (1 - x ^ 2) * (1 - y ^ 2) / (1 + x * y) ^ 2 = ((x + y) / (1 + x * y)) ^ 2 := by
    field_simp
    ring
  have h1 : pseudoHyp p q ^ 2 ≤ ((x + y) / (1 + x * y)) ^ 2 := by
    rw [pseudoHyp_eq_norm_mobius]
    linarith
  exact (pow_le_pow_iff_left₀ (pseudoHyp_nonneg p q) (by positivity) two_ne_zero).1 h1

/-- The strong triangle inequality
`ρ(u, w) ≤ (ρ(u, v) + ρ(v, w)) / (1 + ρ(u, v) ρ(v, w))` on `𝔻`. -/
theorem pseudoHyp_triangle_strong {u v w : ℂ} (hu : u ∈ 𝔻) (hv : v ∈ 𝔻) (hw : w ∈ 𝔻) :
    pseudoHyp u w ≤ (pseudoHyp u v + pseudoHyp v w) / (1 + pseudoHyp u v * pseudoHyp v w) := by
  have e1 : pseudoHyp u w = pseudoHyp (mobius v u) (mobius v w) :=
    (pseudoHyp_mobius hv hu hw).symm
  have e2 : pseudoHyp u v = ‖mobius v u‖ := by
    rw [← pseudoHyp_mobius hv hu hv, mobius_self, pseudoHyp_zero_right]
  have e3 : pseudoHyp v w = ‖mobius v w‖ := by
    rw [← pseudoHyp_mobius hv hv hw, mobius_self, pseudoHyp_zero_left]
  rw [e1, e2, e3]
  exact pseudoHyp_le_norm_add_norm_div (mobius_mem_disc hv hu) (mobius_mem_disc hv hw)

/-- `(a + b) / (1 + a b) < 1` for `a, b ∈ [0, 1)`. -/
theorem add_div_one_add_mul_lt_one {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (hb0 : 0 ≤ b)
    (hb1 : b < 1) : (a + b) / (1 + a * b) < 1 := by
  rw [div_lt_one (by positivity)]
  nlinarith [mul_pos (sub_pos.2 ha1) (sub_pos.2 hb1)]

/-! ### The hyperbolic distance -/

theorem hypDist_nonneg (z w : ℂ) : 0 ≤ hypDist z w :=
  Real.artanh_nonneg (pseudoHyp_nonneg z w)

theorem hypDist_comm (z w : ℂ) : hypDist z w = hypDist w z := by
  rw [hypDist, hypDist, pseudoHyp_comm]

@[simp]
theorem hypDist_self (z : ℂ) : hypDist z z = 0 := by
  rw [hypDist, pseudoHyp_self, Real.artanh_zero]

theorem hypDist_zero_left (w : ℂ) : hypDist 0 w = Real.artanh ‖w‖ := by
  rw [hypDist, pseudoHyp_zero_left]

theorem hypDist_eq_zero_iff {z w : ℂ} (hz : z ∈ 𝔻) (hw : w ∈ 𝔻) : hypDist z w = 0 ↔ z = w := by
  have h := pseudoHyp_mem_Ioo hz hw
  rw [hypDist, Real.artanh_eq_zero_iff, pseudoHyp_eq_zero_iff hz hw]
  constructor
  · rintro (h1 | h1 | h1)
    · linarith [h.1]
    · exact h1
    · linarith [h.2]
  · exact fun h1 ↦ Or.inr (Or.inl h1)

theorem tanh_hypDist {z w : ℂ} (hz : z ∈ 𝔻) (hw : w ∈ 𝔻) :
    Real.tanh (hypDist z w) = pseudoHyp z w :=
  Real.tanh_artanh (pseudoHyp_mem_Ioo hz hw)

/-- `β(z, w) < r ↔ ρ(z, w) < tanh r` (any `r`; for `r ≤ 0` both sides are false). -/
theorem hypDist_lt_iff {z w : ℂ} (hz : z ∈ 𝔻) (hw : w ∈ 𝔻) (r : ℝ) :
    hypDist z w < r ↔ pseudoHyp z w < Real.tanh r := by
  rw [hypDist, ← Real.artanh_lt_artanh_iff (pseudoHyp_mem_Ioo hz hw)
    ⟨Real.neg_one_lt_tanh r, Real.tanh_lt_one r⟩, Real.artanh_tanh]

theorem hypDist_le_iff {z w : ℂ} (hz : z ∈ 𝔻) (hw : w ∈ 𝔻) (r : ℝ) :
    hypDist z w ≤ r ↔ pseudoHyp z w ≤ Real.tanh r := by
  rw [hypDist, ← Real.artanh_le_artanh_iff (pseudoHyp_mem_Ioo hz hw)
    ⟨Real.neg_one_lt_tanh r, Real.tanh_lt_one r⟩, Real.artanh_tanh]

/-- The triangle inequality for the hyperbolic distance on `𝔻`. -/
theorem hypDist_triangle {u v w : ℂ} (hu : u ∈ 𝔻) (hv : v ∈ 𝔻) (hw : w ∈ 𝔻) :
    hypDist u w ≤ hypDist u v + hypDist v w := by
  have h1 := pseudoHyp_mem_Ioo hu hv
  have h2 := pseudoHyp_mem_Ioo hv hw
  have h3 := pseudoHyp_mem_Ioo hu hw
  rw [hypDist, hypDist, hypDist, artanh_add_artanh h1 h2]
  exact Real.artanh_le_artanh h3.1
    (add_div_one_add_mul_lt_one (pseudoHyp_nonneg u v) h1.2 (pseudoHyp_nonneg v w) h2.2)
    (pseudoHyp_triangle_strong hu hv hw)

/-- Möbius invariance of the hyperbolic distance. -/
theorem hypDist_mobius {a z w : ℂ} (ha : a ∈ 𝔻) (hz : z ∈ 𝔻) (hw : w ∈ 𝔻) :
    hypDist (mobius a z) (mobius a w) = hypDist z w := by
  rw [hypDist, hypDist, pseudoHyp_mobius ha hz hw]

/-- Outside `𝔻` the junk values of `artanh` make `hypDist z w = 0` for every `w ∈ 𝔻`. -/
theorem hypDist_eq_zero_of_notMem {z w : ℂ} (hz : z ∉ 𝔻) (hw : w ∈ 𝔻) : hypDist z w = 0 := by
  rw [hypDist, Real.artanh_eq_zero_iff]
  right
  by_cases hD : 1 - conj z * w = 0
  · left
    simp [pseudoHyp, hD]
  · right
    have hz1 : 1 ≤ ‖z‖ := by simpa using hz
    have hw1 := norm_lt_one_of_mem_disc hw
    have key := norm_one_sub_conj_mul_sq_sub z w
    have hDpos : 0 < ‖1 - conj z * w‖ := norm_pos_iff.2 hD
    have hneg : (1 - ‖z‖ ^ 2) * (1 - ‖w‖ ^ 2) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by nlinarith) (by nlinarith [norm_nonneg w])
    rw [pseudoHyp, le_div_iff₀ hDpos, one_mul]
    nlinarith [norm_nonneg (z - w)]

/-! ### Hyperbolic discs -/

theorem mem_hypBall {z w : ℂ} {r : ℝ} : w ∈ hypBall z r ↔ w ∈ 𝔻 ∧ hypDist z w < r :=
  Iff.rfl

theorem hypBall_subset_disc (z : ℂ) (r : ℝ) : hypBall z r ⊆ 𝔻 :=
  fun _ hw ↦ hw.1

/-- For `z ∈ 𝔻`, the hyperbolic disc of radius `r` is the pseudo-hyperbolic disc of radius
`tanh r`. -/
theorem hypBall_eq_pseudoBall {z : ℂ} (hz : z ∈ 𝔻) (r : ℝ) :
    hypBall z r = {w ∈ 𝔻 | pseudoHyp z w < Real.tanh r} := by
  ext w
  constructor
  · rintro ⟨hw, h⟩
    exact ⟨hw, (hypDist_lt_iff hz hw r).1 h⟩
  · rintro ⟨hw, h⟩
    exact ⟨hw, (hypDist_lt_iff hz hw r).2 h⟩

theorem continuousOn_pseudoHyp {z : ℂ} (hz : z ∈ 𝔻) : ContinuousOn (pseudoHyp z) 𝔻 := by
  have h : ContinuousOn (fun w ↦ ‖z - w‖ / ‖1 - conj z * w‖) 𝔻 :=
    ContinuousOn.div (by fun_prop) (by fun_prop)
      fun w hw ↦ (norm_one_sub_conj_mul_pos hz hw).ne'
  exact h

theorem isOpen_hypBall (z : ℂ) (r : ℝ) : IsOpen (hypBall z r) := by
  by_cases hz : z ∈ 𝔻
  · rw [hypBall_eq_pseudoBall hz]
    exact (continuousOn_pseudoHyp hz).isOpen_inter_preimage isOpen_ball isOpen_Iio
  · have e : hypBall z r = 𝔻 ∩ {_w | 0 < r} := by
      ext w
      constructor
      · rintro ⟨hw, h⟩
        exact ⟨hw, by rwa [hypDist_eq_zero_of_notMem hz hw] at h⟩
      · rintro ⟨hw, h⟩
        exact ⟨hw, by rwa [hypDist_eq_zero_of_notMem hz hw]⟩
    rw [e]
    exact isOpen_ball.inter isOpen_const

theorem self_mem_hypBall {z : ℂ} (hz : z ∈ 𝔻) {r : ℝ} (hr : 0 < r) : z ∈ hypBall z r :=
  ⟨hz, by rwa [hypDist_self]⟩

/-- For `z ∈ 𝔻`, `hypBall z r` is the image of the Euclidean disc `ball 0 (tanh r)` under the
involution `mobius z`. -/
theorem hypBall_eq_image_mobius {z : ℂ} (hz : z ∈ 𝔻) (r : ℝ) :
    hypBall z r = mobius z '' ball 0 (Real.tanh r) := by
  rw [hypBall_eq_pseudoBall hz]
  ext w
  constructor
  · rintro ⟨hw, h⟩
    refine ⟨mobius z w, ?_, mobius_mobius hz hw⟩
    rw [mem_ball_zero_iff, ← pseudoHyp_eq_norm_mobius]
    exact h
  · rintro ⟨u, hu, rfl⟩
    rw [mem_ball_zero_iff] at hu
    have hu' : u ∈ 𝔻 := mem_disc_iff_norm_lt_one.2 (hu.trans (Real.tanh_lt_one r))
    refine ⟨mobius_mem_disc hz hu', ?_⟩
    rw [pseudoHyp_eq_norm_mobius, mobius_mobius hz hu']
    exact hu

/-! ### Euclidean description of hyperbolic discs -/

/-- The key identity behind the Euclidean description of pseudo-hyperbolic discs:
with `A = 1 - t² |z|²`, `c = (1 - t²) z / A` and `R = t (1 - |z|²) / A`,
`|w - z|² - t² |1 - z̄ w|² = A (|w - c|² - R²)`. -/
theorem norm_sub_sq_sub_sq_mul_norm_one_sub_sq (z w : ℂ) (t : ℝ)
    (hA : 1 - t ^ 2 * ‖z‖ ^ 2 ≠ 0) :
    ‖w - z‖ ^ 2 - t ^ 2 * ‖1 - conj z * w‖ ^ 2 =
      (1 - t ^ 2 * ‖z‖ ^ 2) *
        (‖w - (((1 - t ^ 2) / (1 - t ^ 2 * ‖z‖ ^ 2) : ℝ) : ℂ) * z‖ ^ 2 -
          (t * (1 - ‖z‖ ^ 2) / (1 - t ^ 2 * ‖z‖ ^ 2)) ^ 2) := by
  have hz2 : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  rw [hz2] at hA ⊢
  simp only [Complex.sq_norm, Complex.normSq_apply, sub_re, sub_im, mul_re, mul_im, conj_re,
    conj_im, one_re, one_im, ofReal_re, ofReal_im]
  field_simp
  ring

/-- For `z ∈ 𝔻` and `0 ≤ t < 1`, the pseudo-hyperbolic disc `{w ∈ 𝔻 : ρ(z, w) < t}` is the
Euclidean disc with centre `(1 - t²) z / (1 - t² |z|²)` and radius
`t (1 - |z|²) / (1 - t² |z|²)`. -/
theorem pseudoBall_eq_ball {z : ℂ} (hz : z ∈ 𝔻) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    {w ∈ 𝔻 | pseudoHyp z w < t} =
      ball ((((1 - t ^ 2) / (1 - t ^ 2 * ‖z‖ ^ 2) : ℝ) : ℂ) * z)
        (t * (1 - ‖z‖ ^ 2) / (1 - t ^ 2 * ‖z‖ ^ 2)) := by
  have hz1 := norm_lt_one_of_mem_disc hz
  have hz0 := norm_nonneg z
  have hA : 0 < 1 - t ^ 2 * ‖z‖ ^ 2 := by
    have : t ^ 2 * ‖z‖ ^ 2 < 1 := by
      have h1 : t ^ 2 < 1 := by nlinarith
      have h2 : ‖z‖ ^ 2 < 1 := by nlinarith
      calc t ^ 2 * ‖z‖ ^ 2 ≤ 1 * ‖z‖ ^ 2 := by gcongr
        _ < 1 := by linarith
    linarith
  set c : ℂ := (((1 - t ^ 2) / (1 - t ^ 2 * ‖z‖ ^ 2) : ℝ) : ℂ) * z
  set R : ℝ := t * (1 - ‖z‖ ^ 2) / (1 - t ^ 2 * ‖z‖ ^ 2)
  have hR0 : 0 ≤ R := by
    have := one_sub_normSq_pos hz
    positivity
  have key := fun w ↦ norm_sub_sq_sub_sq_mul_norm_one_sub_sq z w t hA.ne'
  -- membership in the pseudo-hyperbolic disc, for `w ∈ 𝔻`
  have hiff : ∀ w ∈ 𝔻, pseudoHyp z w < t ↔ ‖w - c‖ < R := by
    intro w hw
    have hD := norm_one_sub_conj_mul_pos hz hw
    rw [pseudoHyp, div_lt_iff₀ hD, norm_sub_rev, ← sq_lt_sq₀ (norm_nonneg _) (by positivity),
      ← sq_lt_sq₀ (norm_nonneg _) hR0, mul_pow, ← sub_neg, key w, ← sub_neg (b := R ^ 2)]
    constructor
    · intro h
      by_contra h'
      exact absurd h (not_lt.2 (mul_nonneg hA.le (not_lt.1 h')))
    · intro h
      exact mul_neg_of_pos_of_neg hA h
  -- the Euclidean disc lies in `𝔻`: `|c| + R < 1`
  have hsub : ball c R ⊆ 𝔻 := by
    intro w hw
    rw [mem_ball, dist_eq_norm] at hw
    have hc : ‖c‖ = (1 - t ^ 2) / (1 - t ^ 2 * ‖z‖ ^ 2) * ‖z‖ := by
      rw [norm_mul, Complex.norm_of_nonneg (by
        have : 0 ≤ 1 - t ^ 2 := by nlinarith
        positivity)]
    have hcR : ‖c‖ + R < 1 := by
      rw [hc, div_mul_eq_mul_div, ← add_div, div_lt_one hA]
      have htz : t * ‖z‖ < 1 := by nlinarith
      nlinarith [mul_pos (mul_pos (sub_pos.2 ht1) (sub_pos.2 hz1)) (sub_pos.2 htz)]
    rw [mem_disc_iff_norm_lt_one]
    calc ‖w‖ = ‖c + (w - c)‖ := by ring_nf
      _ ≤ ‖c‖ + ‖w - c‖ := norm_add_le _ _
      _ < ‖c‖ + R := by linarith
      _ < 1 := hcR
  ext w
  constructor
  · rintro ⟨hw, h⟩
    rw [mem_ball, dist_eq_norm]
    exact (hiff w hw).1 h
  · intro hw
    have hw𝔻 := hsub hw
    rw [mem_ball, dist_eq_norm] at hw
    exact ⟨hw𝔻, (hiff w hw𝔻).2 hw⟩

/-- For `z ∈ 𝔻`, `hypBall z r` (`r ≥ 0`) is the Euclidean disc with centre
`(1 - t²) z / (1 - t² |z|²)` and radius `t (1 - |z|²) / (1 - t² |z|²)`, where `t = tanh r`. -/
theorem hypBall_eq_ball {z : ℂ} (hz : z ∈ 𝔻) {r : ℝ} (hr : 0 ≤ r) :
    hypBall z r =
      ball ((((1 - Real.tanh r ^ 2) / (1 - Real.tanh r ^ 2 * ‖z‖ ^ 2) : ℝ) : ℂ) * z)
        (Real.tanh r * (1 - ‖z‖ ^ 2) / (1 - Real.tanh r ^ 2 * ‖z‖ ^ 2)) := by
  rw [hypBall_eq_pseudoBall hz,
    pseudoBall_eq_ball hz (tanh_nonneg_of_nonneg hr) (Real.tanh_lt_one r)]

/-! ### Euclidean size of hyperbolic discs -/

theorem exp_two_mul_lt_nine {r : ℝ} (hr1 : r ≤ 1) : Real.exp (2 * r) < 9 := by
  have h3 := Real.exp_one_lt_three
  have h : Real.exp (2 * r) ≤ Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith)
  have := Real.exp_pos 1
  nlinarith

/-- `r / 5 ≤ tanh r` for `0 ≤ r ≤ 1`. -/
theorem div_five_le_tanh {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) : r / 5 ≤ Real.tanh r := by
  have hE := exp_two_mul_lt_nine hr1
  have hE1 := Real.add_one_le_exp (2 * r)
  have hEpos := Real.exp_pos (2 * r)
  rw [tanh_eq_exp_two_mul, le_div_iff₀ (by positivity)]
  nlinarith

/-- `tanh r / (1 - tanh r) ≤ 9 r` for `0 ≤ r ≤ 1`. -/
theorem tanh_div_one_sub_tanh_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    Real.tanh r / (1 - Real.tanh r) ≤ 9 * r := by
  have hE := exp_two_mul_lt_nine hr1
  have hEpos := Real.exp_pos (2 * r)
  -- `e^{2r} - 1 ≤ 2r e^{2r}`, from `1 - 2r ≤ e^{-2r}`
  have hE2 : Real.exp (2 * r) - 1 ≤ 2 * r * Real.exp (2 * r) := by
    have h := Real.add_one_le_exp (-(2 * r))
    have hm : Real.exp (-(2 * r)) * Real.exp (2 * r) = 1 := by
      rw [← Real.exp_add]; simp
    nlinarith
  have h1 : 1 - Real.tanh r = 2 / (Real.exp (2 * r) + 1) := by
    rw [tanh_eq_exp_two_mul]
    field_simp
    ring
  have h2 : Real.tanh r / (1 - Real.tanh r) = (Real.exp (2 * r) - 1) / 2 := by
    rw [h1, tanh_eq_exp_two_mul]
    field_simp
  rw [h2]
  nlinarith

/-- The Euclidean size of hyperbolic discs, upper bound: for `z ∈ 𝔻` and `0 < r ≤ 1`,
`hypBall z r ⊆ ball z (18 r (1 - |z|))`. -/
theorem hypBall_subset_ball {z : ℂ} (hz : z ∈ 𝔻) {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    hypBall z r ⊆ ball z (18 * r * (1 - ‖z‖)) := by
  have hs1 := Real.tanh_lt_one r
  have hz1 := norm_lt_one_of_mem_disc hz
  have hz0 := norm_nonneg z
  rw [hypBall_eq_pseudoBall hz]
  refine (pseudoBall_subset_ball hz hs1).trans (ball_subset_ball ?_)
  have h := tanh_div_one_sub_tanh_le hr0.le hr1
  have e : Real.tanh r * (1 - ‖z‖ ^ 2) / (1 - Real.tanh r) =
      Real.tanh r / (1 - Real.tanh r) * ((1 + ‖z‖) * (1 - ‖z‖)) := by
    ring
  rw [e]
  calc Real.tanh r / (1 - Real.tanh r) * ((1 + ‖z‖) * (1 - ‖z‖))
      ≤ 9 * r * (2 * (1 - ‖z‖)) := by
        apply mul_le_mul h _ (by nlinarith) (by positivity)
        nlinarith
    _ = 18 * r * (1 - ‖z‖) := by ring

/-- The Euclidean size of hyperbolic discs, lower bound: for `z ∈ 𝔻` and `0 < r ≤ 1`,
`ball z (r (1 - |z|) / 10) ⊆ hypBall z r`. -/
theorem ball_subset_hypBall {z : ℂ} (hz : z ∈ 𝔻) {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    ball z (r * (1 - ‖z‖) / 10) ⊆ hypBall z r := by
  have h5 := div_five_le_tanh hr0.le hr1
  have hs0 : 0 < Real.tanh r := lt_of_lt_of_le (by linarith) h5
  have hs1 := Real.tanh_lt_one r
  have hz1 := norm_lt_one_of_mem_disc hz
  have hz0 := norm_nonneg z
  rw [hypBall_eq_pseudoBall hz]
  refine (ball_subset_ball ?_).trans (ball_subset_pseudoBall hz hs0 hs1)
  have h1 : 1 - ‖z‖ ≤ 1 - ‖z‖ ^ 2 := by nlinarith
  calc r * (1 - ‖z‖) / 10 = r / 5 * (1 - ‖z‖) / 2 := by ring
    _ ≤ Real.tanh r * (1 - ‖z‖ ^ 2) / 2 := by gcongr

end OC
