import OrtegaCerdaMultipliers.Foundations.Hyperbolic

/-!
# M01 (Foundations) — Hyperbolic geometry: lemmas requested by later modules

See `blueprint/M01_Foundations.md`.

**Scaffold.** These are the M01-type statements that the later module docs assume but that
`Foundations/Hyperbolic.lean` does not (yet) contain.  Proofs are `sorry`; the definition
`hypArea` is real.

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
theorem hypArea_hypBall {z : ℂ} (hz : z ∈ 𝔻) {r : ℝ} (hr : 0 ≤ r) :
    hypArea (hypBall z r) = ENNReal.ofReal (Real.pi * Real.sinh r ^ 2) := sorry

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
    ‖w - c‖ ≤ Real.tanh s / (1 - Real.tanh s) * (1 - ‖c‖ ^ 2) := sorry

theorem norm_one_sub_conj_mul_comparable {z c ξ : ℂ} (hz : z ∈ 𝔻) (hc : c ∈ 𝔻) (hξ : ξ ∈ 𝔻)
    {s : ℝ} (hs : hypDist c ξ ≤ s) :
    ‖1 - conj z * ξ‖ ≤ Real.exp (2 * s) * ‖1 - conj z * c‖ ∧
      ‖1 - conj z * c‖ ≤ Real.exp (2 * s) * ‖1 - conj z * ξ‖ := sorry

theorem convex_closedHypBall {c : ℂ} (hc : c ∈ 𝔻) (s : ℝ) :
    Convex ℝ {w | w ∈ 𝔻 ∧ hypDist c w ≤ s} := sorry

end OC
