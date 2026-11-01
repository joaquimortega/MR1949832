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

theorem hypDist_radial {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t < 1) {u : ℂ} (hu : ‖u‖ = 1) :
    hypDist (s * u) (t * u) = Real.artanh t - Real.artanh s := sorry

theorem hypBall_zero {r : ℝ} (hr : 0 < r) : hypBall 0 r = ball 0 (Real.tanh r) := sorry

theorem continuousOn_hypDist : ContinuousOn (fun p : ℂ × ℂ ↦ hypDist p.1 p.2) (𝔻 ×ˢ 𝔻) := sorry

/-! ## Euclidean size of hyperbolic discs, `tanh` form -/

theorem ball_subset_hypBall_tanh {z : ℂ} (hz : z ∈ 𝔻) {r : ℝ} (hr : 0 < r) :
    ball z (Real.tanh r * (1 - ‖z‖ ^ 2) / 2) ⊆ hypBall z r := sorry

theorem hypBall_subset_ball_tanh {z : ℂ} (hz : z ∈ 𝔻) {r : ℝ} (hr : 0 < r) :
    hypBall z r ⊆ ball z (Real.tanh r * (1 - ‖z‖ ^ 2) / (1 - Real.tanh r)) := sorry

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
