import OrtegaCerdaMultipliers.Doubling.Plane
import OrtegaCerdaMultipliers.Foundations.HyperbolicExtra

/-!
# M03 (Doubling) — The disc with the hyperbolic metric

See `blueprint/M03_Doubling.md` §2.3.  Scaffold: statements, proofs `sorry`; definitions and data
are real.  The metric-space instance on `HDisc` is fully proved (its topology is definitionally
the subspace topology), from the M01 lemmas `hypDist_self`, `hypDist_comm`, `hypDist_triangle`,
`hypDist_eq_zero_iff`, `hypBall_subset_ball`, `isOpen_hypBall`.
-/

open MeasureTheory Metric Set Complex
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace OC

/-- The unit disc as a type, to be equipped with the hyperbolic distance `hypDist`. -/
def HDisc : Type := {z : ℂ // z ∈ 𝔻}

namespace HDisc

instance : TopologicalSpace HDisc := inferInstanceAs (TopologicalSpace {z : ℂ // z ∈ 𝔻})

/-- Hyperbolic distance and the subspace topology are compatible. -/
theorem isOpen_iff_hypDist (s : Set HDisc) :
    IsOpen s ↔ ∀ x ∈ s, ∃ ε > 0, ∀ y : HDisc, hypDist x.1 y.1 < ε → y ∈ s := by
  constructor
  · intro hs x hx
    obtain ⟨U, hU, hUs⟩ := isOpen_induced_iff.1 hs
    have hxU : x.1 ∈ U := by rw [← hUs] at hx; exact hx
    obtain ⟨δ, hδ, hδU⟩ := Metric.isOpen_iff.1 hU x.1 hxU
    have hε : 0 < min 1 (δ / 18) := lt_min one_pos (by positivity)
    refine ⟨min 1 (δ / 18), hε, fun y hy ↦ ?_⟩
    have hy' : y.1 ∈ hypBall x.1 (min 1 (δ / 18)) := ⟨y.2, hy⟩
    have hyb := hypBall_subset_ball x.2 hε (min_le_left _ _) hy'
    have hx1 : ‖x.1‖ < 1 := mem_ball_zero_iff.1 x.2
    have hle : 18 * min 1 (δ / 18) * (1 - ‖x.1‖) ≤ δ := by
      have h1 : 0 ≤ 1 - ‖x.1‖ := by linarith
      have h2 : 1 - ‖x.1‖ ≤ 1 := by linarith [norm_nonneg x.1]
      calc 18 * min 1 (δ / 18) * (1 - ‖x.1‖) ≤ 18 * (δ / 18) * 1 := by
            gcongr
            exact min_le_right _ _
        _ = δ := by ring
    have hyU : y.1 ∈ U := hδU (Metric.ball_subset_ball hle hyb)
    rw [← hUs]
    exact hyU
  · intro h
    refine isOpen_iff_mem_nhds.2 fun x hx ↦ ?_
    obtain ⟨ε, hε, hεs⟩ := h x hx
    exact mem_nhds_iff.2 ⟨{y : HDisc | y.1 ∈ hypBall x.1 ε},
      fun y hy ↦ hεs y (mem_hypBall.1 hy).2,
      isOpen_induced_iff.2 ⟨hypBall x.1 ε, isOpen_hypBall x.1 ε, rfl⟩, self_mem_hypBall x.2 hε⟩

/-- The hyperbolic metric on `HDisc`; its topology is (definitionally) the subspace topology. -/
instance : MetricSpace HDisc :=
  MetricSpace.ofDistTopology (fun a b : HDisc ↦ hypDist a.1 b.1)
    (fun a ↦ hypDist_self a.1) (fun a b ↦ hypDist_comm a.1 b.1)
    (fun a b c ↦ hypDist_triangle a.2 b.2 c.2) isOpen_iff_hypDist
    (fun a b h ↦ Subtype.ext ((hypDist_eq_zero_iff a.2 b.2).1 h))

instance : MeasurableSpace HDisc := inferInstanceAs (MeasurableSpace {z : ℂ // z ∈ 𝔻})
instance : BorelSpace HDisc := inferInstanceAs (BorelSpace {z : ℂ // z ∈ 𝔻})
instance : SecondCountableTopology HDisc :=
  inferInstanceAs (SecondCountableTopology {z : ℂ // z ∈ 𝔻})

/-- The point of `ℂ`. -/
def val (z : HDisc) : ℂ := Subtype.val z

/-- A point of `𝔻` as a point of `HDisc`. -/
def mk (z : ℂ) (hz : z ∈ 𝔻) : HDisc := ⟨z, hz⟩

theorem dist_eq (a b : HDisc) : dist a b = hypDist a.val b.val := rfl

theorem val_mem (a : HDisc) : a.val ∈ 𝔻 := a.2

theorem measurableEmbedding_val : MeasurableEmbedding val := sorry

theorem image_ball (a : HDisc) (r : ℝ) : val '' ball a r = hypBall a.val r := sorry

instance : BallGeometry HDisc := sorry

instance : TopologicalSpace.SeparableSpace HDisc := inferInstance

end HDisc

/-- The pull-back of `μ` to `HDisc`. -/
def discPull (μ : Measure ℂ) : Measure HDisc := μ.comap HDisc.val

theorem discPull_apply (μ : Measure ℂ) (s : Set HDisc) : discPull μ s = μ (HDisc.val '' s) :=
  sorry

theorem discPull_ball (μ : Measure ℂ) (a : HDisc) (r : ℝ) :
    discPull μ (ball a r) = μ (hypBall a.val r) := sorry

theorem isLocallyDoublingDisc_iff (μ : Measure ℂ) :
    IsLocallyDoublingDisc μ ↔ IsLocDoublingM (discPull μ) := sorry

theorem massRadiusDisc_eq (μ : Measure ℂ) (a : HDisc) :
    massRadiusDisc μ a.val = massRadiusM (discPull μ) a := sorry

/-- Euclidean porosity implies hyperbolic porosity. -/
theorem IsPorous.preimage_hDisc {E : Set ℂ} (hE : IsPorous E) :
    IsPorous (HDisc.val ⁻¹' E) := sorry

end OC
