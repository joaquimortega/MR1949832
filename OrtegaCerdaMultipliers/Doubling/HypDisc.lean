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

theorem measurableEmbedding_val : MeasurableEmbedding val :=
  show MeasurableEmbedding (Subtype.val : {z : ℂ // z ∈ 𝔻} → ℂ) from
    MeasurableEmbedding.subtype_coe measurableSet_ball

theorem image_ball (a : HDisc) (r : ℝ) : val '' ball a r = hypBall a.val r := by
  ext w
  constructor
  · rintro ⟨b, hb, rfl⟩
    have hb' : hypDist b.1 a.1 < r := hb
    exact ⟨b.2, by rw [hypDist_comm]; exact hb'⟩
  · rintro ⟨hw, hlt⟩
    refine ⟨mk w hw, ?_, rfl⟩
    show hypDist w a.1 < r
    rw [hypDist_comm]
    exact hlt

theorem tanh_le_tanh_of_le {a b : ℝ} (h : a ≤ b) : Real.tanh a ≤ Real.tanh b := by
  rw [← Real.artanh_le_artanh_iff ⟨Real.neg_one_lt_tanh a, Real.tanh_lt_one a⟩
    ⟨Real.neg_one_lt_tanh b, Real.tanh_lt_one b⟩, Real.artanh_tanh, Real.artanh_tanh]
  exact h

instance : BallGeometry HDisc where
  exists_between x y s hs hsd := by
    have hx : x.1 ∈ 𝔻 := x.2
    have hy : y.1 ∈ 𝔻 := y.2
    have hd : dist x y = hypDist x.1 y.1 := rfl
    rw [hd] at hsd ⊢
    set w := mobius x.1 y.1 with hwdef
    have hw : w ∈ 𝔻 := mobius_mem_disc hx hy
    have hdw : hypDist 0 w = hypDist x.1 y.1 := by
      have := hypDist_mobius hx hx hy
      rw [mobius_self] at this
      exact this
    have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.1 hw
    set d := hypDist x.1 y.1 with hddef
    have hwd : ‖w‖ = Real.tanh d := by
      rw [← hdw, hypDist_zero_left, Real.tanh_artanh ⟨by linarith [norm_nonneg w], hw1⟩]
    by_cases hw0 : w = 0
    · have hd0 : d = 0 := by rw [← hdw, hw0, hypDist_self]
      have hs0 : s = 0 := le_antisymm (hsd.trans hd0.le) hs
      refine ⟨x, ?_, ?_⟩
      · show hypDist x.1 x.1 ≤ s
        rw [hypDist_self, hs0]
      · show hypDist x.1 y.1 ≤ d - s
        rw [hs0, sub_zero]
    · have hwn : 0 < ‖w‖ := norm_pos_iff.2 hw0
      have hwc : (‖w‖ : ℂ) ≠ 0 := by exact_mod_cast hwn.ne'
      set u : ℂ := w / (‖w‖ : ℂ) with hudef
      have hu : ‖u‖ = 1 := by
        rw [hudef, norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg w),
          div_self hwn.ne']
      have hwu : w = ((Real.tanh d : ℝ) : ℂ) * u := by
        rw [hudef, ← hwd]
        field_simp
      set a := Real.tanh s with hadef
      have ha0 : 0 ≤ a := tanh_nonneg_of_nonneg hs
      have hab : a ≤ Real.tanh d := tanh_le_tanh_of_le hsd
      have hb1 : Real.tanh d < 1 := Real.tanh_lt_one d
      set m₀ : ℂ := (a : ℂ) * u with hm₀def
      have hm₀n : ‖m₀‖ = a := by
        rw [hm₀def, norm_mul, Complex.norm_real, Real.norm_of_nonneg ha0, hu, mul_one]
      have hm₀ : m₀ ∈ 𝔻 := by
        rw [mem_ball_zero_iff, hm₀n]
        exact lt_of_le_of_lt hab hb1
      have h0m₀ : hypDist 0 m₀ = s := by
        rw [hypDist_zero_left, hm₀n, hadef, Real.artanh_tanh]
      have hm₀w : hypDist m₀ w = d - s := by
        rw [hm₀def, hwu, hypDist_radial ha0 hab hb1 hu, Real.artanh_tanh, hadef, Real.artanh_tanh]
      have hm : mobius x.1 m₀ ∈ 𝔻 := mobius_mem_disc hx hm₀
      refine ⟨mk (mobius x.1 m₀) hm, le_of_eq ?_, le_of_eq ?_⟩
      · show hypDist x.1 (mobius x.1 m₀) = s
        have := hypDist_mobius hx (mem_ball_self one_pos : (0 : ℂ) ∈ 𝔻) hm₀
        rw [mobius_zero] at this
        rw [this, h0m₀]
      · show hypDist (mobius x.1 m₀) y.1 = d - s
        have := hypDist_mobius hx hm₀ hw
        rw [hwdef, mobius_mobius hx hy] at this
        rw [this, ← hwdef, hm₀w]
  exists_far x r := by
    have hx : x.1 ∈ 𝔻 := x.2
    set t := Real.tanh (max (r + hypDist 0 x.1) 0) with htdef
    have ht0 : 0 ≤ t := tanh_nonneg_of_nonneg (le_max_right _ _)
    have htD : (t : ℂ) ∈ 𝔻 := by
      rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_of_nonneg ht0]
      exact Real.tanh_lt_one _
    refine ⟨mk t htD, ?_⟩
    show r ≤ hypDist x.1 t
    have h1 : hypDist 0 (t : ℂ) = max (r + hypDist 0 x.1) 0 := by
      rw [hypDist_zero_left, Complex.norm_real, Real.norm_of_nonneg ht0, htdef, Real.artanh_tanh]
    have h2 := hypDist_triangle (mem_ball_self one_pos : (0 : ℂ) ∈ 𝔻) hx htD
    linarith [le_max_left (r + hypDist 0 x.1) 0]
  covering R ε hε := by
    classical
    by_cases hR : R ≤ 0
    · refine ⟨0, fun x ↦ ⟨∅, by simp, ?_⟩⟩
      rw [ball_eq_empty.2 hR]
      exact empty_subset _
    rw [not_le] at hR
    have hK : IsCompact (closedBall (0 : ℂ) (Real.tanh R)) := isCompact_closedBall _ _
    have hsub : closedBall (0 : ℂ) (Real.tanh R) ⊆ ⋃ b : HDisc, hypBall b.1 ε := by
      intro z hz
      have hzD : z ∈ 𝔻 := by
        rw [mem_closedBall_zero_iff] at hz
        exact mem_ball_zero_iff.2 (hz.trans_lt (Real.tanh_lt_one R))
      exact mem_iUnion.2 ⟨mk z hzD, self_mem_hypBall hzD hε⟩
    obtain ⟨T, hT⟩ := hK.elim_finite_subcover (fun b : HDisc ↦ hypBall b.1 ε)
      (fun b ↦ isOpen_hypBall _ _) hsub
    refine ⟨T.card, fun x ↦ ?_⟩
    have hx : x.1 ∈ 𝔻 := x.2
    let φ : HDisc → HDisc := fun b ↦ mk (mobius x.1 b.1) (mobius_mem_disc hx b.2)
    refine ⟨T.image φ, Finset.card_image_le, ?_⟩
    intro z hz
    have hzD : z.1 ∈ 𝔻 := z.2
    set z' := mobius x.1 z.1 with hz'def
    have hz'D : z' ∈ 𝔻 := mobius_mem_disc hx hzD
    have hdz : hypDist 0 z' < R := by
      have h1 : hypDist z.1 x.1 < R := hz
      rw [hypDist_comm] at h1
      have := hypDist_mobius hx hx hzD
      rw [mobius_self] at this
      rw [hz'def, this]
      exact h1
    have hz'n : ‖z'‖ ≤ Real.tanh R := by
      have := (hypDist_lt_iff (mem_ball_self one_pos : (0 : ℂ) ∈ 𝔻) hz'D R).1 hdz
      rw [pseudoHyp_zero_left] at this
      exact this.le
    have hz'mem : z' ∈ closedBall (0 : ℂ) (Real.tanh R) := mem_closedBall_zero_iff.2 hz'n
    obtain ⟨b, hbT, hb⟩ := mem_iUnion₂.1 (hT hz'mem)
    refine mem_iUnion₂.2 ⟨φ b, Finset.mem_image_of_mem φ hbT, ?_⟩
    show hypDist z.1 (mobius x.1 b.1) < ε
    have hzz : mobius x.1 z' = z.1 := mobius_mobius hx hzD
    rw [← hzz, hypDist_mobius hx hz'D b.2, hypDist_comm]
    exact hb.2

instance : TopologicalSpace.SeparableSpace HDisc := inferInstance

end HDisc

/-- The pull-back of `μ` to `HDisc`. -/
def discPull (μ : Measure ℂ) : Measure HDisc := μ.comap HDisc.val

theorem discPull_apply (μ : Measure ℂ) (s : Set HDisc) : discPull μ s = μ (HDisc.val '' s) :=
  HDisc.measurableEmbedding_val.comap_apply μ s

theorem discPull_ball (μ : Measure ℂ) (a : HDisc) (r : ℝ) :
    discPull μ (ball a r) = μ (hypBall a.val r) := by
  rw [discPull_apply, HDisc.image_ball]

theorem isLocallyDoublingDisc_iff (μ : Measure ℂ) :
    IsLocallyDoublingDisc μ ↔ IsLocDoublingM (discPull μ) := by
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C, fun x r hr h2r ↦ ?_⟩
    rw [discPull_ball, discPull_ball]
    exact hC x.val x.2 r hr h2r
  · rintro ⟨C, hC⟩
    refine ⟨C, fun z hz r hr h2r ↦ ?_⟩
    have := hC (HDisc.mk z hz) r hr h2r
    rwa [discPull_ball, discPull_ball] at this

theorem massRadiusDisc_eq (μ : Measure ℂ) (a : HDisc) :
    massRadiusDisc μ a.val = massRadiusM (discPull μ) a := by
  simp only [massRadiusDisc, massRadiusM, discPull_ball]

/-- Euclidean porosity implies hyperbolic porosity. -/
theorem IsPorous.preimage_hDisc {E : Set ℂ} (hE : IsPorous E) :
    IsPorous (HDisc.val ⁻¹' E) := sorry

end OC
