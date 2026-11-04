import OrtegaCerdaMultipliers.Multiplier.Kernel
import OrtegaCerdaMultipliers.Multiplier.Cells
import OrtegaCerdaMultipliers.Multiplier.NearField

/-!
# M08 (Multiplier) — Per-cell bounds and the non-near sum (§3.4, §3.7)

See `blueprint/M08_Multiplier.md` §3.4, §3.7.  Helper file (not in the blueprint's file list),
shared by `Potential.lean` and `Estimates.lean`:

* elementary facts on cells (`R i ⊆ Ω`, boundedness, finiteness);
* integrability of the kernels on cells;
* the per-cell bounds (P), (D-near), (D-far) for non-near cells;
* the uniform bound on `Σ_{non-near} |cellPot|` (§3.7), and summability of `cellPot`.
-/

open MeasureTheory Metric Set Complex
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace OC

/-! ### Finiteness and no atoms -/

theorem MeasClassDisc.hypBall_lt_top {ν : Measure ℂ} {Cd : ℝ≥0} {R₀ : ℝ}
    (hν : MeasClassDisc ν Cd R₀) {z : ℂ} (hz : z ∈ 𝔻) (r : ℝ) : ν (hypBall z r) < ∞ :=
  (measure_mono fun _ hw ↦ closedHypBall_subset_closedBall hz r ⟨hw.1, hw.2.le⟩).trans_lt
    (hν.finite _ (closedBall_tanh_subset_disc _) (isCompact_closedBall _ _))

theorem MeasClassDisc.measure_singleton {ν : Measure ℂ} {Cd : ℝ≥0} {R₀ : ℝ}
    (hν : MeasClassDisc ν Cd R₀) {z : ℂ} (hz : z ∈ 𝔻) : ν {z} = 0 :=
  measure_singleton_disc ⟨Cd, hν.doubling⟩ (fun _ hw r ↦ hν.hypBall_lt_top hw r) hz

theorem MeasClassPlane.ball_lt_top {ν : Measure ℂ} {Cd : ℝ≥0} {R₀ : ℝ}
    (hν : MeasClassPlane ν Cd R₀) (z : ℂ) (r : ℝ) : ν (ball z r) < ∞ :=
  (measure_mono ball_subset_closedBall).trans_lt (hν.finite _ (isCompact_closedBall z r))

theorem MeasClassPlane.measure_singleton {ν : Measure ℂ} {Cd : ℝ≥0} {R₀ : ℝ}
    (hν : MeasClassPlane ν Cd R₀) (z : ℂ) : ν {z} = 0 :=
  measure_singleton_plane ⟨Cd, hν.doubling⟩ (fun w r ↦ hν.ball_lt_top w r) z

/-! ### Local finiteness of the nodes -/

theorem nodeCount_ne_zero_iff {Λ : ℕ → Multiset ℂ} {w : ℂ} (hfin : {i | w ∈ Λ i}.Finite) :
    nodeCount Λ w ≠ 0 ↔ w ∈ nodeSet Λ := by
  have hsupp : Function.support (fun i ↦ (Λ i).count w) ⊆ hfin.toFinset := by
    intro i hi; simpa [Multiset.count_ne_zero] using hi
  rw [nodeCount, finsum_eq_sum_of_support_subset _ hsupp, Ne, Finset.sum_eq_zero_iff]
  simp [nodeSet, Multiset.count_eq_zero]

theorem finite_nodeIdx_disc {ν : Measure ℂ} {Cd : ℝ≥0} {R₀ : ℝ} {N : ℕ} {η A B : ℝ}
    {R : ℕ → Set ℂ} {c : ℕ → ℂ} {m : ℕ → ℕ} {Λ : ℕ → Multiset ℂ}
    (hν : MeasClassDisc ν Cd R₀) (hη : 0 < η)
    (hC : IsCells 𝔻 hypDist (massRadiusDisc ν) ν N η A R c)
    (hN : IsNodes 𝔻 hypDist (massRadiusDisc ν) ν N B R c m Λ) {K : Set ℂ} (hK𝔻 : K ⊆ 𝔻)
    (hK : IsCompact K) : {i | ∃ w ∈ Λ i, w ∈ K}.Finite := by
  obtain ⟨C1, -, h1⟩ := claim1_disc_quant Cd R₀ 0
  refine (finite_cells_disc hν hη hC K hK𝔻 hK (|B| * R₀ + 1)).subset ?_
  rintro i ⟨w, hwΛ, hwK⟩
  have hci := hC.center_mem' i
  obtain ⟨hpos, hle, -⟩ := h1 ν hν (c i) hci (c i) hci
  refine ⟨w, hwK, ?_⟩
  rw [hypDist_comm]
  calc hypDist (c i) w ≤ B * massRadiusDisc ν (c i) := hN.near i w hwΛ
    _ ≤ |B| * massRadiusDisc ν (c i) := mul_le_mul_of_nonneg_right (le_abs_self B) hpos.le
    _ ≤ |B| * R₀ := mul_le_mul_of_nonneg_left hle (abs_nonneg B)
    _ < |B| * R₀ + 1 := lt_add_one _

theorem finite_nodeIdx_plane {ν : Measure ℂ} {Cd : ℝ≥0} {R₀ : ℝ} {N : ℕ} {η A B : ℝ}
    {R : ℕ → Set ℂ} {c : ℕ → ℂ} {m : ℕ → ℕ} {Λ : ℕ → Multiset ℂ}
    (hν : MeasClassPlane ν Cd R₀) (hη : 0 < η)
    (hC : IsCells univ dist (massRadius ν) ν N η A R c)
    (hN : IsNodes univ dist (massRadius ν) ν N B R c m Λ) {K : Set ℂ}
    (hK : Bornology.IsBounded K) : {i | ∃ w ∈ Λ i, w ∈ K}.Finite := by
  obtain ⟨C1, -, h1⟩ := claim1_plane_quant Cd R₀ 0
  refine (finite_cells_plane hν hη hC K hK (|B| * R₀ + 1)).subset ?_
  rintro i ⟨w, hwΛ, hwK⟩
  obtain ⟨hpos, hle, -⟩ := h1 ν hν (c i) (c i)
  refine ⟨w, hwK, ?_⟩
  rw [dist_comm]
  calc dist (c i) w ≤ B * massRadius ν (c i) := hN.near i w hwΛ
    _ ≤ |B| * massRadius ν (c i) := mul_le_mul_of_nonneg_right (le_abs_self B) hpos.le
    _ ≤ |B| * R₀ := mul_le_mul_of_nonneg_left hle (abs_nonneg B)
    _ < |B| * R₀ + 1 := lt_add_one _

/-! ### Integrability of the kernels on cells -/

theorem integrableOn_kerPlane_cell {ν : Measure ℂ} {Cd : ℝ≥0} {R₀ : ℝ} {N : ℕ} {η A : ℝ}
    {R : ℕ → Set ℂ} {c : ℕ → ℂ} (hν : MeasClassPlane ν Cd R₀)
    (hC : IsCells univ dist (massRadius ν) ν N η A R c) (i : ℕ) (z : ℂ) :
    IntegrableOn (kerPlane z) (R i) ν := by
  have hRm := hC.measurableSet i
  have hfinR := hC.measure_lt_top i
  set B1 := ball z 1
  have hB1 : ν B1 < ∞ :=
    (measure_mono ball_subset_closedBall).trans_lt (hν.finite _ (isCompact_closedBall z 1))
  obtain ⟨Cc, hCc⟩ := christ_plane_quant Cd R₀ 1
  have hchr := hCc ν hν z 1 one_pos le_rfl
  set D : ℝ := dist z (c i) + A * massRadius ν (c i) + 1
  set K : ℝ := max (Real.log D) 0
  have hmeas : Measurable (kerPlane z) := by unfold kerPlane; fun_prop
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  have hpt : ∀ ζ ∈ R i, ‖kerPlane z ζ‖ₑ ≤ ENNReal.ofReal K +
      B1.indicator (fun ζ ↦ ENNReal.ofReal (Real.log (1 / dist z ζ))) ζ := by
    intro ζ hζ
    rw [Real.enorm_eq_ofReal_abs, kerPlane]
    by_cases hζz : ζ = z
    · simp [hζz]
    have hd : 0 < dist z ζ := dist_pos.2 (Ne.symm hζz)
    rw [← dist_eq_norm]
    by_cases hB : ζ ∈ B1
    · rw [indicator_of_mem hB]
      have hd1 : dist z ζ < 1 := by rw [dist_comm]; exact hB
      have hlog : Real.log (dist z ζ) < 0 := Real.log_neg hd hd1
      rw [abs_of_neg hlog]
      refine le_trans ?_ le_add_self
      apply ENNReal.ofReal_le_ofReal
      rw [one_div, Real.log_inv]
    · rw [indicator_of_notMem hB, add_zero]
      have hd1 : 1 ≤ dist z ζ := by
        rw [dist_comm]; simpa [B1, mem_ball] using hB
      have hlog : 0 ≤ Real.log (dist z ζ) := Real.log_nonneg hd1
      rw [abs_of_nonneg hlog]
      apply ENNReal.ofReal_le_ofReal
      refine le_trans ?_ (le_max_left _ _)
      apply Real.log_le_log hd
      have := hC.subset i ζ hζ
      calc dist z ζ ≤ dist z (c i) + dist (c i) ζ := dist_triangle _ _ _
        _ ≤ D := by simp only [D]; linarith
  calc ∫⁻ ζ in R i, ‖kerPlane z ζ‖ₑ ∂ν
      ≤ ∫⁻ ζ in R i, (ENNReal.ofReal K +
          B1.indicator (fun ζ ↦ ENNReal.ofReal (Real.log (1 / dist z ζ))) ζ) ∂ν :=
        setLIntegral_mono' hRm hpt
    _ = ENNReal.ofReal K * ν (R i) + ∫⁻ ζ in R i,
          B1.indicator (fun ζ ↦ ENNReal.ofReal (Real.log (1 / dist z ζ))) ζ ∂ν := by
        rw [lintegral_add_left measurable_const, setLIntegral_const]
    _ ≤ ENNReal.ofReal K * ν (R i) + ∫⁻ ζ in B1, ENNReal.ofReal (Real.log (1 / dist z ζ)) ∂ν := by
        refine add_le_add le_rfl ?_
        rw [← lintegral_indicator isOpen_ball.measurableSet]
        exact setLIntegral_le_lintegral _ _
    _ < ∞ := by
        refine ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfinR, ?_⟩
        exact hchr.trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top hB1)

theorem integrableOn_kerDisc_cell {ν : Measure ℂ} {Cd : ℝ≥0} {R₀ : ℝ} {N : ℕ} {η A : ℝ}
    {R : ℕ → Set ℂ} {c : ℕ → ℂ} (hν : MeasClassDisc ν Cd R₀)
    (hC : IsCells 𝔻 hypDist (massRadiusDisc ν) ν N η A R c) (i : ℕ) {z : ℂ} (hz : z ∈ 𝔻) :
    IntegrableOn (kerDisc z) (R i) ν := by
  have hRm := hC.measurableSet i
  have hfinR := hC.measure_lt_top i
  set B1 := hypBall z 1
  have hB1 : ν B1 < ∞ := by
    refine (measure_mono ?_).trans_lt (hν.finite _ (closedBall_tanh_subset_disc
      (Real.artanh ‖z‖ + 1)) (isCompact_closedBall _ _))
    exact fun w hw ↦ closedHypBall_subset_closedBall hz 1 ⟨hw.1, hw.2.le⟩
  obtain ⟨Cc, hCc⟩ := christ_disc_quant Cd R₀ 1
  have hchr := hCc ν hν z hz 1 one_pos le_rfl
  set K : ℝ := Real.log 5 - Real.log (Real.tanh 1)
  have ht1 : 0 < Real.tanh 1 := tanh_pos' one_pos
  have hK0 : 0 ≤ - Real.log (Real.tanh 1) := by
    have := Real.log_nonpos ht1.le (Real.tanh_lt_one 1).le; linarith
  have hlog5 : 0 ≤ Real.log 5 := Real.log_nonneg (by norm_num)
  have hmeas : Measurable (kerDisc z) := by unfold kerDisc pseudoHyp; fun_prop
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  have hpt : ∀ ζ ∈ R i, ‖kerDisc z ζ‖ₑ ≤ ENNReal.ofReal K +
      B1.indicator (fun ζ ↦ ENNReal.ofReal (Real.log (1 / hypDist z ζ))) ζ := by
    intro ζ hζ
    have hζ𝔻 := hC.subset_univ i hζ
    rw [Real.enorm_eq_ofReal_abs, kerDisc]
    by_cases hζz : ζ = z
    · simp [hζz, pseudoHyp_self]
    set β := hypDist z ζ
    have hβ : 0 < β := lt_of_le_of_ne (hypDist_nonneg _ _) fun h ↦
      hζz ((hypDist_eq_zero_iff hz hζ𝔻).1 h.symm).symm
    have hp : pseudoHyp ζ z = Real.tanh β := by rw [← tanh_hypDist hζ𝔻 hz, hypDist_comm]
    have hp1 : pseudoHyp ζ z < 1 := pseudoHyp_lt_one hζ𝔻 hz
    rw [hp] at hp1 ⊢
    have htpos : 0 < Real.tanh β := tanh_pos' hβ
    have hlog : Real.log (Real.tanh β) < 0 := Real.log_neg htpos hp1
    rw [abs_of_neg hlog]
    by_cases hB : ζ ∈ B1
    · rw [indicator_of_mem hB]
      have hβ1 : β < 1 := hB.2
      have h5 := div_five_le_tanh hβ.le hβ1.le
      have : -Real.log (Real.tanh β) ≤ K + Real.log (1 / β) := by
        have := Real.log_le_log (by positivity) h5
        rw [Real.log_div hβ.ne' (by norm_num)] at this
        rw [one_div, Real.log_inv]
        simp only [K]; linarith
      exact (ENNReal.ofReal_le_ofReal this).trans ENNReal.ofReal_add_le
    · rw [indicator_of_notMem hB, add_zero]
      have hβ1 : 1 ≤ β := by
        by_contra h; push Not at h; exact hB ⟨hζ𝔻, h⟩
      apply ENNReal.ofReal_le_ofReal
      have := Real.log_le_log ht1 (tanh_le_tanh hβ1)
      simp only [K]; linarith
  calc ∫⁻ ζ in R i, ‖kerDisc z ζ‖ₑ ∂ν
      ≤ ∫⁻ ζ in R i, (ENNReal.ofReal K +
          B1.indicator (fun ζ ↦ ENNReal.ofReal (Real.log (1 / hypDist z ζ))) ζ) ∂ν :=
        setLIntegral_mono' hRm hpt
    _ = ENNReal.ofReal K * ν (R i) + ∫⁻ ζ in R i,
          B1.indicator (fun ζ ↦ ENNReal.ofReal (Real.log (1 / hypDist z ζ))) ζ ∂ν := by
        rw [lintegral_add_left measurable_const, setLIntegral_const]
    _ ≤ ENNReal.ofReal K * ν (R i) +
          ∫⁻ ζ in B1, ENNReal.ofReal (Real.log (1 / hypDist z ζ)) ∂ν := by
        refine add_le_add le_rfl ?_
        rw [← lintegral_indicator (isOpen_hypBall z 1).measurableSet]
        exact setLIntegral_le_lintegral _ _
    _ < ∞ := by
        refine ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfinR, ?_⟩
        exact hchr.trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top hB1)

/-! ### A generic per-cell bound -/

theorem abs_multiset_sum_le {s : Multiset ℂ} {f : ℂ → ℝ} {E : ℝ} (h : ∀ w ∈ s, |f w| ≤ E) :
    |(s.map f).sum| ≤ Multiset.card s * E := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a t ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons]
    have ha := h a (Multiset.mem_cons_self a t)
    have ht := ih fun w hw ↦ h w (Multiset.mem_cons_of_mem hw)
    calc |f a + (t.map f).sum| ≤ |f a| + |(t.map f).sum| := abs_add_le _ _
      _ ≤ E + Multiset.card t * E := add_le_add ha ht
      _ = ((Multiset.card t + 1 : ℕ) : ℝ) * E := by push_cast; ring

/-- Moment cancellation plus a pointwise bound on `k − T` gives `|cellPot| ≤ 2 N E`. -/
theorem abs_cellPot_le_of_bound {k : ℂ → ℂ → ℝ} {ν : Measure ℂ} {R : ℕ → Set ℂ}
    {Λ : ℕ → Multiset ℂ} {i m N : ℕ} {z : ℂ} (hcard : Multiset.card (Λ i) = N)
    (hmeas : ν (R i) = N) (hR : MeasurableSet (R i)) (hb : Bornology.IsBounded (R i))
    (hmom : ∀ j < m, ∫ ζ in R i, ζ ^ j ∂ν = ((Λ i).map (· ^ j)).sum)
    (hint : IntegrableOn (k z) (R i) ν) {T : ℂ → ℝ} {p : Polynomial ℂ} (hp : p.natDegree < m)
    (hT : ∀ ζ, T ζ = (p.eval ζ).re) {E : ℝ} (hΛ : ∀ w ∈ Λ i, |k z w - T w| ≤ E)
    (hRb : ∀ ζ ∈ R i, |k z ζ - T ζ| ≤ E) :
    |cellPot k ν R Λ i z| ≤ 2 * N * E := by
  have hfin : ν (R i) < ∞ := by rw [hmeas]; exact ENNReal.natCast_lt_top N
  rw [cellPot_eq_sub_poly hR hfin hb hmom hint hp hT]
  have h1 := abs_multiset_sum_le hΛ
  have h2 : ‖∫ ζ in R i, (k z ζ - T ζ) ∂ν‖ ≤ E * ν.real (R i) :=
    norm_setIntegral_le_of_norm_le_const hfin fun ζ hζ ↦ by
      rw [Real.norm_eq_abs]; exact hRb ζ hζ
  have hreal : ν.real (R i) = N := by simp [Measure.real, hmeas]
  rw [hreal, Real.norm_eq_abs] at h2
  rw [hcard] at h1
  calc _ ≤ |((Λ i).map fun w ↦ k z w - T w).sum| + |∫ ζ in R i, (k z ζ - T ζ) ∂ν| :=
        abs_sub _ _
    _ ≤ N * E + E * N := add_le_add h1 h2
    _ = 2 * N * E := by ring

/-! ### Per-cell bounds for non-near cells (§3.4) -/

/-- (P): plane, order-3 moments. -/
theorem abs_cellPot_le_plane {ν : Measure ℂ} {N : ℕ} {η A B : ℝ} {R : ℕ → Set ℂ}
    {c : ℕ → ℂ} {m : ℕ → ℕ} {Λ : ℕ → Multiset ℂ}
    (hC : IsCells univ dist (massRadius ν) ν N η A R c)
    (hN : IsNodes univ dist (massRadius ν) ν N B R c m Λ) (hA : 0 < A) (hB : 0 ≤ B) {i : ℕ}
    (hm : 3 ≤ m i) {z : ℂ} (hint : IntegrableOn (kerPlane z) (R i) ν)
    (hρ : 0 < massRadius ν (c i))
    (hfar : 2 * (A + B) * massRadius ν (c i) ≤ dist z (c i)) :
    |cellPot kerPlane ν R Λ i z| ≤
      4 * N * (A + B) ^ 3 * (massRadius ν (c i) / dist z (c i)) ^ 3 := by
  set ρ := massRadius ν (c i)
  set d := dist z (c i)
  have hd : 0 < d := lt_of_lt_of_le (by positivity) hfar
  have hzc : z ≠ c i := dist_pos.1 hd
  obtain ⟨p, hp, hT⟩ := exists_poly_taylorPlane (m := 3) (by norm_num) z (c i)
  have hmom : ∀ j < 3, ∫ ζ in R i, ζ ^ j ∂ν = ((Λ i).map (· ^ j)).sum :=
    fun j hj ↦ hN.moments i j (lt_of_lt_of_le hj hm)
  have hpt : ∀ ζ, ‖ζ - c i‖ ≤ (A + B) * ρ →
      |kerPlane z ζ - taylorPlane 3 z (c i) ζ| ≤ 2 * ((A + B) ^ 3 * (ρ / d) ^ 3) := by
    intro ζ hζ
    have h2 : 2 * ‖ζ - c i‖ ≤ ‖z - c i‖ := by
      rw [← dist_eq_norm z]; linarith
    refine (abs_kerPlane_sub_taylorPlane_le (by norm_num) hzc h2).trans ?_
    rw [← dist_eq_norm z]
    have : ‖ζ - c i‖ / d ≤ (A + B) * ρ / d := div_le_div_of_nonneg_right hζ hd.le
    calc 2 * (‖ζ - c i‖ / d) ^ 3 ≤ 2 * ((A + B) * ρ / d) ^ 3 := by gcongr
      _ = 2 * ((A + B) ^ 3 * (ρ / d) ^ 3) := by ring
  have hbd := abs_cellPot_le_of_bound (hN.card i) (hC.measure_eq i) (hC.measurableSet i)
    (hC.isBounded_plane i) hmom hint hp (fun ζ ↦ hT ζ)
    (fun w hw ↦ hpt w (by
      rw [← dist_eq_norm, dist_comm]
      exact (hN.near i w hw).trans (by nlinarith)))
    (fun ζ hζ ↦ hpt ζ (by
      rw [← dist_eq_norm, dist_comm]
      exact (hC.subset i ζ hζ).trans (by nlinarith)))
  calc _ ≤ 2 * N * (2 * ((A + B) ^ 3 * (ρ / d) ^ 3)) := hbd
    _ = 4 * N * (A + B) ^ 3 * (ρ / d) ^ 3 := by ring

/-- (D-near): disc, small cells, order-3 moments. -/
theorem abs_cellPot_le_disc_near {ν : Measure ℂ} {N : ℕ} {η A B : ℝ} {R : ℕ → Set ℂ}
    {c : ℕ → ℂ} {m : ℕ → ℕ} {Λ : ℕ → Multiset ℂ}
    (hC : IsCells 𝔻 hypDist (massRadiusDisc ν) ν N η A R c)
    (hN : IsNodes 𝔻 hypDist (massRadiusDisc ν) ν N B R c m Λ) (hA : 0 < A) (hB : 0 ≤ B)
    {i : ℕ} (hm : 3 ≤ m i) {z : ℂ} (hz : z ∈ 𝔻) (hint : IntegrableOn (kerDisc z) (R i) ν)
    (hρ : 0 < massRadiusDisc ν (c i)) (hβ : hypDist z (c i) ≤ 1 / 4)
    (hβ' : 64 * (A + B) * massRadiusDisc ν (c i) ≤ hypDist z (c i)) :
    |cellPot kerDisc ν R Λ i z| ≤
      8 * N * (14 * (A + B)) ^ 3 * (massRadiusDisc ν (c i) / hypDist z (c i)) ^ 3 := by
  set ρ := massRadiusDisc ν (c i)
  set β := hypDist z (c i)
  set sr := (A + B) * ρ
  have hc := hC.center_mem' i
  have hsr0 : 0 < sr := by positivity
  have hβ0 : 0 < β := by nlinarith
  have hzc : z ≠ c i := by
    intro h; have : β = 0 := by simp [β, h]
    linarith
  have hz1 := norm_lt_one_of_mem_disc hz
  have hc1 := norm_lt_one_of_mem_disc hc
  have hcpos := one_sub_normSq_pos hc
  have hDpos := norm_one_sub_conj_mul_pos hz hc
  -- lower bound for `|z - c|`
  have hzcl : β * (1 - ‖c i‖ ^ 2) / 10 ≤ ‖z - c i‖ := by
    rw [norm_sub_eq_tanh_mul hz hc, hypDist_comm]
    have h5 := div_five_le_tanh hβ0.le (by linarith)
    have h2 := one_sub_normSq_le_two_mul_norm hz hc
    have ht0 : 0 ≤ Real.tanh β := tanh_nonneg_of_nonneg hβ0.le
    calc β * (1 - ‖c i‖ ^ 2) / 10 = (β / 5) * ((1 - ‖c i‖ ^ 2) / 2) := by ring
      _ ≤ Real.tanh β * ‖1 - conj z * c i‖ := by
          apply mul_le_mul h5 (by linarith) (by positivity) ht0
  have hzcpos : 0 < ‖z - c i‖ := norm_pos_iff.2 (sub_ne_zero.2 hzc)
  -- upper bound for `|ζ - c|`
  have hζc : ∀ ζ ∈ 𝔻, hypDist (c i) ζ ≤ sr → ‖ζ - c i‖ ≤ (4 / 3) * sr * (1 - ‖c i‖ ^ 2) := by
    intro ζ hζ hd
    refine (norm_sub_le_mul_exp hc hζ hd).trans ?_
    have he : Real.exp (2 * sr) ≤ 4 / 3 :=
      (Real.exp_le_exp.2 (by linarith)).trans exp_quarter_le
    have : sr * Real.exp (2 * sr) ≤ 4 / 3 * sr := by nlinarith
    exact mul_le_mul_of_nonneg_right this hcpos.le
  have hratio : ∀ ζ ∈ 𝔻, hypDist (c i) ζ ≤ sr →
      ‖ζ - c i‖ / ‖z - c i‖ ≤ (40 / 3) * sr / β := by
    intro ζ hζ hd
    rw [div_le_div_iff₀ hzcpos hβ0]
    have h1 := hζc ζ hζ hd
    have : ‖ζ - c i‖ * β ≤ (4 / 3) * sr * (1 - ‖c i‖ ^ 2) * β :=
      mul_le_mul_of_nonneg_right h1 hβ0.le
    nlinarith
  have hpt : ∀ ζ ∈ 𝔻, hypDist (c i) ζ ≤ sr →
      |kerDisc z ζ - taylorDisc 3 z (c i) ζ| ≤ 4 * ((14 * (A + B)) ^ 3 * (ρ / β) ^ 3) := by
    intro ζ hζ hd
    have hr := hratio ζ hζ hd
    have hr' : (40 / 3) * sr / β ≤ 1 / 2 := by
      rw [div_le_iff₀ hβ0]; nlinarith
    have h2 : 2 * ‖ζ - c i‖ ≤ ‖z - c i‖ := by
      have := hr.trans hr'
      rw [div_le_iff₀ hzcpos] at this; linarith
    refine (abs_kerDisc_sub_taylorDisc_le (by norm_num) hz hc hzc h2).trans ?_
    have hzD : (1 - ‖z‖ ^ 2) / ‖1 - conj z * c i‖ ≤ 2 := by
      rw [div_le_iff₀ hDpos]
      have := one_sub_mul_le_norm_one_sub_conj_mul z (c i)
      nlinarith [norm_nonneg z, norm_nonneg (c i)]
    have hr0 : 0 ≤ ‖ζ - c i‖ / ‖z - c i‖ := by positivity
    calc 2 * (1 - ‖z‖ ^ 2) * ‖ζ - c i‖ ^ 3 / (‖z - c i‖ ^ 3 * ‖1 - conj z * c i‖)
        = 2 * ((1 - ‖z‖ ^ 2) / ‖1 - conj z * c i‖) * (‖ζ - c i‖ / ‖z - c i‖) ^ 3 := by
          field_simp
      _ ≤ 2 * 2 * ((40 / 3) * sr / β) ^ 3 := by gcongr
      _ ≤ 4 * ((14 * (A + B)) ^ 3 * (ρ / β) ^ 3) := by
          have : (40 / 3) * sr / β ≤ 14 * (A + B) * (ρ / β) := by
            rw [show (40 / 3) * sr / β = (40 / 3) * (A + B) * (ρ / β) by ring]
            gcongr; norm_num
          calc 2 * 2 * ((40 / 3) * sr / β) ^ 3 ≤ 2 * 2 * (14 * (A + B) * (ρ / β)) ^ 3 := by
                gcongr
            _ = 4 * ((14 * (A + B)) ^ 3 * (ρ / β) ^ 3) := by ring
  obtain ⟨p, hp, hT⟩ := exists_poly_taylorDisc (m := 3) (by norm_num) z (c i)
  have hmom : ∀ j < 3, ∫ ζ in R i, ζ ^ j ∂ν = ((Λ i).map (· ^ j)).sum :=
    fun j hj ↦ hN.moments i j (lt_of_lt_of_le hj hm)
  have hbd := abs_cellPot_le_of_bound (hN.card i) (hC.measure_eq i) (hC.measurableSet i)
    (hC.isBounded_disc i) hmom hint hp (fun ζ ↦ hT ζ)
    (fun w hw ↦ hpt w (hN.mem i w hw) ((hN.near i w hw).trans (by nlinarith)))
    (fun ζ hζ ↦ hpt ζ (hC.subset_univ i hζ) ((hC.subset i ζ hζ).trans (by nlinarith)))
  calc _ ≤ 2 * N * (4 * ((14 * (A + B)) ^ 3 * (ρ / β) ^ 3)) := hbd
    _ = 8 * N * (14 * (A + B)) ^ 3 * (ρ / β) ^ 3 := by ring

/-- (D-far): disc, any cell (order-2 moments), hyperbolically far from `z`. -/
theorem abs_cellPot_le_disc_far (A B R₀ M₀ : ℝ) (N : ℕ) (hA : 0 < A) (hB : 0 ≤ B)
    (hM₀ : 0 < M₀) :
    ∃ CD : ℝ, 0 ≤ CD ∧ ∀ (ν : Measure ℂ) (η : ℝ) (R : ℕ → Set ℂ) (c : ℕ → ℂ) (m : ℕ → ℕ)
      (Λ : ℕ → Multiset ℂ), IsCells 𝔻 hypDist (massRadiusDisc ν) ν N η A R c →
      IsNodes 𝔻 hypDist (massRadiusDisc ν) ν N B R c m Λ → ∀ i, 2 ≤ m i → ∀ z ∈ 𝔻,
      IntegrableOn (kerDisc z) (R i) ν → 0 ≤ massRadiusDisc ν (c i) →
      massRadiusDisc ν (c i) ≤ R₀ → M₀ ≤ hypDist z (c i) →
      2 * (A + B) * massRadiusDisc ν (c i) ≤ hypDist z (c i) →
      |cellPot kerDisc ν R Λ i z| ≤
        CD * ((1 - ‖z‖ ^ 2) * ((1 - ‖c i‖ ^ 2) * massRadiusDisc ν (c i)) ^ 2 /
          ‖1 - conj z * c i‖ ^ 3) := by
  set S₀ := (A + B) * max R₀ 0
  set t₀ := Real.tanh (M₀ / 2)
  have ht₀ : 0 < t₀ := tanh_pos' (by linarith)
  refine ⟨4 * N * Real.exp (10 * S₀) * (A + B) ^ 2 / t₀ ^ 2, by positivity, ?_⟩
  intro ν η R c m Λ hC hN i hm z hz hint hρ0 hρR hM hfar
  set ρ := massRadiusDisc ν (c i)
  set β := hypDist z (c i)
  set sr := (A + B) * ρ
  have hc := hC.center_mem' i
  have hsr0 : 0 ≤ sr := by positivity
  have hsrS : sr ≤ S₀ :=
    mul_le_mul_of_nonneg_left (hρR.trans (le_max_left _ _)) (by positivity)
  have hcpos := one_sub_normSq_pos hc
  have hzpos := one_sub_normSq_pos hz
  have hDpos := norm_one_sub_conj_mul_pos hz hc
  set Bc := {w | w ∈ 𝔻 ∧ hypDist (c i) w ≤ sr}
  have hBcconv : Convex ℝ Bc := convex_closedHypBall hc sr
  have hcBc : c i ∈ Bc := ⟨hc, by simp [hsr0]⟩
  -- points of `Bc` are hyperbolically far from `z`
  have hfarξ : ∀ ξ ∈ Bc, M₀ / 2 ≤ hypDist z ξ := by
    intro ξ hξ
    have htri := hypDist_triangle hz hξ.1 hc
    rw [hypDist_comm ξ] at htri
    have : β ≤ hypDist z ξ + sr := htri.trans (by linarith [hξ.2])
    linarith
  have hξz : ∀ ξ ∈ Bc, ξ ≠ z := by
    intro ξ hξ h
    have := hfarξ ξ hξ
    rw [h, hypDist_self] at this
    linarith
  have hlow : ∀ ξ ∈ Bc, t₀ * ‖1 - conj z * ξ‖ ≤ ‖z - ξ‖ := by
    intro ξ hξ
    have h1 : t₀ ≤ pseudoHyp z ξ := by
      rw [← tanh_hypDist hz hξ.1]; exact tanh_le_tanh (hfarξ ξ hξ)
    have hD := norm_one_sub_conj_mul_pos hz hξ.1
    rw [pseudoHyp, le_div_iff₀ hD] at h1
    linarith
  have hcomp : ∀ ξ ∈ Bc, ‖1 - conj z * c i‖ ≤ Real.exp (2 * sr) * ‖1 - conj z * ξ‖ :=
    fun ξ hξ ↦ (norm_one_sub_conj_mul_comparable hz hc hξ.1 hξ.2).2
  set Bd := 2 * (1 - ‖z‖ ^ 2) * Real.exp (6 * sr) / (t₀ ^ 2 * ‖1 - conj z * c i‖ ^ 3)
  have hBd : ∀ ξ ∈ Bc, 2 * (1 - ‖z‖ ^ 2) / (‖z - ξ‖ ^ 2 * ‖1 - conj z * ξ‖) ≤ Bd := by
    intro ξ hξ
    have hD := norm_one_sub_conj_mul_pos hz hξ.1
    have h1 := hlow ξ hξ
    have h2 := hcomp ξ hξ
    have hzξ : 0 < ‖z - ξ‖ := norm_pos_iff.2 (sub_ne_zero.2 (hξz ξ hξ).symm)
    have he : Real.exp (6 * sr) = Real.exp (2 * sr) ^ 3 := by
      rw [← Real.exp_nat_mul]; ring_nf
    rw [div_le_div_iff₀ (by positivity) (by positivity), he]
    have h3 : (t₀ * ‖1 - conj z * ξ‖) ^ 2 ≤ ‖z - ξ‖ ^ 2 := by
      gcongr
    have h4 : ‖1 - conj z * c i‖ ^ 3 ≤ (Real.exp (2 * sr) * ‖1 - conj z * ξ‖) ^ 3 := by
      gcongr
    calc 2 * (1 - ‖z‖ ^ 2) * (t₀ ^ 2 * ‖1 - conj z * c i‖ ^ 3)
        ≤ 2 * (1 - ‖z‖ ^ 2) * (t₀ ^ 2 * (Real.exp (2 * sr) * ‖1 - conj z * ξ‖) ^ 3) := by
          gcongr
      _ = 2 * (1 - ‖z‖ ^ 2) * Real.exp (2 * sr) ^ 3 *
            ((t₀ * ‖1 - conj z * ξ‖) ^ 2 * ‖1 - conj z * ξ‖) := by ring
      _ ≤ 2 * (1 - ‖z‖ ^ 2) * Real.exp (2 * sr) ^ 3 * (‖z - ξ‖ ^ 2 * ‖1 - conj z * ξ‖) := by
          gcongr
  have hpt : ∀ ζ ∈ Bc, |kerDisc z ζ - taylorDisc 2 z (c i) ζ| ≤
      2 * Real.exp (10 * S₀) * (A + B) ^ 2 / t₀ ^ 2 *
        ((1 - ‖z‖ ^ 2) * ((1 - ‖c i‖ ^ 2) * ρ) ^ 2 / ‖1 - conj z * c i‖ ^ 3) := by
    intro ζ hζ
    have hseg : segment ℝ (c i) ζ ⊆ Bc := hBcconv.segment_subset hcBc hζ
    have hK3 := abs_kerDisc_sub_taylorDisc_two_le hz (Bd := Bd)
      (fun ξ hξ ↦ ⟨(hseg hξ).1, hξz ξ (hseg hξ)⟩) (fun ξ hξ ↦ hBd ξ (hseg hξ))
    refine hK3.trans ?_
    have hζc := norm_sub_le_mul_exp hc hζ.1 hζ.2
    have hζc2 : ‖ζ - c i‖ ^ 2 ≤ (sr * Real.exp (2 * sr) * (1 - ‖c i‖ ^ 2)) ^ 2 := by gcongr
    have he10 : Real.exp (6 * sr) * Real.exp (2 * sr) ^ 2 ≤ Real.exp (10 * S₀) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      exact Real.exp_le_exp.2 (by push_cast; nlinarith)
    calc Bd * ‖ζ - c i‖ ^ 2 ≤ Bd * (sr * Real.exp (2 * sr) * (1 - ‖c i‖ ^ 2)) ^ 2 := by
          gcongr
      _ = 2 * (Real.exp (6 * sr) * Real.exp (2 * sr) ^ 2) * (A + B) ^ 2 / t₀ ^ 2 *
            ((1 - ‖z‖ ^ 2) * ((1 - ‖c i‖ ^ 2) * ρ) ^ 2 / ‖1 - conj z * c i‖ ^ 3) := by
          simp only [Bd, sr]; field_simp
      _ ≤ _ := by gcongr
  obtain ⟨p, hp, hT⟩ := exists_poly_taylorDisc (m := 2) (by norm_num) z (c i)
  have hmom : ∀ j < 2, ∫ ζ in R i, ζ ^ j ∂ν = ((Λ i).map (· ^ j)).sum :=
    fun j hj ↦ hN.moments i j (lt_of_lt_of_le hj hm)
  have hbd := abs_cellPot_le_of_bound (hN.card i) (hC.measure_eq i) (hC.measurableSet i)
    (hC.isBounded_disc i) hmom hint hp (fun ζ ↦ hT ζ)
    (fun w hw ↦ hpt w ⟨hN.mem i w hw, (hN.near i w hw).trans (by nlinarith)⟩)
    (fun ζ hζ ↦ hpt ζ ⟨hC.subset_univ i hζ, (hC.subset i ζ hζ).trans (by nlinarith)⟩)
  refine hbd.trans (le_of_eq ?_)
  ring

/-! ### The non-near part is uniformly bounded (§3.7) -/

theorem nonNear_sum_le_disc (Cd : ℝ≥0) (R₀ η A B ρ₀ : ℝ) (N : ℕ) (hη : 0 < η) (hA : 0 < A)
    (hB : 0 ≤ B) (hρ₀ : 0 < ρ₀) :
    ∃ K₀ C : ℝ, 2 * (A + B) ≤ K₀ ∧ 0 ≤ C ∧ ∀ (ν : Measure ℂ) (R : ℕ → Set ℂ) (c : ℕ → ℂ)
      (m : ℕ → ℕ) (Λ : ℕ → Multiset ℂ), MeasClassDisc ν Cd R₀ →
      IsCells 𝔻 hypDist (massRadiusDisc ν) ν N η A R c →
      IsNodes 𝔻 hypDist (massRadiusDisc ν) ν N B R c m Λ → (∀ i, 2 ≤ m i) →
      (∀ i, massRadiusDisc ν (c i) ≤ ρ₀ → 3 ≤ m i) →
      ∀ z ∈ 𝔻, ∀ F : Finset ℕ, (∀ i ∈ F, K₀ * massRadiusDisc ν (c i) ≤ hypDist z (c i)) →
        ∑ i ∈ F, |cellPot kerDisc ν R Λ i z| ≤ C := by
  set K₀ := 64 * (A + B + 1) with hK₀
  have hK₀1 : 1 ≤ K₀ := by rw [hK₀]; nlinarith
  set ρ₀' := min ρ₀ (1 / (8 * (A + B + 1))) with hρ₀'
  have hρ₀'pos : 0 < ρ₀' := lt_min hρ₀ (by positivity)
  set M₀ := min (1 / 4) (K₀ * ρ₀') with hM₀def
  have hM₀ : 0 < M₀ := lt_min (by norm_num) (by positivity)
  obtain ⟨δ, hδ, -, hδK⟩ := claim1_nonNear_disc Cd R₀ K₀ (by linarith)
  obtain ⟨C₁, -, hcl⟩ := claim1_disc_quant Cd R₀ 0
  obtain ⟨Cn, hCn⟩ := nearField_sum_le_disc Cd R₀ η A δ hη hδ
  obtain ⟨CD, hCD0, hCD⟩ := abs_cellPot_le_disc_far A B R₀ M₀ N hA hB hM₀
  obtain ⟨Cf, hCf⟩ := farField_sum_le_disc Cd R₀ η A M₀ hη
  set Cnear : ℝ := 8 * N * (14 * (A + B)) ^ 3
  refine ⟨K₀, Cnear * max Cn 0 + CD * max Cf 0, by rw [hK₀]; nlinarith, by positivity, ?_⟩
  intro ν R c m Λ hν hC hN hm2 hm3 z hz F hF
  rw [← Finset.sum_filter_add_sum_filter_not F (fun i ↦ hypDist z (c i) < M₀)]
  have hci := hC.center_mem'
  have hρ : ∀ i, 0 < massRadiusDisc ν (c i) ∧ massRadiusDisc ν (c i) ≤ R₀ := fun i ↦
    ⟨(hcl ν hν (c i) (hci i) (c i) (hci i)).1, (hcl ν hν (c i) (hci i) (c i) (hci i)).2.1⟩
  have h1 : ∑ i ∈ F.filter (fun i ↦ hypDist z (c i) < M₀), |cellPot kerDisc ν R Λ i z| ≤
      Cnear * max Cn 0 := by
    have hcond : ∀ i ∈ F.filter (fun i ↦ hypDist z (c i) < M₀),
        massRadiusDisc ν (c i) < ρ₀' ∧ hypDist z (c i) ≤ 1 / 4 := by
      intro i hi
      rw [Finset.mem_filter] at hi
      have hK := hF i hi.1
      refine ⟨?_, (hi.2.trans_le (min_le_left _ _)).le⟩
      have : K₀ * massRadiusDisc ν (c i) < K₀ * ρ₀' :=
        hK.trans_lt (hi.2.trans_le (min_le_right _ _))
      exact lt_of_mul_lt_mul_left this (by linarith)
    calc _ ≤ ∑ i ∈ F.filter (fun i ↦ hypDist z (c i) < M₀),
          Cnear * (massRadiusDisc ν (c i) / hypDist z (c i)) ^ 3 := by
          refine Finset.sum_le_sum fun i hi ↦ ?_
          obtain ⟨hρi, hβi⟩ := hcond i hi
          have hK := hF i (Finset.mem_filter.1 hi).1
          have hρ₀le : massRadiusDisc ν (c i) ≤ ρ₀ := hρi.le.trans (min_le_left _ _)
          have hs : (A + B) * massRadiusDisc ν (c i) ≤ 1 / 8 := by
            have h8 : massRadiusDisc ν (c i) ≤ 1 / (8 * (A + B + 1)) :=
              hρi.le.trans (min_le_right _ _)
            rw [le_div_iff₀ (by positivity)] at h8
            nlinarith [(hρ i).1]
          exact abs_cellPot_le_disc_near hC hN hA hB (hm3 i hρ₀le) hz
            (integrableOn_kerDisc_cell hν hC i hz) (hρ i).1 hβi
            (le_trans (by rw [hK₀]; nlinarith [(hρ i).1]) hK)
      _ = Cnear * ∑ i ∈ F.filter (fun i ↦ hypDist z (c i) < M₀),
          (massRadiusDisc ν (c i) / hypDist z (c i)) ^ 3 := by rw [Finset.mul_sum]
      _ ≤ Cnear * max Cn 0 := by
          gcongr
          refine (hCn ν N R c hν hC z hz _ fun i hi ↦ ?_).trans (le_max_left _ _)
          have hK := hF i (Finset.mem_filter.1 hi).1
          refine ⟨hδK ν hν z hz (c i) (hci i) hK, (hcond i hi).2, ?_⟩
          exact le_trans (by rw [hK₀]; nlinarith [(hρ i).1]) hK
  have h2 : ∑ i ∈ F.filter (fun i ↦ ¬ hypDist z (c i) < M₀), |cellPot kerDisc ν R Λ i z| ≤
      CD * max Cf 0 := by
    calc _ ≤ ∑ i ∈ F.filter (fun i ↦ ¬ hypDist z (c i) < M₀),
          CD * ((1 - ‖z‖ ^ 2) * ((1 - ‖c i‖ ^ 2) * massRadiusDisc ν (c i)) ^ 2 /
            ‖1 - conj z * c i‖ ^ 3) := by
          refine Finset.sum_le_sum fun i hi ↦ ?_
          rw [Finset.mem_filter, not_lt] at hi
          have hK := hF i hi.1
          exact hCD ν η R c m Λ hC hN i (hm2 i) z hz (integrableOn_kerDisc_cell hν hC i hz)
            (hρ i).1.le (hρ i).2 hi.2 (le_trans (by rw [hK₀]; nlinarith [(hρ i).1]) hK)
      _ = CD * ∑ i ∈ F.filter (fun i ↦ ¬ hypDist z (c i) < M₀),
          ((1 - ‖z‖ ^ 2) * ((1 - ‖c i‖ ^ 2) * massRadiusDisc ν (c i)) ^ 2 /
            ‖1 - conj z * c i‖ ^ 3) := by rw [Finset.mul_sum]
      _ ≤ CD * max Cf 0 := by
          gcongr
          refine (hCf ν N R c hν hC z hz _ fun i hi ↦ ?_).trans (le_max_left _ _)
          rw [Finset.mem_filter, not_lt] at hi
          exact hi.2
  linarith

theorem nonNear_sum_le_plane (Cd : ℝ≥0) (R₀ η A B : ℝ) (N : ℕ) (hη : 0 < η) (hA : 0 < A)
    (hB : 0 ≤ B) :
    ∃ K₀ C : ℝ, 2 * (A + B) ≤ K₀ ∧ 0 ≤ C ∧ ∀ (ν : Measure ℂ) (R : ℕ → Set ℂ) (c : ℕ → ℂ)
      (m : ℕ → ℕ) (Λ : ℕ → Multiset ℂ), MeasClassPlane ν Cd R₀ →
      IsCells univ dist (massRadius ν) ν N η A R c →
      IsNodes univ dist (massRadius ν) ν N B R c m Λ → (∀ i, 3 ≤ m i) →
      ∀ z : ℂ, ∀ F : Finset ℕ, (∀ i ∈ F, K₀ * massRadius ν (c i) ≤ dist z (c i)) →
        ∑ i ∈ F, |cellPot kerPlane ν R Λ i z| ≤ C := by
  set K₀ := 2 * (A + B) + 1 with hK₀
  have hK₀1 : 1 ≤ K₀ := by rw [hK₀]; linarith
  obtain ⟨δ, hδ, -, hδK⟩ := claim1_nonNear_plane Cd R₀ K₀ (by linarith)
  obtain ⟨C₁, -, hcl⟩ := claim1_plane_quant Cd R₀ 0
  obtain ⟨Cn, hCn⟩ := nearField_sum_le_plane Cd R₀ η A δ hη hδ
  obtain ⟨Cf, hCf⟩ := farField_sum_le_plane Cd R₀ η A (1 / 4) hη (by norm_num)
  set Cc : ℝ := 4 * N * (A + B) ^ 3
  refine ⟨K₀, Cc * (max Cn 0 + max Cf 0), by rw [hK₀]; linarith, by positivity, ?_⟩
  intro ν R c m Λ hν hC hN hm z F hF
  have hρ : ∀ i, 0 < massRadius ν (c i) := fun i ↦ (hcl ν hν (c i) (c i)).1
  have hfar : ∀ i ∈ F, 2 * (A + B) * massRadius ν (c i) ≤ dist z (c i) := fun i hi ↦
    le_trans (by rw [hK₀]; nlinarith [hρ i]) (hF i hi)
  have hA' : ∀ i ∈ F, 2 * A * massRadius ν (c i) ≤ dist z (c i) := fun i hi ↦
    le_trans (by nlinarith [hρ i]) (hfar i hi)
  calc ∑ i ∈ F, |cellPot kerPlane ν R Λ i z|
      ≤ ∑ i ∈ F, Cc * (massRadius ν (c i) / dist z (c i)) ^ 3 :=
        Finset.sum_le_sum fun i hi ↦ abs_cellPot_le_plane hC hN hA hB (hm i)
          (integrableOn_kerPlane_cell hν hC i z) (hρ i) (hfar i hi)
    _ = Cc * (∑ i ∈ F.filter (fun i ↦ dist z (c i) ≤ 1 / 4),
          (massRadius ν (c i) / dist z (c i)) ^ 3 +
        ∑ i ∈ F.filter (fun i ↦ ¬ dist z (c i) ≤ 1 / 4),
          (massRadius ν (c i) / dist z (c i)) ^ 3) := by
        rw [Finset.sum_filter_add_sum_filter_not, Finset.mul_sum]
    _ ≤ Cc * (max Cn 0 + max Cf 0) := by
        gcongr
        · refine (hCn ν N R c hν hC z _ fun i hi ↦ ?_).trans (le_max_left _ _)
          rw [Finset.mem_filter] at hi
          exact ⟨hδK ν hν z (c i) (hF i hi.1), hi.2,
            le_trans (by nlinarith [hρ i]) (hfar i hi.1)⟩
        · refine (hCf ν N R c hν hC z _ fun i hi ↦ ?_).trans (le_max_left _ _)
          rw [Finset.mem_filter, not_le] at hi
          exact ⟨hi.2.le, hA' i hi.1⟩

/-! ### Summability of `cellPot` -/

theorem summable_cellPot_plane {ν : Measure ℂ} {Cd : ℝ≥0} {R₀ : ℝ} {N : ℕ} {η A B : ℝ}
    {R : ℕ → Set ℂ} {c : ℕ → ℂ} {m : ℕ → ℕ} {Λ : ℕ → Multiset ℂ}
    (hν : MeasClassPlane ν Cd R₀) (hη : 0 < η) (hA : 0 < A) (hB : 0 ≤ B)
    (hC : IsCells univ dist (massRadius ν) ν N η A R c)
    (hN : IsNodes univ dist (massRadius ν) ν N B R c m Λ) (hm : ∀ i, 3 ≤ m i) (z : ℂ) :
    Summable fun i ↦ |cellPot kerPlane ν R Λ i z| := by
  obtain ⟨K₀, C, -, -, hK⟩ := nonNear_sum_le_plane Cd R₀ η A B N hη hA hB
  obtain ⟨C₁, -, hcl⟩ := claim1_plane_quant Cd R₀ 0
  have hfin : {i | dist z (c i) < K₀ * massRadius ν (c i)}.Finite := by
    refine (finite_cells_plane hν hη hC {z} Bornology.isBounded_singleton
      (|K₀| * R₀ + 1)).subset fun i hi ↦ ⟨z, rfl, ?_⟩
    obtain ⟨hp, hle, -⟩ := hcl ν hν (c i) (c i)
    calc dist z (c i) < K₀ * massRadius ν (c i) := hi
      _ ≤ |K₀| * massRadius ν (c i) := mul_le_mul_of_nonneg_right (le_abs_self _) hp.le
      _ ≤ |K₀| * R₀ := mul_le_mul_of_nonneg_left hle (abs_nonneg _)
      _ < |K₀| * R₀ + 1 := lt_add_one _
  refine summable_of_sum_le (fun i ↦ abs_nonneg _)
    (c := ∑ i ∈ hfin.toFinset, |cellPot kerPlane ν R Λ i z| + C) fun u ↦ ?_
  rw [← Finset.sum_filter_add_sum_filter_not u (· ∈ hfin.toFinset)]
  refine add_le_add (Finset.sum_le_sum_of_subset_of_nonneg (fun i hi ↦ (Finset.mem_filter.1 hi).2)
    fun i _ _ ↦ abs_nonneg _) (hK ν R c m Λ hν hC hN hm z _ fun i hi ↦ ?_)
  have := (Finset.mem_filter.1 hi).2
  rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_lt] at this
  exact this

theorem summable_cellPot_disc {ν : Measure ℂ} {Cd : ℝ≥0} {R₀ : ℝ} {N : ℕ} {η A B ρ₀ : ℝ}
    {R : ℕ → Set ℂ} {c : ℕ → ℂ} {m : ℕ → ℕ} {Λ : ℕ → Multiset ℂ}
    (hν : MeasClassDisc ν Cd R₀) (hη : 0 < η) (hA : 0 < A) (hB : 0 ≤ B) (hρ₀ : 0 < ρ₀)
    (hC : IsCells 𝔻 hypDist (massRadiusDisc ν) ν N η A R c)
    (hN : IsNodes 𝔻 hypDist (massRadiusDisc ν) ν N B R c m Λ) (hm2 : ∀ i, 2 ≤ m i)
    (hm3 : ∀ i, massRadiusDisc ν (c i) ≤ ρ₀ → 3 ≤ m i) {z : ℂ} (hz : z ∈ 𝔻) :
    Summable fun i ↦ |cellPot kerDisc ν R Λ i z| := by
  obtain ⟨K₀, C, -, -, hK⟩ := nonNear_sum_le_disc Cd R₀ η A B ρ₀ N hη hA hB hρ₀
  obtain ⟨C₁, -, hcl⟩ := claim1_disc_quant Cd R₀ 0
  have hfin : {i | hypDist z (c i) < K₀ * massRadiusDisc ν (c i)}.Finite := by
    refine (finite_cells_disc hν hη hC {z} (singleton_subset_iff.2 hz) isCompact_singleton
      (|K₀| * R₀ + 1)).subset fun i hi ↦ ⟨z, rfl, ?_⟩
    obtain ⟨hp, hle, -⟩ := hcl ν hν (c i) (hC.center_mem' i) (c i) (hC.center_mem' i)
    calc hypDist z (c i) < K₀ * massRadiusDisc ν (c i) := hi
      _ ≤ |K₀| * massRadiusDisc ν (c i) := mul_le_mul_of_nonneg_right (le_abs_self _) hp.le
      _ ≤ |K₀| * R₀ := mul_le_mul_of_nonneg_left hle (abs_nonneg _)
      _ < |K₀| * R₀ + 1 := lt_add_one _
  refine summable_of_sum_le (fun i ↦ abs_nonneg _)
    (c := ∑ i ∈ hfin.toFinset, |cellPot kerDisc ν R Λ i z| + C) fun u ↦ ?_
  rw [← Finset.sum_filter_add_sum_filter_not u (· ∈ hfin.toFinset)]
  refine add_le_add (Finset.sum_le_sum_of_subset_of_nonneg (fun i hi ↦ (Finset.mem_filter.1 hi).2)
    fun i _ _ ↦ abs_nonneg _) (hK ν R c m Λ hν hC hN hm2 hm3 z hz _ fun i hi ↦ ?_)
  have := (Finset.mem_filter.1 hi).2
  rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_lt] at this
  exact this

end OC
