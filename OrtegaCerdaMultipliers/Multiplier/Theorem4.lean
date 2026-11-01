import OrtegaCerdaMultipliers.Multiplier.Potential
import OrtegaCerdaMultipliers.Multiplier.Estimates
import OrtegaCerdaMultipliers.Multiplier.Nodes

/-!
# M08 (Multiplier) — Theorem 4: multipliers in `𝔻` and `ℂ`

See `blueprint/M08_Multiplier.md` §2.8.  Scaffold: the core `multiplier_of_nodes_*` and the
quantitative `theorem4_*_quant` are `sorry`; the comparator statements `theorem4_disc`,
`theorem4_plane` (verbatim from `comparator/statements.lean`) are proved from them.
-/

open MeasureTheory Metric Set Complex
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace OC

/-! ### Helpers: ENNReal bookkeeping and the distance to the node set -/

/-- The three `ENNReal` inequalities of `Thm4Bounds*` from their real counterparts. -/
theorem ennreal_thm4_bounds {C : ℝ≥0} (hC : 1 ≤ C) {M : ℕ} {d ρ x : ℝ} (hd : 0 ≤ d)
    (hρ : 0 < ρ) (hx : 0 ≤ x) (h1 : (C : ℝ)⁻¹ * (d / ρ) ^ M ≤ x) (h2 : x ≤ C * (d / ρ))
    (h3 : d ≤ C * ρ) :
    C⁻¹ * (ENNReal.ofReal d / ENNReal.ofReal ρ) ^ M ≤ ENNReal.ofReal x ∧
      ENNReal.ofReal x ≤ C * (ENNReal.ofReal d / ENNReal.ofReal ρ) ∧
      ENNReal.ofReal d ≤ C * ENNReal.ofReal ρ := by
  have hC0 : (C : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ C := by exact_mod_cast hC
    linarith
  have hCnn : C ≠ 0 := by exact_mod_cast hC0
  have hcoe : ∀ y : ℝ≥0, (y : ℝ≥0∞) = ENNReal.ofReal (y : ℝ) := fun y ↦ by simp
  rw [← ENNReal.ofReal_div_of_pos hρ]
  refine ⟨?_, ?_, ?_⟩
  · rw [← ENNReal.ofReal_pow (div_nonneg hd hρ.le), hcoe,
      ← ENNReal.ofReal_mul (NNReal.coe_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (by simpa using h1)
  · rw [hcoe, ← ENNReal.ofReal_mul (NNReal.coe_nonneg _)]
    exact ENNReal.ofReal_le_ofReal h2
  · rw [hcoe, ← ENNReal.ofReal_mul (NNReal.coe_nonneg _)]
    exact ENNReal.ofReal_le_ofReal h3

/-- `hypDistSet` of a set whose distance from `z` is attained. -/
theorem hypDistSet_eq_ofReal {z : ℂ} {Z : Set ℂ} {d : ℝ} (hle : ∀ w ∈ Z, d ≤ hypDist z w)
    (hex : ∃ w ∈ Z, hypDist z w ≤ d) : hypDistSet z Z = ENNReal.ofReal d := by
  obtain ⟨w₀, hw₀, hw₀d⟩ := hex
  apply le_antisymm
  · exact (iInf₂_le w₀ hw₀).trans (ENNReal.ofReal_le_ofReal hw₀d)
  · exact le_iInf₂ fun w hw ↦ ENNReal.ofReal_le_ofReal (hle w hw)

theorem edistSet_eq_ofReal {z : ℂ} {Z : Set ℂ} {d : ℝ} (hle : ∀ w ∈ Z, d ≤ dist z w)
    (hex : ∃ w ∈ Z, dist z w ≤ d) : edistSet z Z = ENNReal.ofReal d := by
  obtain ⟨w₀, hw₀, hw₀d⟩ := hex
  apply le_antisymm
  · exact (iInf₂_le w₀ hw₀).trans (by rw [edist_dist]; exact ENNReal.ofReal_le_ofReal hw₀d)
  · exact le_iInf₂ fun w hw ↦ by rw [edist_dist]; exact ENNReal.ofReal_le_ofReal (hle w hw)


/-- From the log bounds of `S` to the bounds on `e^S` (real form). -/
theorem exp_bounds_of_log {S d ρ ρ' Cρ C₁ : ℝ} {M : ℕ} (hd : 0 < d) (hρ : 0 < ρ)
    (hρρ' : ρ ≤ ρ') (hρ'ρ : ρ' ≤ Cρ * ρ) (hlo : M * Real.log (d / ρ') - C₁ ≤ S)
    (hhi : S ≤ Real.log (d / ρ') + C₁) :
    (Real.exp C₁ * Cρ ^ M)⁻¹ * (d / ρ) ^ M ≤ Real.exp S ∧
      Real.exp S ≤ Real.exp C₁ * (d / ρ) := by
  have hρ' : 0 < ρ' := hρ.trans_le hρρ'
  have hCρ : 0 < Cρ := by
    by_contra h; push Not at h; nlinarith
  have hdρ' : 0 < d / ρ' := div_pos hd hρ'
  constructor
  · have h1 : Real.exp (M * Real.log (d / ρ') - C₁) = (d / ρ') ^ M / Real.exp C₁ := by
      rw [Real.exp_sub, Real.exp_nat_mul, Real.exp_log hdρ']
    have h2 : (d / ρ) / Cρ ≤ d / ρ' := by
      rw [div_div]; exact div_le_div_of_nonneg_left hd.le hρ' (by linarith)
    have h3 : ((d / ρ) / Cρ) ^ M ≤ (d / ρ') ^ M :=
      pow_le_pow_left₀ (by positivity) h2 M
    calc (Real.exp C₁ * Cρ ^ M)⁻¹ * (d / ρ) ^ M = ((d / ρ) / Cρ) ^ M / Real.exp C₁ := by
          rw [div_pow, div_pow, div_pow]; field_simp
      _ ≤ (d / ρ') ^ M / Real.exp C₁ := by gcongr
      _ = Real.exp (M * Real.log (d / ρ') - C₁) := h1.symm
      _ ≤ Real.exp S := Real.exp_le_exp.2 hlo
  · calc Real.exp S ≤ Real.exp (Real.log (d / ρ') + C₁) := Real.exp_le_exp.2 hhi
      _ = Real.exp C₁ * (d / ρ') := by rw [Real.exp_add, Real.exp_log hdρ', mul_comm]
      _ ≤ Real.exp C₁ * (d / ρ) := by
          gcongr

/-- The minimum of the distance to a locally finite set is attained (disc). -/
theorem exists_min_hypDist {Z : Set ℂ} (hZ : Z ⊆ 𝔻)
    (hfin : ∀ K ⊆ 𝔻, IsCompact K → (K ∩ Z).Finite) {z : ℂ} (hz : z ∈ 𝔻) {w₀ : ℂ}
    (hw₀ : w₀ ∈ Z) : ∃ d : ℝ, (∀ w ∈ Z, d ≤ hypDist z w) ∧ ∃ w ∈ Z, hypDist z w ≤ d := by
  set r := hypDist z w₀
  set K := closedBall (0 : ℂ) (Real.tanh (Real.artanh ‖z‖ + r))
  have hfinK := hfin K (closedBall_tanh_subset_disc _) (isCompact_closedBall _ _)
  have hne : (K ∩ Z).Nonempty :=
    ⟨w₀, closedHypBall_subset_closedBall hz r ⟨hZ hw₀, le_rfl⟩, hw₀⟩
  obtain ⟨w₁, hw₁, hmin⟩ := Set.exists_min_image _ (hypDist z) hfinK hne
  refine ⟨hypDist z w₁, fun w hw ↦ ?_, w₁, hw₁.2, le_rfl⟩
  by_cases hwr : hypDist z w ≤ r
  · exact hmin w ⟨closedHypBall_subset_closedBall hz r ⟨hZ hw, hwr⟩, hw⟩
  · push Not at hwr
    exact (hmin w₀ ⟨closedHypBall_subset_closedBall hz r ⟨hZ hw₀, le_rfl⟩, hw₀⟩).trans hwr.le

/-- The minimum of the distance to a locally finite set is attained (plane). -/
theorem exists_min_dist {Z : Set ℂ} (hfin : ∀ K : Set ℂ, IsCompact K → (K ∩ Z).Finite) (z : ℂ)
    {w₀ : ℂ} (hw₀ : w₀ ∈ Z) : ∃ d : ℝ, (∀ w ∈ Z, d ≤ dist z w) ∧ ∃ w ∈ Z, dist z w ≤ d := by
  set K := closedBall z (dist z w₀)
  have hfinK := hfin K (isCompact_closedBall _ _)
  have hne : (K ∩ Z).Nonempty := ⟨w₀, by simp [K, mem_closedBall, dist_comm], hw₀⟩
  obtain ⟨w₁, hw₁, hmin⟩ := Set.exists_min_image _ (dist z) hfinK hne
  refine ⟨dist z w₁, fun w hw ↦ ?_, w₁, hw₁.2, le_rfl⟩
  by_cases hwr : dist z w ≤ dist z w₀
  · exact hmin w ⟨by rw [mem_closedBall, dist_comm]; exact hwr, hw⟩
  · push Not at hwr
    exact (hmin w₀ ⟨by simp [K, mem_closedBall, dist_comm], hw₀⟩).trans hwr.le

/-- Core: multiplier from an arbitrary admissible node configuration (plane). -/
theorem multiplier_of_nodes_plane (Cd : ℝ≥0) (R₀ η A B : ℝ) (N : ℕ) (hR₀ : 0 < R₀)
    (hη : 0 < η) (hA : 0 < A) (hB : 0 ≤ B) (hN : 1 ≤ N) :
    ∃ (M : ℕ) (C : ℝ≥0), 1 ≤ M ∧ 1 ≤ C ∧ ∀ (ψ : ℂ → ℝ) (μ : Measure ℂ),
      WeightClassPlane ψ μ Cd R₀ → ∀ (R : ℕ → Set ℂ) (c : ℕ → ℂ) (m : ℕ → ℕ)
      (Λ : ℕ → Multiset ℂ),
      IsCells univ dist (massRadius (lapNorm μ)) (lapNorm μ) N η A R c →
      IsNodes univ dist (massRadius (lapNorm μ)) (lapNorm μ) N B R c m Λ → (∀ i, 3 ≤ m i) →
      ∃ h : ℂ → ℂ, Differentiable ℂ h ∧ (∀ w, h w = 0 ↔ w ∈ nodeSet Λ) ∧
        (∀ w, analyticOrderAt h w = (nodeCount Λ w : ℕ∞)) ∧ Thm4BoundsPlane ψ μ h M C := by
  obtain ⟨M, C₁, hM, hC₁, hbd⟩ := multPot_bounds_plane Cd R₀ η A B N hη hA hB hN
  obtain ⟨Cρ, hCρ, hρcomp⟩ := massRadius_lapNorm_quant Cd R₀
  obtain ⟨C0, -, hcl⟩ := claim1_plane_quant Cd R₀ 0
  set Cr : ℝ := max (max (Real.exp C₁ * Cρ ^ M) (Real.exp C₁)) (max (C₁ * Cρ) 1) with hCr
  have hCr1 : 1 ≤ Cr := le_max_of_le_right (le_max_right _ _)
  set C : ℝ≥0 := ⟨Cr, by linarith⟩ with hCdef
  have hCC : (C : ℝ) = Cr := rfl
  refine ⟨M, C, hM, by rw [← NNReal.coe_le_coe, hCC]; simpa using hCr1,
    fun ψ μ hw R c m Λ hC hNd hm ↦ ?_⟩
  have hν := hw.meas.lapNorm
  obtain ⟨hfs, -, hli, hcont, hlap⟩ := multPot_props_plane hw hη hC hNd hm
  have hwk : IsWeakLogModulus univ (nodeCount Λ)
      (fun z ↦ ψ z + multPot kerPlane (lapNorm μ) R Λ z) :=
    ⟨fun K _ hKc ↦ hfs K hKc, hli.locallyIntegrableOn _, hcont, fun χ hχ hc _ ↦ hlap χ hχ hc⟩
  have hΩ : ∀ z ∈ (univ : Set ℂ), ∃ r, dist z 0 < r ∧ closedBall (0 : ℂ) r ⊆ univ :=
    fun z _ ↦ ⟨‖z‖ + 1, by rw [dist_zero_right]; linarith, subset_univ _⟩
  obtain ⟨h, han, hnorm, hord⟩ := exists_analytic_norm_eq_exp_of_isWeakLogModulus hΩ hwk
  have hfinI : ∀ w, {i | w ∈ Λ i}.Finite := fun w ↦
    (finite_nodeIdx_plane hν hη hC hNd (K := {w}) Bornology.isBounded_singleton).subset
      fun i hi ↦ ⟨w, hi, rfl⟩
  have hnc : ∀ w, nodeCount Λ w ≠ 0 ↔ w ∈ nodeSet Λ := fun w ↦ nodeCount_ne_zero_iff (hfinI w)
  have hzero : ∀ w, h w = 0 ↔ w ∈ nodeSet Λ := by
    intro w
    have e := (han w (mem_univ w)).analyticOrderAt_eq_zero
    rw [hord w (mem_univ w)] at e
    rw [← hnc w]
    constructor
    · intro h0 hn0; exact e.1 (by simp [hn0]) h0
    · intro hne; by_contra hh; exact hne (by exact_mod_cast e.2 hh)
  have hfinZ : ∀ K : Set ℂ, IsCompact K → (K ∩ nodeSet Λ).Finite := by
    intro K hKc
    refine (hfs K hKc).subset fun w ⟨hwK, hwN⟩ ↦ ⟨hwK, ?_⟩
    exact (hnc w).2 hwN
  refine ⟨h, fun z ↦ (han z (mem_univ z)).differentiableAt, hzero,
    fun w ↦ hord w (mem_univ w), fun z ↦ ?_⟩
  have hZ : {w | h w = 0} = nodeSet Λ := by ext w; exact hzero w
  rw [hZ]
  obtain ⟨hrem, hest⟩ := hbd μ R c m Λ hw.meas hC hNd hm
  have hρpos : 0 < massRadius μ z := (hcl μ hw.meas z z).1
  obtain ⟨hρρ', hρ'ρ⟩ := hρcomp μ hw.meas z
  obtain ⟨w₀, hw₀, hw₀d⟩ := hrem z
  obtain ⟨d, hdle, hdex⟩ := exists_min_dist hfinZ z hw₀
  rw [edistSet_eq_ofReal hdle hdex]
  have hd0 : 0 ≤ d := by
    obtain ⟨w, hw, hwd⟩ := hdex; exact dist_nonneg.trans hwd
  have hdC : d ≤ C * massRadius μ z := by
    rw [hCC]
    calc d ≤ dist z w₀ := hdle w₀ hw₀
      _ ≤ C₁ * massRadius (lapNorm μ) z := hw₀d
      _ ≤ C₁ * (Cρ * massRadius μ z) := mul_le_mul_of_nonneg_left hρ'ρ hC₁.le
      _ = (C₁ * Cρ) * massRadius μ z := by ring
      _ ≤ Cr * massRadius μ z :=
          mul_le_mul_of_nonneg_right (le_max_of_le_right (le_max_left _ _)) hρpos.le
  by_cases hzN : z ∈ nodeSet Λ
  · have hd : d = 0 := le_antisymm (by simpa using hdle z hzN) hd0
    have hh0 : h z = 0 := (hzero z).2 hzN
    subst hd
    refine ennreal_thm4_bounds (C := C) (by rw [← NNReal.coe_le_coe, hCC]; simpa using hCr1)
      le_rfl hρpos (x := ‖h z‖ * Real.exp (-ψ z)) (by positivity) ?_ ?_ hdC
    · rw [hh0, norm_zero, zero_mul, zero_div, zero_pow (by omega), mul_zero]
    · rw [hh0, norm_zero, zero_mul, zero_div, mul_zero]
  · have hn0 : nodeCount Λ z = 0 := by
      by_contra h0; exact hzN ((hnc z).1 h0)
    have hhz := hnorm z (mem_univ z) hn0
    have hx : ‖h z‖ * Real.exp (-ψ z) = Real.exp (multPot kerPlane (lapNorm μ) R Λ z) := by
      rw [hhz, ← Real.exp_add]; ring_nf
    obtain ⟨hlo, hhi⟩ := hest z hzN d hdle hdex
    have hdpos : 0 < d := by
      obtain ⟨w, hw, hwd⟩ := hdex
      have hwz : w ≠ z := fun e ↦ hzN (e ▸ hw)
      have : 0 < dist z w := dist_pos.2 (Ne.symm hwz)
      linarith [hdle w hw]
    obtain ⟨e1, e2⟩ := exp_bounds_of_log hdpos hρpos hρρ' hρ'ρ hlo hhi
    have hCpos : 0 < Real.exp C₁ * Cρ ^ M := by positivity
    refine ennreal_thm4_bounds (C := C) (by rw [← NNReal.coe_le_coe, hCC]; simpa using hCr1)
      hd0 hρpos (by positivity) ?_ ?_ hdC
    · rw [hx, hCC]
      refine le_trans ?_ e1
      gcongr
      exact le_max_of_le_left (le_max_left _ _)
    · rw [hx, hCC]
      refine e2.trans ?_
      gcongr
      exact le_max_of_le_left (le_max_right _ _)

/-- Core: multiplier from an arbitrary admissible node configuration (disc). -/
theorem multiplier_of_nodes_disc (Cd : ℝ≥0) (R₀ η A B ρ₀ : ℝ) (N : ℕ) (hR₀ : 0 < R₀)
    (hη : 0 < η) (hA : 0 < A) (hB : 0 ≤ B) (hρ₀ : 0 < ρ₀) (hN : 1 ≤ N) :
    ∃ (M : ℕ) (C : ℝ≥0), 1 ≤ M ∧ 1 ≤ C ∧ ∀ (ψ : ℂ → ℝ) (μ : Measure ℂ),
      WeightClassDisc ψ μ Cd R₀ → ∀ (R : ℕ → Set ℂ) (c : ℕ → ℂ) (m : ℕ → ℕ)
      (Λ : ℕ → Multiset ℂ),
      IsCells 𝔻 hypDist (massRadiusDisc (lapNorm μ)) (lapNorm μ) N η A R c →
      IsNodes 𝔻 hypDist (massRadiusDisc (lapNorm μ)) (lapNorm μ) N B R c m Λ →
      (∀ i, 2 ≤ m i) → (∀ i, massRadiusDisc (lapNorm μ) (c i) ≤ ρ₀ → 3 ≤ m i) →
      ∃ h : ℂ → ℂ, DifferentiableOn ℂ h 𝔻 ∧ (∀ w ∈ 𝔻, h w = 0 ↔ w ∈ nodeSet Λ) ∧
        (∀ w ∈ 𝔻, analyticOrderAt h w = (nodeCount Λ w : ℕ∞)) ∧
        Thm4BoundsDisc ψ μ h M C := by
  obtain ⟨M, C₁, hM, hC₁, hbd⟩ := multPot_bounds_disc Cd R₀ η A B ρ₀ N hη hA hB hρ₀ hN
  obtain ⟨Cρ, hCρ, hρcomp⟩ := massRadiusDisc_lapNorm_quant Cd R₀
  obtain ⟨C0, -, hcl⟩ := claim1_disc_quant Cd R₀ 0
  set Cr : ℝ := max (max (Real.exp C₁ * Cρ ^ M) (Real.exp C₁)) (max (C₁ * Cρ) 1) with hCr
  have hCr1 : 1 ≤ Cr := le_max_of_le_right (le_max_right _ _)
  set C : ℝ≥0 := ⟨Cr, by linarith⟩ with hCdef
  have hCC : (C : ℝ) = Cr := rfl
  refine ⟨M, C, hM, by rw [← NNReal.coe_le_coe, hCC]; simpa using hCr1,
    fun ψ μ hw R c m Λ hC hNd hm2 hm3 ↦ ?_⟩
  have hν := hw.meas.lapNorm
  obtain ⟨hfs, -, hli, hcont, hlap⟩ := multPot_props_disc hw hη hρ₀ hC hNd hm2 hm3
  have hwk : IsWeakLogModulus 𝔻 (nodeCount Λ)
      (fun z ↦ ψ z + multPot kerDisc (lapNorm μ) R Λ z) := ⟨hfs, hli, hcont, hlap⟩
  have hΩ : ∀ z ∈ 𝔻, ∃ r, dist z 0 < r ∧ closedBall (0 : ℂ) r ⊆ 𝔻 := by
    intro z hz
    have hz1 := norm_lt_one_of_mem_disc hz
    refine ⟨(‖z‖ + 1) / 2, by rw [dist_zero_right]; linarith,
      closedBall_subset_ball (by linarith)⟩
  obtain ⟨h, han, hnorm, hord⟩ := exists_analytic_norm_eq_exp_of_isWeakLogModulus hΩ hwk
  have hfinI : ∀ w ∈ 𝔻, {i | w ∈ Λ i}.Finite := fun w hw ↦
    (finite_nodeIdx_disc hν hη hC hNd (K := {w}) (singleton_subset_iff.2 hw)
      isCompact_singleton).subset fun i hi ↦ ⟨w, hi, rfl⟩
  have hnc : ∀ w ∈ 𝔻, nodeCount Λ w ≠ 0 ↔ w ∈ nodeSet Λ := fun w hw ↦
    nodeCount_ne_zero_iff (hfinI w hw)
  have hsub : nodeSet Λ ⊆ 𝔻 := fun w ⟨i, hi⟩ ↦ hNd.mem i w hi
  have hzero : ∀ w ∈ 𝔻, h w = 0 ↔ w ∈ nodeSet Λ := by
    intro w hw
    have e := (han w hw).analyticOrderAt_eq_zero
    rw [hord w hw] at e
    rw [← hnc w hw]
    constructor
    · intro h0 hn0; exact e.1 (by simp [hn0]) h0
    · intro hne; by_contra hh; exact hne (by exact_mod_cast e.2 hh)
  have hfinZ : ∀ K ⊆ 𝔻, IsCompact K → (K ∩ nodeSet Λ).Finite := by
    intro K hK hKc
    refine (hfs K hK hKc).subset fun w ⟨hwK, hwN⟩ ↦ ⟨hwK, ?_⟩
    exact (hnc w (hK hwK)).2 hwN
  refine ⟨h, han.differentiableOn, hzero, hord, fun z hz ↦ ?_⟩
  have hZ : {w | w ∈ 𝔻 ∧ h w = 0} = nodeSet Λ := by
    ext w
    exact ⟨fun ⟨hw, h0⟩ ↦ (hzero w hw).1 h0, fun hw ↦ ⟨hsub hw, (hzero w (hsub hw)).2 hw⟩⟩
  rw [hZ]
  obtain ⟨hrem, hest⟩ := hbd μ R c m Λ hw.meas hC hNd hm2 hm3
  have hρpos : 0 < massRadiusDisc μ z := (hcl μ hw.meas z hz z hz).1
  obtain ⟨hρρ', hρ'ρ⟩ := hρcomp μ hw.meas z hz
  obtain ⟨w₀, hw₀, hw₀d⟩ := hrem z hz
  obtain ⟨d, hdle, hdex⟩ := exists_min_hypDist hsub hfinZ hz hw₀
  rw [hypDistSet_eq_ofReal hdle hdex]
  have hd0 : 0 ≤ d := by
    obtain ⟨w, hw, hwd⟩ := hdex; exact (hypDist_nonneg _ _).trans hwd
  have hdC : d ≤ C * massRadiusDisc μ z := by
    rw [hCC]
    calc d ≤ hypDist z w₀ := hdle w₀ hw₀
      _ ≤ C₁ * massRadiusDisc (lapNorm μ) z := hw₀d
      _ ≤ C₁ * (Cρ * massRadiusDisc μ z) := mul_le_mul_of_nonneg_left hρ'ρ hC₁.le
      _ = (C₁ * Cρ) * massRadiusDisc μ z := by ring
      _ ≤ Cr * massRadiusDisc μ z :=
          mul_le_mul_of_nonneg_right (le_max_of_le_right (le_max_left _ _)) hρpos.le
  by_cases hzN : z ∈ nodeSet Λ
  · have hd : d = 0 := le_antisymm (by simpa using hdle z hzN) hd0
    have hh0 : h z = 0 := (hzero z hz).2 hzN
    subst hd
    refine ennreal_thm4_bounds (C := C) (by rw [← NNReal.coe_le_coe, hCC]; simpa using hCr1)
      le_rfl hρpos (x := ‖h z‖ * Real.exp (-ψ z)) (by positivity) ?_ ?_ hdC
    · rw [hh0, norm_zero, zero_mul, zero_div, zero_pow (by omega), mul_zero]
    · rw [hh0, norm_zero, zero_mul, zero_div, mul_zero]
  · have hn0 : nodeCount Λ z = 0 := by
      by_contra h0; exact hzN ((hnc z hz).1 h0)
    have hhz := hnorm z hz hn0
    have hx : ‖h z‖ * Real.exp (-ψ z) = Real.exp (multPot kerDisc (lapNorm μ) R Λ z) := by
      rw [hhz, ← Real.exp_add]; ring_nf
    obtain ⟨hlo, hhi⟩ := hest z hz hzN d hdle hdex
    have hdpos : 0 < d := by
      obtain ⟨w, hw, hwd⟩ := hdex
      have hwz : w ≠ z := fun e ↦ hzN (e ▸ hw)
      have : 0 < hypDist z w := lt_of_le_of_ne (hypDist_nonneg _ _) fun e ↦
        hwz ((hypDist_eq_zero_iff hz (hsub hw)).1 e.symm).symm
      linarith [hdle w hw]
    obtain ⟨e1, e2⟩ := exp_bounds_of_log hdpos hρpos hρρ' hρ'ρ hlo hhi
    have hCpos : 0 < Real.exp C₁ * Cρ ^ M := by positivity
    refine ennreal_thm4_bounds (C := C) (by rw [← NNReal.coe_le_coe, hCC]; simpa using hCr1)
      hd0 hρpos (by positivity) ?_ ?_ hdC
    · rw [hx, hCC]
      refine le_trans ?_ e1
      gcongr
      exact le_max_of_le_left (le_max_left _ _)
    · rw [hx, hCC]
      refine e2.trans ?_
      gcongr
      exact le_max_of_le_left (le_max_right _ _)

/-- The node set is countable. -/
theorem countable_nodeSet (Λ : ℕ → Multiset ℂ) : (nodeSet Λ).Countable := by
  have : nodeSet Λ = ⋃ i, {w | w ∈ Λ i} := by ext; simp [nodeSet]
  rw [this]
  exact countable_iUnion fun i ↦ (Λ i).finite_toSet.countable

theorem theorem4_disc_quant (Cd : ℝ≥0) (R₀ : ℝ) (hR₀ : 0 < R₀) :
    ∃ (M : ℕ) (C : ℝ≥0), 1 ≤ M ∧ 1 ≤ C ∧ ∀ (ψ : ℂ → ℝ) (μ : Measure ℂ),
      WeightClassDisc ψ μ Cd R₀ →
        ∃ h : ℂ → ℂ, DifferentiableOn ℂ h 𝔻 ∧ (∃ z₀ ∈ 𝔻, h z₀ ≠ 0) ∧
          Thm4BoundsDisc ψ μ h M C := by
  obtain ⟨a, A, ha, hA, hpart⟩ := lemma4_disc_quant Cd (15 * R₀) 12 (by norm_num)
  obtain ⟨Bl, -, hnodes⟩ := exists_nodes_disc A hA
  obtain ⟨ρ₀, B', hρ₀, hB', hnodes'⟩ := hnodes 0 le_rfl
  obtain ⟨M, C, hM, hC, hmult⟩ :=
    multiplier_of_nodes_disc Cd R₀ a A B' ρ₀ 12 hR₀ ha hA hB' hρ₀ (by norm_num)
  obtain ⟨C0, -, hcl⟩ := claim1_disc_quant Cd (15 * R₀) 0
  refine ⟨M, C, hM, hC, fun ψ μ hw ↦ ?_⟩
  have hν := hw.meas.lapNorm
  obtain ⟨R, hP⟩ := hpart (lapNorm μ) hν
  obtain ⟨c, hcells⟩ := hP.exists_cells
  have hpos : ∀ i, 0 < massRadiusDisc (lapNorm μ) (c i) := fun i ↦
    (hcl _ hν (c i) (hcells.center_mem' i) (c i) (hcells.center_mem' i)).1
  obtain ⟨m, Λ, hN, hm2, hm3, -, -⟩ := hnodes' (lapNorm μ) a R c hcells hpos (fun _ ↦ false)
  obtain ⟨h, hh, hzero, -, hb⟩ := hmult ψ μ hw R c m Λ hcells hN hm2 hm3
  refine ⟨h, hh, ?_, hb⟩
  have hvol : volume (𝔻 \ nodeSet Λ) ≠ 0 := by
    rw [measure_diff_null ((countable_nodeSet Λ).measure_zero volume)]
    exact (measure_ball_pos volume 0 one_pos).ne'
  obtain ⟨z₀, hz₀, hz₀N⟩ := nonempty_of_measure_ne_zero hvol
  exact ⟨z₀, hz₀, fun h0 ↦ hz₀N ((hzero z₀ hz₀).1 h0)⟩

theorem theorem4_plane_quant (Cd : ℝ≥0) (R₀ : ℝ) (hR₀ : 0 < R₀) :
    ∃ (M : ℕ) (C : ℝ≥0), 1 ≤ M ∧ 1 ≤ C ∧ ∀ (ψ : ℂ → ℝ) (μ : Measure ℂ),
      WeightClassPlane ψ μ Cd R₀ →
        ∃ h : ℂ → ℂ, Differentiable ℂ h ∧ (∃ z₀, h z₀ ≠ 0) ∧ Thm4BoundsPlane ψ μ h M C := by
  obtain ⟨a, A, ha, hA, hpart⟩ := lemma4_plane_quant Cd (15 * R₀) 12 (by norm_num)
  obtain ⟨M, C, hM, hC, hmult⟩ :=
    multiplier_of_nodes_plane Cd R₀ a A ((0 + 12) * A) 12 hR₀ ha hA (by positivity)
      (by norm_num)
  refine ⟨M, C, hM, hC, fun ψ μ hw ↦ ?_⟩
  have hν := hw.meas.lapNorm
  obtain ⟨R, hP⟩ := hpart (lapNorm μ) hν
  obtain ⟨c, hcells⟩ := hP.exists_cells
  obtain ⟨Λ, hN, -, -⟩ := exists_nodes_plane hcells hA.le 0 le_rfl (fun _ ↦ false)
  obtain ⟨h, hh, hzero, -, hb⟩ := hmult ψ μ hw R c (fun _ ↦ 3) Λ hcells hN (fun _ ↦ le_rfl)
  refine ⟨h, hh, ?_, hb⟩
  have hvol : volume (nodeSet Λ)ᶜ ≠ 0 := by
    rw [compl_eq_univ_diff, measure_diff_null ((countable_nodeSet Λ).measure_zero volume)]
    simp
  obtain ⟨z₀, hz₀N⟩ := nonempty_of_measure_ne_zero hvol
  exact ⟨z₀, fun h0 ↦ hz₀N ((hzero z₀).1 h0)⟩

/-- The fixed statement (comparator), from `theorem4_disc_quant`. -/
theorem theorem4_disc (ψ : ℂ → ℝ) (μ : Measure ℂ) (hψ : IsSubharmonicWeight 𝔻 ψ μ)
    (hd : IsLocallyDoublingDisc μ) (hm : ∃ R : ℝ, 0 < R ∧ ∀ z ∈ 𝔻, 1 < μ (hypBall z R)) :
    ∃ (h : ℂ → ℂ) (M : ℕ) (C : ℝ≥0), DifferentiableOn ℂ h 𝔻 ∧ (∃ z₀ ∈ 𝔻, h z₀ ≠ 0) ∧
      ∀ z ∈ 𝔻,
        C⁻¹ * (hypDistSet z {w | w ∈ 𝔻 ∧ h w = 0} / ENNReal.ofReal (massRadiusDisc μ z)) ^ M ≤
          ENNReal.ofReal (‖h z‖ * Real.exp (-ψ z)) ∧
        ENNReal.ofReal (‖h z‖ * Real.exp (-ψ z)) ≤
          C * (hypDistSet z {w | w ∈ 𝔻 ∧ h w = 0} / ENNReal.ofReal (massRadiusDisc μ z)) := by
  obtain ⟨R, hR, hmR⟩ := hm
  obtain ⟨Cd, hCd⟩ := hd
  have hw : WeightClassDisc ψ μ Cd R :=
    ⟨hψ, ⟨fun z hz r hr h2 ↦ hCd z hz r hr h2, hmR, fun K hK hKc ↦ hψ.finite_of_compact K hK hKc⟩⟩
  obtain ⟨M, C, -, -, hall⟩ := theorem4_disc_quant Cd R hR
  obtain ⟨h, hh, hz₀, hb⟩ := hall ψ μ hw
  exact ⟨h, M, C, hh, hz₀, fun z hz ↦ ⟨(hb z hz).1, (hb z hz).2.1⟩⟩

/-- The fixed statement (comparator), from `theorem4_plane_quant`. -/
theorem theorem4_plane (ψ : ℂ → ℝ) (μ : Measure ℂ) (hψ : IsSubharmonicWeight univ ψ μ)
    (hd : IsLocallyDoubling μ) (hm : ∃ R : ℝ, 0 < R ∧ ∀ z : ℂ, 1 < μ (ball z R)) :
    ∃ (h : ℂ → ℂ) (M : ℕ) (C : ℝ≥0), Differentiable ℂ h ∧ (∃ z₀, h z₀ ≠ 0) ∧
      ∀ z : ℂ,
        C⁻¹ * (edistSet z {w | h w = 0} / ENNReal.ofReal (massRadius μ z)) ^ M ≤
          ENNReal.ofReal (‖h z‖ * Real.exp (-ψ z)) ∧
        ENNReal.ofReal (‖h z‖ * Real.exp (-ψ z)) ≤
          C * (edistSet z {w | h w = 0} / ENNReal.ofReal (massRadius μ z)) := by
  obtain ⟨R, hR, hmR⟩ := hm
  obtain ⟨Cd, hCd⟩ := hd
  have hw : WeightClassPlane ψ μ Cd R :=
    ⟨hψ, ⟨fun z r hr h2 ↦ hCd z r hr h2, hmR,
      fun K hKc ↦ hψ.finite_of_compact K (subset_univ K) hKc⟩⟩
  obtain ⟨M, C, -, -, hall⟩ := theorem4_plane_quant Cd R hR
  obtain ⟨h, hh, hz₀, hb⟩ := hall ψ μ hw
  exact ⟨h, M, C, hh, hz₀, fun z ↦ ⟨(hb z).1, (hb z).2.1⟩⟩

end OC
