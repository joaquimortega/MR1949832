/-
Copyright (c) 2026 Joaquim Ortega-Cerdà. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joaquim Ortega-Cerdà
-/
import OrtegaCerdaMultipliers.Multiplier.CellBounds
import OrtegaCerdaMultipliers.LogModulusWeak

/-!
# M08 (Multiplier) — Abstract assembly of the properties of the potential `S`

The plane and disc versions of the properties of `S = multPot k ν R Λ` (convergence, continuity
off the nodes, local integrability and the distributional Laplacian) follow the same argument.
It is carried out once here, for an abstract open set `U` and an abstract kernel `k`, from the
hypotheses packaged in `MultPotData`; `Potential.lean` then builds these data for the plane
(`U = univ`) and for the disc (`U = 𝔻`).
-/

open MeasureTheory Metric Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace OC

/-! ### Generic helper lemmas -/

/-- Integrability of `f · Δχ` for `f` integrable on `tsupport χ`. -/
theorem integrable_mul_laplacian {χ : ℂ → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hc : HasCompactSupport χ) {f : ℂ → ℝ} (hf : IntegrableOn f (tsupport χ)) :
    Integrable fun z ↦ f z * Laplacian.laplacian χ z := by
  obtain ⟨hΔc, hΔs⟩ := laplacian_testFunction hχ
  exact (hf.mul_continuousOn hΔc.continuousOn hc).integrable_of_forall_notMem_eq_zero
    fun z hz ↦ by simp [image_eq_zero_of_notMem_tsupport (fun h ↦ hz (hΔs h))]

/-- The finite sum of `χ` against node multiplicities, when `χ` vanishes on the nodes of all
multisets outside `G`. -/
theorem finsum_nodeCount_mul {Λ : ℕ → Multiset ℂ} {G : Finset ℕ} {χ : ℂ → ℝ}
    (hG : ∀ i, i ∉ G → ∀ w ∈ Λ i, χ w = 0) :
    ∑ᶠ ζ, (nodeCount Λ ζ : ℝ) * χ ζ = ∑ i ∈ G, ((Λ i).map χ).sum := by
  classical
  set Z := G.biUnion fun i ↦ (Λ i).toFinset
  have hcnt : ∀ ζ, χ ζ ≠ 0 → (Function.support fun i ↦ (Λ i).count ζ) ⊆ G := by
    intro ζ hχ i hi
    by_contra hiG
    exact hχ (hG i hiG ζ (Multiset.count_ne_zero.1 hi))
  have hsupp : (Function.support fun ζ ↦ (nodeCount Λ ζ : ℝ) * χ ζ) ⊆ Z := by
    intro ζ hζ
    have hχ : χ ζ ≠ 0 := fun h ↦ hζ (by simp [h])
    have hn : nodeCount Λ ζ ≠ 0 := fun h ↦ hζ (by simp [h])
    rw [nodeCount, finsum_eq_sum_of_support_subset _ (hcnt ζ hχ)] at hn
    obtain ⟨i, hi, hci⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
    exact Finset.mem_biUnion.2 ⟨i, hi, Multiset.mem_toFinset.2 (Multiset.count_ne_zero.1 hci)⟩
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  have hn : ∀ ζ ∈ Z, (nodeCount Λ ζ : ℝ) * χ ζ = ∑ i ∈ G, ((Λ i).count ζ : ℝ) * χ ζ := by
    intro ζ _
    by_cases hχ : χ ζ = 0
    · simp [hχ]
    rw [nodeCount, finsum_eq_sum_of_support_subset _ (hcnt ζ hχ), ← Finset.sum_mul]
    push_cast; rfl
  rw [Finset.sum_congr rfl hn, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hsub : (Λ i).toFinset ⊆ Z := fun ζ hζ ↦ Finset.mem_biUnion.2 ⟨i, hi, hζ⟩
  rw [Finset.sum_multiset_map_count (Λ i) χ, Finset.sum_subset hsub (fun ζ _ hζ ↦ by
    rw [Multiset.mem_toFinset, ← Multiset.count_eq_zero] at hζ; simp [hζ])]
  exact Finset.sum_congr rfl fun ζ _ ↦ by rw [nsmul_eq_mul]

/-- Splitting a summable real series into a finite part and the tail (with the finite part
replaced by `0`). -/
theorem tsum_eq_sum_add_tsum_ite {f : ℕ → ℝ} (hf : Summable f) (G : Finset ℕ) :
    ∑' i, f i = ∑ i ∈ G, f i + ∑' i, (if i ∈ G then 0 else f i) := by
  have hg : Summable fun i ↦ if i ∈ G then f i else 0 :=
    summable_of_ne_finset_zero (s := G) fun i hi ↦ by simp [hi]
  have hh : Summable fun i ↦ if i ∈ G then 0 else f i := by
    have := hf.sub hg
    refine this.congr fun i ↦ ?_
    by_cases hi : i ∈ G <;> simp [hi]
  have e : ∑' i, f i = ∑' i, ((if i ∈ G then f i else 0) + (if i ∈ G then 0 else f i)) := by
    congr 1; ext i; by_cases hi : i ∈ G <;> simp [hi]
  rw [e, hg.tsum_add hh, tsum_eq_sum (s := G) (fun i hi ↦ by simp [hi])]
  congr 1
  exact Finset.sum_congr rfl fun i hi ↦ by simp [hi]

/-! ### The abstract data -/

/-- Hypotheses under which `ψ + multPot k ν R Λ` is a weak log-modulus datum on the open set `U`:
the local structure of the cells and nodes, the continuity and the distributional Laplacian of
the individual cell potentials, and those of the weight `ψ`. -/
structure MultPotData (U : Set ℂ) (ψ : ℂ → ℝ) (k : ℂ → ℂ → ℝ) (ν : Measure ℂ) (R : ℕ → Set ℂ)
    (Λ : ℕ → Multiset ℂ) : Prop where
  isOpen : IsOpen U
  nodes_mem : ∀ i, ∀ w ∈ Λ i, w ∈ U
  finite_nodeIdx : ∀ K ⊆ U, IsCompact K → {i | ∃ w ∈ Λ i, w ∈ K}.Finite
  summable : ∀ z ∈ U, Summable fun i ↦ cellPot k ν R Λ i z
  cell_continuousAt : ∀ i, ∀ z ∈ U, z ∉ Λ i → ContinuousAt (cellPot k ν R Λ i) z
  cell_integrableOn : ∀ i, ∀ K ⊆ U, IsCompact K → IntegrableOn (cellPot k ν R Λ i) K
  local_structure : ∀ K ⊆ U, IsCompact K → ∃ G : Finset ℕ, (∀ i ∉ G, ∀ w ∈ R i, w ∉ K) ∧
    (∀ i ∉ G, ∀ w ∈ Λ i, w ∉ K) ∧ ∃ u : ℕ → ℝ, (∀ i, 0 ≤ u i) ∧ Summable u ∧
      ∀ i ∉ G, ∀ z ∈ K, |cellPot k ν R Λ i z| ≤ u i
  measurableSet : ∀ i, MeasurableSet (R i)
  pairwise_disjoint : Pairwise (Function.onFun Disjoint R)
  iUnion_eq : ⋃ i, R i = U
  measure_lt_top : ∀ K ⊆ U, IsCompact K → ν K < ∞
  weight_continuousOn : ContinuousOn ψ U
  laplacian_cell : ∀ χ : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ → tsupport χ ⊆ U →
    ∀ i, Integrable (fun z ↦ cellPot k ν R Λ i z * Laplacian.laplacian χ z) ∧
      ∫ z, cellPot k ν R Λ i z * Laplacian.laplacian χ z =
        2 * Real.pi * (((Λ i).map χ).sum - ∫ ζ in R i, χ ζ ∂ν)
  laplacian_weight : ∀ χ : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ → tsupport χ ⊆ U →
    ∫ z, ψ z * Laplacian.laplacian χ z = 2 * Real.pi * ∫ ζ, χ ζ ∂ν

namespace MultPotData

variable {U : Set ℂ} {ψ : ℂ → ℝ} {k : ℂ → ℂ → ℝ} {ν : Measure ℂ} {R : ℕ → Set ℂ}
  {Λ : ℕ → Multiset ℂ}

/-- Away from a finite set of cells, the tail of the series is continuous on a compact `K ⊆ U`
(together with the uniform summable bound). -/
theorem local_tail (h : MultPotData U ψ k ν R Λ) {K : Set ℂ} (hK : K ⊆ U) (hKc : IsCompact K) :
    ∃ G : Finset ℕ, (∀ i ∉ G, ∀ w ∈ R i, w ∉ K) ∧ (∀ i ∉ G, ∀ w ∈ Λ i, w ∉ K) ∧
      ∃ u : ℕ → ℝ, (∀ i, 0 ≤ u i) ∧ Summable u ∧
        (∀ i ∉ G, ∀ z ∈ K, |cellPot k ν R Λ i z| ≤ u i) ∧
        ContinuousOn (fun z ↦ ∑' i, if i ∈ G then 0 else cellPot k ν R Λ i z) K := by
  obtain ⟨G, hGR, hGΛ, u, hu0, hus, hub⟩ := h.local_structure K hK hKc
  refine ⟨G, hGR, hGΛ, u, hu0, hus, hub, ?_⟩
  refine continuousOn_tsum (u := u) (fun i ↦ ?_) hus fun i z hz ↦ ?_
  · by_cases hi : i ∈ G
    · simp only [hi, ite_true]; exact continuousOn_const
    · simp only [hi, ite_false]
      intro z hz
      exact (h.cell_continuousAt i z (hK hz) (fun hzΛ ↦ hGΛ i hi z hzΛ hz)).continuousWithinAt
  · by_cases hi : i ∈ G
    · simp only [hi, ite_true, norm_zero]; exact hu0 i
    · simp only [hi, ite_false, Real.norm_eq_abs]; exact hub i hi z hz

/-- Decomposition of `S` into a finite part and the tail. -/
theorem multPot_eq (h : MultPotData U ψ k ν R Λ) (G : Finset ℕ) {z : ℂ} (hz : z ∈ U) :
    multPot k ν R Λ z = ∑ i ∈ G, cellPot k ν R Λ i z +
      ∑' i, (if i ∈ G then 0 else cellPot k ν R Λ i z) :=
  tsum_eq_sum_add_tsum_ite (h.summable z hz) G

/-- `S` is integrable on compact subsets of `U`. -/
theorem integrableOn_multPot (h : MultPotData U ψ k ν R Λ) {K : Set ℂ} (hK : K ⊆ U)
    (hKc : IsCompact K) : IntegrableOn (multPot k ν R Λ) K := by
  obtain ⟨G, -, -, u, -, -, -, hT⟩ := h.local_tail hK hKc
  have hcells : IntegrableOn (fun z ↦ ∑ i ∈ G, cellPot k ν R Λ i z) K :=
    integrable_finsetSum G fun i _ ↦ h.cell_integrableOn i K hK hKc
  refine (hcells.add (hT.integrableOn_compact hKc)).congr_fun (fun z hz ↦ ?_)
    hKc.measurableSet
  simp only [Pi.add_apply]
  rw [h.multPot_eq G (hK hz)]

/-- Local finiteness of the nodes and the nonvanishing of `nodeCount` exactly at the nodes. -/
theorem nodeCount_ne_zero (h : MultPotData U ψ k ν R Λ) {w : ℂ} (hw : w ∈ U) :
    nodeCount Λ w ≠ 0 ↔ w ∈ nodeSet Λ :=
  nodeCount_ne_zero_iff ((h.finite_nodeIdx {w} (singleton_subset_iff.2 hw)
    isCompact_singleton).subset fun _ hi ↦ ⟨w, hi, rfl⟩)

/-- Local finiteness of the set of nodes. -/
theorem finite_nodes (h : MultPotData U ψ k ν R Λ) {K : Set ℂ} (hK : K ⊆ U) (hKc : IsCompact K) :
    (K ∩ Function.support (nodeCount Λ)).Finite := by
  refine ((h.finite_nodeIdx K hK hKc).biUnion fun i _ ↦ (Λ i).finite_toSet).subset ?_
  rintro w ⟨hwK, hw⟩
  obtain ⟨i, hi⟩ := (h.nodeCount_ne_zero (hK hwK)).1 hw
  exact mem_biUnion ⟨w, hi, hwK⟩ hi

/-- `ψ + S` is continuous off the nodes. -/
theorem continuousOn_off_nodes (h : MultPotData U ψ k ν R Λ) :
    ContinuousOn (fun z ↦ ψ z + multPot k ν R Λ z) (U \ Function.support (nodeCount Λ)) := by
  intro z₀ hz₀
  obtain ⟨hz₀U, hz₀n⟩ := hz₀
  have hz₀N : z₀ ∉ nodeSet Λ := fun hN ↦ hz₀n ((h.nodeCount_ne_zero hz₀U).2 hN)
  obtain ⟨K, hKc, hz₀K, hKU⟩ := exists_compact_subset h.isOpen hz₀U
  obtain ⟨G, -, -, u, -, -, -, hT⟩ := h.local_tail hKU hKc
  have hKn : K ∈ 𝓝 z₀ := mem_interior_iff_mem_nhds.1 hz₀K
  have hTat := hT.continuousAt hKn
  have hψat := h.weight_continuousOn.continuousAt (h.isOpen.mem_nhds hz₀U)
  have hGat : ContinuousAt (fun z ↦ ∑ i ∈ G, cellPot k ν R Λ i z) z₀ :=
    tendsto_finsetSum _ fun i _ ↦ h.cell_continuousAt i z₀ hz₀U fun hmem ↦ hz₀N ⟨i, hmem⟩
  have hsum := hψat.add (hGat.add hTat)
  refine (hsum.congr ?_).continuousWithinAt
  filter_upwards [hKn] with z hz
  rw [h.multPot_eq G (hKU hz)]; rfl

/-- `ψ + S` is locally integrable on `U`. -/
theorem locallyIntegrableOn (h : MultPotData U ψ k ν R Λ) :
    LocallyIntegrableOn (fun z ↦ ψ z + multPot k ν R Λ z) U := by
  refine (locallyIntegrableOn_iff h.isOpen.isLocallyClosed).2 fun K hK hKc ↦ ?_
  exact ((h.weight_continuousOn.mono hK).integrableOn_compact hKc).add
    (h.integrableOn_multPot hK hKc)

/-! #### The distributional Laplacian -/

/-- The integral of `χ` against `ν` as a finite sum over the cells meeting its support. -/
theorem integral_eq_sum_cells (h : MultPotData U ψ k ν R Λ) {χ : ℂ → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ U)
    {G : Finset ℕ} (hGR : ∀ i ∉ G, ∀ w ∈ R i, w ∉ tsupport χ) :
    ∫ ζ, χ ζ ∂ν = ∑ i ∈ G, ∫ ζ in R i, χ ζ ∂ν := by
  have hχ0 : ∀ w, w ∉ tsupport χ → χ w = 0 := fun w hw ↦ image_eq_zero_of_notMem_tsupport hw
  have hχint : Integrable χ ν := by
    obtain ⟨Dχ, hDχ⟩ := hχ.continuous.bounded_above_of_compact_support hc
    have hfinK : ν (tsupport χ) < ∞ := h.measure_lt_top _ hs hc
    exact (IntegrableOn.of_bound hfinK hχ.continuous.aestronglyMeasurable.restrict Dχ
      (Eventually.of_forall fun z ↦ hDχ z)).integrable_of_forall_notMem_eq_zero
      fun z hz ↦ hχ0 z hz
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := U) fun z hz ↦
    hχ0 z fun hz' ↦ hz (hs hz')]
  rw [← h.iUnion_eq, integral_iUnion h.measurableSet h.pairwise_disjoint
    (by rw [h.iUnion_eq]; exact hχint.integrableOn)]
  exact tsum_eq_sum fun i hi ↦
    setIntegral_eq_zero_of_forall_eq_zero fun ζ hζ ↦ hχ0 ζ (hGR i hi ζ hζ)

/-- Termwise integration of `S Δχ`: only the cells in `G` contribute. -/
theorem integral_multPot_mul_laplacian (h : MultPotData U ψ k ν R Λ) {χ : ℂ → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ U)
    {G : Finset ℕ} {u : ℕ → ℝ} (hu0 : ∀ i, 0 ≤ u i) (hus : Summable u)
    (hub : ∀ i ∉ G, ∀ z ∈ tsupport χ, |cellPot k ν R Λ i z| ≤ u i)
    (hGR : ∀ i ∉ G, ∀ w ∈ R i, w ∉ tsupport χ) (hGΛ : ∀ i ∉ G, ∀ w ∈ Λ i, w ∉ tsupport χ) :
    ∫ z, multPot k ν R Λ z * Laplacian.laplacian χ z =
      ∑ i ∈ G, 2 * Real.pi * (((Λ i).map χ).sum - ∫ ζ in R i, χ ζ ∂ν) := by
  obtain ⟨hΔc, hΔs⟩ := laplacian_testFunction hχ
  have hΔ0 : ∀ z, z ∉ tsupport χ → Laplacian.laplacian χ z = 0 := fun z hz ↦
    image_eq_zero_of_notMem_tsupport (fun h' ↦ hz (hΔs h'))
  have hχ0 : ∀ w, w ∉ tsupport χ → χ w = 0 := fun w hw ↦ image_eq_zero_of_notMem_tsupport hw
  have hcellΔ := h.laplacian_cell χ hχ hc hs
  have hΔint : Integrable fun z ↦ |Laplacian.laplacian χ z| :=
    (hΔc.integrable_of_hasCompactSupport (hc.mono' ((subset_tsupport _).trans hΔs))).abs
  have hbound : ∀ i ∉ G, ∀ z, ‖cellPot k ν R Λ i z * Laplacian.laplacian χ z‖ ≤
      u i * |Laplacian.laplacian χ z| := by
    intro i hi z
    by_cases hz : z ∈ tsupport χ
    · rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hub i hi z hz) (abs_nonneg _)
    · simp [hΔ0 z hz]
  set w : ℕ → ℝ := fun i ↦ if i ∈ G then
    ∫ z, ‖cellPot k ν R Λ i z * Laplacian.laplacian χ z‖
    else u i * ∫ z, |Laplacian.laplacian χ z| with hw'
  have hw0 : ∀ i, 0 ≤ w i := fun i ↦ by
    simp only [hw']; split_ifs
    · exact integral_nonneg fun _ ↦ norm_nonneg _
    · exact mul_nonneg (hu0 i) (integral_nonneg fun _ ↦ abs_nonneg _)
  have hws : Summable w := by
    have h1 : Summable fun i ↦ u i * ∫ z, |Laplacian.laplacian χ z| := hus.mul_right _
    have h2 : Summable fun i ↦ if i ∈ G then
        ∫ z, ‖cellPot k ν R Λ i z * Laplacian.laplacian χ z‖ else 0 :=
      summable_of_ne_finset_zero (s := G) fun i hi ↦ by simp [hi]
    refine (h1.add h2).of_nonneg_of_le hw0 fun i ↦ ?_
    simp only [hw']
    split_ifs with hi
    · have := mul_nonneg (hu0 i)
        (integral_nonneg (μ := volume) fun z ↦ abs_nonneg (Laplacian.laplacian χ z))
      linarith
    · simp
  have hlint : ∀ i, ∫⁻ z, ‖cellPot k ν R Λ i z * Laplacian.laplacian χ z‖ₑ ≤
      ENNReal.ofReal (w i) := by
    intro i
    by_cases hi : i ∈ G
    · simp only [hw', hi, ite_true]
      rw [ofReal_integral_norm_eq_lintegral_eNorm (hcellΔ i).1]
    · simp only [hw', hi, ite_false]
      rw [← integral_const_mul, ofReal_integral_eq_lintegral_ofReal (hΔint.const_mul (u i))
        (Eventually.of_forall fun z ↦ mul_nonneg (hu0 i) (abs_nonneg _))]
      refine lintegral_mono fun z ↦ ?_
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hbound i hi z)
  have htsum_ne : ∑' i, ∫⁻ z, ‖cellPot k ν R Λ i z * Laplacian.laplacian χ z‖ₑ ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (tsum_le_tsum hlint)
    rw [← ENNReal.ofReal_tsum_of_nonneg hw0 hws]
    exact ENNReal.ofReal_ne_top
  have hint_tsum := integral_tsum (fun i ↦ (hcellΔ i).1.aestronglyMeasurable) htsum_ne
  have hSΔ : ∀ z, multPot k ν R Λ z * Laplacian.laplacian χ z =
      ∑' i, cellPot k ν R Λ i z * Laplacian.laplacian χ z :=
    fun z ↦ by rw [multPot, tsum_mul_right]
  have hterm : ∀ i ∉ G, ∫ z, cellPot k ν R Λ i z * Laplacian.laplacian χ z = 0 := by
    intro i hi
    rw [(hcellΔ i).2]
    have h1 : ((Λ i).map χ).sum = 0 := Multiset.sum_eq_zero fun x hx ↦ by
      obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.1 hx
      exact hχ0 w (hGΛ i hi w hw)
    have h2 : ∫ ζ in R i, χ ζ ∂ν = 0 :=
      setIntegral_eq_zero_of_forall_eq_zero fun ζ hζ ↦ hχ0 ζ (hGR i hi ζ hζ)
    rw [h1, h2]; ring
  simp_rw [hSΔ]
  rw [hint_tsum, tsum_eq_sum (s := G) fun i hi ↦ hterm i hi]
  exact Finset.sum_congr rfl fun i _ ↦ (hcellΔ i).2

/-- The distributional Laplacian of `ψ + S` is `2π` times the sum of the Dirac masses at the
nodes. -/
theorem laplacian_eq (h : MultPotData U ψ k ν R Λ) {χ : ℂ → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ U) :
    ∫ z, (ψ z + multPot k ν R Λ z) * Laplacian.laplacian χ z =
      2 * Real.pi * ∑ᶠ ζ, (nodeCount Λ ζ : ℝ) * χ ζ := by
  obtain ⟨G, hGR, hGΛ, u, hu0, hus, hub, -⟩ := h.local_tail hs hc
  have hχ0 : ∀ w, w ∉ tsupport χ → χ w = 0 := fun w hw ↦ image_eq_zero_of_notMem_tsupport hw
  have hψint : Integrable fun z ↦ ψ z * Laplacian.laplacian χ z :=
    integrable_mul_laplacian hχ hc ((h.weight_continuousOn.mono hs).integrableOn_compact hc)
  have hSint : Integrable fun z ↦ multPot k ν R Λ z * Laplacian.laplacian χ z :=
    integrable_mul_laplacian hχ hc (h.integrableOn_multPot hs hc)
  have hS_int := h.integral_multPot_mul_laplacian hχ hc hs hu0 hus hub hGR hGΛ
  have hfin : ∑ᶠ ζ, (nodeCount Λ ζ : ℝ) * χ ζ = ∑ i ∈ G, ((Λ i).map χ).sum :=
    finsum_nodeCount_mul fun i hi w hw ↦ hχ0 w (hGΛ i hi w hw)
  have hsplit : ∫ z, (ψ z + multPot k ν R Λ z) * Laplacian.laplacian χ z =
      (∫ z, ψ z * Laplacian.laplacian χ z) +
        ∫ z, multPot k ν R Λ z * Laplacian.laplacian χ z := by
    have h' := integral_add hψint hSint
    refine Eq.trans ?_ h'
    congr 1; ext z; ring
  rw [hsplit, h.laplacian_weight χ hχ hc hs, hS_int, h.integral_eq_sum_cells hχ hc hs hGR, hfin,
    ← Finset.mul_sum, Finset.sum_sub_distrib]
  ring

/-- All the properties of `ψ + S` needed for the weak log-modulus datum. -/
theorem props (h : MultPotData U ψ k ν R Λ) :
    (∀ K ⊆ U, IsCompact K → (K ∩ Function.support (nodeCount Λ)).Finite) ∧
    (∀ z ∈ U, Summable fun i ↦ cellPot k ν R Λ i z) ∧
    LocallyIntegrableOn (fun z ↦ ψ z + multPot k ν R Λ z) U ∧
    ContinuousOn (fun z ↦ ψ z + multPot k ν R Λ z) (U \ Function.support (nodeCount Λ)) ∧
    ∀ χ : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ → tsupport χ ⊆ U →
      ∫ z, (ψ z + multPot k ν R Λ z) * Laplacian.laplacian χ z =
        2 * Real.pi * ∑ᶠ ζ, (nodeCount Λ ζ : ℝ) * χ ζ :=
  ⟨fun _ hK hKc ↦ h.finite_nodes hK hKc, h.summable, h.locallyIntegrableOn,
    h.continuousOn_off_nodes, fun _ hχ hc hs ↦ h.laplacian_eq hχ hc hs⟩

end MultPotData

end OC
