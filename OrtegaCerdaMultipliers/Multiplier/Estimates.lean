import OrtegaCerdaMultipliers.Multiplier.CellBounds
import OrtegaCerdaMultipliers.Multiplier.Kernel
import OrtegaCerdaMultipliers.Multiplier.Cells
import OrtegaCerdaMultipliers.Multiplier.NearField

/-!
# M08 (Multiplier) — The corrected estimates (2), (3) for `S`

See `blueprint/M08_Multiplier.md` §2.6.  Scaffold: statements, proofs `sorry`.
-/

open MeasureTheory Metric Set Complex
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace OC

/-! ### Helpers -/

/-- Splitting a tsum into a finite part and a bounded tail. -/
theorem abs_tsum_sub_sum_le {f : ℕ → ℝ} (hf : Summable fun i ↦ |f i|) (G : Finset ℕ) {C : ℝ}
    (hC : ∀ u : Finset ℕ, (∀ i ∈ u, i ∉ G) → ∑ i ∈ u, |f i| ≤ C) :
    |∑' i, f i - ∑ i ∈ G, f i| ≤ C := by
  set g : ℕ → ℝ := fun i ↦ if i ∈ G then f i else 0
  set h : ℕ → ℝ := fun i ↦ if i ∈ G then 0 else f i
  have hgs : Summable g := summable_of_ne_finset_zero (s := G) fun i hi ↦ by simp [g, hi]
  have hhabs : Summable fun i ↦ |h i| :=
    hf.of_nonneg_of_le (fun i ↦ abs_nonneg _) fun i ↦ by
      simp only [h]; split_ifs <;> simp
  have hhs : Summable h := hhabs.of_abs
  have hfg : ∑' i, f i = ∑' i, g i + ∑' i, h i := by
    rw [← hgs.tsum_add hhs]; congr 1; ext i; simp only [g, h]; split_ifs <;> simp
  have hg : ∑' i, g i = ∑ i ∈ G, f i := by
    rw [tsum_eq_sum (s := G) fun i hi ↦ by simp [g, hi]]
    exact Finset.sum_congr rfl fun i hi ↦ by simp [g, hi]
  rw [hfg, hg, add_sub_cancel_left]
  have h1 : |∑' i, h i| ≤ ∑' i, |h i| := by
    have := norm_tsum_le_tsum_norm (f := h) (by simpa [Real.norm_eq_abs] using hhabs)
    simpa [Real.norm_eq_abs] using this
  refine h1.trans (Real.tsum_le_of_sum_le (fun i ↦ abs_nonneg _) fun u ↦ ?_)
  calc ∑ i ∈ u, |h i| = ∑ i ∈ u.filter (· ∉ G), |f i| := by
        rw [Finset.sum_filter]; exact Finset.sum_congr rfl fun i _ ↦ by
          simp only [h]; split_ifs <;> simp_all
    _ ≤ C := hC _ fun i hi ↦ (Finset.mem_filter.1 hi).2

/-- `cellPot` with a constant subtracted from the kernel (`ν(R i) = N = #Λ i`). -/
theorem cellPot_eq_sub_const {k : ℂ → ℂ → ℝ} {ν : Measure ℂ} {R : ℕ → Set ℂ}
    {Λ : ℕ → Multiset ℂ} {i N : ℕ} {z : ℂ} (hcard : Multiset.card (Λ i) = N)
    (hmeas : ν (R i) = N) (hint : IntegrableOn (k z) (R i) ν) (L : ℝ) :
    cellPot k ν R Λ i z =
      ((Λ i).map fun w ↦ k z w - L).sum - ∫ ζ in R i, (k z ζ - L) ∂ν := by
  have hfin : ν (R i) < ∞ := by rw [hmeas]; exact ENNReal.natCast_lt_top N
  rw [cellPot, integral_sub hint (integrableOn_const hfin.ne), setIntegral_const,
    Multiset.sum_map_sub, Multiset.map_const', Multiset.sum_replicate, hcard]
  have : ν.real (R i) = N := by simp [Measure.real, hmeas]
  rw [this, smul_eq_mul, nsmul_eq_mul]
  ring

/-- Lower bound of a set integral through a lintegral bound of its negative part. -/
theorem neg_le_setIntegral {f : ℂ → ℝ} {s : Set ℂ} {μ : Measure ℂ} (hf : IntegrableOn f s μ)
    {g : ℂ → ℝ≥0∞} {C : ℝ} (hC : 0 ≤ C)
    (hpt : ∀ᵐ ζ ∂μ.restrict s, ENNReal.ofReal (-f ζ) ≤ g ζ)
    (hg : ∫⁻ ζ in s, g ζ ∂μ ≤ ENNReal.ofReal C) : -C ≤ ∫ ζ in s, f ζ ∂μ := by
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hf]
  have h1 : ∫⁻ ζ in s, ENNReal.ofReal (-f ζ) ∂μ ≤ ENNReal.ofReal C :=
    (lintegral_mono_ae hpt).trans hg
  have h2 : (∫⁻ ζ in s, ENNReal.ofReal (-f ζ) ∂μ).toReal ≤ C := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
    rwa [ENNReal.toReal_ofReal hC] at this
  have h3 : 0 ≤ (∫⁻ ζ in s, ENNReal.ofReal (f ζ) ∂μ).toReal := ENNReal.toReal_nonneg
  linarith

/-- Upper bound of a set integral by an a.e. constant bound. -/
theorem setIntegral_le_const_mul {f : ℂ → ℝ} {s : Set ℂ} {μ : Measure ℂ}
    (hf : IntegrableOn f s μ) (hs : μ s < ∞) {P : ℝ} (hpt : ∀ᵐ ζ ∂μ.restrict s, f ζ ≤ P) :
    ∫ ζ in s, f ζ ∂μ ≤ P * μ.real s := by
  have := setIntegral_mono_ae_restrict hf (integrableOn_const hs.ne) hpt
  rwa [setIntegral_const, smul_eq_mul, mul_comm] at this

/-- A finite double sum with one distinguished term. -/
theorem sum_multiset_le_of_distinguished {G : Finset ℕ} {Λ : ℕ → Multiset ℂ} {N : ℕ}
    (hcard : ∀ i, Multiset.card (Λ i) = N) {f : ℂ → ℝ} {P : ℝ} (hP : 0 ≤ P)
    (hf : ∀ i ∈ G, ∀ w ∈ Λ i, f w ≤ P) {i₀ : ℕ} (hi₀ : i₀ ∈ G) {w₀ : ℂ} (hw₀ : w₀ ∈ Λ i₀) :
    ∑ i ∈ G, ((Λ i).map f).sum ≤ f w₀ + (G.card + 1) * N * P := by
  have hbound : ∀ i ∈ G, ((Λ i).map f).sum ≤ N * P := by
    intro i hi
    calc ((Λ i).map f).sum ≤ ((Λ i).map fun _ ↦ P).sum :=
          Multiset.sum_map_le_sum_map _ _ fun w hw ↦ hf i hi w hw
      _ = N * P := by simp [Multiset.map_const', Multiset.sum_replicate, hcard i]
  rw [← Finset.add_sum_erase G _ hi₀]
  have h1 : ((Λ i₀).map f).sum ≤ f w₀ + N * P := by
    rw [← Multiset.cons_erase hw₀, Multiset.map_cons, Multiset.sum_cons]
    have hc : Multiset.card ((Λ i₀).erase w₀) ≤ N := by
      rw [← hcard i₀]; exact Multiset.card_le_card (Multiset.erase_le _ _)
    have : (((Λ i₀).erase w₀).map f).sum ≤ N * P := by
      calc (((Λ i₀).erase w₀).map f).sum ≤ (((Λ i₀).erase w₀).map fun _ ↦ P).sum :=
            Multiset.sum_map_le_sum_map _ _ fun w hw ↦
              hf i₀ hi₀ w (Multiset.mem_of_mem_erase hw)
        _ = Multiset.card ((Λ i₀).erase w₀) * P := by
            simp [Multiset.map_const', Multiset.sum_replicate]
        _ ≤ N * P := by gcongr
    linarith
  have h2 : ∑ i ∈ G.erase i₀, ((Λ i).map f).sum ≤ G.card * N * P := by
    calc ∑ i ∈ G.erase i₀, ((Λ i).map f).sum ≤ ∑ i ∈ G.erase i₀, (N * P : ℝ) :=
          Finset.sum_le_sum fun i hi ↦ hbound i (Finset.mem_of_mem_erase hi)
      _ = (G.erase i₀).card * (N * P) := by simp
      _ ≤ G.card * (N * P) := by
          gcongr; exact Finset.erase_subset _ _
      _ = G.card * N * P := by ring
  have hNP : 0 ≤ (N : ℝ) * P := by positivity
  nlinarith


/-- Estimate (2), corrected: `M log(d/ρ) − C ≤ S(z) ≤ log(d/ρ) + C` off the nodes, and
`d(z, Λ) ≤ C ρ(z)` everywhere.  Here `ρ = massRadius (lapNorm μ)`. -/
theorem multPot_bounds_plane (Cd : ℝ≥0) (R₀ η A B : ℝ) (N : ℕ) (hη : 0 < η) (hA : 0 < A)
    (hB : 0 ≤ B) (hN : 1 ≤ N) :
    ∃ (M : ℕ) (C : ℝ), 1 ≤ M ∧ 0 < C ∧ ∀ (μ : Measure ℂ) (R : ℕ → Set ℂ) (c : ℕ → ℂ)
      (m : ℕ → ℕ) (Λ : ℕ → Multiset ℂ), MeasClassPlane μ Cd R₀ →
      IsCells univ dist (massRadius (lapNorm μ)) (lapNorm μ) N η A R c →
      IsNodes univ dist (massRadius (lapNorm μ)) (lapNorm μ) N B R c m Λ → (∀ i, 3 ≤ m i) →
      (∀ z, ∃ w ∈ nodeSet Λ, dist z w ≤ C * massRadius (lapNorm μ) z) ∧
      ∀ z, z ∉ nodeSet Λ → ∀ d : ℝ, (∀ w ∈ nodeSet Λ, d ≤ dist z w) →
        (∃ w ∈ nodeSet Λ, dist z w ≤ d) →
        M * Real.log (d / massRadius (lapNorm μ) z) - C ≤ multPot kerPlane (lapNorm μ) R Λ z ∧
        multPot kerPlane (lapNorm μ) R Λ z ≤ Real.log (d / massRadius (lapNorm μ) z) + C := sorry

set_option maxHeartbeats 800000 in
/-- Estimate (3), corrected (disc, hyperbolic distance). -/
theorem multPot_bounds_disc (Cd : ℝ≥0) (R₀ η A B ρ₀ : ℝ) (N : ℕ) (hη : 0 < η) (hA : 0 < A)
    (hB : 0 ≤ B) (hρ₀ : 0 < ρ₀) (hN : 1 ≤ N) :
    ∃ (M : ℕ) (C : ℝ), 1 ≤ M ∧ 0 < C ∧ ∀ (μ : Measure ℂ) (R : ℕ → Set ℂ) (c : ℕ → ℂ)
      (m : ℕ → ℕ) (Λ : ℕ → Multiset ℂ), MeasClassDisc μ Cd R₀ →
      IsCells 𝔻 hypDist (massRadiusDisc (lapNorm μ)) (lapNorm μ) N η A R c →
      IsNodes 𝔻 hypDist (massRadiusDisc (lapNorm μ)) (lapNorm μ) N B R c m Λ →
      (∀ i, 2 ≤ m i) → (∀ i, massRadiusDisc (lapNorm μ) (c i) ≤ ρ₀ → 3 ≤ m i) →
      (∀ z ∈ 𝔻, ∃ w ∈ nodeSet Λ, hypDist z w ≤ C * massRadiusDisc (lapNorm μ) z) ∧
      ∀ z ∈ 𝔻, z ∉ nodeSet Λ → ∀ d : ℝ, (∀ w ∈ nodeSet Λ, d ≤ hypDist z w) →
        (∃ w ∈ nodeSet Λ, hypDist z w ≤ d) →
        M * Real.log (d / massRadiusDisc (lapNorm μ) z) - C ≤
            multPot kerDisc (lapNorm μ) R Λ z ∧
        multPot kerDisc (lapNorm μ) R Λ z ≤ Real.log (d / massRadiusDisc (lapNorm μ) z) + C := by
  set R₁ := 15 * R₀
  obtain ⟨K₀, Cnf, hK₀, hCnf0, hnn⟩ := nonNear_sum_le_disc Cd R₁ η A B ρ₀ N hη hA hB hρ₀
  obtain ⟨Mc, δ, C₃, hδ, hC₃, hcn⟩ := cells_near_disc Cd R₁ η A B K₀ hη hK₀
  obtain ⟨C1, -, hcl⟩ := claim1_disc_quant Cd R₁ 0
  set Smax := 2 * C₃ * max R₁ 0 + 1 with hSmaxdef
  have hSmax : 0 < Smax := by positivity
  obtain ⟨Cχ, hχ⟩ := christ_disc_quant Cd R₁ Smax
  obtain ⟨CB, hCB⟩ := measure_hypBall_massRadius_quant Cd R₁ (2 * C₃)
  set cS := min (1 / 5) (Real.tanh 1 / Smax) with hcSdef
  have hcS : 0 < cS := lt_min (by norm_num) (div_pos (tanh_pos' one_pos) hSmax)
  have hlcS : Real.log cS ≤ 0 := Real.log_nonpos hcS.le ((min_le_left _ _).trans (by norm_num))
  set P := max (Real.log C₃) 0 with hPdef
  have hP : 0 ≤ P := le_max_right _ _
  set c₀ := Real.log cS + Real.log (2 * C₃) with hc₀
  set M := N * Mc + 1 with hMdef
  set C := |Real.log (δ / 2)| + (Mc + 1) * N * P + Mc * ((Cχ : ℝ) * CB + |c₀| * N) + Cnf +
    M * P + Mc * N * |Real.log cS| + Mc * N * P + C₃ + 1 with hCdef
  refine ⟨M, C, by omega, by positivity, ?_⟩
  intro μ R c m Λ hμ hC hNd hm2 hm3
  have hν : MeasClassDisc (lapNorm μ) Cd R₁ := hμ.lapNorm
  set ν := lapNorm μ with hνdef
  set ρ := massRadiusDisc ν with hρdef
  have hcnz := fun z hz ↦ hcn ν N R c m Λ hν hN hC hNd z hz
  have hcard_pos : ∀ i, ∃ w, w ∈ Λ i := by
    intro i
    have : Multiset.card (Λ i) ≠ 0 := by rw [hNd.card i]; omega
    obtain ⟨w, hw⟩ := Multiset.card_pos_iff_exists_mem.1 (Nat.pos_of_ne_zero this)
    exact ⟨w, hw⟩
  have hC3C : C₃ ≤ C := by
    have h1 : 0 ≤ |Real.log (δ / 2)| + (Mc + 1) * N * P + Mc * ((Cχ : ℝ) * CB + |c₀| * N) + Cnf +
        M * P + Mc * N * |Real.log cS| + Mc * N * P := by positivity
    linarith
  constructor
  · intro z hz
    obtain ⟨-, hC3, -, ⟨i₀, -, hnear⟩⟩ := hcnz z hz
    obtain ⟨w, hw⟩ := hcard_pos i₀
    have hρz : 0 < ρ z := (hcl ν hν z hz z hz).1
    exact ⟨w, ⟨i₀, hw⟩, (hC3 i₀ hnear w (Or.inr hw)).trans
      (mul_le_mul_of_nonneg_right hC3C hρz.le)⟩
  intro z hz hzN d hdle hdex
  obtain ⟨hcnt, hC3, hC4, -⟩ := hcnz z hz
  have hρz : 0 < ρ z := (hcl ν hν z hz z hz).1
  have hρzR : ρ z ≤ R₁ := (hcl ν hν z hz z hz).2.1
  set G0 := {i | hypDist z (c i) < K₀ * ρ (c i)} with hG0
  have hG0fin : G0.Finite := Set.finite_of_encard_le_coe hcnt
  set G := hG0fin.toFinset with hGdef
  have hGcard : G.card ≤ Mc := by
    have := hG0fin.encard_eq_coe_toFinset_card; rw [this] at hcnt; exact_mod_cast hcnt
  have hmemG : ∀ i, i ∈ G ↔ hypDist z (c i) < K₀ * ρ (c i) := fun i ↦ Set.Finite.mem_toFinset _
  set L := Real.log (ρ z) with hL
  set S := multPot kerDisc ν R Λ z with hS
  -- the tail
  have hsum := summable_cellPot_disc hν hη hA hB hρ₀ hC hNd hm2 hm3 hz
  have htail : |S - ∑ i ∈ G, cellPot kerDisc ν R Λ i z| ≤ Cnf :=
    abs_tsum_sub_sum_le hsum G fun u hu ↦ hnn ν R c m Λ hν hC hNd hm2 hm3 z hz u fun i hi ↦ by
      have := hu i hi; rw [hmemG, not_lt] at this; exact this
  -- per-cell decomposition
  have hint := fun i ↦ integrableOn_kerDisc_cell hν hC i hz
  set T₁ := ∑ i ∈ G, ((Λ i).map fun w ↦ kerDisc z w - L).sum with hT₁
  set T₂ := ∑ i ∈ G, ∫ ζ in R i, (kerDisc z ζ - L) ∂ν with hT₂
  have hSG : ∑ i ∈ G, cellPot kerDisc ν R Λ i z = T₁ - T₂ := by
    rw [hT₁, hT₂, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ ↦
      cellPot_eq_sub_const (hNd.card i) (hC.measure_eq i) (hint i) L
  -- kernel bounds near `z`
  have hker : ∀ w ∈ 𝔻, kerDisc z w = Real.log (Real.tanh (hypDist z w)) := fun w hw ↦ by
    rw [kerDisc, ← tanh_hypDist hw hz, hypDist_comm]
  have hC3S : C₃ * ρ z ≤ Smax := by
    have : C₃ * ρ z ≤ C₃ * max R₁ 0 :=
      mul_le_mul_of_nonneg_left (hρzR.trans (le_max_left _ _)) hC₃.le
    have h2 : 0 ≤ C₃ * max R₁ 0 := by positivity
    rw [hSmaxdef]; linarith
  have hβpos : ∀ w ∈ 𝔻, w ≠ z → 0 < hypDist z w := fun w hw hwz ↦
    lt_of_le_of_ne (hypDist_nonneg _ _) fun h ↦ hwz ((hypDist_eq_zero_iff hz hw).1 h.symm).symm
  have hup : ∀ w ∈ 𝔻, w ≠ z → hypDist z w ≤ C₃ * ρ z →
      kerDisc z w - L ≤ Real.log (hypDist z w / ρ z) ∧ Real.log (hypDist z w / ρ z) ≤ P := by
    intro w hw hwz hβ
    have hb := hβpos w hw hwz
    refine ⟨?_, ?_⟩
    · rw [hker w hw, hL, Real.log_div hb.ne' hρz.ne']
      have := Real.log_le_log (tanh_pos' hb) (tanh_le_self hb.le)
      linarith
    · refine le_trans ?_ (le_max_left _ _)
      apply Real.log_le_log (by positivity)
      rw [div_le_iff₀ hρz]; exact hβ
  have hlow : ∀ w ∈ 𝔻, w ≠ z → hypDist z w ≤ C₃ * ρ z →
      Real.log cS + Real.log (hypDist z w / ρ z) ≤ kerDisc z w - L := by
    intro w hw hwz hβ
    have hb := hβpos w hw hwz
    have ht := mul_le_tanh hSmax hb.le (hβ.trans hC3S)
    rw [hker w hw, hL, ← Real.log_mul hcS.ne' (by positivity), ← Real.log_div (tanh_pos' hb).ne'
      hρz.ne', mul_div_assoc']
    gcongr
  set ℓ := Real.log (d / ρ z) with hℓ
  -- `d` is positive and at most `C₃ ρ(z)`
  have hdpos : 0 < d := by
    obtain ⟨w, ⟨i, hw⟩, hwd⟩ := hdex
    have hwz : w ≠ z := fun e ↦ hzN (e ▸ ⟨i, hw⟩)
    exact (hβpos w (hNd.mem i w hw) hwz).trans_le hwd
  have hdC₃ : d ≤ C₃ * ρ z := by
    obtain ⟨-, -, -, ⟨i₀, -, hnear⟩⟩ := hcnz z hz
    obtain ⟨w, hw⟩ := hcard_pos i₀
    exact (hdle w ⟨i₀, hw⟩).trans (hC3 i₀ hnear w (Or.inr hw))
  have hℓP : ℓ ≤ P := by
    refine le_trans ?_ (le_max_left _ _)
    apply Real.log_le_log (by positivity)
    rw [div_le_iff₀ hρz]; exact hdC₃
  -- facts on near nodes
  have hnode : ∀ i ∈ G, ∀ w ∈ Λ i, w ∈ 𝔻 ∧ w ≠ z ∧ hypDist z w ≤ C₃ * ρ z ∧ d ≤ hypDist z w :=
    fun i hi w hw ↦ ⟨hNd.mem i w hw, fun e ↦ hzN (e ▸ ⟨i, hw⟩),
      hC3 i ((hmemG i).1 hi) w (Or.inr hw), hdle w ⟨i, hw⟩⟩
  -- upper bound for `T₁`
  have hT₁up : T₁ ≤ ℓ + |Real.log (δ / 2)| + (Mc + 1) * N * P := by
    have hfP : ∀ i ∈ G, ∀ w ∈ Λ i, kerDisc z w - L ≤ P := fun i hi w hw ↦ by
      obtain ⟨h1, h2, h3, -⟩ := hnode i hi w hw
      exact (hup w h1 h2 h3).1.trans (hup w h1 h2 h3).2
    have hGc : ((G.card : ℝ) + 1) * N * P ≤ (Mc + 1) * N * P := by
      have : (G.card : ℝ) ≤ Mc := by exact_mod_cast hGcard
      gcongr
    by_cases hd2 : d < δ / 2 * ρ z
    · obtain ⟨w₀, ⟨i₀, hw₀⟩, hw₀d⟩ := hdex
      have hi₀ : i₀ ∈ G := by
        by_contra hi₀
        rw [hmemG, not_lt] at hi₀
        have := (hC4 i₀ hi₀).2 w₀ hw₀
        nlinarith
      have hw₀z : w₀ ≠ z := fun e ↦ hzN (e ▸ ⟨i₀, hw₀⟩)
      have h1 := sum_multiset_le_of_distinguished hNd.card hP hfP hi₀ hw₀
      obtain ⟨hw₀𝔻, -, hw₀C, -⟩ := hnode i₀ hi₀ w₀ hw₀
      have h2 : kerDisc z w₀ - L ≤ ℓ := by
        refine (hup w₀ hw₀𝔻 hw₀z hw₀C).1.trans ?_
        apply Real.log_le_log (div_pos (hβpos w₀ hw₀𝔻 hw₀z) hρz)
        exact div_le_div_of_nonneg_right hw₀d hρz.le
      have h3 := abs_nonneg (Real.log (δ / 2))
      linarith
    · push Not at hd2
      have h1 : T₁ ≤ (G.card + 1) * N * P := by
        calc T₁ ≤ ∑ i ∈ G, (N * P : ℝ) := Finset.sum_le_sum fun i hi ↦ by
              calc ((Λ i).map fun w ↦ kerDisc z w - L).sum ≤ ((Λ i).map fun _ ↦ P).sum :=
                    Multiset.sum_map_le_sum_map _ _ fun w hw ↦ hfP i hi w hw
                _ = N * P := by simp [Multiset.map_const', Multiset.sum_replicate, hNd.card i]
          _ = G.card * N * P := by rw [Finset.sum_const, nsmul_eq_mul]; ring
          _ ≤ (G.card + 1) * N * P := by
              have := mul_nonneg (Nat.cast_nonneg N : (0:ℝ) ≤ N) hP
              nlinarith
      have h2 : Real.log (δ / 2) ≤ ℓ := by
        apply Real.log_le_log (by positivity)
        rw [le_div_iff₀ hρz]; linarith
      have h3 := neg_abs_le (Real.log (δ / 2))
      linarith
  -- lower bound for `T₁`
  have hT₁low : M * ℓ - M * P - Mc * N * |Real.log cS| ≤ T₁ := by
    have h1 : (G.card * N : ℝ) * (Real.log cS + ℓ) ≤ T₁ := by
      calc (G.card * N : ℝ) * (Real.log cS + ℓ) = ∑ i ∈ G, (N * (Real.log cS + ℓ) : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul]; ring
        _ ≤ T₁ := Finset.sum_le_sum fun i hi ↦ by
            calc (N * (Real.log cS + ℓ) : ℝ) = ((Λ i).map fun _ ↦ Real.log cS + ℓ).sum := by
                  rw [Multiset.map_const', Multiset.sum_replicate, hNd.card i, nsmul_eq_mul]
              _ ≤ ((Λ i).map fun w ↦ kerDisc z w - L).sum :=
                  Multiset.sum_map_le_sum_map _ _ fun w hw ↦ by
                    obtain ⟨h1, h2, h3, h4⟩ := hnode i hi w hw
                    refine le_trans ?_ (hlow w h1 h2 h3)
                    have := Real.log_le_log (div_pos hdpos hρz)
                      (div_le_div_of_nonneg_right h4 hρz.le)
                    linarith
    have hGM : (G.card : ℝ) ≤ Mc := by exact_mod_cast hGcard
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have hn : (G.card * N : ℝ) ≤ Mc * N := mul_le_mul_of_nonneg_right hGM hN0
    have hMc : (M : ℝ) = (N : ℝ) * Mc + 1 := by
      simp only [hMdef, Nat.cast_add, Nat.cast_mul, Nat.cast_one]
    have hnM : (G.card * N : ℝ) ≤ M := by
      rw [hMc]; linarith [mul_comm (Mc : ℝ) N]
    have hn0 : (0 : ℝ) ≤ G.card * N := mul_nonneg (Nat.cast_nonneg _) hN0
    have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg _
    have hlog : -(Mc * N * |Real.log cS|) ≤ (G.card * N : ℝ) * Real.log cS := by
      rw [abs_of_nonpos hlcS]
      have := mul_le_mul_of_nonpos_right hn hlcS
      linarith
    have hℓpart : M * ℓ - M * P ≤ (G.card * N : ℝ) * ℓ := by
      by_cases hℓ0 : ℓ ≤ 0
      · have := mul_le_mul_of_nonpos_right hnM hℓ0
        have := mul_nonneg hM0 hP
        linarith
      · push Not at hℓ0
        have := mul_nonneg hn0 hℓ0.le
        have := mul_le_mul_of_nonneg_left hℓP hM0
        linarith
    have e : (G.card * N : ℝ) * (Real.log cS + ℓ) =
        (G.card * N : ℝ) * Real.log cS + (G.card * N : ℝ) * ℓ := by ring
    linarith
  -- bounds for `T₂`
  have hae : ∀ i, ∀ᵐ ζ ∂ν.restrict (R i), ζ ∈ R i ∧ ζ ≠ z := by
    intro i
    have h1 : ∀ᵐ ζ ∂ν, ζ ≠ z := by
      rw [ae_iff]; simpa using hν.measure_singleton hz
    filter_upwards [ae_restrict_mem (hC.measurableSet i), ae_restrict_of_ae h1] with ζ h1 h2
    exact ⟨h1, h2⟩
  have hRpt : ∀ i ∈ G, ∀ ζ ∈ R i, ζ ∈ 𝔻 ∧ hypDist z ζ ≤ C₃ * ρ z := fun i hi ζ hζ ↦
    ⟨hC.subset_univ i hζ, hC3 i ((hmemG i).1 hi) ζ (Or.inl hζ)⟩
  have hNreal : ∀ i, ν.real (R i) = N := fun i ↦ by simp [Measure.real, hC.measure_eq i]
  have hT₂up : T₂ ≤ Mc * N * P := by
    calc T₂ ≤ ∑ i ∈ G, P * (N : ℝ) := Finset.sum_le_sum fun i hi ↦ by
          rw [← hNreal i]
          refine setIntegral_le_const_mul ((hint i).sub (integrableOn_const
            (hC.measure_lt_top i).ne)) (hC.measure_lt_top i) ?_
          filter_upwards [hae i] with ζ hζ
          obtain ⟨h1, h2⟩ := hRpt i hi ζ hζ.1
          exact (hup ζ h1 hζ.2 h2).1.trans (hup ζ h1 hζ.2 h2).2
      _ = G.card * N * P := by rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ Mc * N * P := by
          have : (G.card : ℝ) ≤ Mc := by exact_mod_cast hGcard
          gcongr
  have hT₂low : -(Mc * ((Cχ : ℝ) * CB + |c₀| * N)) ≤ T₂ := by
    set s := 2 * C₃ * ρ z with hs
    have hs0 : 0 < s := by positivity
    have hsS : s ≤ Smax := by
      have : s ≤ 2 * C₃ * max R₁ 0 :=
        mul_le_mul_of_nonneg_left (hρzR.trans (le_max_left _ _)) (by positivity)
      linarith
    have hchr := hχ ν hν z hz s hs0 hsS
    have hball := hCB ν hν z hz
    have hlint : ∫⁻ ζ in hypBall z s, ENNReal.ofReal (Real.log (s / hypDist z ζ)) ∂ν ≤
        ENNReal.ofReal ((Cχ : ℝ) * CB) := by
      refine hchr.trans ?_
      rw [ENNReal.ofReal_mul (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal,
        ENNReal.ofReal_coe_nnreal]
      gcongr
    have hcell : ∀ i ∈ G, c₀ * N - (Cχ : ℝ) * CB ≤ ∫ ζ in R i, (kerDisc z ζ - L) ∂ν := by
      intro i hi
      have hsub : R i ⊆ hypBall z s := fun ζ hζ ↦ by
        obtain ⟨h1, h2⟩ := hRpt i hi ζ hζ
        exact ⟨h1, h2.trans_lt (by rw [hs]; nlinarith)⟩
      have hI : IntegrableOn (fun ζ ↦ kerDisc z ζ - L) (R i) ν :=
        (hint i).sub (integrableOn_const (hC.measure_lt_top i).ne)
      have hI' : IntegrableOn (fun ζ ↦ kerDisc z ζ - L - c₀) (R i) ν :=
        hI.sub (integrableOn_const (hC.measure_lt_top i).ne)
      have h1 := neg_le_setIntegral hI' (g := fun ζ ↦ ENNReal.ofReal (Real.log (s / hypDist z ζ)))
        (by positivity) (by
          filter_upwards [hae i] with ζ hζ
          obtain ⟨h1, h2⟩ := hRpt i hi ζ hζ.1
          apply ENNReal.ofReal_le_ofReal
          have hb := hβpos ζ h1 hζ.2
          have hl := hlow ζ h1 hζ.2 h2
          have e : Real.log (s / hypDist z ζ) =
              Real.log (2 * C₃) - Real.log (hypDist z ζ / ρ z) := by
            rw [hs, Real.log_div (by positivity) hb.ne', Real.log_div hb.ne' hρz.ne',
              Real.log_mul (by positivity) hρz.ne']
            ring
          rw [e]
          linarith [hl, hc₀])
        ((lintegral_mono_set hsub).trans hlint)
      have e2 : ∫ ζ in R i, (kerDisc z ζ - L - c₀) ∂ν =
          ∫ ζ in R i, (kerDisc z ζ - L) ∂ν - c₀ * N := by
        have := integral_sub (μ := ν.restrict (R i)) (f := fun ζ ↦ kerDisc z ζ - L)
          (g := fun _ ↦ c₀) hI (integrableOn_const (hC.measure_lt_top i).ne)
        rw [this, setIntegral_const, hNreal i, smul_eq_mul, mul_comm]
      rw [e2] at h1
      linarith
    calc -(Mc * ((Cχ : ℝ) * CB + |c₀| * N)) ≤ -(G.card * ((Cχ : ℝ) * CB + |c₀| * N)) := by
          have : (G.card : ℝ) ≤ Mc := by exact_mod_cast hGcard
          have h0 : 0 ≤ (Cχ : ℝ) * CB + |c₀| * N := by positivity
          nlinarith
      _ = ∑ i ∈ G, (-((Cχ : ℝ) * CB + |c₀| * N)) := by rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ ∑ i ∈ G, (c₀ * N - (Cχ : ℝ) * CB) := Finset.sum_le_sum fun i _ ↦ by
          have := neg_abs_le c₀
          have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
          nlinarith
      _ ≤ T₂ := Finset.sum_le_sum hcell
  -- conclusion
  have htail' := abs_le.1 htail
  rw [hSG] at htail'
  constructor
  · have h0 : 0 ≤ |Real.log (δ / 2)| + (Mc + 1) * N * P + C₃ + 1 := by positivity
    have h1 : 0 ≤ (Mc : ℝ) * ((Cχ : ℝ) * CB + |c₀| * N) := by positivity
    rw [hCdef]; nlinarith
  · have h0 : 0 ≤ (M : ℝ) * P + Mc * N * |Real.log cS| + Mc * N * P + C₃ + 1 := by positivity
    rw [hCdef]; nlinarith

end OC
