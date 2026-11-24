/-
Copyright (c) 2026 Joaquim Ortega-Cerdà. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joaquim Ortega-Cerdà
-/
import OrtegaCerdaMultipliers.Multiplier.CellBounds
import OrtegaCerdaMultipliers.Multiplier.Kernel
import OrtegaCerdaMultipliers.Multiplier.Cells
import OrtegaCerdaMultipliers.Multiplier.NearField

/-!
# M08 (Multiplier) — The corrected estimates (2), (3) for `S`

See `blueprint/M08_Multiplier.md` §2.6, §3.9.
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
    calc ∑ i ∈ G.erase i₀, ((Λ i).map f).sum ≤ ∑ _ ∈ G.erase i₀, (N * P : ℝ) :=
          Finset.sum_le_sum fun i hi ↦ hbound i (Finset.mem_of_mem_erase hi)
      _ = (G.erase i₀).card * (N * P) := by simp
      _ ≤ G.card * (N * P) := by
          gcongr; exact Finset.erase_subset _ _
      _ = G.card * N * P := by ring
  nlinarith


/-! ### Kernel-free estimates for the sums over the near cells -/

/-- Upper bound for the node sums over the near cells `G`. -/
theorem sum_map_le_upper {G : Finset ℕ} {Λ : ℕ → Multiset ℂ} {N Mc : ℕ}
    (hcard : ∀ i, Multiset.card (Λ i) = N) {f : ℂ → ℝ} {P ℓ a : ℝ} (hP : 0 ≤ P)
    (hG : G.card ≤ Mc) (hfP : ∀ i ∈ G, ∀ w ∈ Λ i, f w ≤ P)
    (hcase : (∃ i₀ ∈ G, ∃ w₀ ∈ Λ i₀, f w₀ ≤ ℓ) ∨ a ≤ ℓ) :
    ∑ i ∈ G, ((Λ i).map f).sum ≤ ℓ + |a| + (Mc + 1) * N * P := by
  have hGc : ((G.card : ℝ) + 1) * N * P ≤ (Mc + 1) * N * P := by
    have : (G.card : ℝ) ≤ Mc := by exact_mod_cast hG
    gcongr
  rcases hcase with ⟨i₀, hi₀, w₀, hw₀, hf⟩ | ha
  · have h1 := sum_multiset_le_of_distinguished hcard hP hfP hi₀ hw₀
    have h3 := abs_nonneg a
    linarith
  · have h1 : ∑ i ∈ G, ((Λ i).map f).sum ≤ (G.card + 1) * N * P := by
      calc ∑ i ∈ G, ((Λ i).map f).sum ≤ ∑ _ ∈ G, (N * P : ℝ) :=
            Finset.sum_le_sum fun i hi ↦ by
              calc ((Λ i).map f).sum ≤ ((Λ i).map fun _ ↦ P).sum :=
                    Multiset.sum_map_le_sum_map _ _ fun w hw ↦ hfP i hi w hw
                _ = N * P := by simp [Multiset.map_const', Multiset.sum_replicate, hcard i]
        _ = G.card * N * P := by rw [Finset.sum_const, nsmul_eq_mul]; ring
        _ ≤ (G.card + 1) * N * P := by
            have := mul_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N) hP
            linarith
    have h3 := neg_abs_le a
    linarith

/-- Lower bound for the node sums over the near cells `G`. -/
theorem sum_map_ge_lower {G : Finset ℕ} {Λ : ℕ → Multiset ℂ} {N Mc : ℕ}
    (hcard : ∀ i, Multiset.card (Λ i) = N) {f : ℂ → ℝ} {P ℓ lc : ℝ} (hP : 0 ≤ P)
    (hlc : lc ≤ 0) (hℓP : ℓ ≤ P) (hG : G.card ≤ Mc)
    (hlow : ∀ i ∈ G, ∀ w ∈ Λ i, lc + ℓ ≤ f w) :
    ((N : ℝ) * Mc + 1) * ℓ - ((N : ℝ) * Mc + 1) * P - Mc * N * |lc| ≤
      ∑ i ∈ G, ((Λ i).map f).sum := by
  have h1 : (G.card * N : ℝ) * (lc + ℓ) ≤ ∑ i ∈ G, ((Λ i).map f).sum := by
    calc (G.card * N : ℝ) * (lc + ℓ) = ∑ _ ∈ G, (N * (lc + ℓ) : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ ∑ i ∈ G, ((Λ i).map f).sum := Finset.sum_le_sum fun i hi ↦ by
          calc (N * (lc + ℓ) : ℝ) = ((Λ i).map fun _ ↦ lc + ℓ).sum := by
                rw [Multiset.map_const', Multiset.sum_replicate, hcard i, nsmul_eq_mul]
            _ ≤ ((Λ i).map f).sum :=
                Multiset.sum_map_le_sum_map _ _ fun w hw ↦ hlow i hi w hw
  have hGM : (G.card : ℝ) ≤ Mc := by exact_mod_cast hG
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hn : (G.card * N : ℝ) ≤ Mc * N := mul_le_mul_of_nonneg_right hGM hN0
  have hnM : (G.card * N : ℝ) ≤ N * Mc + 1 := by linarith [mul_comm (Mc : ℝ) N]
  have hn0 : (0 : ℝ) ≤ G.card * N := mul_nonneg (Nat.cast_nonneg _) hN0
  have hM0 : (0 : ℝ) ≤ N * Mc + 1 := by positivity
  have hlog : -(Mc * N * |lc|) ≤ (G.card * N : ℝ) * lc := by
    rw [abs_of_nonpos hlc]
    have := mul_le_mul_of_nonpos_right hn hlc
    linarith
  have hℓpart : (N * Mc + 1) * ℓ - (N * Mc + 1) * P ≤ (G.card * N : ℝ) * ℓ := by
    by_cases hℓ0 : ℓ ≤ 0
    · have := mul_le_mul_of_nonpos_right hnM hℓ0
      have := mul_nonneg hM0 hP
      linarith
    · push Not at hℓ0
      have := mul_nonneg hn0 hℓ0.le
      have := mul_le_mul_of_nonneg_left hℓP hM0
      linarith
  linarith

/-- Upper bound for the integrals of the kernel over the near cells `G`. -/
theorem sum_setIntegral_le_bound {ν : Measure ℂ} {R : ℕ → Set ℂ} {N Mc : ℕ} {G : Finset ℕ}
    (hνR : ∀ i, ν (R i) = N) {g : ℂ → ℝ} {P : ℝ} (hP : 0 ≤ P) (hG : G.card ≤ Mc)
    (hint : ∀ i ∈ G, IntegrableOn g (R i) ν)
    (hae : ∀ i ∈ G, ∀ᵐ ζ ∂ν.restrict (R i), g ζ ≤ P) :
    ∑ i ∈ G, ∫ ζ in R i, g ζ ∂ν ≤ Mc * N * P := by
  have hNreal : ∀ i, ν.real (R i) = N := fun i ↦ by simp [Measure.real, hνR i]
  have hlt : ∀ i, ν (R i) < ∞ := fun i ↦ by rw [hνR i]; exact ENNReal.natCast_lt_top N
  calc ∑ i ∈ G, ∫ ζ in R i, g ζ ∂ν ≤ ∑ _ ∈ G, P * (N : ℝ) := Finset.sum_le_sum fun i hi ↦ by
        rw [← hNreal i]
        exact setIntegral_le_const_mul (hint i hi) (hlt i) (hae i hi)
    _ = G.card * N * P := by rw [Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ Mc * N * P := by
        have : (G.card : ℝ) ≤ Mc := by exact_mod_cast hG
        gcongr

/-- Lower bound for the integrals of the kernel over the near cells `G`, from a bound of the
negative part by a lintegral over a set `B` containing the cells. -/
theorem sum_setIntegral_ge_bound {ν : Measure ℂ} {R : ℕ → Set ℂ} {N Mc : ℕ} {G : Finset ℕ}
    (hνR : ∀ i, ν (R i) = N) {g : ℂ → ℝ} {B : Set ℂ} {gg : ℂ → ℝ≥0∞} {c₀ Cx : ℝ}
    (hCx : 0 ≤ Cx) (hG : G.card ≤ Mc) (hint : ∀ i ∈ G, IntegrableOn g (R i) ν)
    (hsub : ∀ i ∈ G, R i ⊆ B) (hlint : ∫⁻ ζ in B, gg ζ ∂ν ≤ ENNReal.ofReal Cx)
    (hpt : ∀ i ∈ G, ∀ᵐ ζ ∂ν.restrict (R i), ENNReal.ofReal (-(g ζ - c₀)) ≤ gg ζ) :
    -(Mc * (Cx + |c₀| * N)) ≤ ∑ i ∈ G, ∫ ζ in R i, g ζ ∂ν := by
  have hNreal : ∀ i, ν.real (R i) = N := fun i ↦ by simp [Measure.real, hνR i]
  have hlt : ∀ i, ν (R i) < ∞ := fun i ↦ by rw [hνR i]; exact ENNReal.natCast_lt_top N
  have hcell : ∀ i ∈ G, c₀ * N - Cx ≤ ∫ ζ in R i, g ζ ∂ν := by
    intro i hi
    have hI' : IntegrableOn (fun ζ ↦ g ζ - c₀) (R i) ν :=
      (hint i hi).sub (integrableOn_const (hlt i).ne)
    have h1 := neg_le_setIntegral hI' hCx (hpt i hi) ((lintegral_mono_set (hsub i hi)).trans hlint)
    have e2 : ∫ ζ in R i, (g ζ - c₀) ∂ν = ∫ ζ in R i, g ζ ∂ν - c₀ * N := by
      have := integral_sub (μ := ν.restrict (R i)) (f := g) (g := fun _ ↦ c₀) (hint i hi)
        (integrableOn_const (hlt i).ne)
      rw [this, setIntegral_const, hNreal i, smul_eq_mul, mul_comm]
    rw [e2] at h1
    linarith only [h1]
  have hGM : (G.card : ℝ) ≤ Mc := by exact_mod_cast hG
  calc -(Mc * (Cx + |c₀| * N)) ≤ -(G.card * (Cx + |c₀| * N)) := by
        have h0 : 0 ≤ Cx + |c₀| * N := by positivity
        exact neg_le_neg (mul_le_mul_of_nonneg_right hGM h0)
    _ = ∑ _ ∈ G, (-(Cx + |c₀| * N)) := by rw [Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ ∑ _ ∈ G, (c₀ * N - Cx) := Finset.sum_le_sum fun _ _ ↦ by
        have := neg_abs_le c₀
        have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
        have h5 := mul_le_mul_of_nonneg_right this hN0
        linarith only [h5]
    _ ≤ ∑ i ∈ G, ∫ ζ in R i, g ζ ∂ν := Finset.sum_le_sum hcell

/-- The kernel-free core of estimates (2), (3): everything is expressed through the distance
`D = d(z, ·)`, the kernel minus `log ρ(z)` (called `g`) and its pointwise bounds on the points
within `C₃ ρ(z)` of `z`. -/
theorem multPot_bounds_core {Ω : Set ℂ} {D g : ℂ → ℝ} {z : ℂ} {ν : Measure ℂ} {R : ℕ → Set ℂ}
    {Λ : ℕ → Multiset ℂ} {N Mc : ℕ} {G : Finset ℕ} {B : Set ℂ}
    {ρz C₃ δ d P lc Cx Cnf S : ℝ}
    (hcard : ∀ i, Multiset.card (Λ i) = N) (hνR : ∀ i, ν (R i) = N)
    (hmeas : ∀ i, MeasurableSet (R i)) (hρz : 0 < ρz) (hC₃ : 0 < C₃) (hδ : 0 < δ)
    (hP : 0 ≤ P) (hlc : lc ≤ 0) (hCx : 0 ≤ Cx) (hG : G.card ≤ Mc)
    (hDpos : ∀ w ∈ Ω, w ≠ z → 0 < D w)
    (hglog : ∀ w ∈ Ω, w ≠ z → D w ≤ C₃ * ρz → g w ≤ Real.log (D w / ρz))
    (hglow : ∀ w ∈ Ω, w ≠ z → D w ≤ C₃ * ρz → lc + Real.log (D w / ρz) ≤ g w)
    (hPlog : ∀ x : ℝ, 0 < x → x ≤ C₃ → Real.log x ≤ P)
    (hΛΩ : ∀ i, ∀ w ∈ Λ i, w ∈ Ω) (hΛz : ∀ i, ∀ w ∈ Λ i, w ≠ z)
    (hnear : ∀ i ∈ G, ∀ w ∈ Λ i, D w ≤ C₃ * ρz)
    (hfar : ∀ i ∉ G, ∀ w ∈ Λ i, δ * ρz ≤ 2 * D w)
    (hdle : ∀ i, ∀ w ∈ Λ i, d ≤ D w) (hdex : ∃ i, ∃ w ∈ Λ i, D w ≤ d) (hdC₃ : d ≤ C₃ * ρz)
    (hRpt : ∀ i ∈ G, ∀ ζ ∈ R i, ζ ∈ Ω ∧ D ζ ≤ C₃ * ρz) (hae : ∀ᵐ ζ ∂ν, ζ ≠ z)
    (hint : ∀ i ∈ G, IntegrableOn g (R i) ν) (hsub : ∀ ζ ∈ Ω, D ζ ≤ C₃ * ρz → ζ ∈ B)
    (hlint : ∫⁻ ζ in B, ENNReal.ofReal (Real.log (2 * C₃ * ρz / D ζ)) ∂ν ≤ ENNReal.ofReal Cx)
    (hS : |S - ∑ i ∈ G, (((Λ i).map g).sum - ∫ ζ in R i, g ζ ∂ν)| ≤ Cnf) :
    ((N : ℝ) * Mc + 1) * Real.log (d / ρz) -
        (((N : ℝ) * Mc + 1) * P + Mc * N * |lc| + Mc * N * P + Cnf) ≤ S ∧
      S ≤ Real.log (d / ρz) + (|Real.log (δ / 2)| + (Mc + 1) * N * P +
        Mc * (Cx + |lc + Real.log (2 * C₃)| * N) + Cnf) := by
  have hdpos : 0 < d := by
    obtain ⟨i, w, hw, hwd⟩ := hdex
    exact (hDpos w (hΛΩ i w hw) (hΛz i w hw)).trans_le hwd
  have hℓP : Real.log (d / ρz) ≤ P :=
    hPlog _ (div_pos hdpos hρz) (by rw [div_le_iff₀ hρz]; exact hdC₃)
  have hPn : ∀ w ∈ Ω, w ≠ z → D w ≤ C₃ * ρz → Real.log (D w / ρz) ≤ P := fun w hw hwz hD ↦
    hPlog _ (div_pos (hDpos w hw hwz) hρz) (by rw [div_le_iff₀ hρz]; exact hD)
  have hfP : ∀ i ∈ G, ∀ w ∈ Λ i, g w ≤ P := fun i hi w hw ↦
    (hglog w (hΛΩ i w hw) (hΛz i w hw) (hnear i hi w hw)).trans
      (hPn w (hΛΩ i w hw) (hΛz i w hw) (hnear i hi w hw))
  have hcase : (∃ i₀ ∈ G, ∃ w₀ ∈ Λ i₀, g w₀ ≤ Real.log (d / ρz)) ∨
      Real.log (δ / 2) ≤ Real.log (d / ρz) := by
    by_cases hd2 : 2 * d < δ * ρz
    · left
      obtain ⟨i₀, w₀, hw₀, hw₀d⟩ := hdex
      have hi₀ : i₀ ∈ G := by
        by_contra hi₀
        have := hfar i₀ hi₀ w₀ hw₀
        have : 0 < δ * ρz := by positivity
        linarith
      refine ⟨i₀, hi₀, w₀, hw₀, (hglog w₀ (hΛΩ i₀ w₀ hw₀) (hΛz i₀ w₀ hw₀)
        (hnear i₀ hi₀ w₀ hw₀)).trans (Real.log_le_log ?_ ?_)⟩
      · exact div_pos (hDpos w₀ (hΛΩ i₀ w₀ hw₀) (hΛz i₀ w₀ hw₀)) hρz
      · exact div_le_div_of_nonneg_right hw₀d hρz.le
    · right
      push Not at hd2
      refine Real.log_le_log (by positivity) ?_
      rw [le_div_iff₀ hρz]
      linarith
  have hT₁up := sum_map_le_upper hcard hP hG hfP hcase
  have hT₁low := sum_map_ge_lower hcard hP hlc hℓP hG fun i hi w hw ↦
    (add_le_add_right (Real.log_le_log (div_pos hdpos hρz)
      (div_le_div_of_nonneg_right (hdle i w hw) hρz.le)) lc).trans
      (hglow w (hΛΩ i w hw) (hΛz i w hw) (hnear i hi w hw))
  have haeR : ∀ i ∈ G, ∀ᵐ ζ ∂ν.restrict (R i), ζ ∈ Ω ∧ ζ ≠ z ∧ D ζ ≤ C₃ * ρz := by
    intro i hi
    filter_upwards [ae_restrict_mem (hmeas i), ae_restrict_of_ae hae] with ζ hζ hζz
    exact ⟨(hRpt i hi ζ hζ).1, hζz, (hRpt i hi ζ hζ).2⟩
  have hT₂up := sum_setIntegral_le_bound hνR hP hG hint fun i hi ↦ by
    filter_upwards [haeR i hi] with ζ ⟨h1, h2, h3⟩
    exact (hglog ζ h1 h2 h3).trans (hPn ζ h1 h2 h3)
  have hT₂low := sum_setIntegral_ge_bound hνR hCx hG hint
    (fun i hi ζ hζ ↦ hsub ζ (hRpt i hi ζ hζ).1 (hRpt i hi ζ hζ).2) hlint
    (c₀ := lc + Real.log (2 * C₃)) fun i hi ↦ by
      filter_upwards [haeR i hi] with ζ ⟨h1, h2, h3⟩
      apply ENNReal.ofReal_le_ofReal
      have hb := hDpos ζ h1 h2
      have hl := hglow ζ h1 h2 h3
      have e : Real.log (2 * C₃ * ρz / D ζ) =
          Real.log (2 * C₃) - Real.log (D ζ / ρz) := by
        rw [Real.log_div (by positivity) hb.ne', Real.log_div hb.ne' hρz.ne',
          Real.log_mul (by positivity) hρz.ne']
        ring
      rw [e]
      linarith
  rw [Finset.sum_sub_distrib] at hS
  have hS' := abs_le.1 hS
  constructor <;> linarith [hS'.1, hS'.2]

/-- Estimates (2), (3) at a fixed point `z`, for abstract distance `D`, mass radius `ρ` and
kernel `k`: the cell and node data are reduced to the finite set of near cells and the kernel-free
core. -/
theorem multPot_bounds_pointwise {Ω : Set ℂ} {D ρ : ℂ → ℝ} {k : ℂ → ℂ → ℝ} {z : ℂ}
    {ν : Measure ℂ} {R : ℕ → Set ℂ} {c : ℕ → ℂ} {Λ : ℕ → Multiset ℂ} {N Mc : ℕ} {B : Set ℂ}
    {K₀ C₃ δ d P lc Cx Cnf : ℝ}
    (hN1 : 1 ≤ N) (hcard : ∀ i, Multiset.card (Λ i) = N) (hνR : ∀ i, ν (R i) = N)
    (hmeas : ∀ i, MeasurableSet (R i)) (hΛΩ : ∀ i, ∀ w ∈ Λ i, w ∈ Ω) (hRΩ : ∀ i, R i ⊆ Ω)
    (hρz : 0 < ρ z) (hC₃ : 0 < C₃) (hδ : 0 < δ) (hP : 0 ≤ P) (hlc : lc ≤ 0) (hCx : 0 ≤ Cx)
    (hcnt : {i | D (c i) < K₀ * ρ (c i)}.encard ≤ Mc)
    (hC3 : ∀ i, D (c i) < K₀ * ρ (c i) → ∀ w ∈ R i ∪ {w | w ∈ Λ i}, D w ≤ C₃ * ρ z)
    (hC4 : ∀ i, K₀ * ρ (c i) ≤ D (c i) →
      δ * ρ z ≤ D (c i) ∧ ∀ w ∈ Λ i, δ * ρ z ≤ 2 * D w)
    (hex : ∃ i, z ∈ R i ∧ D (c i) < K₀ * ρ (c i))
    (hsum : Summable fun i ↦ |cellPot k ν R Λ i z|)
    (hnn : ∀ u : Finset ℕ, (∀ i ∈ u, K₀ * ρ (c i) ≤ D (c i)) →
      ∑ i ∈ u, |cellPot k ν R Λ i z| ≤ Cnf)
    (hint : ∀ i, IntegrableOn (k z) (R i) ν) (hae : ∀ᵐ ζ ∂ν, ζ ≠ z)
    (hDpos : ∀ w ∈ Ω, w ≠ z → 0 < D w)
    (hglog : ∀ w ∈ Ω, w ≠ z → D w ≤ C₃ * ρ z →
      k z w - Real.log (ρ z) ≤ Real.log (D w / ρ z))
    (hglow : ∀ w ∈ Ω, w ≠ z → D w ≤ C₃ * ρ z →
      lc + Real.log (D w / ρ z) ≤ k z w - Real.log (ρ z))
    (hPlog : ∀ x : ℝ, 0 < x → x ≤ C₃ → Real.log x ≤ P)
    (hsub : ∀ ζ ∈ Ω, D ζ ≤ C₃ * ρ z → ζ ∈ B)
    (hlint : ∫⁻ ζ in B, ENNReal.ofReal (Real.log (2 * C₃ * ρ z / D ζ)) ∂ν ≤
      ENNReal.ofReal Cx)
    (hzN : z ∉ nodeSet Λ) (hdle : ∀ w ∈ nodeSet Λ, d ≤ D w)
    (hdex : ∃ w ∈ nodeSet Λ, D w ≤ d) :
    ((N : ℝ) * Mc + 1) * Real.log (d / ρ z) -
        (((N : ℝ) * Mc + 1) * P + Mc * N * |lc| + Mc * N * P + Cnf) ≤ multPot k ν R Λ z ∧
      multPot k ν R Λ z ≤ Real.log (d / ρ z) + (|Real.log (δ / 2)| + (Mc + 1) * N * P +
        Mc * (Cx + |lc + Real.log (2 * C₃)| * N) + Cnf) := by
  have hcard_pos : ∀ i, ∃ w, w ∈ Λ i := fun i ↦ by
    have : Multiset.card (Λ i) ≠ 0 := by rw [hcard i]; omega
    exact Multiset.card_pos_iff_exists_mem.1 (Nat.pos_of_ne_zero this)
  have hG0fin : {i | D (c i) < K₀ * ρ (c i)}.Finite := Set.finite_of_encard_le_coe hcnt
  set G := hG0fin.toFinset with hGdef
  have hGcard : G.card ≤ Mc := by
    have := hG0fin.encard_eq_coe_toFinset_card; rw [this] at hcnt; exact_mod_cast hcnt
  have hmemG : ∀ i, i ∈ G ↔ D (c i) < K₀ * ρ (c i) := fun i ↦ Set.Finite.mem_toFinset _
  have hΛz : ∀ i, ∀ w ∈ Λ i, w ≠ z := fun i w hw e ↦ hzN (e ▸ ⟨i, hw⟩)
  have hdC₃ : d ≤ C₃ * ρ z := by
    obtain ⟨i₀, -, hnear⟩ := hex
    obtain ⟨w, hw⟩ := hcard_pos i₀
    exact (hdle w ⟨i₀, hw⟩).trans (hC3 i₀ hnear w (Or.inr hw))
  have htail : |multPot k ν R Λ z - ∑ i ∈ G, cellPot k ν R Λ i z| ≤ Cnf :=
    abs_tsum_sub_sum_le hsum G fun u hu ↦ hnn u fun i hi ↦ by
      have := hu i hi; rw [hmemG, not_lt] at this; exact this
  have hlt : ∀ i, ν (R i) ≠ ∞ := fun i ↦ by rw [hνR i]; exact (ENNReal.natCast_lt_top N).ne
  have hS : |multPot k ν R Λ z - ∑ i ∈ G, (((Λ i).map fun w ↦ k z w - Real.log (ρ z)).sum -
      ∫ ζ in R i, (k z ζ - Real.log (ρ z)) ∂ν)| ≤ Cnf := by
    convert htail using 3
    exact (Finset.sum_congr rfl fun i _ ↦
      cellPot_eq_sub_const (hcard i) (hνR i) (hint i) (Real.log (ρ z))).symm
  exact multPot_bounds_core (G := G) (g := fun w ↦ k z w - Real.log (ρ z)) hcard hνR hmeas hρz
    hC₃ hδ hP hlc hCx hGcard hDpos hglog hglow hPlog hΛΩ hΛz
    (fun i hi w hw ↦ hC3 i ((hmemG i).1 hi) w (Or.inr hw))
    (fun i hi w hw ↦ (hC4 i (not_lt.1 (fun h ↦ hi ((hmemG i).2 h)))).2 w hw)
    (fun i w hw ↦ hdle w ⟨i, hw⟩) (by obtain ⟨w, ⟨i, hw⟩, hwd⟩ := hdex; exact ⟨i, w, hw, hwd⟩)
    hdC₃ (fun i hi ζ hζ ↦ ⟨hRΩ i hζ, hC3 i ((hmemG i).1 hi) ζ (Or.inl hζ)⟩) hae
    (fun i _ ↦ (hint i).sub (integrableOn_const (hlt i))) hsub hlint hS

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
        multPot kerPlane (lapNorm μ) R Λ z ≤ Real.log (d / massRadius (lapNorm μ) z) + C := by
  set R₁ := 15 * R₀
  obtain ⟨K₀, Cnf, hK₀, hCnf0, hnn⟩ := nonNear_sum_le_plane Cd R₁ η A B N hη hA hB
  obtain ⟨Mc, δ, C₃, hδ, hC₃, hcn⟩ := cells_near_plane Cd R₁ η A B K₀ hη hK₀
  obtain ⟨C1, -, hcl⟩ := claim1_plane_quant Cd R₁ 0
  set Smax := 2 * C₃ * max R₁ 0 + 1
  obtain ⟨Cχ, hχ⟩ := christ_plane_quant Cd R₁ Smax
  obtain ⟨CB, hCB⟩ := measure_ball_massRadius_quant Cd R₁ (2 * C₃)
  set P := max (Real.log C₃) 0
  have hP : 0 ≤ P := le_max_right _ _
  set M := N * Mc + 1 with hMdef
  set Cx : ℝ := (Cχ : ℝ) * CB
  set C := |Real.log (δ / 2)| + (Mc + 1) * N * P + Mc * (Cx + |Real.log (2 * C₃)| * N) + Cnf +
    M * P + Mc * N * P + C₃ + 1 with hCdef
  have hCx : 0 ≤ Cx := by positivity
  refine ⟨M, C, by omega, by positivity, ?_⟩
  intro μ R c m Λ hμ hC hNd hm
  have hν : MeasClassPlane (lapNorm μ) Cd R₁ := hμ.lapNorm
  set ν := lapNorm μ
  have hcnz := hcn ν N R c m Λ hν hN hC hNd
  have hC3C : C₃ ≤ C := by
    have h1 : 0 ≤ |Real.log (δ / 2)| + (Mc + 1) * N * P + Mc * (Cx + |Real.log (2 * C₃)| * N) +
        Cnf + M * P + Mc * N * P := by positivity
    linarith
  constructor
  · intro z
    obtain ⟨-, hC3, -, ⟨i₀, -, hnear⟩⟩ := hcnz z
    obtain ⟨w, hw⟩ := Multiset.card_pos_iff_exists_mem.1 (show 0 < Multiset.card (Λ i₀) by
      rw [hNd.card i₀]; omega)
    exact ⟨w, ⟨i₀, hw⟩, (hC3 i₀ hnear w (Or.inr hw)).trans
      (mul_le_mul_of_nonneg_right hC3C (hcl ν hν z z).1.le)⟩
  intro z hzN d hdle hdex
  obtain ⟨hcnt, hC3, hC4, hex⟩ := hcnz z
  have hρz : 0 < massRadius ν z := (hcl ν hν z z).1
  have hρzR : massRadius ν z ≤ R₁ := (hcl ν hν z z).2.1
  have hkeq : ∀ w, w ≠ z → kerPlane z w - Real.log (massRadius ν z) =
      Real.log (dist z w / massRadius ν z) := fun w hwz ↦ by
    rw [kerPlane, ← dist_eq_norm, Real.log_div (dist_pos.2 (Ne.symm hwz)).ne' hρz.ne']
  have hs0 : 0 < 2 * C₃ * massRadius ν z := by positivity
  have hsS : 2 * C₃ * massRadius ν z ≤ Smax := by
    have : 2 * C₃ * massRadius ν z ≤ 2 * C₃ * max R₁ 0 :=
      mul_le_mul_of_nonneg_left (hρzR.trans (le_max_left _ _)) (by positivity)
    linarith
  have hlint : ∫⁻ ζ in ball z (2 * C₃ * massRadius ν z),
      ENNReal.ofReal (Real.log (2 * C₃ * massRadius ν z / dist z ζ)) ∂ν ≤ ENNReal.ofReal Cx := by
    have hchr := hχ ν hν z _ hs0 hsS
    have hball := hCB ν hν z
    refine hchr.trans ?_
    rw [ENNReal.ofReal_mul (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal,
      ENNReal.ofReal_coe_nnreal]
    gcongr
  have hae : ∀ᵐ ζ ∂ν, ζ ≠ z := by
    rw [ae_iff]; simpa using hν.measure_singleton z
  have key := multPot_bounds_pointwise (Ω := univ) (D := dist z) (ρ := massRadius ν)
    (k := kerPlane) (B := ball z (2 * C₃ * massRadius ν z)) (lc := 0) (Cx := Cx) (Cnf := Cnf)
    (P := P) hN hNd.card (hC.measure_eq) hC.measurableSet (fun _ _ _ ↦ mem_univ _)
    (fun _ ↦ subset_univ _) hρz hC₃ hδ hP le_rfl hCx hcnt hC3 hC4 hex
    (summable_cellPot_plane hν hη hA hB hC hNd hm z) (hnn ν R c m Λ hν hC hNd hm z)
    (fun i ↦ integrableOn_kerPlane_cell hν hC i z) hae
    (fun w _ hwz ↦ dist_pos.2 (Ne.symm hwz))
    (fun w _ hwz _ ↦ (hkeq w hwz).le) (fun w _ hwz _ ↦ by rw [zero_add]; exact (hkeq w hwz).ge)
    (fun x hx hxC ↦ (Real.log_le_log hx hxC).trans (le_max_left _ _))
    (fun ζ _ hD ↦ by
      rw [mem_ball, dist_comm]; exact hD.trans_lt (by nlinarith [mul_pos hC₃ hρz]))
    hlint hzN hdle hdex
  have hMc : (M : ℝ) = (N : ℝ) * Mc + 1 := by
    simp only [hMdef, Nat.cast_add, Nat.cast_mul, Nat.cast_one]
  simp only [abs_zero, mul_zero, add_zero, zero_add] at key
  rw [← hMc] at key
  obtain ⟨k1, k2⟩ := key
  constructor
  · have h0 : 0 ≤ |Real.log (δ / 2)| + (Mc + 1) * N * P + C₃ + 1 := by positivity
    have h1 : 0 ≤ (Mc : ℝ) * (Cx + |Real.log (2 * C₃)| * N) := by positivity
    rw [hCdef]; linarith
  · have h0 : 0 ≤ (M : ℝ) * P + Mc * N * P + C₃ + 1 := by positivity
    rw [hCdef]; linarith

/-- On the disc the kernel is the logarithm of the hyperbolic tangent of the hyperbolic
distance. -/
theorem kerDisc_eq_log_tanh {z w : ℂ} (hz : z ∈ 𝔻) (hw : w ∈ 𝔻) :
    kerDisc z w = Real.log (Real.tanh (hypDist z w)) := by
  rw [kerDisc, ← tanh_hypDist hw hz, hypDist_comm]

/-- Upper bound `log tanh d ≤ log d` for the kernel on the disc. -/
theorem kerDisc_sub_le {z : ℂ} (hz : z ∈ 𝔻) {ρ X : ℝ} (hρ : 0 < ρ)
    (hβpos : ∀ w ∈ 𝔻, w ≠ z → 0 < hypDist z w) :
    ∀ w ∈ 𝔻, w ≠ z → hypDist z w ≤ X →
      kerDisc z w - Real.log ρ ≤ Real.log (hypDist z w / ρ) := by
  intro w hw hwz _
  have hb := hβpos w hw hwz
  rw [kerDisc_eq_log_tanh hz hw, Real.log_div hb.ne' hρ.ne']
  have := Real.log_le_log (tanh_pos' hb) (tanh_le_self hb.le)
  linarith

/-- Lower bound `log tanh d ≥ log (c d)` for the kernel on the disc, `d ≤ S`. -/
theorem kerDisc_sub_ge {z : ℂ} (hz : z ∈ 𝔻) {ρ S X : ℝ} (hρ : 0 < ρ) (hS : 0 < S)
    (hX : X ≤ S) (hβpos : ∀ w ∈ 𝔻, w ≠ z → 0 < hypDist z w) :
    ∀ w ∈ 𝔻, w ≠ z → hypDist z w ≤ X →
      Real.log (min (1 / 5) (Real.tanh 1 / S)) + Real.log (hypDist z w / ρ) ≤
        kerDisc z w - Real.log ρ := by
  intro w hw hwz hβ
  have hb := hβpos w hw hwz
  have hc : 0 < min (1 / 5) (Real.tanh 1 / S) :=
    lt_min (by norm_num) (div_pos (tanh_pos' one_pos) hS)
  have ht := mul_le_tanh hS hb.le (hβ.trans hX)
  rw [kerDisc_eq_log_tanh hz hw, ← Real.log_mul hc.ne' (by positivity),
    ← Real.log_div (tanh_pos' hb).ne' hρ.ne', mul_div_assoc']
  gcongr

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
  set Smax := 2 * C₃ * max R₁ 0 + 1
  have hSmax : 0 < Smax := by positivity
  obtain ⟨Cχ, hχ⟩ := christ_disc_quant Cd R₁ Smax
  obtain ⟨CB, hCB⟩ := measure_hypBall_massRadius_quant Cd R₁ (2 * C₃)
  set cS := min (1 / 5) (Real.tanh 1 / Smax)
  have hcS : 0 < cS := lt_min (by norm_num) (div_pos (tanh_pos' one_pos) hSmax)
  have hlcS : Real.log cS ≤ 0 := Real.log_nonpos hcS.le ((min_le_left _ _).trans (by norm_num))
  set P := max (Real.log C₃) 0
  have hP : 0 ≤ P := le_max_right _ _
  set M := N * Mc + 1 with hMdef
  set Cx : ℝ := (Cχ : ℝ) * CB
  set C := |Real.log (δ / 2)| + (Mc + 1) * N * P +
    Mc * (Cx + |Real.log cS + Real.log (2 * C₃)| * N) + Cnf +
    M * P + Mc * N * |Real.log cS| + Mc * N * P + C₃ + 1 with hCdef
  have hCx : 0 ≤ Cx := by positivity
  refine ⟨M, C, by omega, by positivity, ?_⟩
  intro μ R c m Λ hμ hC hNd hm2 hm3
  have hν : MeasClassDisc (lapNorm μ) Cd R₁ := hμ.lapNorm
  set ν := lapNorm μ
  have hcnz := fun z hz ↦ hcn ν N R c m Λ hν hN hC hNd z hz
  have hC3C : C₃ ≤ C := by
    have h1 : 0 ≤ |Real.log (δ / 2)| + (Mc + 1) * N * P +
        Mc * (Cx + |Real.log cS + Real.log (2 * C₃)| * N) + Cnf +
        M * P + Mc * N * |Real.log cS| + Mc * N * P := by positivity
    linarith
  constructor
  · intro z hz
    obtain ⟨-, hC3, -, ⟨i₀, -, hnear⟩⟩ := hcnz z hz
    obtain ⟨w, hw⟩ := Multiset.card_pos_iff_exists_mem.1 (show 0 < Multiset.card (Λ i₀) by
      rw [hNd.card i₀]; omega)
    exact ⟨w, ⟨i₀, hw⟩, (hC3 i₀ hnear w (Or.inr hw)).trans
      (mul_le_mul_of_nonneg_right hC3C (hcl ν hν z hz z hz).1.le)⟩
  intro z hz hzN d hdle hdex
  obtain ⟨hcnt, hC3, hC4, hex⟩ := hcnz z hz
  have hρz : 0 < massRadiusDisc ν z := (hcl ν hν z hz z hz).1
  have hρzR : massRadiusDisc ν z ≤ R₁ := (hcl ν hν z hz z hz).2.1
  have hs0 : 0 < 2 * C₃ * massRadiusDisc ν z := by positivity
  have hsS : 2 * C₃ * massRadiusDisc ν z ≤ Smax := by
    have : 2 * C₃ * massRadiusDisc ν z ≤ 2 * C₃ * max R₁ 0 :=
      mul_le_mul_of_nonneg_left (hρzR.trans (le_max_left _ _)) (by positivity)
    linarith
  have hlint : ∫⁻ ζ in hypBall z (2 * C₃ * massRadiusDisc ν z),
      ENNReal.ofReal (Real.log (2 * C₃ * massRadiusDisc ν z / hypDist z ζ)) ∂ν ≤
        ENNReal.ofReal Cx := by
    have hchr := hχ ν hν z hz _ hs0 hsS
    have hball := hCB ν hν z hz
    refine hchr.trans ?_
    rw [ENNReal.ofReal_mul (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal,
      ENNReal.ofReal_coe_nnreal]
    gcongr
  have hae : ∀ᵐ ζ ∂ν, ζ ≠ z := by
    rw [ae_iff]; simpa using hν.measure_singleton hz
  have hβpos : ∀ w ∈ 𝔻, w ≠ z → 0 < hypDist z w := fun w hw hwz ↦
    lt_of_le_of_ne (hypDist_nonneg _ _) fun h ↦ hwz ((hypDist_eq_zero_iff hz hw).1 h.symm).symm
  have hC3S : C₃ * massRadiusDisc ν z ≤ 2 * C₃ * massRadiusDisc ν z := by
    nlinarith [mul_pos hC₃ hρz]
  have key := multPot_bounds_pointwise (Ω := 𝔻) (D := hypDist z) (ρ := massRadiusDisc ν)
    (k := kerDisc) (B := hypBall z (2 * C₃ * massRadiusDisc ν z)) (lc := Real.log cS)
    (Cx := Cx) (Cnf := Cnf) (P := P) hN hNd.card hC.measure_eq hC.measurableSet hNd.mem
    hC.subset_univ hρz hC₃ hδ hP hlcS hCx hcnt hC3 hC4 hex
    (summable_cellPot_disc hν hη hA hB hρ₀ hC hNd hm2 hm3 hz)
    (hnn ν R c m Λ hν hC hNd hm2 hm3 z hz) (fun i ↦ integrableOn_kerDisc_cell hν hC i hz) hae
    hβpos (kerDisc_sub_le hz hρz hβpos) (kerDisc_sub_ge hz hρz hSmax (hC3S.trans hsS) hβpos)
    (fun x hx hxC ↦ (Real.log_le_log hx hxC).trans (le_max_left _ _))
    (fun ζ hζ hD ↦ ⟨hζ, hD.trans_lt (by nlinarith [mul_pos hC₃ hρz])⟩) hlint hzN hdle hdex
  have hMc : (M : ℝ) = (N : ℝ) * Mc + 1 := by
    simp only [hMdef, Nat.cast_add, Nat.cast_mul, Nat.cast_one]
  rw [← hMc] at key
  obtain ⟨k1, k2⟩ := key
  constructor
  · have h0 : 0 ≤ |Real.log (δ / 2)| + (Mc + 1) * N * P + C₃ + 1 := by positivity
    have h1 : 0 ≤ (Mc : ℝ) * (Cx + |Real.log cS + Real.log (2 * C₃)| * N) := by positivity
    rw [hCdef]; linarith
  · have h0 : 0 ≤ (M : ℝ) * P + Mc * N * |Real.log cS| + Mc * N * P + C₃ + 1 := by positivity
    rw [hCdef]; linarith

end OC
