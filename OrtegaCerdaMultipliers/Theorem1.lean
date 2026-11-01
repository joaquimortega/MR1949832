import OrtegaCerdaMultipliers.SeveralMultipliers
import OrtegaCerdaMultipliers.Regularization
import OrtegaCerdaMultipliers.ModelKernels

/-!
# M12 (Theorem1) — Theorem 1 (locally doubling), Christ's Theorem 1, Proposition 1

See `blueprint/M12_Theorem1.md`.  Scaffold: statements, proofs `sorry`; `thm1H` is a real
definition.  `theorem1`, `theorem1_christ`, `prop1` are verbatim from
`comparator/statements.lean`; `theorem1_christ` is proved from `theorem1` and M03's
`IsDoubling.isLocallyDoubling`.

Reconciliation (consumed from upstream): `lemma6_plane_volume` (M04, corollary of
`lemma6_plane`), `prop2_plane_full`, `exists_measurable_partition` (M09),
`Measure.exists_add_eq_of_le` (M04), `IsSubharmonicWeight.sigmaFinite` (M02),
`IsDoubling.isLocallyDoubling` (M03), `plane_kernel_operator` (M10).  M12 does not import M11.
-/

open MeasureTheory Metric Set Complex
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace OC

theorem IsLocallyDoubling.of_le_of_le {μ ν : Measure ℂ} (hμ : IsLocallyDoubling μ)
    {a b : ℝ≥0∞} (ha : a ≠ 0) (hb : b ≠ ∞) (h₁ : a • μ ≤ ν) (h₂ : ν ≤ b • μ) :
    IsLocallyDoubling ν := by
  obtain ⟨Cd, hCd⟩ := hμ
  set a' : ℝ≥0 := (min a 1).toNNReal with ha'
  have ha'c : (a' : ℝ≥0∞) = min a 1 :=
    ENNReal.coe_toNNReal (min_lt_of_right_lt ENNReal.one_lt_top).ne
  have ha'0 : a' ≠ 0 := by
    intro h0
    have : (a' : ℝ≥0∞) = 0 := by rw [h0]; rfl
    rw [ha'c] at this
    rcases min_eq_iff.1 this with h | h
    · exact ha h.1
    · exact one_ne_zero h.1
  have h₁' : ∀ s, (a' : ℝ≥0∞) * μ s ≤ ν s := fun s ↦ by
    calc (a' : ℝ≥0∞) * μ s ≤ a * μ s := by gcongr; rw [ha'c]; exact min_le_left _ _
      _ ≤ ν s := h₁ s
  refine ⟨b.toNNReal * Cd / a', fun z s hs h2s ↦ ?_⟩
  calc ν (ball z (2 * s)) ≤ b * μ (ball z (2 * s)) := h₂ _
    _ ≤ b * (Cd * μ (ball z s)) := by gcongr; exact hCd z s hs h2s
    _ = ((b.toNNReal * Cd / a' : ℝ≥0) : ℝ≥0∞) * (a' * μ (ball z s)) := by
        symm
        rw [← mul_assoc, ← ENNReal.coe_mul, div_mul_cancel₀ _ ha'0, ENNReal.coe_mul,
          ENNReal.coe_toNNReal hb, mul_assoc]
    _ ≤ ((b.toNNReal * Cd / a' : ℝ≥0) : ℝ≥0∞) * ν (ball z s) := by gcongr; exact h₁' _

theorem two_le_measure_ball_three_mul {μ : Measure ℂ} {r : ℝ} (hr : 0 < r)
    (h : ∀ z : ℂ, 1 ≤ μ (ball z r)) (z : ℂ) : 2 ≤ μ (ball z (3 * r)) := by
  set w₀ : ℂ := z + ((2 * r : ℝ) : ℂ) with hw₀
  have hdist : dist z w₀ = 2 * r := by
    rw [hw₀, dist_eq_norm, sub_add_cancel_left, norm_neg, Complex.norm_real,
      Real.norm_of_nonneg (by linarith)]
  have hdisj : Disjoint (ball z r) (ball w₀ r) :=
    ball_disjoint_ball (by rw [hdist]; linarith)
  have hsub : ball z r ∪ ball w₀ r ⊆ ball z (3 * r) := by
    refine union_subset (ball_subset_ball (by linarith)) (fun w hw ↦ ?_)
    rw [mem_ball] at hw ⊢
    calc dist w z ≤ dist w w₀ + dist w₀ z := dist_triangle _ _ _
      _ < r + 2 * r := by rw [dist_comm w₀ z, hdist]; linarith
      _ = 3 * r := by ring
  calc (2 : ℝ≥0∞) = 1 + 1 := by norm_num
    _ ≤ μ (ball z r) + μ (ball w₀ r) := add_le_add (h z) (h w₀)
    _ = μ (ball z r ∪ ball w₀ r) := (measure_union hdisj measurableSet_ball).symm
    _ ≤ μ (ball z (3 * r)) := measure_mono hsub

theorem isSubharmonicWeight_sub_normSq {φ' : ℂ → ℝ} {ν : Measure ℂ} {ε c : ℝ} (hc : 0 ≤ c)
    (hcε : 4 * c ≤ ε) (hφ' : IsSubharmonicWeight univ φ' (ν + ENNReal.ofReal ε • volume)) :
    IsSubharmonicWeight univ (fun z ↦ φ' z - c * ‖z‖ ^ 2)
      (ν + ENNReal.ofReal (ε - 4 * c) • volume) := sorry

theorem exists_aux_weight_plane (φ : ℂ → ℝ) (μ : Measure ℂ) (hφ : IsSubharmonicWeight univ φ μ)
    (hd : IsLocallyDoubling μ) (hm : ∃ r : ℝ, 0 < r ∧ ∀ z : ℂ, 1 ≤ μ (ball z r)) :
    ∃ (ψ : ℂ → ℝ) (μψ : Measure ℂ) (c B : ℝ), 0 < c ∧ 0 ≤ B ∧
      IsSubharmonicWeight univ ψ μψ ∧ IsLocallyDoubling μψ ∧
      (∃ R : ℝ, 0 < R ∧ ∀ z : ℂ, 1 < μψ (ball z R)) ∧
      ∀ z, |ψ z - (φ z - c * ‖z‖ ^ 2)| ≤ B := sorry

theorem isClosed_goodSet_plane (Z : Set ℂ) (ρ : ℂ → ℝ) (ε : ℝ) :
    IsClosed {z : ℂ | ∀ w ∈ Z, ε * ρ w ≤ dist z w} := by
  simp only [ofPred_forall]
  exact isClosed_iInter fun w ↦ isClosed_iInter fun _ ↦
    isClosed_le continuous_const (continuous_id.dist continuous_const)

/-- The holomorphic factor of the kernel `κ'` of Theorem 1:
`H(z, ζ) = ∑ᵢ χ_{Ωᵢ}(ζ) hᵢ(z)/hᵢ(ζ) · e^{2c(ζ̄ z - |ζ|²)}`. -/
def thm1H {n : ℕ} (h : Fin n → ℂ → ℂ) (Ω : Fin n → Set ℂ) (c : ℝ) (z ζ : ℂ) : ℂ :=
  (∑ i, (Ω i).indicator (fun ζ ↦ h i z / h i ζ) ζ) *
    Complex.exp (2 * c * (conj ζ * z - ((‖ζ‖ ^ 2 : ℝ) : ℂ)))

theorem exists_plane_solution_kernel (φ : ℂ → ℝ) (μ : Measure ℂ)
    (hφ : IsSubharmonicWeight univ φ μ) (hd : IsLocallyDoubling μ)
    (hm : ∃ r : ℝ, 0 < r ∧ ∀ z : ℂ, 1 ≤ μ (ball z r)) :
    ∃ (H : ℂ → ℂ → ℂ) (c A : ℝ), 0 < c ∧ 0 ≤ A ∧ Measurable (Function.uncurry H) ∧
      (∀ ζ, Differentiable ℂ (fun z ↦ H z ζ)) ∧ (∀ ζ, H ζ ζ = 1) ∧
      ∀ z ζ, ‖H z ζ‖ ≤ A * Real.exp (φ z - φ ζ) * Real.exp (-c * ‖z - ζ‖ ^ 2) := sorry

/-- **Theorem 1** (paper, p. 356; Christ's theorem), in the locally doubling form that the
paper's proof gives (p. 357): one solution `u` of `∂̄u = f` with
`‖u e^{-φ}‖_p ≲ ‖f e^{-φ}‖_p` for every `p ∈ [1, ∞]`. -/
theorem theorem1 (φ : ℂ → ℝ) (μ : Measure ℂ) (hφ : IsSubharmonicWeight univ φ μ)
    (hd : IsLocallyDoubling μ) (hm : ∃ r : ℝ, 0 < r ∧ ∀ z : ℂ, 1 ≤ μ (ball z r)) :
    ∃ C : ℝ≥0, ∀ f : ℂ → ℂ, AEStronglyMeasurable f volume →
      (∃ p : ℝ≥0∞, 1 ≤ p ∧ eLpNorm (fun z ↦ f z * (Real.exp (-φ z) : ℝ)) p volume < ∞) →
      ∃ u : ℂ → ℂ, IsWeakDbarSol univ u f ∧ ∀ p : ℝ≥0∞, 1 ≤ p →
        eLpNorm (fun z ↦ u z * (Real.exp (-φ z) : ℝ)) p volume ≤
          C * eLpNorm (fun z ↦ f z * (Real.exp (-φ z) : ℝ)) p volume := sorry

/-- **Theorem 1** as stated in the paper (Christ, [Chr91]): `Δφ` doubling. -/
theorem theorem1_christ (φ : ℂ → ℝ) (μ : Measure ℂ) (hφ : IsSubharmonicWeight univ φ μ)
    (hd : IsDoubling μ) (hm : ∃ r : ℝ, 0 < r ∧ ∀ z : ℂ, 1 ≤ μ (ball z r)) :
    ∃ C : ℝ≥0, ∀ f : ℂ → ℂ, AEStronglyMeasurable f volume →
      (∃ p : ℝ≥0∞, 1 ≤ p ∧ eLpNorm (fun z ↦ f z * (Real.exp (-φ z) : ℝ)) p volume < ∞) →
      ∃ u : ℂ → ℂ, IsWeakDbarSol univ u f ∧ ∀ p : ℝ≥0∞, 1 ≤ p →
        eLpNorm (fun z ↦ u z * (Real.exp (-φ z) : ℝ)) p volume ≤
          C * eLpNorm (fun z ↦ f z * (Real.exp (-φ z) : ℝ)) p volume :=
  theorem1 φ μ hφ hd.isLocallyDoubling hm

/-- **Proposition 1** (paper, p. 359): under the hypotheses of Theorem 1, the solution is given by
`u(z) = ∫ e^{φ(z) - φ(ζ)} k(z, ζ) f(ζ) dm(ζ)` with `|k(z, ζ)| ≲ e^{-ε|z-ζ|²} / |z - ζ|`.  (The
paper claims `≃`; the lower bound fails at the zeros of the multipliers, NOTEBOOK.) -/
theorem prop1 (φ : ℂ → ℝ) (μ : Measure ℂ) (hφ : IsSubharmonicWeight univ φ μ)
    (hd : IsLocallyDoubling μ) (hm : ∃ r : ℝ, 0 < r ∧ ∀ z : ℂ, 1 ≤ μ (ball z r)) :
    ∃ (k : ℂ → ℂ → ℂ) (ε C : ℝ), 0 < ε ∧ Measurable (Function.uncurry k) ∧
      (∀ z ζ, z ≠ ζ → ‖k z ζ‖ ≤ C * Real.exp (-ε * ‖z - ζ‖ ^ 2) / ‖z - ζ‖) ∧
      ∀ f : ℂ → ℂ, AEStronglyMeasurable f volume →
        (∃ p : ℝ≥0∞, 1 ≤ p ∧ eLpNorm (fun z ↦ f z * (Real.exp (-φ z) : ℝ)) p volume < ∞) →
        IsWeakDbarSol univ
          (fun z ↦ ∫ ζ, (Real.exp (φ z - φ ζ) : ℂ) * k z ζ * f ζ) f := sorry

/-- The kernel of the construction vanishes at the zeros of the multipliers: the printed
lower bound `|k| ≳ e^{-ε|z-ζ|²}/|z-ζ|` fails for it. -/
theorem thm1H_eq_zero_of_zero {n : ℕ} {h : Fin n → ℂ → ℂ} {Ω : Fin n → Set ℂ} {c : ℝ}
    (hΩ : ∀ ζ, ∃! i, ζ ∈ Ω i) {i : Fin n} {ζ z : ℂ} (hζ : ζ ∈ Ω i) (hz : h i z = 0) :
    thm1H h Ω c z ζ = 0 := by
  obtain ⟨j, -, huniq⟩ := hΩ ζ
  unfold thm1H
  rw [Finset.sum_eq_single i
    (fun k _ hki ↦ indicator_of_notMem (fun hk ↦ hki ((huniq k hk).trans (huniq i hζ).symm)) _)
    (by simp), indicator_of_mem hζ, hz, zero_div, zero_mul]

end OC
