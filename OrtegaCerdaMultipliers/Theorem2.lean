import OrtegaCerdaMultipliers.SeveralMultipliers
import OrtegaCerdaMultipliers.Regularization
import OrtegaCerdaMultipliers.ModelKernels

/-!
# M11 (Theorem2) — Theorem 2 (disc): weighted `L^p` and sup estimates; the bridge to BOC

See `blueprint/M11_Theorem2.md`.  Scaffold: statements, proofs `sorry`; definitions are real.
`theorem2`, `theorem2_uniform`, `theorem2_printed` are verbatim from
`comparator/statements.lean`.  `theorem2_uniform` is proved from the uniform kernel
`exists_disc_solution_kernel_quant` and M10's `disc_kernel_operator`; `theorem2` is proved from
`theorem2_uniform`.  The uniform kernel comes from `exists_aux_weight_disc_quant` (built on M04's
`lemma6_disc_quant` and M03's explicit-radius growth lemma) and M09's `prop2_disc_quant`.

Reconciliation (consumed from upstream): `hypArea` (M01), `lemma6_disc_hypArea` (M04, corollary
of `lemma6_disc`), `exists_hypBall_measure_gt` (M03), `prop2_disc_full`,
`exists_measurable_partition`, `prop2_disc_unif` (M09), `Measure.exists_add_eq_of_le` (M04),
`IsSubharmonicWeight.sigmaFinite`, `integral_mul_laplacian_of_contDiffOn` (M02),
`disc_kernel_operator` (M10).
-/

open MeasureTheory Metric Set Complex
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace OC

/-! ## Measure-theoretic helpers -/

theorem integral_log_one_sub_normSq_mul_laplacian {χ : ℂ → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχc : HasCompactSupport χ) (hχs : tsupport χ ⊆ 𝔻) :
    ∫ z, Real.log (1 - ‖z‖ ^ 2) * Laplacian.laplacian χ z = -(4 * ∫ z, χ z ∂hypArea) := sorry

/-! ## Hyperbolic area of hyperbolic discs -/

theorem one_sub_normSq_le_of_mem_hypBall {z w : ℂ} (hz : z ∈ 𝔻) {r : ℝ} (hr1 : r ≤ 1)
    (hw : w ∈ hypBall z r) : 1 - ‖z‖ ^ 2 ≤ 12 * (1 - ‖w‖ ^ 2) := sorry

theorem hypArea_hypBall_ge {z : ℂ} (hz : z ∈ 𝔻) {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    ENNReal.ofReal (Real.pi * r ^ 2 / 900) ≤ hypArea (hypBall z r) := sorry

theorem hypArea_hypBall_le {z : ℂ} (hz : z ∈ 𝔻) {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    hypArea (hypBall z r) ≤ ENNReal.ofReal (46656 * Real.pi * r ^ 2) := sorry

theorem IsLocallyDoublingDisc.of_le_of_le {μ ν : Measure ℂ} (hμ : IsLocallyDoublingDisc μ)
    {a b : ℝ≥0∞} (ha : a ≠ 0) (hb : b ≠ ∞) (h₁ : a • μ ≤ ν) (h₂ : ν ≤ b • μ) :
    IsLocallyDoublingDisc ν := sorry

theorem isLocallyDoublingDisc_hypArea : IsLocallyDoublingDisc hypArea := sorry

/-! ## The auxiliary weight -/

theorem isSubharmonicWeight_add_log {φ' : ℂ → ℝ} {ν : Measure ℂ} {ε c : ℝ} (hc : 0 ≤ c)
    (hcε : 4 * c ≤ ε) (hφ' : IsSubharmonicWeight 𝔻 φ' (ν + ENNReal.ofReal ε • hypArea)) :
    IsSubharmonicWeight 𝔻 (fun z ↦ φ' z + c * Real.log (1 - ‖z‖ ^ 2))
      (ν + ENNReal.ofReal (ε - 4 * c) • hypArea) := sorry

theorem exists_aux_weight_disc (φ : ℂ → ℝ) (μ : Measure ℂ) (hφ : IsSubharmonicWeight 𝔻 φ μ)
    (hd : IsLocallyDoublingDisc μ) (hm : ∃ r : ℝ, 0 < r ∧ ∀ z ∈ 𝔻, 1 < μ (hypBall z r)) :
    ∃ (ψ : ℂ → ℝ) (μψ : Measure ℂ) (c B : ℝ), 0 < c ∧ c < 1 ∧ 0 ≤ B ∧
      IsSubharmonicWeight 𝔻 ψ μψ ∧ IsLocallyDoublingDisc μψ ∧
      (∃ R : ℝ, 0 < R ∧ ∀ z ∈ 𝔻, 1 < μψ (hypBall z R)) ∧
      ∀ z ∈ 𝔻, |ψ z - (φ z + c * Real.log (1 - ‖z‖ ^ 2))| ≤ B := sorry

/-! ## The partition and the kernel -/

theorem measurableSet_goodSet_disc (Z : Set ℂ) (ρ : ℂ → ℝ) (ε : ℝ) :
    MeasurableSet {z | z ∈ 𝔻 ∧ ∀ w ∈ Z, w ∈ 𝔻 → ε * ρ w ≤ hypDist z w} := sorry

/-- The holomorphic factor of the kernel of Theorem 2:
`H(z, ζ) = ∑ᵢ χ_{Ωᵢ}(ζ) hᵢ(z)/hᵢ(ζ) · (1 - |ζ|²)/(1 - ζ̄ z)`. -/
def thm2H {n : ℕ} (h : Fin n → ℂ → ℂ) (Ω : Fin n → Set ℂ) (z ζ : ℂ) : ℂ :=
  (∑ i, (Ω i).indicator (fun ζ ↦ h i z / h i ζ) ζ) *
    (((1 - ‖ζ‖ ^ 2 : ℝ) : ℂ) / (1 - conj ζ * z))

theorem exists_disc_solution_kernel (φ : ℂ → ℝ) (μ : Measure ℂ)
    (hφ : IsSubharmonicWeight 𝔻 φ μ) (hd : IsLocallyDoublingDisc μ)
    (hm : ∃ r : ℝ, 0 < r ∧ ∀ z ∈ 𝔻, 1 < μ (hypBall z r)) :
    ∃ (H : ℂ → ℂ → ℂ) (c A : ℝ), 0 < c ∧ c < 1 ∧ 0 ≤ A ∧ Measurable (Function.uncurry H) ∧
      (∀ ζ ∈ 𝔻, DifferentiableOn ℂ (fun z ↦ H z ζ) 𝔻) ∧ (∀ ζ ∈ 𝔻, H ζ ζ = 1) ∧
      ∀ z ∈ 𝔻, ∀ ζ ∈ 𝔻, ‖H z ζ‖ ≤ A * Real.exp (φ z - φ ζ) *
        ((1 - ‖z‖ ^ 2) / (1 - ‖ζ‖ ^ 2)) ^ c * ((1 - ‖ζ‖ ^ 2) / ‖1 - conj ζ * z‖) := sorry

/-! ## Uniform forms (constants depending only on `(Cd, r)`) -/

/-- The auxiliary weight `ψ ≈ φ + c log(1 − |z|²)`, uniformly in the class `(Cd, r)`: from
`lemma6_disc_quant` (M04), `isSubharmonicWeight_add_log` and the growth lemma
`ofReal_lt_measure_hypBall` (M03, explicit radius). -/
theorem exists_aux_weight_disc_quant (Cd : ℝ≥0) (r : ℝ) (hr : 0 < r) :
    ∃ (c B : ℝ) (Cd' : ℝ≥0) (R' : ℝ), 0 < c ∧ c < 1 ∧ 0 ≤ B ∧ 0 < R' ∧
      ∀ (φ : ℂ → ℝ) (μ : Measure ℂ), IsSubharmonicWeight 𝔻 φ μ → MeasClassDisc μ Cd r →
        ∃ (ψ : ℂ → ℝ) (μψ : Measure ℂ), IsSubharmonicWeight 𝔻 ψ μψ ∧ MeasClassDisc μψ Cd' R' ∧
          ∀ z ∈ 𝔻, |ψ z - (φ z + c * Real.log (1 - ‖z‖ ^ 2))| ≤ B := sorry

/-- The kernel of Theorem 2, uniformly in the class `(Cd, r)`: from
`exists_aux_weight_disc_quant`, `prop2_disc_quant` (M09) applied to the auxiliary weight, and
`exists_measurable_partition`. -/
theorem exists_disc_solution_kernel_quant (Cd : ℝ≥0) (r : ℝ) (hr : 0 < r) :
    ∃ (c A : ℝ), 0 < c ∧ c < 1 ∧ 0 ≤ A ∧ ∀ (φ : ℂ → ℝ) (μ : Measure ℂ),
      IsSubharmonicWeight 𝔻 φ μ → MeasClassDisc μ Cd r →
      ∃ H : ℂ → ℂ → ℂ, Measurable (Function.uncurry H) ∧
        (∀ ζ ∈ 𝔻, DifferentiableOn ℂ (fun z ↦ H z ζ) 𝔻) ∧ (∀ ζ ∈ 𝔻, H ζ ζ = 1) ∧
        ∀ z ∈ 𝔻, ∀ ζ ∈ 𝔻, ‖H z ζ‖ ≤ A * Real.exp (φ z - φ ζ) *
          ((1 - ‖z‖ ^ 2) / (1 - ‖ζ‖ ^ 2)) ^ c * ((1 - ‖ζ‖ ^ 2) / ‖1 - conj ζ * z‖) := sorry

/-! ## Main statements -/

/-- **Theorem 2, uniform form**: the constant depends only on the doubling constant `Cd` and the
radius `r` of the mass condition (this is what the proof gives, and what the companion BOC
project needs: one constant for a whole family of weights). -/
theorem theorem2_uniform (Cd : ℝ≥0) (r : ℝ) (hr : 0 < r) :
    ∃ C : ℝ≥0, ∀ (φ : ℂ → ℝ) (μ : Measure ℂ), IsSubharmonicWeight 𝔻 φ μ →
      (∀ z ∈ 𝔻, ∀ s : ℝ, 0 < s → 2 * s < 1 → μ (hypBall z (2 * s)) ≤ Cd * μ (hypBall z s)) →
      (∀ z ∈ 𝔻, 1 < μ (hypBall z r)) →
      ∀ f : ℂ → ℂ, AEStronglyMeasurable f (volume.restrict 𝔻) →
      (∃ p : ℝ≥0∞, 1 ≤ p ∧
        eLpNorm (fun z ↦ f z * ((1 - ‖z‖ ^ 2) * Real.exp (-φ z) : ℝ)) p discMeasure < ∞) →
      ∃ u : ℂ → ℂ, IsWeakDbarSol 𝔻 u f ∧ ∀ p : ℝ≥0∞, 1 ≤ p →
        eLpNorm (fun z ↦ u z * (Real.exp (-φ z) : ℝ)) p discMeasure ≤
          C * eLpNorm (fun z ↦ f z * ((1 - ‖z‖ ^ 2) * Real.exp (-φ z) : ℝ)) p discMeasure := by
  obtain ⟨c, A, hc0, hc1, -, hK⟩ := exists_disc_solution_kernel_quant Cd r hr
  refine ⟨(24 * A / (c * (1 - c))).toNNReal, fun φ μ hφ hdμ hmμ f hf hadm ↦ ?_⟩
  obtain ⟨H, hHm, hHd, hH1, hHb⟩ := hK φ μ hφ (MeasClassDisc.of_weight hφ hdμ hmμ)
  obtain ⟨hsol, hest⟩ := disc_kernel_operator hφ.continuousOn hc0 hc1 hHm hHd hH1 hHb f hf hadm
  exact ⟨_, hsol, hest⟩

/-- **Theorem 2** (paper, p. 357), in the normalisation that its proof gives (NOTEBOOK): one
solution `u` of `∂̄u = f` in `𝔻` satisfies, for every `p ∈ [1, ∞]`,
`‖u e^{-φ}‖_{L^p(dm/(1-|z|²))} ≲ ‖f (1-|z|²) e^{-φ}‖_{L^p(dm/(1-|z|²))}`.  For `p = ∞` this is
`sup |u| e^{-φ} ≲ sup |f(ζ)| (1-|ζ|) e^{-φ(ζ)}` (essential suprema). -/
theorem theorem2 (φ : ℂ → ℝ) (μ : Measure ℂ) (hφ : IsSubharmonicWeight 𝔻 φ μ)
    (hd : IsLocallyDoublingDisc μ) (hm : ∃ r : ℝ, 0 < r ∧ ∀ z ∈ 𝔻, 1 < μ (hypBall z r)) :
    ∃ C : ℝ≥0, ∀ f : ℂ → ℂ, AEStronglyMeasurable f (volume.restrict 𝔻) →
      (∃ p : ℝ≥0∞, 1 ≤ p ∧
        eLpNorm (fun z ↦ f z * ((1 - ‖z‖ ^ 2) * Real.exp (-φ z) : ℝ)) p discMeasure < ∞) →
      ∃ u : ℂ → ℂ, IsWeakDbarSol 𝔻 u f ∧ ∀ p : ℝ≥0∞, 1 ≤ p →
        eLpNorm (fun z ↦ u z * (Real.exp (-φ z) : ℝ)) p discMeasure ≤
          C * eLpNorm (fun z ↦ f z * ((1 - ‖z‖ ^ 2) * Real.exp (-φ z) : ℝ)) p discMeasure := by
  obtain ⟨r, hr, hmr⟩ := hm
  obtain ⟨Cd, hCd⟩ := hd
  obtain ⟨C, hC⟩ := theorem2_uniform Cd r hr
  exact ⟨C, hC φ μ hφ hCd hmr⟩

theorem IsSubharmonicWeight.div_const {Ω : Set ℂ} {φ : ℂ → ℝ} {μ : Measure ℂ}
    (hφ : IsSubharmonicWeight Ω φ μ) {p : ℝ} (hp : 0 < p) :
    IsSubharmonicWeight Ω (fun z ↦ φ z / p) (ENNReal.ofReal p⁻¹ • μ) := sorry

theorem IsLocallyDoublingDisc.smul {μ : Measure ℂ} (h : IsLocallyDoublingDisc μ) (a : ℝ≥0∞) :
    IsLocallyDoublingDisc (a • μ) := sorry

/-- **Theorem 2**, the `L^p` estimate exactly as printed (paper, p. 357), with the solution
allowed to depend on `p`:
`∫_𝔻 |u|^p e^{-φ} dm/(1-|z|²) ≲ ∫_𝔻 |f (1-|z|²)|^p e^{-φ} dm/(1-|z|²)`. -/
theorem theorem2_printed (φ : ℂ → ℝ) (μ : Measure ℂ) (hφ : IsSubharmonicWeight 𝔻 φ μ)
    (hd : IsLocallyDoublingDisc μ) (hm : ∃ r : ℝ, 0 < r ∧ ∀ z ∈ 𝔻, 1 < μ (hypBall z r))
    (p : ℝ) (hp : 1 ≤ p) :
    ∃ C : ℝ≥0, ∀ f : ℂ → ℂ, AEStronglyMeasurable f (volume.restrict 𝔻) →
      ∫⁻ z, ENNReal.ofReal (‖f z * (1 - ‖z‖ ^ 2)‖ ^ p * Real.exp (-φ z)) ∂discMeasure < ∞ →
      ∃ u : ℂ → ℂ, IsWeakDbarSol 𝔻 u f ∧
        ∫⁻ z, ENNReal.ofReal (‖u z‖ ^ p * Real.exp (-φ z)) ∂discMeasure ≤
          C * ∫⁻ z, ENNReal.ofReal (‖f z * (1 - ‖z‖ ^ 2)‖ ^ p * Real.exp (-φ z)) ∂discMeasure :=
  sorry

/-! ## The bridge to BOC -/

/-- The Riesz measure of `ψ₀ / 2` for `ψ₀ ∈ C²(𝔻)`: `Δ(ψ₀/2) dm = 2 lap ψ₀ dm` on `𝔻`. -/
def bridgeMeasure (ψ₀ : ℂ → ℝ) : Measure ℂ :=
  (volume.restrict 𝔻).withDensity fun z ↦ ENNReal.ofReal (2 * lap ψ₀ z)

theorem bridge_isSubharmonicWeight {ψ₀ : ℂ → ℝ} (hψ : ContDiffOn ℝ 2 ψ₀ 𝔻)
    (hpos : ∀ z ∈ 𝔻, 0 ≤ lap ψ₀ z) :
    IsSubharmonicWeight 𝔻 (fun z ↦ ψ₀ z / 2) (bridgeMeasure ψ₀) := sorry

theorem bridge_le_le {ψ₀ : ℂ → ℝ} {δ M : ℝ} (hlow : ∀ z ∈ 𝔻, δ ≤ invLap ψ₀ z)
    (hup : ∀ z ∈ 𝔻, invLap ψ₀ z ≤ M) :
    ENNReal.ofReal (2 * δ) • hypArea ≤ bridgeMeasure ψ₀ ∧
      bridgeMeasure ψ₀ ≤ ENNReal.ofReal (2 * M) • hypArea := sorry

theorem bridge_isLocallyDoublingDisc {ψ₀ : ℂ → ℝ} {δ M : ℝ} (hδ : 0 < δ)
    (hlow : ∀ z ∈ 𝔻, δ ≤ invLap ψ₀ z) (hup : ∀ z ∈ 𝔻, invLap ψ₀ z ≤ M) :
    IsLocallyDoublingDisc (bridgeMeasure ψ₀) := sorry

theorem bridge_mass {ψ₀ : ℂ → ℝ} {δ : ℝ} (hδ : 0 < δ) (hlow : ∀ z ∈ 𝔻, δ ≤ invLap ψ₀ z) :
    ∃ R : ℝ, 0 < R ∧ ∀ z ∈ 𝔻, 1 < bridgeMeasure ψ₀ (hypBall z R) := sorry

theorem dbar_sup_estimate_C2 {ψ₀ : ℂ → ℝ} (hψ : ContDiffOn ℝ 2 ψ₀ 𝔻) {δ M : ℝ} (hδ : 0 < δ)
    (hlow : ∀ z ∈ 𝔻, δ ≤ invLap ψ₀ z) (hup : ∀ z ∈ 𝔻, invLap ψ₀ z ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : ℂ → ℂ, ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g →
      tsupport g ⊆ 𝔻 → ∃ W : ℂ → ℂ, IsWeakDbarSol 𝔻 W g ∧ ∀ B : ℝ,
        (∀ ζ ∈ 𝔻, ‖g ζ‖ * (1 - ‖ζ‖) * Real.exp (-ψ₀ ζ / 2) ≤ B) →
        ∀ᵐ z ∂(volume.restrict 𝔻), ‖W z‖ * Real.exp (-ψ₀ z / 2) ≤ C * B := sorry

/-- The bridge with a constant uniform in `ψ₀` (needed by BOC, M11 §8.3).  Not derivable from
the per-weight `theorem2`; it follows from `theorem2_uniform` (now among the comparator
statements) together with `bridge_*`, or from `prop2_disc_unif`. -/
theorem dbar_sup_estimate_C2_uniform {δ M : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ψ₀ : ℂ → ℝ, ContDiffOn ℝ 2 ψ₀ 𝔻 → (∀ z ∈ 𝔻, δ ≤ invLap ψ₀ z) →
      (∀ z ∈ 𝔻, invLap ψ₀ z ≤ M) → ∀ g : ℂ → ℂ, ContDiff ℝ (⊤ : ℕ∞) g →
      HasCompactSupport g → tsupport g ⊆ 𝔻 → ∃ W : ℂ → ℂ, IsWeakDbarSol 𝔻 W g ∧ ∀ B : ℝ,
        (∀ ζ ∈ 𝔻, ‖g ζ‖ * (1 - ‖ζ‖) * Real.exp (-ψ₀ ζ / 2) ≤ B) →
        ∀ᵐ z ∂(volume.restrict 𝔻), ‖W z‖ * Real.exp (-ψ₀ z / 2) ≤ C * B := sorry

end OC
