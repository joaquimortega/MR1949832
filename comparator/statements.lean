/-- **Theorem 4 (disc)** (paper, p. 363): multipliers.  If `Δψ = μ` is locally doubling in `𝔻`
(hyperbolic distance) and every hyperbolic disc of some radius `R` has mass `> 1`, there is a
holomorphic `h ≢ 0` on `𝔻` with zero set `Λ` and
`(d(z,Λ)/ρ(z))^M ≲ |h(z)| e^{-ψ(z)} ≲ d(z,Λ)/ρ(z)`. -/
theorem theorem4_disc (ψ : ℂ → ℝ) (μ : Measure ℂ) (hψ : IsSubharmonicWeight 𝔻 ψ μ)
    (hd : IsLocallyDoublingDisc μ) (hm : ∃ R : ℝ, 0 < R ∧ ∀ z ∈ 𝔻, 1 < μ (hypBall z R)) :
    ∃ (h : ℂ → ℂ) (M : ℕ) (C : ℝ≥0), DifferentiableOn ℂ h 𝔻 ∧ (∃ z₀ ∈ 𝔻, h z₀ ≠ 0) ∧
      ∀ z ∈ 𝔻,
        C⁻¹ * (hypDistSet z {w | w ∈ 𝔻 ∧ h w = 0} / ENNReal.ofReal (massRadiusDisc μ z)) ^ M ≤
          ENNReal.ofReal (‖h z‖ * Real.exp (-ψ z)) ∧
        ENNReal.ofReal (‖h z‖ * Real.exp (-ψ z)) ≤
          C * (hypDistSet z {w | w ∈ 𝔻 ∧ h w = 0} / ENNReal.ofReal (massRadiusDisc μ z)) := sorry

/-- **Theorem 4 (plane)** (paper, p. 363). -/
theorem theorem4_plane (ψ : ℂ → ℝ) (μ : Measure ℂ) (hψ : IsSubharmonicWeight univ ψ μ)
    (hd : IsLocallyDoubling μ) (hm : ∃ R : ℝ, 0 < R ∧ ∀ z : ℂ, 1 < μ (ball z R)) :
    ∃ (h : ℂ → ℂ) (M : ℕ) (C : ℝ≥0), Differentiable ℂ h ∧ (∃ z₀, h z₀ ≠ 0) ∧
      ∀ z : ℂ,
        C⁻¹ * (edistSet z {w | h w = 0} / ENNReal.ofReal (massRadius μ z)) ^ M ≤
          ENNReal.ofReal (‖h z‖ * Real.exp (-ψ z)) ∧
        ENNReal.ofReal (‖h z‖ * Real.exp (-ψ z)) ≤
          C * (edistSet z {w | h w = 0} / ENNReal.ofReal (massRadius μ z)) := sorry

/-- **Proposition 2 (disc)** (paper, p. 369): finitely many multipliers `h₁, …, h_n`, each
satisfying the conclusion of Theorem 4, whose exceptional sets
`E_{h_i} = ⋃_{λ ∈ Z(h_i)} D(λ, ε ρ(λ))` have empty intersection; outside `E_{h_i}`,
`|h_i| ≃ e^ψ` (the remark after Theorem 4). -/
theorem prop2_disc (ψ : ℂ → ℝ) (μ : Measure ℂ) (hψ : IsSubharmonicWeight 𝔻 ψ μ)
    (hd : IsLocallyDoublingDisc μ) (hm : ∃ R : ℝ, 0 < R ∧ ∀ z ∈ 𝔻, 1 < μ (hypBall z R)) :
    ∃ (n : ℕ) (h : Fin n → ℂ → ℂ) (M : ℕ) (ε : ℝ) (C : ℝ≥0), 0 < ε ∧ 0 < C ∧
      (∀ i, DifferentiableOn ℂ (h i) 𝔻 ∧ (∃ z₀ ∈ 𝔻, h i z₀ ≠ 0) ∧ ∀ z ∈ 𝔻,
        C⁻¹ * (hypDistSet z {w | w ∈ 𝔻 ∧ h i w = 0} /
            ENNReal.ofReal (massRadiusDisc μ z)) ^ M ≤
          ENNReal.ofReal (‖h i z‖ * Real.exp (-ψ z)) ∧
        ENNReal.ofReal (‖h i z‖ * Real.exp (-ψ z)) ≤
          C * (hypDistSet z {w | w ∈ 𝔻 ∧ h i w = 0} / ENNReal.ofReal (massRadiusDisc μ z))) ∧
      (∀ z ∈ 𝔻, ∃ i, ∀ w ∈ 𝔻, h i w = 0 → ε * massRadiusDisc μ w ≤ hypDist z w) ∧
      ∀ i, ∀ z ∈ 𝔻, (∀ w ∈ 𝔻, h i w = 0 → ε * massRadiusDisc μ w ≤ hypDist z w) →
        (C : ℝ)⁻¹ * Real.exp (ψ z) ≤ ‖h i z‖ ∧ ‖h i z‖ ≤ C * Real.exp (ψ z) := sorry

/-- **Proposition 2 (plane)** (paper, p. 369). -/
theorem prop2_plane (ψ : ℂ → ℝ) (μ : Measure ℂ) (hψ : IsSubharmonicWeight univ ψ μ)
    (hd : IsLocallyDoubling μ) (hm : ∃ R : ℝ, 0 < R ∧ ∀ z : ℂ, 1 < μ (ball z R)) :
    ∃ (n : ℕ) (h : Fin n → ℂ → ℂ) (M : ℕ) (ε : ℝ) (C : ℝ≥0), 0 < ε ∧ 0 < C ∧
      (∀ i, Differentiable ℂ (h i) ∧ (∃ z₀, h i z₀ ≠ 0) ∧ ∀ z : ℂ,
        C⁻¹ * (edistSet z {w | h i w = 0} / ENNReal.ofReal (massRadius μ z)) ^ M ≤
          ENNReal.ofReal (‖h i z‖ * Real.exp (-ψ z)) ∧
        ENNReal.ofReal (‖h i z‖ * Real.exp (-ψ z)) ≤
          C * (edistSet z {w | h i w = 0} / ENNReal.ofReal (massRadius μ z))) ∧
      (∀ z : ℂ, ∃ i, ∀ w, h i w = 0 → ε * massRadius μ w ≤ dist z w) ∧
      ∀ i, ∀ z : ℂ, (∀ w, h i w = 0 → ε * massRadius μ w ≤ dist z w) →
        (C : ℝ)⁻¹ * Real.exp (ψ z) ≤ ‖h i z‖ ∧ ‖h i z‖ ≤ C * Real.exp (ψ z) := sorry

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
          C * eLpNorm (fun z ↦ f z * ((1 - ‖z‖ ^ 2) * Real.exp (-φ z) : ℝ)) p discMeasure := sorry

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
          C * eLpNorm (fun z ↦ f z * ((1 - ‖z‖ ^ 2) * Real.exp (-φ z) : ℝ)) p discMeasure := sorry

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
          C * eLpNorm (fun z ↦ f z * (Real.exp (-φ z) : ℝ)) p volume := sorry

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

/-- **Theorem 5** (paper, p. 374): multipliers for measures on the real line.  There is an entire
`f ≢ 0` with zeros `Λ ⊆ ℝ` such that, for every `ε > 0`, `|f(z)| ≃ e^{φ(z)}` whenever
`|z - λ| ≥ ε ρ(λ)` for all `λ ∈ Λ`. -/
theorem theorem5 (φ : ℂ → ℝ) (μ : Measure ℂ) (hφ : IsSubharmonicWeight univ φ μ)
    (hd : IsLocallyDoublingLine μ) (hm : ∃ r : ℝ, 0 < r ∧ ∀ x : ℝ, 1 < μ (lineInterval x r)) :
    ∃ f : ℂ → ℂ, Differentiable ℂ f ∧ (∃ z₀, f z₀ ≠ 0) ∧ (∀ z, f z = 0 → z.im = 0) ∧
      ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ,
        (∀ x : ℝ, f x = 0 → ε * massRadiusLine μ x ≤ ‖z - x‖) →
          C⁻¹ * Real.exp (φ z) ≤ ‖f z‖ ∧ ‖f z‖ ≤ C * Real.exp (φ z) := sorry

/-- **Theorem 3** (paper, p. 358), corrected and conditional on the Ortega-Cerdà–Seip theorem
[OCS99] (`TheoremOCS`), which the paper uses as a black box.  As printed (with the unweighted
integral `∫_{|z-x|<1} d|μ|(z)/|x - z|`) the theorem is false (NOTEBOOK N-01); the integral must
carry the weight `e^{-φ(z)}`. -/
theorem theorem3_weighted (hOCS : TheoremOCS) (φ : ℂ → ℝ) (μ : Measure ℂ)
    (hφ : IsSubharmonicWeight univ φ μ) (hd : IsLocallyDoublingLine μ)
    (hm : ∃ r : ℝ, 0 < r ∧ ∀ x : ℝ, 1 < μ (lineInterval x r)) (K : ℝ≥0) :
    ∃ C : ℝ≥0, ∀ (ν : Measure ℂ) (σ : ℂ → ℂ) (L : Set ℂ),
      IsFiniteMeasure ν → IsCompact L → ν Lᶜ = 0 → Measurable σ → (∀ z, ‖σ z‖ = 1) →
      (∀ x : ℝ, ∀ r : ℝ, 0 < r →
        (ν.withDensity fun z ↦ ENNReal.ofReal (Real.exp (-φ z))) (ball (x : ℂ) r) ≤
          K * ENNReal.ofReal r) →
      ∃ u : ℂ → ℂ, IsWeakDbarSolMeasure u ν σ ∧ DifferentiableOn ℂ u Lᶜ ∧
        Filter.Tendsto (fun z ↦ ‖u z‖ * Real.exp (-φ z)) (Filter.cocompact ℂ) (nhds 0) ∧
        ∀ x : ℝ, (x : ℂ) ∉ L →
          ENNReal.ofReal (‖u x‖ * Real.exp (-φ x)) ≤
            C * (1 + ∫⁻ z in ball (x : ℂ) 1,
              ENNReal.ofReal (Real.exp (-φ z) / ‖(x : ℂ) - z‖) ∂ν) := sorry
