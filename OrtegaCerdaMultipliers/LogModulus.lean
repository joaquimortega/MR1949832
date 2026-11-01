import Mathlib
import OrtegaCerdaMultipliers.Defs

/-!
# M07 — Holomorphic functions with prescribed log-modulus

Paper, p. 366: "Now we take a holomorphic function `h` that vanishes at all the points `λ_j^i` …
We choose `g` in such a way that `log |h| = ψ − (1/2π) ∫ log|z−ζ| (Δψ − Σ δ)`."

Blueprint: `blueprint/M07_LogModulus.md`.

Main result (`exists_analytic_norm_eq_exp`): let `Ω` be a union of closed balls centred at a
fixed `c` (e.g. `ball c R` or `univ`), `n : ℂ → ℕ` a multiplicity function and `v : ℂ → ℝ`
such that on each ball `B = ball c r` with `closedBall c r ⊆ Ω` there is a finite `F ⊇ B ∩ supp n`
and a harmonic `u` on `B` with `v = u + log |∏_{ζ ∈ F} (z - ζ)^{n ζ}|` on `B \ supp n`.
Then there is `h` holomorphic on `Ω`, with `|h| = e^v` off `supp n` and `ord_a h = n a` on `Ω`.

Route: on each admissible ball, `h_r := k · exp G · P` with `Re G = u` (Mathlib's
`HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq`), normalised by `h_r(p) = e^{v(p)}` at a fixed
`p ∈ Ω \ supp n`.  Two such functions agree on the smaller ball (maximum modulus on a small disc
around `p`, then the identity theorem), so `h z := h_{R(z)} z` is well defined and holomorphic.
-/

open Metric Set Filter Topology Complex InnerProductSpace MeasureTheory

noncomputable section

namespace OC

/-- The local polynomial `∏_{ζ ∈ F} (z - ζ)^{n ζ}`. -/
def zeroProd (n : ℂ → ℕ) (F : Finset ℂ) (z : ℂ) : ℂ :=
  ∏ ζ ∈ F, (z - ζ) ^ n ζ

lemma zeroProd_analyticAt (n : ℂ → ℕ) (F : Finset ℂ) (z : ℂ) :
    AnalyticAt ℂ (zeroProd n F) z := by
  unfold zeroProd
  exact Finset.analyticAt_fun_prod _ fun ζ _ ↦ (analyticAt_id.sub analyticAt_const).pow _

/-- `zeroProd n F z ≠ 0` as soon as `n z = 0`. -/
lemma zeroProd_ne_zero {n : ℂ → ℕ} {F : Finset ℂ} {z : ℂ} (hz : n z = 0) :
    zeroProd n F z ≠ 0 := by
  unfold zeroProd
  rw [Finset.prod_ne_zero_iff]
  intro ζ _
  by_cases h : z = ζ
  · subst h; simp [hz]
  · exact pow_ne_zero _ (sub_ne_zero.mpr h)

/-- Factor out the zero at `a`. -/
lemma zeroProd_eq_mul_erase {n : ℂ → ℕ} {F : Finset ℂ} {a : ℂ} (ha : n a ≠ 0 → a ∈ F) (z : ℂ) :
    zeroProd n F z = (z - a) ^ n a * zeroProd n (F.erase a) z := by
  unfold zeroProd
  by_cases haF : a ∈ F
  · rw [Finset.mul_prod_erase F (fun ζ ↦ (z - ζ) ^ n ζ) haF]
  · have : n a = 0 := by by_contra h; exact haF (ha h)
    rw [Finset.erase_eq_of_notMem haF, this, pow_zero, one_mul]

lemma zeroProd_erase_ne_zero (n : ℂ → ℕ) (F : Finset ℂ) (a : ℂ) :
    zeroProd n (F.erase a) a ≠ 0 := by
  unfold zeroProd
  rw [Finset.prod_ne_zero_iff]
  intro ζ hζ
  exact pow_ne_zero _ (sub_ne_zero.mpr (Finset.ne_of_mem_erase hζ).symm)

/-- **Ball-wise hypothesis** (what Weyl's lemma for `Δ` delivers, see `blueprint/M07`):
on every ball `ball c r` with `closedBall c r ⊆ Ω`, `v` is `u + log |P|` off `supp n`, with `u`
harmonic and `P = zeroProd n F` containing all the zeros in the ball. -/
def LogModulusBallwise (Ω : Set ℂ) (c : ℂ) (n : ℂ → ℕ) (v : ℂ → ℝ) : Prop :=
  ∀ r : ℝ, 0 < r → closedBall c r ⊆ Ω → ∃ F : Finset ℂ, (∀ z ∈ ball c r, n z ≠ 0 → z ∈ F) ∧
    ∃ u : ℂ → ℝ, HarmonicOnNhd u (ball c r) ∧
      ∀ z ∈ ball c r, n z = 0 → v z = u z + Real.log ‖zeroProd n F z‖

/-- **Step 1–2: one ball.**  On an admissible ball there is a holomorphic `H` with `|H| = e^v`
off `supp n`, the prescribed orders, and the normalisation `H p = e^{v p}`. -/
theorem exists_on_ball {c : ℂ} {r : ℝ} {n : ℂ → ℕ} {v : ℂ → ℝ} (F : Finset ℂ)
    (hF : ∀ z ∈ ball c r, n z ≠ 0 → z ∈ F) (u : ℂ → ℝ) (hu : HarmonicOnNhd u (ball c r))
    (hv : ∀ z ∈ ball c r, n z = 0 → v z = u z + Real.log ‖zeroProd n F z‖)
    {p : ℂ} (hp : p ∈ ball c r) (hnp : n p = 0) :
    ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H (ball c r) ∧
      (∀ z ∈ ball c r, n z = 0 → ‖H z‖ = Real.exp (v z)) ∧
      (∀ a ∈ ball c r, analyticOrderAt H a = n a) ∧ H p = (Real.exp (v p) : ℂ) := by
  obtain ⟨G, hG, hGre⟩ := hu.exists_analyticOnNhd_ball_re_eq
  set H₀ : ℂ → ℂ := fun z ↦ exp (G z) * zeroProd n F z with hH₀
  have hH₀norm : ∀ z ∈ ball c r, n z = 0 → ‖H₀ z‖ = Real.exp (v z) := by
    intro z hz hnz
    have hP := zeroProd_ne_zero (F := F) hnz
    have hRe : (G z).re = u z := hGre hz
    rw [hH₀, norm_mul, Complex.norm_exp, hRe, hv z hz hnz, Real.exp_add,
      Real.exp_log (norm_pos_iff.mpr hP)]
  have hH₀p : H₀ p ≠ 0 := by
    intro h0
    have := hH₀norm p hp hnp
    rw [h0, norm_zero] at this
    exact (Real.exp_pos _).ne' this.symm
  set k : ℂ := (Real.exp (v p) : ℂ) / H₀ p with hk
  have hk0 : k ≠ 0 := div_ne_zero (by exact_mod_cast (Real.exp_pos _).ne') hH₀p
  have hknorm : ‖k‖ * Real.exp (v p) = Real.exp (v p) := by
    rw [hk, norm_div, hH₀norm p hp hnp, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), div_self (Real.exp_pos _).ne', one_mul]
  have hknorm' : ‖k‖ = 1 := by
    have := hknorm
    nlinarith [Real.exp_pos (v p)]
  refine ⟨fun z ↦ k * H₀ z, ?_, ?_, ?_, ?_⟩
  · intro z hz
    exact analyticAt_const.mul ((hG z hz).cexp.mul (zeroProd_analyticAt n F z))
  · intro z hz hnz
    rw [norm_mul, hknorm', one_mul, hH₀norm z hz hnz]
  · intro a ha
    have hAn : AnalyticAt ℂ (fun z ↦ k * H₀ z) a :=
      analyticAt_const.mul ((hG a ha).cexp.mul (zeroProd_analyticAt n F a))
    rw [hAn.analyticOrderAt_eq_natCast]
    refine ⟨fun z ↦ k * exp (G z) * zeroProd n (F.erase a) z,
      analyticAt_const.mul (hG a ha).cexp |>.mul (zeroProd_analyticAt n _ a),
      mul_ne_zero (mul_ne_zero hk0 (Complex.exp_ne_zero _)) (zeroProd_erase_ne_zero n F a),
      Eventually.of_forall fun z ↦ ?_⟩
    simp only [hH₀, smul_eq_mul, zeroProd_eq_mul_erase (hF a ha) z]
    ring
  · simp only [hk]
    field_simp

/-- **Step 3: compatibility.**  Two holomorphic functions on `ball c r` with the same modulus
`e^v` off `supp n` (locally finite near `p`) and the same value at `p` coincide. -/
theorem eqOn_of_norm_eq {c p : ℂ} {r : ℝ} {n : ℂ → ℕ} {v : ℂ → ℝ} {H₁ H₂ : ℂ → ℂ}
    (F : Finset ℂ) (hF : ∀ z ∈ ball c r, n z ≠ 0 → z ∈ F)
    (h₁ : AnalyticOnNhd ℂ H₁ (ball c r)) (h₂ : AnalyticOnNhd ℂ H₂ (ball c r))
    (hn₁ : ∀ z ∈ ball c r, n z = 0 → ‖H₁ z‖ = Real.exp (v z))
    (hn₂ : ∀ z ∈ ball c r, n z = 0 → ‖H₂ z‖ = Real.exp (v z))
    (hp : p ∈ ball c r) (hnp : n p = 0) (hH : H₁ p = H₂ p) :
    EqOn H₁ H₂ (ball c r) := by
  -- a small disc around `p` free of zeros
  have hU : IsOpen (ball c r \ ((F.erase p : Finset ℂ) : Set ℂ)) :=
    isOpen_ball.sdiff (F.erase p).finite_toSet.isClosed
  have hpU : p ∈ ball c r \ ((F.erase p : Finset ℂ) : Set ℂ) :=
    ⟨hp, by simp⟩
  obtain ⟨δ, hδ, hδU⟩ := Metric.isOpen_iff.mp hU p hpU
  have hzero : ∀ z ∈ ball p δ, z ∈ ball c r ∧ n z = 0 := by
    intro z hz
    obtain ⟨hzB, hzF⟩ := hδU hz
    refine ⟨hzB, ?_⟩
    by_contra hnz
    by_cases hzp : z = p
    · exact hnz (hzp ▸ hnp)
    · exact hzF (by simpa [Finset.mem_erase, hzp] using hF z hzB hnz)
  have hne : ∀ z ∈ ball p δ, H₂ z ≠ 0 := by
    intro z hz h0
    have := hn₂ z (hzero z hz).1 (hzero z hz).2
    rw [h0, norm_zero] at this
    exact (Real.exp_pos _).ne' this.symm
  set q : ℂ → ℂ := fun z ↦ H₁ z / H₂ z
  have hqd : DifferentiableOn ℂ q (ball p δ) := fun z hz ↦
    ((h₁ z (hzero z hz).1).differentiableAt.div (h₂ z (hzero z hz).1).differentiableAt
      (hne z hz)).differentiableWithinAt
  have hqn : ∀ z ∈ ball p δ, ‖q z‖ = 1 := by
    intro z hz
    simp only [q, norm_div, hn₁ z (hzero z hz).1 (hzero z hz).2,
      hn₂ z (hzero z hz).1 (hzero z hz).2, div_self (Real.exp_pos _).ne']
  have hpδ : p ∈ ball p δ := mem_ball_self hδ
  have hmax : IsMaxOn (norm ∘ q) (ball p δ) p := fun z hz ↦ by
    simp only [mem_ofPred_eq, Function.comp_apply, hqn z hz, hqn p hpδ, le_refl]
  have hconst := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm
    (convex_ball p δ).isPreconnected isOpen_ball hqd hpδ hmax
  have hq1 : q p = 1 := by
    simp only [q, hH]
    exact div_self (hne p hpδ)
  have hev : H₁ =ᶠ[𝓝 p] H₂ := by
    filter_upwards [isOpen_ball.mem_nhds hpδ] with z hz
    have := hconst hz
    simp only [Function.const_apply, hq1, q] at this
    exact (div_eq_one_iff_eq (hne z hz)).mp this
  exact h₁.eqOn_of_preconnected_of_eventuallyEq h₂ (convex_ball c r).isPreconnected hp hev

/-- **Main theorem (M07), ball-wise hypothesis.**  `Ω` is a union of closed balls centred at `c`
(this covers `ball c R` and `univ`). -/
theorem exists_analytic_norm_eq_exp {Ω : Set ℂ} {c : ℂ}
    (hΩ : ∀ z ∈ Ω, ∃ r, dist z c < r ∧ closedBall c r ⊆ Ω)
    {n : ℂ → ℕ} {v : ℂ → ℝ} (hball : LogModulusBallwise Ω c n v) :
    ∃ h : ℂ → ℂ, AnalyticOnNhd ℂ h Ω ∧ (∀ z ∈ Ω, n z = 0 → ‖h z‖ = Real.exp (v z)) ∧
      ∀ z ∈ Ω, analyticOrderAt h z = n z := by
  rcases Ω.eq_empty_or_nonempty with hΩe | ⟨z₀, hz₀⟩
  · exact ⟨0, by simp [hΩe], by simp [hΩe], by simp [hΩe]⟩
  -- a base point `p ∈ Ω` off the zero set
  obtain ⟨r₀, hr₀, hr₀Ω⟩ := hΩ z₀ hz₀
  have hr₀pos : 0 < r₀ := lt_of_le_of_lt dist_nonneg hr₀
  obtain ⟨F₀, hF₀, -⟩ := hball r₀ hr₀pos hr₀Ω
  obtain ⟨p, hpF, hpB⟩ := ((F₀ : Set ℂ).toFinite.countable.dense_compl ℂ).exists_mem_open
    isOpen_ball ⟨c, mem_ball_self hr₀pos⟩
  have hnp : n p = 0 := by
    by_contra h
    exact hpF (hF₀ p hpB h)
  have hpΩ : p ∈ Ω := hr₀Ω (ball_subset_closedBall hpB)
  -- admissible radii and the local solutions
  let Adm : ℝ → Prop := fun r ↦ 0 < r ∧ dist p c < r ∧ closedBall c r ⊆ Ω
  have hH : ∀ r : ℝ, ∃ H : ℂ → ℂ, Adm r → AnalyticOnNhd ℂ H (ball c r) ∧
      (∀ z ∈ ball c r, n z = 0 → ‖H z‖ = Real.exp (v z)) ∧
      (∀ a ∈ ball c r, analyticOrderAt H a = n a) ∧ H p = (Real.exp (v p) : ℂ) := by
    intro r
    by_cases hr : Adm r
    · obtain ⟨F, hF, u, hu, hv⟩ := hball r hr.1 hr.2.2
      obtain ⟨H, hH⟩ := exists_on_ball F hF u hu hv (mem_ball.mpr hr.2.1) hnp
      exact ⟨H, fun _ ↦ hH⟩
    · exact ⟨0, fun h ↦ absurd h hr⟩
  choose H hH using hH
  have hcompat : ∀ r r', Adm r → Adm r' → r ≤ r' → EqOn (H r) (H r') (ball c r) := by
    intro r r' hr hr' hrr'
    obtain ⟨F, hF, -⟩ := hball r hr.1 hr.2.2
    have hsub : ball c r ⊆ ball c r' := ball_subset_ball hrr'
    exact eqOn_of_norm_eq (v := v) F hF (hH r hr).1 ((hH r' hr').1.mono hsub) (hH r hr).2.1
      (fun z hz hnz ↦ (hH r' hr').2.1 z (hsub hz) hnz) (mem_ball.mpr hr.2.1) hnp
      ((hH r hr).2.2.2.trans (hH r' hr').2.2.2.symm)
  -- radius attached to each point
  have hR : ∀ z : ℂ, ∃ R : ℝ, z ∈ Ω → Adm R ∧ dist z c < R := by
    intro z
    by_cases hz : z ∈ Ω
    · obtain ⟨r₁, h₁, h₁Ω⟩ := hΩ z hz
      obtain ⟨r₂, h₂, h₂Ω⟩ := hΩ p hpΩ
      refine ⟨max r₁ r₂, fun _ ↦ ⟨⟨lt_of_le_of_lt dist_nonneg (h₁.trans_le (le_max_left _ _)),
        h₂.trans_le (le_max_right _ _), ?_⟩, h₁.trans_le (le_max_left _ _)⟩⟩
      rcases max_choice r₁ r₂ with h | h <;> rw [h] <;> assumption
    · exact ⟨0, fun h ↦ absurd h hz⟩
  choose R hR using hR
  have hlocal : ∀ z ∈ Ω, (fun w ↦ H (R w) w) =ᶠ[𝓝 z] H (R z) := by
    intro z hz
    have hzB : z ∈ ball c (R z) := mem_ball.mpr (hR z hz).2
    filter_upwards [isOpen_ball.mem_nhds hzB] with w hw
    have hwΩ : w ∈ Ω := (hR z hz).1.2.2 (ball_subset_closedBall hw)
    have hwB : w ∈ ball c (R w) := mem_ball.mpr (hR w hwΩ).2
    rcases le_total (R w) (R z) with h | h
    · exact hcompat _ _ (hR w hwΩ).1 (hR z hz).1 h hwB
    · exact (hcompat _ _ (hR z hz).1 (hR w hwΩ).1 h hw).symm
  refine ⟨fun w ↦ H (R w) w, ?_, ?_, ?_⟩
  · intro z hz
    exact ((hH (R z) (hR z hz).1).1 z (mem_ball.mpr (hR z hz).2)).congr (hlocal z hz).symm
  · intro z hz hnz
    exact (hH (R z) (hR z hz).1).2.1 z (mem_ball.mpr (hR z hz).2) hnz
  · intro z hz
    rw [analyticOrderAt_congr (hlocal z hz)]
    exact (hH (R z) (hR z hz).1).2.2.1 z (mem_ball.mpr (hR z hz).2)

/-- The plane: `Ω = ℂ`. -/
theorem exists_analytic_norm_eq_exp_univ {n : ℂ → ℕ} {v : ℂ → ℝ}
    (hball : LogModulusBallwise univ 0 n v) :
    ∃ h : ℂ → ℂ, AnalyticOnNhd ℂ h univ ∧ (∀ z, n z = 0 → ‖h z‖ = Real.exp (v z)) ∧
      ∀ z, analyticOrderAt h z = n z := by
  obtain ⟨h, h1, h2, h3⟩ := exists_analytic_norm_eq_exp (Ω := univ) (c := 0)
    (fun z _ ↦ ⟨dist z 0 + 1, by linarith, subset_univ _⟩) hball
  exact ⟨h, h1, fun z ↦ h2 z (mem_univ z), fun z ↦ h3 z (mem_univ z)⟩

/-- A ball `ball c R` (in particular the disc `𝔻 = ball 0 1`). -/
theorem exists_analytic_norm_eq_exp_ball {c : ℂ} {R : ℝ} {n : ℂ → ℕ} {v : ℂ → ℝ}
    (hball : LogModulusBallwise (ball c R) c n v) :
    ∃ h : ℂ → ℂ, AnalyticOnNhd ℂ h (ball c R) ∧
      (∀ z ∈ ball c R, n z = 0 → ‖h z‖ = Real.exp (v z)) ∧
      ∀ z ∈ ball c R, analyticOrderAt h z = n z := by
  refine exists_analytic_norm_eq_exp (fun z hz ↦ ?_) hball
  refine ⟨(dist z c + R) / 2, by linarith [mem_ball.mp hz], closedBall_subset_ball ?_⟩
  linarith [mem_ball.mp hz]

theorem exists_analytic_norm_eq_exp_disc {n : ℂ → ℕ} {v : ℂ → ℝ}
    (hball : LogModulusBallwise 𝔻 0 n v) :
    ∃ h : ℂ → ℂ, AnalyticOnNhd ℂ h 𝔻 ∧ (∀ z ∈ 𝔻, n z = 0 → ‖h z‖ = Real.exp (v z)) ∧
      ∀ z ∈ 𝔻, analyticOrderAt h z = n z :=
  exists_analytic_norm_eq_exp_ball hball

/-! ## Alternative entry point: the pointwise hypothesis -/

/-- **Pointwise hypothesis.**  `supp n` is locally finite in `Ω`, and near each `a ∈ Ω`,
`v = u_a + n(a) log |z - a|` off `supp n`, with `u_a` harmonic. -/
structure LogModulusLocal (Ω : Set ℂ) (n : ℂ → ℕ) (v : ℂ → ℝ) : Prop where
  finite_support : ∀ K ⊆ Ω, IsCompact K → (K ∩ Function.support n).Finite
  local_harmonic : ∀ a ∈ Ω, ∃ ε > 0, ∃ u : ℂ → ℝ, HarmonicOnNhd u (ball a ε) ∧
    ∀ z ∈ ball a ε, n z = 0 → v z = u z + n a * Real.log ‖z - a‖

/-- The pointwise hypothesis implies the ball-wise one: on `ball c r` the function
`W(w) := u_w(w) - log |∏_{ζ ∈ F, ζ ≠ w} (w - ζ)^{n ζ}|` is harmonic (near `z` it agrees with
`u_z - log |∏_{ζ ∈ F \ {z}} …|`), and `v = W + log |∏_{ζ ∈ F} …|` off `supp n`. -/
theorem LogModulusLocal.ballwise {Ω : Set ℂ} {n : ℂ → ℕ} {v : ℂ → ℝ}
    (hd : LogModulusLocal Ω n v) (c : ℂ) : LogModulusBallwise Ω c n v := by
  intro r hr hrΩ
  have hfin := hd.finite_support _ hrΩ (isCompact_closedBall c r)
  set F := hfin.toFinset with hFdef
  have hF : ∀ z ∈ ball c r, n z ≠ 0 → z ∈ F := fun z hz hnz ↦ by
    rw [hFdef, Set.Finite.mem_toFinset]
    exact ⟨ball_subset_closedBall hz, hnz⟩
  choose! ε hε u hu hvu using hd.local_harmonic
  have hΩ' : ∀ z ∈ ball c r, z ∈ Ω := fun z hz ↦ hrΩ (ball_subset_closedBall hz)
  -- the key identity off the zero set
  have hlog : ∀ z w : ℂ, (n z ≠ 0 → z ∈ F) → w ≠ z → n w = 0 →
      Real.log ‖zeroProd n F w‖ = n z * Real.log ‖w - z‖ + Real.log ‖zeroProd n (F.erase z) w‖ := by
    intro z w hzF hwz hnw
    rw [zeroProd_eq_mul_erase hzF w, norm_mul, norm_pow,
      Real.log_mul (pow_ne_zero _ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hwz)))
        (norm_ne_zero_iff.mpr ?_), Real.log_pow]
    have := zeroProd_ne_zero (F := F) hnw
    rw [zeroProd_eq_mul_erase hzF w] at this
    exact right_ne_zero_of_mul this
  refine ⟨F, hF, fun w ↦ u w w - Real.log ‖zeroProd n (F.erase w) w‖, ?_, ?_⟩
  · intro z hz
    have hzΩ := hΩ' z hz
    have hev : (fun w ↦ u w w - Real.log ‖zeroProd n (F.erase w) w‖) =ᶠ[𝓝 z]
        (fun w ↦ u z w - Real.log ‖zeroProd n (F.erase z) w‖) := by
      have h1 : ball c r ∈ 𝓝 z := isOpen_ball.mem_nhds hz
      have h2 : ball z (ε z) ∈ 𝓝 z := ball_mem_nhds z (hε z hzΩ)
      have h3 : ((F.erase z : Finset ℂ) : Set ℂ)ᶜ ∈ 𝓝 z :=
        (F.erase z).finite_toSet.isClosed.isOpen_compl.mem_nhds (by simp)
      filter_upwards [h1, h2, h3] with w hw1 hw2 hw3
      by_cases hwz : w = z
      · rw [hwz]
      have hnw : n w = 0 := by
        by_contra h
        exact hw3 (by simpa [Finset.mem_erase, hwz] using hF w hw1 h)
      have hvw := hvu w (hΩ' w hw1) w (mem_ball_self (hε w (hΩ' w hw1))) hnw
      have hvz := hvu z hzΩ w hw2 hnw
      have hP : zeroProd n (F.erase w) w = zeroProd n F w := by
        rw [zeroProd_eq_mul_erase (F := F) (a := w) (fun h ↦ absurd hnw h) w, hnw, pow_zero, one_mul]
      simp only [hP]
      rw [hlog z w (hF z hz) hwz hnw]
      push_cast [hnw] at hvw
      linarith
    refine (harmonicAt_congr_nhds hev).mpr ?_
    exact (hu z hzΩ z (mem_ball_self (hε z hzΩ))).sub
      ((zeroProd_analyticAt n _ z).harmonicAt_log_norm (zeroProd_erase_ne_zero n F z))
  · intro z hz hnz
    have hvz := hvu z (hΩ' z hz) z (mem_ball_self (hε z (hΩ' z hz))) hnz
    have hP : zeroProd n (F.erase z) z = zeroProd n F z := by
      rw [zeroProd_eq_mul_erase (F := F) (a := z) (fun h ↦ absurd hnz h) z, hnz, pow_zero, one_mul]
    simp only [hP]
    push_cast [hnz] at hvz
    linarith

/-! ## Weak (distributional) entry point, via M02 -/

/-- **M02 interface (Weyl's lemma for `Δ`)**, assumed here as a hypothesis: a locally integrable
function with zero weak Laplacian on an open set is a.e. equal to a harmonic function. -/
def WeylLaplacianStmt : Prop :=
  ∀ U : Set ℂ, IsOpen U → ∀ f : ℂ → ℝ, LocallyIntegrableOn f U →
    (∀ χ : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ → tsupport χ ⊆ U →
      ∫ z, f z * Laplacian.laplacian χ z = 0) →
    ∃ u : ℂ → ℝ, HarmonicOnNhd u U ∧ ∀ᵐ z ∂(volume.restrict U), f z = u z

/-- **M02 interface (the logarithmic kernel)**: `log |· - a|` is locally integrable and
`Δ log |z - a| = 2π δ_a` weakly. -/
def LogKernelStmt : Prop :=
  ∀ a : ℂ, LocallyIntegrable (fun z ↦ Real.log ‖z - a‖) ∧
    ∀ χ : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ →
      ∫ z, Real.log ‖z - a‖ * Laplacian.laplacian χ z = 2 * Real.pi * χ a

/-- **Weak hypothesis** (what M08 verifies for `v = ψ + S`): `Δv = 2π Σ n(ζ) δ_ζ` on `Ω`. -/
structure IsWeakLogModulus (Ω : Set ℂ) (n : ℂ → ℕ) (v : ℂ → ℝ) : Prop where
  finite_support : ∀ K ⊆ Ω, IsCompact K → (K ∩ Function.support n).Finite
  locallyIntegrableOn : LocallyIntegrableOn v Ω
  continuousOn : ContinuousOn v (Ω \ Function.support n)
  laplacian_eq : ∀ χ : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ → tsupport χ ⊆ Ω →
    ∫ z, v z * Laplacian.laplacian χ z = 2 * Real.pi * ∑ᶠ ζ, (n ζ : ℝ) * χ ζ

/-- Test functions: `Δχ` is continuous and supported in `tsupport χ`.  (Standard.) -/
lemma laplacian_testFunction {χ : ℂ → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) :
    Continuous (Laplacian.laplacian χ) ∧ tsupport (Laplacian.laplacian χ) ⊆ tsupport χ := by
  have hfun : Laplacian.laplacian χ =
      fun z ↦ iteratedFDeriv ℝ 2 χ z ![1, 1] + iteratedFDeriv ℝ 2 χ z ![I, I] :=
    laplacian_eq_iteratedFDeriv_complexPlane χ
  have hcont : Continuous (iteratedFDeriv ℝ 2 χ) :=
    hχ.continuous_iteratedFDeriv (WithTop.coe_le_coe.mpr (le_top : ((2 : ℕ) : ℕ∞) ≤ ⊤))
  refine ⟨?_, ?_⟩
  · rw [hfun]
    exact ((continuous_eval_const _).comp hcont).add ((continuous_eval_const _).comp hcont)
  · refine closure_minimal (fun z hz ↦ ?_) (isClosed_tsupport χ)
    apply tsupport_iteratedFDeriv_subset (𝕜 := ℝ) 2
    apply subset_tsupport
    intro h0
    apply hz
    rw [hfun]
    simp [h0]

/-- The weak hypothesis implies the ball-wise one (one application of Weyl per ball).
See `blueprint/M07_LogModulus.md`, §3. -/
theorem IsWeakLogModulus.ballwise (hweyl : WeylLaplacianStmt) (hker : LogKernelStmt)
    {Ω : Set ℂ} {n : ℂ → ℕ} {v : ℂ → ℝ} (hd : IsWeakLogModulus Ω n v) (c : ℂ) :
    LogModulusBallwise Ω c n v := by
  intro r hr hrΩ
  have hfin := hd.finite_support _ hrΩ (isCompact_closedBall c r)
  set F := hfin.toFinset with hFdef
  have hFmem : ∀ ζ, ζ ∈ F ↔ ζ ∈ closedBall c r ∧ n ζ ≠ 0 := fun ζ ↦ by
    rw [hFdef, Set.Finite.mem_toFinset]; rfl
  have hF : ∀ z ∈ ball c r, n z ≠ 0 → z ∈ F := fun z hz hnz ↦
    (hFmem z).2 ⟨ball_subset_closedBall hz, hnz⟩
  have hBΩ : ball c r ⊆ Ω := ball_subset_closedBall.trans hrΩ
  -- `L = Σ_{ζ ∈ F} n ζ log |z - ζ|` and `f = v - L`
  set L : ℂ → ℝ := fun z ↦ ∑ ζ ∈ F, (n ζ : ℝ) * Real.log ‖z - ζ‖ with hL
  have hLint : LocallyIntegrable L :=
    locallyIntegrable_finsetSum F fun ζ _ ↦ by
      have := (hker ζ).1.smul (n ζ : ℝ)
      exact this.congr (Eventually.of_forall fun z ↦ by simp [smul_eq_mul])
  set f : ℂ → ℝ := fun z ↦ v z - L z with hf
  have hfloc : LocallyIntegrableOn f (ball c r) :=
    (hd.locallyIntegrableOn.mono_set hBΩ).sub (hLint.locallyIntegrableOn _)
  -- (ii) `f` is weakly harmonic on the ball
  have hfΔ : ∀ χ : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ →
      tsupport χ ⊆ ball c r → ∫ z, f z * Laplacian.laplacian χ z = 0 := by
    intro χ hχ hc hs
    obtain ⟨hΔc, hΔs⟩ := laplacian_testFunction hχ
    have hΔcs : HasCompactSupport (Laplacian.laplacian χ) :=
      IsCompact.of_isClosed_subset hc (isClosed_tsupport _) hΔs
    have hv_int : Integrable (fun z ↦ v z * Laplacian.laplacian χ z) := by
      have hK : IsCompact (tsupport (Laplacian.laplacian χ)) := hΔcs
      have h1 : IntegrableOn v (tsupport (Laplacian.laplacian χ)) :=
        hd.locallyIntegrableOn.integrableOn_compact_subset (hΔs.trans (hs.trans hBΩ)) hK
      exact (h1.mul_continuousOn hΔc.continuousOn hK).integrable_of_forall_notMem_eq_zero
        (fun z hz ↦ by simp [image_eq_zero_of_notMem_tsupport hz])
    have hlog_int : ∀ ζ, Integrable (fun z ↦ Real.log ‖z - ζ‖ * Laplacian.laplacian χ z) :=
      fun ζ ↦ by
        simpa [smul_eq_mul] using
          (hker ζ).1.integrable_smul_right_of_hasCompactSupport hΔc hΔcs
    have hsplit : (fun z ↦ f z * Laplacian.laplacian χ z) = fun z ↦
        v z * Laplacian.laplacian χ z -
          ∑ ζ ∈ F, (n ζ : ℝ) * (Real.log ‖z - ζ‖ * Laplacian.laplacian χ z) := by
      ext z
      simp only [hf, hL, sub_mul, Finset.sum_mul, mul_assoc]
    rw [hsplit, integral_sub hv_int (integrable_finsetSum _ fun ζ _ ↦ (hlog_int ζ).const_mul _),
      integral_finsetSum _ fun ζ _ ↦ (hlog_int ζ).const_mul _,
      hd.laplacian_eq χ hχ hc (hs.trans hBΩ)]
    simp_rw [integral_const_mul, (hker _).2 χ hχ hc]
    have hsupp : Function.support (fun ζ ↦ (n ζ : ℝ) * χ ζ) ⊆ (F : Set ℂ) := by
      intro ζ hζ
      have hζ' : (n ζ : ℝ) ≠ 0 ∧ χ ζ ≠ 0 := by simpa using hζ
      exact (hFmem ζ).2 ⟨ball_subset_closedBall (hs (subset_tsupport _ hζ'.2)),
        by exact_mod_cast hζ'.1⟩
    rw [finsum_eq_sum_of_support_subset _ hsupp, Finset.mul_sum, sub_eq_zero]
    exact Finset.sum_congr rfl fun ζ _ ↦ by ring
  -- (iii) Weyl
  obtain ⟨u, hu, hae⟩ := hweyl (ball c r) isOpen_ball f hfloc hfΔ
  -- (iv) a.e. equality upgrades to equality on the open set `ball c r \ F`
  have hUo : IsOpen (ball c r \ (F : Set ℂ)) := isOpen_ball.sdiff F.finite_toSet.isClosed
  have hUn : ∀ z ∈ ball c r \ (F : Set ℂ), z ∈ Ω ∧ n z = 0 := fun z hz ↦
    ⟨hBΩ hz.1, by by_contra h; exact hz.2 (hF z hz.1 h)⟩
  have hfc : ContinuousOn f (ball c r \ (F : Set ℂ)) := by
    refine (hd.continuousOn.mono fun z hz ↦ ⟨(hUn z hz).1, by simpa using (hUn z hz).2⟩).sub ?_
    refine continuousOn_finsetSum _ fun ζ hζ ↦ continuousOn_const.mul ?_
    refine ContinuousOn.log (f := fun z ↦ ‖z - ζ‖) (by fun_prop) ?_
    intro z hz
    refine norm_ne_zero_iff.mpr (sub_ne_zero.mpr ?_)
    rintro rfl
    exact hz.2 hζ
  have hfu : EqOn f u (ball c r \ (F : Set ℂ)) :=
    Measure.eqOn_open_of_ae_eq (ae_restrict_of_ae_restrict_of_subset sdiff_subset hae) hUo hfc
      (hu.continuousOn.mono sdiff_subset)
  refine ⟨F, hF, u, hu, fun z hz hnz ↦ ?_⟩
  have hzF : z ∉ F := fun h ↦ ((hFmem z).1 h).2 hnz
  have h1 : f z = u z := hfu ⟨hz, hzF⟩
  have h2 : Real.log ‖zeroProd n F z‖ = L z := by
    have hne : ∀ ζ ∈ F, z - ζ ≠ 0 := fun ζ hζ h ↦ hzF (sub_eq_zero.mp h ▸ hζ)
    simp only [zeroProd, norm_prod, norm_pow, hL]
    rw [Real.log_prod fun ζ hζ ↦ pow_ne_zero _ (norm_ne_zero_iff.mpr (hne ζ hζ))]
    exact Finset.sum_congr rfl fun ζ _ ↦ Real.log_pow _ _
  simp only [hf] at h1
  rw [h2]
  linarith

/-- **M07, weak form**: the statement M08 calls. -/
theorem exists_analytic_norm_eq_exp_of_weak (hweyl : WeylLaplacianStmt) (hker : LogKernelStmt)
    {Ω : Set ℂ} {c : ℂ} (hΩ : ∀ z ∈ Ω, ∃ r, dist z c < r ∧ closedBall c r ⊆ Ω)
    {n : ℂ → ℕ} {v : ℂ → ℝ} (hd : IsWeakLogModulus Ω n v) :
    ∃ h : ℂ → ℂ, AnalyticOnNhd ℂ h Ω ∧ (∀ z ∈ Ω, n z = 0 → ‖h z‖ = Real.exp (v z)) ∧
      ∀ z ∈ Ω, analyticOrderAt h z = n z :=
  exists_analytic_norm_eq_exp hΩ (hd.ballwise hweyl hker c)

end OC
