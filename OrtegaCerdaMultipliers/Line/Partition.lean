import OrtegaCerdaMultipliers.Line.Basic

/-!
# M13 (Theorem5) — The signed distribution function, the knots, the barycentres

See `blueprint/M13_Theorem5.md` §3.2–§3.4.

Internal structure: `LineHyp μ r α` bundles the standing hypotheses of §3.3 (the knot lemmas are
proved in its namespace and re-exported with the scaffold's signatures); `LineConsts μ r C₂ c₀ α₁`
bundles the constants of §2 (mass radius `r`, Claim 2 constant `C₂`, barycentre margin `c₀`,
largest admissible `α₁`), obtained once by `IsLineMeasure.exists_lineConsts`.
-/

open MeasureTheory Metric Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace OC

/-- Signed distribution function of `σ_α = μ − 2α·dt`: `G_α(t) = σ_α((0,t])` (oriented). -/
def lineCDF (μ : Measure ℂ) (α t : ℝ) : ℝ :=
  (if 0 ≤ t then (linePull μ (Ioc 0 t)).toReal else -(linePull μ (Ioc t 0)).toReal)
    - 2 * α * t

/-- First hitting time of the level `s` by `G_α`. -/
def lineLevel (μ : Measure ℂ) (α s : ℝ) : ℝ := sInf {t : ℝ | lineCDF μ α t = s}

/-- Knots `e_k = T_α(4π k)`; the cells are `I_k = (e_k, e_{k+1}]`, with `σ_α(I_k) = 4π`. -/
def lineKnot (μ : Measure ℂ) (α : ℝ) (k : ℤ) : ℝ := lineLevel μ α (4 * Real.pi * k)

/-- Length `a_k = e_{k+1} − e_k` of the cell `I_k`. -/
def lineLength (μ : Measure ℂ) (α : ℝ) (k : ℤ) : ℝ := lineKnot μ α (k + 1) - lineKnot μ α k

/-- Signed barycentre `λ_k = (1/4π) ∫_{I_k} t dσ_α(t)`. -/
def lineCentre (μ : Measure ℂ) (α : ℝ) (k : ℤ) : ℝ :=
  ((∫ t in Ioc (lineKnot μ α k) (lineKnot μ α (k + 1)), t ∂linePull μ) -
    2 * α * ∫ t in lineKnot μ α k..lineKnot μ α (k + 1), t) / (4 * Real.pi)

/-- The two nodes `λ_k ± s a_k` of the cell `I_k` (`b = true` is `+`). -/
def lineNode (μ : Measure ℂ) (α s : ℝ) (k : ℤ) (b : Bool) : ℝ :=
  lineCentre μ α k + (if b then s else -s) * lineLength μ α k

/-! 13.2 the signed distribution function -/

theorem IsLineMeasure.m13_toReal_Ioc_add {μ : Measure ℂ} (hμ : IsLineMeasure μ) {a b c : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) :
    (linePull μ (Ioc a c)).toReal =
      (linePull μ (Ioc a b)).toReal + (linePull μ (Ioc b c)).toReal := by
  rw [← Ioc_union_Ioc_eq_Ioc hab hbc, measure_union (Ioc_disjoint_Ioc_of_le le_rfl)
    measurableSet_Ioc, ENNReal.toReal_add (hμ.linePull_Ioc_lt_top a b).ne
    (hμ.linePull_Ioc_lt_top b c).ne]

theorem lineCDF_sub {μ : Measure ℂ} (hμ : IsLineMeasure μ) (α : ℝ) {a b : ℝ} (hab : a ≤ b) :
    lineCDF μ α b - lineCDF μ α a = (linePull μ (Ioc a b)).toReal - 2 * α * (b - a) := by
  unfold lineCDF
  rcases le_or_gt 0 a with ha | ha
  · rw [ite_eq_left ha, ite_eq_left (ha.trans hab), hμ.m13_toReal_Ioc_add ha hab]; ring
  rcases le_or_gt 0 b with hb | hb
  · rw [ite_eq_right (not_le.2 ha), ite_eq_left hb, hμ.m13_toReal_Ioc_add ha.le hb]; ring
  · rw [ite_eq_right (not_le.2 ha), ite_eq_right (not_le.2 hb), hμ.m13_toReal_Ioc_add hab hb.le]; ring

theorem lineCDF_eq (μ : Measure ℂ) (α t : ℝ) : lineCDF μ α t = lineCDF μ 0 t - 2 * α * t := by
  simp [lineCDF]

theorem IsLineMeasure.m13_measure_Icc_tendsto {μ : Measure ℂ} (hμ : IsLineMeasure μ) (t₀ : ℝ) :
    Tendsto (fun δ : ℝ ↦ linePull μ (Icc (t₀ - δ) (t₀ + δ))) (𝓝[>] 0) (𝓝 0) := by
  have h := tendsto_measure_biInter_gt (μ := linePull μ) (s := fun δ : ℝ ↦ Icc (t₀ - δ) (t₀ + δ))
    (a := 0) (fun _ _ ↦ measurableSet_Icc.nullMeasurableSet)
    (fun i j _ hij ↦ Icc_subset_Icc (by linarith) (by linarith))
    ⟨1, one_pos, (hμ.m13_linePull_compact_lt_top isCompact_Icc).ne⟩
  have hI : (⋂ r > (0 : ℝ), Icc (t₀ - r) (t₀ + r)) = {t₀} := by
    ext t
    simp only [mem_iInter, mem_Icc, mem_singleton_iff]
    constructor
    · intro h
      by_contra hne
      have hpos : 0 < |t - t₀| := abs_pos.2 (sub_ne_zero.2 hne)
      have := h (|t - t₀| / 2) (by positivity)
      rcases le_or_gt 0 (t - t₀) with h0 | h0
      · rw [abs_of_nonneg h0] at this hpos; linarith [this.2]
      · rw [abs_of_neg h0] at this hpos; linarith [this.1]
    · rintro rfl r hr; constructor <;> linarith
  rw [hI, linePull_apply, image_singleton, hμ.measure_singleton] at h
  exact h

theorem continuous_lineCDF {μ : Measure ℂ} (hμ : IsLineMeasure μ) (α : ℝ) :
    Continuous (lineCDF μ α) := by
  have key : Continuous (lineCDF μ 0) := by
    rw [Metric.continuous_iff]
    intro t₀ ε hε
    have h := (hμ.m13_measure_Icc_tendsto t₀)
    have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), linePull μ (Icc (t₀ - δ) (t₀ + δ)) < ENNReal.ofReal ε :=
      (tendsto_order.1 h).2 _ (by simpa using hε)
    obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
    refine ⟨u / 2, by simp at hu; linarith, fun t ht ↦ ?_⟩
    have hδ : linePull μ (Icc (t₀ - u / 2) (t₀ + u / 2)) < ENNReal.ofReal ε :=
      hsub ⟨by simp at hu; linarith, by simp at hu; linarith⟩
    have hfin := (hμ.m13_linePull_compact_lt_top (isCompact_Icc (a := t₀ - u / 2) (b := t₀ + u / 2)))
    have hlt : (linePull μ (Icc (t₀ - u / 2) (t₀ + u / 2))).toReal < ε := by
      rw [← ENNReal.toReal_ofReal hε.le]
      exact (ENNReal.toReal_lt_toReal hfin.ne ENNReal.ofReal_ne_top).2 hδ
    rw [Real.dist_eq] at ht ⊢
    have habs := abs_lt.1 ht
    rcases le_total t₀ t with h1 | h1
    · have := lineCDF_sub hμ 0 h1
      have hle : (linePull μ (Ioc t₀ t)).toReal ≤ (linePull μ (Icc (t₀ - u / 2) (t₀ + u / 2))).toReal :=
        ENNReal.toReal_mono hfin.ne (measure_mono (fun x hx ↦ ⟨by linarith [hx.1], by linarith [hx.2]⟩))
      rw [abs_lt]; constructor <;> nlinarith [ENNReal.toReal_nonneg (a := linePull μ (Ioc t₀ t))]
    · have := lineCDF_sub hμ 0 h1
      have hle : (linePull μ (Ioc t t₀)).toReal ≤ (linePull μ (Icc (t₀ - u / 2) (t₀ + u / 2))).toReal :=
        ENNReal.toReal_mono hfin.ne (measure_mono (fun x hx ↦ ⟨by linarith [hx.1], by linarith [hx.2]⟩))
      rw [abs_lt]; constructor <;> nlinarith [ENNReal.toReal_nonneg (a := linePull μ (Ioc t t₀))]
  have : lineCDF μ α = fun t ↦ lineCDF μ 0 t - 2 * α * t := funext (lineCDF_eq μ α)
  rw [this]
  exact key.sub (continuous_const.mul continuous_id)

theorem lineCDF_add_ge {μ : Measure ℂ} (hμ : IsLineMeasure μ) {r α : ℝ} (hr : 0 < r)
    (hmr : ∀ x : ℝ, 1 < μ (lineInterval x r)) (hα : 0 ≤ α) (hαr : α * r ≤ 1 / 8) (t : ℝ) :
    lineCDF μ α t + 1 / 2 ≤ lineCDF μ α (t + 2 * r) := by
  have h := lineCDF_sub hμ α (show t ≤ t + 2 * r by linarith)
  have h1 : 1 < (linePull μ (Ioc t (t + 2 * r))).toReal := by
    have hm := hmr (t + r)
    rw [← m13_linePull_Ioo] at hm
    have hm' : 1 < linePull μ (Ioc t (t + 2 * r)) :=
      lt_of_lt_of_le hm (measure_mono (fun x hx ↦ ⟨by linarith [hx.1], by linarith [hx.2]⟩))
    have := (ENNReal.toReal_lt_toReal ENNReal.one_ne_top (hμ.linePull_Ioc_lt_top _ _).ne).2 hm'
    simpa using this
  nlinarith



/-- The standing hypotheses of §3.3, bundled. -/
structure LineHyp (μ : Measure ℂ) (r α : ℝ) : Prop where
  hμ : IsLineMeasure μ
  hr : 0 < r
  hmr : ∀ x : ℝ, 1 < μ (lineInterval x r)
  hα : 0 ≤ α
  hαr : α * r ≤ 1 / 8

namespace LineHyp

variable {μ : Measure ℂ} {r α : ℝ} (h : LineHyp μ r α)
include h

theorem cont : Continuous (lineCDF μ α) := continuous_lineCDF h.hμ α

theorem add_ge (t : ℝ) : lineCDF μ α t + 1 / 2 ≤ lineCDF μ α (t + 2 * r) :=
  lineCDF_add_ge h.hμ h.hr h.hmr h.hα h.hαr t

theorem add_nat_ge (t : ℝ) (n : ℕ) : lineCDF μ α t + n / 2 ≤ lineCDF μ α (t + 2 * r * n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have := h.add_ge (t + 2 * r * n)
    push_cast
    rw [show t + 2 * r * (n + 1) = t + 2 * r * n + 2 * r by ring]
    linarith

/-- `G → +∞` at `+∞`. -/
theorem eventually_gt (s : ℝ) : ∃ T : ℝ, ∀ t, T ≤ t → s < lineCDF μ α t := by
  obtain ⟨m, -, hm⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 (by linarith [h.hr] :
    (0 : ℝ) ≤ 2 * r)) h.cont.continuousOn
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * (s - lineCDF μ α m) + 2)
  refine ⟨2 * r * N, fun t ht ↦ ?_⟩
  have hr := h.hr
  set n := ⌊t / (2 * r)⌋₊ with hn
  have ht0 : 0 ≤ t := le_trans (by positivity) ht
  have hq : 0 ≤ t / (2 * r) := by positivity
  have h1 : (n : ℝ) ≤ t / (2 * r) := Nat.floor_le hq
  have h2 : t / (2 * r) < n + 1 := Nat.lt_floor_add_one _
  have hNn : (N : ℝ) ≤ n + 1 := by
    have : (N : ℝ) ≤ t / (2 * r) := by rw [le_div_iff₀ (by positivity)]; linarith
    linarith
  set t' := t - 2 * r * n
  have ht' : t' ∈ Icc 0 (2 * r) := by
    constructor
    · have := (le_div_iff₀ (by positivity : (0:ℝ) < 2 * r)).1 h1; simp only [t']; linarith
    · have := (div_lt_iff₀ (by positivity : (0:ℝ) < 2 * r)).1 h2; simp only [t']; linarith
  have := h.add_nat_ge t' n
  rw [show t' + 2 * r * n = t by simp only [t']; ring] at this
  have := hm ht'
  simp only [mem_ofPred_eq] at this
  linarith

/-- `G → −∞` at `−∞`. -/
theorem eventually_lt (s : ℝ) : ∃ T : ℝ, ∀ t, t ≤ T → lineCDF μ α t < s := by
  obtain ⟨m, -, hm⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 (by linarith [h.hr] :
    -(2 * r) ≤ 0)) h.cont.continuousOn
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * (lineCDF μ α m - s) + 2)
  refine ⟨-(2 * r * N), fun t ht ↦ ?_⟩
  have hr := h.hr
  set n := ⌊-t / (2 * r)⌋₊ with hn
  have ht0 : 0 ≤ -t := by have : (0:ℝ) ≤ 2 * r * N := by positivity
                          linarith
  have hq : 0 ≤ -t / (2 * r) := by positivity
  have h1 : (n : ℝ) ≤ -t / (2 * r) := Nat.floor_le hq
  have h2 : -t / (2 * r) < n + 1 := Nat.lt_floor_add_one _
  have hNn : (N : ℝ) ≤ n + 1 := by
    have : (N : ℝ) ≤ -t / (2 * r) := by rw [le_div_iff₀ (by positivity)]; linarith
    linarith
  set t' := t + 2 * r * n
  have ht' : t' ∈ Icc (-(2 * r)) 0 := by
    constructor
    · have := (div_lt_iff₀ (by positivity : (0:ℝ) < 2 * r)).1 h2; simp only [t']; linarith
    · have := (le_div_iff₀ (by positivity : (0:ℝ) < 2 * r)).1 h1; simp only [t']; linarith
  have := h.add_nat_ge t n
  have := hm ht'
  simp only [mem_ofPred_eq] at this
  linarith

theorem level_set_nonempty (s : ℝ) : {t : ℝ | lineCDF μ α t = s}.Nonempty := by
  obtain ⟨T₁, hT₁⟩ := h.eventually_lt s
  obtain ⟨T₂, hT₂⟩ := h.eventually_gt s
  have hle : T₁ ≤ max T₁ T₂ := le_max_left _ _
  obtain ⟨t, -, ht⟩ := intermediate_value_Icc hle h.cont.continuousOn
    ⟨(hT₁ T₁ le_rfl).le, (hT₂ _ (le_max_right _ _)).le⟩
  exact ⟨t, ht⟩

theorem level_set_bddBelow (s : ℝ) : BddBelow {t : ℝ | lineCDF μ α t = s} := by
  obtain ⟨T₁, hT₁⟩ := h.eventually_lt s
  refine ⟨T₁, fun t ht ↦ ?_⟩
  by_contra hlt
  have := hT₁ t (not_le.1 hlt).le
  simp only [mem_ofPred_eq] at ht
  linarith

theorem lineCDF_lineLevel (s : ℝ) : lineCDF μ α (lineLevel μ α s) = s :=
  (isClosed_eq h.cont continuous_const).csInf_mem (h.level_set_nonempty s)
    (h.level_set_bddBelow s)

/-- First hitting time: `G < s` before `T(s)`. -/
theorem lt_of_lt_lineLevel {s t : ℝ} (ht : t < lineLevel μ α s) : lineCDF μ α t < s := by
  by_contra hge
  push Not at hge
  obtain ⟨T₁, hT₁⟩ := h.eventually_lt s
  have hle : min T₁ t ≤ t := min_le_right _ _
  obtain ⟨t', ht'm, ht'⟩ := intermediate_value_Icc hle h.cont.continuousOn
    ⟨(hT₁ _ (min_le_left _ _)).le, hge⟩
  have : lineLevel μ α s ≤ t' := csInf_le (h.level_set_bddBelow s) ht'
  linarith [ht'm.2]

theorem lineLevel_strictMono : StrictMono (lineLevel μ α) := by
  intro s s' hss'
  by_contra hle
  push Not at hle
  rcases hle.lt_or_eq with hlt | heq
  · have := h.lt_of_lt_lineLevel hlt
    rw [h.lineCDF_lineLevel] at this
    linarith
  · have h1 := h.lineCDF_lineLevel s
    have h2 := h.lineCDF_lineLevel s'
    rw [heq] at h2
    linarith

theorem lineCDF_lineKnot (k : ℤ) : lineCDF μ α (lineKnot μ α k) = 4 * Real.pi * k :=
  h.lineCDF_lineLevel _

theorem lineKnot_strictMono : StrictMono (lineKnot μ α) := fun k k' hk ↦
  h.lineLevel_strictMono (by
    have : (k : ℝ) < k' := by exact_mod_cast hk
    nlinarith [Real.pi_pos])

theorem lineLength_le (k : ℤ) : lineLength μ α k ≤ 52 * r := by
  unfold lineLength
  by_contra hlt
  push Not at hlt
  have h1 := h.add_nat_ge (lineKnot μ α k) 26
  rw [h.lineCDF_lineKnot] at h1
  have h2 := h.lt_of_lt_lineLevel (s := 4 * Real.pi * ((k + 1 : ℤ) : ℝ))
    (t := lineKnot μ α k + 2 * r * (26 : ℕ)) (by
      have : lineKnot μ α (k + 1) = lineLevel μ α (4 * Real.pi * ((k + 1 : ℤ) : ℝ)) := rfl
      push_cast at this ⊢; linarith)
  push_cast at h1 h2
  linarith [Real.pi_lt_d2]

theorem lineLength_pos (k : ℤ) : 0 < lineLength μ α k := by
  unfold lineLength
  linarith [h.lineKnot_strictMono (lt_add_one k)]

theorem exists_le_lineKnot (t : ℝ) : ∃ k : ℤ, t ≤ lineKnot μ α k := by
  by_contra hall
  push Not at hall
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (h.cont.continuousOn (s := Icc (lineKnot μ α 0) t))
  obtain ⟨n, hn⟩ := exists_nat_gt (C / (4 * Real.pi))
  have hmem : lineKnot μ α n ∈ Icc (lineKnot μ α 0) t :=
    ⟨h.lineKnot_strictMono.monotone (by positivity), (hall n).le⟩
  have := hC _ hmem
  rw [h.lineCDF_lineKnot, Real.norm_eq_abs] at this
  have := le_of_abs_le this
  rw [div_lt_iff₀ (by positivity)] at hn
  push_cast at this
  nlinarith [Real.pi_pos]

theorem exists_lineKnot_lt (t : ℝ) : ∃ k : ℤ, lineKnot μ α k < t := by
  by_contra hall
  push Not at hall
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (h.cont.continuousOn (s := Icc t (lineKnot μ α 0)))
  obtain ⟨n, hn⟩ := exists_nat_gt (C / (4 * Real.pi))
  have hmem : lineKnot μ α (-n) ∈ Icc t (lineKnot μ α 0) :=
    ⟨hall _, h.lineKnot_strictMono.monotone (by simp)⟩
  have := hC _ hmem
  rw [h.lineCDF_lineKnot, Real.norm_eq_abs] at this
  have := neg_le_of_abs_le this
  rw [div_lt_iff₀ (by positivity)] at hn
  push_cast at this
  nlinarith [Real.pi_pos]

theorem existsUnique_mem (t : ℝ) :
    ∃! k : ℤ, t ∈ Ioc (lineKnot μ α k) (lineKnot μ α (k + 1)) := by
  obtain ⟨k₀, hk₀⟩ := h.exists_lineKnot_lt t
  obtain ⟨m, hm, hmin⟩ := Int.exists_least_of_bdd (P := fun k ↦ t ≤ lineKnot μ α k)
    ⟨k₀, fun k hk ↦ by
      by_contra hlt; push Not at hlt
      linarith [h.lineKnot_strictMono.monotone hlt.le]⟩ (h.exists_le_lineKnot t)
  refine ⟨m - 1, ⟨?_, by simpa using hm⟩, fun j hj ↦ ?_⟩
  · by_contra hle; push Not at hle
    have := hmin (m - 1) hle
    omega
  · have h1 := hmin (j + 1) hj.2
    by_contra hne
    have : m ≤ j := by omega
    linarith [h.lineKnot_strictMono.monotone this, hj.1]

/-- Only finitely many cells meet a bounded interval. -/
theorem cells_meeting_subset (a b : ℝ) : ∃ K₀ K₁ : ℤ, ∀ k : ℤ,
    a < lineKnot μ α (k + 1) → lineKnot μ α k < b → K₀ ≤ k ∧ k ≤ K₁ := by
  obtain ⟨K₀, hK₀⟩ := h.exists_lineKnot_lt a
  obtain ⟨K₁, hK₁⟩ := h.exists_le_lineKnot b
  refine ⟨K₀, K₁, fun k hka hkb ↦ ⟨?_, ?_⟩⟩
  · by_contra hlt; push Not at hlt
    have : k + 1 ≤ K₀ := by omega
    linarith [h.lineKnot_strictMono.monotone this]
  · by_contra hlt; push Not at hlt
    linarith [h.lineKnot_strictMono.monotone hlt.le]

theorem linePull_Ioc_lineKnot (k : ℤ) :
    linePull μ (Ioc (lineKnot μ α k) (lineKnot μ α (k + 1))) =
      ENNReal.ofReal (4 * Real.pi + 2 * α * lineLength μ α k) := by
  have hs := lineCDF_sub h.hμ α (h.lineKnot_strictMono (lt_add_one k)).le
  rw [h.lineCDF_lineKnot, h.lineCDF_lineKnot] at hs
  push_cast at hs
  rw [← ENNReal.ofReal_toReal (h.hμ.linePull_Ioc_lt_top _ _).ne]
  congr 1
  unfold lineLength
  linarith

theorem toReal_linePull_Ioc_lineKnot (k : ℤ) :
    (linePull μ (Ioc (lineKnot μ α k) (lineKnot μ α (k + 1)))).toReal =
      4 * Real.pi + 2 * α * lineLength μ α k := by
  rw [h.linePull_Ioc_lineKnot, ENNReal.toReal_ofReal]
  have := h.lineLength_pos k
  have := h.hα
  positivity

end LineHyp


/-! 13.3 the knots -/
theorem lineCDF_lineKnot {μ : Measure ℂ} (hμ : IsLineMeasure μ) {r α : ℝ} (hr : 0 < r)
    (hmr : ∀ x : ℝ, 1 < μ (lineInterval x r)) (hα : 0 ≤ α) (hαr : α * r ≤ 1 / 8) (k : ℤ) :
    lineCDF μ α (lineKnot μ α k) = 4 * Real.pi * k :=
  (LineHyp.mk hμ hr hmr hα hαr).lineCDF_lineKnot k
theorem lineKnot_strictMono {μ : Measure ℂ} (hμ : IsLineMeasure μ) {r α : ℝ} (hr : 0 < r)
    (hmr : ∀ x : ℝ, 1 < μ (lineInterval x r)) (hα : 0 ≤ α) (hαr : α * r ≤ 1 / 8) :
    StrictMono (lineKnot μ α) :=
  (LineHyp.mk hμ hr hmr hα hαr).lineKnot_strictMono
theorem lineLength_le {μ : Measure ℂ} (hμ : IsLineMeasure μ) {r α : ℝ} (hr : 0 < r)
    (hmr : ∀ x : ℝ, 1 < μ (lineInterval x r)) (hα : 0 ≤ α) (hαr : α * r ≤ 1 / 8) (k : ℤ) :
    lineLength μ α k ≤ 52 * r :=
  (LineHyp.mk hμ hr hmr hα hαr).lineLength_le k
theorem existsUnique_lineKnot_mem {μ : Measure ℂ} (hμ : IsLineMeasure μ) {r α : ℝ} (hr : 0 < r)
    (hmr : ∀ x : ℝ, 1 < μ (lineInterval x r)) (hα : 0 ≤ α) (hαr : α * r ≤ 1 / 8) (t : ℝ) :
    ∃! k : ℤ, t ∈ Ioc (lineKnot μ α k) (lineKnot μ α (k + 1)) :=
  (LineHyp.mk hμ hr hmr hα hαr).existsUnique_mem t
theorem linePull_Ioc_lineKnot {μ : Measure ℂ} (hμ : IsLineMeasure μ) {r α : ℝ} (hr : 0 < r)
    (hmr : ∀ x : ℝ, 1 < μ (lineInterval x r)) (hα : 0 ≤ α) (hαr : α * r ≤ 1 / 8) (k : ℤ) :
    linePull μ (Ioc (lineKnot μ α k) (lineKnot μ α (k + 1))) =
      ENNReal.ofReal (4 * Real.pi + 2 * α * lineLength μ α k) :=
  (LineHyp.mk hμ hr hmr hα hαr).linePull_Ioc_lineKnot k

/-! 13.4 the barycentre stays in the middle of its cell; the nodes are separated -/

namespace LineHyp

variable {μ : Measure ℂ} {r α : ℝ} (h : LineHyp μ r α)
include h

/-- Claim 2 (L7) on the cells. -/
theorem cell_rho {C₂ : ℝ} (hC₂ : ∀ a b : ℝ, a < b →
      ENNReal.ofReal (4 * Real.pi) ≤ μ ((fun t : ℝ ↦ (t : ℂ)) '' Ioc a b) →
      μ ((fun t : ℝ ↦ (t : ℂ)) '' Ioc a b) ≤ ENNReal.ofReal (4 * Real.pi + 13) →
      ∀ t ∈ Icc a b, massRadiusLine μ t ≤ b - a ∧ b - a ≤ C₂ * massRadiusLine μ t)
    (k : ℤ) : ∀ t ∈ Icc (lineKnot μ α k) (lineKnot μ α (k + 1)),
      massRadiusLine μ t ≤ lineLength μ α k ∧ lineLength μ α k ≤ C₂ * massRadiusLine μ t := by
  have hpos := h.lineLength_pos k
  have hle := h.lineLength_le k
  have hm := h.linePull_Ioc_lineKnot k
  rw [linePull_apply] at hm
  refine hC₂ _ _ (h.lineKnot_strictMono (lt_add_one k)) ?_ ?_
  · rw [hm]; exact ENNReal.ofReal_le_ofReal (by nlinarith [h.hα])
  · rw [hm]; exact ENNReal.ofReal_le_ofReal (by nlinarith [h.hα, h.hαr, h.hr])

theorem integrableOn_id (a b : ℝ) : IntegrableOn (fun t : ℝ ↦ t) (Ioc a b) (linePull μ) := by
  have := h.hμ.m13_isFiniteMeasureOnCompacts'
  exact (continuous_id.integrableOn_Icc (a := a) (b := b)).mono_set Ioc_subset_Icc_self

omit h in
/-- Doubling twice: the right half of an interval carries a fixed fraction of its mass. -/
theorem measure_Ioc_le_half {C : ℝ≥0}
    (hC : ∀ x ρ : ℝ, 0 < ρ → ρ ≤ 26 * r → μ (lineInterval x (2 * ρ)) ≤ C * μ (lineInterval x ρ))
    {a b : ℝ} (hab : a < b) (hb : b - a ≤ 52 * r) :
    linePull μ (Ioc a b) ≤ C ^ 2 * linePull μ (Ioo ((a + b) / 2) b) ∧
      linePull μ (Ioc a b) ≤ C ^ 2 * linePull μ (Ioo a ((a + b) / 2)) := by
  set ℓ := b - a
  have hℓ : 0 < ℓ := sub_pos.2 hab
  have key : ∀ c : ℝ, Ioc a b ⊆ Ioo (c - ℓ) (c + ℓ) → linePull μ (Ioc a b) ≤
      C ^ 2 * linePull μ (Ioo (c - ℓ / 4) (c + ℓ / 4)) := by
    intro c hc
    calc linePull μ (Ioc a b) ≤ linePull μ (Ioo (c - ℓ) (c + ℓ)) := measure_mono hc
      _ = μ (lineInterval c (2 * (2 * (ℓ / 4)))) := by rw [m13_linePull_Ioo]; ring_nf
      _ ≤ C * μ (lineInterval c (2 * (ℓ / 4))) := hC _ _ (by positivity) (by linarith)
      _ ≤ C * (C * μ (lineInterval c (ℓ / 4))) := by
          gcongr; exact hC _ _ (by positivity) (by linarith)
      _ = C ^ 2 * linePull μ (Ioo (c - ℓ / 4) (c + ℓ / 4)) := by
          rw [m13_linePull_Ioo, ← mul_assoc, pow_two]
  constructor
  · have := key (a + 3 * ℓ / 4) (fun x hx ↦ ⟨by linarith [hx.1], by linarith [hx.2]⟩)
    convert this using 4 <;> simp only [ℓ] <;> ring
  · have := key (a + ℓ / 4) (fun x hx ↦ ⟨by linarith [hx.1], by linarith [hx.2]⟩)
    convert this using 4 <;> simp only [ℓ] <;> ring

/-- The signed barycentre stays in the middle of its cell. -/
theorem centre_mem {C : ℝ≥0} (hC1 : 1 ≤ C)
    (hC : ∀ x ρ : ℝ, 0 < ρ → ρ ≤ 26 * r → μ (lineInterval x (2 * ρ)) ≤ C * μ (lineInterval x ρ))
    (hαC : α * (52 * r) ≤ Real.pi / (C : ℝ) ^ 2) (k : ℤ) :
    lineKnot μ α k + 1 / (4 * (C : ℝ) ^ 2) * lineLength μ α k ≤ lineCentre μ α k ∧
      lineCentre μ α k ≤ lineKnot μ α (k + 1) - 1 / (4 * (C : ℝ) ^ 2) * lineLength μ α k := by
  set a := lineKnot μ α k
  set b := lineKnot μ α (k + 1)
  have hab : a < b := h.lineKnot_strictMono (lt_add_one k)
  have hℓ : lineLength μ α k = b - a := rfl
  have hℓle := h.lineLength_le k
  rw [hℓ] at hℓle ⊢
  have hM := h.toReal_linePull_Ioc_lineKnot k
  rw [hℓ] at hM
  set M := (linePull μ (Ioc a b)).toReal
  have hMfin := h.hμ.linePull_Ioc_lt_top a b
  have hint := h.integrableOn_id a b
  have hid : ∫ t in a..b, t = (b ^ 2 - a ^ 2) / 2 := integral_id
  have hlam : lineCentre μ α k = ((∫ t in Ioc a b, t ∂linePull μ) - 2 * α * ((b ^ 2 - a ^ 2) / 2)) /
      (4 * Real.pi) := by rw [lineCentre, hid]
  have hC0 : (0 : ℝ) < (C : ℝ) := by exact_mod_cast (zero_lt_one.trans_le hC1)
  obtain ⟨hR, hL⟩ := LineHyp.measure_Ioc_le_half (μ := μ) hC hab hℓle
  have hfinR : linePull μ (Ioo ((a + b) / 2) b) ≠ ∞ :=
    ne_top_of_le_ne_top hMfin.ne (measure_mono (fun x hx ↦ ⟨by linarith [hx.1], hx.2.le⟩))
  have hfinL : linePull μ (Ioo a ((a + b) / 2)) ≠ ∞ :=
    ne_top_of_le_ne_top hMfin.ne (measure_mono (fun x hx ↦ ⟨hx.1, by linarith [hx.2]⟩))
  have toR : ∀ {J : Set ℝ}, linePull μ J ≠ ∞ → linePull μ (Ioc a b) ≤ C ^ 2 * linePull μ J →
      M ≤ (C : ℝ) ^ 2 * (linePull μ J).toReal := by
    intro J hJ hle
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) hJ) hle
    rwa [ENNReal.toReal_mul] at this
  have hRr := toR hfinR hR
  have hLr := toR hfinL hL
  have hπ := Real.pi_pos
  have hα := h.hα
  -- integrals over the halves
  have hIR : (b - a) / 2 * (linePull μ (Ioo ((a + b) / 2) b)).toReal ≤
      ∫ t in Ioc a b, (t - a) ∂linePull μ := by
    have h1 : ∫ t in Ioo ((a + b) / 2) b, (t - a) ∂linePull μ ≤
        ∫ t in Ioc a b, (t - a) ∂linePull μ :=
      setIntegral_mono_set (hint.sub (integrableOn_const hMfin.ne))
        ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun t ht ↦
          by simp only [Pi.zero_apply]; linarith [ht.1]))
        (LE.le.eventuallyLE (show _ ≤ Ioc a b from fun x hx ↦ ⟨by linarith [hx.1], hx.2.le⟩))
    have h2 := setIntegral_ge_of_const_le_real (f := fun t ↦ t - a) (c := (b - a) / 2)
      (μ := linePull μ) measurableSet_Ioo hfinR (fun t ht ↦ by linarith [ht.1])
      ((hint.sub (integrableOn_const hMfin.ne)).mono_set
        (fun x hx ↦ ⟨by linarith [hx.1], hx.2.le⟩))
    rw [measureReal_def] at h2
    linarith
  have hIL : (b - a) / 2 * (linePull μ (Ioo a ((a + b) / 2))).toReal ≤
      ∫ t in Ioc a b, (b - t) ∂linePull μ := by
    have h1 : ∫ t in Ioo a ((a + b) / 2), (b - t) ∂linePull μ ≤
        ∫ t in Ioc a b, (b - t) ∂linePull μ :=
      setIntegral_mono_set ((integrableOn_const hMfin.ne).sub hint)
        ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun t ht ↦
          by simp only [Pi.zero_apply]; linarith [ht.2]))
        (LE.le.eventuallyLE (show _ ≤ Ioc a b from fun x hx ↦ ⟨hx.1, by linarith [hx.2]⟩))
    have h2 := setIntegral_ge_of_const_le_real (f := fun t ↦ b - t) (c := (b - a) / 2)
      (μ := linePull μ) measurableSet_Ioo hfinL (fun t ht ↦ by linarith [ht.2])
      (((integrableOn_const hMfin.ne).sub hint).mono_set
        (fun x hx ↦ ⟨hx.1, by linarith [hx.2]⟩))
    rw [measureReal_def] at h2
    linarith
  have e1 : ∫ t in Ioc a b, (t - a) ∂linePull μ = (∫ t in Ioc a b, t ∂linePull μ) - M * a := by
    rw [integral_sub hint (integrableOn_const hMfin.ne), setIntegral_const, measureReal_def,
      smul_eq_mul]
  have e2 : ∫ t in Ioc a b, (b - t) ∂linePull μ = M * b - (∫ t in Ioc a b, t ∂linePull μ) := by
    rw [integral_sub (integrableOn_const hMfin.ne) hint, setIntegral_const, measureReal_def,
      smul_eq_mul]
  rw [e1] at hIR
  rw [e2] at hIL
  -- the key bound `α (b - a) ≤ π / C²`
  have hαℓ : α * (b - a) ≤ Real.pi / (C : ℝ) ^ 2 :=
    le_trans (mul_le_mul_of_nonneg_left hℓle hα) hαC
  have hC2 : (0 : ℝ) < (C : ℝ) ^ 2 := by positivity
  have hRr' : 4 * Real.pi / (C : ℝ) ^ 2 ≤ (linePull μ (Ioo ((a + b) / 2) b)).toReal := by
    rw [div_le_iff₀ hC2]; nlinarith
  have hLr' : 4 * Real.pi / (C : ℝ) ^ 2 ≤ (linePull μ (Ioo a ((a + b) / 2))).toReal := by
    rw [div_le_iff₀ hC2]; nlinarith
  have hπC : Real.pi / (C : ℝ) ^ 2 * (C : ℝ) ^ 2 = Real.pi := div_mul_cancel₀ _ hC2.ne'
  have hc : 1 / (4 * (C : ℝ) ^ 2) * (b - a) * (4 * Real.pi) = (b - a) * (Real.pi / (C : ℝ) ^ 2) := by
    field_simp
  have hMa : M * a = 4 * Real.pi * a + 2 * α * (b - a) * a := by rw [hM]; ring
  have hMb : M * b = 4 * Real.pi * b + 2 * α * (b - a) * b := by rw [hM]; ring
  have hsq : 2 * α * ((b ^ 2 - a ^ 2) / 2) = 2 * α * (b - a) * a + α * (b - a) * (b - a) := by
    ring
  have hsq' : 2 * α * ((b ^ 2 - a ^ 2) / 2) = 2 * α * (b - a) * b - α * (b - a) * (b - a) := by
    ring
  have hba : 0 ≤ b - a := by linarith
  have p1 := mul_le_mul_of_nonneg_left hRr' (by linarith : (0:ℝ) ≤ (b - a) / 2)
  have p2 := mul_le_mul_of_nonneg_left hLr' (by linarith : (0:ℝ) ≤ (b - a) / 2)
  have p3 := mul_le_mul_of_nonneg_left hαℓ hba
  rw [hlam]
  set P := Real.pi / (C : ℝ) ^ 2
  set I := ∫ t in Ioc a b, t ∂linePull μ
  set mR := (linePull μ (Ioo ((a + b) / 2) b)).toReal
  set mL := (linePull μ (Ioo a ((a + b) / 2))).toReal
  have e4 : 4 * Real.pi / (C : ℝ) ^ 2 = 4 * P := by simp only [P]; ring
  rw [e4] at p1 p2
  have e5 : (a + 1 / (4 * (C : ℝ) ^ 2) * (b - a)) * (4 * Real.pi) = 4 * Real.pi * a + (b - a) * P := by
    rw [add_mul, hc]; ring
  have e6 : (b - 1 / (4 * (C : ℝ) ^ 2) * (b - a)) * (4 * Real.pi) = 4 * Real.pi * b - (b - a) * P := by
    rw [sub_mul, hc]; ring
  clear_value P I mR mL M a b
  constructor
  · rw [le_div_iff₀ (by positivity), e5]
    nlinarith
  · rw [div_le_iff₀ (by positivity), e6]
    nlinarith

end LineHyp

/-- The constants of the construction (§2 of the blueprint), bundled. -/
structure LineConsts (μ : Measure ℂ) (r C₂ c₀ α₁ : ℝ) : Prop where
  hμ : IsLineMeasure μ
  hr : 0 < r
  hmr : ∀ x : ℝ, 1 < μ (lineInterval x r)
  hC₂ : 1 ≤ C₂
  hc₀ : 0 < c₀
  hc₀' : c₀ ≤ 1 / 4
  hα₁ : 0 < α₁
  hα₁r : α₁ * r ≤ 1 / 8
  centre : ∀ α : ℝ, 0 ≤ α → α ≤ α₁ → ∀ k : ℤ,
    lineKnot μ α k + c₀ * lineLength μ α k ≤ lineCentre μ α k ∧
      lineCentre μ α k ≤ lineKnot μ α (k + 1) - c₀ * lineLength μ α k
  rho : ∀ α : ℝ, 0 ≤ α → α ≤ α₁ → ∀ k : ℤ, ∀ t ∈ Icc (lineKnot μ α k) (lineKnot μ α (k + 1)),
    massRadiusLine μ t ≤ lineLength μ α k ∧ lineLength μ α k ≤ C₂ * massRadiusLine μ t

theorem LineConsts.hyp {μ : Measure ℂ} {r C₂ c₀ α₁ α : ℝ} (hc : LineConsts μ r C₂ c₀ α₁)
    (hα : 0 ≤ α) (hα' : α ≤ α₁) : LineHyp μ r α :=
  ⟨hc.hμ, hc.hr, hc.hmr, hα, le_trans (mul_le_mul_of_nonneg_right hα' hc.hr.le) hc.hα₁r⟩

theorem IsLineMeasure.exists_lineConsts {μ : Measure ℂ} (hμ : IsLineMeasure μ) :
    ∃ r C₂ c₀ α₁ : ℝ, LineConsts μ r C₂ c₀ α₁ := by
  obtain ⟨r, hr, hmr⟩ := hμ.mass
  obtain ⟨C₂, hC₂, hL7⟩ := hμ.length_comparable (m₁ := 4 * Real.pi) (m₂ := 4 * Real.pi + 13)
    (by nlinarith [Real.pi_gt_three])
  obtain ⟨C, hC1, hC⟩ := hμ.doubling_le (A := 26 * r) (by positivity)
  have hC0 : (0 : ℝ) < (C : ℝ) := by exact_mod_cast (zero_lt_one.trans_le hC1)
  have hC1' : (1 : ℝ) ≤ (C : ℝ) := by exact_mod_cast hC1
  refine ⟨r, C₂, 1 / (4 * (C : ℝ) ^ 2), min (1 / (8 * r)) (Real.pi / (52 * r * (C : ℝ) ^ 2)),
    ⟨hμ, hr, hmr, hC₂, by positivity, ?_, by positivity, ?_, ?_, ?_⟩⟩
  · rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  · calc min (1 / (8 * r)) (Real.pi / (52 * r * (C : ℝ) ^ 2)) * r ≤ 1 / (8 * r) * r :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) hr.le
      _ = 1 / 8 := by field_simp
  · intro α hα hα' k
    have hl : LineHyp μ r α := ⟨hμ, hr, hmr, hα, le_trans
      (mul_le_mul_of_nonneg_right (hα'.trans (min_le_left _ _)) hr.le) (by field_simp; norm_num)⟩
    refine hl.centre_mem hC1 hC ?_ k
    calc α * (52 * r) ≤ Real.pi / (52 * r * (C : ℝ) ^ 2) * (52 * r) :=
          mul_le_mul_of_nonneg_right (hα'.trans (min_le_right _ _)) (by positivity)
      _ = Real.pi / (C : ℝ) ^ 2 := by field_simp
  · intro α hα hα' k
    have hl : LineHyp μ r α := ⟨hμ, hr, hmr, hα, le_trans
      (mul_le_mul_of_nonneg_right (hα'.trans (min_le_left _ _)) hr.le) (by field_simp; norm_num)⟩
    exact hl.cell_rho hL7 k

theorem lineNode_eq (μ : Measure ℂ) (α s : ℝ) (k : ℤ) (b : Bool) :
    ∃ o : ℝ, (o = s ∨ o = -s) ∧ lineNode μ α s k b = lineCentre μ α k + o * lineLength μ α k :=
  ⟨if b then s else -s, by cases b <;> simp, rfl⟩

theorem lineNode_zero (μ : Measure ℂ) (α : ℝ) (k : ℤ) (b : Bool) :
    lineNode μ α 0 k b = lineCentre μ α k := by
  cases b <;> simp [lineNode]

namespace LineConsts

variable {μ : Measure ℂ} {r C₂ c₀ α₁ : ℝ} (hc : LineConsts μ r C₂ c₀ α₁)
include hc

/-- Points `λ_k + o a_k` with `|o| ≤ c₀/2` are well inside the cell. -/
theorem offset_mem {α : ℝ} (hα : 0 ≤ α) (hα' : α ≤ α₁) (k : ℤ) {o : ℝ} (ho : |o| ≤ c₀ / 2) :
    lineKnot μ α k + c₀ / 2 * lineLength μ α k ≤ lineCentre μ α k + o * lineLength μ α k ∧
      lineCentre μ α k + o * lineLength μ α k ≤
        lineKnot μ α (k + 1) - c₀ / 2 * lineLength μ α k := by
  have hpos := (hc.hyp hα hα').lineLength_pos k
  have h1 := hc.centre α hα hα' k
  have := abs_le.1 ho
  constructor <;> nlinarith

theorem separated_aux {α s : ℝ} (hα : 0 ≤ α) (hα' : α ≤ α₁) (hs : 0 < s) (hs' : s ≤ c₀ / 2)
    {k k' : ℤ} (hkk : k < k') {o o' : ℝ} (ho : |o| ≤ s) (ho' : |o'| ≤ s) :
    s / 2 * (massRadiusLine μ (lineCentre μ α k + o * lineLength μ α k) +
        massRadiusLine μ (lineCentre μ α k' + o' * lineLength μ α k')) ≤
      |(lineCentre μ α k + o * lineLength μ α k) -
        (lineCentre μ α k' + o' * lineLength μ α k')| := by
  have hl := hc.hyp hα hα'
  obtain ⟨h1, h2⟩ := hc.offset_mem hα hα' k (ho.trans hs')
  obtain ⟨h3, h4⟩ := hc.offset_mem hα hα' k' (ho'.trans hs')
  have hp := hl.lineLength_pos k
  have hp' := hl.lineLength_pos k'
  have hc0 := hc.hc₀
  have hk0 : 0 ≤ c₀ / 2 * lineLength μ α k := by positivity
  have hk0' : 0 ≤ c₀ / 2 * lineLength μ α k' := by positivity
  have r1 := (hc.rho α hα hα' k (lineCentre μ α k + o * lineLength μ α k)
    ⟨by linarith, by linarith⟩).1
  have r2 := (hc.rho α hα hα' k' (lineCentre μ α k' + o' * lineLength μ α k')
    ⟨by linarith, by linarith⟩).1
  have hmono : lineKnot μ α (k + 1) ≤ lineKnot μ α k' :=
    hl.lineKnot_strictMono.monotone (by omega)
  rw [abs_sub_comm, abs_of_nonneg (by linarith)]
  have m1 := mul_le_mul_of_nonneg_right hs' hp.le
  have m2 := mul_le_mul_of_nonneg_right hs' hp'.le
  have m3 := mul_le_mul_of_nonneg_left r1 (by positivity : (0:ℝ) ≤ s / 2)
  have m4 := mul_le_mul_of_nonneg_left r2 (by positivity : (0:ℝ) ≤ s / 2)
  linarith

end LineConsts

theorem IsLineMeasure.lineCentre_mem {μ : Measure ℂ} (hμ : IsLineMeasure μ) :
    ∃ α₁ c₀ : ℝ, 0 < α₁ ∧ 0 < c₀ ∧ c₀ ≤ 1 / 4 ∧ ∀ α : ℝ, 0 ≤ α → α ≤ α₁ → ∀ k : ℤ,
      lineKnot μ α k + c₀ * lineLength μ α k ≤ lineCentre μ α k ∧
      lineCentre μ α k ≤ lineKnot μ α (k + 1) - c₀ * lineLength μ α k := by
  obtain ⟨r, C₂, c₀, α₁, hc⟩ := hμ.exists_lineConsts
  exact ⟨α₁, c₀, hc.hα₁, hc.hc₀, hc.hc₀', hc.centre⟩

theorem LineConsts.node_rep {μ : Measure ℂ} {α s : ℝ} {ν : ℝ}
    (hν : ν ∈ range (fun p : ℤ × Bool ↦ lineNode μ α 0 p.1 p.2) ∪
          range (fun p : ℤ × Bool ↦ lineNode μ α s p.1 p.2)) :
    ∃ (k : ℤ) (o : ℝ), (o = 0 ∨ o = s ∨ o = -s) ∧ ν = lineCentre μ α k + o * lineLength μ α k := by
  rcases hν with ⟨⟨k, b⟩, rfl⟩ | ⟨⟨k, b⟩, rfl⟩
  · exact ⟨k, 0, Or.inl rfl, by simp [lineNode_zero]⟩
  · obtain ⟨o, ho, he⟩ := lineNode_eq μ α s k b
    exact ⟨k, o, Or.inr ho, he⟩

theorem IsLineMeasure.lineNode_separated {μ : Measure ℂ} (hμ : IsLineMeasure μ) :
    ∃ α₁ s₁ : ℝ, 0 < α₁ ∧ 0 < s₁ ∧ s₁ ≤ 1 / 8 ∧ ∀ α : ℝ, 0 ≤ α → α ≤ α₁ →
      ∀ s : ℝ, 0 < s → s ≤ s₁ →
      ∀ ν ∈ range (fun p : ℤ × Bool ↦ lineNode μ α 0 p.1 p.2) ∪
          range (fun p : ℤ × Bool ↦ lineNode μ α s p.1 p.2),
      ∀ ν' ∈ range (fun p : ℤ × Bool ↦ lineNode μ α 0 p.1 p.2) ∪
          range (fun p : ℤ × Bool ↦ lineNode μ α s p.1 p.2),
      ν ≠ ν' → s / 2 * (massRadiusLine μ ν + massRadiusLine μ ν') ≤ |ν - ν'| := by
  obtain ⟨r, C₂, c₀, α₁, hc⟩ := hμ.exists_lineConsts
  refine ⟨α₁, c₀ / 2, hc.hα₁, by linarith [hc.hc₀], by linarith [hc.hc₀'],
    fun α hα hα' s hs hs' ν hν ν' hν' hne ↦ ?_⟩
  obtain ⟨k, o, ho3, rfl⟩ := LineConsts.node_rep hν
  obtain ⟨k', o', ho3', rfl⟩ := LineConsts.node_rep hν'
  have habs : ∀ {o : ℝ}, (o = 0 ∨ o = s ∨ o = -s) → |o| ≤ s := by
    intro o ho
    rcases ho with rfl | rfl | rfl
    · simp [hs.le]
    · rw [abs_of_pos hs]
    · rw [abs_neg, abs_of_pos hs]
  rcases lt_trichotomy k k' with hkk | rfl | hkk
  · exact hc.separated_aux hα hα' hs hs' hkk (habs ho3) (habs ho3')
  · have hl := hc.hyp hα hα'
    have hp := hl.lineLength_pos k
    have hoo : s ≤ |o - o'| := by
      rcases ho3 with rfl | rfl | rfl <;> rcases ho3' with rfl | rfl | rfl <;>
        first
        | exact absurd rfl hne
        | (rw [abs_of_nonneg (by linarith)]; linarith)
        | (rw [abs_of_nonpos (by linarith)]; linarith)
    obtain ⟨h1, h2⟩ := hc.offset_mem hα hα' k ((habs ho3).trans hs')
    obtain ⟨h3, h4⟩ := hc.offset_mem hα hα' k ((habs ho3').trans hs')
    have hc0 := hc.hc₀
    have hk0 : 0 ≤ c₀ / 2 * lineLength μ α k := by positivity
    have r1 := (hc.rho α hα hα' k (lineCentre μ α k + o * lineLength μ α k)
      ⟨by linarith, by linarith⟩).1
    have r2 := (hc.rho α hα hα' k (lineCentre μ α k + o' * lineLength μ α k)
      ⟨by linarith, by linarith⟩).1
    have e : (lineCentre μ α k + o * lineLength μ α k) - (lineCentre μ α k + o' * lineLength μ α k)
        = (o - o') * lineLength μ α k := by ring
    rw [e, abs_mul, abs_of_pos hp]
    have m1 := mul_le_mul_of_nonneg_right hoo hp.le
    have m3 := mul_le_mul_of_nonneg_left r1 (by positivity : (0:ℝ) ≤ s / 2)
    have m4 := mul_le_mul_of_nonneg_left r2 (by positivity : (0:ℝ) ≤ s / 2)
    linarith
  · rw [add_comm, abs_sub_comm]
    exact hc.separated_aux hα hα' hs hs' hkk (habs ho3') (habs ho3)

end OC
