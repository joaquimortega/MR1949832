# Corrected version of *Multipliers and weighted ∂̄-estimates* (RMI 18 (2002), 355–377)

This folder contains a corrected version of the paper. It makes the smallest changes that fix the problems recorded in `../NOTEBOOK.md`.

## Files

| File | Content |
|---|---|
| `original_dbar2.tex` | The author's LaTeX source (the accepted version, which agrees with the printed paper), unmodified. |
| `dbar_fixed.tex` | The corrected source. |
| `dbar_fixed.pdf` | The corrected paper (19 pages). |
| `CHANGES.md` | This file. |

These four files are in the repository. `dbar_diff.pdf` (`latexdiff original_dbar2.tex dbar_fixed.tex`, additions in blue, deletions in red) is kept locally only. To regenerate it, run the command below.

Build: `latexmk -pdf dbar_fixed.tex`. The repository's `.gitignore` excludes `*.pdf`, so `dbar_fixed.pdf` was added explicitly.

For the diff, one deleted display in Lemma 6 had to be patched by hand in the generated `dbar_diff.tex`: latexdiff splits a `\left\{…\right\}` pair across groups. The command was:
```
latexdiff --preamble=<colour preamble> --math-markup=whole original_dbar2.tex dbar_fixed.tex
```

## Base text

`dbar2.tex` is the revised version accepted by the journal. Its abstract, statements and proofs agree with the printed paper. The printed version differs from it only in the following points:
- **Journal typesetting errors, absent from the source.**
  - p. 366: "the statement of Theorem 3" should be Theorem 4. The source has `\ref{multiplicador}`, which gives 4.
  - "Added in proof": the multiplier is "(Theorem 3)" in print and Theorem 4 in the source.
  - p. 365: "as in 4" should be "as in Lemma 4".
  
  These need no correction here; the first one is the "wrong theorem number" part of N-15.
- **Bibliography.** The journal gives publication data for [BC99] and [LM99]; the source still lists them as preprints. The bibliography is left as in the source.
- **Grant line.** The journal's grant line differs slightly from the source's.

Theorem, lemma and proposition numbers are unchanged: Theorems 1–5, Lemmas 1–8, Propositions 1–2, Claims 1–2.

## Global convention

`Δ` is the standard Laplacian (`Δ log|z| = 2πδ₀`). This is stated in the Remark after Hörmander's theorem. The paper used it in §3 and §4.1, but used `∂∂̄` in §4.2 and in the Remark after Theorem 2 (N-15). The constants in §4.2 and in that Remark are adjusted accordingly.

## Changes, by NOTEBOOK entry

Line numbers refer to `original_dbar2.tex`.

### Errata (false as printed)

| Entry | Where | Change |
|---|---|---|
| **N-01** | Theorem 3, l. 202 | The integral becomes `∫_{|z−x|<1} e^{−φ(z)} d|μ|(z)/|x−z|`. A new Remark after Theorem 3 says that the weight can be dropped when `φ` is bounded below on `|Im z| < 1`, and not in general (invariance under `φ ↦ φ + Re H`, `μ ↦ e^H μ`, `u ↦ u e^H`; the weight `|Im z| + Re z·Im z`). The proof is in §4.3, see N-18. |
| **N-02** | Theorem 4, l. 633–634; proof of Theorem 2, l. 1191–1192 | Inequalities swapped: `(d/ρ)^M ≲ |h|e^{−ψ} ≲ d/ρ`. |
| **N-03** | Proposition 1, l. 228; proof of Theorem 1, l. 1278 | `≃` → `≲`. Added one sentence after Proposition 1: the kernel vanishes at the zeros of the multipliers. |
| **N-04** | Theorem 2, l. 147–149 | The weight `e^{−φ}` becomes `e^{−pφ}` on both sides, so one solution `u` works for all `p ∈ [1,∞)` and for the sup bound. This is the form the proof gives. The Remark after Theorem 2 now derives the printed form (weight `e^{−φ}`, with `u = u_p` depending on `p`) by applying the theorem to `φ/p`. The Remark's threshold `−1+ε` becomes `−4+ε` (standard Laplacian, weight `pφ + log(1−|z|²)`). |
| **N-04** | Lemma 7, l. 1167–1168 | The exponent `α−1` becomes `pα−1` (Schur-test form, valid for all `p` at once with fixed `α`). The proof notes that the printed form follows by replacing `α` by `α/p`. |
| **N-13** | Lemma 5, l. 832–870 | Restated for a measure supported in a closed disk `D`, with any `k ≥ m`. The nodes `Λ` lie in `2mD`, not "inside `R`", and `κ` lies in `(C+4m)D ∖ CD`. The Chebyshev-quadrature citation is replaced by an explicit construction: `m` roots of a polynomial obtained from Newton's identities, each repeated `k` times. `κ` uses `k`-th roots of unity. A one-line counterexample to "inside `R`" is included. |
| **N-15** | Construction, l. 822–829, 872–902, 904–967 | Cells have mass `N` for `Δψ/2π`, and the point masses carry `2π`. The middle terms of (2) and (3) get the factor `−1/2π`; the left-hand sides read `M log(d/ρ) − C`; (3) gets `+C` on the right. The near-field display (l. 960–963) is corrected: sign, `2π`, and an explanation of where `(d/ρ)^M` and `d/ρ` come from. |
| **N-19, N-20** | Lemma 6, l. 1108–1143 | The global potentials `K[μ₁]`, `K[μ̃₁]` are removed, including the plane kernel with the sign error, the disc kernel and the growth bound `(1−r)^{−2}`. They are replaced by a local potential `V(z) = ∫ G(z,ζ) dμ₁(ζ)`, where `G(z,ζ) = (1/2π)(∫ log[z,w] dσ_ζ(w) − log[z,ζ])` and `[z,w]` is `|z−w|`, resp. the pseudo-hyperbolic distance. `G(·,ζ)` vanishes off `D(ζ,2R)` (mean value property), `ΔV = μ̃₁ − μ₁`, and `|V| ≲ ∫_{D(z,2R)} (1 + log(2R/d)) dμ₁`. The paper's conclusion, via [Chr91, Lemma 2.3], is unchanged. [And85] and [Pas88] are no longer cited in the text but are kept in the bibliography. |
| **N-22** | Proof of Theorem 2, l. 1181–1251 | `ψ = φ + (ε/8) log(1−|z|²)`, after Lemma 6 and `ε ≤ 1`; `α = ε/8` in Lemma 7. The `L^p` chain uses `e^{−pφ}` and `(1−|z|)^{pε/8}`. The kernel bound becomes `|κ| ≲ … ((1−|z|)/(1−|ζ|))^{ε/8} e^{φ(z)−φ(ζ)}`, followed by "Schur's test, for all `p ∈ [1,∞]`, same `u`". Also added: `|h_i| ≲ e^ψ` everywhere (Remark after Theorem 4). Lemma 6 is now cited (it has a label). |
| **N-23** | Proof of Theorem 1, l. 1268–1281 | `ψ = φ − (ε/8)|z|²` (standard Laplacian, after Lemma 6), kernel `e^{(ε/4)(ζ̄z−|ζ|²)}` (Lemma 8 with `α = ε/8`), bound `≲ e^{φ(z)−φ(ζ)} e^{−(ε/8)|z−ζ|²}/|z−ζ|`. In the paper's `∂∂̄` normalisation this is the NOTEBOOK's `e^{ε(…)}` instead of `e^{2ε(…)}`. |

### Gaps

| Entry | Where | Change |
|---|---|---|
| **N-07** | Quotation of [OCS99], l. 1313–1324 | Added a sentence: [OCS99, Lemma 4] states `limsup < ∞`; the solution constructed there gives `= 0`, which is what is used. "C depends on α and the Carleson constant". |
| **N-09** | Lemma 2, l. 303–319 | The statement covers segments and circular arcs (arcs via polar coordinates). The proof explains why the projected measure `ν` is doubling for small intervals (covering by balls on the middle line). |
| **N-10** | §2, commented-out Remark, l. 264–268 | The Remark is restored, with the chaining proof that local doubling holds at every bounded scale. It says that Lemmas 1 and 3 hold with `1` replaced by any constant `A`. The proof of Theorem 4 cites it where Lemma 3 is used up to `2 sup ρ`. Lemma 3's final exponent `(mγ−1)/γ` becomes `γ(mγ−1)` (l. 570). |
| **N-12** | Lemma 4, Remark and proof, l. 669–800 | The coarse strips have width `2R` (a `2R×2R` square contains a disk of radius `R`). In the disc, polar rectangles are replaced by Cayley preimages of axis-parallel rectangles (horocyclic boxes), using strips `Λ^j ≤ Im w < Λ^{j+1}`; the central region is then automatic. The bisection threshold is a constant `C` depending on the doubling constant, via `R ⊂ 3R'` (was "`R ⊂ 2R'` … the doubling constant"). Added that both halves have positive mass. The final slicing is justified by reverse doubling for slabs (was "we use Lemma 1"). |
| **N-14** | Proof of Theorem 4, disc, before l. 969 | New paragraph with two regimes. Cells with `ρ ≤ ρ₀` use Lemma 5 nodes, which then lie in `𝔻`. Larger cells use `N` copies of the barycenter (`κ`: `b ± v`, `N/2` copies each, `k` even), matching only moments 0 and 1, which suffices at hyperbolic distance `≥ δ₀`. The split `Ω₁`/`Ω₂` is at `δ₀` instead of `1` (l. 995–1002). |
| **N-13 (consequence)** | Proof of Theorem 4, l. 915–916; Proposition 2, l. 1037–1051 | Since nodes lie near `R_i` but not inside it, "immediate neighbors" is replaced by *neighbors*, defined by `d(R_i,R_j) < K max(diam R_i, diam R_j)` with `K ≥ 2m+2`. The Taylor point `w` lies on the segment `[λ₀, ζ]`. |
| **N-16** | Proof of Theorem 5, l. 1303–1307 | The barycenter route. Intervals of `Δφ`-mass `4π`, a double zero at each barycenter (real, well inside the interval), a second-order Taylor bound, and the sum controlled by Lemma 1. Lemma 5 is not used, so the zeros are real. |
| **N-18** | §4.3, last paragraph, l. 1326–1327 | The one-line proof of Theorem 3 is replaced by a sketch. Multipliers for `φ − α|Im z|` come from the signed measure `Δφ − 2α dx`, `α ≤ α₀`, by the proof of Theorem 5. A second multiplier comes from the zeros `λ_k ± s|I_k|`. Then solve `∂̄v_i = χ_{Ω_i}μ/f_i` with [OCS99] and set `u = f₁v₁ + f₂v₂`. The sketch shows where the factor `e^{−φ(z)}` of N-01 comes from. |
| **N-21** | Lemma 6 statement, l. 1081; proof, l. 1087 | The disc form `(1−|z|²)²Δψ > ε` is added to the statement. The disc "dyadic squares" are specified as the pieces of a Lemma 4 partition for hyperbolic area. |

### Typos

| Entry | Where | Change |
|---|---|---|
| **N-08** | Proof of Lemma 1, l. 295–297 | Attributions swapped: the right inequality is [Chr91, Lemma 2.1], the left one follows from the definition. |
| **N-15** | p. 366, theorem number | Already correct in the source (journal typesetting error, see above). |

### Not changed

- **N-05, N-06** (formalization divergences): no change to the paper is needed.
- **N-11** (moment order 3 suffices): a simplification. The paper's `m` with `mγ > 1` is kept; it is only weakened where a fix needs it (order 2 for large disc cells; order 2 on the line, N-16).
- **N-17** (greedy colouring instead of Besicovitch): a simplification, not applied.
- **N-24**: a clarification. The proof of Lemma 7 now says "Hölder's inequality, in the form of Schur's test", because of the N-04 change.
- **The Remark after Theorem 4** ("`M` can be chosen to be 1" with separated zeros) is not proved by the construction, but it is stated as an aside that is not used. It is kept.
- **W-01**: withdrawn, nothing to do.

### Other small edits made in passing

- "in the case of `Ω = D` In both cases" → "`Ω = D`. In both cases" (missing period).
- In the proof of Lemma 6, "`μ₂` is `μ − μ₁`" → "`Δφ − μ₁`".
- In the proof of Theorem 4, "Call `M = 2 sup ρ`" is renamed `M'`: `M` is the exponent of Theorem 4, now used explicitly nearby.
- In Proposition 2, `λ(R)` → `Λ(R)`, as in Lemma 5.
- In the construction of the zeros (Theorem 4), "which we may take `≥ 3`" is added for `m`. The far-field step for `|z−ζ| ≥ M'` bounds `(ρ/|z−ζ|)^m` by `sup ρ · ρ²/|z−ζ|³`, which needs `m ≥ 3`. Lemma 3 allows any larger `m`. This is not a NOTEBOOK entry; it was noticed while making the other corrections.
- Title footnote and date: "corrected version, November 2, 2026", with a pointer to this file and to the formalization repository.

## Status

The original source, the corrected source, the PDF and this file are in the repository. Only the diff PDF is kept locally.
