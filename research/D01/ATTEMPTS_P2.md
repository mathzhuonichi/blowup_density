# D01 obligation P2 — attempts and scope (lane 062, split-and-start)

Target of this lane: (1) the split `research/D01/P2_SPLIT.md` (≤ 8 sub-lemmas, S/M/L +
blockers), and (2) prove the S-level piece — the Leray complement fiber-symbol algebra.
New module: `formalization/NSFormalization/Section4/D01/LeraySymbol.lean`.
Conformance: `research/D01/axioms_p2.lean`.  No `sorry`, no `axiom`.
This lane does **not** attempt the M/L pieces (per task: stop at S).

## Result — what closed (S)

`LeraySymbol.lean` (namespace `NSFormalization.Section4.D01.Leray`), all
`[propext, Classical.choice, Quot.sound]`:

- `complementSymbol ξ := (ℝ ∙ ξ).starProjection : Space →L[ℝ] Space` — the `(I−P)`
  Fourier fiber multiplier, orthogonal projection onto the longitudinal line `ℝ ∙ ξ`.
- `complementSymbol_apply`: `= (⟨ξ,v⟩/‖ξ‖²) • ξ`, i.e. the matrix `ξξᵀ/‖ξ‖²`.
  (`Submodule.starProjection_singleton`.)
- `complementSymbol_idempotent`: **projection** (via `_apply_mem` + `_fixed_of_mem`,
  mirroring HeliCorgi's `r3LeraySymbol_idempotent`).
- `complementSymbol_opNorm_le_one` and `norm_complementSymbol_le`: **operator norm ≤ 1**
  (`Submodule.starProjection_norm_le`, `Submodule.norm_starProjection_apply_le`).
- `complementSymbol_neg`: **even** in ξ (`complementSymbol (-ξ) = complementSymbol ξ`),
  via the explicit formula + `inner_neg_left`, `norm_neg`.
- `leraySymbol_add_complementSymbol`, `leraySymbol_eq_sub`, `complementSymbol_eq_sub`:
  complementarity `P(ξ) + (I−P)(ξ) = I` with **reused** HeliCorgi `MNS2.r3LeraySymbol`
  (via `MNS2.r3LeraySymbol_apply`).
- `complementSymbol_apply_mem`, `complementSymbol_fixed_of_mem`, `complementSymbol_self`.

These are exactly the four facts P2_SPLIT sub-lemma **d1** asks for (projection, opNorm ≤ 1,
real = `→L[ℝ]`, even), plus the bridge to the reused HeliCorgi solenoidal symbol.

## Reuse decisions (positive examples)

- The complement symbol is defined the same way HeliCorgi defines the *solenoidal* symbol
  (`R3LerayFrequencySymbol.lean`: `r3LeraySymbol ξ := ((ℝ∙ξ)ᗮ).starProjection`), just onto
  `ℝ∙ξ` instead of its orthocomplement.  All proofs reuse the same `Submodule.starProjection_*`
  Mathlib lemmas that file uses.  `Formal.R3LerayFrequencySymbol` was confirmed to build under
  this repo's pin (Lean 4.34.0-rc2) — `lake build Formal.R3LerayFrequencySymbol` → success.
- The complementarity theorems `rw [MNS2.r3LeraySymbol_apply, complementSymbol_apply]; abel`
  reuse HeliCorgi's proved explicit formula directly, giving a concrete P/Q bridge to the
  ported declaration (the point of P2 — bridging HeliCorgi to our vocabulary).
- `Space = EuclideanSpace ℝ (Fin 3)` is definitionally HeliCorgi's `MNS2.R3`, so
  `MNS2.r3LeraySymbol ξ` typechecks with `ξ : Space` with no transport.

## Failed / rejected approaches

- **Full multiplier CLM on `RealVectorSobolev` as an S piece (SL3):** rejected.  A Paper3/Section4
  survey (subagent, very thorough) found **no operator-valued / coordinate-mixing Fourier
  multiplier** in tree.  Every existing symbol multiplier is scalar (`(ContinuousLinearMap.mul
  ℂ ℂ).holderL`, e.g. `sobolevOrderLowering`) or **diagonal** per-coordinate
  (`ContinuousLinearMap.pi` of one scalar map, `HalfOrder.lowerVectorL`; `cyclesToAngularRealVector`).
  The Leray symbol `ξξᵀ/‖ξ‖²` mixes coordinates, so it does not fit `ContinuousLinearMap.pi`
  as-is.  Building it (9 scalar `holderL` multipliers with symbols `ξᵢξⱼ/‖ξ‖²` + assembly +
  reality projection + `IsSobolevDatum` identification) is genuinely new infrastructure — marked
  **M**, not S, in P2_SPLIT.  Not attempted in code (out of scope for split-and-start).
- **Route A (HeliCorgi complex `L²` operator) as the main route:** rejected as primary.
  `MNS2.r3LerayComplementL2` / `r3HelmholtzPressure_gradient` are order-0, complex, cycles
  convention, distributional (𝓢').  Reaching the classical pointwise `pressureGradient` on real
  `Space → Space` at every order needs a cycles↔angular + complex↔real + 𝓢'↔classical + L²→Hᵐ
  stack (ATTEMPTS_L9C's four bridges).  Route B (native angular multiplier on `RealVectorSobolev`)
  avoids the convention/real transports at the operator level, so it is primary; Route A is kept
  only as the order-0 cross-check for SL7/(e).  No existing identification wires HeliCorgi's
  operator to `RealVectorSobolev` (checked `HeliCorgiPort.lean` and Paper3 — none).
- **`simpa [complementSymbol] using Submodule.starProjection_apply_mem …`** for
  `complementSymbol_apply_mem` — triggered the `unnecessarySimpa` linter.  Replaced with
  `simp only [complementSymbol]; exact …` (clean build, no warnings on the module).

## Blockers carried forward (for the next P2 lane)

- **SL3 (crux, M):** the operator-valued Leray multiplier CLM on `RealVectorSobolev m`.
  Ingredients present: scalar `holderL` template (`SobolevOrderLowering.lean:26`), the pointwise
  bound `|ξᵢξⱼ| ≤ ‖ξ‖²`, `ContinuousLinearMap.pi` assembly (`HalfOrder.lean:103`), `realProjectionTo`.
- **SL4β = D01 unit L3 (L, booked/open):** pointwise-solenoidal `L²` field ↦ closed solenoidal
  subspace, so `P` fixes / `(I−P)` kills it.
- **SL4α (S/M, unproved in tree):** `div ∂ₜu = ∂ₜ div u = 0` for the smooth solution.
- **SL5 (M):** Fourier image of a gradient is longitudinal (angular convention).
- **SL2, SL6, SL7, SL8 (M):** assembly on top of SL3–SL5.

## Commands (from `WT/verification`, `. ../scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`)

- `lake build Formal.R3LerayFrequencySymbol` → `Build completed successfully (8763 jobs)`
  (one upstream `simpa` linter note; reuse anchor confirmed compiling at this pin).
- `lake build NSFormalization.Section4.D01.LeraySymbol` → `Build completed successfully (8816 jobs)`,
  `Built NSFormalization.Section4.D01.LeraySymbol (2.6s)`, no warnings on the module.
- `lake env lean ../research/D01/axioms_p2.lean` → all 11 declarations report
  `[propext, Classical.choice, Quot.sound]`.

## Review fixes (applied after `research/D01/REVIEW_P2.md`, ACCEPT-WITH-NOTES)

The reviewer confirmed the Lean is accept-grade (clean build, no module diagnostics, all
standard-axiom, every symbol lemma independently re-checked at `ξ=0`, `e₁`, `e₂`). The split
document had three wrong headline conclusions; findings 1–4 fixed in `P2_SPLIT.md`.

**Lean added to `LeraySymbol.lean`** (finding-2/5/6 fibre facts + homogeneity; all standard-axiom):
1. `complementSymbol_eq_zero_of_inner_eq_zero` — `(I−P)` kills transverse (solenoidal) vectors:
   `⟨ξ,v⟩ = 0 → complementSymbol ξ v = 0` (`rw [complementSymbol_apply, h, zero_div, zero_smul]`).
2. `complementSymbol_smul_self` — `(I−P)` fixes longitudinal (gradient) vectors:
   `complementSymbol ξ (c • ξ) = c • ξ` (via `complementSymbol_fixed_of_mem` + `Submodule.smul_mem`).
3. `complementSymbol_smul` — **0-homogeneity** `complementSymbol (c•ξ) = complementSymbol ξ` for
   `c ≠ 0`; `complementSymbol_neg` is now the `c=−1` case.  Documented the `ξ=0` convention in the
   module docstring (`ℝ∙0 = ⊥`, symbol = 0, `{0}` null so `Lᵖ`-irrelevant).

These are the pointwise-fibre content the reviewer compiled: they let route B bypass unit L3
(finding 2) — "`(I−P)` kills a solenoidal field" is fact 1 composed with SL3's a.e. action.

**Split rewrites (`P2_SPLIT.md`):**
- **F1 — SL3 regraded M → S/M.**  Dropped the "missing infrastructure" and nine-scalar-entry
  claims.  Named the two ready templates: HeliCorgi's `R3LerayPointwiseL2.lean` (operator-valued
  `L²` multiplier from this symbol, `MemLp.of_le` for norm ≤ 1) and Mathlib `holderL` with
  `B = ContinuousLinearMap.id ℝ (R3C →L[ℝ] R3C)` (`holderL` is not scalar-only; `norm_holderL_le`
  + `norm_id_le` give `opNorm ≤ 1` in one step).  Recorded the real (small) work item: the
  `q = 2` `FiniteHilbertBochner.assemble/coordinates` isometry, and that the ℂ fibre algebra
  `r3LeraySymbolComplex` is already upstream.  Noted the nine-entry route cannot reach `≤ 1`
  (triangle ⇒ `≤ 3`; the constant is a pointwise-matrix fact) and that `≤ C` suffices downstream.
- **F2 — SL4β (= unit L3) deleted from the critical path.**  Route B defines `P` by symbol, so
  kill-solenoidal is the fibre fact (added).  SL5 restated via **curl-freeness (Clairaut)**, not a
  datum for `p` (`ClassicalSolutionR` gives `p` no decay).  The separate L/M blockers collapse to
  one **M** lemma SL6: `IsSobolevDatum m (∂ⱼz) (iξⱼ·A)` (scalar block `SobolevDirectionalDerivative`
  exists).  Recorded that 0-homogeneity makes the cycles↔angular transport free (route A = route B).
- **F3 — SL7 added as the non-circular entry point.**  Order-0 Plancherel seed
  `MemLp z 2 ⟹ ∃ A, IsSobolevDatum 0 z A` (Mathlib `Lp.fourierTransformₗᵢ`; the all-jets
  `exists_isSobolevDatum_of_contDiff_memLp` cannot seed order 0) + `ClassicalSolutionR.pressure_gradient`
  (order-0 datum for `∇p`) + bootstrap to every order (matrix symbol commutes with the scalar order
  weight, shape of `sobolevRealization_orderLowering`).  Stopped demoting Route A to "cross-check".
- **F4 — cost bottom line rewritten.**  No **L** piece gates P2; work items are SL7a (order-0
  Plancherel, S/M), SL6 (`iξⱼ` datum, M), SL3 (S/M, upstream template), SL4α (S/M).
- Citation fixes: angular reading cited to `Data.lean:160`/`angularRealization` (type is
  convention-neutral) not `RealVectorPositiveDensity.lean:15`; `HeliCorgiPort` exposes six examples.

### Failed / rejected during the fixes
- `complementSymbol_smul` closing step `congr 1; field_simp; ring` **failed** (`ring_nf made no
  progress`).  Root cause: `congr 1` cannot reduce `a • ξ = b • ξ` to `a = b` (unsound at `ξ = 0`,
  so it makes no progress and leaves the smul equation, which `field_simp` then does not touch).
  Verified in scratch that `real_inner_smul_left` fires and `field_simp` alone closes the *scalar*
  goal.  Fixed by proving the coefficient equality as a `have hcoeff … := by field_simp` and
  `rw [hcoeff]` (no `congr`, no `ring`).

### Commands after the fixes (from `WT/verification`, `LEAN_NUM_THREADS=6`)
- `lake build NSFormalization.Section4.D01.LeraySymbol` → `Build completed successfully (8816 jobs)`,
  `Built … LeraySymbol (2.8s)`, no warnings on the module.
- `lake env lean ../formalization/NSFormalization/Section4/D01/LeraySymbol.lean` → no output (fresh
  elaboration, zero warnings).
- `lake env lean ../research/D01/axioms_p2.lean` → **14** declarations, all
  `[propext, Classical.choice, Quot.sound]`.
- `make check` → exit 0.
