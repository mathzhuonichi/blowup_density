# U05 — Pinned upstream toolchain compatibility probe (HeliCorgi under Lean 4.34.0-rc2)

Lane 004. Date: 2026-09-13. Author: automated probe (Claude Opus 5).
Status: **evidence complete, no source ported, nothing committed outside `research/U05/`.**

## Question

Does `vendor/HeliCorgi/Formal/` (pinned to `leanprover/lean4:v4.32.1` and Mathlib
`520045ab14e26149ee970e2e617ca04b09bde5d6`) compile unchanged under this repository's pin
(`leanprover/lean4:v4.34.0-rc2`, Mathlib `85e3a25e006c35636f0e53b0e9296caca2685bc0`)?

## Answer in one line

**Almost.** 84 of the 88 modules in the import closure of the four requested targets compile
unchanged; **one** module (`Formal.R3RealLocalMildSolution`) fails with **one** error, and that
single error blocks 3 downstream modules including the target `Formal.R3MildContinuation`.
Three of the four targets — local existence, Helmholtz pressure and the full Navier–Stokes
equation identification — build with no edits at all.

---

## (a) Import closure of the four targets

Targets:

- `Formal.R3EndpointSafeProjectedLocalExistence`
- `Formal.R3MildContinuation`
- `Formal.R3NavierStokesEquation`
- `Formal.R3HelmholtzPressure`

Closure computed by transitively following `import Formal.*` lines:

| quantity | value |
|---|---:|
| modules in the closure (incl. the 4 targets) | **88** |
| `.lean` files in `vendor/HeliCorgi/Formal/` | 128 |
| modules outside the closure | 40 |
| source lines in the closure | 14 223 |
| source lines in all 128 files | 21 524 |
| `sorry` / bespoke `axiom` in the whole of `Formal/` | 0 |

External (non-`Formal`) imports used by the closure — all Mathlib, no third-party package:
`Mathlib` (whole, 13 modules do this), `Mathlib.MeasureTheory.Function.L2Space` (4),
`Mathlib.Analysis.Fourier.LpSpace` (3), `Mathlib.MeasureTheory.Function.Holder` (3),
`Mathlib.Analysis.SpecialFunctions.JapaneseBracket` (3), and 23 further modules used once or
twice (`Analysis.Distribution.Sobolev`, `Analysis.Distribution.SchwartzSpace.{Deriv,Fourier}`,
`Analysis.Fourier.Convolution`, `Topology.MetricSpace.Contracting`, `MeasureTheory.Integral.*`, …).
Nothing outside Mathlib is required, so no extra dependency has to be resolved.

The full closure in topological build order is the table in section (b).

---

## (b) Pass / fail per module, in build order

Legend: `pass` = built clean, `pass (warn)` = built with linter/deprecation warnings,
`replayed`/`cached` = Lake replayed a log or found the module up to date from an earlier
identical run in the same probe (still a successful elaboration under 4.34.0-rc2).

| # | module | status | elab | note |
|---:|---|---|---:|---|
| 1 | `Formal.EndpointSafeTwoSpaceDuhamel` | pass | 2.3s |  |
| 2 | `Formal.R3LerayFrequencySymbol` | pass (warn) | replayed |  |
| 3 | `Formal.R3StokesFrequencySymbol` | pass | cached | built in the earlier smoke run, up to date |
| 4 | `Formal.R3StokesL2Operator` | pass (warn) | replayed |  |
| 5 | `Formal.R3CoordinateLinearAux` | pass (warn) | 2.9s |  |
| 6 | `Formal.R3L2ScalarAux` | pass (warn) | 3.8s |  |
| 7 | `Formal.FlowMapFTC` | pass | cached | built in the earlier smoke run, up to date |
| 8 | `Formal.FlowMapChainRule` | pass | cached | built in the earlier smoke run, up to date |
| 9 | `Formal.FlowMapOperatorContinuity` | pass | cached | built in the earlier smoke run, up to date |
| 10 | `Formal.FlowMapContDiffOne` | pass | cached | built in the earlier smoke run, up to date |
| 11 | `Formal.FlowMapLocalContDiff` | pass | cached | built in the earlier smoke run, up to date |
| 12 | `Formal.PDEBridgeAdapter` | pass | cached | built in the earlier smoke run, up to date |
| 13 | `Formal.NavierStokesTimeBridge` | pass | cached | built in the earlier smoke run, up to date |
| 14 | `Formal.FlowMapNonextendibilityCriterion` | pass (warn) | replayed |  |
| 15 | `Formal.UniformRestartContinuation` | pass (warn) | replayed |  |
| 16 | `Formal.R3SobolevCarrier` | pass (warn) | replayed |  |
| 17 | `Formal.R3SolenoidalSobolevCarrier` | pass | 3.2s |  |
| 18 | `Formal.R3NormalizedFrequencyLpTop` | pass | 2.5s |  |
| 19 | `Formal.R3L2CoordinateAux` | pass | 2.5s |  |
| 20 | `Formal.R3NormalizedDivergenceTerm` | pass | 2.5s |  |
| 21 | `Formal.R3DivergencePointwise` | pass (warn) | 2.5s |  |
| 22 | `Formal.R3NormalizedDivergenceFrequency` | pass | 2.5s |  |
| 23 | `Formal.R3ClosedSolenoidalCarrier` | pass | 2.4s |  |
| 24 | `Formal.R3SolenoidalCarrierCompleteness` | pass | 2.5s |  |
| 25 | `Formal.R3LerayL2Operator` | pass (warn) | 2.8s |  |
| 26 | `Formal.R3SchwartzConvection` | pass | 3.9s |  |
| 27 | `Formal.R3SchwartzSobolevCore` | pass | 3.5s |  |
| 28 | `Formal.R3SchwartzConvectionSobolevReduction` | pass | 2.9s |  |
| 29 | `Formal.R3H2BesselWeightGeometry` | pass | 2.5s |  |
| 30 | `Formal.R3H2WeightedConvolutionKernel` | pass | 2.6s |  |
| 31 | `Formal.R3H2AdditiveConvolutionWeight` | pass | 2.7s |  |
| 32 | `Formal.R3YoungL1L2Bochner` | pass | 2.0s |  |
| 33 | `Formal.R3SchwartzSobolevMonotonicity` | pass | 2.9s |  |
| 34 | `Formal.R3H2YoungWeightedBridge` | pass | 2.9s |  |
| 35 | `Formal.R3H2FourierL1Bound` | pass | 4.5s |  |
| 36 | `Formal.R3LerayFourierBridge` | pass (warn) | 3.8s |  |
| 37 | `Formal.R3LerayComplexFiberSymbol` | pass (warn) | 2.8s |  |
| 38 | `Formal.R3LerayComplexDivergenceBridge` | pass | 2.6s |  |
| 39 | `Formal.R3LerayPointwiseL2` | pass | 2.7s |  |
| 40 | `Formal.R3LerayPointwiseProjectionIdentification` | pass | 2.9s |  |
| 41 | `Formal.R3H2LerayBridge` | pass (warn) | 5.8s |  |
| 42 | `Formal.R3SchwartzProductConvolution` | pass | 3.2s |  |
| 43 | `Formal.R3SchwartzConvectionH2FrequencyMajorant` | pass | 4.7s |  |
| 44 | `Formal.R3SchwartzConvectionScalarMajorants` | pass | 4.2s |  |
| 45 | `Formal.R3YoungRealL1L2Bochner` | pass (warn) | 3.0s |  |
| 46 | `Formal.R3SchwartzNormFieldL2` | pass | 4.0s |  |
| 47 | `Formal.R3YoungRealSetIntegralBridge` | pass (warn) | 4.5s |  |
| 48 | `Formal.R3YoungRealConvolutionCommutativity` | pass | 3.7s |  |
| 49 | `Formal.R3SchwartzMajorantYoungRepresentative` | pass | 2.7s |  |
| 50 | `Formal.R3SchwartzScalarMajorantL2` | pass | 2.6s |  |
| 51 | `Formal.R3SchwartzConvectionH2L2Majorant` | pass | 2.0s |  |
| 52 | `Formal.R3H2VelocityFourierL1Bound` | pass | 4.0s |  |
| 53 | `Formal.R3H2CoordinateFourierBounds` | pass | 2.0s |  |
| 54 | `Formal.R3H3DerivativeWeightGeometry` | pass | 2.6s |  |
| 55 | `Formal.R3SchwartzDerivativeFrequencyBound` | pass | 3.1s |  |
| 56 | `Formal.R3SchwartzDerivativeH3LpBounds` | pass | 3.4s |  |
| 57 | `Formal.R3SchwartzConvectionH3Closure` | pass | 4.6s |  |
| 58 | `Formal.R3SchwartzConvectionSobolevEstimate` | pass | 4.1s |  |
| 59 | `Formal.R3SchwartzSobolevDensity` | pass | 2.8s |  |
| 60 | `Formal.R3SobolevConvectionExtension` | pass (warn) | 7.6s |  |
| 61 | `Formal.R3ProjectedSobolevConvection` | pass | 3.0s |  |
| 62 | `Formal.R3StokesDivergenceCommutation` | pass | 2.5s |  |
| 63 | `Formal.R3StokesSolenoidalPreservation` | pass | 3.2s |  |
| 64 | `Formal.R3StokesH2H3Smoothing` | pass (warn) | 4.4s |  |
| 65 | `Formal.R3StokesH3Evolution` | pass | 7.9s |  |
| 66 | `Formal.R3EndpointSafeProjectedDuhamel` | pass | 4.1s |  |
| 67 | `Formal.EndpointSafeTwoSpacePicard` | pass (warn) | 3.6s |  |
| 68 | `Formal.R3EndpointSafeProjectedLocalExistence` | pass | 4.1s | **TARGET** |
| 69 | `Formal.R3ConjugationReflection` | pass | 4.7s |  |
| 70 | `Formal.R3FourierConjugationBridge` | pass | 5.4s |  |
| 71 | `Formal.R3StokesConjugationEquivariance` | pass | 4.5s |  |
| 72 | `Formal.R3LerayConjugationEquivariance` | pass | 4.1s |  |
| 73 | `Formal.R3ConvectionConjugationEquivariance` | pass | 14s |  |
| 74 | `Formal.R3RealLocalMildSolution` | **FAIL** | 3.9s |  |
| 75 | `Formal.R3QuantitativeLifespan` | **not built** | — | blocked by R3RealLocalMildSolution |
| 76 | `Formal.EndpointSafeTwoSpaceRestart` | pass | 4.6s |  |
| 77 | `Formal.EndpointSafeTwoSpaceConcatenation` | pass (warn) | 3.0s |  |
| 78 | `Formal.EndpointSafeTwoSpaceUniqueness` | **not built** | — | blocked by R3RealLocalMildSolution |
| 79 | `Formal.R3MildContinuation` | **not built** | — | **TARGET** blocked by R3RealLocalMildSolution |
| 80 | `Formal.R3CoordinateIncompressibility` | pass | 4.1s |  |
| 81 | `Formal.R3ClassicalIncompressibility` | pass | 4.5s |  |
| 82 | `Formal.R3DecoderFrequencyBridge` | pass | 3.5s |  |
| 83 | `Formal.R3InversionConsistency` | pass | 4.2s |  |
| 84 | `Formal.R3HelmholtzPressure` | pass | 9.5s | **TARGET** |
| 85 | `Formal.R3ConvectionSourceIdentification` | pass (warn) | 8.3s |  |
| 86 | `Formal.R3ProjectedMomentumDuhamelInfrastructure` | pass (warn) | 6.9s |  |
| 87 | `Formal.R3ProjectedMomentumEquation` | pass | 7.0s |  |
| 88 | `Formal.R3NavierStokesEquation` | pass | 5.2s | **TARGET** |

Totals: **84 pass / 1 fail / 3 not reached (blocked)** out of 88.
Of the four targets, `R3EndpointSafeProjectedLocalExistence`, `R3HelmholtzPressure` and
`R3NavierStokesEquation` **pass**; `R3MildContinuation` is **not reached**.

The three unreached modules are unreached only because they import the failing one:

```
Formal.R3RealLocalMildSolution        <- FAILS
  └─ Formal.R3QuantitativeLifespan
  └─ Formal.EndpointSafeTwoSpaceUniqueness
        └─ Formal.R3MildContinuation  (target)
```

They have therefore **never been elaborated** under 4.34.0-rc2 and may hide further breakage.

---

## (c) Error taxonomy

### Hard errors: 1 (one module, one error)

| class | count | modules |
|---|---:|---|
| **changed definitional transparency of `NNReal` in tactic unification** | 1 | `Formal.R3RealLocalMildSolution` |
| renamed / removed Mathlib lemma | 0 | — |
| changed signature or implicitness | 0 | — |
| `simp` set drift | 0 | — |
| universe / instance issue | 0 | — |
| other | 0 | — |

**The single error** (`research/U05/build.log` line 338):

```
error: Formal/R3RealLocalMildSolution.lean:76:16: Tactic `rewrite` failed:
  Did not find an occurrence of the pattern
    r3L2Conj ((r3StokesH3Evolution ?hnu ?t) ?g)
  in the target expression
    r3L2Conj ((r3StokesH3Evolution ⋯ ⟨t, ⋯⟩) u0) - …

Note: The target expression is not type-correct under the `implicit` transparency level,
which may have triggered the failure. …
Full error:
  Application type mismatch: The argument  ⟨t, ⋯⟩
  has type    { r // 0 ≤ r }
  but is expected to have type    ℝ≥0
  in the application  r3StokesH3Evolution ⋯ ⟨t, ⋯⟩
```

Diagnosis. HeliCorgi builds nonnegative times with the anonymous constructor,
`r3StokesH3Evolution hnu.le ⟨t, ht.1⟩ u0`, exploiting `NNReal = { r : ℝ // 0 ≤ r }` as a
definitional equality. Under Lean 4.34.0-rc2 the type-correctness check that `rw`/`kabstract`
performs runs at `implicit` transparency, at which `NNReal` no longer unfolds to the subtype, so
the elaborated `Subtype.mk t ht.1` no longer matches a pattern whose metavariable has type `ℝ≥0`.
Mathlib anticipated exactly this and added a constructor with a docstring saying so
(`Mathlib/Data/NNReal/Defs.lean:71`, Mathlib PR #37609 `feat: use a constructor for NNReal`, 2026-04-04 — i.e. already present at HeliCorgi's
own pin, they just did not use it):

> *Important: You should use `NNReal.mk` instead of the anonymous constructor `⟨_, _⟩` to avoid
> abuse of the definitional equality between `ℝ≥0` and `{ r : ℝ // 0 ≤ r }`.*

So this is best classified as **deprecated/changed tactic behaviour driven by a transparency
change**, not a lemma rename. It is mechanical, but it propagates (see the fix experiment).

Static blast radius. Counting source lines inside the 88-module closure that pass an anonymous
constructor to an `ℝ≥0`-indexed operator (`linearEvolution`, `IsMildAt`, `r3StokesH3Evolution`,
`r3StokesL2Operator`, `r3StokesL2Path`): **42 lines in 10 files** —
`EndpointSafeTwoSpaceConcatenation` (16), `EndpointSafeTwoSpaceRestart` (12),
`R3RealLocalMildSolution` (5), `EndpointSafeTwoSpaceDuhamel` (2), `R3NavierStokesEquation` (2),
`R3EndpointSafeProjectedDuhamel` (1), `EndpointSafeTwoSpacePicard` (1),
`R3EndpointSafeProjectedLocalExistence` (1), `R3ProjectedMomentumDuhamelInfrastructure` (1),
`R3ProjectedMomentumEquation` (1). (Grep-based, so treat it as the right order of magnitude
rather than an exact edit list.) Only the ones in `R3RealLocalMildSolution` actually break the
build; the other 37 are harmless as written, because no tactic has to *match* against them —
but they all become live the moment a shared statement is converted, which is what experiment 2
below demonstrates.

### Fix experiment (2 attempts, inside the probe copy only — `vendor/` untouched)

1. **`replace ht : (0 : ℝ) ≤ t ∧ t ≤ T := ht`** inserted after `intro t ht`
   (`R3RealLocalMildSolution.lean:55`). Did not fix it, but stripped the red herring and exposed
   the real `ℝ≥0` vs `{ r // 0 ≤ r }` mismatch quoted above. Reverted.
2. **`⟨t, ht.1⟩` → `NNReal.mk t ht.1`**, applied in `R3RealLocalMildSolution.lean` (5 sites) and
   then also in the two *statements* it rewrites against — `EndpointSafeTwoSpaceDuhamel.lean:613,635`
   (`IsMildSolutionOn`, `equation_at_time`) and `R3EndpointSafeProjectedDuhamel.lean:171`
   (`r3EndpointSafeProjectedMild_equation_at_time`). Log: `research/U05/build-after-fix.log`.
   Result: **the original error disappears**, and exactly two *new* `rewrite` failures appear at
   call sites that still use the old spelling and therefore no longer match the amended statements:

   ```
   error: Formal/EndpointSafeTwoSpacePicard.lean:832:12: Tactic `rewrite` failed:
     Did not find an occurrence of the pattern  ⟨t, ⋯⟩
     in the target expression  u ↑(NNReal.mk t ⋯) = (C.linearEvolution (NNReal.mk t ⋯)) u₀ - …
   error: Formal/R3ProjectedMomentumDuhamelInfrastructure.lean:779:8: Tactic `rewrite` failed:
     Did not find an occurrence of the pattern  r3H3ToL2Operator ((r3StokesH3Evolution ⋯ ⟨t, ⋯⟩) u₀)
     in the target expression  r3H3ToL2Operator ((r3StokesH3Evolution ⋯ (NNReal.mk t ⋯)) u₀) = …
   ```

   Both are the *same* rule applied at two more places. This is the load-bearing finding for the
   effort estimate: the fix is a single mechanical substitution, but it must be applied
   **consistently across all ~42 sites in one pass**, not incrementally, and each iteration costs a
   ~2-minute full rebuild of the closure. The probe was then reverted to pristine
   (`bash make_probe.sh`) and rebuilt; the pristine state reproduces `build.log` exactly
   (exit 1, 84 oleans).

### Warnings: 52, in 20 of the 88 modules — none fatal today

| class | count | representative |
|---|---:|---|
| `letI`/`haveI` in a Prop goal — "Try this: `have`/`let`" | 16 | `Formal/R3StokesL2Operator.lean:111:2` |
| `linter.unusedVariables` (unreferenced binder) | 15 | `Formal/FlowMapNonextendibilityCriterion.lean:40:16` — ``Variable name `ht0` is not explicitly referenced`` |
| **deprecated Mathlib names** | 11 | `Formal/EndpointSafeTwoSpacePicard.lean:627:18` — ``continuousOn_iff_continuous_restrict`` → ``continuousOn_iff_continuous_domRestrict`` |
| `linter.unnecessarySimpa` | 8 | `Formal/R3LerayFrequencySymbol.lean:43:2` — "try 'simp' instead of 'simpa'" |
| `linter.defProp` (a `def` whose type is a Prop) | 1 | `Formal/UniformRestartContinuation.lean:95:0` |
| `tac1 <;> tac2` where `(tac1; tac2)` suffices | 1 | `Formal/R3DivergencePointwise.lean:25:19` |

The 11 deprecations are only 3 distinct aliases:
`continuousOn_iff_continuous_restrict` → `continuousOn_iff_continuous_domRestrict` (2×),
`if_pos`/`if_neg` → `ite_eq_left`/`ite_eq_right` (8×),
`MeasureTheory.Measure.QuasiMeasurePreserving.ae_eq` → `…ae_eq_comp` (1×).

This matters because `verification/lakefile.toml` sets `warningAsError = true` on the `Tests`
lib and `vendor/NavierStokesAndEuler` sets it on `Euler`. If HeliCorgi sources are ever built
under a `warningAsError = true` lean_lib, **all 52 warnings become errors**. Under
`formalization/`'s current settings (no `warningAsError`) they do not.

---

## (d) Mathlib revision gap

| | HeliCorgi | this repository |
|---|---|---|
| toolchain | `leanprover/lean4:v4.32.1` | `leanprover/lean4:v4.34.0-rc2` |
| Mathlib rev | `520045ab14e26149ee970e2e617ca04b09bde5d6` | `85e3a25e006c35636f0e53b0e9296caca2685bc0` |
| that commit | `chore: bump toolchain to v4.32.1` | `chore: bump toolchain to v4.34.0-rc2 (#43012)` |
| date | 2026-07-23 11:50:32 +0200 | 2026-08-21 15:44:32 +0000 |
| Lake config | `lakefile.lean`, `require mathlib @ "v4.32.1"` | `lakefile.toml`, `rev = "v4.34.0-rc2"` |

Their revision **is** present in the shared clone, so the distance is exact:

```
$ git -C .../packages/mathlib log --oneline 520045ab..85e3a25e | wc -l
826
```

**826 commits / 29 days / two Lean minor releases behind.** For a Mathlib gap this is small,
which is consistent with the measured outcome (95 % of the closure compiles untouched).

---

## (e) Porting effort and recommendation

### Effort, by class

| class | modules | work | estimate |
|---|---:|---|---|
| A. compiles unchanged | 84 | none | **0 h** |
| B. `NNReal` anonymous-constructor idiom | 1 broken module, ~42 call sites in 10 files | one mechanical substitution `⟨x, h⟩` → `NNReal.mk x h` over ~42 lines in 10 files, applied in a single pass, then 2–4 rebuild/iterate cycles at ~2 min each | **2–6 h** |
| C. the 3 never-elaborated modules | 3 | unknown; they have never seen 4.34.0-rc2. Base rate from class A suggests 0–1 further errors of the same kind | **0–4 h** |
| D. warning hygiene (only if built under `warningAsError = true`) | 20 | 52 warnings, 6 mechanical classes, 3 distinct deprecated aliases | **1–2 h** |

**Total: 0.5–1.5 person-days**, most likely under one day, to get all 88 modules green.
Class A alone — three of the four targets, i.e. the whole chain up to and including
`∂ₜU − νΔU + (U·∇)U + ∇p = 0, ∇·U = 0` (`R3NavierStokesEquation`) plus the Helmholtz pressure
identification — is available **today for zero work**.

### Recommendation: port the closure, do not keep a second toolchain

1. **Reject "separate 4.32.1 checkout with a bridge."** There is no such thing as a bridge
   between Lean toolchains: `.olean` files are toolchain-specific and cannot be imported across
   4.32.1 and 4.34.0-rc2. A "bridge" would have to restate HeliCorgi's conclusions as hypotheses
   or axioms in our package, which `collaboration/tasks/U05.md` and `CONTRIBUTING.md` explicitly
   forbid ("No hypothetical proposition fields or admitted theorem may stand in for a missing PDE
   statement"). The 4.32.1 checkout stays useful only as a *source* reference.
2. **Reject downgrading our pin to 4.32.1.** `formalization/`, `verification/` and
   `vendor/NavierStokesAndEuler/` are all on 4.34.0-rc2, and the OpenAI package requires it.
3. **Recommended, step 1 (no source edits, do this now).** Add a `lean_lib` to `formalization/`
   whose `srcDir` is `../vendor/HeliCorgi` with an explicit module list of the **84 modules that
   already compile**. This is a lakefile-only change: it builds the vendored sources in place
   under our toolchain and our Mathlib pin, keeps `vendor/` byte-identical (satisfying the CI rule
   that forbids HeliCorgi source edits), and immediately makes local existence, ball uniqueness,
   the realness gate's operator layer, the Helmholtz pressure and the full NS-equation
   identification citable from our package. Watch out for two things: the lib must not carry
   `warningAsError = true`, and HeliCorgi's own `lakefile.lean` must not be pulled in as a path
   dependency (it would try to require Mathlib at `v4.32.1`).
4. **Recommended, step 2 (needs a decision).** The continuation / blow-up-dichotomy branch
   (`R3RealLocalMildSolution` → `R3QuantitativeLifespan` / `EndpointSafeTwoSpaceUniqueness` →
   `R3MildContinuation`) needs the `NNReal.mk` substitution (~42 lines, 10 files). Two clean ways to get it without
   breaking the no-vendor-edits rule:
   - **preferred:** send the patch upstream to HeliCorgi and re-vendor. It is a one-rule change
     they should want anyway, since Mathlib's own docstring asks for it.
   - **fallback:** record a reviewed patch file under `research/U05/` (or a `vendor-patches/`
     directory) applied by `scripts/lean-install.sh` at checkout time, so the tracked vendor tree
     stays pristine and the deviation is auditable.
   Do **not** silently fork the four files into `formalization/`: module names would collide with
   the `srcDir` lib from step 1.
5. **Re-run this probe on every Mathlib bump.** `research/U05/probe/make_probe.sh` +
   `lake build <4 targets>` is a ~2-minute regression test once Mathlib is built, and it needs no
   network and no extra disk.

---

## (f) Exact commands and wall times

Environment for every command below:

```bash
cd /data_8T/ping/blowup_density/.claude/worktrees/004-U05-toolchain-probe
. scripts/lean-env.sh                 # sets ELAN_HOME to <repo>/.elan
export LEAN_NUM_THREADS=6
export http_proxy=http://127.0.0.1:9 https_proxy=http://127.0.0.1:9 GIT_TERMINAL_PROMPT=0
```

The dead-proxy variables are a safety interlock: any attempt by Lake to clone or fetch would have
failed instantly instead of downloading Mathlib. Nothing ever tried.
Note: **Lake 5.0.0 (Lean 4.34.0-rc2) has no `-j` flag** (`lake build -j 6` → `error: unknown short
option '-j'`); job parallelism is driven by `LEAN_NUM_THREADS`. Measured 353 % CPU on the main run.

| # | command | wall time | result |
|---:|---|---:|---|
| 1 | `bash research/U05/probe/make_probe.sh` | < 1 s | copies `vendor/HeliCorgi/Formal` (128 files) into the probe, copies `vendor/NavierStokesAndEuler/lake-manifest.json`, symlinks `.lake/packages` → `verification/.lake/packages` |
| 2 | `lake resolve-deps` | 0.1 s | exit 0. One benign `warning: manifest out of date: git revision of dependency 'mathlib' changed` (our lakefile pins the SHA `85e3a25e…`, the borrowed manifest records `inputRev = "v4.34.0-rc2"` resolving to the same SHA). Lake did **not** fetch, clone or check out anything. |
| 3 | `lake env printenv LEAN_PATH` | 0.1 s | confirms the probe uses the shared prebuilt Mathlib at `/data_8T/ping/blowup_density/verification/.lake/packages/mathlib/.lake/build/lib/lean` |
| 4 | `lake build Formal.R3SobolevCarrier` (smoke) | **28.1 s** | exit 0, 8775 jobs, warnings only |
| 5 | `lake build --no-ansi Formal.R3EndpointSafeProjectedLocalExistence Formal.R3MildContinuation Formal.R3NavierStokesEquation Formal.R3HelmholtzPressure` | **1 m 53.4 s** (user 319.9 s, sys 80.7 s, 353 % CPU, max RSS 6.96 GB) | **exit 1** — 84/88 built, 1 failure, 3 blocked. Full log: `research/U05/build.log` |
| 6 | same, after fix experiment 2 | **13.3 s** | exit 1 — original error gone, 2 new `rewrite` failures at unconverted call sites. Log: `research/U05/build-after-fix.log` |
| 7 | `bash research/U05/probe/make_probe.sh` then command 5 again | ~2 min (not instrumented) | exit 1, 84 oleans — pristine state restored and reproduces `build.log` |

Well within the 45-minute budget; no kill was needed.

### Shared-package integrity (the thing that must not break)

`git rev-parse HEAD` was recorded for all 11 packages in
`/data_8T/ping/blowup_density/verification/.lake/packages` before the probe and re-checked after
every build:

```
Cli ab3a82db…  Comparator 19e111e2…  LeanSearchClient ba67e212…  Qq 507746ab…
aesop 18889deb…  batteries d54dddc5…  importGraph d8823026…  lean4export cacf989b…
mathlib 85e3a25e006c35636f0e53b0e9296caca2685bc0  plausible d9598f07…  proofwidgets a8acbfd8…
```

**All 11 unchanged**, and `git -C …/mathlib status --short` is empty (clean working tree).
No `lake update` was run anywhere. `vendor/` is byte-identical to HEAD
(`diff -rq vendor/HeliCorgi/Formal research/U05/probe/Formal` is silent).

---

## Files produced

| path | tracked? | what |
|---|---|---|
| `research/U05/REPORT.md` | yes | this report |
| `research/U05/build.log` | yes | full log of the pristine 88-module build (408 lines) |
| `research/U05/build-after-fix.log` | yes | log of fix experiment 2 |
| `research/U05/probe/lakefile.toml` | yes | probe package: `HeliCorgiProbe`, Mathlib pinned to `85e3a25e…`, `lean_lib Formal` |
| `research/U05/probe/lean-toolchain` | yes | `leanprover/lean4:v4.34.0-rc2` |
| `research/U05/probe/make_probe.sh` | yes | re-creates the source copy, the borrowed manifest and the packages symlink |
| `research/U05/probe/.gitignore` | yes | ignores `Formal/`, `.lake/`, `lake-manifest.json` |
| `research/U05/probe/Formal/` | no (ignored) | copy of `vendor/HeliCorgi/Formal`, regenerated by `make_probe.sh` |
| `research/U05/probe/.lake/` | no (ignored) | build output; `packages` is a symlink to the shared tree |
| `research/U05/probe/lake-manifest.json` | no (ignored) | copy of `vendor/NavierStokesAndEuler/lake-manifest.json` |

Nothing under `vendor/`, `formalization/`, `verification/`, `paper/` or `collaboration/` was
modified. No git write command was run.
