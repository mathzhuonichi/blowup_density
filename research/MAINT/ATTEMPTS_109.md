# Lane 109-MAINT-promotions — attempts / record

Pure maintenance: promote reviewer-flagged Paper3/Source/A03-level facts out of the
Section4 modules where they were first proved, into their canonical homes; keep a
same-namespace alias at the old location so nothing downstream breaks. Every moved
statement + proof is byte-identical; the only proof changes are the two explicitly
requested corollary re-pointings (items 3 and 5b). Aliases use the Mathlib `alias`
command (tested: no ambiguity with the old module's existing `open` of the target
namespace; the old-namespace alias is created and resolves `#print axioms` through to
the standard three logical axioms).

## Move table

| # | theorem | from | to | alias kept? (namespace) | importers rebuilt |
|---|---------|------|----|-------------------------|-------------------|
| 1a | `angularFrequencyDilation_coeFn` | `Section4/D01/Transverse.lean:66` | `Paper3/AngularFourierDilation.lean` | yes, `alias` in `NSFormalization.Section4.D01` (Transverse.lean) | Transverse, OrderZeroSymbol, LerayLowering, Longitudinal |
| 1b | `transverse_of_transverse_symm` | `Section4/D01/OrderZeroSymbol.lean:491` (lane 094) | `Paper3/AngularFourierDilation.lean` | yes, `alias` in `NSFormalization.Section4.D01` (OrderZeroSymbol.lean) | OrderZeroSymbol (+ lane 108, which imports OrderZeroSymbol by bare name — bare name still resolves in `NSFormalization.Section4.D01`) |
| 2 | `angular_plancherel` | `Section4/B02/LowHigh.lean:186` | — | **SKIPPED** (see below) | — |
| 3 | `angularFourier_conj` | `Section4/B02/AnnularReal.lean:54` | `Paper3/AngularFourierDilation.lean` **(target deviation — see below; NOT `Source/FourierConvention.lean`)** | yes, `alias` in `NSFormalization.Section4.B02` (AnnularReal.lean) | AnnularReal; and `D01/HomogeneousWitness.lean:190 angularFourier_conj_neg` rewritten as a one-line corollary (statement unchanged) |
| 4a | `isScalarSobolevDatum_smul` | `Section4/A04/MomentumDatum.lean:116` | `Section4/A03/ScalarTameProduct.lean` | yes, `alias` in `NSFormalization.Section4.A04` (MomentumDatum.lean) | MomentumDatum |
| 4b | `isScalarSobolevDatum_neg` | `Section4/A04/MomentumDatum.lean:140` | `Section4/A03/ScalarTameProduct.lean` | yes, `alias` in `NSFormalization.Section4.A04` | MomentumDatum |
| 4c | `isSobolevDatum_smul` | `Section4/A04/MomentumDatum.lean:132` | `Section4/A03/VectorTameProduct.lean` | yes, `alias` in `NSFormalization.Section4.A04` | MomentumDatum |
| 4d | `isSobolevDatum_neg` | `Section4/A04/MomentumDatum.lean:146` | `Section4/A03/VectorTameProduct.lean` | yes, `alias` in `NSFormalization.Section4.A04` | MomentumDatum |
| 5a | `columnsSobolevENorm_toReal_sq_eq_sum` | `Section4/A04/NonlinearColumns.lean:137` | `Section4/A03/OuterTameProduct.lean` | yes, `alias` in `NSFormalization.Section4.A04` (NonlinearColumns.lean) | NonlinearColumns |
| 5b | `gradientSobolevENorm_toReal_sq_eq_sum` | stays in `Section4/A04/LaplacianDatum.lean:96` | (not moved) | — | LaplacianDatum: proof re-pointed to `A03.columnsSobolevENorm_toReal_sq_eq_sum hfin` (rfl-transparent; statement unchanged). Qualified name used because LaplacianDatum's `open A03 (...)` is selective and does not list the moved name. |
| 6 | `contDiff_slice_pressure` | `Section4/R42/PressureGradient.lean:70` | (LEFT in place) | — | none — measurement only, see below |

A03 does not import A04 (checked by import closure: A04 appears 0 times in the closures of the three
edited `A03` modules; note `A03/*.lean` also import `Euler.EulerProof`, `Section4.D01.SmoothDatum` and
`NavierStokes.ProblemStatement`, none of which reach A04), and `D01` does not import any `B02` module
(checked), so no move created a cycle.

## Item 6 measurement (import cost of `D01.DatumToJets` for `PressureGradient`)

`PressureGradient` currently imports only `A02.SolutionClass` (+ Mathlib). Transitive
project-module (NSFormalization + vendor `Euler`/`NavierStokes`, Mathlib excluded) closures:

- current `PressureGradient` project closure: **52 modules**
- `D01.DatumToJets` project closure: **1113 modules**
- **extra project modules if `PressureGradient` imported `D01.DatumToJets`: 1063**

1063 ≫ ~10 (the bulk is the entire vendor `Euler.*` library, pulled in via
`EulerLpTranslation`/`SmoothL2Field` deep in the D01 datum stack). This confirms the
existing docstring rationale ("inlined here to keep this module's import surface to
`A02.SolutionClass` + Mathlib"). **Decision: LEFT the byte-identical copy
`contDiff_slice_pressure` in place; not replaced by `D01.contDiff_slice_scalar`.**

## Skipped / deviated, with reasons

### Item 2 — SKIPPED: `angular_plancherel` → Paper3
`angular_plancherel` (`LowHigh.lean:186`) is not a self-contained statement: its proof
consumes a chain of `B02`-local helpers defined in the same file —
`angular_lintegral_eq_cycles`, `sq_eLpNorm_two`, `eLpNorm_fourierIntegral_eq`, and
transitively `coeFn_l2Fourier_ae`, `l2_fourier_pairing`, `fourier_mul_formula`,
`lintegral_comp_const_smul`, `finrank_space_eq_three`. Moving `angular_plancherel`
"verbatim, same proof" would require relocating that entire cluster.
Neither candidate target holds the angular-Plancherel machinery (read both headers):
`Paper3/AngularFourierDilation.lean` works at the abstract `Lp`/distribution level and
`Paper3/AngularRealSobolev.lean` is real-Sobolev transport — neither has the
`L¹ ∩ L²` pointwise-`𝓕` Plancherel bridge. The helper cluster additionally needs
`import NavierStokes.R3.CompactSchwartz` (used by `coeFn_l2Fourier_ae`) plus
`Mathlib.Analysis.Fourier.LpSpace` / `Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff`,
none of which are in the Paper3 import surface (Paper3 depends only on `Source.*` + Mathlib).
Promoting it therefore means dragging a whole helper cluster and a heavy vendor import
into a low-level Paper3 module — not a single-theorem verbatim move. Left in place per
the "do not force it" rule.

### Item 3 — target deviation: `Source/FourierConvention.lean` was infeasible; used `Paper3/AngularFourierDilation.lean`
The named target is a bad home and so is the obvious Source fallback (reviewer-corrected rationale,
`REVIEW_109.md` finding 1 — the first version of this bullet wrongly claimed an import cycle):

- **`Source/FourierConvention.lean` (named target): not circular, but a layering inversion with a
  measured import cost.** `angularFourier_conj`'s proof uses `fourier_conjugate` from
  `Source/RealSobolev.lean`. `RealSobolev` and `FourierConvention` do **not** import each other
  (closure check both ways: `False`), so adding `import RealSobolev` to `FourierConvention` would
  compile. It is rejected because it would grow `FourierConvention`'s closure from 30 to 73 modules,
  pull 11 `Paper3.*` modules under a `Source`-layer file that has 6 direct importers, and invert the
  `Source → Paper3` layering. The obstacle is layering and closure cost, not a cycle.
- **`Source/RealSobolev.lean` (tried): missing `angularFourier`.** `RealSobolev` does not
  import `Source/FourierConvention` (verified: `FourierConvention ∉ closure(RealSobolev)`),
  so `angularFourier` is not in scope there — `lake env lean` reported
  `Local variable 'angularFourier' has no definition`. This attempt was reverted
  (RealSobolev has no net change).
- **The lowest modules importing BOTH `angularFourier` (FourierConvention) and
  `fourier_conjugate` (RealSobolev) are `Paper3/AngularSobolevCoordinates` and
  `Paper3/AngularFourierDilation`.** No `Source` module sits below both dependencies,
  so a Source home matching the task's intent does not exist.

Chose `Paper3/AngularFourierDilation.lean`: it is the natural angular-Fourier home, it
already hosts the lane-109 item-1 promotions, and both `B02/AnnularReal` and
`D01/HomogeneousWitness` transitively import it (so the alias and the D01 corollary both
resolve). Statement and proof are byte-identical; feasibility was achieved with two
header `open`s only (`open NSFormalization.Source.RealSobolev (FourierData fourier_conjugate)`
and adding `ComplexConjugate` to the scoped opens) — no proof-body edit. `D01`'s
`angularFourier_conj_neg` (which already reproved the fact directly from
`fourier_conjugate`) is now a one-line corollary of the promoted `angularFourier_conj`,
statement unchanged. **Flagged for lead review:** if a `Source` home is required, both
`angularFourier_conj` and `fourier_conjugate` would have to move together into a module
that also sees `angularFourier` — a larger change than this maintenance lane's scope.

## Verification (exact results)

- `cd verification && lake build <the 9 prescribed modules>` →
  `Build completed successfully (9944 jobs).`
- `lake env lean` on every edited module (11 files) → all **SILENT** (no output).
- research axiom audits re-elaborate, moved names still standard-axiom-only:
  - `research/D01/axioms_transverse.lean`: `…D01.angularFrequencyDilation_coeFn` → `[propext, Classical.choice, Quot.sound]`
  - `research/D01/axioms_order_zero.lean`: `…D01.transverse_of_transverse_symm` → `[propext, Classical.choice, Quot.sound]`
  - `research/A04/axioms_sl2.lean`: `…A04.{isScalarSobolevDatum_smul, isSobolevDatum_smul, isScalarSobolevDatum_neg, isSobolevDatum_neg}` → `[propext, Classical.choice, Quot.sound]`
  - `research/A04/axioms_sl5_columns.lean`: `…A04.columnsSobolevENorm_toReal_sq_eq_sum` → `[propext, Classical.choice, Quot.sound]`
  - `research/A04/axioms_sl3.lean`: `…A04.gradientSobolevENorm_toReal_sq_eq_sum` → `[propext, Classical.choice, Quot.sound]`
  - `research/B02/axioms_u2_sl3.lean`: `…B02.angularFourier_conj` (and `…Paper3.angularFourier_conj`) → `[propext, Classical.choice, Quot.sound]`
  (all files: no errors, no unknown identifiers)
- `cd .. && make check` → contract policy 13/13 OK; work queue consistent; architecture checks pass.
- `make test` → exit 0; **18/18** contracts "checked; standard logical axioms only".

Note: `lake build`/`make test` emit one locationless trace line
"The `ring` tactic failed to close the goal…" during replay. It is pre-existing
dependency noise (a recoverable `ring` in some dependency proof): all 11 edited modules
are silent under `lake env lean`, Tests are `warningAsError = true` yet all pass, and
`make test` exits 0.
