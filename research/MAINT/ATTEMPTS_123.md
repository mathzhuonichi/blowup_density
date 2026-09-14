# Lane 123-MAINT-pairing-home — attempts / record

Pure maintenance: relocate two modules to remove a D01 → A04 reverse module edge (against the
task DAG, where D01 is the root of the critical chain D01 → A01 → A02 → A04). No new mathematics;
every declaration name/statement/proof body byte-identical; only the module `import` lines change.
Motivated by `research/A04/REVIEW_SIMP_SL3.md` Finding 6.

Worktree `.claude/worktrees/123-MAINT-pairing-home`, branch `erenup/123-MAINT-pairing-home`,
base `origin/erenup/integration`.

## The problem

`Section4/D01/LerayLowering.lean` (lane 085) had
`import NSFormalization.Section4.A04.LaplacianPairing` and `import …A04.RealPairing`, consuming
five of their declarations (`angularOrderLoweringMid`, `angularOrderLowering_eq_dilation_mid`,
`angularOrderLoweringMid_coeFn`, `lowering_mid_symbol_eq`, `angularOrderLowering_self`).
That is a genuine inverted module edge: a D01 file importing A04 files.

Both `A04/LaplacianPairing.lean` and `A04/RealPairing.lean` put their whole bodies in namespace
`NSFormalization.Paper3` and (per the 115 reviewer) use **no** `Section4.A04` declaration.

## Dependency evidence

Every non-Mathlib declaration referenced by the two files, and its **defining module** (found by
`grep -rn 'def/theorem <name>'` over `formalization/NSFormalization`):

| declaration used | defining module | layer |
|---|---|---|
| `angularWeightEquiv`, `angularWeightSymbol`, `angularWeightMap_coeFn` | `Paper3/AngularSobolevCoordinates.lean` | Paper3 |
| `sobolevDirectionalDerivative`, `sobolevDirectionalSymbol`, `sobolevDirectionalDerivative_coeFn` | `Paper3/SobolevDirectionalDerivative.lean` | Paper3 |
| `angularFrequencyDilation` | `Paper3/AngularFourierDilation.lean` | Paper3 |
| `angularOrderLowering`, `cyclesToAngular` | `Paper3/AngularTameProduct.lean` | Paper3 |
| `sobolevOrderLowering`, `sobolevOrderLowering_coeFn` | `Paper3/SobolevOrderLowering.lean` | Paper3 |
| `sobolevBesselWeight`, `sobolevBesselWeight_mul` | `Paper3/SobolevHilbertModel.lean` | Paper3 |
| `RealSobolevHilbert`, `FourierData`, `frequencyUnit` | `Source/RealSobolev.lean` (opened) | Source |
| **`angularDirectionalDerivative`** | **`Section4/D01/DerivativeDatum.lean:62`** | **D01** |
| **`mid_symbol_imaginary`** | **`Section4/D01/DerivativeDatum.lean:183`** | **D01** |
| **`lowering_symbol_real`** | **`Section4/D01/DerivativeDatum.lean:175`** | **D01** |
| **`angularDirectionalDerivativeReal`, `angularDirectionalDerivativeReal_coe`** | **`Section4/D01/DerivativeDatum.lean:134,141`** | **D01** (used by `RealPairing` only) |

Note: the D01-defined declarations (`angularDirectionalDerivative`, `mid_symbol_imaginary`,
`lowering_symbol_real`, `angularDirectionalDerivativeReal(_coe)`) are all in the
`NSFormalization.Paper3` **namespace** block of `DerivativeDatum.lean` (lines 55–219), so they are
not `Section4.A04` names and the 115 reviewer's "no A04 declaration used" claim is correct. But
their **defining module** is a `Section4.D01.*` module, which is the layering fact that matters.

`A04.LaplacianDatum` (the sole current import of `LaplacianPairing`) imports `A04.HighEnergy` +
`D01.DerivativeDatum`; `LaplacianPairing` reached `D01.DerivativeDatum` (and all the Paper3/Source
helpers) transitively through it, and used **nothing** from `A04.LaplacianDatum`/`HighEnergy`.

### Probes (imports replaced)

- **Positive** — `tmp/probe123/probe_lap.lean` = `LaplacianPairing` body with line 1 replaced by
  `import NSFormalization.Section4.D01.DerivativeDatum` (dropping `A04.LaplacianDatum`):
  `lake env lean` → **silent, exit 0**. So `D01.DerivativeDatum` alone suffices for
  `LaplacianPairing`; nothing from `A04.LaplacianDatum`/`HighEnergy` is used.
- **Negative** — `tmp/probe123/probe_lap_paper3.lean` = same body importing only the six Paper3
  helper modules (`AngularFourierDilation`, `SobolevDirectionalDerivative`, `AngularTameProduct`,
  `AngularSobolevCoordinates`, `SobolevOrderLowering`, `SobolevHilbertModel`) **without**
  `D01.DerivativeDatum`: `lake env lean` → **exit 1**, errors:
  ```
  ...:67:4: error: Function expected at   angularDirectionalDerivative   (identifier ... is unknown ...)
  ...:100:15: error(lean.unknownIdentifier): Unknown identifier `mid_symbol_imaginary`
  ...:111:8: error: Function expected at   angularDirectionalDerivative
  ```
  This proves a **`Paper3/` home is infeasible** — a Paper3-layer module cannot import
  `Section4.D01.DerivativeDatum`.

## Home decision

`Section4/D01/` (NOT `Paper3/`, which reviewer Finding 6 tentatively suggested). Both files
genuinely need the D01 module `Section4.D01.DerivativeDatum`, which `Paper3/` cannot import.
Either home would remove the reverse edge, but only the D01 home is feasible.

- `Section4/A04/LaplacianPairing.lean` → `Section4/D01/LaplacianPairing.lean`
  (import: `A04.LaplacianDatum` → `D01.DerivativeDatum`)
- `Section4/A04/RealPairing.lean` → `Section4/D01/RealPairing.lean`
  (import: `A04.LaplacianPairing` → `D01.LaplacianPairing`; the second import
  `D01.DerivativeDatum` was already present and is unchanged)

Both moved files then live in D01 and import only D01/Paper3/Source/Mathlib — so `LerayLowering`
(D01) importing them is a D01 → D01 edge. No shim modules left at the old A04 paths (the namespace
`NSFormalization.Paper3` is unchanged, so no `alias` is needed).

## Name-collision check

All 21 relocated declarations were grepped for `def`/`theorem`/`lemma` definitions across the whole
`formalization/NSFormalization` tree: each is defined in exactly **one** place (the file being
moved). Zero duplicates, so the move (namespace unchanged) introduces no `NSFormalization.Paper3.*`
FQN collision. Confirmed post-move by the two `axioms_*` conformance files elaborating with no
unknown-identifier / ambiguity errors.

## Importers updated (import line only)

| file | change |
|---|---|
| `Section4/D01/LerayLowering.lean` (lines 4,5) | `A04.LaplacianPairing`→`D01.LaplacianPairing`, `A04.RealPairing`→`D01.RealPairing` |
| `Section4/A04/NonlinearPairing.lean` (line 1) | `A04.RealPairing`→`D01.RealPairing` |
| `Section4/A04/LaplacianAssembly.lean` (line 1) | `A04.RealPairing`→`D01.RealPairing` |
| `research/A04/axioms_sl3_pairing.lean` (line 1) | `A04.LaplacianPairing`→`D01.LaplacianPairing` |
| `research/A04/axioms_sl3_real.lean` (line 1) | `A04.RealPairing`→`D01.RealPairing` |
| `Section4/D01/RealPairing.lean` (moved file, line 1) | `A04.LaplacianPairing`→`D01.LaplacianPairing` |

(A04 modules `NonlinearPairing`/`LaplacianAssembly` importing `D01.RealPairing` is a **forward**
A04 → D01 edge, allowed by the DAG.) The `.md` mentions of the old module paths are history and
were left as they are, except: a one-line relocation note added at the top of
`research/A04/ATTEMPTS_SL3_PAIRING.md` and `ATTEMPTS_SL3_REAL.md`, and a "DONE" note in the MAINT
list of `research/A04/ATTEMPTS_SIMP.md`.

## Byte-identical verification

`git diff -M --find-renames HEAD` on the two files: each shows `similarity index 99%`, a
`rename from …/A04/… to …/D01/…`, and a single changed hunk = the import line. Independent
`sha256sum` of each file's body (line 3 onward — the entire docstring + all declarations) against
the pre-move A04 original: **IDENTICAL** for both files.

## Import-closure probe (`research/MAINT/probes/closure_123.py`)

Parses every `.lean` under `formalization/NSFormalization`, builds the `NSFormalization.*` import
graph, and computes the transitive closure of every `Section4.D01.*` module. Output:

```
=== D01 modules whose import-closure reaches A04 (reverse edge) ===
  NONE — no Section4.D01.* module imports any Section4.A04.* module.
  NSFormalization.Section4.D01.LaplacianPairing imports: ['NSFormalization.Section4.D01.DerivativeDatum']
  NSFormalization.Section4.D01.RealPairing imports: ['NSFormalization.Section4.D01.LaplacianPairing', 'NSFormalization.Section4.D01.DerivativeDatum']
  NSFormalization.Section4.A04.LaplacianPairing present as file? False
  NSFormalization.Section4.A04.RealPairing present as file? False
```

(The "Paper3/* imports no Section4.*" check the brief mentions applies only if the home were
`Paper3/`; the home is `Section4/D01/`, so it is N/A here.)

## Commands run (all `lake` from `verification/`, env sourced first, `LEAN_NUM_THREADS=6`)

| command | result |
|---|---|
| `lake env lean tmp/probe123/probe_lap.lean` (D01.DerivativeDatum-only import) | silent, exit 0 |
| `lake env lean tmp/probe123/probe_lap_paper3.lean` (Paper3-only, negative) | exit 1; `angularDirectionalDerivative`/`mid_symbol_imaginary`/`lowering_symbol_real` unknown |
| `lake build …D01.{LaplacianPairing,RealPairing,LerayLowering}, …A04.{NonlinearPairing,LaplacianAssembly}` | `Build completed successfully (9929 jobs).` |
| `lake build …A04.NonlinearBound, …D01.PressureJets` | `Build completed successfully (9945 jobs).` (`A04.PressureDrop` does not exist) |
| `lake build` full `Section4` module list (96 modules from `find`) | `Build completed successfully (10119 jobs).` (only pre-existing vendor `Formal.*` deprecation warnings) |
| `lake env lean` on the two moved files `Section4/D01/{LaplacianPairing,RealPairing}.lean` | each silent, exit 0 |
| `lake env lean research/A04/axioms_sl3_pairing.lean` | 10 decls, all `[propext, Classical.choice, Quot.sound]` |
| `lake env lean research/A04/axioms_sl3_real.lean` | 11 decls, all `[propext, Classical.choice, Quot.sound]` |
| `scripts/gates.sh …` (`make check`, `make test`, `make test-mutations`, `check_contracts`) | `make check` OK; `make test` all 21 `Tests.*` "checked; standard logical axioms only", 0 errors; mutations `Mutation suite passed`; `check_contracts` architecture OK; `== gates OK` |
| `python3 research/MAINT/probes/closure_123.py` | exit 0; no D01→A04 reverse edge (output above) |

## Failures / dead ends

None. The one non-obvious point was reviewer Finding 6's tentative `Paper3/` home suggestion, which
the negative probe shows to be infeasible; the D01 home is the correct (and only feasible) choice.
No `sorry`/`axiom`/`native_decide`/`maxHeartbeats` used or present.
