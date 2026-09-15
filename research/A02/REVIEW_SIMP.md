# Review of lane 040 (SIMP-A02): dedupe pass over `Section4/A02/{SolutionClass,Restrict,Order,Energy}.lean`

Reviewed commit `24a252a` on `erenup/040-SIMP-A02-dedupe`, against its parent
`fcf9289`.  Worktree `.claude/worktrees/040-SIMP-A02-dedupe`; every `lake`
invocation from `WT/verification`, one at a time, `LEAN_NUM_THREADS=6`, no `-j`.
All scratch files were written under `/tmp/rv040/` and are gone; the worktree is
untouched apart from this file (`git status --porcelain` empty before and after).

## Verdict: **ACCEPT-WITH-NOTES**

The lane's central claim — *no mathematics changed* — is confirmed, and confirmed
more strongly than by text comparison alone: every surviving public declaration
elaborates to a **byte-identical type** before and after (finding 2).  The two
notes are documentation nits in `ATTEMPTS_SIMP.md`; neither blocks the merge and
neither touches Lean.

---

## 1. Builds — PASS

```
cd WT && bash scripts/lean-install.sh
```
→ `== OK`; the full `lake test` replayed with every registered contract reporting
`checked; standard logical axioms only`.

```
cd WT/verification
lake build NSFormalization.Section4.A02.Energy \
           NSFormalization.Section4.A02.Order \
           NSFormalization.Section4.A02.Restrict
```
→ `Build completed successfully (9882 jobs).`, **exit 0**.  `grep -n "A02"` over
the complete captured output returns **nothing**: no A02 module emits a warning
or an info line of its own.  (The warnings in the output are all pre-existing,
from `Paper3/*` and `Source/*`.)

Fresh elaboration of each of the four modules:

```
lake env lean ../formalization/NSFormalization/Section4/A02/SolutionClass.lean   exit=0, output empty
lake env lean ../formalization/NSFormalization/Section4/A02/Restrict.lean        exit=0, output empty
lake env lean ../formalization/NSFormalization/Section4/A02/Order.lean           exit=0, output empty
lake env lean ../formalization/NSFormalization/Section4/A02/Energy.lean          exit=0, output empty
```

Axiom audits:

```
lake env lean ../research/A02/axioms_u1a.lean     exit=0
```
3 / 3 lines, each exactly `[propext, Classical.choice, Quot.sound]`:
`uniformFiniteEnergy_of_sobolev`, `uniformFiniteEnergy_of_sobolevDatumPath`,
`ClassicalSolutionR.uniformFiniteEnergy`.

```
lake env lean ../research/A02/AxiomsU4U6.lean     exit=0
```
No errors or warnings of any kind, so all **9** `example`s typecheck; **25 / 25**
`#print axioms` lines print exactly `[propext, Classical.choice, Quot.sound]`
(checked by filtering the output for any token other than those three).

```
cd WT && make check      EXIT=0
```
`check_formalization_plan.py --check`, `check_contracts.py`,
`test_contract_policy.py` (13 tests, OK), `check_work_queue.py`
(`30 work items: ownership, contract registration and task cards consistent.`).

## 2. Statements unchanged — PASS (verified twice, textually and semantically)

`git diff HEAD~1 -- formalization/NSFormalization/Section4/A02/` touches three
files; `Order.lean` is not in the diff at all.

### 2a. Text level

A comment/whitespace stripper (`/- … -/` nesting, `/-! … -/`, `/-- … -/`, `--`,
string-literal aware) was run over the `HEAD~1` and `HEAD` copies of all four
modules and the results diffed:

| module | stripped-code diff |
|---|---|
| `SolutionClass.lean` | **empty** — every change is in the module docstring |
| `Order.lean` | **empty** — file untouched |
| `Restrict.lean` | exactly three things: the import list, three dropped `open`s, and the §0 block |
| `Energy.lean` | imports, `open`s, and §1–2; the three §3 theorems unchanged |

No hunk anywhere touches the text between a `theorem`/`def`/`structure` keyword
and its `:=`.

The deleted `Restrict.lean` §0 was compared against the surviving copy:

```
before/Restrict.lean stripped lines 11–56   md5 641300c9ede3a5abdd96ec8472470d18
after/SolutionClass.lean stripped lines 11–56   md5 641300c9ede3a5abdd96ec8472470d18
```

— identical, and (lines 1–10) so are the five `import`s and all five `open`s that
precede them.  The 15 restated objects are therefore declared in a *bit-for-bit
identical elaboration context* in `SolutionClass.lean` as they were in
`Restrict.lean`.

The three surviving `Energy.lean` theorems were diffed line by line
(`before:199-206 / after:89-96`, `before:235-241 / after:140-146`,
`before:252-256 / after:157-161`): byte-identical signatures; for
`uniformFiniteEnergy_of_sobolev` and `ClassicalSolutionR.uniformFiniteEnergy` the
**proof terms are byte-identical too**.

### 2b. Semantic level (the check that matters)

Byte-identical statement text is *not* by itself sufficient here, because the
lane also removed `open`s: `Restrict.lean` lost `open NSFormalization.Paper3`,
`open NSFormalization.Source.RealSobolev (FourierData)` and `open scoped
SchwartzMap`; `Energy.lean` lost `open NSFormalization.Source
NSFormalization.Source.RealSobolev`, `open …FourierPhysicalJets` and
`open scoped SchwartzMap`.  An identifier could in principle re-resolve to a
different constant and still typecheck.  This was ruled out directly.

The `HEAD~1` copies of `Restrict.lean` and `Energy.lean` were elaborated
standalone (`lake env lean` on a `/tmp` copy — their imports are all built), with
`set_option pp.fullNames true`, `set_option pp.universes true` and a `#check @`
for every declaration appended; the same suffix was elaborated against the
post-lane modules.  Both pairs of outputs are byte-identical:

```
lake env lean /tmp/rv040/chk_before_restrict.lean   exit=0, 210 lines
lake env lean /tmp/rv040/chk_after_restrict.lean    exit=0, 210 lines
diff → no output;  md5 c697fa4d3074f822304ff2b59ea221a9 (both)

lake env lean /tmp/rv040/chk_before_energy.lean     exit=0
lake env lean /tmp/rv040/chk_after_energy.lean      exit=0
diff → no output
```

Covered: the **17** `Restrict.lean` §1–3 declarations (`ClassicalSolutionR.restrict`,
`.nonempty_restrict`, `exists_restrict`, `slice_eq_of_eqOn`,
`scalarSlice_eq_of_eqOn`, `spatialDerivative_eq_of_eqOn`,
`pressureGradient_eq_of_eqOn`, `temporalDerivative_eq_of_eqOn`,
`navierStokesResidual_eq_of_eqOn`, `ClassicalSolutionR.congr`,
`exists_eq_fields_of_eqOn`, `exists_eq_fields_of_agree`,
`pressureGradient_sub_basepoint`, `contDiffOn_basepoint`,
`ClassicalSolutionR.normalizePressure`, `exists_pressure_normalization`,
`normalizePressure_gauge_invariant`), the structure signature
`@ClassicalSolutionR.mk` (all 10 fields), the **14** `#print`ed
`SolutionClass.lean` definitions (bodies, not just types), and the **3**
`Energy.lean` deliverables.  `RealVectorSobolev` in particular still resolves to
`NSFormalization.Paper3.RealVectorSobolev` on both sides.

`Order.lean` needs no such check: it is byte-identical and its transitive import
closure is unchanged (before, `Restrict.lean` imported the five modules
`Paper3.{AngularFourierDilation, RealVectorPositiveDensity,
PositiveTemporalDensity}`, `Source.RealSobolev`,
`NavierStokes.R3.ProblemStatement` directly; after, it imports `SolutionClass`,
whose import list is exactly those same five), and the declaration set it sees is
unchanged.

### 2c. Deleted declarations and their replacements

**Group A — `Restrict.lean` §0, 15 declarations.**  Nothing is deleted from the
environment: each moves to `SolutionClass.lean` under the *same name in the same
namespace* `NSFormalization.Section4.A02`.  Verified present and identical in 2b.

`SpatialField, SpaceTimeField, SpaceTimeScalar, futureTimes, forceTimeMeasure,
IsSobolevDatum, IsSobolevPath, MemHInfty, IsSolenoidal, initialClassR, MemForceR,
PressureGaugeEquivOn, ClassicalSolutionR, maximalLifespanR, RegularThrough`

Matches `ATTEMPTS_SIMP.md`'s restatement map exactly.

**Group B — `Energy.lean` §1–2, 12 declarations genuinely removed.**  Each
replacement in `ATTEMPTS_SIMP.md`'s dedupe table was checked to exist in
`formalization/NSFormalization/Section4/D01/DatumToJets.lean`; **every line
number in the table is correct**:

| deleted `A02.*` | canonical `D01.*` | verified at |
|---|---|---|
| `cyclesComponent` | `cyclesComponentOfAngular` | `DatumToJets.lean:140` |
| `norm_cyclesComponent_le` | `norm_cyclesComponentOfAngular_le` | `:153` |
| `compactRep_of_isSobolevDatum` | `compactRep_cyclesComponentOfAngular` | `:161` |
| `componentLp`, `sliceLp`, `componentLp_ae`, `sliceLp_ae` | `jetOfDatum`, `jetOfDatum_ae` at `j = 0` | `:196`, `:202` |
| `sliceConst`, `norm_sliceLp_le` | `jetDatumConst 0 0`, `norm_jetOfDatum_le` | `:218`, `:224` |
| `sliceConst_nonneg` | `jetDatumConst_pos` | `DatumToJets.lean` |
| `memLp_of_isSobolevDatum` | `memLp_of_isSobolevDatum` | `:267` |
| `l2Sq_le_of_isSobolevDatum` | `eLpNorm_le_of_isSobolevDatum` + `LpNormTools.lpNorm_two_sq_eq_l2Sq` | `:276` |
| (slice continuity) | `contDiff_slice` | `:366` |

**No dangling references.**  A `grep -rn --include='*.lean'` over `formalization`,
`verification` and `research` for each of the 12 names, excluding
`Section4/D01/`, returns matches only in prose and only for
`memLp_of_isSobolevDatum` (`Energy.lean:49` docstring; `Energy.lean:76` the
explicit `open NSFormalization.Section4.D01 (…)` list; `Energy.lean:110` the use,
which therefore resolves to D01's; `axioms_u1a.lean:10` a comment; and
`Contracts/V1/DatumLemmas.lean:34,205` / `Bindings/DatumLemmas.lean:191-192`,
which were already bound to D01) and for `sliceLp_ae` / `l2Sq_le_of_isSobolevDatum`
in that same `axioms_u1a.lean` comment.  The registered contract is indeed
authoritative for D01:

```
verification/Bindings/DatumLemmas.lean:191-192
  memLp_of_isSobolevDatum := fun _ _ _ hz hA =>
    NSFormalization.Section4.D01.memLp_of_isSobolevDatum hz hA
```

**The five defeq claims in `ATTEMPTS_SIMP.md` were independently re-run** and all
hold (`lake env lean /tmp/rv040/rfl_check.lean`, exit 0, empty output):

```
example : @A02.IsSobolevDatum   = @D01.IsSobolevDatum   := rfl
example : @A02.IsSobolevPath    = @D01.IsSobolevPath    := rfl
example : @A02.MemForceR        = @D01.MemForceR        := rfl
example :  A02.futureTimes      =  D01.futureTimes      := rfl
example :  A02.forceTimeMeasure =  D01.forceTimeMeasure := rfl
```

No import cycle is introduced: `grep -rn "^import NSFormalization.Section4.A02"
formalization/NSFormalization/Section4/D01/` is empty.  The heavier
`D01.DatumToJets` import is confined to `Energy.lean`; `Restrict.lean` and
`Order.lean` got *lighter* (`Restrict.lean` now imports one module instead of
five).

**No REJECT-level finding.**

## 3. Collision fix — PASS (both directions)

*Pre-lane state reproduced.*  The `HEAD~1` `Restrict.lean` was placed in the same
environment as `SolutionClass.lean` (its content prefixed with
`import NSFormalization.Section4.A02.SolutionClass`) — exactly the environment
that `import …A02.Order` + `import …A02.Energy` produced before this lane:

```
lake env lean /tmp/rv040/collide_before.lean
error: `NSFormalization.Section4.A02.SpatialField` has already been declared
error: `NSFormalization.Section4.A02.SpaceTimeField` has already been declared
error: `NSFormalization.Section4.A02.SpaceTimeScalar` has already been declared
error: `NSFormalization.Section4.A02.futureTimes` has already been declared
error: `NSFormalization.Section4.A02.forceTimeMeasure` has already been declared
error: `NSFormalization.Section4.A02.IsSobolevDatum` has already been declared
error: `NSFormalization.Section4.A02.IsSobolevPath` has already been declared
error: `NSFormalization.Section4.A02.MemHInfty` has already been declared
error: `NSFormalization.Section4.A02.IsSolenoidal` has already been declared
error: `NSFormalization.Section4.A02.initialClassR` has already been declared
error: `NSFormalization.Section4.A02.MemForceR` has already been declared
error: `NSFormalization.Section4.A02.PressureGaugeEquivOn` has already been declared
error: `NSFormalization.Section4.A02.ClassicalSolutionR` has already been declared
error: `NSFormalization.Section4.A02.maximalLifespanR` has already been declared
error: `NSFormalization.Section4.A02.RegularThrough` has already been declared
```

All 15 collided — the lane's claim is accurate, and this was a real latent
blocker for any downstream module needing both U1a and U6.

*Post-lane state.*  A scratch file importing both modules and exercising the U1a
and U6 theorems over the **same** `ClassicalSolutionR` value:

```lean
import NSFormalization.Section4.A02.Order
import NSFormalization.Section4.A02.Energy
open NSFormalization.Section4.A02
example (nu T b : ℝ) (a : SpatialField) (f : SpaceTimeField)
    (u : ClassicalSolutionR nu a f T) (hb0 : 0 <= b) (hbT : b < T) :
    NavierStokesR3.ProblemStatement.UniformFiniteEnergy (Set.Icc (0:ℝ) b) u.velocity :=
  u.uniformFiniteEnergy hb0 hbT
example (nu T : ℝ) (a : SpatialField) (f : SpaceTimeField)
    (u : ClassicalSolutionR nu a f T) :
    ENNReal.ofReal T <= maximalLifespanR nu a f :=
  horizon_le_lifespan u
```
→ `exit=0`, **output empty**.  Deleted.

## 4. Negative check — PASS, reproduces the record exactly

A scratch copy of the post-lane `Energy.lean` with `hbT` dropped from the proof
term of `ClassicalSolutionR.uniformFiniteEnergy` (one-line change, `diff`
confirmed to be the only difference):

```
lake env lean /tmp/rv040/neg_drop_hbT.lean
/tmp/rv040/neg_drop_hbT.lean:161:2: error: Type mismatch
  uniformFiniteEnergy_of_sobolev u.velocity_smooth u.sobolev hb0
has type
  b < T → UniformFiniteEnergy (Icc 0 b) u.velocity
but is expected to have type
  UniformFiniteEnergy (Icc 0 b) u.velocity
```

Byte-for-byte the failure `ATTEMPTS_SIMP.md` records.  `b < T` is load-bearing.
Deleted.

## 5. CI reachability — PASS

`--dry-run` exists (`build_changed_lean.py --help`: `--base-ref BASE_REF`,
`--dry-run`).

```
python3 experiments/build_changed_lean.py --base-ref origin/main --dry-run
EXIT=0
```

The "Changed Lean modules" list contains all four:
`NSFormalization.Section4.A02.Energy`, `…A02.Order`, `…A02.Restrict`,
`…A02.SolutionClass` (alongside 61 other modules).  `origin/main` was at
`4ba9f2b`.

## Notes (non-blocking, documentation only)

1. **`ATTEMPTS_SIMP.md` miscounts the `AxiomsU4U6.lean` examples.**  It records
   "all 8 `example`s typecheck"; the file has **9**
   (`AxiomsU4U6.lean:48,55,64,74,80,86,92,97,106`).  All 9 do typecheck, so the
   conclusion stands; only the count is wrong.  `AxiomsU4U6.lean` is not touched
   by this lane, so this is a transcription slip, not a regression.
2. **`ATTEMPTS_SIMP.md` §"CI reachability" records a spurious failure.**  It notes
   a trailing `FileNotFoundError: 'lake'` from `build_changed_lean.py`.  The
   script has a `--dry-run` flag that skips the build and exits 0 cleanly; the
   record would be more useful citing
   `python3 experiments/build_changed_lean.py --base-ref origin/main --dry-run`.

## Observation carried forward (pre-existing, correctly flagged by the lane)

No `verification/{Bindings,Tests,Contracts}` module imports any A02 module
(`grep -rn "^import NSFormalization.Section4.A02"` hits only the three intra-A02
imports and the two `research/A02/*.lean` audit files).  The four modules are
therefore reached by CI only through `build_changed_lean.py`, which satisfies the
tester requirement but leaves them outside the registered-contract `Tests`
closure.  `ATTEMPTS_SIMP.md` states this and flags it for the lane that registers
the A02 contract; this review confirms it and does not treat it as a defect of
lane 040.

## Commands, in order

| command | result |
|---|---|
| `bash scripts/lean-install.sh` | `== OK`; full `lake test` green |
| `lake build …A02.{Energy,Order,Restrict}` | exit 0, `9882 jobs`, zero A02 lines in output |
| `lake env lean …/A02/SolutionClass.lean` | exit 0, empty |
| `lake env lean …/A02/Restrict.lean` | exit 0, empty |
| `lake env lean …/A02/Order.lean` | exit 0, empty |
| `lake env lean …/A02/Energy.lean` | exit 0, empty |
| `lake env lean ../research/A02/axioms_u1a.lean` | exit 0; 3/3 standard axioms |
| `lake env lean ../research/A02/AxiomsU4U6.lean` | exit 0; 9 examples typecheck, 25/25 standard axioms |
| `make check` | exit 0 (4 checkers, 13 policy tests OK) |
| stripped-source diff, 4 modules | `SolutionClass`/`Order` empty; `Restrict`/`Energy` only imports, opens, deleted blocks |
| `md5sum` of §0 vs `SolutionClass` | equal (`641300c9…`) |
| `lake env lean chk_{before,after}_restrict.lean` + `diff` | identical, `c697fa4d…` — 17 + `mk` + 14 decls |
| `lake env lean chk_{before,after}_energy.lean` + `diff` | identical — 3 decls |
| `lake env lean rfl_check.lean` | exit 0, empty — 5/5 A02↔D01 defeqs hold |
| `lake env lean collide_before.lean` | 15 `already been declared` errors (pre-lane state) |
| `lake env lean collide_after.lean` | exit 0, empty (post-lane) |
| `lake env lean neg_drop_hbT.lean` | expected `Type mismatch`, matches the record |
| `build_changed_lean.py --base-ref origin/main --dry-run` | exit 0; all four A02 modules listed |
