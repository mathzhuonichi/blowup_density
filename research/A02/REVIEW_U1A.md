# Review — lane 033, task A02, unit U1a

Reviewer: independent lane-033 reviewer (opus), read/build only.
Worktree: `.claude/worktrees/033-A02-energy-u1a`, commit `f27769c`, base
`erenup/integration` at `2554554`.

## Verdict: **ACCEPT-WITH-NOTES**

The unit is delivered, complete and honest.  The Lean builds clean with no
`sorry`, no added axiom and no linter output from either new file; the target
theorem is *exactly* the unit's statement and it plugs into
`classical_uniqueness_on_Icc`'s energy slot (verified by elaborating the
application, not by eye); the restatement of the D01 solution class is
byte-identical to lane 032's §0 and token-identical to `Contracts/V1/Data.lean`;
the two spot-checked claims of `ATTEMPTS_U1A.md` are true, and so is every other
citation I sampled (17/17).  The three notes below are actions for the **lead at
merge**, not defects in this lane; none of them requires a change here.

---

## Findings

### 1. (info — merge action, blocking for the lead, not for this lane) `SolutionClass.lean` and lane 032's `Restrict.lean` §0 declare the same names in the same namespace

* Declarations: `NSFormalization.Section4.A02.{SpatialField, SpaceTimeField,
  SpaceTimeScalar, futureTimes, forceTimeMeasure, IsSobolevDatum, IsSobolevPath,
  MemHInfty, IsSolenoidal, initialClassR, MemForceR, PressureGaugeEquivOn,
  ClassicalSolutionR, maximalLifespanR, RegularThrough}`.
* Situation: this lane's `Section4/A02/SolutionClass.lean:47-133` is
  byte-identical to `Section4/A02/Restrict.lean:78-164` on
  `erenup/032-A02-restrict-order` (verified by `diff`, md5
  `35ff39cd3aaa39f8736bb4c55bf94ee3` on both extracts).  That is what the lead
  asked for, and it is correct as delivered: nothing currently imports both
  modules, so neither branch breaks on its own, and `build_changed_lean.py`
  compiles each separately, so **CI would not catch the collision either**.
* Why it still matters: after both lanes land, any module importing both gets
  fifteen duplicate declarations, and `A02.ClassicalSolutionR` would exist as
  two distinct inductive types depending on the import path.
* Fix (lead, at merge of 032): delete lines 78-164 of 032's `Restrict.lean` and
  add `import NSFormalization.Section4.A02.SolutionClass`.  `ATTEMPTS_U1A.md:111-120`
  already states this plan; it is recorded here so it is not lost.

### 2. (info — post-rebase cleanup) Sections 1-2 of `Energy.lean` duplicate machinery merged to `erenup/integration` as `Section4/D01/DatumToJets.lean`

* Declarations: `A02.{cyclesComponent, norm_cyclesComponent_le,
  compactRep_of_isSobolevDatum, componentLp, componentLp_ae, sliceLp, sliceLp_ae,
  memLp_of_isSobolevDatum, l2Sq_le_of_isSobolevDatum}` —
  `Energy.lean:89-188`, about 100 lines.
* This is not a defect: `DatumToJets.lean` did not exist at the lane's base
  `2554554`, and the lane could not have built against it.  I verified all seven
  overlap rows of `ATTEMPTS_U1A.md:182-190` against
  `worktrees/000-integration` head `16ae258` — every cited declaration exists at
  exactly the cited line (see commands below).
* Fix (optional, at rebase): follow the lane's own recipe,
  `ATTEMPTS_U1A.md:192-210`.  Note the hypothesis strength difference it flags is
  real — `D01.memLp_of_isSobolevDatum` (`DatumToJets.lean:267`) wants
  `ContDiff ℝ ∞ z` where the local version wants only `Continuous z`; both are
  available from `velocity_smooth` via `D01.contDiff_slice` (`:366`).

### 3. (info — known layering caveat, already documented) the unit is proved about the *restated* `ClassicalSolutionR`, not the contract's

* `NSFormalization` is a dependency of the `Contracts` library, so
  `Contracts.V1.Data.ClassicalSolutionR` cannot be imported into
  `formalization/`.  The two structures are distinct inductive types; no `rfl`
  bridge exists for the structure itself, as `SolutionClass.lean:23-27` says.
* I did **not** take this on trust.  I constructed the field-by-field bridge and
  elaborated it: every one of the ten fields transfers by bare projection, with
  no transport, and the unit's conclusion then holds verbatim for the contract's
  structure.  The check file and its exit code are in the commands section.  So
  the restatement is faithful in the strongest available sense, and a
  `verification/Bindings` module will discharge the contract statement by
  `exact`.

### No defects found

Specifically checked and clean: no `sorry`/`admit`/`native_decide`/`axiom` token
anywhere in the two new files (not even in comments); the axiom audit prints
`[propext, Classical.choice, Quot.sound]` for all six declarations; the proof
uses exactly the two structure fields it claims (`velocity_smooth`, `sobolev`)
and no other; `hb0 : 0 ≤ b` is genuinely load-bearing (it is what makes
`0 ∈ Icc 0 b` at `Energy.lean:211`, hence `0 ≤ C`); the commit adds 4 files and
touches nothing outside `Section4/A02` and `research/A02`.

---

## Check 2 — is the theorem the unit's target?

`Energy.lean:252-256` elaborates to (`#check`, `pp.fullNames`):

```
@NSFormalization.Section4.A02.ClassicalSolutionR.uniformFiniteEnergy : ∀ {ν T : ℝ}
  {a : NSFormalization.Section4.A02.SpatialField} {f : NSFormalization.Section4.A02.SpaceTimeField}
  (u : NSFormalization.Section4.A02.ClassicalSolutionR ν a f T) {b : ℝ},
  0 ≤ b → b < T → NavierStokesR3.ProblemStatement.UniformFiniteEnergy (Set.Icc 0 b) u.velocity
```

* This is the target of the unit table (`research/A02/COMPARISON.md:163`)
  verbatim, with `T' = b`.
* `UniformFiniteEnergy` is `NavierStokesR3.ProblemStatement.UniformFiniteEnergy`,
  `vendor/NavierStokesAndEuler/NavierStokes/R3/ProblemStatement.lean:81-83`.  It
  is the **only** definition of that name in the tree (grep over `vendor/`,
  `formalization/`, `verification/` finds one `def`), so the whole-namespace
  `open NavierStokes.ProblemStatement` at `Energy.lean:80` shadows nothing:
  `NavierStokes/ProblemStatement.lean` contains no `UniformFiniteEnergy`,
  `kineticEnergy` or `SquareIntegrableAtTime`.
* `ClassicalSolutionR` resolves to the `SolutionClass.lean:100` restatement.
* Downstream fit: `classical_uniqueness_on_Icc`
  (`Source/BoundedViscosityUniqueness.lean:23`) takes
  `heu : UniformFiniteEnergy (Icc 0 T) u` at `:29` and `hev` at `:30`, with its
  own horizon variable `T`.  I elaborated the full application at `T := b`,
  filling `heu`/`hev` with `u.uniformFiniteEnergy hb0 hbT` — it typechecks.  The
  shapes match: the unit's `Icc 0 b` with `b < T` is exactly what the uniqueness
  theorem consumes on a compact subinterval.

## Check 3 — restatement fidelity

* `diff` of `Restrict.lean:78-164` (lane 032, read-only) against
  `SolutionClass.lean:47-133`: **empty**, identical md5.
* Token-for-token against `verification/Contracts/V1/Data.lean` for all fifteen
  restated objects (docstrings stripped, whitespace normalized): **all match**.
  `ClassicalSolutionR` is additionally byte-identical: `Data.lean:624-648` vs
  `SolutionClass.lean:100-124`, `diff` empty — same ten fields in the same
  order, same docstrings, `Ico` in `velocity_smooth`/`pressure_smooth`/
  `divergence`/`sobolev`/`pressure_gradient` and `Ioo` in `momentum`, same binder
  names (`ν a f T`, `m`, `G`, `t`, `x`, `i`, `ψ`).
* Every `Data.lean:NNN` line citation in `SolutionClass.lean`'s docstrings is
  correct (99, 104, 108, 113, 118, 160, 174, 495, 504, 509, 544, 589, 624-648,
  657, 664 — all verified).

## Check 4 — honesty of `ATTEMPTS_U1A.md`

Spot-check A — **D01 overlap table (`:182-190`)**: `DatumToJets.lean` exists on
`erenup/integration` (`worktrees/000-integration`, head `16ae258`).  All seven
cited declarations are at the cited lines, exactly as the table says:
`cyclesComponentOfAngular:140`, `norm_cyclesComponentOfAngular_le:153`,
`compactRep_cyclesComponentOfAngular:161`, `jetOfDatum:196`, `jetOfDatum_ae:202`,
`memLp_of_isSobolevDatum:267`, `eLpNorm_le_of_isSobolevDatum:276`,
`contDiff_slice:366`.  **True.**

Spot-check B — **"D01 unit L1 is not used" (`:143-151`)**: the unit table at
`COMPARISON.md:163` does list "D01 unit **L1** (datum uniqueness)" as a
dependency of U1a, and `Energy.lean` contains no reference to `sobolevENorm`, to
any datum-uniqueness lemma, or to any D01 module at all (its five imports are
`Section4.A02.SolutionClass`, `Source.FourierPhysicalJets`,
`Paper3.AngularTameProduct`, `NavierStokes.R3.ComparisonFiniteEnergy`,
`NavierStokes.R3.LpNormTools`).  **True**, and the positive finding stands: U1a's
dependency list can be shortened.

Further sampling (not required, done anyway): all ten declaration citations of
the route table `:75-84` are exact; `ls formalization/.lake` is `build` as
claimed `:218`; the claim at `:99-101` that the base had no local
`ClassicalSolutionR` is confirmed (`git grep` at `2554554` finds only the two
docstring mentions in `Section4/D01/SmoothDatum.lean:42,384`).  The two recorded
build failures (concurrent-`lake` corruption, `positivity` on an opaque `def`)
are consistent with the delivered code.

---

## Commands and results

All `lake` invocations from `WT/verification`, `LEAN_NUM_THREADS=6`, no `-j`,
one `lake` process at a time.

| # | command | result |
|---|---|---|
| 1 | `cd WT && bash scripts/lean-install.sh` | **exit 0**, ends `== OK`; its `lake test` reported `checked; standard logical axioms only` for every registered contract |
| 2 | `lake build NSFormalization.Section4.A02.Energy` | **exit 0**, `Build completed successfully (8858 jobs)`; `grep -i 'sorry\|declaration uses\|admit\|error'` over the full log: **no match**; no line mentioning `A02` at all (no warning from either new module) |
| 3 | `lake env lean ../research/A02/axioms_u1a.lean` | **exit 0**; all six declarations (`uniformFiniteEnergy_of_sobolev`, `uniformFiniteEnergy_of_sobolevDatumPath`, `memLp_of_isSobolevDatum`, `sliceLp_ae`, `l2Sq_le_of_isSobolevDatum`, `ClassicalSolutionR.uniformFiniteEnergy`) → `depends on axioms: [propext, Classical.choice, Quot.sound]` |
| 4 | `grep -n 'sorry\|admit\|native_decide\|axiom' formalization/NSFormalization/Section4/A02/{Energy,SolutionClass}.lean` | **exit 1**, no output — not even inside comments |
| 5 | `make check` | **exit 0**: `check_formalization_plan --check`, `check_contracts`, `test_contract_policy` (13 tests, OK), `check_work_queue` (`30 work items: ownership, contract registration and task cards consistent.`) |
| 6 | `lake env lean ../formalization/NSFormalization/Section4/A02/SolutionClass.lean` | **exit 0**, **no output** (fresh elaboration, zero warnings) |
| 7 | `lake env lean ../formalization/NSFormalization/Section4/A02/Energy.lean` | **exit 0**, **no output** (fresh elaboration, zero warnings) |
| 8 | `lake env lean /tmp/033_check_target.lean` — `#check` of the target + an `example` applying it into `classical_uniqueness_on_Icc`'s `heu`/`hev` slots at `T := b` | **exit 0**; printed signature reproduced in Check 2 above |
| 9 | `lake env lean /tmp/033_bridge.lean` — field-by-field `def bridge : Data.ClassicalSolutionR → A02.ClassicalSolutionR` (all ten fields by bare projection) plus an `example` deriving `UniformFiniteEnergy (Icc 0 b) u.velocity` for a **contract** solution | **exit 0** |
| 10 | `diff <(sed -n '78,164p' <032>/Restrict.lean) <(sed -n '47,133p' SolutionClass.lean)` | **empty**; `md5sum` equal on both extracts |
| 11 | `diff <(sed -n '624,648p' verification/Contracts/V1/Data.lean) <(sed -n '100,124p' SolutionClass.lean)` | **empty** |
| 12 | token comparison of all 15 restated objects against `Data.lean` (python, docstrings stripped) | `ALL_MATCH` |
| 13 | `grep -rn UniformFiniteEnergy --include=*.lean vendor/ formalization/ verification/` filtered to definitions | one hit: `vendor/NavierStokesAndEuler/NavierStokes/R3/ProblemStatement.lean:81` |
| 14 | `python3 experiments/build_changed_lean.py --base-ref 2554554 --dry-run` | `Changed Lean modules: NSFormalization.Section4.A02.Energy, NSFormalization.Section4.A02.SolutionClass` — CI's changed-module step does cover both new files (they are not in the default target closure: `formalization/NSFormalization.lean` imports no `Section4` module) |
| 15 | `git show --stat f27769c` | 4 files, 655 insertions, 0 deletions; nothing outside `Section4/A02` and `research/A02` |

Files 8 and 9 were written to `/tmp`, outside the worktree; nothing in the
worktree was modified except this review file.
