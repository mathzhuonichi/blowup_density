REJECT

## 1. What the lane claims

The worker claims all five U8 fields, for every `data : InsertionData` and
`ε ∈ Ioc 0 (ε₀ data)`: full-horizon `solution`, `maximal`, exact `lifespan`,
pointwise `blowup`, and essential-supremum `blowup_limsup`
(`research/T18/REPORT_436.md:7-15`).  Those are exactly the five Spec fields at
`research/T18/Spec.lean:1796-1828`:

```lean
solution : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
  ∃ w : ClassicalSolutionT ν a (force ε) place.T,
    w.velocity = velocity ε ∧ w.pressure = pressure ε
maximal : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
  IsMaximalPeriodicSolution ν a (force ε) (velocity ε) (pressure ε)
lifespan : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
  maximalLifespanT ν a (force ε) = ENNReal.ofReal place.T
blowup : ∀ ε ∈ Ioc (0 : ℝ) ε₀, SpeedUnboundedAt place.T (velocity ε)
blowup_limsup : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
  MaximalPartial.limsupLeft place.T
    (fun t => MaximalPartial.speedENorm (fun x => velocity ε (t, x))) = ⊤
```

Statement fidelity is good.  The canonical declarations have these exact
statements at `formalization/NSFormalization/Section3/T18/Lifespan.lean:167-170`,
`:177-178`, `:207-213`, `:300-303`, and `:338-349`.  The contract-vocabulary
conformance record repeats the same fields at
`research/T18/probes/u8_closes.lean:237-254`, and its constructor discharges all
five at `:261-284`.  The paper asks for `T_max = T` and unbounded maximum norm at
`paper/sections/03-torus.tex:287-295`; its proof explicitly says that uniqueness
gives the maximal solution below `T` and that unbounded maximum norm excludes an
extension past `T` at `paper/sections/03-torus.tex:332-339`.  Thus the lane's
direct uniqueness-plus-boundedness route is faithful even though it is shorter
than the continuation-API route proposed in the brief.

No interval or extended-real vacuity was introduced.  `ClassicalSolutionT`
requires `0 < T` (`verification/Contracts/V1/TorusLocalTheory.lean:144-195`),
`InsertionData` carries the positive placement horizon and positive common scale
through its records (`formalization/NSFormalization/Section3/T18/Insertion.lean:37-57,98-103`),
and the review probe gives the concrete guarded scale `ε₀ data / 2`
(`research/T18/probes/rev436_nonvacuity.lean:10-13`).  A fully concrete
`InsertionData` witness is still unavailable because the T15/T17 assembly
witnesses are outside U8; the worker says so explicitly at
`research/T18/REPORT_436.md:38-40`, as the brief permits.

## 2. What is in Lean

`insertedSolution` fills every field of the full-horizon solution directly from
U3/U4/U6 and the torus datum/pressure lemmas
(`formalization/NSFormalization/Section3/T18/Lifespan.lean:109-164`).  Its
Sobolev path uses `exists_periodicDatum_smooth`
(`formalization/NSFormalization/Section3/T11/CriterionBridge.lean:27-54`) and
`continuousOn_periodicDatum_path_of_slab`
(`formalization/NSFormalization/Section3/T11/Maximal.lean:151-173`), so the
reported removal of the R3 cutoff path is honest.

`blowup` transfers the scaling witness only after proving the packet is nonzero,
locating its point in the topological support, and applying the correction
cancellation (`Lifespan.lean:177-203`).  `blowup_limsup` invokes the R42
pointwise-to-essential-supremum theorem whose continuity and positive-measure
argument is at `formalization/NSFormalization/Section4/R42/BlowupEssSup.lean:52-124`.

For the upper lifespan bound, a longer solution is bounded on
`Icc 0 T × fundamentalCube` and periodicity transports the bound to all space
(`Lifespan.lean:217-268`); `velocity_unique` then contradicts pointwise blow-up
(`Lifespan.lean:270-297`).  The cited lattice facts are the actual closed cube
and lattice vector at `Section3/T13/Localization.lean:25-38`, cube closedness at
`Section3/T13/ConstantEndpoints.lean:240-247`, and integer-period transport at
`Section3/T13/TorusIdentity.lean:882-888`.  The lower bound is the realized
horizon term in the defining supremum (`Lifespan.lean:300-303` and
`Section3/T11/ExtendsBeyond.lean:67-75`).  `maximal` then realizes every positive
shorter horizon using `insertedSolutionOn` (`Lifespan.lean:307-349`), exactly
matching `IsMaximalPeriodicSolution` at
`verification/Contracts/V1/TorusLocalTheory.lean:303-307`.

Hygiene is clean in the lane Lean delta: no `sorry`, `admit`, declaration
`axiom`, `native_decide`, or `set_option maxHeartbeats` occurs.  All 21 audited
declarations use exactly `[propext, Classical.choice, Quot.sound]`.  Commit
`26af11b8` adds the sole formalization module rather than modifying an existing
one; its exact name-status output is:

```text
A	formalization/NSFormalization/Section3/T18/Lifespan.lean
M	logs/LESSONS.md
A	research/T18/ATTEMPTS_U8.md
M	research/T18/T18_SPLIT.md
A	research/T18/axioms_u8.lean
A	research/T18/probes/u8_closes.lean
```

The required current-base triple-dot check warns that the histories have
multiple merge bases and lists 52 paths, including earlier-added verification
files.  It lists no modified pre-existing formalization `.lean` file.  The lane
commit itself touches no `verification/` path, but I nevertheless ran the two
verification gates because the mandated current-base diff includes such paths.

The substantive negative mutation changes the exact lifespan from `T` to
`T + 1` (`research/T18/probes/rev436_negative.lean:9-13`) and fails by a type
mismatch, not by dropping an argument.  The non-vacuity probe also instantiates
the compact-periodic boundedness lemma with the zero field on the nonempty
window `[0,1]` inside `[0,2)` (`rev436_nonvacuity.lean:15-26`).

## 3. Gaps and verdict reason

There is no mathematical U8 gap found.

The two “not in the tree” statements in `REPORT_436.md:41-43` were checked
before acceptance.  The whole Section4 search finds only the R3 lemma, notably
`formalization/NSFormalization/Section4/A02/Patch.lean:125-170`; the same search
under all of Section3 finds no `lifespan_le_of_unbounded`.  Searching all of
Section4 for a `periodicLpENorm ⊤`/`speedENorm` bridge returns nothing.  The
tree-wide `periodicLpENorm ⊤` hits are only
`Section3/T12/FourierEmbeddings.lean:388,464,472` and the contract/test copies
reported by the worker, so both gap descriptions are accurate.

The rejection is operational and blocking: the required compatibility gate
against the current `origin/erenup/integration-section3` fails.  The lane is at
`9ad0327e`, the current base ref is `5bb24052`, and the base contains stable
`verification/Contracts/V1/ConservativeForcing.lean` from `8bb95ef8`, while the
lane snapshot lacks that file.  Consequently both the standalone checker and
`scripts/gates.sh` reproduce:

```text
AssertionError: Removed stable specification: verification/Contracts/V1/ConservativeForcing.lean
```

Required fix: synchronize the lane with the current integration base while
preserving the reviewed U8 delta, then rerun both commands below to exit 0.  No
Lean proof or statement change is requested.

## 4. Commands and results

All Lake commands ran from `verification/` after `. ../scripts/lean-env.sh`, with
`LEAN_NUM_THREADS=6`.

1. `lake build NSFormalization.Section3.T18.Lifespan` — exit 0.  It replayed
   pre-existing dependency warnings but emitted no warning from the target
   module.  The exact filtered/final output was:

```text
⚠ [10177/10567] Replayed NSFormalization.Paper1.PeriodicLocalLifespan
warning: NSFormalization/Paper1/PeriodicLocalLifespan.lean:100:23: Variable name `U` is not explicitly referenced.
warning: NSFormalization/Paper1/PeriodicLocalLifespan.lean:325:24: Variable name `V` is not explicitly referenced.
warning: NSFormalization/Paper1/PeriodicLocalLifespan.lean:335:24: Variable name `V` is not explicitly referenced.
warning: NSFormalization/Paper1/PeriodicLocalLifespan.lean:400:26: `dif_pos` has been deprecated: Use `dite_eq_left` instead
warning: NSFormalization/Paper1/PeriodicLocalLifespan.lean:587:13: Variable name `hS` is not explicitly referenced.
Build completed successfully (10611 jobs).
```

2. `lake env lean ../formalization/NSFormalization/Section3/T18/Lifespan.lean`
   — exit 0, exact output: empty.

3. `lake env lean ../research/T18/probes/u8_closes.lean` — exit 0, exact
   output: empty.

4. `lake env lean ../research/T18/axioms_u8.lean` — exit 0.  Exact axiom sets
   (line wrapping aside) were:

```text
'NSFormalization.Section3.T18.rawPressure' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T18.pressure_eq_normalize' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T18.reference_pressureSlice_integrable' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T18.rawPressureSlice_integrable' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T18.pressureGaugeT_normalize' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T18.isPeriodicOn_normalizePressureT' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T18.pressure_periodic' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T18.pressure_gauge' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T18.sobolev_path' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T18.pressure_gradient_memLp' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T18.insertedSolution' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T18.solution' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T18.blowup' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T18.blowup_limsup' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T18.exists_sub_latticeVector_mem_fundamentalCube' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T18.isCompact_fundamentalCube' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T18.exists_speed_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T18.lifespan_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T18.lifespan' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T18.insertedSolutionOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T18.maximal' depends on axioms: [propext, Classical.choice, Quot.sound]
```

5. `lake env lean ../research/T18/probes/rev436_nonvacuity.lean` — exit 0,
   exact output: empty.

6. `lake env lean ../research/T18/probes/rev436_negative.lean` — expected exit
   1, exact output:

```text
../research/T18/probes/rev436_negative.lean:13:2: error: Type mismatch
  lifespan data ε hε
has type
  maximalLifespanT data.ν data.a (force data ε) = ENNReal.ofReal data.place.T
but is expected to have type
  maximalLifespanT data.ν data.a (force data ε) = ENNReal.ofReal (data.place.T + 1)
```

7. `make check` — exit 0.  Exact tail:

```text
      "NavierStokes.WeightedQuotients",
      "NavierStokes.WeightedRadialPrimitive",
      "NavierStokes.ZerothStressIdentity",
      "TestSupport.Axioms",
      "Tests.AffineVariation"
    ]
  },
  "base_compatibility_checked": false,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.048s

OK
python3 experiments/check_work_queue.py
45 work items: ownership, contract registration and task cards consistent.
```

8. `BASE_REF=origin/erenup/integration-section3 LEAN_NUM_THREADS=6
   scripts/gates.sh NSFormalization.Section3.T18.Lifespan` — exit 1 after the
   module build, contract tests, and mutation tests passed.  Exact final output:

```text
extra_axiom: rejected as required
weakened_hypothesis: rejected as required
Mutation suite passed. This is an infrastructure check, not a PDE proof.
== check_contracts
Traceback (most recent call last):
  File "/data_8T/ping/blowup_density/.claude/worktrees/436-T18-U8-lifespan/experiments/check_contracts.py", line 153, in <module>
    print(json.dumps(check(base=args.base_ref), indent=2))
                     ^^^^^^^^^^^^^^^^^^^^^^^^^
  File "/data_8T/ping/blowup_density/.claude/worktrees/436-T18-U8-lifespan/experiments/check_contracts.py", line 143, in check
    check_compatibility(root, base, contracts)
  File "/data_8T/ping/blowup_density/.claude/worktrees/436-T18-U8-lifespan/experiments/check_contracts.py", line 62, in check_compatibility
    assert (root / path).is_file(), f'Removed stable specification: {path}'
           ^^^^^^^^^^^^^^^^^^^^^^^
AssertionError: Removed stable specification: verification/Contracts/V1/ConservativeForcing.lean
```

9. `python3 experiments/check_contracts.py --base-ref
   origin/erenup/integration-section3` — exit 1 with the same traceback and
   final `AssertionError` above.

10. Hygiene `rg` over the lane module, worker probes, axiom file, and reviewer
    probes for `sorry|admit|native_decide|^[[:space:]]*axiom|set_option
    maxHeartbeats` — exit 1/no matches.  `git diff --check` — exit 0/no output.

Fixes required:

1. Synchronize with current `origin/erenup/integration-section3`, retaining its
   stable `ConservativeForcing` contract/binding/test and manifest entry.
2. Rerun the standalone compatibility checker and `scripts/gates.sh`; both must
   exit 0 before acceptance.
