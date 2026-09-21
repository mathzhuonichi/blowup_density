ACCEPT

## 1. What the lane claims

The worker claims a fixed scalar cutoff `cutoff : Space → ℝ`, built from a
`ContDiffBump` with plateau radius `5/2` and support radius `3`, with
`largerCube = Metric.ball 0 4` (`research/T12/REPORT_365.md:5-9`).  The claimed
API is smoothness, an open plateau and equality on the fundamental cube, range
in `[0,1]`, compact support and support control, global first/second derivative
bounds and cube vanishing, followed by the cutoff-product smoothness,
compact-support, cube-equality, and `MemHInfty` results
(`research/T12/REPORT_365.md:11-23`).  The report also claims a two-mode closure
probe (`research/T12/REPORT_365.md:25-28`) and a 23-declaration standard-axiom
audit (`research/T12/REPORT_365.md:30-42`).

These are the mathematical obligations in the lane brief.  The fixed-cube
route asks for a cutoff equal to one on `fundamentalCube`, supported in a fixed
larger neighborhood, with controlled derivatives and a compactly supported
product (`research/T12/T12_SPLIT.md:26-33`,
`research/T12/T12_SPLIT.md:58-62`).  The paper's relevant fixed-cutoff pattern
is exactly `χ ∈ C_c^∞(Ω)` equal to one near the compact set, with multiplication
by this fixed `χ` used for localization (`paper/sections/03-torus.tex:615-624`).
The tree definition of the cube really is the closed `[0,1]³`
(`formalization/NSFormalization/Section3/T13/Localization.lean:25-29`), and the
existing Urysohn construction has the same smooth/compact/range/open-plateau
clauses (`formalization/NSFormalization/Section3/T16/LocalPotential.lean:213-240`).

## 2. What is in Lean

The implementation matches the claims and the requested statements:

- `largerCube`, `cutoffBump`, and scalar `cutoff` have exactly the reported
  definitions (`formalization/NSFormalization/Section3/T12/Cutoff.lean:29-37`).
  The support ball is genuinely smaller than the radius-four open ball; this is
  a documented fixed enlargement, not an empty set or an `ENNReal.toReal`
  artifact.
- The cube norm bound is proved from all three coordinate inequalities
  (`formalization/NSFormalization/Section3/T12/Cutoff.lean:39-53`).  It feeds an
  actual open radius-`5/2` plateau and the exact theorem
  `∀ x ∈ fundamentalCube, cutoff x = 1`
  (`formalization/NSFormalization/Section3/T12/Cutoff.lean:55-71`).  Thus the
  equality is locally constant around every cube point, as U3/U5 require.
- The exact range theorem is `∀ x, cutoff x ∈ Icc (0 : ℝ) 1`, and the exact
  support/compact-support theorems are
  `tsupport cutoff ⊆ interior largerCube` and `HasCompactSupport cutoff`
  (`formalization/NSFormalization/Section3/T12/Cutoff.lean:73-90`).
- Both derivative topological supports lie in `interior largerCube`
  (`formalization/NSFormalization/Section3/T12/Cutoff.lean:92-98`).  The global
  bounds quantify over every `x`, with no added hypotheses
  (`formalization/NSFormalization/Section3/T12/Cutoff.lean:100-114`).  First and
  second Fréchet derivatives vanish on the whole fundamental cube
  (`formalization/NSFormalization/Section3/T12/Cutoff.lean:116-157`), and their
  ordinary function supports lie in the stated shell
  (`formalization/NSFormalization/Section3/T12/Cutoff.lean:158-171`).
- `cutoffMul` has the exact pointwise scalar multiplication definition.  Its
  smoothness hypothesis is used directly, compact support is unconditional,
  and cube equality has no hypothesis on the field
  (`formalization/NSFormalization/Section3/T12/Cutoff.lean:173-188`).
  `memHInfty_cutoffMul` uses its `ContDiff` hypothesis to produce all compactly
  supported jets (`formalization/NSFormalization/Section3/T12/Cutoff.lean:190-196`).
  This concludes the exact local definition of `MemHInfty`
  (`formalization/NSFormalization/Section4/A02/SolutionClass.lean:87-90`) via the
  intended conversion theorem
  (`formalization/NSFormalization/Section4/D01/SmoothDatum.lean:305-312`).
- The delivered closure probe uses the same `probeFreq`/`probeCoeff` formula as
  the earlier two-mode probe and checks both pointwise and `EqOn` cube equality
  (`research/T12/probes/cutoff_closes.lean:26-44`; compare
  `research/T12/probes/tame_product_closes.lean:40-60`).

There are no proposition inputs, unused mathematical binders, empty intervals,
or `toReal` guards.  The positive review probe proves `0 ∈ fundamentalCube`,
`cutoff 0 = 1`, and instantiates `memHInfty_cutoffMul` on the nonzero constant
field `coordinateVector 0`; the localized field remains nonzero at the origin
(`research/T12/probes/rev365_nonvacuity.lean:13-38`).  This is an explicit
non-vacuity witness for both the plateau and product statements.

## 3. Gaps and hygiene

No U2 theorem claimed by the report is missing.  U3--U6 are explicitly scoped
out (`research/T12/REPORT_365.md:44-55`) and are not disguised as missing-tree
claims.  Consequently there is no report claim of the form “lemma X is not in
the tree” to accept.  As a defensive check, whole-tree `grep -rn` in
`formalization/NSFormalization/Section4` found the intended
`memHInfty_of_contDiff_memLp` at `Section4/D01/SmoothDatum.lean:308` and
`exists_smoothL2Field_of_memHInfty` at
`Section4/D01/DatumToJets.lean:306`; it found no pre-existing `cutoffMul`.

Hygiene passes.  Keyword searches over the delivered Lean files found no
`sorry`, `admit`, `axiom` declaration, `native_decide`, or `maxHeartbeats`.
The word “axiom” occurs only in the audit-file comment
(`research/T12/axioms_cutoff.lean:3-5`).  `git diff --check` is clean.  Against
`origin/erenup/integration-section3`, all three tracked Lean files are new; no
existing Lean module was modified.  The only modified pre-existing file is the
required U2 status record `research/T12/T12_SPLIT.md`.  The imported
`Localization`, `ConstantEndpoints`, `SolutionClass`, and `SmoothDatum` files
are byte-identical between lane HEAD and the current integration ref, despite
the lane branch being 70 integration commits behind.

The substantive negative probe changes the main plateau constant from `1` to
`2` (`research/T12/probes/rev365_mutation.lean:12-14`).  It fails for the
expected mathematical reason, not because an argument was removed:

```text
../research/T12/probes/rev365_mutation.lean:14:2: error: Type mismatch
  cutoff_eq_one x hx
has type
  cutoff x = 1
but is expected to have type
  cutoff x = 2
EXIT=1
```

## 4. Commands and results

All Lean commands were run after `. scripts/lean-env.sh`, from `verification/`
where applicable, with `LEAN_NUM_THREADS=6`.

`lake build NSFormalization.Section3.T12.Cutoff` exited 0.  Its exact terminal
status was:

```text
Build completed successfully (9891 jobs).
EXIT=0
```

The build replayed linter warnings only from pre-existing modules
`Source.FiniteHilbertBochner`, `Source.RealSobolev`,
`Paper3.SpatiallyCompactTime`, `Paper3.RealPositiveDensity`,
`Paper3.RealVectorPositiveDensity`, `Source.PacketForceExtension`,
`Source.ViscosityPacket`, and `Source.PhysicalBesselSobolev`; there was no
diagnostic from `Section3/T12/Cutoff.lean` itself.

Direct elaboration of the module and delivered closure probe was exactly
silent:

```text
$ LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section3/T12/Cutoff.lean
EXIT=0
$ LEAN_NUM_THREADS=6 lake env lean ../research/T12/probes/cutoff_closes.lean
EXIT=0
```

The axioms file exited 0.  Its exact declarations/results were:

```text
largerCube: [propext, Classical.choice, Quot.sound]
cutoffBump: [propext, Classical.choice, Quot.sound]
cutoff: [propext, Classical.choice, Quot.sound]
norm_le_two_of_mem_fundamentalCube: [propext, Classical.choice, Quot.sound]
cutoff_contDiff: [propext, Classical.choice, Quot.sound]
cutoff_eq_one_on_ball: [propext, Classical.choice, Quot.sound]
cutoff_eq_one: [propext, Classical.choice, Quot.sound]
cutoff_range: [propext, Classical.choice, Quot.sound]
tsupport_cutoff: [propext, Classical.choice, Quot.sound]
hasCompactSupport_cutoff: [propext, Classical.choice, Quot.sound]
tsupport_fderiv_cutoff: [propext, Classical.choice, Quot.sound]
tsupport_iteratedFDeriv_two_cutoff: [propext, Classical.choice, Quot.sound]
support_fderiv_cutoff_subset_shell: [propext, Classical.choice, Quot.sound]
support_iteratedFDeriv_two_cutoff_subset_shell: [propext, Classical.choice, Quot.sound]
exists_cutoff_fderiv_bound: [propext, Classical.choice, Quot.sound]
exists_cutoff_iteratedFDeriv_two_bound: [propext, Classical.choice, Quot.sound]
fderiv_cutoff_eq_zero: [propext, Classical.choice, Quot.sound]
iteratedFDeriv_two_cutoff_eq_zero: [propext, Classical.choice, Quot.sound]
cutoffMul: [propext, Classical.choice, Quot.sound]
contDiff_cutoffMul: [propext, Classical.choice, Quot.sound]
hasCompactSupport_cutoffMul: [propext, Classical.choice, Quot.sound]
cutoffMul_eq_on_cube: [propext, Classical.choice, Quot.sound]
memHInfty_cutoffMul: [propext, Classical.choice, Quot.sound]
EXIT=0
```

(`lake env lean` prints fully qualified names and wraps some lists over several
lines; the list above preserves the exact 23 name/list pairs.)

`make check` exited 0.  The exact concluding output was:

```text
  "base_compatibility_checked": false,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.042s

OK
python3 experiments/check_work_queue.py
45 work items: ownership, contract registration and task cards consistent.
EXIT=0
```

`BASE_REF=origin/erenup/integration-section3 LEAN_NUM_THREADS=6
scripts/gates.sh NSFormalization.Section3.T12.Cutoff` exited 0.  Its exact gate
markers and concluding output excerpts were:

```text
== make check
== lake build NSFormalization.Section3.T12.Cutoff
Build completed successfully (9891 jobs).
== make test
[42 contract checks reported "checked; standard logical axioms only"]
== make test-mutations
extra_axiom: rejected as required
weakened_hypothesis: rejected as required
Mutation suite passed. This is an infrastructure check, not a PDE proof.
== check_contracts
  "base_compatibility_checked": true,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
== gates OK
EXIT=0
```

The separately requested base-ref check also exited 0 with exact tail:

```text
      "Tests.PacketImport"
    ]
  },
  "base_compatibility_checked": true,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
```

The reviewer positive probe was silent and exited 0.  The reviewer mutation
probe produced the expected error quoted in Part 3 and exited 1.  Finally:

```text
$ git diff --name-status origin/erenup/integration-section3...HEAD
A formalization/NSFormalization/Section3/T12/Cutoff.lean
A research/T12/ATTEMPTS_CUTOFF.md
A research/T12/REPORT_365.md
M research/T12/T12_SPLIT.md
A research/T12/axioms_cutoff.lean
A research/T12/probes/cutoff_closes.lean
$ git diff --check origin/erenup/integration-section3...HEAD
EXIT=0
```

Fixes: none.
