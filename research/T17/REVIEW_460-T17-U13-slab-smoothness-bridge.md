ACCEPT

## 1. What the lane claims

The continuation report claims the exact proposition
`correctionStatementSlab'` and a proof
`correctionStatementSlab'_holds` (`research/T17/REPORT_460b.md:5-30`), plus a
zero-extension call from an arbitrary classical solution and preservation of the
accepted counterexample to the original statement. Those claims are accurate.

- Whitespace-insensitive comparison of the continuation brief
  (`collaboration/briefs/cont_460-T17-U13-slab-smoothness-bridge.md:10-21`)
  against the Lean definition
  (`formalization/NSFormalization/Section3/T17/SlabBridge2.lean:20-31`) returns
  `statement_cmp_exit=0`. Thus the statement is token-for-token the requested
  one; in particular, it retains `IsPeriodicOn univ v` and replaces global
  smoothness by `ContDiffOn` on `Ioo 0 (place.T + δ) ×ˢ univ`.
- The proof is the theorem at
  `formalization/NSFormalization/Section3/T17/SlabBridge2.lean:192-357`.
  Every displayed hypothesis is consumed in the construction at lines 194-230.
  `place.time_pos` is a genuine field of `PlacementData`
  (`formalization/NSFormalization/Section3/T15/Scaling.lean:108-115`), so the
  open slab is nonempty when combined with `0 < δ`; `0 < r` makes the ball
  nonempty, and the constructed `D.ε₀` is positive at
  `SlabBridge2.lean:202-204`. There is no `⊤.toReal`, empty-interval trick, or
  unused named premise.
- The stronger proof-internal estimate `2ε² < min place.T δ / 2` is introduced
  only after the theorem binders (`SlabBridge2.lean:200-211`) by applying the
  existing threshold theorem at `T/2,δ/2`; the public statement at lines 20-31
  is unchanged. The underlying threshold theorem chooses a positive scale
  (`formalization/NSFormalization/Section3/T16/LocalPotential.lean:262-287`).
  This shrinks the existential witness and does not add or weaken a premise.
- The original statement has slab periodicity and closed-at-zero slab
  smoothness (`formalization/NSFormalization/Section3/T17/SlabBridge.lean:14-25`),
  whereas the continuation has global periodicity and open-slab smoothness
  (`SlabBridge2.lean:20-31`); all other tokens agree. The original negation is
  still present at `SlabBridge.lean:53-61`, and a commit-to-commit diff of that
  module is empty (`original_module_unchanged_exit=0`). This is exactly the two-
  hypothesis distinction requested by the lead. The obstruction is honest:
  `CorrectionAPI.reference_periodic` is global
  (`formalization/NSFormalization/Section3/T17/Correction.lean:97-100`).
- The paper's correction lemma requires a smooth reference only on the relevant
  fixed spacetime neighborhood and uses the `2ε²` support window
  (`paper/sections/03-torus.tex:218-284`), while the local-potential lemma uses
  the same support window (`paper/sections/03-torus.tex:176-215`). The Lean
  `localPotentialAPI` already asks only for cylinder `ContDiffOn`
  (`formalization/NSFormalization/Section3/T16/Assembly.lean:423-438`) and builds
  every potential/correction field at lines 439-478. Thus the continuation is
  the mathematics requested by the brief, not a vacuous strengthening.
- The worker's classical probe really defines
  `v_ext z := if z.1 ∈ Ico 0 S then reference.velocity z else 0`, for an
  arbitrary `reference : ClassicalSolutionT ν a g S`, and proves global
  periodicity, open-slab smoothness, and divergence before applying the main
  theorem by `exact`
  (`research/T17/probes/slab_from_classical.lean:14-52`). The canonical
  classical record supplies precisely slab smoothness, divergence, and slab
  periodicity (`formalization/NSFormalization/Section3/T10/PeriodicData.lean:265-295`).

The report's helper-declaration inventory is also accurate: the extension is at
`SlabBridge2.lean:35-83`; the four global transfer lemmas are at lines 87-161;
the two window lemmas and the rescaled-reference lemma are at lines 163-189;
and the completed 45-field assembly is at lines 267-357. The record being filled
is exactly the paper-facing 45-field `CorrectionAPI`
(`formalization/NSFormalization/Section3/T17/Correction.lean:71-281`).

## 2. What is in Lean

The implementation follows the continuation brief faithfully.

1. `exists_slab_extension` multiplies by a time-only bump with inner radius
   `m/2` and outer radius `3m/4`, proves its support lies in the open slab, and
   preserves spatial periodicity and divergence
   (`SlabBridge2.lean:35-83`). T16's gluing theorem used there is the stated
   local-to-global result (`formalization/NSFormalization/Section3/T16/Assembly.lean:60-79`).
2. The returned witness `D` is `correctionData v ...` for the original reference,
   and its `LocalPotentialAPI` is constructed directly from the original `v`
   (`SlabBridge2.lean:214-221`). The auxiliary globally smooth reference gets a
   separate `E` and API (`SlabBridge2.lean:215-230`). No unrestricted potential
   is transferred.
3. At each admissible scale the proof obtains global equality of corrections,
   forces, correction profiles, and force profiles
   (`SlabBridge2.lean:231-263`). It then rewrites every guarded field and copies
   only reference-independent data/sign fields (`SlabBridge2.lean:267-357`).
   This matches the force formula's only two reference-dependent terms
   (`formalization/NSFormalization/Section3/T17/Transport.lean:255-266`). All 22
   scale-dependent record fields have the `ε ∈ Ioc 0 D.ε₀` guard
   (`Correction.lean:105-278`); there is no unguarded-scale field missed by the
   transfer.
4. The report's cited profile route is genuine: Paper1's profile and force-
   profile constructors require global smoothness
   (`formalization/NSFormalization/Paper1/CorrectionProfile.lean:49-54,201-216`
   and
   `formalization/NSFormalization/Paper1/CorrectionForceProfile.lean:56-66,185-200`),
   which is why the auxiliary extension is needed only inside the proof.

Non-vacuity was not exhibited in `REPORT_460b.md`, so the reviewer added the
permitted probe `research/T17/probes/rev460_nonvacuity.lean`. It instantiates the
continuation theorem with the existing nonzero constant reference, positive
viscosity/radius/margin, and obtains a positive admissible `D.ε₀`
(`research/T17/probes/rev460_nonvacuity.lean:12-27`). It elaborates with exit 0
and zero output.

Hygiene is clean. Relative to `origin/erenup/integration-section3`, all eight lane
paths are additions; no existing module, contract, binding, or test is modified.
The changed Lean files and reviewer probes contain no `sorry`, `admit`, `axiom`,
or `native_decide`, and contain no `maxHeartbeats`. `git diff --check` exits 0.
The two brief files were already untracked and remain untouched.

## 3. Gaps and negative checks

There is no residual mathematical or Lean gap in the continuation.

The substantive mutation probe removes the global periodicity premise while
leaving every other binder and the conclusion unchanged
(`research/T17/probes/rev460_drop_global_periodicity.lean:12-25`). The mutated
statement is kernel-refuted by the lane's negative-time counterexample at lines
27-38. Reusing the accepted proof then fails, as expected, at lines 40-45:

```text
../research/T17/probes/rev460_drop_global_periodicity.lean:45:17: error: Application type mismatch: The argument
  hv
has type
  ContDiffOn ℝ ∞ v (Ioo 0 (place.T + δ) ×ˢ univ)
but is expected to have type
  T10.IsPeriodicOn univ v
in the application
  correctionStatementSlab'_holds ν u p f K place v r δ hν hr hr2 hδ hv
```

This is a hypothesis-level mutation of the main proposition, not an omitted
application argument; moreover, the compiled negation shows that the mutation
is false rather than merely inconvenient for the existing proof.

For the historical first report's missing-bridge discussion, the mandated whole-
tree search was run:

```text
$ grep -rn -E "localPotentialAPI_slab|correctionStatementSlab_holds|extended-reference|slab-relative reference" formalization/NSFormalization/Section4
grep_exit=1
```

No such lemma exists in Section4. This does not create a continuation gap:
global periodicity is deliberately retained, and the already-existing T16
`localPotentialAPI` has the needed local smoothness signature. The checkout does
still lack the lead's G5 addendum in `research/T17/SPEC_ISSUES.md`; the user-
supplied lead ruling is authoritative for this review, so this record lag is not
a lane defect.

## 4. Commands and results

All Lean commands sourced `scripts/lean-env.sh`, used `LEAN_NUM_THREADS=6`, and
ran Lake only from `verification/`.

### Statement and hygiene checks

```text
$ cmp -s <(sed -n '10,20p' collaboration/briefs/cont_460-T17-U13-slab-smoothness-bridge.md | tr -d '[:space:]') <(sed -n '20,31p' formalization/NSFormalization/Section3/T17/SlabBridge2.lean | tr -d '[:space:]')
statement_cmp_exit=0
$ git diff --exit-code 09e4503e..aee9ec81 -- formalization/NSFormalization/Section3/T17/SlabBridge.lean
original_module_unchanged_exit=0
```

```text
$ git diff --name-status origin/erenup/integration-section3...HEAD
A formalization/NSFormalization/Section3/T17/SlabBridge.lean
A formalization/NSFormalization/Section3/T17/SlabBridge2.lean
A research/T17/ATTEMPTS_U13.md
A research/T17/REPORT_460.md
A research/T17/REPORT_460b.md
A research/T17/T17_SPLIT_U13.md
A research/T17/axioms_u13.lean
A research/T17/probes/slab_from_classical.lean
```

The forbidden-token and `maxHeartbeats` searches both produced zero output;
`git diff --check origin/erenup/integration-section3...HEAD` also produced zero
output, all with exit 0. The same path diff contains no `verification/` entry,
so the conditional `scripts/gates.sh` and
`check_contracts.py --base-ref origin/erenup/integration-section3` gates are not
applicable.

### Build

`lake build NSFormalization.Section3.T17.Assembly` exited 0 with 10032 jobs.
The required combined module build exited 0 with 10034 jobs. It had no output
from either slab module; Lake replayed pre-existing dependency diagnostics.
Exact first and last excerpts (each at most 40 lines; middle omitted under the
raw-output rule):

```text
⚠ [8778/9200] Replayed NSFormalization.Source.FiniteHilbertBochner
warning: NSFormalization/Source/FiniteHilbertBochner.lean:24:19: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
warning: NSFormalization/Source/FiniteHilbertBochner.lean:23:37: This simp argument is unused:
  PiLp.single_apply

Hint: Omit it from the simp argument list.
  [apply] simp [h]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: NSFormalization/Source/FiniteHilbertBochner.lean:39:23: This simp argument is unused:
  PiLp.single_apply

Hint: Omit it from the simp argument list.
  [apply] simp [insert, coord]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
⚠ [9820/10034] Replayed NSFormalization.Paper1.PeriodicSobolevHilbert
info: NSFormalization/Paper1/PeriodicSobolevHilbert.lean:60:55: Try this:
... middle omitted ...
warning: NSFormalization/Paper1/PeriodicLocalLifespan.lean:325:24: Variable name `V` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _V

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: NSFormalization/Paper1/PeriodicLocalLifespan.lean:335:24: Variable name `V` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _V

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: NSFormalization/Paper1/PeriodicLocalLifespan.lean:400:26: `dif_pos` has been deprecated: Use `dite_eq_left` instead
warning: NSFormalization/Paper1/PeriodicLocalLifespan.lean:587:13: Variable name `hS` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hS

Note: This linter can be disabled with `set_option linter.unusedVariables false`
Build completed successfully (10034 jobs).
```

### Direct elaboration and probes

Each of these exited 0 with exactly zero output:

```text
lake env lean ../formalization/NSFormalization/Section3/T17/SlabBridge.lean
lake env lean ../formalization/NSFormalization/Section3/T17/SlabBridge2.lean
lake env lean ../research/T17/probes/slab_from_classical.lean
lake env lean ../research/T17/probes/rev460_nonvacuity.lean
```

The negative mutation command exited 1 with the exact expected error quoted in
Part 3.

### Axioms

`lake env lean ../research/T17/axioms_u13.lean` exited 0 with exact output:

```text
'NSFormalization.Section3.T17.correctionStatementSlab' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T17.slabCounterexample' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T17.slabCounterexample_periodic' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T17.slabCounterexample_smooth' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T17.slabCounterexample_divergence' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T17.slabCounterexample_not_periodic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T17.not_correctionStatementSlab' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T17.correctionStatementSlab'' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T17.exists_slab_extension' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T17.physicalCorrection_eq_of_slices' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T17.correctionProfile_eq_of_slices' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T17.correctionForce_eq_of_slices' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T17.forceProfile_eq_of_slices' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T17.chart_time_mem_window' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T17.rescaledReference_eqOn_of_slices' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T17.temporalCutoff_time_mem_window' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T17.correctionStatementSlab'_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Every declaration has exactly `[propext, Classical.choice, Quot.sound]`.

### `make check`

`LEAN_NUM_THREADS=6 make check` exited 0. Exact first and last excerpts (each at
most 40 lines; middle omitted under the raw-output rule):

```text
python3 experiments/check_formalization_plan.py --check
{
  "task_count": 45,
  "source_counts": {
    "formalization": 691,
    "vendor/NavierStokesAndEuler": 2486,
    "vendor/HeliCorgi": 129
  },
  "source_manifest_entries": 2975,
  "missing_copied_imports": [],
  "citation_interfaces_reachable": [],
  "tokens_in_copied_umbrella_closure": [
    {
      "module": "NSFormalization.Paper1.BoundaryCorollary",
      "path": "formalization/NSFormalization/Paper1/BoundaryCorollary.lean",
      "line": 90,
      "token": "sorry"
    }
  ],
... middle omitted ...
      "NavierStokes.WaveInteractionBounds",
      "NavierStokes.WaveStateRegularity",
      "NavierStokes.WeightedClasses",
      "NavierStokes.WeightedODEJets",
      "NavierStokes.WeightedQuotients",
      "NavierStokes.WeightedRadialPrimitive",
      "NavierStokes.ZerothStressIdentity",
      "TestSupport.Axioms",
      "Tests.Correction3"
    ]
  },
  "base_compatibility_checked": false,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.046s

OK
python3 experiments/check_work_queue.py
45 work items: ownership, contract registration and task cards consistent.
```

The copied-source `BoundaryCorollary` diagnostic and source-hash diagnostic are
pre-existing informational output; `make check` passed. Lane-local hygiene was
checked separately above.

Fixes: none.
