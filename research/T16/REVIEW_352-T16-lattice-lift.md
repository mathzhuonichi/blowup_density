REJECT

## What the lane claims

`research/T16/REPORT_352.md:5-24` claims that the lattice lift is the genuine
sum in the brief, definitionally equal to
`NavierStokes.PeriodicLocalization.periodize`, and that it transports every
canonical correction field.  The report correctly says “seven”: the canonical
`LocalPotentialAPI` has exactly the seven fields `correction_formula` through
`correction_cancels` at `formalization/NSFormalization/Section3/T16/LocalPotential.lean:140-162`.
The brief's “eight” is a counting error, not a missing eighth Lean field.

## What is in Lean

The lift definition and defeq bridge are exact:
`latticeLift` is the stated `tsum` at
`formalization/NSFormalization/Section3/T16/LatticeLift.lean:54-58`, and
`latticeLift_eq_periodize` is `rfl` at
`formalization/NSFormalization/Section3/T16/LatticeLift.lean:70-74`.  The
support-to-cube and ball coordinate lemmas are stated at
`formalization/NSFormalization/Section3/T16/LatticeLift.lean:78-109`;
smoothness and periodicity at
`formalization/NSFormalization/Section3/T16/LatticeLift.lean:113-127`; ball
locality (`tsum_eq_single 0`) at
`formalization/NSFormalization/Section3/T16/LatticeLift.lean:129-161`;
divergence transport and finite-sum lemmas at
`formalization/NSFormalization/Section3/T16/LatticeLift.lean:165-240`; time
and slice support at
`formalization/NSFormalization/Section3/T16/LatticeLift.lean:244-318`; and
integer-shift/cancellation transport at
`formalization/NSFormalization/Section3/T16/LatticeLift.lean:322-369`.

The conjunction returned by `correction_fields_of_chart` has the seven exact
canonical bodies at
`formalization/NSFormalization/Section3/T16/LatticeLift.lean:400-415`, and the probe copies those seven bodies
verbatim at `research/T16/probes/lattice_lift_closes.lean:25-91`.  The bump
non-vacuity check is at `research/T16/probes/lattice_lift_closes.lean:94-120`
and is substantive: it proves the lift is
nonzero at the origin and periodic.  The axiom file lists all 19 declarations
at `research/T16/axioms_lattice_lift.lean:7-26`.

## Gaps

1. **Blocking statement-fidelity gap (correction_cancels).**
   `latticeLift_cancels` requires
   `hcancel : ∀ x ∈ ball x₀ r, v (t,x) + w (t,x) = 0` and chooses
   `O = periodicSet (ball x₀ r)`
   (`formalization/NSFormalization/Section3/T16/LatticeLift.lean:341-369`).
   Consequently the packaged theorem requires the same whole-ball hypothesis
   `hWcancel`
   (`formalization/NSFormalization/Section3/T16/LatticeLift.lean:393-399`)
   and invokes it in
   `formalization/NSFormalization/Section3/T16/LatticeLift.lean:450-453`.
   This is stronger than, and not the same as, the canonical field, which only
   asks for some open neighborhood of the packet support
   (`formalization/NSFormalization/Section3/T16/LocalPotential.lean:158-162`).
   The data record carries the plateau facts at
   `formalization/NSFormalization/Section3/T16/LocalPotential.lean:120-129`,
   not a whole-ball cancellation hypothesis.
   It is
   also not what the cited mathematics says: the paper has cancellation “on an
   open neighborhood of `supp U_ε(t)`” (`paper/sections/03-torus.tex:188-193`).
   The existing chart lemma supplies exactly that weaker shape—an open `O`
   containing `K` and eventual cancellation on `O`
   (`formalization/NSFormalization/Paper1/LocalCutoff.lean:130-154`), with
   `localCorrection_eq_neg` requiring the local plateau hypothesis
   (`formalization/NSFormalization/Paper1/LocalCutoff.lean:77-87`).  For the
   intended compactly supported physical correction,
   `W ε` is zero outside its scaled cutoff while a general `v` is not zero on
   all of `ball x₀ r`, so `hWcancel` is generally unprovable.  Thus the lane
   does not close `correction_cancels` for the chart situation in the brief;
   it proves only a vacuous/over-assumed transport statement.

2. **Module gate is not silent.**  The module has three own warnings: deprecated
   `push_neg` at
   `formalization/NSFormalization/Section3/T16/LatticeLift.lean:256`, deprecated
   `Set.mem_setOf_eq` at
   `formalization/NSFormalization/Section3/T16/LatticeLift.lean:355`, and the
   unused named input `hθR` at
   `formalization/NSFormalization/Section3/T16/LatticeLift.lean:385`.  The last is also an
   explicit unused hypothesis in the packaged theorem, contrary to the
   brief's no-unused-binders requirement.  These are straightforward cleanup
   items, but the claimed “0 output” for the module is false.

3. The report's declared residual (`potential_smooth`/`potential_curl`) is
   accurately kept out of this lane (`research/T16/REPORT_352.md:39-48`).  A
   tree search found the relevant existing I02 and Paper1 declarations, in
   particular `timePotential_contDiffOn` and `spatialCurl_timePotential_on`
   (`formalization/NSFormalization/Section4/I02/Reference.lean:86-110`) and
   the chart lemmas cited above; no existing declaration repairs the
   whole-ball `hWcancel` mismatch.

## Commands and results

All commands used `. scripts/lean-env.sh`, ran from `verification/`, and used
`LEAN_NUM_THREADS=6`.  The exact results were:

```text
$ lake build NSFormalization.Section3.T16.LatticeLift
... warning: NSFormalization/Section3/T16/LatticeLift.lean:256:6: `push_neg` has been deprecated. Prefer using `push Not` instead.
... warning: NSFormalization/Section3/T16/LatticeLift.lean:355:30: `Set.mem_setOf_eq` has been deprecated. Use `Set.mem_ofPred_eq` instead.
... warning: NSFormalization/Section3/T16/LatticeLift.lean:385:23: Variable name `hθR` is not explicitly referenced.
Build completed successfully (9358 jobs).
```

```text
$ lake env lean ../formalization/NSFormalization/Section3/T16/LatticeLift.lean
.../LatticeLift.lean:256:6: warning: `push_neg` has been deprecated. Prefer using `push Not` instead.
.../LatticeLift.lean:355:30: warning: `Set.mem_setOf_eq` has been deprecated. Use `Set.mem_ofPred_eq` instead.
.../LatticeLift.lean:385:23: warning: Variable name `hθR` is not explicitly referenced.
```

```text
$ lake env lean ../research/T16/probes/lattice_lift_closes.lean
(no output; exit 0)
```

```text
$ lake env lean ../research/T16/axioms_lattice_lift.lean
'NSFormalization.Section3.T16.latticeLift' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T16.latticeVector_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T16.latticeVector_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T16.latticeLift_eq_periodize' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T16.supportedInCube_of_ball' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T16.coord_of_ball' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T16.latticeLift_smooth' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T16.latticeLift_periodic' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T16.latticeLift_eq_of_ball' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T16.sdiv_congr' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T16.spatialDivergence_translate' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T16.spatialDivergence_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T16.spatialDivergence_finsetSum' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T16.latticeLift_divergence_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T16.latticeLift_timeSupport' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T16.latticeLift_sliceSupport' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T16.isPeriodicOn_sub_latticeVector' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T16.latticeLift_cancels' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T16.correction_fields_of_chart' depends on axioms: [propext, Classical.choice, Quot.sound]
```

```text
$ make check
exit=0
.............
----------------------------------------------------------------------
Ran 13 tests in 0.043s

OK
45 work items: ownership, contract registration and task cards consistent.
```

`verification/` was not touched by the lane-only diff (`git diff --name-only
1f219211..HEAD` lists only the new module and research records), so the
conditional `scripts/gates.sh`/`check_contracts.py --base-ref
origin/erenup/integration-section3` gate does not apply.  The comparison to
`origin/erenup/integration-section3` includes inherited lane-347 files,
including `LocalPotential.lean`; this is not a lane-352 edit.

The exact lane-only name output was:

```text
formalization/NSFormalization/Section3/T16/LatticeLift.lean
research/T16/ATTEMPTS_LATTICE_LIFT.md
research/T16/COMPARISON.md
research/T16/REPORT_352.md
research/T16/axioms_lattice_lift.lean
research/T16/probes/lattice_lift_closes.lean
```

The required comparison command against `origin/erenup/integration-section3`
also shows the inherited lane-347 files (`LocalPotential.lean`,
`REPORT_347.md`, `SPEC_ISSUES.md`, `axioms_local_potential.lean`, and
`probes/api_on_canonical.lean`) in addition to the six lane-352 paths above;
there is no lane-352 edit to those inherited files.

The required substantive negative probe is
`research/T16/probes/rev352_widen_ball.lean`, changing the load-bearing bound
from `r + ρ ≤ 1` to `r + ρ ≤ 2`.  Its exact result is:

```text
.../rev352_widen_ball.lean:17:38: error: Application type mismatch: The argument
  hρr
has type
  r + ρ ≤ 2
but is expected to have type
  r + ρ ≤ 1
in the application
  @latticeLift_eq_of_ball w x₀ ρ r hslice hρr
```

No forbidden proof token occurs in the module or field probe; the only hygiene
grep hit is the word “Axiom” in the conformance file's comment at
`research/T16/axioms_lattice_lift.lean:3`.  No `maxHeartbeats` declaration is
present.  The report's “not this lane” claim was checked with `grep -rn` over
the complete `formalization/NSFormalization/Section4` tree and the relevant
Paper1/T10 files before this verdict.

Fixes required before acceptance:

1. Replace the whole-ball `hWcancel`/`hcancel` interface with the exact open
   neighborhood/plateau cancellation data needed by `correction_cancels`, and
   periodize that neighborhood while retaining the packet-support inclusion.
2. Remove or genuinely use `hθR`; replace deprecated `push_neg` and
   `Set.mem_setOf_eq` so the module typecheck is silent.

---

## Lane 352 response (revision r1)

Both blocking items addressed in commit on `erenup/352-T16-lattice-lift`:

1. **Fidelity (correction_cancels).**  `latticeLift_cancels` no longer assumes
   whole-ball cancellation.  Its new hypotheses are an open plateau
   `O` with `hO : IsOpen O`, `hOsub : O ⊆ ball x₀ r`,
   `hcancel : ∀ x ∈ O, v (t,x) + w (t,x) = 0`, and the periodic packet bound
   `hpacket : tsupport (fun x => P x) ⊆ periodicSet O`; the output existential
   returns `O' = periodicSet O` (periodicity extends the cancellation from `O`
   to every integer translate).  The packaged `correction_fields_of_chart`
   correspondingly takes the local cancellation datum

   ```
   hWcancel : ∀ ε ∈ Ioc (0:ℝ) ε₀, ∀ t ∈ Ico (T - ε ^ 2) T,
     ∃ O : Set Space, IsOpen O ∧ O ⊆ ball x₀ r ∧
       tsupport (fun x => periodicScaledPacket U x₀ T ε (t, x)) ⊆ periodicSet O ∧
       ∀ x ∈ O, v (t, x) + W ε (t, x) = 0
   ```

   which is exactly the tuple `Paper1.exists_local_background_removal` returns
   (open `O ⊇ supp Uε`, `O ⊆` cutoff ball, `v + w = 0` on `O`) plus T14's
   periodic packet support.  The whole-ball `hWcancel` is gone.

2. **Hygiene.**  `push_neg` replaced by a `not_not.mp` term; the `periodicSet`
   openness now uses an explicit `ext`/`constructor` proof (no
   `Set.mem_setOf_eq`); the unused `hθR` binder removed from
   `correction_fields_of_chart`.  `lake env lean` on the module now prints no
   output (0 warnings, 0 errors); `lake build` shows no `LatticeLift.lean`
   warnings.

Gates re-run: module build 0 errors/0 warnings; `lake env lean` on module,
`research/T16/probes/lattice_lift_closes.lean` (updated to the new `hWcancel`),
and `research/T16/axioms_lattice_lift.lean` all clean (19 decls
`[propext, Classical.choice, Quot.sound]`); the negative probe
`rev352_widen_ball.lean` still errors (load-bearing bound intact); `make check`
passes.
