REJECT

## What the lane claims

`research/T16/REPORT_352.md:5-25` claims the genuine lattice `tsum`, its
definitional identification with `NavierStokes.PeriodicLocalization.periodize`,
and transport of the canonical correction fields.  The canonical structure has
seven `correction_*` fields, not eight: `correction_formula` through
`correction_cancels` are at
`formalization/NSFormalization/Section3/T16/LocalPotential.lean:140-162`.
The report is right to call this a seven-field conjunction; the brief's “eight”
is a counting error.

## What is in Lean

The lift is the requested sum at
`formalization/NSFormalization/Section3/T16/LatticeLift.lean:57-60`, and the
definitional bridge is `rfl` at
`formalization/NSFormalization/Section3/T16/LatticeLift.lean:74-75`.  The support-to-cube, smoothness,
periodicity, ball-locality, divergence, time-support, and slice-support lemmas
are present at
`formalization/NSFormalization/Section3/T16/LatticeLift.lean:81-128,135-162,168-241,247-320`.
The integer shift and local cancellation transport are at
`formalization/NSFormalization/Section3/T16/LatticeLift.lean:327-379`.

`correction_fields_of_chart` does return seven conjunction components with the
right canonical output bodies at
`formalization/NSFormalization/Section3/T16/LatticeLift.lean:395-428`, and the
probe copies those specialized bodies at
`research/T16/probes/lattice_lift_closes.lean:38-80`.  The nonzero bump witness
is substantive: smoothness, periodicity, and nonzero value of the lift are
checked at `research/T16/probes/lattice_lift_closes.lean:87-120`.

## Gaps

1. **Blocking cancellation-interface gap.**  The packaged theorem does not
   derive the concrete chart cancellation needed by the brief.  Its new
   `hWcancel` assumption is pointwise cancellation plus an additional
   periodized packet-support bound:
   `formalization/NSFormalization/Section3/T16/LatticeLift.lean:409-412`.
   The canonical field, by contrast, asks for the output existential only
   (`LocalPotential.lean:158-162`), and the paper states cancellation on an open
   neighborhood (`paper/sections/03-torus.tex:188-193`).

   The cited chart theorem does not return the assumed statement.  It returns
   `K ⊆ O` and *eventual* cancellation in each neighborhood,
   `∀ᶠ y in 𝓝 x`, at
   `formalization/NSFormalization/Paper1/LocalCutoff.lean:130-140`; its
   construction of the plateau is at
   `formalization/NSFormalization/Paper1/LocalCutoff.lean:14-26`.  The exact mismatch is
   reproduced by the permitted scratch probe
   `research/T16/probes/rev352_cancel_interface.lean:10-17`:

   ```text
   ../research/T16/probes/rev352_cancel_interface.lean:17:2: error: Type mismatch
     hzero x hx
   has type
     ∀ᶠ (y : Space) in 𝓝 x, v (t, y) + w (t, y) = 0
   but is expected to have type
     v (t, x) + w (t, x) = 0
   ```

   In addition, the required packet inclusion is only a hypothesis in
   `latticeLift_cancels`
   (`formalization/NSFormalization/Section3/T16/LatticeLift.lean:348-356`) and in `hWcancel`; the tree contains only
   the totalized packet definition at
   `formalization/NSFormalization/Section3/T16/LocalPotential.lean:81-84`.
   `rg -n -i 'periodicScaledPacket|periodic.*packet|packet.*periodic'
   formalization/NSFormalization` finds no support theorem.  Thus the report's
   assertion that `exists_local_background_removal` “returns exactly this
   tuple” and that “T14 supplies the periodic packet support”
   (`research/T16/REPORT_352.md:48-50`) is not supported by this tree.  The
   report must either prove these obligations (including the eventual-to-
   pointwise conversion) or state them as an explicit residual; merely adding
   `hWcancel` leaves the intended `physicalCorrection` case unclosed.

2. The report says the downstream assembly is lane 358
   (`research/T16/REPORT_352.md:48`), while this brief assigns assembly to lane 353.  This is
   a documentation fix, but the cancellation obligation above is substantive,
   not a one-line naming issue.

3. The report's separate potential gap is correctly kept out of this lane.  The
   whole `Section4` search found the I02 declarations
   `formalization/NSFormalization/Section4/I02/Reference.lean:86-110`, but no
   lattice-lift or periodic-packet-support declaration.  This satisfies the
   required “not in the tree” check for the claims made here.

## Commands and results

All Lean commands used `. scripts/lean-env.sh`, ran from `verification/`, and
used `LEAN_NUM_THREADS=6`.

```text
$ LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T16.LatticeLift
⚠ [8778/9073] Replayed NSFormalization.Source.FiniteHilbertBochner
warning: NSFormalization/Source/FiniteHilbertBochner.lean:24:19: try 'simp' instead of 'simpa'
warning: NSFormalization/Source/FiniteHilbertBochner.lean:23:37: This simp argument is unused:
  PiLp.single_apply
warning: NSFormalization/Source/FiniteHilbertBochner.lean:39:23: This simp argument is unused:
  PiLp.single_apply
⚠ [9321/9358] Replayed NSFormalization.Source.RealSobolev
warning: NSFormalization/Source/RealSobolev.lean:90:30: This simp argument is unused:
  Complex.smul_re
warning: NSFormalization/Source/RealSobolev.lean:90:47: This simp argument is unused:
  Complex.smul_im
warning: NSFormalization/Source/RealSobolev.lean:90:64: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice
⚠ [9325/9358] Replayed NSFormalization.Paper3.SpatiallyCompactTime
warning: NSFormalization/Paper3/SpatiallyCompactTime.lean:88:19: `ContinuousLinearMap.sub_apply` has been deprecated: Use `sub_apply` instead.
⚠ [9332/9358] Replayed NSFormalization.Paper3.RealPositiveDensity
warning: NSFormalization/Paper3/RealPositiveDensity.lean:67:59: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice
warning: NSFormalization/Paper3/RealPositiveDensity.lean:76:63: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice
warning: NSFormalization/Paper3/RealPositiveDensity.lean:88:59: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice
warning: NSFormalization/Paper3/RealPositiveDensity.lean:100:59: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice
⚠ [9335/9358] Replayed NSFormalization.Paper3.RealVectorPositiveDensity
warning: NSFormalization/Paper3/RealVectorPositiveDensity.lean:29:5: Variable name `hc` is not explicitly referenced.
⚠ [9345/9358] Replayed NSFormalization.Source.PacketForceExtension
warning: NSFormalization/Source/PacketForceExtension.lean:44:25: `if_pos` has been deprecated: Use `ite_eq_left` instead
⚠ [9348/9358] Replayed NSFormalization.Source.ViscosityPacket
warning: NSFormalization/Source/ViscosityPacket.lean:34:63: This simp argument is unused:
  Function.comp_def
Build completed successfully (9358 jobs).
```

The module itself is silent:

```text
$ lake env lean ../formalization/NSFormalization/Section3/T16/LatticeLift.lean
(no output; exit 0)
$ lake env lean ../research/T16/probes/lattice_lift_closes.lean
(no output; exit 0)
```

The axiom audit is clean for all 19 declarations; every line is exactly:

```text
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

The required substantive mutation widens `r + ρ ≤ 1` to `r + ρ ≤ 2` in
`research/T16/probes/rev352_widen_ball.lean:10-17`; it fails as expected:

```text
../research/T16/probes/rev352_widen_ball.lean:17:38: error: Application type mismatch: The argument
  hρr
has type
  r + ρ ≤ 2
but is expected to have type
  r + ρ ≤ 1
in the application
  @latticeLift_eq_of_ball w x₀ ρ r hslice hρr
```

`make check` exits 0.  Its final checks are exactly:

```text
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.045s

OK
python3 experiments/check_work_queue.py
45 work items: ownership, contract registration and task cards consistent.
```

The lane-only diff against its lane-347 parent contains the new module and
records/probes; no `verification/` path is touched.  The requested comparison
is `git diff --name-status origin/erenup/integration-section3...HEAD`, whose
only code addition is `formalization/NSFormalization/Section3/T16/LatticeLift.lean`;
there is no existing-module modification.  Therefore the conditional
`scripts/gates.sh` and `check_contracts.py --base-ref
origin/erenup/integration-section3` gate was not applicable.  The hygiene
search found no forbidden proof token in the module or probes, and no
`maxHeartbeats` declaration.

---

## Lane 352 response (revision r2)

All three points addressed (existing declaration names/statements unchanged —
lane 358 has merged a6f0e836):

1. **Eventual→pointwise bridge.**  Added
   `cancel_of_eventually {v w : SpaceTimeField} {O : Set Space} {t : ℝ}
   (h : ∀ x ∈ O, ∀ᶠ y in 𝓝 x, v (t, y) + w (t, y) = 0) :
   ∀ x ∈ O, v (t, x) + w (t, x) = 0` (via `Filter.Eventually.self_of_nhds`), and
   `correction_fields_of_chart'` — identical conclusion to
   `correction_fields_of_chart`, but its `hWcancel` is the *eventual* form
   `∀ x ∈ O, ∀ᶠ y in 𝓝 x, v + W ε = 0` that `exists_local_background_removal`
   actually returns; it converts internally via `cancel_of_eventually`.  The
   scratch probe `research/T16/probes/rev352_cancel_interface.lean` now compiles
   (its `exact hzero x hx` type error is resolved by `cancel_of_eventually`), and
   it also exercises `correction_fields_of_chart'` end-to-end.

2. **Documentation.**  The module docstrings, `REPORT_352.md`, `COMPARISON.md`
   and `ATTEMPTS_LATTICE_LIFT.md` no longer claim the chart theorem or T14
   "supplies" `hWcancel`.  They now state that the two components of `hWcancel`
   (periodic packet support `⊆ periodicSet O`; pointwise cancellation on `O`) are
   **obligations of assembly lane 358**, with the exact route 358 uses
   (`periodicScaledPacket = latticeLift (scaledPacket)` + T14 `delayed_full_support`
   + `latticeLift_sliceSupport` for the packet bound; `theta_one`/`eta_one` via
   `exists_local_background_removal` + `cancel_of_eventually` for the cancellation).

3. **Lane number.**  All references now read lane 358 (the assembly lane, per the
   lead), including the two module docstrings that previously said 353.

Gates re-run: module build 0 errors / 0 module warnings; `lake env lean` on the
module, `lattice_lift_closes.lean`, `rev352_cancel_interface.lean` and
`axioms_lattice_lift.lean` all clean (21 decls `[propext, Classical.choice,
Quot.sound]`); `rev352_widen_ball.lean` still errors (bound intact);
`make check` passes.
