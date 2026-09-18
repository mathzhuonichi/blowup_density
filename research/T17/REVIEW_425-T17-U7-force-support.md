ACCEPT-WITH-NOTES

## 1. What the lane claims

The worker report claims the three canonical U7 conclusions at the concrete
`correctionData`: `force_smooth`, `force_periodic`, and `force_support`
(`research/T17/REPORT_425.md:22-46`), together with the supporting
`latticeLift_spaceSupport` and `source_force_tsupport` lemmas
(`research/T17/REPORT_425.md:48-50`). All five declarations exist at the cited
locations (`formalization/NSFormalization/Section3/T17/ForceSupport.lean:77-127`,
`:135-159`, `:164-182`, and `:191-244`).

The three conclusion types are literally the canonical fields after replacing
`D` by `correctionData v x₀ T θ η O θR ε₀` and replacing the placement
projections by bare `x₀,T`:

- canonical `force_smooth`: `Correction.lean:159-162`; delivered theorem:
  `ForceSupport.lean:135-148`;
- canonical `force_periodic`: `Correction.lean:163-166`; delivered theorem:
  `ForceSupport.lean:164-177`;
- canonical `force_support`: `Correction.lean:167-172`; delivered theorem:
  `ForceSupport.lean:191-206`.

This also agrees with the reconciled Spec block
(`research/T17/Spec.lean:838-851`). In particular, the scale interval is
`Ioc 0 D.ε₀`, the time coefficient is exactly `2`, and the spatial set is
`periodicSet (Metric.ball ...)`, not a closed ball. The conformance probe closes
the three concrete statements by `exact` (`force_support_closes.lean:32-83`)
and projects all three corresponding fields from a hypothetical canonical
record without conversion (`force_support_closes.lean:93-122`).

The mathematics matches the manuscript: the cutoff is compactly supported in
the open spatial cutoff and in `(-2,2)` (`paper/sections/03-torus.tex:181-189`),
the small-scale conditions and smooth zero extension are stated at
`03-torus.tex:212`, and `H_ε` is the local differential expression whose
smoothness/support is asserted at `03-torus.tex:218-225`. The exact Lean source
support supplier has the open cylinder
`Ioo (T-2ε²) (T+2ε²) ×ˢ ball x₀ (ε*R)`
(`Source/PhysicalRemoval.lean:56-74`), and the force-support lemma preserves
that support (`Source/LocalizedInsertion.lean:45-54`).

The global hypothesis `hv : ContDiff ℝ ∞ v` is the documented G1 premise
(`research/T17/SPEC_ISSUES.md:3`). It is used honestly: `force_smooth` supplies
it to both `force_eq` and `physicalForce_smooth`
(`ForceSupport.lean:150-156`); `force_periodic` and `force_support` use
`hv.contDiffOn` for the transport theorem (`ForceSupport.lean:179-182` and
`:208-211`). The supplier really requires global smoothness
(`Paper1/CorrectionVectorNorms.lean:22-26`), while `force_eq` requires local
smoothness on the chart cylinder (`Section3/T17/Transport.lean:281-291`). No
named premise repackages a goal, and all other hypotheses are used by the
concrete-data construction/transport.

## 2. What is in Lean

`force_smooth` rewrites by the transport identity, applies the actual T16
smooth lattice-lift theorem, and obtains its spatial support input from the
open-cylinder supplier (`ForceSupport.lean:149-159`; supplier signature at
`Section3/T16/LatticeLift.lean:120-125`). `force_periodic` uses the transported
periodicity theorem directly (`ForceSupport.lean:178-182`; underlying lattice
periodicity at `LatticeLift.lean:128-132`).

For `force_support`, the worker correctly did not use the insufficient
slice-only theorem: that theorem requires `ρ < r` and returns the larger
`periodicSet (ball x₀ r)` for one time slice
(`LatticeLift.lean:273-278`). Instead, the new theorem proves the space-time
support inclusion by the existing locally finite sum neighbourhood
(`ForceSupport.lean:77-110`; supplier at
`vendor/NavierStokesAndEuler/NavierStokes/PeriodicLocalization.lean:135-143`).
The final proof combines exact time support with the periodic image of the
compact spatial projection (`ForceSupport.lean:213-244`). This is a genuine
open-ball result, not a closure/closed-ball weakening.

The lane's non-vacuity instance constructs a nonzero constant periodic,
divergence-free reference and a strictly positive `ε₀`, then instantiates all
three results (`force_support_closes.lean:160-197`). Thus the quantified `Ioc`
is not empty; there is no `⊤.toReal = 0`-style collapse. The probe itself
typechecks and its five printed declarations have exactly the standard three
axioms (`force_support_closes.lean:201-205`).

Hygiene is clean. The lane diff against
`origin/erenup/integration-section3...HEAD` adds the one implementation module
and research records/probes, and only modifies the required status record; no
pre-existing `.lean` module is modified. The new implementation is 246 lines
and the conformance probe is 205 lines, as reported
(`REPORT_425.md:54-58`). There are no declarations or uses of
`sorry`, `admit`, `axiom`, or `native_decide`, and no `maxHeartbeats` setting in
the added Lean files. Every declaration in `axioms_u7.lean:3-7` prints exactly
`[propext, Classical.choice, Quot.sound]`.

The substantive reviewer mutation changes the conclusion's time constant from
`2` to `1`, without dropping an argument or hypothesis
(`research/T17/probes/rev425_wrong_time_constant.lean:17-35`). Lean rejects it
with the expected interval type mismatch (exact output in part 4).

## 3. Gaps

There is no residual U7 proof gap. G1 remains an assembly/spec-level issue:
the canonical record has `reference_periodic` but no `reference_smooth`, so U12
must supply global smoothness or use the documented truncation route
(`SPEC_ISSUES.md:3`; `REPORT_425.md:65-67`). That is explicit and does not make
this lane's theorems dishonest.

The report's “not in the tree” claim concerns a closedness lemma for
`periodicSet` (`REPORT_425.md:71-75`). A whole-tree search under
`formalization/NSFormalization/Section4` for `periodicSet` and for the relevant
`IsClosed` combinations returned no matches. A broader
`formalization/NSFormalization` search found the definition/monotonicity and
slice-support consumers, but no `IsClosed (periodicSet ...)` theorem; the
relevant existing replacement is only `periodicSet_mono`
(`Section3/T16/Assembly.lean:243-246`). The mathematical gap claim is therefore
accepted. The literal wording that raw `grep -rn "periodicSet" formalization/`
“yields only” four hits is imprecise, because there are also consumer
occurrences; it does not affect the proof.

One exact documentary fix is required before merge: in
`research/T17/T17_SPLIT.md:188-191`, replace the stale T16 citations
`latticeLift_smooth:116`, `latticeLift_periodic:124`,
`latticeLift_timeSupport:247`, and `latticeLift_sliceSupport:271` with
`:120`, `:128`, `:251`, and `:275`, respectively. The worker report already
records the correct locations (`REPORT_425.md:68-69`).

The brief-requested background file `research/T17/REPORT_412.md` is absent from
this checkout; this does not affect the checked U7 statements or their build.

## 4. Commands and results

All Lake commands were run one at a time from `verification/`, after sourcing
`../scripts/lean-env.sh`, with `LEAN_NUM_THREADS=6`.

`lake build NSFormalization.Section3.T17.ForceSupport` exited 0. Exact output:

```text
⚠ [8778/8904] Replayed NSFormalization.Source.FiniteHilbertBochner
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
⚠ [9317/9362] Replayed NSFormalization.Paper3.SpatiallyCompactTime
warning: NSFormalization/Paper3/SpatiallyCompactTime.lean:88:19: `ContinuousLinearMap.sub_apply` has been deprecated: Use `sub_apply` instead

Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.sub_apply` to `sub_apply x`).
⚠ [9325/9362] Replayed NSFormalization.Source.PacketForceExtension
warning: NSFormalization/Source/PacketForceExtension.lean:44:25: `if_pos` has been deprecated: Use `ite_eq_left` instead
⚠ [9328/9362] Replayed NSFormalization.Source.ViscosityPacket
warning: NSFormalization/Source/ViscosityPacket.lean:34:63: This simp argument is unused:
  Function.comp_def

Hint: Omit it from the simp argument list.
  [apply] simp [viscosityVelocity, dilateField, viscosityHomeomorph, Prod.map]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
⚠ [9339/9362] Replayed NSFormalization.Source.RealSobolev
warning: NSFormalization/Source/RealSobolev.lean:90:30: This simp argument is unused:
  Complex.smul_re

Hint: Omit it from the simp argument list.
  [apply] simp [Complex.smul_im]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: NSFormalization/Source/RealSobolev.lean:90:47: This simp argument is unused:
  Complex.smul_im

Hint: Omit it from the simp argument list.
  [apply] simp [Complex.smul_re]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: NSFormalization/Source/RealSobolev.lean:90:64: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
⚠ [9349/9362] Replayed NSFormalization.Paper3.RealPositiveDensity
warning: NSFormalization/Paper3/RealPositiveDensity.lean:67:59: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Paper3/RealPositiveDensity.lean:76:63: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Paper3/RealPositiveDensity.lean:88:59: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Paper3/RealPositiveDensity.lean:100:59: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
⚠ [9352/9362] Replayed NSFormalization.Paper3.RealVectorPositiveDensity
warning: NSFormalization/Paper3/RealVectorPositiveDensity.lean:29:5: Variable name `hc` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hc

Note: This linter can be disabled with `set_option linter.unusedVariables false`
Build completed successfully (9362 jobs).
```

All warnings are replayed dependency warnings; there is no warning from the
lane module.

`lake env lean ../formalization/NSFormalization/Section3/T17/ForceSupport.lean`
exited 0 with exactly zero output.

`lake env lean ../research/T17/probes/force_support_closes.lean` exited 0 with
exact output:

```text
'NSFormalization.Section3.T17.Probe.field_force_smooth' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T17.Probe.field_force_periodic' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T17.Probe.field_force_support' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T17.Probe.fields_at_placement' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T17.Probe.nonvacuous_force_support' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`lake env lean ../research/T17/axioms_u7.lean` exited 0 with exact output:

```text
'NSFormalization.Section3.T17.latticeLift_spaceSupport' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T17.source_force_tsupport' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T17.force_smooth' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T17.force_periodic' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T17.force_support' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`lake env lean ../research/T17/probes/rev425_wrong_time_constant.lean` exited 1,
as required. Exact output:

```text
../research/T17/probes/rev425_wrong_time_constant.lean:34:2: error: Type mismatch
  force_support ν hv x₀ T δ r hvper O θR ε₀ hθ hη hθc hηc hθsupp hηsupp hr2 hεtime hεspace
has type
  ∀ ε ∈ Ioc 0 (correctionData v x₀ T θ η O θR ε₀).ε₀,
    tsupport (correctionForce ν v (correctionData v x₀ T θ η O θR ε₀) ε) ⊆
      Ioo (T - 2 * ε ^ 2) (T + 2 * ε ^ 2) ×ˢ periodicSet (ball x₀ (ε * (correctionData v x₀ T θ η O θR ε₀).θRadius))
but is expected to have type
  ∀ ε ∈ Ioc 0 (correctionData v x₀ T θ η O θR ε₀).ε₀,
    tsupport (correctionForce ν v (correctionData v x₀ T θ η O θR ε₀) ε) ⊆
      Ioo (T - ε ^ 2) (T + ε ^ 2) ×ˢ periodicSet (ball x₀ (ε * (correctionData v x₀ T θ η O θR ε₀).θRadius))
```

`. scripts/lean-env.sh && LEAN_NUM_THREADS=6 make check` exited 0. Its very
large JSON closure inventory was captured unabridged at
`/tmp/rev425_make_check.log`; exact audit metadata and tail were:

```text
  47563 1963045 /tmp/rev425_make_check.log
01783519fff79f2c51201c1748fd8845b4905dd5fcfab09f256a1f6edaeaa3ff  /tmp/rev425_make_check.log
      "Tests.Localization"
    ]
  },
  "base_compatibility_checked": false,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.043s

OK
python3 experiments/check_work_queue.py
45 work items: ownership, contract registration and task cards consistent.
```

The forbidden-token/heartbeat grep had zero output. The lane-only
`git diff --name-status origin/erenup/integration-section3...HEAD` was:

```text
A formalization/NSFormalization/Section3/T17/ForceSupport.lean
A research/T17/ATTEMPTS_U7.md
A research/T17/REPORT_425.md
M research/T17/T17_SPLIT.md
A research/T17/axioms_u7.lean
A research/T17/probes/force_support_closes.lean
```

No path under `verification/` was touched, so the conditional
`scripts/gates.sh` and
`experiments/check_contracts.py --base-ref origin/erenup/integration-section3`
gates do not apply. No git state-changing command was run.

Required fix: update the four stale T16 line numbers in
`research/T17/T17_SPLIT.md:188-191` from `116/124/247/271` to
`120/128/251/275`.
