ACCEPT

## 1. What the lane claims

The lane claims the four U8 fields: pointwise blow-up, essential-supremum
blow-up, lifespan exactly `T`, and record-form maximality. These are exactly the
canonical targets in `BoundaryInsertionAPI`: `lifespan`, `maximal`, `blowup`,
and `blowup_limsup` at
`formalization/NSFormalization/Section3/T23/Boundary.lean:292`, `:302`, `:308`,
and `:313`. The worker's field probe repeats those four target types and closes
them by `exact` at
`research/T23/probes/T23-U8-interior-blowup_closes.lean:35-57`; the two box
specializations are checked at `:59-67`.

This matches the requested mathematics. The paper specifies insertion in any
prescribed interior ball at `paper/sections/03-torus.tex:646`, interior support
at `:654-655`, no-slip uniqueness at `:664`, and concludes that the constructed
solution is singular exactly at `T` at `:664`. The stronger four-field spelling
is the reconciled Spec at `research/T23/Spec.lean:847-870`. The local
essential-supremum adaptation is faithful to the cited global model theorem at
`formalization/NSFormalization/Section4/R42/BlowupEssSup.lean:100`, and the
lifespan argument follows the cited torus pattern at
`formalization/NSFormalization/Section3/T18/Lifespan.lean:249`, `:273`, `:300`,
and `:338` while replacing the torus cube by `closure Ω`.

The production theorem statements exist where claimed:

- `U8.blowup` is at
  `formalization/NSFormalization/Section3/T23/InteriorBlowup.lean:137-141` and
  has the exact canonical `SpeedUnboundedAt place.T (velocity ε)` conclusion.
- `U8.blowup_limsup` is at the same file, `:146-155`, and has the exact
  whole-space `A02.speedENorm`/`limsupLeft` conclusion.
- `U8.lifespan` is at
  `formalization/NSFormalization/Section3/T23/Lifespan.lean:104-112` and has
  equality with `ENNReal.ofReal place.T`, not a one-sided bound.
- `U8.maximal` is at the same file, `:115-128`, and retains the literal
  `velocity ε` and `pressure ε` fields.

The hypotheses are honest cross-lane inputs, not assumed versions of a U8
conclusion. Their types are visible together at
`InteriorBlowup.lean:105-122` and `Lifespan.lean:80-100`: raw packet blow-up,
the family-to-placement threshold inclusion, interior-ball containment, the
literal U3 velocity formula and solution package, packet-slice support, U2
cancellation, viscosity positivity, domain openness/boundedness, and the named
G1 identity `IBP Ω`. The last is precisely the isolated scalar boundary identity
defined at `formalization/NSFormalization/Section3/T23/DomainSolution.lean:215-221`;
it is the approved smooth-branch input, not a lifespan or blow-up hypothesis.
The box variants discharge it with the proved `ibp_box` at
`DomainSolution.lean:223-245` and `Lifespan.lean:130-142`.

There is no `⊤.toReal = 0` shortcut: the limsup proof first obtains `b < ⊤` and
uses `ENNReal.ofReal_toReal hb2.ne` only afterward
(`InteriorBlowup.lean:85-100`). There is no empty-time-interval shortcut:
`DomainPlacementData.time_pos` is a stored strict positivity field
(`Placement.lean:40-44`), and admissible `ε` contributes `0 < ε` directly.
The API separately stores `eps_pos`; the reviewer probe gives concrete
inhabitants of both the canonical placement interval and the exact generic
family guard at `research/T23/probes/rev486_nonvacuity.lean:10-24`.

## 2. What is in Lean

`scaledPacket_speedUnbounded` really consumes
`speed_unbounded_at_target` and `zeroPastField_speed`
(`InteriorBlowup.lean:14-20`; upstream declarations at
`Source/PacketScaling.lean:179-184` and `:278-282`). The interior argument then
uses nonzero packet value, `packet_slice_zero`, slice support, cancellation, and
the closed-ball/domain inclusion to produce a witness in both the prescribed
ball and `Ω` (`InteriorBlowup.lean:25-56`; `LocalCorrection.lean:61-72`).

The essential-supremum step uses continuity at just the witness: the strict
superlevel set is a positive-volume neighborhood
(`InteriorBlowup.lean:60-74`). `SmoothOnClosedSlab.contDiffAt_slice` supplies
that ambient continuity from the solution's open-neighborhood extension
(`DomainSolution.lean:143-153`), and the frequently/limsup argument is at
`InteriorBlowup.lean:78-101`. Thus no exterior regularity was silently added.

The lifespan proof is also substantive. A longer solution is bounded on the
compact product `Icc 0 T × closure Ω` (`Lifespan.lean:13-23`). The lower bound
comes from the actual full-horizon solution and the defining supremum
(`:25-29`). The upper bound extracts a genuinely longer solution from the
supremum, applies the proved U7 core `velocity_eq_of_ibp`, and contradicts the
interior witness (`:33-57`; U7 core at
`DifferenceEnergy.lean:298-345`). `restrictHorizon` reconstructs every field of
the domain solution with the same literal velocity and pressure (`Lifespan.lean:59-76`),
which is then used for maximality (`:115-128`). The box uniqueness path is
proved without a new premise at `DifferenceEnergy.lean:375-386`.

The negative test changes a main mathematical constant rather than dropping an
argument: `research/T23/probes/rev486_lifespan_mutation.lean:31-36` changes
`ofReal place.T` to `ofReal (place.T + 1)`. It fails exactly because the
production theorem proves the unmutated lifespan:

```text
../research/T23/probes/rev486_lifespan_mutation.lean:35:2: error: Type mismatch
  U8.lifespan place D reference hspeed hscale hball hformula hsupport hcancel hsolution hν ho hb hI
has type
  ∀ ε ∈ Ioc 0 ε₀, domainMaximalLifespan ν Ω a (force ε) = ENNReal.ofReal place.T
but is expected to have type
  ∀ ε ∈ Ioc 0 ε₀, domainMaximalLifespan ν Ω a (force ε) = ENNReal.ofReal (place.T + 1)
```

The matching non-vacuity probe compiles with exit 0 and zero output.

Hygiene is clean. A word-boundary search of the two production modules found no
`sorry`, `admit`, `axiom`, or `native_decide`; a `maxHeartbeats` search also had
no output. Both production modules import only the canonical T23 chain, starting
at `InteriorBlowup.lean:1` and `Lifespan.lean:1`; no
`Paper1/BoundaryCorollary.lean` import occurs. `git diff --check` exits 0 with
zero output.

The required comparison
`git diff --name-only origin/erenup/integration-section3...HEAD` warns that the
history has multiple merge bases and lists the lane-480 parent additions as
well as U8. `git diff --name-status` shows every Lean path as `A`, not `M`.
Within the U8 range `cda74e54^..HEAD`, the only production Lean paths are the
two new U8 modules; the remaining U8 paths are its attempts/report/status/probe
artifacts. Thus U8 modified no pre-existing Lean module. The exact name-only
output was:

```text
warning: origin/erenup/integration-section3...HEAD: multiple merge bases, using b9eab7ff49606d56f033a7e76c835bf2ecbcaa5c
NEXT_SESSION.md
formalization/NSFormalization/Section3/T23/Boundary.lean
formalization/NSFormalization/Section3/T23/Geometry.lean
formalization/NSFormalization/Section3/T23/InteriorBlowup.lean
formalization/NSFormalization/Section3/T23/Lifespan.lean
formalization/NSFormalization/Section3/T23/WholeSpaceCorrection.lean
research/T23/ATTEMPTS_T23-U8-interior-blowup.md
research/T23/ATTEMPTS_UCAN.md
research/T23/REPORT_480.md
research/T23/REPORT_486.md
research/T23/SPEC_ISSUES.md
research/T23/T23_SPLIT.md
research/T23/axioms_486.log
research/T23/axioms_T23-U8-interior-blowup.lean
research/T23/axioms_ucan.lean
research/T23/imports_486.log
research/T23/probes/T23-U8-interior-blowup_closes.lean
research/T23/probes/boundary_api_on_canonical.lean
```

## 3. Gaps

There is no residual U8 proof gap. The smooth-domain G1 theorem remains an
upstream assembly dependency, exactly as the worker says:

```lean
∀ (Ω : Set Space), IsOpen Ω → Bornology.IsBounded Ω →
  IsRegularLevelDomain Ω → IBP Ω
```

It is recorded as deliberately unproved at
`research/T23/SPEC_ISSUES.md:21-27`; the complete uniqueness consequence under
`IBP Ω` is already proved at `DifferenceEnergy.lean:347-358`. Per the lead's
specific ruling, this explicit upstream field-shaped input is approved and is
not a U8 rejection reason. The box branch has no such residual.

The mandated whole-Section-4 searches did not find the missing regular-level
domain lemma or any T23 bounded-domain substitute. Exact output:

```text
formalization/NSFormalization/Section4/A04/NonlinearColumns.lean:82:/-- **Row 5b, order `m+1`.**  The same at order `m+1`, needed on the column side of the SL5 IBP,
formalization/NSFormalization/Section4/A04/NonlinearPairing.lean:21:  (`sum_real_inner_angularDirectionalDerivative`, the form the double-sum IBP consumes, since
formalization/NSFormalization/Section4/A04/NonlinearPairing.lean:28:  from the same datum), while SL5's IBP has `u` in one slot and `Wⱼ = uⱼ·u` in the other, so the
formalization/NSFormalization/Section4/A04/NonlinearPairing.lean:141:sign of `∑ⱼ ⟪aⱼ, bⱼ⟫` need not be tracked when the IBP produces `-⟪G, N⟫`.  Termwise
formalization/NSFormalization/Section4/D01/OrderZeroCurl.lean:67:/-- Two-index compact-support IBP (094 inlines this only at `k = j` inside `cs_pairing_zero`). -/
```

The second search for
`noSlip_uniqueness|velocity_eq_of_ibp|domainMaximalLifespan|ClassicalSolutionOmega`
and the third for `BoundaryInsertionAPI|boundaryInsertionStatement` produced
zero output. The displayed hits are unrelated spectral/compact-support IBP;
for example, `OrderZeroCurl.lean:67-84` assumes a globally smooth,
compactly-supported factor and is not a regular-level-domain theorem.

G0's arbitrary-cutoff statement repair and U9 registration are outside U8 and
are not claimed here (`REPORT_486.md:76-79`). They do not weaken or alter any of
the four U8 conclusions.

## 4. Commands and results

All Lean commands sourced `scripts/lean-env.sh`, used
`LEAN_NUM_THREADS=6`, and ran Lake only from `verification/`.

1. Prerequisite closure:

   ```sh
   lake build NSFormalization.Section3.T23.Boundary NSFormalization.Section3.T23.BoxIntegration NSFormalization.Section3.T23.LocalCorrectionBridge NSFormalization.Section3.T23.StatementRepair
   ```

   Exit 0. The output began with replayed dependency warnings and ended exactly:

   ```text
   Build completed successfully (10087 jobs).
   ```

2. New modules, run separately as required:

   ```sh
   lake build NSFormalization.Section3.T23.InteriorBlowup
   lake build NSFormalization.Section3.T23.Lifespan
   ```

   Both exit 0; exact final lines:

   ```text
   Build completed successfully (10088 jobs).
   Build completed successfully (10089 jobs).
   ```

   Existing dependency warnings were replayed. There was no warning or error
   whose path was `Section3/T23/InteriorBlowup.lean` or
   `Section3/T23/Lifespan.lean`, so the modules themselves are silent.

3. Direct typechecks:

   ```sh
   lake env lean ../formalization/NSFormalization/Section3/T23/InteriorBlowup.lean
   lake env lean ../formalization/NSFormalization/Section3/T23/Lifespan.lean
   lake env lean ../research/T23/probes/T23-U8-interior-blowup_closes.lean
   lake env lean ../research/T23/probes/boundary_api_on_canonical.lean
   lake env lean ../research/T23/probes/rev486_nonvacuity.lean
   ```

   Each exits 0 with exactly zero output.

4. Axiom audit:

   ```sh
   lake env lean ../research/T23/axioms_T23-U8-interior-blowup.lean
   ```

   Exit 0. Exact output (15 declarations):

   ```text
   'NSFormalization.Section3.T23.scaledPacket_speedUnbounded' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T23.interior_blowup' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T23.ofReal_le_eLpNormTop_of_continuousAt' depends on axioms: [propext,
    Classical.choice,
    Quot.sound]
   'NSFormalization.Section3.T23.limsupLeft_speedENorm_eq_top_of_interior' depends on axioms: [propext,
    Classical.choice,
    Quot.sound]
   'NSFormalization.Section3.T23.U8.interior' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T23.U8.blowup' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T23.U8.blowup_limsup' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T23.ClassicalSolutionOmega.speed_bound' depends on axioms: [propext,
    Classical.choice,
    Quot.sound]
   'NSFormalization.Section3.T23.domainLifespan_ge_horizon' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T23.domainLifespan_eq_of_interior' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T23.ClassicalSolutionOmega.restrictHorizon' depends on axioms: [propext,
    Classical.choice,
    Quot.sound]
   'NSFormalization.Section3.T23.U8.lifespan' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T23.U8.maximal' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T23.U8.lifespan_box' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T23.U8.maximal_box' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

5. `make check`:

   ```sh
   LEAN_NUM_THREADS=6 make check
   ```

   Exit 0. The raw output had 67,332 lines, so only bounded first/last excerpts
   are quoted. It began:

   ```text
   python3 experiments/check_formalization_plan.py --check
   {
     "task_count": 45,
     "source_counts": {
       "formalization": 733,
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
     "tracked_cache_free": true,
     "source_hashes_match": false
   }
   Explicit axiom/admission tokens, all copied sources: 11
   python3 experiments/check_contracts.py
   ```

   It ended:

   ```text
     "base_compatibility_checked": false,
     "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
   }
   python3 experiments/test_contract_policy.py
   .............
   ----------------------------------------------------------------------
   Ran 13 tests in 0.044s

   OK
   python3 experiments/check_work_queue.py
   45 work items: ownership, contract registration and task cards consistent.
   ```

   The copied-umbrella `BoundaryCorollary` token and
   `source_hashes_match: false` are pre-existing inventory findings, not an
   error or an import in this lane. The check reports 54 registered contracts.

6. Standard gate script:

   ```sh
   BASE_REF=origin/erenup/integration-section3 LEAN_NUM_THREADS=6 scripts/gates.sh NSFormalization.Section3.T23.InteriorBlowup NSFormalization.Section3.T23.Lifespan
   ```

   Exit 0. The raw output had 67,655 lines. Its exact final gate block was:

   ```text
   == make test-mutations
   extra_axiom: rejected as required
   weakened_hypothesis: rejected as required
   Mutation suite passed. This is an infrastructure check, not a PDE proof.
   == check_contracts
     "base_compatibility_checked": true,
     "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
   }
   == gates OK
   ```

   The module-build portion ended `Build completed successfully (10089 jobs).`
   The `make test` portion printed only checked-contract lines, each ending
   `checked; standard logical axioms only`.

7. Explicit base compatibility check (run even though `verification/` was not
   touched):

   ```sh
   python3 experiments/check_contracts.py --base-ref origin/erenup/integration-section3
   ```

   Exit 0. Its 67,300-line output began with the 54-contract closure JSON and
   ended exactly:

   ```text
       ]
     },
     "base_compatibility_checked": true,
     "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
   }
   ```

8. Reviewer negative test:

   ```sh
   lake env lean ../research/T23/probes/rev486_lifespan_mutation.lean
   ```

   Exit 1 with the expected type mismatch quoted in Part 2. This is the
   intentional failing scratch probe, not a production failure.

No fix is required.
