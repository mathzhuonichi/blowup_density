ACCEPT-WITH-NOTES

## 1. What the lane claims

The lane claims one fixed space-time field whose slices represent `U` almost
everywhere and which is jointly smooth, first on the stronger closed slab and
then on the requested half-open slab.  The exact public statements in the
worker report agree with the source:

- `scalarJointRepresentative_contDiffOn` has precisely the stated inputs
  `n s S hS horder G hG` and the closed-slab `C^n` conclusion
  (`formalization/NSFormalization/Section4/A01/JointRepresentative.lean:283`).
- `jointRepresentative`, `jointRepresentative_slice`, and
  `jointRepresentative_contDiffOn` have the reported all-`j,m` `hpaths`
  interface and conclusions (`JointRepresentative.lean:475`,
  `JointRepresentative.lean:485`, `JointRepresentative.lean:538`).
- `exists_joint_smooth_representative` concludes, in the reported order,
  `∃ u, (∀ t : Icc 0 S, slice u t =ᵐ ⇑(U t)) ∧ ContDiffOn ℝ ∞ u
  (Ico 0 S ×ˢ univ)` (`JointRepresentative.lean:552`).
- `exists_joint_smooth_representative_of_hall` has the lane-178 `hall`
  premise verbatim and the same packaged conclusion
  (`JointRepresentative.lean:572`; the producer is
  `formalization/NSFormalization/Section4/A01/DatumPathSmooth.lean:715`).

This is faithful to the R4 brief.  The cited manuscript passage actually says
that all spatial Sobolev orders, the projected equation, and repeated time
differentiation give every `C^j_t H^k_x` order and the initial one-sided
derivatives (`paper/sections/appendix-a-local-theory.tex:66` and
`paper/sections/appendix-a-local-theory.tex:71`).  The implementation consumes
exactly that property as `hpaths`; it does not assume a smooth representative
as an input.

The representative is not a `Classical.choose` made independently at every
slice.  `jointRepresentative` chooses one entire order-2 datum path and applies
`vectorJointRepresentative` to it (`JointRepresentative.lean:475`).  Point
evaluation comes from the continuous-linear
`angularBoundedRepresentative`/`evalCLM` construction
(`formalization/NSFormalization/Paper3/AngularTameProduct.lean:140`,
`JointRepresentative.lean:256`).  At joint order `n`, the proof chooses one
order-`n+2` datum path (`JointRepresentative.lean:518`) and proves joint
regularity by transferring the path's `derivWithin` in time and the
continuous-linear angular derivative in space
(`JointRepresentative.lean:303`, `JointRepresentative.lean:318`,
`JointRepresentative.lean:359`).  The order-2 and order-`n+2`
representatives are both a.e. equal to the same `U t`, hence their continuous
representatives agree everywhere (`JointRepresentative.lean:415`,
`JointRepresentative.lean:442`, `JointRepresentative.lean:457`).  Thus this is
one field, not an unrelated family indexed by regularity order.

Endpoint handling is honest.  The successor proof uses `derivWithin` on
`Icc 0 S`, `uniqueDiffOn_Icc hS`, and
`HasFDerivWithinAt`; it never replaces the within derivative by an ambient
`fderiv` of the time path (`JointRepresentative.lean:303`,
`JointRepresentative.lean:359`, `JointRepresentative.lean:363`).  The only
ambient `HasFDerivAt` used there is in the unrestricted spatial variable
(`JointRepresentative.lean:374`).  This covers both `t = 0` and `t = S` and is
consistent with the domain of `hpaths`.

The slice identity also follows through the intended chain.  `hpaths 0 2`
supplies `IsSobolevDatum 2 (⇑(U t)) ...`, and
`jointRepresentative_slice` passes it to `vectorRepresentative_ae`
(`JointRepresentative.lean:491`).  The latter is componentwise A03
`representative_ae` (`JointRepresentative.lean:415` and
`formalization/NSFormalization/Section4/A03/ScalarTameProduct.lean:156`).

The final named inputs are satisfiable restrictions of standard properties:

- `hS : 0 < S` is the usual restriction to a positive local horizon.
- `U` is the ordinary solution path restricted to `Icc 0 S`, not an extra
  predicate.
- `hpaths` is the restriction to `Icc 0 S` of the standard all-order
  `C^j_t H^m_x` property of a smooth solution.
- `hν : 0 < ν` is the standard positive-viscosity restriction.
- `hall` is the compatible all-order cylinder realization of the same `U`,
  restricted to the common horizon.

These are also documented next to the theorems
(`JointRepresentative.lean:548` and `JointRepresentative.lean:565`).  There
is no `⊤.toReal`, empty-interval device, clamped post-horizon carrier, or unused
mathematical hypothesis.  The explicit `U := 0`, `S := 1` instance is genuine
and was re-typechecked (`research/A01/axioms_b1_r4.lean:38`).

## 2. What is in Lean

The finite-order engine first proves the spatial derivative formula by density
and uniform convergence (`JointRepresentative.lean:163`), then inducts jointly
in time and space on the closed slab (`JointRepresentative.lean:283`).  Vector
reassembly is componentwise (`JointRepresentative.lean:383`), and cross-order
compatibility is isolated in
`vectorRepresentative_eq_of_datums`/`vectorJointRepresentative_eqOn_of_datums`
(`JointRepresentative.lean:442` and `JointRepresentative.lean:454`).  Finally,
all finite orders are assembled with `contDiffOn_infty`
(`JointRepresentative.lean:538`).

All requested interfaces typecheck in
`research/A01/probes/rev190_interfaces.lean`:

- lane 180's consumer pattern `⟨velocity, hslice, hc3⟩` compiles unchanged
  (`rev190_interfaces.lean:15`); its target consumes exactly `hslice` and
  `hc3` at `ConstructorAssembly.lean:228` and `ConstructorAssembly.lean:234`
  on branch `erenup/180-A01-b2-assembly`;
- lane 178's `hall` is accepted token-for-token
  (`rev190_interfaces.lean:41`);
- lane 192's all-`j,m` fourth output from `cylinderPair_of_bounds` plugs
  directly into `hpaths` (`rev190_interfaces.lean:29`; on branch
  `erenup/192-A01-wiring-hsob`, `CylinderWiring.lean:55`).  In contrast, the
  narrower constructor-shaped export `constructorInputs_of_bounds` deliberately
  retains only `hsob 0`, so that particular projection alone is not `hpaths`
  (`CylinderWiring.lean:148` on that branch).

The interval-widening mutation in
`research/A01/probes/rev190_widen_interval.lean:11` changes the main closed
slab from `Icc 0 S` to `Icc (-1) S`.  It fails exactly because the proof only
has regularity on the interval controlled by `hpaths`:

```text
../research/A01/probes/rev190_widen_interval.lean:20:2: error: Type mismatch
  jointRepresentative_contDiffOn hS U hpaths
has type
  ContDiffOn ℝ ∞ (jointRepresentative U hpaths) (Icc 0 S ×ˢ univ)
but is expected to have type
  ContDiffOn ℝ ∞ (jointRepresentative U hpaths) (Icc (-1) S ×ˢ univ)
```

Hygiene is clean in the delivered Lean.  There are 26 declarations in the new
module and 26 matching `#print axioms` commands
(`research/A01/axioms_b1_r4.lean:11`); every result is exactly
`[propext, Classical.choice, Quot.sound]`.  Searches found none of
`sorry`, `admit`, `axiom`, `native_decide`, or `set_option maxHeartbeats` in
the new module or axiom file.  Thus the development-time timeout mentioned in
the report left no override.  The branch diff adds the one formalization module
and records only; it modifies no pre-existing Lean module and touches nothing
under `verification/`.

## 3. Gaps and notes

There is no R4 Lean or mathematical gap in this lane.  The current checkout's
whole-`Section4` search for the worker's upstream discussion found
`compatible_carriers_hall`, its uniqueness-discharged version
`compatible_carriers_hall'`, and `mildUniqueness`
(`formalization/NSFormalization/Section4/A01/CommonHorizon.lean:224`,
`formalization/NSFormalization/Section4/A01/MildUniqueness.lean:186`, and
`formalization/NSFormalization/Section4/A01/MildUniqueness.lean:233`).  On this
branch they still take force-path smoothness as `hfs`; the whole-tree search
finds consumers of that premise but no producer.  Lane 192's
`forcePath_sobolevPath_contDiffOn` and `cylinderPair_of_bounds` supply it and
then export the all-`j,m` `hsob` directly.  Therefore lane 192 composes with
this lane without an adapter.

Two pre-existing sentences in the touched ladder record are stale, but neither
affects the code or R4 row:

1. `research/A01/B1_LADDER.md:117` says `MildUniqueness` is still unproved,
   contradicted by `MildUniqueness.lean:186` in this checkout.
2. `research/A01/B1_LADDER.md:137` says this checkout lacks
   `ConstructorPieces.lean`, but that module is present at
   `formalization/NSFormalization/Section4/A01/ConstructorPieces.lean:1`.

Exact one-line documentation fixes are listed after the command results.

## 4. Commands and results

All Lake commands ran from `verification/` after `. ../scripts/lean-env.sh`
with `LEAN_NUM_THREADS=6`.

1. `lake build NSFormalization.Section4.A01.JointRepresentative`

   Exit 0.  Lake replayed warnings only from dependencies; no diagnostic named
   `JointRepresentative.lean`.  The exact final output was:

   ```text
   Build completed successfully (10028 jobs).
   ```

   The replay headers named
   `NSFormalization.Source.FiniteHilbertBochner`,
   `Formal.R3LerayFrequencySymbol`, `NSFormalization.Source.RealSobolev`,
   `NSFormalization.Paper3.SpatiallyCompactTime`,
   `NSFormalization.Paper3.RealPositiveDensity`,
   `NSFormalization.Paper3.RealVectorPositiveDensity`,
   `Formal.R3StokesL2Operator`, `Formal.R3L2ScalarAux`,
   `Formal.FlowMapNonextendibilityCriterion`,
   `Formal.UniformRestartContinuation`, `Formal.R3SobolevCarrier`,
   `Formal.R3CoordinateLinearAux`, `Formal.R3DivergencePointwise`,
   `Formal.R3LerayL2Operator`, `Formal.R3LerayFourierBridge`,
   `Formal.R3LerayComplexFiberSymbol`,
   `NSFormalization.Source.PhysicalBesselSobolev`,
   `NSFormalization.Source.PacketForceExtension`,
   `NSFormalization.Source.ViscosityPacket`, and
   `NSFormalization.Paper3.SobolevDirectionalDerivative`.

2. `lake env lean ../formalization/NSFormalization/Section4/A01/JointRepresentative.lean`

   Exit 0, exact output: empty.

3. `lake env lean ../research/A01/axioms_b1_r4.lean`

   Exit 0.  It printed one line for each of the 26 declarations from
   `boundedEvaluation_hasFDerivWithinAt` through
   `exists_joint_smooth_representative_of_hall`; every line ended in the exact
   set:

   ```text
   depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

4. `lake env lean ../research/A01/probes/rev190_interfaces.lean`

   Exit 0, exact output: empty.

5. `lake env lean ../research/A01/probes/rev190_widen_interval.lean`

   Exit 1 with the exact expected error pasted in Part 2.

6. `make check` from the worktree root

   Exit 0.  The command emitted the registry's large dependency-closure JSON.
   Its exact architecture notices and final checks were:

   ```text
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
   ...
   "base_compatibility_checked": false,
   "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
   }
   .............
   ----------------------------------------------------------------------
   Ran 13 tests in 0.044s

   OK
   30 work items: ownership, contract registration and task cards consistent.
   ```

   The copied-source notice is pre-existing and outside this lane.

7. `git diff --name-only origin/erenup/integration...HEAD`

   Exit 0, exact committed output:

   ```text
   formalization/NSFormalization/Section4/A01/JointRepresentative.lean
   research/A01/ATTEMPTS_B1_R4.md
   research/A01/B1_LADDER.md
   research/A01/REPORT_190.md
   research/A01/axioms_b1_r4.lean
   ```

   `git diff --name-only --diff-filter=M ... -- '*.lean'` and
   `git diff --name-only ... -- verification` both produced no output.
   `git diff --check origin/erenup/integration...HEAD` also exited 0 with no
   output.

8. `grep`/`rg` hygiene and missing-lemma audit

   The forbidden-token/max-heartbeat search on the new Lean files produced no
   output.  The whole `formalization/NSFormalization/Section4` audit produced
   the candidates cited in Part 3, rather than accepting the stale ladder
   claim.  Since the committed diff does not touch `verification/`, the
   conditional `scripts/gates.sh` and
   `check_contracts.py --base-ref origin/erenup/integration` gates were not
   applicable.

Fixes required before treating the records as current (one line each):

1. In `research/A01/B1_LADDER.md:117`, replace “此唯一性尚未证明” with
   “lane 188 已证明 `mildUniqueness`; 本分支剩余供给是 `hfs`，lane 192 将其由
   `MemForceR` 导出并给出全 `j,m` 的 `hsob`”.
2. In `research/A01/B1_LADDER.md:137`, delete the sentence claiming this
   checkout lacks `ConstructorPieces.lean` (the module is present).
