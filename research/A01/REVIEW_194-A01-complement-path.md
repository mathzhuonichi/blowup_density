ACCEPT

## 1. What the lane claims

The report claims two exported results: one fixed physical complement path with
`C^j_t H^m_x` datum paths for every pair `j,m`, plus a jointly smooth physical
representative of that complement path.  Those are the two names exported from
the nested namespace at
`formalization/NSFormalization/Section4/A01/ComplementPath.lean:662`.

The exact principal statement is present at
`formalization/NSFormalization/Section4/A01/ComplementPath.lean:629-646`:

```lean
theorem exists_complement_paths :
    ∃ w : ℝ → (Space → Space),
      (∀ j m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
        ContDiffOn ℝ j G (Icc (0 : ℝ) S) ∧
        ∀ t : Icc (0 : ℝ) S, IsSobolevDatum (m : ℝ) (w t.1) (G t.1)) ∧
      ∀ t : Icc (0 : ℝ) S, ∃ A : RealVectorSobolev 0,
        IsSobolevDatum 0 (⇑(residualCarrier hf hν hS a U hpairs t)) A ∧
        IsSobolevDatum 0 (w t.1) (lerayComplement 0 A)
```

This agrees with the report's quoted type at
`research/A01/REPORT_194.md:48-55` and with the brief.  In particular, the
quantifiers really are `∀ j m`, not `m ≤ 6`, and the identity is asserted at every
closed-interval time.

The exact joint-representative statement is present at
`formalization/NSFormalization/Section4/A01/ComplementPath.lean:649-657` and
agrees with `research/A01/REPORT_194.md:57-61`:

```lean
theorem exists_complement_joint_representative :
    ∃ G : A02.SpaceTimeField,
      ContDiffOn ℝ ∞ G (Ico (0 : ℝ) S ×ˢ (univ : Set Space)) ∧
      ∀ t : Icc (0 : ℝ) S, (fun x => G (t.1, x)) =ᵐ[volume]
        physicalComplement hf hν hS a U hpairs t.1
```

The mathematical sign and projection convention agrees with the paper: the
projected equation is at `paper/sections/02-preliminaries.tex:80-83`, while the
pressure/complement identity is at `paper/sections/02-preliminaries.tex:89-101`.
The lane deliberately forms the unprojected momentum residual and then applies
the datum-level Leray complement; its three-term formula is defined at
`formalization/NSFormalization/Section4/A01/ComplementPath.lean:28-36`.
The copied lane-189 definition and smoothness proof are indeed the same formulas
at `PressureRegularity.lean@erenup/189-A01-pressure-regularity:325-362`, and the
underlying projected residual/order-loss ladder is documented and proved at
`formalization/NSFormalization/Section4/A01/DatumPathSmooth.lean:194-232` and
`:236-280`.

## 2. What is in Lean

### Lead checkpoint 1: fixed residual versus all orders

The fixed carrier is exactly the order-six residual made from the `q = 7`
velocity realization (`q+1 = 8`) at
`formalization/NSFormalization/Section4/A01/ComplementPath.lean:528-534`.
It is not silently reused as a finite-order carrier for every `m`.

For each requested `j,m`, `residualCarrier_paths` independently sets
`k := max 6 m` and `q := k + 2 + 2*j`, then calls `hpairs q hq`
(`ComplementPath.lean:543-553`).  The finite theorem explicitly requires
`k + 2 + 2*j ≤ q+1` (`ComplementPath.lean:211-225`); its proof uses order
`k+1` for the product and order `k+2` for the Laplacian through the existing
cylinder regularity ladder (`ComplementPath.lean:226-237`).  After constructing
the order-`k` residual datum, the proof lowers it to arbitrary `m`
(`ComplementPath.lean:567-572`).  Finally, `residualOrdinaryPath_eq` identifies
that higher-order realization with the fixed order-six carrier using the common
velocity `U` and common force (`ComplementPath.lean:558-566`; comparison lemma
at `:269-304`).  Thus the order loss is honest and all `m` are supplied by the
all-`q` family.

The comparable existing tree theorem uses the same per-`(j,m)` strategy:
`datumPath_contDiffOn_all_orders` chooses a fresh high order at
`formalization/NSFormalization/Section4/A01/DatumPathSmooth.lean:715-734`.

### Lead checkpoint 2: exact residual slice and lane 195

In the main identity, `residualSlice t` is concretely
`⇑(residualCarrier ... t)`, the descended ordinary `L²` carrier
(`ComplementPath.lean:530-535`, `:634-646`), and its selected datum is
`orderZeroDatumCLM` of that carrier (`ComplementPath.lean:574-576`).

The requested physical bridge is proved here, not deferred to lane 197:

- `residualCarrier_physical` proves a.e. equality with the physical residual of
  any smooth representative of `U t` (`ComplementPath.lean:578-600`).
- `residualDatum_physical` transports the exact order-zero datum across that
  a.e. equality (`ComplementPath.lean:601-610`).
- `residualDatum_physicalSlice` states the result in standard velocity-field
  notation (`ComplementPath.lean:612-621`).

Lane 195's exact premise unfolds `momentumResidualOfVelocity` as
`(f - advection) + νΔu` (`formalization/NSFormalization/Section4/A01/ConstructorPressure.lean:50-53`),
whereas lane 194 prints the definitionally equal order
`νΔu + (f - advection)`.  This is only a commutativity normalization, not a
mathematical mismatch.  The consumer probe at
`research/A01/probes/rev194_lane195_bridge.lean:40-54` derives lane 195's exact
`hres` using `jointRepresentative_slice` and closes with:

```lean
simpa only [momentumResidualOfVelocity, add_comm] using hd
```

It typechecks with zero output.  Lane 197 is still responsible for its distinct
projected-cylinder/Fourier-projector comparison, not for this physical residual
datum bridge.

### Lead checkpoint 3: joint representative

No solenoidal carrier is fabricated.  Despite its historical namespace,
`EulerMeanSolenoidal.L2` is definitionally plain `Lp Space 2 volume`, not a
subtype (`vendor/NavierStokesAndEuler/Euler/MeanSolenoidalSpace.lean:16-22`).
`complementCarrier_joint` invokes the generic
`exists_joint_smooth_representative` directly
(`ComplementPath.lean:337-349`).  That generic theorem assumes only a continuous
plain-`L²` carrier and compatible datum paths
(`formalization/NSFormalization/Section4/A01/JointRepresentative.lean:548-563`).

Its construction fixes the order-two `vectorJointRepresentative`
(`JointRepresentative.lean:472-481`), proves every slice a.e. equal to the input
carrier (`:483-495`), and obtains all finite joint orders from higher datum paths
(`:499-546`).  Therefore the exported identities

```lean
∀ t : Icc 0 S, (fun x => G (↑t,x)) =ᵐ w t.1
ContDiffOn ℝ ∞ G (Ico 0 S ×ˢ univ)
```

are genuine, including the slice at `t = S`.

### Lead checkpoint 4: satisfiability and lane 192

The `hpairs` hypothesis at `ComplementPath.lean:514-526` is token-for-token the
all-order cylinder-pair conjunct exported by lane 192 at
`CylinderWiring.lean@9ca0a45:42-57`.  The direct import/consumer probe
`research/A01/probes/rev194_lane192_supply.lean:20-38` destructs
`cylinderPair_of_bounds` and passes its `hpairs` witness straight to
`exists_complement_paths`; it typechecks with zero output.  This lane predates
the merge of lane 192, so the review command used the merged `9ca0a45` olean
alongside the current lane's olean without altering either worktree.

The named hypotheses are ordinary restrictions: `MemForceR`, positive
viscosity, positive horizon, a smooth `L²` initial field, the common continuous
velocity carrier, and lane 192's standard cylinder realizations
(`ComplementPath.lean:508-526`).  The divergence conjunct is unused locally
(`:549`) but is retained only because the brief required lane 192's combined
export shape; it does not make the result vacuous.  There are no `.toReal`
bounds in this module and `hS : 0 < S` prevents an empty time interval.

The zero instance is genuine: it constructs the zero force and a zero
cylinder-pair witness at every order, applies the main supply theorem, and then
identifies the fixed residual with the zero physical residual
(`research/A01/axioms_complement_path.lean:62-125`).

### Lead checkpoint 5: hygiene and fidelity

All 38 nested declarations and both exported names are audited by 40
`#print axioms` commands (`axioms_complement_path.lean:5-45`), and every output
is exactly `[propext, Classical.choice, Quot.sound]`.  There is no
`sorry`, `admit`, `axiom`, or `native_decide` token in either changed Lean file.
Every `maxHeartbeats` setting is declaration-local, commented, and exactly
`400000` (`ComplementPath.lean:97-101`, `:169-173`, `:239-243`, `:266-270`,
`:388-391`; `axioms_complement_path.lean:62-65`).

`git diff --name-only origin/erenup/integration...HEAD` shows one formalization
file, and `git cat-file` confirms it did not exist on the base.  No pre-existing
Lean module was modified.  The report's theorem quotations and the stated count
of declarations agree with the source (`research/A01/REPORT_194.md:47-91`,
`:93-104`).

## 3. Gaps

There is no blocking gap in this lane.  The report does not make a "not in the
tree" claim; it only scopes pressure-potential and projected-momentum assembly
to later work (`research/A01/REPORT_194.md:106-109`).  The required whole-tree
search was nevertheless run:

```text
$ grep -rn --include='*.lean' -E 'physicalResidual_datum_eq|residualDatum_physicalSlice|hprojected_of_cylinder|lowered_projected_datum_of_cylinder|pressure potential|projected momentum' formalization/NSFormalization/Section4
formalization/NSFormalization/Section4/A04/MomentumDatum.lean:9:(`Spec.lean` `energyIdentityHigh`) pairs the projected momentum equation
formalization/NSFormalization/Section4/C01/EnergyIdentity.lean:11:`Section4/A04/EnergyIdentityHigh.lean`): the projected momentum equation paired
formalization/NSFormalization/Section4/A01/ComplementPath.lean:613:theorem residualDatum_physicalSlice (velocity : A02.SpaceTimeField)
formalization/NSFormalization/Section4/A01/RadialPotential.lean:9:# A01 · unit P1: the radial pressure potential differentiates back to its gradient
formalization/NSFormalization/Section4/A01/DatumPathDeriv.lean:88:/-- The projected momentum residual is continuous in every available order. -/
formalization/NSFormalization/Section4/A01/DatumPathDeriv.lean:98:/-- The order-`m` cylinder right-hand side of the projected momentum equation. -/
```

The substantive negative check widens the main theorem's time regularity
interval from `[0,S]` to `[-1,S]`
(`research/A01/probes/rev194_mutation_fail.lean:35-45`).  Reusing the production
proof fails for precisely that mutation:

```text
../research/A01/probes/rev194_mutation_fail.lean:45:2: error: Type mismatch
  exists_complement_paths hf hν hS a U hpairs
has type
  ∃ w,
    (∀ (j m : ℕ), ∃ G, ContDiffOn ℝ (↑j) G (Icc 0 S) ∧ ∀ (t : ↑(Icc 0 S)), IsSobolevDatum (↑m) (w ↑t) (G ↑t)) ∧
      ∀ (t : ↑(Icc 0 S)),
        ∃ A,
          IsSobolevDatum 0 (↑↑((residualCarrier hf hν hS a U hpairs) t)) A ∧
            IsSobolevDatum 0 (w ↑t) ((Leray.lerayComplement 0) A)
but is expected to have type
  ∃ w,
    (∀ (j m : ℕ), ∃ G, ContDiffOn ℝ (↑j) G (Icc (-1) S) ∧ ∀ (t : ↑(Icc (-1) S)), IsSobolevDatum (↑m) (w ↑t) (G ↑t)) ∧
      ∀ (t : ↑(Icc 0 S)),
        ∃ A,
          IsSobolevDatum 0 (↑↑((residualCarrier hf hν hS a U hpairs) t)) A ∧
            IsSobolevDatum 0 (w ↑t) ((Leray.lerayComplement 0) A)
```

## 4. Commands and results

Every Lean command was run after `. scripts/lean-env.sh`, from
`verification/`, with `LEAN_NUM_THREADS=6`.

```text
$ lake build NSFormalization.Section4.A01.ComplementPath
⚠ [8777/9529] Replayed NSFormalization.Source.FiniteHilbertBochner
...
⚠ [10180/10242] Replayed NSFormalization.Paper3.SobolevDirectionalDerivative
Build completed successfully (10242 jobs).
```

The omitted middle lines are replayed warnings from existing dependencies; the
exact warning locations include `FiniteHilbertBochner.lean:23-24,39`,
`RealSobolev.lean:90`, and vendor files.  There is no diagnostic from
`ComplementPath.lean`.  The brief's silent form was checked separately:

```text
$ lake -q --log-level=error build NSFormalization.Section4.A01.ComplementPath
<no output; exit 0>

$ lake env lean ../formalization/NSFormalization/Section4/A01/ComplementPath.lean
<no output; exit 0>
```

The axioms/non-vacuity file succeeds.  It emits 40 instances of this exact
axiom list (one for every `#print axioms` at
`axioms_complement_path.lean:5-45`) and nothing else:

```text
$ lake env lean ../research/A01/axioms_complement_path.lean
'NSFormalization.Section4.A01.ComplementPath.unprojectedResidualPath' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
...
'NSFormalization.Section4.A01.ComplementPath.exists_complement_joint_representative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

The two positive probes have exact zero output:

```text
$ lake env lean ../research/A01/probes/rev194_lane195_bridge.lean
<no output; exit 0>

$ lake env env LEAN_PATH="$lane194_overlay:$lane194_lean_path" lean ../research/A01/probes/rev194_lane192_supply.lean
<no output; exit 0>
```

`make check` exits 0.  Its exact non-bulk terminal results are:

```text
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.042s

OK
python3 experiments/check_work_queue.py
30 work items: ownership, contract registration and task cards consistent.
```

The full gate wrapper, including mutation tests and base compatibility, exits 0:

```text
$ BASE_REF=origin/erenup/integration scripts/gates.sh NSFormalization.Section4.A01.ComplementPath
== make check
...
== lake build NSFormalization.Section4.A01.ComplementPath
Build completed successfully (10242 jobs).
== make test
info: Tests/Thresholds.lean:13:0: Contract BlowupDensity.Tests.checkedThresholds: checked; standard logical axioms only
...
info: Tests/EnergyAbsorptionV4.lean:100:0: Contract BlowupDensity.Tests.energyAbsorptionV4_terminalFinite: checked; standard logical axioms only
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

Hygiene commands:

```text
$ git diff --name-only origin/erenup/integration...HEAD
formalization/NSFormalization/Section4/A01/ComplementPath.lean
research/A01/A3_SPLIT.md
research/A01/ATTEMPTS_COMPLEMENT_PATH.md
research/A01/REPORT_194.md
research/A01/axioms_complement_path.lean

$ rg -n '\b(sorry|admit|axiom|native_decide)\b' <changed Lean files>
<no output; exit 1 as expected>

$ git diff --check origin/erenup/integration...HEAD
<no output; exit 0>
```

Fixes required: none.
