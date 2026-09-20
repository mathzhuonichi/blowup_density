ACCEPT

## 1. What the lane claims

The worker claims a new identity-layer module for eq:Rcritical1, conditional on
the separately named critical carrier `hcrit` and trilinear estimate `htri`.
That is the correct scope of lane 175: the paper defines
`y = ‖Λ^(1/2)u‖₂`, `z = ‖Λ^(3/2)u‖₂`, and
`b = ‖f‖_{Ḣ^(1/2)}` at `paper/sections/04-whole-space.tex:91`, then states

```text
½(y²)' + (ν − C₀y)z² ≤ by
```

at `paper/sections/04-whole-space.tex:96-99`.  The implementation's public
definitions and all 16 public theorems exist where the report says they do:

- datum-infimum realization and the three real norms:
  `formalization/NSFormalization/Section4/R43/CriticalPairing.lean:43-91`;
- the three datum pairing statements, with exactly the reported hypotheses and
  conclusions: `CriticalPairing.lean:102-150`;
- `CriticalDatumPath`, `criticalEnergyPath`, `criticalEnergyDerivative`, and
  `CriticalTrilinearEstimate`: `CriticalPairing.lean:161-226`;
- the seven path/continuity/derivative identities: `CriticalPairing.lean:232-302`;
- `rcritical1_of_trilinear` with exactly the conjunction printed in the worker
  report: `CriticalPairing.lean:306-318`.

The report's spelling of `htri` is exact.  Lean has

```lean
∀ t ∈ Ioo (0 : ℝ) T,
  |⟪hcrit.advectionHalf t, hcrit.velocityHalf t⟫| ≤
    C₀ * ‖hcrit.velocityHalf t‖ * ‖hcrit.velocityThreeHalf t‖ ^ 2
```

at `CriticalPairing.lean:220-226`.  Since an order-`s` homogeneous datum is
`|ξ|^s û` in the manuscript's angular Fourier convention
(`formalization/NSFormalization/Section4/D01/HomogeneousWitness.lean:129-132`),
the inner product of the two order-`1/2` data is precisely
`⟨(u·∇)u, Λu⟩`.  Thus this is exactly
`|⟨(u·∇)u,Λu⟩| ≤ C₀ y z²`, not a weaker or stronger estimate.

The scalar conclusion is also exact: `CriticalPairing.lean:311-318` is token
for token the `henergy` expression in
`formalization/NSFormalization/Section4/R43/Pieces.lean:152-154` and
`formalization/NSFormalization/Paper1/ScalarEnergy.lean:130-133`.  The passing
probe composes the theorem directly into both consumers, without an adapter, at
`research/R43/probes/rev175_contract_shape.lean:12-27` and `:30-46`.

## 2. What is in Lean

### Audit of every `hcrit` field

`CriticalDatumPath` does not contain the desired pairing identities, the
trilinear estimate, the derivative of `y²`, or the scalar energy inequality.
Its fields have the following roles.

| Fields | Audit |
|---|---|
| `velocityHalf`, `velocityThreeHalf`, `laplacianHalf`, `advectionHalf`, `pressureHalf`, `forceHalf` (`CriticalPairing.lean:164-169`) | Carrier choices only. They assert no equality or estimate. |
| the six `*_isDatum` fields (`CriticalPairing.lean:170-184`) | Genuine open carrier obligations: they tie those choices to the physical velocity, Laplacian, advection, pressure gradient, and force at orders `1/2` or `3/2`. This is the missing homogeneous half-order bridge described at `formalization/NSFormalization/Section4/D01/HalfOrder.lean:40-53`. |
| `velocityHalf_smooth` (`CriticalPairing.lean:185`) | Genuine critical-path regularity. It is stronger than the `C¹` fact needed locally but natural for a classical solution. It does not assert `(y²)'`; that is derived using `A04.hasDerivAt_datumNormSq_of_contDiffOn` at `CriticalPairing.lean:241-247`, whose tree statement is `formalization/NSFormalization/Section4/A04/DerivNorm.lean:116-122`. |
| `momentum` (`CriticalPairing.lean:186-188`) | The genuinely missing transport of the physical momentum equation to the homogeneous order-`1/2` carrier. The existing theorem is only the unweighted carrier-B `toLp` equation (`formalization/NSFormalization/Section4/C01/MomentumCarrierB.lean:193-206`). It is not an energy or pairing conclusion. |
| `order_shift`, `laplacian_symbol` (`CriticalPairing.lean:189-196`) | Exact Fourier compatibility of the chosen data: `Z=|ξ|A` and `L=-|ξ|²A`. These are the carrier-level content needed to identify the three datum choices; neither field states `⟪L,A⟫=-‖Z‖²`. The latter is proved componentwise from the two symbols at `CriticalPairing.lean:102-132`. |
| `velocity_transverse`, `pressure_longitudinal` (`CriticalPairing.lean:197-201`) | Exact homogeneous Leray compatibility corresponding to divergence-free velocity and gradient pressure. They do not assert orthogonality. Orthogonality is derived through the self-adjoint Leray-complement lemma `formalization/NSFormalization/Section4/A04/PressureDrop.lean:155-165` at `CriticalPairing.lean:136-144`. The existing physical-to-datum transversality theorem is only at integer inhomogeneous order (`PressureDrop.lean:175-207`), so the half-order fields remain genuine bridge obligations. |

Accordingly, `rcritical1_of_trilinear` is neither vacuous nor a restatement of a
field of `hcrit`.  Once `hcrit` and `htri` are supplied, its final step is
necessarily scalar algebra, but the Laplacian and pressure identities are first
derived from lower-level symbol/projection compatibility
(`CriticalPairing.lean:319-364`).  This is exactly the intended identity layer.

The explicit `hf : MemForceR f` is proof-irrelevant as an index of `hcrit` (no
structure field inspects the proof term), but it is an honest ambient paper
assumption, not a hidden estimate.  The worker report says this plainly at
`research/R43/REPORT_175.md:83`.

### Pairings and non-vacuity

- Laplacian: `critical_laplacian_pairing` proves
  `⟪L,A⟫=-‖Z‖²` from the two exact a.e. symbols by reducing the real vector
  inner product to complex `L²` integrals (`CriticalPairing.lean:102-132`).  It
  does not assume the pairing.  The cited older Laplacian module really stops at
  derivative skew-adjointness and explicitly leaves datum assembly/order
  reconciliation open
  (`formalization/NSFormalization/Section4/D01/LaplacianPairing.lean:29-38`).
- Pressure: `critical_pressure_pairing` uses the datum-level Fourier Leray
  complement `formalization/NSFormalization/Section4/D01/LerayDatum.lean:251-268`
  and the self-adjointness consequence at `A04/PressureDrop.lean:160-165`; the
  path theorem obtains the longitudinal witness and applies the proved pairing
  (`CriticalPairing.lean:283-290`).
- Force: `critical_force_pairing` is exactly real Hilbert Cauchy--Schwarz
  (`CriticalPairing.lean:146-150`); homogeneous-datum uniqueness then rewrites
  both sides to `b(t)y(t)` (`CriticalPairing.lean:292-302`).

There is no `⊤.toReal = 0` escape in the main theorem.  On every time where a
norm is used, `hcrit` supplies a homogeneous datum (`CriticalPairing.lean:170-184`),
and uniqueness identifies the datum-infimum with its finite Hilbert norm
(`CriticalPairing.lean:64-91`).  Nor is the time interval empty:
`ClassicalSolutionR.horizon_pos` gives `0<T`
(`formalization/NSFormalization/Section4/A02/SolutionClass.lean:114-120`).

The conformance file constructs every field of `CriticalDatumPath` for the
genuine zero solution, including the actual zero homogeneous data and both
Fourier symbols (`research/R43/axioms_s1.lean:43-117`).  It then constructs
`htri` and instantiates both conclusions at the explicit interior time
`1 ∈ Ioo 0 2` (`axioms_s1.lean:119-137`).  Thus `CriticalDatumPath` is
satisfiable and the theorem is not vacuous.  I searched for a cheap non-flat
`ClassicalSolutionR` instance; the only explicit constructor in the Section4
tree is `A04.zeroSol` (`formalization/NSFormalization/Section4/A04/ZeroSolution.lean:87-105`).
Constructing the full non-flat `hcrit` would itself solve the named bridge gap,
so no such extra instance is cheaply available.  There is no sign of an
inconsistency: the tree constructs homogeneous data for arbitrary Schwartz and
smooth compactly supported fields
(`D01/HomogeneousWitness.lean:471-480`, `:513-528`), and the two symbol fields
are exactly the consistent identities for `|ξ|^s û`.

### Axioms and hygiene

All 16 theorem names in `research/R43/axioms_s1.lean:25-40` print exactly
`[propext, Classical.choice, Quot.sound]`.  Static search finds no declaration
using `sorry`, `admit`, `axiom`, or `native_decide`, and no `maxHeartbeats` in
either lane Lean file.  `git diff --check` is clean.

The base diff contains one new formalization module and research records only:

```text
formalization/NSFormalization/Section4/R43/CriticalPairing.lean
research/R43/ATTEMPTS_S1.md
research/R43/R43_SPLIT.md
research/R43/REPORT_175.md
research/R43/axioms_s1.lean
```

No existing Lean module was modified.  The sole existing record edit is the
brief-required update to the S1 rows (`research/R43/R43_SPLIT.md:61-77`).

## 3. Gaps

The report declares exactly two gaps, and both are honest.

1. S1b remains `htri : CriticalTrilinearEstimate (C₀ := C₀) hcrit`, exactly
   the paper's nonlinear estimate (`CriticalPairing.lean:218-226`).  The whole
   Section4 search returned only its definition and use:

   ```text
   $ grep -rn "CriticalTrilinearEstimate" formalization/NSFormalization/Section4
   formalization/NSFormalization/Section4/R43/CriticalPairing.lean:220:def CriticalTrilinearEstimate
   formalization/NSFormalization/Section4/R43/CriticalPairing.lean:310:    (htri : CriticalTrilinearEstimate (C₀ := C₀) hcrit) :
   ```

2. Construction of `hcrit` from `ClassicalSolutionR` and `MemForceR` remains
   open.  The whole-tree cross-search was empty:

   ```text
   $ grep -rnE "ClassicalSolutionR.*IsHomogeneousSliceDatum|IsHomogeneousSliceDatum.*ClassicalSolutionR" formalization/NSFormalization/Section4
   <no output; exit 1>
   $ grep -rnE "homogeneous.*momentum|momentum.*homogeneous" formalization/NSFormalization/Section4
   <no output; exit 1>
   ```

   The only whole-tree constructors found under the exact existence name are
   the Schwartz/compact constructors and their citations:

   ```text
   $ grep -rn "exists_isHomogeneousSliceDatum" formalization/NSFormalization/Section4
   formalization/NSFormalization/Section4/B02/LebesgueDatum.lean:23:*compact-smooth* fields (`exists_isHomogeneousSliceDatum`,
   formalization/NSFormalization/Section4/D01/HomogeneousWitness.lean:471:theorem exists_isHomogeneousSliceDatum {s : ℝ} (hs : -3 / 2 < s) (z : SpatialField)
   formalization/NSFormalization/Section4/D01/HomogeneousWitness.lean:489:  obtain ⟨B, hB, hnorm⟩ := exists_isHomogeneousSliceDatum hs z ψ hz
   formalization/NSFormalization/Section4/D01/HomogeneousWitness.lean:524:      exists_isHomogeneousSliceDatum hs z (compactSchwartzComponents hzs hzc) (fun _ _ => rfl)
   formalization/NSFormalization/Section4/D01/HalfOrder.lean:50:constructions (`Section4.D01.Homogeneous.exists_isHomogeneousSliceDatum`,
   ```

No additional gap or hidden premise was found.

## 4. Commands and results

All Lean commands were run after `. scripts/lean-env.sh`; all `lake` commands
were run from `verification/` with `LEAN_NUM_THREADS=6`.

1. Module build:

   ```text
   $ lake build NSFormalization.Section4.R43.CriticalPairing
   [replayed linter warnings from pre-existing dependencies only; none names CriticalPairing.lean]
   Build completed successfully (10200 jobs).
   ```

   Exit 0.  The exact final output line is shown; the replayed warnings are from
   such existing files as `Source/FiniteHilbertBochner.lean`,
   `Source/RealSobolev.lean`, and vendor `Formal/*`, not this lane.

2. Direct module typecheck:

   ```text
   $ lake env lean ../formalization/NSFormalization/Section4/R43/CriticalPairing.lean
   <no output>
   ```

   Exit 0.

3. Axiom/non-vacuity file:

   ```text
   $ lake env lean ../research/R43/axioms_s1.lean
   'NSFormalization.Section4.R43.isHomogeneousSliceDatum_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section4.R43.dotHomogeneousENorm_eq_of_isHomogeneousSlice' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section4.R43.criticalNormAt_eq_norm' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section4.R43.criticalDissipationAt_eq_norm' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section4.R43.criticalForceAt_eq_norm' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section4.R43.critical_laplacian_pairing' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section4.R43.critical_pressure_pairing' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section4.R43.critical_force_pairing' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section4.R43.criticalEnergyPath_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section4.R43.criticalEnergyPath_hasDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section4.R43.criticalNormAt_continuousOn' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section4.R43.criticalEnergyDerivative_hasDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section4.R43.criticalLaplacianPairing_path' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section4.R43.criticalPressurePairing_path' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section4.R43.criticalForcePairing_path' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section4.R43.rcritical1_of_trilinear' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

   Exit 0; the final example is silent and closes.

4. Exact consumer-shape probe:

   ```text
   $ lake env lean ../research/R43/probes/rev175_contract_shape.lean
   <no output>
   ```

   Exit 0.

5. Substantive negative mutation.  The probe changes the force-pairing
   Cauchy--Schwarz factor from `1` to `1/2`
   (`research/R43/probes/rev175_mutation_fail.lean:8-12`):

   ```text
   $ lake env lean ../research/R43/probes/rev175_mutation_fail.lean
   ../research/R43/probes/rev175_mutation_fail.lean:12:2: error: Type mismatch
     critical_force_pairing A F
   has type
     |⟪F, A⟫| ≤ ‖F‖ * ‖A‖
   but is expected to have type
     |⟪F, A⟫| ≤ 1 / 2 * ‖F‖ * ‖A‖
   ```

   Exit 1 as required.  This changes a numerical constant in a main identity;
   it does not merely omit an argument.

6. Repository gates:

   ```text
   $ make check
   python3 experiments/check_formalization_plan.py --check
   ...
   python3 experiments/test_contract_policy.py
   .............
   ----------------------------------------------------------------------
   Ran 13 tests in 0.049s

   OK
   python3 experiments/check_work_queue.py
   30 work items: ownership, contract registration and task cards consistent.
   ```

   Exit 0.  The elided middle is the command's generated 27-contract closure
   JSON (25,428 output lines); it reports
   `"base_compatibility_checked": false` because this invocation is the ordinary
   architecture check, as designed.

   ```text
   $ make test
   ℹ [10527/10528] Replayed Tests.TameProduct
   info: Tests/TameProduct.lean:14:0: Contract BlowupDensity.Tests.checkedTameProduct: checked; standard logical axioms only
   ℹ [10528/10528] Replayed Tests.EnergyAbsorptionPartialV3
   info: Tests/EnergyAbsorptionPartialV3.lean:41:0: Contract BlowupDensity.Tests.checkedEnergyAbsorptionPartialV3: checked; standard logical axioms only
   ```

   Exit 0 (exact tail; earlier output is replayed pre-existing warnings and
   successful contract checks).

   ```text
   $ make test-mutations
   implementation_refactor: accepted
   admitted_proof: rejected as required
   extra_axiom: rejected as required
   weakened_hypothesis: rejected as required
   Mutation suite passed. This is an infrastructure check, not a PDE proof.
   ```

   Exit 0.

7. Hygiene and conditional gates:

   ```text
   $ git diff --check
   <no output; exit 0>
   $ git diff --name-only origin/erenup/integration...HEAD | grep '^verification/'
   <no output; exit 1>
   ```

   Since `verification/` was not touched, the brief's conditional
   `scripts/gates.sh` and
   `python3 experiments/check_contracts.py --base-ref origin/erenup/integration`
   commands are not applicable.  Their constituent standard `make test` and
   `make test-mutations` gates were nevertheless rerun above.

Fixes: none.
