ACCEPT

## 1. What the lane claims

The lane claims the two carrier constructions requested for R43:

1. for an `H^∞` real vector field `v`, a physical field `rieszLambda v hv`
   realizing the manuscript multiplier `Λ = (-Δ)^(1/2)`, remaining in
   `MemHInfty`, with every supplied order-`3/2` datum `Z` of `v` serving as the
   order-`1/2` datum of `rieszLambda v hv`; and
2. for every coordinate `j`, an order-`1/2` datum of `dirDeriv j v` whose
   component symbol is exactly R43's `rieszCoordinateSymbol j ξ * Zᵢ ξ`.

This is the mathematics used in the paper.  The paper fixes
`Λ = (-Δ)^(1/2)` at `paper/sections/02-preliminaries.tex:50-55`, then at
`paper/sections/04-whole-space.tex:90-98` sets
`y = ‖Λ^(1/2)u‖₂`, `z = ‖Λ^(3/2)u‖₂`, and tests against `Λu`; the
critical embedding explicitly contains `‖∇u‖₃ + ‖Λu‖₃` at
`paper/sections/04-whole-space.tex:91-95`.

Every main declaration quoted by `research/A05/REPORT_191.md` exists with the
reported type:

- `rieszLambda` is at
  `formalization/NSFormalization/Section4/A05/RieszShift.lean:444-449`;
- `rieszLambda_memHInfty` is at `RieszShift.lean:466-473`;
- `rieszLambda_halfDatum` is at `RieszShift.lean:732-739`;
- `derivativeHalfDatum` and its exact multiplier identity are at
  `RieszShift.lean:831-842`;
- `derivativeHalfDatum_isDatum` is at `RieszShift.lean:955-964`;
- `shiftedCriticalData_of_memHInfty` is at `RieszShift.lean:966-977`; and
- `criticalAdvectionLpBridge_shifted` is at
  `formalization/NSFormalization/Section4/R43/ShiftedData.lean:23-41`.

The last two declarations are correctly `noncomputable def`s rather than
`theorem`s: their codomains are Type-valued structures/functions, not
propositions.  Their types are otherwise exactly the interfaces requested by
the brief; no mathematical hypothesis was added.

There is no vacuous `ENNReal.toReal` conclusion, empty-interval escape, or
unused named hypothesis in these statements.  The core constructor uses both
`hv` and `hZ` at `RieszShift.lean:971-977`.  The slice wrapper's interior
interval is genuine because `ClassicalSolutionR.horizon_pos : 0 < T` is a
structure field at `Section4/A02/SolutionClass.lean:114-120`.

## 2. What is in Lean

### U4: the physical `Λv`

The lane does not use `Source.FractionalRealization.realization` as its final
physical representative.  That tree theorem realizes the original Sobolev
distribution in its critical `Lᵖ` space for `0 < a < 3/2`
(`Source/FractionalRealization.lean:44-52,76-93`), while
`Source.BesselFractionalData.datum` supplies the frequency datum
`|ξ|^a⟨ξ⟩^(-a)h` (`Source/BesselFractionalData.lean:12-13,45-53`).
Instead, the lane takes an equally direct all-order route:

- it defines the fixed real `L²` class
  `rieszLambdaL2 v hv = -∑ⱼ Rⱼ(∂ⱼv)` at `RieszShift.lean:415-420`;
- the exact R43 symbol is
  `if ξ = 0 then 0 else I * (ξ j / ‖ξ‖)` at
  `Section4/R43/Trilinear.lean:45-49`;
- the Mathlib cycles-frequency derivative factor is
  `(2π I) * ξⱼ` at `RieszShift.lean:390-409`; and
- the sign and constant computation
  `-∑ⱼ (Iξⱼ/|ξ|)(2πIξⱼ) = frequencyUnit * |ξ|`
  is proved at `RieszShift.lean:475-492`, then propagated to the component
  Fourier classes at `RieszShift.lean:494-607`.

Normalized angular dilation removes `frequencyUnit = 2π`, giving exactly the
manuscript multiplier `|ξ|` at `RieszShift.lean:695-730`.  Thus this is the
required `L²` field with Fourier transform `|ξ| v̂`, not merely an abstract
field having a compatible norm.

No order or decay assumption is lost in `rieszLambda_memHInfty`.  The input
`MemHInfty` is first converted to square-integrable jets of every order by
`D01.memHInfty_jets` (`Section4/D01/DatumToJets.lean:284-292`) in
`sourceSmoothField` (`RieszShift.lean:411-413`).  One directional derivative is
taken, but the input tower contains all orders.  Translation-commutation then
gives a smooth orbit for the Riesz-transformed `L²` class
(`RieszShift.lean:422-442`), and the tree's
`EulerMeanSmoothRepresentative.smoothL2Field` supplies a smooth representative
with all tensor jets in `L²`
(`vendor/NavierStokesAndEuler/Euler/MeanOrbitSmoothL2Field.lean:35-52`).
Finally `memHInfty_of_contDiff_memLp` packages those jets at
`RieszShift.lean:468-473`.  There is no compact-support, `L¹`, or additional
decay premise.

`rieszLambda` is extensionally canonical.  The upstream representative is
implemented with `Classical.choose` at
`vendor/NavierStokesAndEuler/Euler/MeanSmoothRepresentative.lean:78-87`, but
`representative_unique` proves that any continuous representative of the fixed
`L²` class is equal to it at `:97-101`, while `smoothL2Field_toLp` pins it to
that class at `Euler/MeanOrbitSmoothL2Field.lean:49-52`.  Hence the choice cannot
differ from the Fourier class used in the later datum proof.  It is not a
choice from a datum existential, and proof irrelevance removes dependence on
which proof of `hv` is supplied.

### U4 datum identity and the `3/2` endpoint

The tree definition says exactly that an order-`s` datum represents
`|ξ|^s û`: `IsHomogeneousDatum` uses
`|ξ|^(-s) G` at `Section4/D01/HomogeneousWitness.lean:234-240`, and the
slice/vector wrappers are at `:245-253`.  The lane first aligns the supplied
slice distribution with the canonical physical `L²` distribution using
`isSliceDistribution_unique`, then proves

```text
angularVHat_i(ξ)      = |ξ|^(-3/2) Z_i(ξ)
angularLambdaHat_i(ξ) = |ξ| angularVHat_i(ξ)
                         = |ξ|^(-1/2) Z_i(ξ)
```

at `RieszShift.lean:740-792`.  This uses the supplied `Z` itself; it does not
select a second order-`3/2` datum and compare the two.  Consequently no special
U1 endpoint theorem is needed.  For completeness, the generic datum uniqueness
theorem really is valid at every real `s`, with no excluded `3/2` endpoint, at
`HomogeneousWitness.lean:320-353`.

### U8: derivative sign, `I`, and exact consumer field

The consumer field is token-for-token

```lean
fun ξ => rieszCoordinateSymbol j ξ * (Z i : FourierData) ξ
```

at `Section4/R43/Trilinear.lean:78-81`, and the producer has that same expression
at `RieszShift.lean:837-842`.  R43 defines the nonzero symbol as
`I * (ξ j / ‖ξ‖)` at `Trilinear.lean:47-48`.

The sign and imaginary factor agree with the tree convention.  The underlying
cycles-frequency identity is
`ℱ(∂_a φ) = (2π I) (ξ·a) ℱφ` at
`Paper3/SobolevDirectionalDerivative.lean:89-116`.  The lane proves that
angular dilation cancels `2π`, leaving `I ξⱼ`, at
`RieszShift.lean:862-897`; combining this with the order weights gives the
positive symbol `Iξⱼ/|ξ|` at `RieszShift.lean:910-953` and the actual
physical derivative datum at `:957-964`.  A wrong sign or omitted `I` would not
satisfy the proved statement.

### Classical velocity slices and the remaining bridge field

`criticalAdvectionLpBridge_shifted` uses exactly the two appropriate facts:

- `C01.velocity_slice_memHInfty` at
  `Section4/C01/VelocityJets.lean:65-81`, derived from
  `ClassicalSolutionR.velocity_smooth` and the datum half of `.sobolev` at
  `VelocityJets.lean:62-73`; and
- `hcrit.velocityThreeHalf_isDatum` on `Ico 0 T` at
  `Section4/R43/CriticalPairing.lean:161-173`.

At `ShiftedData.lean:35-41`, an `Ioo 0 T` witness is honestly converted to
`Ico 0 T` for both facts.  No endpoint or interval mismatch is hidden.

`CriticalAdvectionLpBridge` has exactly two fields at
`Section4/R43/Trilinear.lean:298-310`.  This lane supplies all of `shifted`; the
one-line HANDOFF statement still to prove is precisely

```lean
⟪hcrit.advectionHalf t, hcrit.velocityHalf t⟫ =
  ∫ x, inner ℝ
    (advection (C01.lift (fun y => w.velocity (t, y))) 0 x)
    ((criticalAdvectionLpBridge_shifted hcrit t ht).lambda x)
```

for every `t` and `ht : t ∈ Ioo 0 T`.  This is a fractional
Parseval/duality identity only; it contains no estimate.

### Non-vacuity, axioms, and hygiene

The nonzero audit is genuine.  It defines
`zB x = Cut.bump x • coordinateVector 0` at
`research/A05/axioms_u4_u8.lean:28-29`, proves smoothness, compact support,
`MemHInfty`, and `zB ≠ 0` at `:31-51`, and obtains an actual order-`3/2`
datum from `isHomogeneousSliceDatum_compact` at `:53-57`.  The tree theorem
constructing that datum is at
`Section4/D01/HomogeneousWitness.lean:513-525`.  The lane then instantiates
`shiftedCriticalData_of_memHInfty` with this proved datum at
`axioms_u4_u8.lean:61-67`.  This is not a zero-only or empty-existential test.

The axiom audit contains 73 declarations from the two new modules plus six
non-vacuity declarations, 79 `#print axioms` commands in total
(`axioms_u4_u8.lean:85-165`).  All 79 report exactly
`[propext, Classical.choice, Quot.sound]`.  In particular, the two Type-valued
definitions have no hidden proof obligation discharged by an extra axiom.

Static search finds no `sorry`, `admit`, `axiom`, `native_decide`, or
`set_option maxHeartbeats` in either new module.  Both formalization files are
new relative to `origin/erenup/integration`; no pre-existing Lean module was
modified.  No `verification/` path was touched.

## 3. Gaps

The worker's only residual claim is correct: the fractional `pairing_identity`
above is not in the tree.  I searched the whole
`formalization/NSFormalization/Section4` tree, not only A05/R43.  The exact
relevant output was:

```text
formalization/NSFormalization/Section4/R43/Trilinear.lean:297:It contains no inequality.  Constructing `shifted` requires the unexported A05 U4/U8 carriers (plus `MemHInfty` closure for `Λu`), while `pairing_identity` is a separate fractional Parseval/duality obligation. -/
formalization/NSFormalization/Section4/R43/Trilinear.lean:305:  pairing_identity : ∀ t (ht : t ∈ Ioo (0 : ℝ) T),
formalization/NSFormalization/Section4/R43/Trilinear.lean:368:    rw [hbridge.pairing_identity t ht]
formalization/NSFormalization/Section4/R43/ShiftedData.lean:9:independent fractional Parseval field `pairing_identity` remains open.
```

Broader searches for `Parseval`, `Plancherel`, `advectionHalf`, and
`velocityHalf` found only order-zero/integer identities or the declarations and
uses above; none proves the needed fractional physical integral identity.  The
same search was also run over `Source/`, `Paper1/`, and `Paper3/`; their only
Parseval matches are unrelated generic, order-zero, or periodic results.

The substantive negative probe is
`research/A05/probes/rev191_symbol_sign.lean:17-22`.  It flips the sign of the
main U8 multiplier without dropping any argument.  The unchanged proof fails
exactly as expected:

```text
../research/A05/probes/rev191_symbol_sign.lean:22:2: error: Type mismatch
  derivativeHalfDatum_symbol j i Z
has type
  ↑↑↑((derivativeHalfDatum j Z).ofLp i) =ᵐ[volume] fun ξ =>
    NSFormalization.Section4.R43.rieszCoordinateSymbol j ξ * ↑↑↑(Z.ofLp i) ξ
but is expected to have type
  ↑↑↑((derivativeHalfDatum j Z).ofLp i) =ᵐ[volume] fun ξ =>
    -NSFormalization.Section4.R43.rieszCoordinateSymbol j ξ * ↑↑↑(Z.ofLp i) ξ
```

There is no U4/U8 gap requiring a fix to this lane.  The broader all-order
`IsRieszPower` API mentioned in `research/A05/COMPARISON.md:208` remains outside
this lane's requested R43 carrier interface.

## 4. Commands and results

All Lean commands were run from `verification/` after sourcing
`scripts/lean-env.sh`, with `LEAN_NUM_THREADS=6`.

Module builds:

```text
$ LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.A05.RieszShift
RieszShift target diagnostics=0
Build completed successfully (10266 jobs).

$ LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.R43.ShiftedData
ShiftedData target diagnostics=0
Build completed successfully (10267 jobs).
```

Both raw build invocations exit `0`.  Lake replays linter warnings from
pre-existing dependencies (`FiniteHilbertBochner`, `RieszPotentialNearField`,
`RealSobolev`, several Paper3 modules, and vendor Formal modules); the exact
target-diagnostic projection above confirms that neither new module emits a
warning or error.

Direct typechecks:

```text
$ LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section4/A05/RieszShift.lean
<no output>
exit_code=0

$ LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section4/R43/ShiftedData.lean
<no output>
exit_code=0
```

Axiom and non-vacuity file:

```text
$ LEAN_NUM_THREADS=6 lake env lean ../research/A05/axioms_u4_u8.lean
exit_code=0
```

Its output has 79 declarations; every individual line is of the exact form

```text
'<declaration>' depends on axioms: [propext, Classical.choice, Quot.sound]
```

(with Lean line-wrapping only).  The independent exact-output validator gives:

```text
exit_code=0
axiom_results=79 exact_standard=79 mismatches=0
```

The two satisfiability examples are silent and close.

Repository check:

```text
$ make check
exit_code=0
python3 experiments/check_formalization_plan.py --check
  "task_count": 30,
python3 experiments/check_contracts.py
  "registered_contracts": 29,
  "base_compatibility_checked": false,
python3 experiments/test_contract_policy.py
Ran 13 tests in 0.052s
OK
python3 experiments/check_work_queue.py
30 work items: ownership, contract registration and task cards consistent.
```

`make check` also prints the complete plan and contract-closure JSON
inventories; the displayed lines are the exact non-inventory/status projection
of that successful run.

Hygiene:

```text
exit_code=0
forbidden_tokens=0 maxHeartbeats=0
git_diff_check=clean
verification_paths_changed=0
new:formalization/NSFormalization/Section4/A05/RieszShift.lean
new:formalization/NSFormalization/Section4/R43/ShiftedData.lean
```

Because `verification_paths_changed=0`, the brief's conditional
`scripts/gates.sh` and
`python3 experiments/check_contracts.py --base-ref origin/erenup/integration`
gates do not apply.  The unconditional architecture check still ran through
`make check` as shown above.

Negative mutation:

```text
$ LEAN_NUM_THREADS=6 lake env lean ../research/A05/probes/rev191_symbol_sign.lean
exit_code=1
../research/A05/probes/rev191_symbol_sign.lean:22:2: error: Type mismatch
  derivativeHalfDatum_symbol j i Z
has type
  ↑↑↑((derivativeHalfDatum j Z).ofLp i) =ᵐ[volume] fun ξ =>
    NSFormalization.Section4.R43.rieszCoordinateSymbol j ξ * ↑↑↑(Z.ofLp i) ξ
but is expected to have type
  ↑↑↑((derivativeHalfDatum j Z).ofLp i) =ᵐ[volume] fun ξ =>
    -NSFormalization.Section4.R43.rieszCoordinateSymbol j ξ * ↑↑↑(Z.ofLp i) ξ
```

Fixes: none.
