# Lane 161 continuation: finite-order continuous angular datum paths

## Theorem and scope

`A01/ConstructorDatumPath.lean` closes the finite-order continuity component of c8:
for a continuous cylinder path `u : C(Icc 0 S, SobolevSpace 1 (q+1))`, a continuous
ordinary path `U`, angular invariance of `u`, and `ordinaryLift (U t) = value 1 (u t)`,
every `m ≤ q+1` admits an actual path
`A : C(Icc 0 S, RealVectorSobolev (m : ℝ))` realizing `⇑(U t)` as an angular datum.
There is no assumed smooth representative, time derivative, datum continuity,
Duhamel equation, solenoidality, positivity of `S`, or extra three-order margin.
An a.e.-agreeing velocity receives the same continuous datum path.

## Lean outputs and proof

- `hasWeakDerivsL2Bound_of_word_full`: all remaining weak derivative words have
  squared L2 norm at most `‖u‖²` if `n+m ≤ q+1`.
- `hasWeakDerivsL2Bound_of_cylinder_full`: the zero-word specialization.
- `norm_datum_sub_sq_le_of_cylinder`: any data `A,B` of ordinary carriers `U,V`
  satisfy `‖A-B‖² ≤ 4^m * ‖u-v‖²` under the same two angular/lift hypotheses.
- `datum_path_continuous_of_cylinder`: any choice of the existing finite-order
  data is continuous, by the preceding difference bound and a square-root squeeze.
- `exists_continuous_datum_path_of_cylinder`: chooses per-slice data and bundles
  their proved continuity.
- `exists_continuous_datum_slice_of_cylinder`: the A02 datum predicate consumer
  for velocity slices agreeing almost everywhere with `U`.

The norm bridge reuses `OrderTwoCap.eLpNorm_descend_le`, replaces its old
three-order-loss induction by `word_descent_ae_top`, then uses the sharp D01
`norm_isSobolevDatum_le_of_memLp_derivs_sharp`. Subtraction is justified by the
all-order D01 `isSobolevDatum_sub`; the Lp representative subtraction is only an
a.e. equality, handled explicitly by `IsSobolevDatum.congr_field`.

## Remaining constructor obligations

This does not produce a jointly smooth velocity, time derivatives, all-order
compatibility on one horizon, or a solution on an interval extending past S.
The independent c6 divergence descent, c4/c9 pressure, c7 momentum, and row (v)
input-output links remain. No complete classical constructor is claimed.

## Validation

Source-level check: both new Lean files have UTF-8 without BOM, LF line endings,
and exactly one terminal newline. No proof placeholders were introduced.
The assigned Luna compiler checked the module and
`research/A01/axioms_constructor_datum_path.lean`, which prints all six theorem
axioms and consumes the actual continuous datum path at `q=6,m=7,S=1`.
First module run (`tmp/compile_ConstructorDatumPath_20260915.log`, exit 1)
elaborated the full-order norm, difference estimate, continuity, and bundled
carrier-path construction. Its only error was the final slice consumer's
untyped `∀ t`, inferred as a real through `velocity (↑t,x)` rather than as an
`Icc` subtype. The binder is now explicitly `∀ t : Icc (0 : ℝ) S`.
The assigned Luna compiler's corrected run passed:

- `tmp/compile_ConstructorDatumPath_r2b_20260915.log`: module built successfully,
  9985 build jobs, target build 173 seconds, `BUILD_EXIT_CODE=0`.
- `tmp/probe_axioms_constructor_datum_path_r2b_20260915.log`: the top-order
  continuous-path consumer passed, `PROBE_EXIT_CODE=0`. All six exported theorems
  and `nonvacuous_top_order_path` report exactly `propext`, `Classical.choice`,
  `Quot.sound` as transitive axioms.

I read these actual logs after the root agent reported their completion; the
assigned Luna compiler ran all Lean commands. No Lean command was run by this
source author. The intermediate `r2` launch returned exit -1 without Lean errors;
the successful `r2b` run is the verification evidence for the final source.

## Read-only next-step survey: c6 divergence descent

The ordinary carrier `EulerMeanSolenoidal.L2` is an abbreviation for unrestricted
`Lp Space 2 volume`, not a solenoidal subtype. Its name cannot discharge c6.
The minimal independent next theorem is
`ordinaryLift U ∈ divergenceFreeSpace 1 1 0 → U ∈ solenoidalSpace`.
It needs neither cylinder angular invariance nor spatial regularity of U.

The missing bridge is the membership of `ordinaryLift (testGradient φ hc hs)`
in the cylinder gradient space, for every compact smooth ordinary scalar test φ.
Use the lifted scalar test `φ ∘ Prod.fst`. Its support lies in
`tsupport φ × univ`; the circle factor is compact. Its local lift is
`h ↦ φ (x.1+h.1)`, so smoothness and the gradient identity follow by composition
and the chain rule. `ordinaryLift_ae` and `testGradient_ae` then identify its
ordinary lifted gradient as a genuine cylinder gradient generator.
Apply cylinder orthogonality to this generator and use the isometry's inner
product preservation; `EulerMeanSolenoidal.mem_solenoidal_iff` gives the result.

The final classical upgrade already exists:
`EulerMeanClassical.solenoidal_representative_divergence` in
`Euler/MeanClassicalConstraints.lean:14` takes U's solenoidality and an actual
smooth field f with `U =ᵐ f` and returns `∀ x, divergence f x = 0`.
Thus the remaining c6 work is the reverse test-gradient bridge, plus the B1
representative handoff; there is no need to reprove its a.e.-to-pointwise step.
`CylinderClassicalSolenoidal.mem_of_classical` and
`MeanCylinderSolenoidal.embedding_mem` only give the opposite direction.
No c6 Lean declaration was added in this lane continuation.
