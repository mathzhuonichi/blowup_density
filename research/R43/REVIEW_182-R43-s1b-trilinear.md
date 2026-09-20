ACCEPT-WITH-NOTES

## 1. What the lane claims

The lane claims a conditional proof of the nonlinear term in
`eq:Rcritical1`.  The paper defines
`y = ‖Λ^(1/2)u‖₂`, `z = ‖Λ^(3/2)u‖₂`, and
`b = ‖f‖_{Ḣ^(1/2)}` and records the two critical embeddings at
`paper/sections/04-whole-space.tex:91-95`; testing against `Λu` gives
`½(y²)' + (ν-C₀y)z² ≤ by` at `:96-99`.  Appendix B states the Euclidean
embedding, its vector/tensor componentwise form, and exactly
`‖∇v‖₃ + ‖Λv‖₃ ≤ C‖v‖_{Ḣ^(3/2)}` at
`paper/sections/appendix-b-embeddings.tex:8-36`.

Every declaration and exact statement claimed in `REPORT_182.md` exists:

- `derivativeCriticalConst = 4 * criticalL3Const` and its positivity are at
  `formalization/NSFormalization/Section4/R43/Trilinear.lean:36-43`.
- `derivativeCriticalL3` has exactly the reported `eLpNorm` statement at
  `Trilinear.lean:99-104`.
- `lintegral_enorm_mul_three_le` has exactly the reported three-factor
  `L³` statement at `Trilinear.lean:176-184`.
- `criticalAdvectionHolder` has exactly the reported physical-integral
  statement at `Trilinear.lean:228-236`.
- `trilinearConst`, its expansion
  `trilinearConst = 16 * criticalL3Const ^ 3`, and positivity are at
  `Trilinear.lean:313-331`.
- `criticalTrilinearEstimate_of_hcrit` has exactly the reported two explicit
  inputs `hcrit` and `hbridge` and conclusion at `Trilinear.lean:336-341`.
- `rcritical1_of_hcrit` has exactly the reported conjunction and uses
  `C₀ := trilinearConst` at `Trilinear.lean:406-420`.

The consumer predicate is literally

```lean
∀ t ∈ Ioo (0 : ℝ) T,
  |⟪hcrit.advectionHalf t, hcrit.velocityHalf t⟫| ≤
    C₀ * ‖hcrit.velocityHalf t‖ * ‖hcrit.velocityThreeHalf t‖ ^ 2
```

at
`formalization/NSFormalization/Section4/R43/CriticalPairing.lean:220-226`.
Thus the final Lean statement is the requested `C₀ y z²` estimate, conditional
on the new carrier/identity bridge rather than on `hcrit` alone.

## 2. What is in Lean

### Field-by-field audit of `CriticalAdvectionLpBridge`

`ShiftedCriticalData` is defined at `Trilinear.lean:68-81`.

- `lambda` chooses a physical field; it asserts no proposition.
- `lambda_memHInfty` is a regularity/carrier obligation.  It is stronger than
  mere `L²` membership, but it contains neither an `L³` bound nor a constant.
- `lambdaHalf_isDatum` says that `Z` is the order-`1/2` datum of `lambda`.
  At the actual use site, `Z = hcrit.velocityThreeHalf t`, which is already the
  order-`3/2` datum of the velocity by
  `CriticalPairing.lean:172-173`.  Since a homogeneous order-`s` datum is
  `|ξ|^s û` (`Section4/D01/HomogeneousWitness.lean:129-132`, with the exact
  predicate at `:234-253`), this is the exact carrier identity
  `lambda = Λv`, not an estimate.
- `derivativeHalf` chooses three order-half data.
- `derivativeHalf_isDatum` identifies them with the three physical directional
  derivatives; again this is a carrier identity, not a norm bound.
- `derivativeHalf_symbol` states
  `D_{j,i}(ξ) = (i ξ_j/|ξ|) Z_i(ξ)`.  This is the exact angular-frequency order
  shift.  The angular convention cancels Mathlib's `2π` derivative factor as
  confirmed by `Source/AngularGradientIdentity.lean:44-55`.

`CriticalAdvectionLpBridge` itself is at `Trilinear.lean:299-311`.

- `shifted` supplies the preceding carrier package at each genuine interior
  time.
- `pairing_identity` supplies only the equality between the datum pairing and
  the physical integral.  It does not bound either side, assert an `L³`
  membership with a constant, or state any part of the desired conclusion.

Therefore `criticalTrilinearEstimate_of_hcrit` is neither a restatement nor a
vacuous consequence of the bridge.  Its proof still establishes the velocity
embedding, both derivative-factor bounds, three-factor Hölder, the finite
`ENNReal.toReal` passage, and the final constant at `Trilinear.lean:342-402`.
It is, however, explicitly conditional: the tree does not yet construct the
bridge from an arbitrary `CriticalDatumPath`.

The bridge is satisfiable.  The conformance file constructs a genuine
`CriticalDatumPath` for `A04.zeroSol` at
`research/R43/axioms_s1b.lean:32-107`, constructs all shifted fields/data at
`:109-132`, constructs the entire bridge at `:134-144`, and instantiates both
main conclusions at the explicit interior time `1 ∈ Ioo 0 2` at `:146-164`.
This is stronger than an empty-interval witness, and `ClassicalSolutionR`
always has `0 < T` by `Section4/A02/SolutionClass.lean:115-120`.

For a genuine nonzero smooth `CriticalDatumPath`, the bridge is mathematically
consistent as well: take the physical multiplier `lambda = Λv`; its order-half
datum is the already supplied order-three-halves datum `Z`, and the derivative
data have multiplier `(iξ_j/|ξ|)Z`.  Fractional Parseval/duality then gives
`pairing_identity`.  What is absent is a Lean construction of these objects and
that last duality identity, not a mathematical obstruction.  In particular,
the zero witness proves consistency, while the standard multiplier model
explains why nonzero genuine paths should admit the bridge.

### Hölder and the constant-one pointwise bound

The three-factor theorem uses Mathlib's
`ENNReal.lintegral_prod_norm_pow_le` at `Trilinear.lean:203-215`.  Its three
exponents are all `1/3`; `norm_num [Fin.sum_univ_three]` discharges
`1/3+1/3+1/3=1`.  The three resulting integrals are rewritten to `eLpNorm _ 3`
at `:185-221`.

The physical specialization first applies real-inner-product
Cauchy--Schwarz and then
`NSFormalization.Section4.C01.advection_norm_le` at
`Trilinear.lean:244-273`.  The cited lemma is proved at
`Section4/C01/Trilinear.lean:87-114`: it identifies
`(v·∇)v = Σ_j v_j ∂_jv`, applies finite-dimensional Cauchy--Schwarz, and
identifies the second Euclidean norm with the Frobenius norm of `gradTensor`.
Consequently the pointwise constant is exactly `1`, with no hidden factor of
`3` or `√3`.

### The shifted embedding and constants

Here `Z` is the order-`3/2` homogeneous datum of the velocity at the main use
site (`CriticalPairing.lean:172-173` and `Trilinear.lean:303-305`).  Each of the
three derivative columns is bounded through
`A05.u7_vector_eLpNorm_le_of_datum` at `Trilinear.lean:117-122`; the `Λv`
carrier uses the same lemma at `:158-160`.  That A05 vector lemma is the
componentwise wrapper at `Section4/A05/CriticalL3.lean:377-388`, and it invokes
`u6_scalar_eLpNorm_le` at `a = 1/2` through
`CriticalL3.lean:334-343`.

The multiplier estimate is honest.  `Trilinear.lean:51-59` proves
`|ξ_j|/‖ξ‖ ≤ 1` from `PiLp.norm_apply_le`; the formerly problematic denominator
`|‖ξ‖|` is normalized by `abs_of_pos hnorm` at `:58`.  No absolute value is
dropped.  Summing the three column bounds gives `3*C*‖Z‖ₑ` at `:140-157`, and
adding the single `Λv` bound gives `4*C*‖Z‖ₑ` at `:161-170`.  Thus the factor
`4` is exactly “three coordinates plus `Λ`,” albeit deliberately coarse.

The final proof bounds each of `‖∇v‖₃` and `‖Λv‖₃` by the common sum bound
`4*C*‖Z‖` (`Trilinear.lean:352-363`).  Together with the velocity factor `C`,
this gives `C*(4C)*(4C) = 16C³` at `:375-393`.  Positivity is separately proved
at `:326-331`.  The final `toReal` step explicitly proves that the right side is
not `⊤` at `:394-402`; there is no `⊤.toReal = 0` escape.

Finally, `rcritical1_of_hcrit` is a direct composition with lane 175's
`rcritical1_of_trilinear` (`CriticalPairing.lean:304-318`) at
`Trilinear.lean:419-420`.  Its scalar inequality is exactly the paper's
`eq:Rcritical1` with `C₀ := trilinearConst`, plus the useful derivative
conjunct.

### Fidelity and hygiene

The lane copy of `CriticalPairing.lean` has SHA-256
`dc4d3d6dfc2665fc9c460e83ae552ad5b16ae415b11de4d5c73d4c09441244e2`,
identical to `git show a6fac76:.../CriticalPairing.lean`.  The mandated endpoint
comparison

```text
git diff --exit-code origin/erenup/integration -- formalization/NSFormalization/Section4/R43/CriticalPairing.lean
```

has no output and exits `0`.  The historical triple-dot diff lists
`CriticalPairing.lean` and `Trilinear.lean` as added, not modified; it lists no
pre-existing Lean module as modified.  The only existing tracked file changed
by the lane is the brief-required record `research/R43/R43_SPLIT.md`.

Static search of the two formalization modules finds no
`sorry`, `admit`, `axiom`, or `native_decide`, and no `maxHeartbeats` setting.
`git diff --check` exits `0` with no output.  All binders of the main theorems
are used through their dependent indices or proofs; no norm statement relies
on an empty interval or an unattained datum-infimum.

## 3. Gaps

The worker's substantive gap claim is correct: no theorem currently constructs
`CriticalAdvectionLpBridge hcrit`, so the unconditional

```lean
∀ hcrit, CriticalTrilinearEstimate (C₀ := trilinearConst) hcrit
```

has not been proved.  I reran the worker's exact search and broadened it to all
of `formalization/NSFormalization/Section4`.  The physical-Riesz search found
only the A05 residual docstring, integer/inhomogeneous datum-lowering lemmas in
A04, and this lane's own declarations.  The homogeneous-derivative search found
only an A01 gap docstring outside this lane.  The fractional
advection/Parseval search found only the present `pairing_identity` and its use.
Generic integer/order-zero Plancherel lemmas do exist, but none has the needed
fractional `advectionHalf`/`velocityHalf` identity.  Thus the “not in the tree”
claim survives the required whole-Section4 audit.

There is one documentation correction.  `Trilinear.lean:297-298`,
`REPORT_182.md:136-138`, and `ATTEMPTS_S1B.md:105-109` say or imply that
constructing the whole bridge is “precisely A05 U4/U8.”  A05 U4/U8 accounts for
the physical `Λ` and derivative carrier work, but its published scope at
`research/A05/COMPARISON.md:208-212` does not include the fractional
`pairing_identity`; current U4 also promises `MemLp 2`, not the bridge's
`lambda_memHInfty`.  The latter closure is mathematically natural for an
`H^∞` velocity but is still a proof obligation.  This is a gap-classification
wording issue, not a defect in the conditional theorem.

Exact one-line replacement for each of those three occurrences:

```text
Constructing `shifted` requires the unexported A05 U4/U8 carriers (plus `MemHInfty` closure for `Λu`), while `pairing_identity` is a separate fractional Parseval/duality obligation.
```

No Lean-statement change is requested.

## 4. Commands and results

All Lean commands were run after sourcing `scripts/lean-env.sh`; every `lake`
command was run from `verification/` with `LEAN_NUM_THREADS=6`.

1. Module build:

   ```text
   $ LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.R43.Trilinear
   [replayed warnings from pre-existing dependencies only]
   Build completed successfully (10249 jobs).
   ```

   Exit `0`.  The complete output names only pre-existing files under
   `NSFormalization.Source`, `NSFormalization.Paper3`, and `vendor/HeliCorgi`;
   no warning names `Trilinear.lean` or another lane-owned line.

2. Direct module typecheck:

   ```text
   $ LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section4/R43/Trilinear.lean
   <no output>
   ```

   Exit `0`.

3. Axiom and non-vacuity file:

   ```text
   $ LEAN_NUM_THREADS=6 lake env lean ../research/R43/axioms_s1b.lean
   'NSFormalization.Section4.R43.derivativeCriticalConst_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section4.R43.rieszCoordinateSymbol_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section4.R43.memHInfty_dirDeriv' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section4.R43.derivativeCriticalL3' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section4.R43.lintegral_enorm_mul_three_le' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section4.R43.criticalAdvectionHolder' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section4.R43.trilinearConst_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section4.R43.trilinearConst_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section4.R43.criticalTrilinearEstimate_of_hcrit' depends on axioms: [propext,
    Classical.choice,
    Quot.sound]
   'NSFormalization.Section4.R43.rcritical1_of_hcrit' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

   Exit `0`; there are exactly ten `#print axioms` results, all exactly the
   required three axioms.  The final zero-solution example is silent and closes.

4. Repository check:

   ```text
   $ make check
   python3 experiments/check_formalization_plan.py --check
   ...
   python3 experiments/check_contracts.py
   ...
   python3 experiments/test_contract_policy.py
   .............
   ----------------------------------------------------------------------
   Ran 13 tests in 0.046s

   OK
   python3 experiments/check_work_queue.py
   30 work items: ownership, contract registration and task cards consistent.
   ```

   Exit `0`.  The omitted portions are the checkers' very large JSON source and
   contract-closure inventories (the command emitted 277901 tokens in this
   harness), not diagnostics or failures.

5. Substantive negative mutation:

   `research/R43/probes/rev182_mutation_constant.lean:8-15` keeps both `hcrit`
   and `hbridge` but strengthens the main conclusion by changing the constant
   from `trilinearConst` to `trilinearConst / 2`.

   ```text
   $ LEAN_NUM_THREADS=6 lake env lean ../research/R43/probes/rev182_mutation_constant.lean
   ../research/R43/probes/rev182_mutation_constant.lean:15:2: error: Type mismatch
     criticalTrilinearEstimate_of_hcrit hcrit hbridge
   has type
     @CriticalTrilinearEstimate ν a f T trilinearConst w hf hcrit
   but is expected to have type
     @CriticalTrilinearEstimate ν a f T (trilinearConst / 2) w hf hcrit
   ```

   Exit `1`, as expected.  This changes the numerical strength of the main
   estimate; it does not merely omit an argument.

6. Hygiene/base commands:

   ```text
   $ git diff --check
   <no output>

   $ git diff --exit-code origin/erenup/integration -- formalization/NSFormalization/Section4/R43/CriticalPairing.lean
   <no output>

   $ git diff --name-status origin/erenup/integration...HEAD -- '*.lean'
   A formalization/NSFormalization/Section4/R43/CriticalPairing.lean
   A formalization/NSFormalization/Section4/R43/Trilinear.lean
   A research/R43/axioms_s1b.lean
   ```

   All exit successfully.  No file under `verification/` occurs in the lane's
   triple-dot diff, so the brief's conditional `scripts/gates.sh` and
   `check_contracts.py --base-ref origin/erenup/integration` gates do not apply
   and were not run.

Fixes: replace the inaccurate “precisely A05 U4/U8” attribution in the three
locations listed in §3 with the exact one-line carrier-versus-Parseval wording;
no Lean change.
