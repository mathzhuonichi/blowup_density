# Lane 311 / U9a attempts and remaining obligation

## Paths investigated

Read CLAUDE.md, T11_SPLIT §0–§4, RECONCILIATION §0–§3, IMPLEMENTATION_CANDIDATES,
the first 40 LESSONS lines, canonical LocalTheory/PeriodicData, the target probe,
the registered TorusData contract, and the named R1/R2 sources. FourierCalculus is
present. The mandatory tree search used:

```sh
grep -rnE 'heatOneDerivative|EndpointSafeTwoSpaceDuhamelContract|ClassicalPeriodicLocalTheory|PeriodicQuantitativeLocalInput|HasAprioriBound' \
  formalization/NSFormalization/Paper1/Periodic*.lean \
  formalization/NSFormalization/Section3/ \
  formalization/NSFormalization/Section4/{A01,A02,A04,D01} \
  vendor/HeliCorgi/Formal/
```

Initial search: 108 matches. A final search includes this lane's declarations too.
Local full outputs: `tmp/311/tree-search{,-final}.txt` (ignored build artifacts).

R1 endpoint package: `restart_past_terminal` is an assumed field, not an existence
conclusion. The zero-fixed flow-map condition also is not automatic for forced flow.
R1 Duhamel/Picard modules: genuine abstract analysis; need concrete operators, a
forced equation and physical recovery. Existing scalar heat smoothing **was found**
and reused. The new proof is its canonical real-vector lift, including exact
Euclidean norm control, semigroup law and smoothing coherence.

R2 A01 Horizon/AprioriInvariance: useful causal-window/prescribed-horizon pattern.
Its ordinary-cylinder theorem cannot consume general nonzero periodic fields:
`OrdinaryRepresentative` requires ordinary whole-space L². Chosen route transfers
the pattern to weighted Z³ coefficients, not that impossible input condition.

No `apply` failure is fabricated for these mathematical interface mismatches;
these conclusions follow by reading the actual statements. Neither route currently
supplies the all-data H¹ quantitative input. Full evidence and exact U9b–e targets
are in `EXISTENCE_ROUTE.md`.

## Actual compiler failures and fixes

1. Nested continuous-linear-map norm failed:
   ```text
   failed to synthesize instance of type class
     Norm (↥(PeriodicSobolev 3) →L[ℝ] ↥(PeriodicSobolev 3) →L[ℝ] ↥(PeriodicSobolev 2))
   ```
   Scalar CLM and carrier instances individually synthesized. Pinning the submodule
   NormedAddCommGroup and NormedSpace routes with explicitly named local instances
   `torusProbeNormedGroup` and `torusProbeNormedSpace` resolved the nested synthesis.
   No anonymous instances were added.
2. Rewriting through the heat alias initially failed:
   ```text
   Tactic `rewrite` failed: Did not find an occurrence of the pattern
     |Paper1.PeriodicHeatMultiplier.heatSymbol ν t k|
   in the target expression
     |torusHeatSymbol ν t k| ≤ 1
   ```
   Unfold the alias before rewriting. Explicit `ℝ` casts before complex coercion
   also fixed `failed to synthesize instance of type class HPow ℂ ℝ ...`.
3. Untyped `lp.single` in a `change` inferred a dependent family, producing
   `Type mismatch ... but is expected to have type ℂ`. Explicit
   `: PeriodicScalarData` annotations fixed this. `WithLp.ext` was unavailable;
   use extensionality / `WithLp.ofLp_injective 2` instead.
4. Derivative projection attempt failed with
   `Unknown constant HasFDerivAtFilter.fderiv_apply`.
   Rewrite with `.hasFDerivAt.fderiv` and then evaluate. Scalar derivative
   elaboration also exposed two real-module instance presentations; `convert!`
   resolves their definitional equality without changing the statement.
5. Non-vacuity helper lookup failed:
   `Unknown constant Real.integrableOn_exp_neg_Ioi`.
   The actual theorem is unnamespaced `integrableOn_exp_neg_Ioi`.
   `enorm_lt_top` takes implicit `x`, not explicit `A` or named `a`.
6. An implicit infimum bound caused:
   ```text
   (deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached
   ```
   Specify the intermediate extended norm and unfold the relevant infimum before
   `iInf_le_of_le`. Only the large non-vacuity declaration has a commented,
   declaration-local `maxHeartbeats 400000`; no global increase.
7. Conformance output formatting initially failed:
   `Unknown option pp.width` and
   `Docstring on #guard_msgs does not match generated message`.
   Removed the option and preserved Lean's actual multiline output for the two
   long names. All 33 named source declarations now have guarded exact standard
   three-axiom output.

All the above errors are resolved. Final module and probe elaboration have no errors
or warnings from the new source. Existing imported modules emit their own warnings
when Lake replays dependencies.

## Exactly one residual named local-existence input

```lean
def PeriodicQuantitativeLocalInput : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ K : ℝ≥0∞, K ≠ ⊤ → ∃ δ : ℝ, 0 < δ ∧
    ∀ a : SpatialField, a ∈ initialClassT → periodicSobolevENorm 1 a ≤ K →
      ∀ g : SpaceTimeField, ContDiff ℝ ∞ g → IsPeriodicOn univ g →
        (∀ m : ℕ, forceSobolevENormT 1 (m : ℝ) g ≤ K) →
          ∃ w : ClassicalSolutionT ν a g δ, PeriodicLocalRegularity ν a g δ w
```

U9e is the proposed discharge unit. The operator/mild structures are exact
construction specifications; no inhabitant of the operator contract is assumed
by the unconditional heat or nonzero-forced-witness results.

The non-vacuity theorem verifies all this input's data/force premises at a finite K
and its full classical/regularity output for `u=(2-exp(-t))e₁`, `g=exp(-t)e₁`.
It proves both fields nonzero at time zero. It does not assert the universal input.

Separate statement issue: the U10 plan's compact-force argument supplies a bound
for each m; the input requires one K for all m. Nonzero spatial Fourier modes with
a compact smooth time bump violate that uniform-in-order premise. This is not a
compiler error and is not repaired by weakening any target in this lane.
