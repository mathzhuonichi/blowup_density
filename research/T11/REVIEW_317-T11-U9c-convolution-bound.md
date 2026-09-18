ACCEPT-WITH-NOTES

## 1. What the lane claims

The worker report claims the unconditional theorem
`torusConvolutionInput : TorusConvolutionInput` and copies the proposition as

```lean
∃ Q : PeriodicSobolev 3 →L[ℝ] PeriodicSobolev 3 →L[ℝ] PeriodicSobolev 2,
  ∀ A B i k, (Q A B).1 i k = torusProjectedConvectionSymbol A B i k
```

at `research/T11/REPORT_317.md:5-15`. This is token-for-token the residual
input introduced by lane 313 at
`formalization/NSFormalization/Section3/T11/LocalExistence.lean:230-235` and
the U9c target at `research/T11/EXISTENCE_ROUTE.md:202-215,244-252`.

The additional declarations claimed in the report also exist with exactly the
reported types:

- `torusConvolutionCLM` at
  `formalization/NSFormalization/Section3/T11/ConvolutionBound.lean:408-412`;
- its exact coefficient identity at
  `formalization/NSFormalization/Section3/T11/ConvolutionBound.lean:414-416`;
- its operator-norm bound at
  `formalization/NSFormalization/Section3/T11/ConvolutionBound.lean:418-420`;
- `torusConvolutionInput` at
  `formalization/NSFormalization/Section3/T11/ConvolutionBound.lean:422-424`;
- the positive-viscosity contract corollary at
  `formalization/NSFormalization/Section3/T11/ConvolutionBound.lean:426-429`.

The report's displayed constant is also exact: `convolutionBoundSquared` is
`64 * ∑' k, (periodicFrequencyWeight k ^ 3)⁻¹` at
`ConvolutionBound.lean:108-109`, and `torusConvolutionConstant` is nine times
its square root at `ConvolutionBound.lean:286-288`.

The mathematics matches the brief. The paper gives the nonzero-frequency
Leray symbol, identity at the zero mode, boundedness on every Sobolev space,
and the projected convection term at `paper/sections/02-preliminaries.tex:75-83`.
The canonical tree definitions implement exactly that symbol at
`formalization/NSFormalization/Section3/T10/PeriodicData.lean:184-207`, and
lane 313's fixed H³×H³→H² weighted convection and projected symbols are at
`formalization/NSFormalization/Section3/T11/LocalExistenceProbe.lean:202-218`.
The mild equation uses the same `-ℙ div (u ⊗ u)` term at
`paper/sections/appendix-a-local-theory.tex:109-114`.

No hypothesis has been added to the main theorem: it has no binders at all
(`ConvolutionBound.lean:422-424`). The only added binder is the honest
`0 < ν` required by the downstream contract constructor
(`LocalExistence.lean:237-266` and `ConvolutionBound.lean:426-429`). There is
no `ENNReal.toReal`, empty interval, finite-support premise, solenoidality
premise, or unused named analytic input in the result.

## 2. What is in Lean

The proof realizes the requested analytic route rather than postulating it:

- the derivative and Peetre-type cubic weight bounds are proved at
  `ConvolutionBound.lean:28-62`, using the tree's weight-shift theorem
  `formalization/NSFormalization/Paper1/PeriodicWeightShift.lean:25-51`;
- lattice inverse-cube summability and the uniform kernel-square sum are at
  `ConvolutionBound.lean:84-129`, based on
  `formalization/NSFormalization/Paper1/PeriodicInverseWeightSummable.lean:53-79`;
- ℓ² Cauchy–Schwarz and the double-sum reindexing/product energy estimate are
  at `ConvolutionBound.lean:131-238`;
- conjugate reflection, the complete H² datum, and its explicit bilinear norm
  bound are at `ConvolutionBound.lean:240-317`;
- the canonical Leray contraction used at `ConvolutionBound.lean:347-360` is
  `formalization/NSFormalization/Section3/T10/Leray.lean:176-181,221-256`;
- additivity/homogeneity and `LinearMap.mkContinuous₂` bundle the exact
  coefficient map at `ConvolutionBound.lean:319-416`.

Thus a zero or otherwise incorrect bilinear map cannot satisfy the delivered
coefficient field unless it equals the canonical projected symbol at every
input and frequency. The conformance probe repeats the unwrapped existential,
the named result, the coefficient equality, norm bound, and contract
inhabitants at `research/T11/probes/convolution_bound_closes.lean:11-31`.
It also supplies nonzero carrier inputs at
`research/T11/probes/convolution_bound_closes.lean:33-43`; the same instance is
in the module at `ConvolutionBound.lean:440-449`.

The axiom audit contains 20 public and 22 private declaration checks
(`research/T11/axioms_convolution_bound.lean:5-83,85-158`). All 42 guarded
messages are exactly `[propext, Classical.choice, Quot.sound]`; the audit
typechecks with zero output.

The required negative probe is
`research/T11/probes/rev317_coefficient_mutation.lean:13-23`. It retains every
binder and changes the main identity from `= symbol` to `= symbol + 1`.
Reusing the reviewed coefficient proof fails precisely at this changed
constant, not because an argument was removed.

## 3. Gaps and hygiene

There is no residual gap in U9c and no named input. The report correctly keeps
physical recovery/common-horizon bootstrap in U9d
(`research/T11/REPORT_317.md:54-58`), rather than using it as a premise here.
The report makes no "not in the tree" claim about U9c. As an additional audit,
whole-tree `grep -rn` searches under
`formalization/NSFormalization/Section4` found no occurrence of
`TorusConvolutionInput`, `torusProjectedConvectionSymbol`,
`torusConvolutionCLM`, the H³×H³→H² target, a torus physical-recovery lemma,
or `PeriodicQuantitativeLocalInput`.

Hygiene passes. The base diff contains one new Lean module and research
records/probes only; no pre-existing Lean module is modified. No executable
occurrence of `sorry`, `admit`, `axiom`, or `native_decide` occurs in the lane
Lean files. The sole heartbeat override is declaration-local, exactly 400000,
and has the adjacent explanation at `ConvolutionBound.lean:286-293`. Both
local instances are explicitly named at `ConvolutionBound.lean:23-26`, as are
the probe instances at `convolution_bound_closes.lean:6-9`.

Two comments use inaccurate terminology but do not affect a statement or
proof. Exact one-line fixes:

1. At `formalization/NSFormalization/Section3/T11/ConvolutionBound.lean:431`,
   replace "A nonzero datum and nonzero forcing mode" with
   "Two nonzero constant-mode data".
2. At `research/T11/probes/convolution_bound_closes.lean:33`, replace
   "Nonzero datum and force modes" with "Two nonzero constant-mode data".

## 4. Commands and results

All Lean commands were run after sourcing `scripts/lean-env.sh`, only from
`verification/`, with `LEAN_NUM_THREADS=6`. Exit codes and literal output are
below. For the two very large commands, exact head/tail excerpts are shown and
the omitted middle consists only of replayed dependency warnings or the
contract closure manifest.

1. `cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T11.ConvolutionBound`

   Exit 0. Exact head/tail:

   ```text
   ⚠ [8778/9054] Replayed NSFormalization.Source.FiniteHilbertBochner
   warning: NSFormalization/Source/FiniteHilbertBochner.lean:24:19: try 'simp' instead of 'simpa'

   Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
   warning: NSFormalization/Source/FiniteHilbertBochner.lean:23:37: This simp argument is unused:
     PiLp.single_apply
   [... replayed warnings from pre-existing dependencies omitted ...]
   ⚠ [9898/9910] Replayed NSFormalization.Paper3.SobolevDirectionalDerivative
   warning: NSFormalization/Paper3/SobolevDirectionalDerivative.lean:103:16: `SchwartzMap.smul_apply` has been deprecated: Use `smul_apply` instead

   Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.smul_apply` to `smul_apply x`).
   Build completed successfully (9910 jobs).
   ```

   No warning names `ConvolutionBound.lean`; the direct check below is silent.

2. `cd verification && LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section3/T11/ConvolutionBound.lean`

   Exit 0; output exactly empty.

3. `cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/T11/probes/convolution_bound_closes.lean`

   Exit 0; output exactly empty.

4. `cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/T11/axioms_convolution_bound.lean`

   Exit 0; output exactly empty. Additionally,
   `rg -c "depends on axioms: \\[propext, Classical.choice, Quot.sound\\]" research/T11/axioms_convolution_bound.lean`
   printed exactly:

   ```text
   42
   ```

5. `make check` from the worktree root

   Exit 0. Exact bounded output excerpts:

   ```text
   python3 experiments/check_formalization_plan.py --check
   {
     "task_count": 45,
     "source_counts": {
       "formalization": 565,
       "vendor/NavierStokesAndEuler": 2486,
       "vendor/HeliCorgi": 129
     },
     "source_manifest_entries": 2975,
     "missing_copied_imports": [],
     "citation_interfaces_reachable": [],
   [... contract closure manifest omitted ...]
     "base_compatibility_checked": false,
     "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
   }
   python3 experiments/test_contract_policy.py
   .............
   ----------------------------------------------------------------------
   Ran 13 tests in 0.046s

   OK
   python3 experiments/check_work_queue.py
   45 work items: ownership, contract registration and task cards consistent.
   ```

6. `cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/T11/probes/rev317_coefficient_mutation.lean`

   Expected exit 1. Exact output:

   ```text
   ../research/T11/probes/rev317_coefficient_mutation.lean:23:2: error: Type mismatch
     hQ A B i k
   has type
     ↑((↑((Q A) B)).ofLp i) k = torusProjectedConvectionSymbol A B i k
   but is expected to have type
     ↑((↑((Q A) B)).ofLp i) k = torusProjectedConvectionSymbol A B i k + 1
   ```

7. `git diff --check origin/erenup/integration-section3...HEAD`

   Exit 0; output exactly empty.

8. `git diff --name-only origin/erenup/integration-section3...HEAD`

   Exit 0; exact output:

   ```text
   formalization/NSFormalization/Section3/T11/ConvolutionBound.lean
   research/T11/ATTEMPTS_CONVOLUTION_BOUND.md
   research/T11/REPORT_317.md
   research/T11/T11_SPLIT.md
   research/T11/axioms_convolution_bound.lean
   research/T11/probes/convolution_bound_closes.lean
   ```

9. `grep -rnE "TorusConvolutionInput|torusConvolutionInput|torusProjectedConvectionSymbol|torusConvolutionCLM|H³.?×.?H³.?→.?H²|H3.?x.?H3.?to.?H2" formalization/NSFormalization/Section4` and the corresponding torus physical-recovery/common-horizon search

   Exit 0 with `|| true`; output exactly empty.

10. `git diff --name-only origin/erenup/integration-section3...HEAD -- verification`

    Exit 0; output exactly empty. Therefore the conditional `scripts/gates.sh`
    and `check_contracts.py --base-ref origin/erenup/integration-section3`
    gates do not apply: this lane did not touch `verification/`.
