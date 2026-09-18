ACCEPT-WITH-NOTES

## 1. What the lane claims

The worker claims exact proofs of the three requested `MeanZeroSobolevCalculusAPI`
fields with explicit constants: `boundedRepresentative` with `linftyConst`,
`hTwo_le_laplacian` with `hTwoConst`, and `lambda_exists`, with no named input.
The report makes these claims at `research/T12/REPORT_341.md:5-38` and lists
the implementation and audit files at `research/T12/REPORT_341.md:40-74`.

The paper passages support the requested mathematics.  The local-theory lemma
states the torus/whole-space `H² → L∞` estimate at
`paper/sections/appendix-a-local-theory.tex:7-13`, including no mean-zero
condition.  The continuation argument explicitly uses
`‖v‖_{H²} ≤ C‖Δv‖₂` for mean-zero fields at
`paper/sections/03-torus.tex:490-500`.  Appendix B fixes the torus multiplier
`Λ = (-Δ)^{1/2}` with symbol `2π|k|` at
`paper/sections/appendix-b-embeddings.tex:8-9`; its torus embedding and
derivative discussion are at `:75-103`.

The API fields are exactly the reconciled binders: `boundedRepresentative` at
`research/T12/probes/api_on_canonical.lean:137-140`, `lambda_exists` at
`research/T12/probes/api_on_canonical.lean:159-161`, and `hTwo_le_laplacian` at
`research/T12/probes/api_on_canonical.lean:194-197`.  In particular, the first
has only `MemPeriodicHmVector 2 v`, the second has only smooth periodicity, and
the third has smooth periodicity plus physical mean zero.

## 2. What is in Lean

The three exported statements match those API fields exactly after substituting
the explicit constants:

* `boundedRepresentative` is exactly the field at
  `formalization/NSFormalization/Section3/T12/FourierEmbeddings.lean:384-388`.
  `linftyConst` is the inverse-weight `ℓ²` constant at
  `formalization/NSFormalization/Section3/T12/FourierEmbeddings.lean:322-336`; the weight
  itself is the T10 `1 + 4π²|k|²` definition at
  `formalization/NSFormalization/Section3/T10/PeriodicData.lean:66-69`.
  The proof uses the existing weighted Cauchy–Schwarz lemma
  `formalization/NSFormalization/Section3/T10/FourierCalculus.lean:103-114`,
  `L²` Fourier-basis representation
  `formalization/NSFormalization/Section3/T10/Parseval.lean:37-47`, and the
  new a.e. reconstruction at
  `formalization/NSFormalization/Section3/T12/FourierEmbeddings.lean:361-382`; no smoothness or
  mean-zero premise is added.

* `hTwo_le_laplacian` is exactly the API field at
  `formalization/NSFormalization/Section3/T12/FourierEmbeddings.lean:163-168`.
  `hTwoConst = 1 + 1/(4π²)` and its positivity are at
  `formalization/NSFormalization/Section3/T12/FourierEmbeddings.lean:123-132`.
  The registered Laplacian coefficient identity
  used by the proof is
  `formalization/NSFormalization/Section3/T10/ForcePaths.lean:417-420`; the
  proof kills the zero mode using `IsMeanZeroT` at
  `formalization/NSFormalization/Section3/T12/FourierEmbeddings.lean:193-198`,
  and uses the existing Parseval theorem at
  `formalization/NSFormalization/Section3/T10/Parseval.lean:115-125`.

* `lambda_exists` is exactly the API field at
  `formalization/NSFormalization/Section3/T12/FourierEmbeddings.lean:293-318`.
  `lambdaCoeff` and `lambdaField` are defined at
  `formalization/NSFormalization/Section3/T12/FourierEmbeddings.lean:223-232`;
  smooth weighted summability is proved at
  `formalization/NSFormalization/Section3/T12/FourierEmbeddings.lean:240-281`,
  and the coefficient/reality/periodicity clauses are discharged at
  `formalization/NSFormalization/Section3/T12/FourierEmbeddings.lean:283-318`.
  The predicate being proved is the tree definition
  `formalization/NSFormalization/Section3/T12/MeanZeroCalculus.lean:92-101`.
  The reused smooth-series declarations are present at
  `formalization/NSFormalization/Section3/T11/MildPressure.lean:64-85` and
  `:98-149`, and the multiplier construction is not a placeholder.

The conformance probe copies each target verbatim at
`research/T12/probes/fourier_embeddings_closes.lean:27-53`.  It also gives a
nonzero single-mode witness: `modeField` is proved smooth/periodic at
`research/T12/probes/fourier_embeddings_closes.lean:106-132`, mean-zero and
`H²`-member at `research/T12/probes/fourier_embeddings_closes.lean:139-157`,
nonzero at `research/T12/probes/fourier_embeddings_closes.lean:159-165`, and
the conjunction plus the `lambda_exists` application close at
`research/T12/probes/fourier_embeddings_closes.lean:167-175`.
Thus the hypotheses are satisfiable by a nonconstant field, not only by zero.

The module has no `sorry`, `admit`, `axiom`, `native_decide`, heartbeat
override, or instance declaration (the searches over the module/probe/audit
files are empty apart from report/audit prose mentioning those words).  The
lane commit itself changes only the new FourierEmbeddings module and its
research records (`git diff --name-status HEAD^ HEAD`); relative to
`origin/erenup/integration-section3`, the only Lean paths are added files, not
modified pre-existing modules.  The inherited T11 prerequisite is an added
file from the merged 339 parent, not a modification by lane 341.

The exact relative diff status is:

```text
A formalization/NSFormalization/Section3/T11/ClassicalRegularity.lean
A formalization/NSFormalization/Section3/T12/FourierEmbeddings.lean
A research/T11/ATTEMPTS_CLASSICAL_REGULARITY.md
A research/T11/REPORT_339.md
M research/T11/T11_SPLIT.md
A research/T11/axioms_classical_regularity.lean
A research/T11/probes/classical_regularity_closes.lean
A research/T12/ATTEMPTS_FOURIER_EMBEDDINGS.md
M research/T12/COMPARISON.md
A research/T12/REPORT_341.md
A research/T12/axioms_fourier_embeddings.lean
A research/T12/probes/fourier_embeddings_closes.lean
```

The two `M` entries are research records; no pre-existing Lean module is
modified.

## 3. Gaps

The report's declared gaps are scope gaps in the T12 API, not failures of the
three delivered fields: `tameProduct`, `velocityCriticalL3`,
`gradientLambdaCriticalL3`, and `gradientLSix` remain open in the T12 structure
(`research/T12/REPORT_341.md:76-92`).  The required whole-`Section4` searches
were run before accepting that wording.  They found related but nonidentical
Section 4 results: `tameProductScalar`/`tameProductVector` at
`formalization/NSFormalization/Section4/A03/ScalarTameProduct.lean:250-258`
and `formalization/NSFormalization/Section4/A03/VectorTameProduct.lean:270-278`,
and a whole-space `velocityCriticalL3` at
`formalization/NSFormalization/Section4/A05/CriticalL3.lean:390-409`.
There is no exact T12 declaration named `gradientLambdaCriticalL3`; the only
`gradientLSix` hit is explanatory text in
`formalization/NSFormalization/Section4/A05/HessianLaplacian.lean:9-15`.
Likewise, the Section 4 pointwise `H²` result is a different whole-space jet
interface (`formalization/NSFormalization/Section4/A03/BoundedRepresentative.lean:153-185`),
so the report is correct that T12's pointwise `supNorm_le` interface is not
delivered here.

One notes-level record fix is required.  The brief asks for a one-line status
update in the unit's §1 comparison row, but lane 341 appends a 17-line status
section at `research/T12/COMPARISON.md:56-72`.  Collapse that addition to one
line in the §1 row (or one appended line explicitly labeled as the row status).
The mathematics and proof records do not need revision.  `git diff --check
HEAD^ HEAD` is clean; the broader diff check reports only an inherited blank
line at `research/T11/axioms_classical_regularity.lean:358`, outside lane 341.

## 4. Commands and results

All Lean commands sourced `scripts/lean-env.sh`, used `LEAN_NUM_THREADS=6`, and
ran Lake from `verification/`.

Build and direct checks:

```text
$ LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T12.FourierEmbeddings
Build completed successfully (9988 jobs).
[exit 0; replayed diagnostics were from pre-existing dependencies and none named FourierEmbeddings.lean]

$ LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section3/T12/FourierEmbeddings.lean
[exit 0; exactly 0 bytes]

$ LEAN_NUM_THREADS=6 lake env lean ../research/T12/probes/fourier_embeddings_closes.lean
[exit 0; 12 lines, all standard axiom reports]

$ LEAN_NUM_THREADS=6 lake env lean ../research/T12/axioms_fourier_embeddings.lean
[exit 0; 39 physical lines for 33 #print axioms declarations]
```

Every one of the 33 axiom reports has exactly
`[propext, Classical.choice, Quot.sound]`; for example, the target lines are:

```text
'NSFormalization.Section3.T12.hTwo_le_laplacian' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.lambda_exists' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.boundedRepresentative' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The conformance probe's non-vacuity audit likewise prints the same three-item
list for each witness declaration, including `modeField_ne_zero`.

Repository gates:

```text
$ make check
[exit 0]
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.044s

OK
python3 experiments/check_work_queue.py
45 work items: ownership, contract registration and task cards consistent.

$ BASE_REF=origin/erenup/integration-section3 LEAN_NUM_THREADS=6 scripts/gates.sh NSFormalization.Section3.T12.FourierEmbeddings
== make test-mutations
extra_axiom: rejected as required
weakened_hypothesis: rejected as required
Mutation suite passed. This is an infrastructure check, not a PDE proof.
== check_contracts
  "base_compatibility_checked": true,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
== gates OK
[exit 0 at the time of the first run, against integration tip a405dab1]

$ python3 experiments/check_contracts.py --base-ref origin/erenup/integration-section3
AssertionError: Removed stable specification: verification/Contracts/V1/TorusLocalTheory.lean
[exit 1 on the later rerun]
```

The later failure is external base drift: `origin/erenup/integration-section3`
advanced to lane 340/348 after the first run and now contains
`verification/Contracts/V1/TorusLocalTheory.lean`, while this lane's older base
does not.  Lane 341 does not touch `verification/`; the brief makes this
contract-policy gate conditional on verification changes.  Before merge, the
lane should be rebased/merged onto the current integration tip and the gate
rerun.

Negative mutation (substantive constant change) was run in
`research/T12/probes/rev341_negative_constant.lean:14-19`, changing the main
`hTwo_le_laplacian` constant from `hTwoConst` to `hTwoConst + 1` without
dropping any binder or hypothesis.  The expected failure is:

```text
../research/T12/probes/rev341_negative_constant.lean:19:2: error: Type mismatch: After simplification, term
  hTwo_le_laplacian
 has type
  ∀ (v : SpatialField),
    SmoothPeriodicT v →
      IsMeanZeroT v → periodicSobolevENorm 2 v ≤ ENNReal.ofReal hTwoConst * periodicLpENorm 2 (laplacian v)
but is expected to have type
  ∀ (v : SpatialField),
    SmoothPeriodicT v →
      IsMeanZeroT v → periodicSobolevENorm 2 v ≤ ENNReal.ofReal (hTwoConst + 1) * periodicLpENorm 2 (laplacian v)
```

That probe exits 1 as intended; the delivered conformance probe exits 0.

Final verdict: ACCEPT-WITH-NOTES.

Fixes: collapse `research/T12/COMPARISON.md:56-72` to the required one-line
§1 status update; before merge, rebase/merge the lane onto the current
integration tip and rerun the base-sensitive contract check; optionally clarify
in the report that the listed gaps are open in the T12 API despite related
whole-space Section 4 analogues.
