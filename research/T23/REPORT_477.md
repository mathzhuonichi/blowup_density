# Lane 477 / T23 U2 — checked partial delivery

Branch: `erenup/477-T23-U2-local-correction-G0`. No push, merge or rebase.
First skeleton commit: `122fd83e`; last proof checkpoint: `59606dfd`.

## 1. Statements

- **G0:** kernel-checked `boundaryInsertionAPI_zero_cutoff` for the **literal**
  `BoundaryInsertionAPI`: no instance exists when `D.ε₀ = 0`. The standalone
  probe contains the original Spec byte-for-byte, including its literal
  `boundaryInsertionStatement`. This is the authorised exact-false-instance
  alternative; it is not a claimed proof of `¬ boundaryInsertionStatement`.
  `boundaryInsertionStatement'` existentially chooses matching `C` and `D`,
  with `0 < r` and both ball inclusions explicit. It is a definition only.
- **Actual local construction:** `exists_localCorrection_with_derivative_bounds`
  chooses **one** raw `D` and positive threshold. It proves the cutoffs, radial
  potential and curl, globally smooth divergence-free compact correction,
  open-neighbourhood cancellation, both global cross transports on `Ico 0 T`,
  globally smooth compact force, all-time support and the exact I02 mixed
  correction-jet / spatial force-jet bounds. Constants are chosen before ε.
  No placement/correction/extension witness is assumed by the constructor.
- **Local supplier bridge:** the curl of a fixed spatially truncated radial
  potential gives a solenoidal spatial extension; a fixed time cutoff makes it
  globally smooth. One threshold gives global equality of the actual correction
  and force with those of this fixed extension, hence equality of their jets.
  Exterior values of the original reference need no regularity. The packet is
  un-periodised, and its inactive past handles the initial endpoint.

## 2. Files

Implementation:

- `formalization/NSFormalization/Section3/T23/LocalCorrection.lean` — exact
  seven-field raw structure, core constructor, cancellation, cross transports,
  force locality/regularity/support, physical identity and threshold shrinking.
- `formalization/NSFormalization/Section3/T23/SpatialExtension.lean` — fixed
  spatial/window solenoidal extensions and radial-cylinder correction transport.
- `formalization/NSFormalization/Section3/T23/LocalCorrectionBridge.lean` —
  matching fixed extension, uniform jet estimates and the single-D constructor.
- `formalization/NSFormalization/Section3/T23/StatementRepair.lean` — actual
  raw zero cutoff and its threshold obstruction; see the location gap below.

Research: `probes/g0_counterexample.lean`, `probes/local_correction_closes.lean`,
`axioms_u2.lean`, `axioms_u2.log`, `ATTEMPTS_U2.md`, this report, the G0 addendum
in `SPEC_ISSUES.md`, and the U2 status line in `T23_SPLIT.md`.

No `Placement.lean`, existing Lean module, contract, registry or generated task
card was edited. The pre-existing untracked lane brief was left untouched.

## 3. Gaps and error text

**Partial, not U2-complete or registration-ready.**

1. The full literal and repaired G0 declarations currently live in the research
   probe, **not** the canonical `StatementRepair.lean`. The latter proves only
   the raw obstruction. The implementation/contract trees have no canonical
   `BoundaryInsertionAPI` / `ClassicalSolutionOmega` at this snapshot (scoped
   `grep -rn` recorded in the G0 addendum). We did not import Contracts into
   implementation modules or manufacture a competing placement/domain API.
2. A matching **registered** I02/I03 pair has not been constructed/consumed.
   In particular, the remaining bridge must retain `A.correction = C` and
   equality with this jointly chosen actual correction and force. Independently
   chosen cutoff records cannot be identified. The exact residual conjunction
   is in `ATTEMPTS_U2.md` R1.
3. Energy, mixed-Lebesgue and Sobolev norm fields remain open at the same `D`.
   The new derivative bounds do not replace those fields, and no path-infimum
   norm has been identified with T23's per-slice domain norm. Exact remaining
   energy/Sobolev statements are recorded in R1.
4. The core's original-reference radial potential and the whole-space supplier's
   extension-reference radial potential agree locally; global equality is not
   inferred. The G0 repair copies the supplier potential into its raw `D`;
   the boundary API does not require the core's stronger global potential formula.

There are **no outstanding compiler errors in delivered Lean files**. Failed
attempts and their exact diagnostics are retained in `ATTEMPTS_U2.md`. For
example, the first support adaptation failed with:

```text
LocalCorrection.lean:174:4: error: Type mismatch: After simplification, term
  hy
 has type
  y ∈ Function.support fun x => scaledVelocity U x₀ T ε (t, x)
but is expected to have type
  parabolicVelocity ε⁻¹ (T - ε ^ 2) x₀ (zeroPastField U) (t, y) ≠ 0
```

This was fixed by exposing nonzero membership and explicitly unfolding both
rescalings. The open gaps above are unimplemented assembly obligations, not
hidden failing proofs. No admissions, named-input stubs or replacement APIs
are used to claim their completion.

## 4. Commands and results

Every Lean shell sourced `. scripts/lean-env.sh`; all Lake invocations ran from
`verification/` with `LEAN_NUM_THREADS=6`. Import closures were built first.

- `lake build NSFormalization.Section3.T23.StatementRepair NSFormalization.Section3.T23.LocalCorrection NSFormalization.Section3.T23.LocalCorrectionBridge`
  — exit 0, 9908 jobs; only replayed upstream diagnostics.
- `lake env lean` on **each of all four implementation files** — exit 0,
  **0 output bytes** each.
- `lake env lean ../research/T23/probes/g0_counterexample.lean` and
  `lake env lean ../research/T23/probes/local_correction_closes.lean` — exit 0,
  **0 output bytes** each. Includes exact registered cross-transport forms,
  the zero-time endpoint, constructor and operator drift probes.
- `lake env lean ../research/T23/axioms_u2.lean` — exit 0; **21** named
  implementation theorems each print exactly
  `[propext, Classical.choice, Quot.sound]`. The literal G0 theorem is separately
  checked by `#guard_msgs` with the same exact three axioms: **22 proofs audited**.
- `make check` — exit 0, including 13 policy tests and the 45-item queue check.
  Its broad inventory still reports the existing umbrella's BoundaryCorollary
  admission and `source_hashes_match: false`; neither is a claim about this
  lane's import closure. An explicit source-import traversal of **1162** files
  from these modules/probe found **no** BoundaryCorollary import.
- `lake test` — exit 0, 10998 jobs; registered tests pass.
- `make test-mutations` — exit 0; implementation refactor accepted, admission,
  extra-axiom and weakened-hypothesis mutations rejected as required.
- Byte comparisons: original Spec is contained verbatim in the G0 probe;
  the seven-field `CutoffData` structure is copied verbatim in LocalCorrection.
- No forbidden proof tokens in the four implementation modules;
  `git diff --check` passes. All proof checkpoints were committed incrementally.
