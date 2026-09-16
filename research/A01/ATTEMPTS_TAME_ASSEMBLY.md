# Lane 207 — cylinder tame assembly

## Scope and source audit

Read CLAUDE.md, NEXT_SESSION.md, HANDOFF §0 and §2 P7, REPORT_206,
ATTEMPTS_SMOOTH_TAME, REPORT_205 §3, REVIEW_200 §3, and LESSONS first 40
lines. REVIEW_206-A01-smooth-tame.md was absent. Followed route A, including
angular-dependent fields; no invariant-subspace restriction or descent assumption.

This branch lacked SignedLimit.lean and SignedPassage.lean, despite the task's
integration snapshot. Restored both **byte-for-byte** from the already available
Git ref `origin/erenup/204-A01-signed-passage`, commit
`46e15f81db7cbbe9dd419f954c8a7d1df95dadc4`. Its RootComparison.lean agrees with
this checkout. This is source restoration into new files, not a merge, rebase,
fetch, or modification of existing proof modules. Their 34 declarations are
included in the conformance audit, alongside 22 declarations from TameAssembly.

## Completed proof route

1. Scalar-vector multiplication is not symmetric: `L(u) • v` does not become
   `L(v) • u` on exchanging factors. `cylinderRightProduct_memLp` instead applies
   the actual H³ cylinder embedding to the transported vector and constructs its
   L² class. `cylinderMixedProduct_right` combines this with lane 206's positive
   word interpolation. Its constant is exactly `‖L‖ * sobolevEmbeddingConstant 1 3`.
2. `wordAtLevel_ae`, `wordAtLevel_value`, and `toJet_word` identify finite words
   with smooth cylinder derivatives at every available order. No all-order L²
   premise is needed for this identification. `boundedWordBlock_value` gives
   the identical statement for blocks. This avoids misusing spatial-only
   `word_descent_ae_*` on angular-dependent functions.
3. For a surviving commutator leaf, a,b≥1 and a+b≤q+2. Either a+3≤q+2 or,
   since q≥6, b+3≤q+2. `cylinderMixedWord_bound` therefore represents and bounds
   every leaf using one of the two orientations.
4. `cylinderL2Bound_add` combines actual L² representatives, preserving their
   a.e. identities and adding norm bounds. Induction over `cylinderLeibniz`
   proves the multiplicity bound 2^n. Induction over `cylinderCommutatorLeibniz`
   counts the surviving branches, also at most 2^n; its empty word is zero.
5. `cylinderDerivative_ae` identifies derivative operators by translation
   differentiation. `productHq_ae` identifies the actual Sobolev product;
   `cylinderWord_ae` identifies its top words. Together with the scalar product
   and lane 205's sign theorem, this proves `cylinderCoordinateCommutator_ae`.
   Lp.ext then identifies the finite commutator with the negative of the
   representative supplied by the recursive estimate.
6. The velocity functionals have norm ≤1. `familyNorm_le_sum_norm` sums the
   per-word bound over the exact finite word family. Thus
   C(q)=card(SobolevWord(q+1))*2^(q+1)*sobolevEmbeddingConstant 1 3.
   Smooth density loses no constant. The forcing normalization is
   max(A q,C(q)/4), with E(q)=mildNormConstant q.
7. Existing recut forcing assembly accepts this larger constant. Restored lane
   204 signed passage discharges finite mild energy. Lane 196/193 then supplies
   all-order bounds on the same base-solution horizon.

## Satisfiability and constructor horizon

No named analytic input remains in the tame/forcing/finite-energy chain.
The general theorems are not certified by zero examples. The audit includes
an actual zero commutator application without a tame premise, and the probe
applies the unconditional local constructor to zero force/data.

The prompt's fixed-S milestone, if S is an arbitrary positive time, drops the
base-solution horizon requirement of `hb_of_base'`. Positivity alone does not
supply that base solution. The user was asked to clarify and the local-existence
interpretation was used. The probe proves both:

* `constructor_of_base`: the exact requested velocity/solution conclusion on
  a supplied base mild solution's positive horizon, with all analytic inputs
  discharged;
* `a01_constructor_unconditional`: from hf, ha, ν>0, Smax>0 alone, there is
  0<S≤Smax and a solution with `w.velocity = velocity` on S. The vendor's
  base-order local existence supplies S and the base solution inside the proof.

No arbitrary-prescribed-time/global-existence assertion is made. Also, as
requested, the solution's initial datum is `velocity(0,·)`; this probe does not
add the separate pointwise identification with `a.field`.

## Resolved diagnostics and negative routes

* Missing namespace produced `Function expected at localFieldLift` and later
  `Function expected at velocityComponents`. Opened the actual vendor namespaces.
* `wordAtLevel_ae` is not definitionally the finite `word` statement. Initial
  `exact` produced `Type mismatch`. Rewriting `wordAtLevel_value` and
  `toJet_word` fixed this. Blocks similarly use `boundedWordBlock_value`.
* Rewriting under a local abbreviation for the last direction did not match.
  An explicit `change` exposes that direction before rewriting.
* A coercion in the commutator a.e. identity left `OuterMeasureClass ?m.588
  (LiftDomain 1)` stuck. Explicitly typing the difference as `LiftL2 1` and the
  measure as `liftMeasure 1` resolved it.
* Pointwise negation required `Pi.neg_apply` before rewriting the representative.
* An initial probe failed because `ConstructorAssembly.olean` was absent;
  building ConstructorAssembly, PressureRegularity and ZeroSolution resolved it.
* Two `unnecessarySeqFocus` warnings were removed; final direct module check
  has zero output. One commented declaration-local 400000-heartbeat setting
  handles the dependent finite commutator identification.

All requested gates and the additional contract/mutation suites pass. See
REPORT_207.md for exact statements, source provenance and commands.
