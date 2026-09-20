# Lane 278-SPEC-t13-spec report

## 1. Specified theorem

This lane gives the reconciled, statement-only specification of
`lem:localization` (`paper/sections/03-torus.tex:22-98`).  For real
three-vector fields and `0 < s < 1`, the six-field `LocalizationAPI` records:
positivity and finiteness of the explicit `c_s`; the whole-space and torus
Gagliardo/Fourier identities with that same constant; the uniform one-sided
localization estimate for support in a fixed coordinate ball; and separate
`s=0` and `s=1` endpoint equalities.  No proof or inhabitant of the API is
claimed.

## 2. What Lean now contains

`research/T13/Spec.lean` elaborates the fixed fundamental cube, coordinate-ball
support, definitional lattice periodization, singular kernel, `cFrac`, lattice
tail, whole-space and torus difference integrals, and physical gradient norm.
Its record fields are exactly `constant_pos_finite`, `wholeSpace_identity`,
`torus_identity`, `localization`, `endpoint_zero`, and `endpoint_one`, each with
paper line citations and a non-vacuity comment.  Tail summability and tail
bounds are deliberately not fields.

Because `research/` is not an import root, the file imports T10's public
modules and copies only the needed declarations from
`research/T10/Spec.lean:46-203` verbatim under the original
`BlowupDensity.T10.Draft` namespace.  T13 consequently refers to T10's
`periodicSobolevENorm`, `periodicHomogeneousENorm`, `IsPeriodicDatum`,
`meanZeroPartT`, `torusLift`, and Fourier coefficient conventions by name.
The copy is marked for deletion once `T01.torus_data` is registered.

`research/T13/COMPARISON.md` gives the merged paper-clause table with A/B
provenance and rulings, exact T10/D01 proof dependencies, cross-references to
T10's “Needs a lemma” items, and owner questions.  The two drafts, their two
comparisons, and both prior reports were copied byte-for-byte from lanes 265
and 266; SHA-256 comparison against the branch blobs succeeded for all six
files.

## 3. Remaining gaps

Every assertion in `LocalizationAPI` remains to be proved.  The principal
gaps are positivity/finiteness of `cFrac`; the D01-infimum bridge for
`dotHomogeneousENorm`; fixed-cube/Haar and periodic Parseval bridges; existence
and norm identification for T10 homogeneous data of smooth mean-zero periodic
fields; local finiteness, smoothness, agreement, and uniqueness of `periodize`;
the lattice-tail clearance estimate; the difference-integral comparison; and
the single-copy endpoint identities.  In particular, T10's current selected
API has order-zero Parseval and mean-zero data facts, but no homogeneous
existence/norm field, so the proof lane must supply that bridge or extend the
eventual T10 binding.

## 4. Commands and results

- `cd verification && lake env lean ../research/T13/Spec.lean` — succeeded
  with exit code 0 and no diagnostics.
- SHA-256 comparison of each provenance file against `git show` from
  `erenup/265-SPEC-t13-draft-a` or `erenup/266-SPEC-t13-draft-b` — all six
  matched.
- `git diff --check` — succeeded.
- Declaration scan for `sorry`, `admit`, `axiom`, `theorem`, and
  `native_decide` in `Spec.lean` — no matches; the only proof terms in the file
  are those inside T10's verbatim `realPeriodicSubmodule` definition.
- `make check` — succeeded.  Its repository-wide inventory retained the
  pre-existing `source_hashes_match: false` and the known
  `Paper1/BoundaryCorollary.lean` admission notice.
- `make test` — succeeded; all 10,732 registered build/test tasks replayed,
  with pre-existing dependency linter warnings only.
- `make test-mutations` — succeeded: `implementation_refactor` was accepted,
  while `admitted_proof`, `extra_axiom`, and `weakened_hypothesis` were rejected
  as required.
