# Lane 265-SPEC-t13-draft-a report

## 1. Specified theorem

Draft A specifies the four clauses requested for Section 3's uniform
localization lemma: the whole-space and torus Gagliardo identities with the
same explicit (c_s), the one-sided localization estimate with a constant
uniform over supports shrinking inside a fixed coordinate ball, and the
(s=0)/(s=1) endpoint identities. This lane is statements only; it does not
claim a proof of those clauses.

## 2. What Lean now contains

`DraftA.lean` contains elaborated definitions of (I_{\mathbb R}),
(I_{\mathbb T}), (c_s), (K_s), the nonzero lattice tail, exact spatial
periodization, support/chart predicates, and coefficient-side periodic
inhomogeneous and homogeneous norms on componentwise
`lp (Fin 3 → ℤ) 2`. `LocalizationAPI` has exactly four fields and uses the
registered whole-space `sobolevENorm` and `dotHomogeneousENorm` vocabulary.
The torus difference integral is over the concrete fundamental cube; Fourier
coefficients continue to use the existing `torusLift`/Haar layer.

`COMPARISON_A.md` maps every paper clause to its Lean field, records the exact
support/periodization, vector, Fourier-weight, constant, and quantifier-order
choices, and lists registration and proof obligations.

## 3. Remaining gaps

All mathematical assertions in `LocalizationAPI` remain to be proved. The
main analytic gaps are positivity/finiteness of (c_s), whole-space
Plancherel in the registered homogeneous datum model, torus Parseval/Tonelli
with the exact (2π) weight, construction of the periodic weighted `lp` data,
the uniform nonzero-lattice tail estimate from the ball-to-boundary distance,
and the endpoint single-copy identities. The local T10 periodic norm
definitions and T13 kernel/localization definitions are explicitly marked
"needs registration".

## 4. Commands and results

- `cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Paper1.PeriodicSobolevHilbert NSFormalization.Paper1.TorusCube` — succeeded; it emitted one pre-existing linter warning in `PeriodicSobolevHilbert.lean`.
- `cd verification && lake env lean ../research/T13/DraftA.lean` — succeeded with no diagnostics after the dependency build.
- `make check` — succeeded; repository-wide output retained the known `BoundaryCorollary.lean` admission/source-hash notices.
- `make test` — succeeded; all registered contract tests replayed, with pre-existing dependency linter warnings only.
- `make test-mutations` — succeeded; mutation checks rejected the test mutations, with the same pre-existing dependency warnings.
