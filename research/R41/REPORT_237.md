# Lane 237 — independent specification draft B

## 1. Statement written

Created `research/R41/DraftB.lean`, with statement-only structure
`BlowupDensity.Contracts.V1.DraftB.RMainAPI`. Its four explicit fields specify
fixed-datum density, the zero-datum iff, the numerical thresholds, and the
joint regular-reference approximation rider. Every field cites manuscript
lines and states its quantifier order. No proof, placeholder proposition,
new axiom, implementation import, or local vocabulary definition was added.

## 2. Choices

Real q restricted to 1 or 2; real s; `ENNReal.ofReal q` for norm exponents.
Registered relative density stays inside the smooth force class. Breakdown
by T remains distinct from the rider's exact maximal lifespan T. The iff is
one field. All rider conclusions share one family, with unchanged initial
velocity enforced by the solution type, explicit earlier-history equality,
and both force and energy norms tending to zero from positive ε.
`COMPARISON_B.md` contains the clause table and full representation choices.

## 3. Ambiguities

The paper leaves s implicit and does not restate the subcritical restriction
in its final rider. “Same earlier history” and the approximation parameter
are resolved using Theorem 4.2's ε-family and [0,T−2ε²] interval. “Singularity
exactly at T” is rendered as exact classical lifespan. Stronger insertion
claims (spatial support, limsup blowup, quantitative rate, simultaneous all-q,s
convergence) are not silently added. See the comparison for all identified
ambiguities and the distinction between the theorem and its following remark.

## 4. Commands and results

- Read `CLAUDE.md`, the permitted manuscript passages, and registered
  `Data.lean`, `Thresholds.lean`, `CriticalRegularity.lean`; followed no links
  to competing specifications. Searched for `AGENTS.md`: none found.
- `. scripts/lean-env.sh; cd verification; lake env lean ../research/R41/DraftB.lean`
  — exit 0, no errors or warnings (Lean v4.34.0-rc2).
- `git diff --check` — passed.
- Full `make check`, `make test`, and `make test-mutations` were intentionally
  not run: those repository-wide gates inspect/build other registered
  statements and bindings, conflicting with this lane's explicit double-blind
  restriction. The requested isolated elaboration was run instead. No
  registered contract or implementation was changed.
- Shared session/queue files were not read or edited to preserve isolation.
- Committed only the three requested deliverables on
  `erenup/237-SPEC-r41-draft-b`. No push, merge, or rebase.
