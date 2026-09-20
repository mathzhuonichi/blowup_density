# Lane 292 report — T15 draft B

## 1. Specified theorem

Drafted the Lean statement of Proposition 3.3, “Scaling at fixed viscosity”
(`paper/sections/03-torus.tex:101-159`). For one T14 packet and one common
small-scale family, it states the explicit parabolic rescalings, single-copy
periodization, the fixed-viscosity periodic classical solution with zero
initial data, blow-up at `T`, pressure normalization, both exact packet-energy
identities, the exact mixed-norm scaling identity for all endpoints, and the
localized periodic `L¹_t H^s_x` bound for `0≤s≤1`. The subcritical convergence
clause is a separate derived proposition, not an assumed API field.

## 2. What Lean now contains

`research/T15/DraftB.lean` contains an elaborating statement-only draft in
`BlowupDensity.T15.DraftB`. It temporarily copies only the T10/T14/T13
declarations needed by the draft, defines the three scaled fields and their
lattice periodizations explicitly, introduces a torus mixed Lebesgue norm in
the same measurable-`Lp`-path style as Section 4, and defines a Type-valued
`ScalingAPI`. The API fixes its geometry, threshold, and `C_s` data before
`ε`; it records concrete summability, `MemLp`, and integrability facts so the
totalized sums and Bochner integrals cannot make the displayed identities
vacuous. `research/T15/COMPARISON_B.md` maps every paper clause to the draft and
the registered `I03.scaling` field.

## 3. Remaining gaps

This lane supplies specifications, not proofs or a registered contract. The
main implementation obligations are: construct the enlarged force carrier
`K_*`; prove local finiteness and the single-copy lattice equalities; bridge the
explicit rescalings to I03; assemble `ClassicalSolutionT` after pressure
normalization; prove exact endpoint and mixed-norm changes of variables; apply
T13 localization to construct T10 Sobolev datum paths; and prove negative-order
monotonicity plus the derived convergence statement. There is also a naming
discrepancy to resolve at registration: the reconciled T13 file currently uses
`BlowupDensity.T13.Spec`, while the T15 brief requires the temporary copy under
`BlowupDensity.T13.Draft`.

## 4. Commands and results

- `cd verification && . ../scripts/lean-env.sh && lake env lean ../research/T15/DraftB.lean` — passed.
- `. scripts/lean-env.sh && make check && make test && make test-mutations` — passed;
  the mutation suite accepted the implementation refactor and rejected the
  admitted-proof, extra-axiom, and weakened-hypothesis mutations as required.
- Source audits covered `CLAUDE.md`, `collaboration/SECTION3_PLAN.md` §1–§3,
  `03-torus.tex:99-175`, all fields of `Contracts/V1/Scaling.lean` and
  `Contracts/V1/Packet.lean`, the reconciled T10/T13/T14 specs, and the requested
  `Paper1/` implementation-candidate heads.
- No other T15 lane artifact or brief was read.
