# Lane 235 — density from insertion

## Successful proof

`Bindings/DensityFromInsertion.lean` imports lane 233 directly and uses the
registered `Data.BreakdownDenseR` predicate throughout. The exponent is
`q : ℝ≥0∞`; `ThresholdAPI.formula q.toReal 0` converts the insertion threshold
to the literal paper expression `2 / q.toReal - 3 / 2`.

For each reference and positive ENNReal radius, split on its lifespan being
at most the prescribed time. In that case return the reference, using the
zero measurable Sobolev datum path to prove G5 (in fact for every q).
Otherwise obtain the aligned V2 insertion record from lane 233. Intersect
its eventual strict norm bound with `Ioc_mem_nhdsGT family.eps_pos` and use
the nontrivial right-neighborhood filter to obtain an actual parameter.
`InsertionLifespan.memForceR_force` and `insertionFromData_lifespan` establish
membership in the original breakdown set. Zero initial data specialize the
same theorem via `A04.zero_mem_initialClassR`.

## Failed attempts and corrections

- `zero_le _` failed: here `zero_le` is already a proposition proof, not a
  function. Use `zero_le`.
- An inline subtype witness with an `IsSobolevPath` hole produced tactic goals
  in an unexpected order (`introN` had no binders). Name the zero-path proof
  before applying `iInf_le`; the resulting proof needs no heartbeat override.
- The first build log redirection failed because this worktree had no `tmp/`;
  created that local directory and reran the build successfully.
- The brief's lane-232 `NonDensity.lean` filename is absent even on that branch;
  read-only inspection found `NonDensityL2.lean` there. This base contains only
  `NonDensityL1.lean`, so no combined iff is asserted or imported.

## Fidelity and limits

The output closes RMainAPI's densityFixedInitial and densityZero mathematical
claims for F_R. It does not construct the stronger research RDensityAPI record:
that record additionally retains an explicit branch disjunction and aligned
R42 witness in the returned proposition. The proof uses precisely such a
record internally, but exports the requested Data density vocabulary.
Compact/rapid force-class specializations remain outside this lane.
The existing Packet/Scaling duplicate-name import caveat is inherited.

All three implementation declarations and both named concrete audit results
print exactly `[propext, Classical.choice, Quot.sound]`. The audit also has
an example with ν=T=1, a=g=0, q=1, s=0, radius=1. Gate results are recorded in
REPORT_235.md; full logs remain in ignored `tmp/*235.log`.
