# Lane 256 report — completed Sobolev density

## 1. Proved theorem

`BlowupDensity.Bindings.completedSobolevDensity` proves the first clause of
Proposition 4.6 with the `REnergyAPI.completedSobolevDensity` statement
verbatim: for `a ∈ initialClassR`, `ν,T > 0`, `q ∈ {1,2}`, and
`s < criticalOrder q.toReal`, compact smooth forces with maximal lifespan at
most `T` are dense in the full completed `L^q(0,∞;H^s)` space.

## 2. What Lean now has

The binding first approximates an arbitrary completed datum by a compact force,
then uses compact-class breakdown density, extracts an actual measurable datum
path from the force-norm infimum, adds the two realization paths, and applies
the Bochner triangle inequality.  The module also contains the requested
non-vacuity example at `ν = T = 1`, `a = 0`, `q = 1`, `s = 0`, and zero target.

## 3. Remaining gap

There is no remaining gap for this field and no isolated satisfiability
hypothesis.  The other two fields of the reconciled R46 specification —
completed homogeneous density and strong trajectory closure — are outside this
lane and remain separate assembly tasks.

## 4. Validation

- `LEAN_NUM_THREADS=6 lake build Bindings.CompletedSobolevDensity`: exit 0; Lake
  replayed pre-existing dependency warnings, with no diagnostic from the new
  module.  The quiet/error-level rerun exited 0 with zero output.
- `lake env lean Bindings/CompletedSobolevDensity.lean`: exit 0, zero output.
- `lake env lean ../research/R46/axioms_sobolev_density.lean`: prints exactly
  `[propext, Classical.choice, Quot.sound]` for the theorem.
- `make check`: exit 0 (the existing copied-source notices remain unchanged).
- `make test`: exit 0; all 32 registered contracts pass their existing tests.
