# 1. The theorem proved

For every `0 < ν`, `hf : A02.MemForceR f`, classical solution
`w : ClassicalSolutionR ν a f T`, and `t ∈ Ioo 0 T`,
`R44.energy_identity` proves

`HasDerivAt (fun r => Y (u r)^2)
  (-2 * ν * Z (u t)^2 - 2 * ⟪datum₋½((u·∇)u), Ju⟫
   + 2 * forceJPairing (jWeightDatumPath w hf t ht')) t`.

The dissipation and pressure evaluations are equalities, not bounds. The norms
are lane 218's actual inhomogeneous `Y` and `Z`.

# 2. What is now in Lean

`formalization/NSFormalization/Section4/R44/EnergyIdentity.lean` continues the
existing draft: canonical slice data, smooth velocity paths, the order-six
force lowering pin, norm differentiation, exact momentum transport,
`inner_eq_jPairing`, `laplacian_jPairing`, `pressure_jPairing_zero`, the energy
assembly, and `zero_energy_terms`. `research/R44/axioms_s1b.lean` audits all
20 declarations and instantiates the derivative theorem at `A04.zeroSol`,
`ν = T = 1`, `t = 1/2`, and zero force.

`ATTEMPTS_S1B.md` records the successful route and elaboration failures.
`R44_SPLIT.md` marks S1b closed and narrows G2 to the remaining rows.
Only new Lean files were added; existing Lean modules were not changed.

# 3. Gaps and integration

There is no unproved S1b analytic fact and no additional named hypothesis.
S1c/S1d, time-integral assembly, and contract registration are separate work.
Lane 220 already owns `advectionJPairing h ha`; to avoid a duplicate declaration,
this lane uses `energyAdvectionJPairing h N`. Both expand to exactly the same
real inner product when `N = ha.advectionNegHalf`. Datum uniqueness identifies
that datum with the canonical one here. The exact consumer rewrite is recorded
in `ATTEMPTS_S1B.md`; a sibling-API adapter is still an integration step.

# 4. Validation

* `cd verification && . ../scripts/lean-env.sh && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.R44.EnergyIdentity`: passed. Dependency replay emits existing warnings; the new module emits none.
* `LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section4/R44/EnergyIdentity.lean`: passed, zero output.
* `LEAN_NUM_THREADS=6 lake env lean ../research/R44/axioms_s1b.lean`: passed; all 20 declarations report exactly `[propext, Classical.choice, Quot.sound]`; the zero-solution example closes.
* `make check`: passed (including 13 contract-policy tests and work-queue consistency). Its existing source-manifest diagnostics are not an S1b failure.
* `LEAN_NUM_THREADS=6 make test`: passed; registered contract tests report standard logical axioms only.
* `LEAN_NUM_THREADS=6 make test-mutations`: passed; implementation refactoring accepted, and admission, extra-axiom, and weakened-hypothesis mutations rejected as required.
* `git diff --check`: passed.

No push, merge, or rebase was performed.
