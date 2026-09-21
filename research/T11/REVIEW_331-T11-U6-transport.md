ACCEPT-WITH-NOTES

## 1. What the lane claims

The worker claims a shared transport constructor for
`v(t,x)=α • u(αt,x+X(t))-c(t)`, `q(t,x)=α² p(αt,x+X(t))`, and
`g(t,x)=α² • f(αt,x+X(t))-d(t)`, with `ν'=αν` and `αT'=T`
(`research/T11/REPORT_331.md:5-19`).  The actual declaration has exactly those
parameters and pointwise equations (`formalization/NSFormalization/Section3/T11/Transport.lean:680-690`).
The three concrete constructors are the advertised `α=1`, `α=ν⁻¹`, and `α=ν`
instances (`Transport.lean:800-843`, `:1145-1162`).  The paper's rescaling and
Galilean formulas agree with appendix A (`paper/sections/appendix-a-local-theory.tex:79-105`).

The report is honest that the three API fields are not all closed: the exact
canonical targets are `transformed_solution` (`research/T11/probes/api_on_canonical.lean:165-173`),
`to_unit` (`:205-215`), and `from_unit` (`:216-225`), while the lane supplies
conditional/partial variants (`Transport.lean:1204-1278`).  The brief explicitly
allows an honest partial delivery with an exact obstacle, so this is not treated
as a blocker.

## 2. What is in Lean

`classicalSolutionT_transport` constructs the complete `ClassicalSolutionT`
record, with every listed field filled (`Transport.lean:714-727`); the source
structure itself has 13 fields, not 14 (`formalization/NSFormalization/Section3/T10/PeriodicData.lean:265-299`).
The chain-rule/residual theorem is present (`Transport.lean:680-690`), the
rescaling regularity transport has all three clauses
(`Transport.lean:919-979`), and the Galilean pressure-Poisson transport is
conditional on the source regularity record (`Transport.lean:1174-1192`).
The target-shape probe copies the target subsets and contains a nonzero constant
flow instance (`research/T11/probes/transport_closes.lean:36-108`, `:112-168`).

The 72 audited declarations are covered by 72 `#guard_msgs`/`#print axioms`
entries (`research/T11/axioms_transport.lean:1-411`), and the successful audit
output is exactly `[propext, Classical.choice, Quot.sound]` for each.
The module, probe, and audit contain no admission token or `maxHeartbeats`
override; the only grep hit is the word “axiom” in the audit comment itself.

## 3. Gaps and notes

1. **Note — applicability of the “not in tree” claim.**  The report says that
   the tree has no declaration producing a `C^∞` datum path
   (`research/T11/REPORT_331.md:82-87`; the same assertion is repeated in
   `research/T11/ATTEMPTS_TRANSPORT.md:76-84`).  A whole-Section4 grep does find
   `ManuscriptLocalRegularity.sobolev_smooth` and
   `sobolev_smooth_of_pipeline` (`formalization/NSFormalization/Section4/A01/ManuscriptRegularity.lean:38-41`,
   `:91-102`).  Those declarations are for `ClassicalSolutionR` and require
   explicit all-order `hpaths`/carrier hypotheses, not an arbitrary torus
   `ClassicalSolutionT`; they therefore do not discharge the residual.  Fix the
   report/attempts sentence to say “no applicable unconditional theorem for an
   arbitrary `ClassicalSolutionT`” and mention this incompatible Section4 result.

2. **Note — constructor scope.**  The brief mentions a `(α,β,γ)` map of the
   form `(αt,βx+X(t))`, but this constructor deliberately fixes `β=1`
   (`research/T11/ATTEMPTS_TRANSPORT.md:8-15`; `Transport.lean:680-689`).  Both
   requested API instances use `β=1`, so the delivered instances are faithful;
   add one sentence to the report explicitly recording that this is the scoped
   specialization, rather than calling it a fully general β-transform.

3. **Note — exact API wording.**  `transformed_solution_fields` includes an
   extra projected-equation conjunct (`Transport.lean:1240-1253`); it is not
   literally just the target with the regularity conjunct deleted.  The probe
   correctly projects away that extra conjunct (`research/T11/probes/transport_closes.lean:79-88`),
   but the report should say “target subset plus projected” at
   `research/T11/REPORT_331.md:36-42`.

4. **Note — bookkeeping.**  Change “14 fields” to “13 fields” in
   `research/T11/REPORT_331.md:15,68`.  Also qualify its build sentence
   (`:99-106`): the module itself emitted no diagnostics, but `lake build`
   replayed pre-existing dependency linter warnings (shown below).

The residual itself is correctly identified: `ClassicalSolutionT.sobolev` only
provides `ContinuousOn`, while `PeriodicLocalRegularity.sobolev_smooth` requires
`ContDiffOn` (`PeriodicData.lean:286-290`; `LocalTheory.lean:79-88`).  The
Galilean translation-family smoothness issue is also recorded as a genuine
additional obstacle (`REPORT_331.md:89-95`).  The reviewer mutation changes the
main residual's `- d t` to `+ d t`; the valid audit probe is
`research/T11/probes/rev331_negative.lean:1-39`, and the direct mutated proof
fails with:

```
/dev/stdin:35:4: error: Type mismatch
  navierStokesResidual_transport _hvline _hv _hq _hX _hc _hu _hu2 _hp
has type
  NavierStokesR3.ProblemStatement.navierStokesResidual (α * ?m.185) v q t x =
    α ^ 2 • NavierStokesR3.ProblemStatement.navierStokesResidual ?m.185 u p (α * t) (x + X t) - d t
but is expected to have type
  NavierStokesR3.ProblemStatement.navierStokesResidual (α * ν) v q t x =
    α ^ 2 • NavierStokesR3.ProblemStatement.navierStokesResidual ν u p (α * t) (x + X t) + d t
```

## 4. Commands and results

All commands used `. scripts/lean-env.sh`; every `lake` command ran from
`verification/` with `LEAN_NUM_THREADS=6`.

```
cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T11.Transport
exit=0; Build completed successfully (9949 jobs).
```

The build also printed only replayed dependency warnings (for example
`FiniteHilbertBochner.lean:24:19` and `Paper3/SobolevDirectionalDerivative.lean:103:16`);
`grep Transport.lean` found no module diagnostic.  These commands each exited 0
with no output:

```
cd verification && lake env lean ../formalization/NSFormalization/Section3/T11/Transport.lean
cd verification && lake env lean ../research/T11/probes/transport_closes.lean
cd verification && lake env lean ../research/T11/axioms_transport.lean
cd verification && lake env lean ../research/T11/probes/rev331_negative.lean
```

`make check` exited 0; its exact final lines were:

```
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.044s

OK
python3 experiments/check_work_queue.py
45 work items: ownership, contract registration and task cards consistent.
```

The full gate script also exited 0 (`BASE_REF=origin/erenup/integration-section3
LEAN_NUM_THREADS=6 scripts/gates.sh NSFormalization.Section3.T11.Transport`) and
ended exactly with:

```
== make test-mutations
extra_axiom: rejected as required
weakened_hypothesis: rejected as required
Mutation suite passed. This is an infrastructure check, not a PDE proof.
== check_contracts
  "base_compatibility_checked": true,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
== gates OK
```

`python3 experiments/check_contracts.py --base-ref origin/erenup/integration-section3`
also exited 0 with `"base_compatibility_checked": true`.  Hygiene checks found
no forbidden token in the module or probes, `git diff --check` was silent, and
`git diff --name-only origin/erenup/integration-section3...HEAD` shows only the
new Transport/research files plus the append-only split-row update; the base has
no `Transport.lean` at that path.

Fixes: (1) qualify the Section4 gap claim as “no applicable unconditional
`ClassicalSolutionT` theorem” and cite A01's inapplicable pipeline theorem;
(2) state explicitly that the shared constructor is the β=1 specialization;
(3) describe `transformed_solution_fields` as the target subset plus projected;
(4) correct 14→13 fields and qualify the dependency-warning build output.
