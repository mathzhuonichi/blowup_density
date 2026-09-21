# Lane 506 — P21 Route B, B3

Status: **B3 abstract real-analysis unit closed. P6 / L21_H1 remains Partial.**

## 1. Statements

The domain-independent module `NSFormalization.Section4.A04.EnstrophyBarrier`
exports six theorems:

- `enstrophy_integrated_of_bound`: from a supplied height M and the differential
  inequality, proves `∫ₐᵇ Z ≤ (K+C(1+M)^3(b-a)+CF(b-a))/c`. Requires compact
  integrability of Z, endpoint continuity of Y and interior differentiability.
  No integrability of Y′ is assumed; the one-sided FTC suffices.
- `enstrophy_reciprocal_barrier`: proves
  `1/(1+Y(a))² - 2C(1+F)(b-a) ≤ 1/(1+Y(b))²` by differentiating
  `-(1+Y)⁻²` and using nonnegative dissipation.
- `enstrophy_uniform_barrier`: chooses
  `d=1/(4C(1+F)(1+K)²)>0`, `M=2(1+K)-1` before all restart times,
  interval lengths, Y and Z. For S≤d it proves Y≤M on the closed interval.
  The force-dependent denominator handles arbitrarily large F.
- `enstrophy_endpoint_lintegral`: a countable directed rational exhaustion of
  `Ico a b` passes uniform nonnegative-integral bounds to the endpoint, without
  needing measurability for this formulation.
- `enstrophy_endpoint_integral`: for measurable nonnegative Z, local compact
  integrability and uniform real integral bounds, proves BOTH compact endpoint
  integrability and the endpoint integral bound.
- `enstrophy_uniform_barrier_and_dissipation`: one uniform window supplies both
  the closed-interval height and integrated dissipation bounds.

All differentiation assumptions are strictly interior. The barrier alone does
not require Z integrable. The combined API assumes S≥0; the standalone barrier
also handles empty intervals. Constants depend only on C,K,F (hence in
particular only on the allowed c,C,K,F parameters).

## 2. Files

- `formalization/NSFormalization/Section4/A04/EnstrophyBarrier.lean`.
- `formalization/blueprint/entrypoints.json`: new proof module registered.
- `research/P21/probes/b3_closes.lean`: constant Y and zero Z; the actual cubic
  ODE solution `(sqrt(1-2t))⁻¹-1` with C=c=1 and K=F=0; endpoint Z=0.
- `research/P21/axioms_b3.lean`: prints and checks all six exported theorems.
- `research/P21/ATTEMPTS_B3.md`: proof routes and resolved elaboration errors.
- `research/P21/P6_SPLIT.md`: B3 status and B4 handoff.
- `formalization/blueprint/AXIOM_AUDIT.json`: refreshed after article audit.
- `formalization/blueprint/DEPENDENCY_GRAPH.md`: mandatory regeneration also
  reflects inherited C35_FULL/G36_FULL closures; authoritative coverage unchanged.

No B0/B1 modules were restated or changed. No spatial bridge is needed for
these abstract theorems. No contract or authoritative article coverage marker was changed.

## 3. Gaps and qualifications

No remaining B3 proof gap or Lean error. Every exported theorem has exactly
`[propext, Classical.choice, Quot.sound]`.

The real endpoint theorem explicitly requires local integrability: in Lean a
nonintegrable function's real integral is defined to be zero, so bounds on
such totalized values alone cannot imply endpoint integrability. The lintegral
version states the unrestricted nonnegative-integral result. Compact local
integrability is already an explicit premise of the dissipation API and must
be supplied from classical solutions by B4.

B4/B5 still must instantiate Y and Z, supply classical time regularity and a
common force cap, invoke the existing H² continuation criterion and maximality,
and construct the common smooth interval and restart API. No H¹-uniform
restart conclusion or lower bound for the old selected horizon is claimed.
The revised proposition does not display a separate H¹-uniform clause.

Resolved errors include `HasDerivAt.one_div` (use `.inv`) and module-instance
side goals from `convert` (use `convert!`); exact details are in ATTEMPTS_B3.

## 4. Commands and results

All Lean commands use `. scripts/lean-env.sh`, the verification environment,
and `LEAN_NUM_THREADS=6`.

- Module build: passed (2653 jobs).
- Constant / explicit cubic ODE / endpoint probes: passed.
- Axiom probe: all six standard-only checks passed.
- Required article audit (`--build --output-dir tmp/article-audit --workers 2`):
  passed, 69 declarations / 27 entries / zero forbidden-axiom results. Reviewed
  and copied report.json to AXIOM_AUDIT.json.
- `python3 experiments/check_formalization_plan.py`: passed after refreshing
  the audit; generated graph now agrees with the inherited proof_graph.json.
- `make check`: source packaging and 32-contract registry passed; policy suite
  10/11 passed. Inherited failure in
  `test_recoloring_a_missing_clause_cannot_hide_whole_statement_partial`:
  `AssertionError: AssertionError not raised`, test_contract_policy.py:34.
  The test chooses C35_FULL, already Closed before this lane, then expects
  setting it Closed to contradict whole-statement coverage. Both facts are
  confirmed against the starting commit (`ef2cc079^`). Test left unchanged.
- `make test`: passed (11015 jobs / standard-only contract axiom checks).
- `make paper`: passed, both PDF logs clean and reader checks passed;
  generated PDF churn restored.
- `make test-mutations`: passed; implementation refactor accepted, admitted
  proof / extra axiom / weakened hypothesis rejected as required.
- `git diff --check`: passed.

Logs: ignored `tmp/b3-{article-audit,check,test,mutations,paper}.log`, with
per-environment audit logs under `tmp/article-audit/`.

Closed proof steps were committed separately. No push, merge or rebase.
The pre-existing untracked lane brief remains untouched.
