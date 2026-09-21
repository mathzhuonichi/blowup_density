# Lane 508 — P21 Route B, B4 on T³

Status: **B4-T³ closed.** `h1RestartT` is proved. P6 / L21_H1 remains Partial;
B5 owns endpoint registration and article coverage changes.

## 1. Statements

`NSFormalization.Section3.T11.h1RestartT` in
`Section3/T11/H1Restart.lean:576` proves precisely:

```lean
∀ ν, 0 < ν → ∀ f, f ∈ forceClassT → ∀ S, 0 ≤ S →
  ∀ K : ℝ≥0∞, K ≠ ⊤ → ∃ δ > 0,
    ∀ t₀ ∈ Icc 0 S, ∀ a' ∈ initialClassT, periodicSobolevENorm 1 a' ≤ K →
      ∃ w : ClassicalSolutionT ν a' (timeShiftT t₀ f) δ,
        PeriodicLocalRegularity ν a' (timeShiftT t₀ f) δ w
```

The quantifier order is unchanged: δ precedes BOTH t₀ and a'. The module uses
canonical T10/T11 types. The probe checks transport to the contract's distinct
solution structure with the existing binding. A separate generated temporary
probe also proves the literal `BlowupDensity.Research.P21.h1RestartT` Prop
from the unchanged text of `Targets.lean`.

The 23 proved declarations include:

- Full H¹/H² identities in B2's carriers, and all three B0 energy equalities.
  Ordered Hessian energy equals Laplacian energy by periodic Parseval;
  ordinary energy retains the nonzero mean.
- `enstrophy_differential_on_IccT'`, with no spatial bridge hypotheses;
  `enstrophy_differential_smoothT`, usable on positive force shifts.
- Initial-endpoint continuity, interior differentiability, the squared
  shifted force cap and the compact real/extended-integral conversion.
- Uniform running and endpoint dissipation bounds, choosing D=min d 1
  before shift and datum. The B3 force parameter is cap.toReal².
- H³ energy/Grönwall under smooth periodic forcing; H³ Picard/gluing
  extension for shifted test forces; maximal existence for smooth periodic
  forces; and a strict uniform lower bound on the maximal lifespan.
- The exact H¹ restart conclusion, using δ=D and
  `periodicLocalRegularity_of_classical'` for the full three-field bundle.

The fixed-force R1 route is used. No rough-data existence claim, selected-H³
horizon lower bound, cross-force H¹ result or named-input closure is asserted.
The revised Proposition 2.1 does not display a separate H¹-uniform clause;
this proves the retained stronger obligation recorded in Targets.lean.

## 2. Files

- `formalization/NSFormalization/Section3/T11/H1Restart.lean`.
- `formalization/blueprint/entrypoints.json`: new proof module registered.
- `research/P21/probes/b4t_closes.lean`: explicit datum e₀, zero force,
  restart time 1/2, nonzero returned initial velocity; contract-vocabulary
  transport; must-fail infinite-cap mutation under `#guard_msgs`.
- `research/P21/axioms_b4t.lean`: all 23 exports printed and checked, with an
  additional exact-set check for `[propext, Classical.choice, Quot.sound]`.
- `research/P21/ATTEMPTS_B4T.md`: route, force-scope repair and actual errors.
- `research/P21/P6_SPLIT.md`: B4-T³ status and exact B5 handoff.
- `research/P21/REPORT_508.md`: this report.
- `formalization/blueprint/AXIOM_AUDIT.json` and generated
  `DEPENDENCY_GRAPH.md`: refreshed by the required audit/generation gates.
  These synchronize stale generated artifacts with inherited article targets
  and statuses; they make no new B4 article-coverage claim.

No protected B0/B2/B3 module, contract, binding, registry, authoritative
proof_graph.json, blueprint status or paper source was edited. Lane 507's
module was read for the route and was not copied into this worktree.

## 3. Gaps and error text

**No remaining B4-T³ mathematical gap.** All module and consumer proofs
compile without admissions, custom axioms or heartbeat overrides.

A required route correction was the force-class mismatch: B2 and the
registered `extendsBeyondH3` require forceClassT, while generic positive
shifts need not vanish near their new initial time. This is resolved here,
not assumed away. The differential estimate is rebuilt from the existing
smooth-force energy identity and B2 physical estimates. Continuation reuses
`torusPairingBound_slice`, `torusGronwallChain`,
`periodicQuantitativeLocalInputH3` and `glueClassicalSolutionT` under the
correct smooth/periodic and finite shifted L¹-force hypotheses. The result
needed for the contradiction is a larger realized horizon, so no new
normalized-pressure overlap theorem is necessary at that step.

The endpoint passage uses B3's `enstrophy_endpoint_lintegral`, matching
`squaredHTwoIntegralT` directly. Compact integrability was already proved
before passing to the endpoint. It does not rely on bounds for totalized
nonintegrable real integrals.

Resolved compiler errors included a real/natural Sobolev-index rewrite
mismatch (`Did not find an occurrence of torusRealPairing G F`), an unsolved
expanded Fourier-sum equality, and the need for explicit endpoints in
`Continuous.intervalIntegrable`. Full details are in ATTEMPTS_B4T.md.
The negative mutation intentionally produces `error: unsolved goals / ⊢ False`
when it attempts to use K=⊤ without the required finite-ball hypothesis.

B5 remains separate. `RestartBeyond.lean:408` uses its named input only via
`restart H`; replacing that one application with `h1RestartT` supplies its
entire analytic input. The exact endpoint target and quantifier order are
recorded in P6_SPLIT.md. No new sup-force input predicate is needed.

## 4. Commands and results

All Lean commands used `scripts/lean-env.sh`, the verification Lake environment
and `LEAN_NUM_THREADS=6`. Logs are under ignored `tmp/b4t-*.log`.

- Required module build: passed, 10674 jobs.
- Direct module checks after every closed lemma: passed.
- `lake env lean ../research/P21/probes/b4t_closes.lean`: passed, including
  explicit nonzero datum, contract transport and expected failed mutation.
- `lake env lean ../research/P21/axioms_b4t.lean`: passed; all 23 exports have
  exactly the three standard axioms (including the primed compact theorem).
- Direct generated target probe `tmp/b4t-target.lean`: passed against the
  actual unchanged Targets.lean definition.
- `python3 experiments/audit_article_axioms.py --build --output-dir tmp/article-audit --workers 2`:
  passed before make check; 72 declarations, 27 article entries, zero
  forbidden-axiom results and no forbidden source tokens. Reviewed report
  copied to AXIOM_AUDIT.json.
- `python3 experiments/check_formalization_plan.py`: passed; generated graph
  synchronized with inherited authoritative statuses.
- `make check`: passed; 2271 source modules, 34 registered contracts, all
  11 policy tests. The old C35_FULL policy-fixture failure is absent here.
- `make test`: passed, 11027 jobs.
- `make test-mutations`: passed; implementation refactor accepted, admitted
  proof / extra axiom / weakened hypothesis rejected.
- `make paper`: passed; both PDF logs clean and reader-document checks pass.
  Generated PDF-only churn was restored; no paper or PDF changes remain.
- Temporary `tmp/b4t-endpoint-handoff.lean`: passed; it compiles the existing
  `restartBeyond` proof with only its H binder removed and its `restart H`
  call replaced by `h1RestartT`. Thus the B5 consumption claim was tested.
- `git diff --check`: passed. Protected modules, authoritative graph,
  contracts, registry and paper sources have no lane diff.

All closed lemmas have separate `[508-P21-B4T]` commits. No push, merge,
rebase, external message or sub-agent launch was performed.
