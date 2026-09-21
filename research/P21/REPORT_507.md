# Lane 507 — P21 Route B, B4 on R³

Status: **B4 closed, unconditionally.** P6 / L21_H1 registration remains Partial;
torus and B5 registration are separate. No reviewed B0/B1/B3 module was edited.

## 1. Theorem proved

`NSFormalization.Section4.A04.h1RestartR` proves the exact local-name form of
`research/P21/Targets.lean:h1RestartR`:

```lean
∀ ν, 0 < ν → ∀ f, MemForceR f → ∀ S, 0 ≤ S → ∀ K : ℝ≥0∞, K ≠ ⊤ →
  ∃ δ > 0, ∀ t₀ ∈ Icc 0 S, ∀ a' ∈ initialClassR,
    sobolevENorm 1 a' ≤ K →
      ∃ w : ClassicalSolutionR ν a' (timeShift t₀ f) δ,
        A01.ManuscriptLocalRegularity ν a' (timeShift t₀ f) δ w
```

One δ precedes both restart time and datum. It is obtained from a strict lower
bound on the maximal lifespan, **not** on the existing selected high-order
`A01.localHorizon'`. No bridge, nonlinear estimate, local supplier or extension
principle remains as an assumption.

The research probe additionally proves the literal target Prop after the
existing contract solution/regularity conversions. `h1RestartAt` provides B5's
per-time `ofReal (t₀+δ) ≤ maximalLifespanR` conclusion. B5 can apply
`restartBeyond_of_restartAt` and halve the margin for the strict endpoint target.

Two normalization corrections matter:

- The registered datum uses angular frequency; B1 is instantiated at **κ=1**.
- B0's cap bounds the L² norm; the real squared-force cap is
  **`(forceL2CapR f S).toReal ^ 2`**.

## 2. What is in Lean

- `Section4/A04/H1BridgesSmooth.lean`: five theorems, including the support-free
  Sobolev successor identity, exact order-zero/H¹/H² physical energies, and
  Frobenius gradient norm equality. D01's sharp datum-raising identity and
  weak-derivative pairing already supply the support-free Fourier argument.
  A05's Hessian/Laplacian identity supplies the second-derivative conversion.
- `Section4/A04/H1Restart.lean`: twelve theorems, including the unconditional
  enstrophy inequality, common squared-force cap, time regularity, finite slice
  norms, compact integral conversion, uniform running and endpoint dissipation,
  maximal-lifespan contradiction, full `h1RestartR`, and `h1RestartAt`.
- Arbitrary classical regularity uses `classical_hasSmoothSobolevPath`, whose
  proof uses uniqueness on overlapping selected-carrier windows, together with
  A01's general pressure recovery, projected equation and pressure potential.
- The endpoint passage uses B3's `enstrophy_endpoint_lintegral` and proves the
  conversion to the registered integrand on each finite-norm slice. It bounds
  `squaredHTwoIntegral` directly; no global measurability assertion about
  unconstrained times is needed.
- Both modules are in `entrypoints.json` `proof_modules`.
- `probes/b4_closes.lean`: actual `Targets.h1RestartR` transport, a concrete
  ν=1 / zero-force / zero-datum / K=0 instance, and the must-fail bound deletion.
- `axioms_b4.lean`: all 17 exported proof-module theorems print **exactly**
  `[propext, Classical.choice, Quot.sound]`; automated standard-axiom checks pass.
- `ATTEMPTS_B4.md` records routes and resolved elaboration errors;
  `P6_SPLIT.md` records the B5 API and normalization corrections.

Authorized existing-file edits are entrypoints, the B4 research handoff and the
required generated audit/graph refresh. The inherited audit and generated graph
were stale relative to the existing guide and `proof_graph.json`; regeneration
reflects those inherited article changes. **No contract, binding, registry,
authoritative blueprint-status, or paper source is changed.**

## 3. Gaps

No B4 analytic hypothesis or residual Lean goal remains. This lane is R³ only;
no torus theorem, rough-H¹ local theory, broader force-class theorem or final
contract registration is claimed. The revised proposition states local existence
and integral continuation; its displayed text does not itself contain the
separate H¹-uniform sentence.

The isolated bound-deletion mutation exits 1 with the exact residual:

```text
error: Tactic `assumption` failed
...
ha : a ∈ initialClassR
⊢ sobolevENorm 1 a ≤ K
```

This checks that the same supplier application needs the H¹ bound; it is not a
claim to have disproved unrestricted uniform existence.

## 4. Commands and results

All Lean commands source `. scripts/lean-env.sh`, run Lake from `verification/`,
and set `LEAN_NUM_THREADS=6`.

- `lake build NSFormalization.Section4.A04.H1Restart`: passed; both new modules
  and dependency closure built. Direct module checks pass without warnings.
- Exact target and non-vacuity/mutation probe: passed. Commands from verification:

  ```sh
  lake env lean -R .. -o ../tmp/research/P21/Targets.olean ../research/P21/Targets.lean
  lake env bash -c 'export LEAN_PATH="../tmp:$LEAN_PATH"; lean ../research/P21/probes/b4_closes.lean'
  ```

  Create `tmp/research/P21` from the repository root first. The temporary `.olean`
  imports the actual research target, not a duplicate statement.
- `lake env lean ../research/P21/axioms_b4.lean`: passed, all 17 exact standard
  axiom sets also compared mechanically with the required set.
- Isolated temporary mutation clearing `hnorm`: rejected as intended (exit 1),
  exact missing-bound error above; positive probe exits 0.
- `python3 experiments/audit_article_axioms.py --build --output-dir tmp/article-audit --workers 2`:
  passed, **72 declarations / 27 article entries / zero forbidden-axiom results**.
  Reviewed generated report and refreshed `AXIOM_AUDIT.json`.
- First `make check` stopped at `Regenerate the dependency graph`.
  `python3 experiments/check_formalization_plan.py` regenerated the inherited
  stale graph. Rerun `make check`: passed, **41 nodes / 27 article mappings /
  2271 source modules / 34 contracts / all 11 policy tests**.
- `make test`: passed, 11027 build/test jobs and standard-only contract checks.
- `make test-mutations`: passed; implementation refactor accepted, admitted
  proof / extra axiom / weakened hypothesis rejected as required.
- `make paper`: passed, both PDF logs clean and reader-document checks passed.
  Generated PDF churn was restored; no paper or PDF change is retained.
- `git diff --check`: passed, including the final documentation and generated metadata.

Logs are in ignored `tmp/b4-*.log`; article environment logs are under
`tmp/article-audit/`. Each closed proof step was committed separately with the
required prefix. No push, merge, rebase or external message was performed.
