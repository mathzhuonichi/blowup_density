ACCEPT

## 1. What the lane claims

`research/R41/REPORT_249.md:5` claims full registration of Theorem 4.1 for `Y = F_R`, including all four reconciled fields. `verification/contracts.json:346` registers exactly that scope as `R41.main_thresholds`, V1, with `Tests.MainThresholds` in its compiled closure. The additions-only ledger diff preserves the existing state and owner. No existing Lean module was modified.

## 2. What is in Lean

1. **Statement fidelity — pass.** Read the paper with `sed -n '1,85p' paper/sections/04-whole-space.tex`: lines 8–11 give the two density statements, line 13 the numerical values and rider, and lines 32–42 the same-family insertion conclusions. Contract fields at `verification/Contracts/V1/MainThresholds.lean:23`, `:40`, `:54`, and `:79` preserve these statements. The structure text matches `research/R41/Spec.lean:48` after changing only its name and excluding trailing blank lines outside the declaration (the contract has one additional trailing blank line). No mathematical token or internal comment differs. `verification/Tests/MainThresholds.lean:18`, `:26`, `:35`, and `:41` independently restate the four field types.
2. **Density and bridges — pass.** The witness is `verification/Bindings/MainThresholds.lean:85`. It uses `verification/Bindings/DensityFromInsertion.lean:30` and `:53` for density. The only-if argument uses `formalization/NSFormalization/Section4/R41/NonDensity.lean:73`, with the actual `rMainThresholds` at `:37`; `verification/Bindings/MainThresholds.lean:34` splits the ENNReal exponent into precisely 1 and 2. The force-class and norm bridges at `:15` and `:17` are `rfl`; breakdown transport at `:21` and `:27` uses the structure-aware lifespan bridge `verification/Bindings/MaximalPartial.lean:130`. Also opened `research/R41D/axioms_nondensity.lean:31` for the supplier-side vocabulary audit.
3. **Rider — pass.** `verification/Bindings/MainThresholds.lean:100` calls `verification/Bindings/InsertionFromData.lean:87` exactly once. Reference uniqueness at `:107` identifies the named reference on `[0,T)`. Witnesses at `:117`, force membership/lifespan at `:120`, and the solution at `:122` all use that record. Suppliers were opened at `verification/Bindings/InsertionLifespan.lean:161`, `verification/Contracts/V2/InsertionLifespan.lean:129`, and `verification/Contracts/V1/InsertionFamily.lean:224`. Positive ε puts the history endpoint strictly below T (`Bindings/MainThresholds.lean:125`); the requested window is unchanged.
4. **Both limits — pass.** Force convergence uses `verification/Bindings/InsertionFromData.lean:121` at `Bindings/MainThresholds.lean:127`. Energy convergence at `:65` squeezes the canonical ENNReal norm by `verification/Contracts/V1/InsertionFamily.lean:313`, whose two positive powers vanish at zero. Slice congruence at `Bindings/MainThresholds.lean:50` transports spatial derivatives as well as velocities. `verification/Contracts/V1/Data.lean:444`, `:459`, and `:475` agree with the energy norm at `paper/sections/01-introduction.tex:143` (opened with `sed -n '136,150p'`). There is no conversion of an infinite norm through `.toReal`; the only relevant `.toReal` is the exponent, restricted to 1 or 2.
5. **Non-vacuity and hypotheses — pass.** Positive viscosity/horizon and admissible data are retained; the named reference is an actual `ClassicalSolutionR`, not an assumed analytic conclusion. `Data.lean:657`, `:672`, and `:702` define actual solution lifespan, breakdown membership, and positive-radius approximation. The worker already supplies density and both endpoint non-density instances at `research/R41/axioms_contract.lean:20`, `:28`, and `:36`. Additional reviewer probe `research/R41/probes/rev249_nonvacuity.lean:6` extracts an actual admissible force with lifespan at most 1 and norm distance less than 1 at q=2, s=-1. Its second example at `:15` proves a positive-length history window for a positive ε whenever T>0; shrinking ε below both that bound and ε₀ makes this compatible with the family's domain. Thus possible empty windows for large ε do not make the asymptotic history assertion vacuous.
6. **Hygiene/build — pass.** The three new production Lean files and audit file have no forbidden proof tokens and no `maxHeartbeats` setting. The sole text-search hit for `axiom` is the Tests docstring at `verification/Tests/MainThresholds.lean:5`, not a declaration. Contract imports only `Contracts.V1.Data` (`:1`). The base diff adds these Lean files rather than editing frozen files. All ten audit outputs are exactly `[propext, Classical.choice, Quot.sound]`. Direct binding elaboration is silent. Lake replays warnings from existing dependency modules; none originates in `Bindings/MainThresholds.lean`. The Tests audit intentionally prints its success message at `Tests/MainThresholds.lean:15`.
7. **Substantive negative check — pass.** `research/R41/probes/rev249_endpoint.lean:6` changes the zero-data density threshold from `<` to `≤`, preserving every argument. Reusing the actual proof fails at line 10 with the expected type mismatch. This is a false boundary change, independently contradicted by the worker's two endpoint non-density examples, rather than an argument-dropping test.

## 3. Gaps

No missing mathematical field or additional supplier hypothesis was found. The exclusions in `research/R41/REPORT_249.md:37` (other force classes and completed-space density) are scope exclusions, not claims that lemmas are absent from the tree. Consequently there is no missing-lemma claim to accept without searching. For completeness, a recursive `grep -rnE` over the entire Section4 tree for the named density/insertion/energy-convergence supplier names is reproduced below; the binding-layer suppliers were also opened directly.

The missing `research/R41/RECONCILIATION.md` reported at `REPORT_249.md:41` is confirmed. It is a pre-existing provenance limitation, not an omitted deliverable of this registration lane: the supplied Spec and binding plan are present and the contract matches the Spec. No statement decision or weakening was introduced here.

Required fixes: none.

## 4. Commands and results

All Lake invocations were sequential, from `verification/`, after `. scripts/lean-env.sh` and `export LEAN_NUM_THREADS=6`. No git mutation or edit to existing records/Lean files was performed. Only this report and the two authorized reviewer probes were added. Existing environment/cache was used; no installer or dependency mutation was needed.

Full raw gate outputs are local `/tmp/rev249_*.log` files. Below, short output is pasted in full; large outputs have exact first/last 20 lines, with an explicit omission marker to avoid embedding megabytes of closure JSON.

### `lake build Bindings.MainThresholds` — exit 0

```text
⚠ [8778/9046] Replayed NSFormalization.Source.FiniteHilbertBochner
warning: NSFormalization/Source/FiniteHilbertBochner.lean:24:19: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
warning: NSFormalization/Source/FiniteHilbertBochner.lean:23:37: This simp argument is unused:
  PiLp.single_apply

Hint: Omit it from the simp argument list.
  [apply] simp [h]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: NSFormalization/Source/FiniteHilbertBochner.lean:39:23: This simp argument is unused:
  PiLp.single_apply

Hint: Omit it from the simp argument list.
  [apply] simp [insert, coord]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
⚠ [9875/10022] Replayed NSFormalization.Source.BoundedReferenceFlux
warning: NSFormalization/Source/BoundedReferenceFlux.lean:17:5: Variable name `hU0` is not explicitly referenced.
[... 258 lines omitted ...]
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: NSFormalization/Source/FractionalRealization.lean:83:2: Try this: 
  letI̵

The goal is a proposition, so `let` is preferred over `letI`.
The difference between `let` and `letI` is that `letI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: NSFormalization/Source/FractionalRealization.lean:104:2: Try this: 
  letI̵

The goal is a proposition, so `let` is preferred over `letI`.
The difference between `let` and `letI` is that `letI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
Build completed successfully (10607 jobs).
```

### `lake env lean Bindings/MainThresholds.lean` — exit 0

Zero output (0 bytes).

### `lake build Tests.MainThresholds` — exit 0

```text
⚠ [8778/8894] Replayed NSFormalization.Source.FiniteHilbertBochner
warning: NSFormalization/Source/FiniteHilbertBochner.lean:24:19: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
warning: NSFormalization/Source/FiniteHilbertBochner.lean:23:37: This simp argument is unused:
  PiLp.single_apply

Hint: Omit it from the simp argument list.
  [apply] simp [h]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: NSFormalization/Source/FiniteHilbertBochner.lean:39:23: This simp argument is unused:
  PiLp.single_apply

Hint: Omit it from the simp argument list.
  [apply] simp [insert, coord]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
⚠ [9876/10609] Replayed NSFormalization.Source.BoundedReferenceFlux
warning: NSFormalization/Source/BoundedReferenceFlux.lean:17:5: Variable name `hU0` is not explicitly referenced.
[... 260 lines omitted ...]
Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: NSFormalization/Source/FractionalRealization.lean:83:2: Try this: 
  letI̵

The goal is a proposition, so `let` is preferred over `letI`.
The difference between `let` and `letI` is that `letI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: NSFormalization/Source/FractionalRealization.lean:104:2: Try this: 
  letI̵

The goal is a proposition, so `let` is preferred over `letI`.
The difference between `let` and `letI` is that `letI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
ℹ [10609/10609] Replayed Tests.MainThresholds
info: Tests/MainThresholds.lean:15:0: Contract BlowupDensity.Tests.checkedMainThresholds: checked; standard logical axioms only
Build completed successfully (10609 jobs).
```

### `lake env lean ../research/R41/axioms_contract.lean` — exit 0

```text
'BlowupDensity.Bindings.mainThresholds_forceClassR_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.mainThresholds_forceSobolevENorm_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.maximalPartial_maximalLifespanR_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.mainThresholds_breakdownSetR_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.mainThresholds_BreakdownDenseR_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.mainThresholds_nonDensity' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.mainThresholds_energy_congr' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.mainThresholds_energyConvergence' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.mainThresholds' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Tests.checkedMainThresholds' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### `make check` — exit 0

```text
python3 experiments/check_formalization_plan.py --check
{
  "task_count": 30,
  "source_counts": {
    "formalization": 547,
    "vendor/NavierStokesAndEuler": 2486,
    "vendor/HeliCorgi": 129
  },
  "source_manifest_entries": 2975,
  "missing_copied_imports": [],
  "citation_interfaces_reachable": [],
  "tokens_in_copied_umbrella_closure": [
    {
      "module": "NSFormalization.Paper1.BoundaryCorollary",
      "path": "formalization/NSFormalization/Paper1/BoundaryCorollary.lean",
      "line": 90,
      "token": "sorry"
    }
  ],
  "tracked_cache_free": true,
[... 33640 lines omitted ...]
      "NavierStokes.WeightedClasses",
      "NavierStokes.WeightedODEJets",
      "NavierStokes.WeightedQuotients",
      "NavierStokes.WeightedRadialPrimitive",
      "NavierStokes.ZerothStressIdentity",
      "TestSupport.Axioms",
      "Tests.MainThresholds"
    ]
  },
  "base_compatibility_checked": false,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.044s

OK
python3 experiments/check_work_queue.py
30 work items: ownership, contract registration and task cards consistent.
```

### `scripts/gates.sh` — exit 0

```text
== make check
python3 experiments/check_formalization_plan.py --check
{
  "task_count": 30,
  "source_counts": {
    "formalization": 547,
    "vendor/NavierStokesAndEuler": 2486,
    "vendor/HeliCorgi": 129
  },
  "source_manifest_entries": 2975,
  "missing_copied_imports": [],
  "citation_interfaces_reachable": [],
  "tokens_in_copied_umbrella_closure": [
    {
      "module": "NSFormalization.Paper1.BoundaryCorollary",
      "path": "formalization/NSFormalization/Paper1/BoundaryCorollary.lean",
      "line": 90,
      "token": "sorry"
    }
  ],
[... 33685 lines omitted ...]
info: Tests/EnergyHighPartialV2.lean:30:0: Contract BlowupDensity.Tests.checkedEnergyHighPartialV2: checked; standard logical axioms only
info: Tests/DatumLemmasV3.lean:31:0: Contract BlowupDensity.Tests.checkedDatumLemmasV3: checked; standard logical axioms only
info: Tests/Correction.lean:19:0: Contract BlowupDensity.Tests.checkedCorrection: checked; standard logical axioms only
info: Tests/MaximalPartial.lean:16:0: Contract BlowupDensity.Tests.checkedMaximalPartial: checked; standard logical axioms only
info: Tests/Uniqueness.lean:16:0: Contract BlowupDensity.Tests.checkedUniqueness: checked; standard logical axioms only
info: Tests/HomogeneousNorm.lean:17:0: Contract BlowupDensity.Tests.checkedHomogeneousNorm: checked; standard logical axioms only
info: Tests/HomogeneousPartialV2.lean:35:0: Contract BlowupDensity.Tests.checkedHomogeneousPartialV2: checked; standard logical axioms only
info: Tests/MaximalPartialV2.lean:24:0: Contract BlowupDensity.Tests.checkedMaximalPartialV2: checked; standard logical axioms only
info: Tests/InsertionLifespanV2.lean:32:0: Contract BlowupDensity.Tests.checkedInsertionLifespanV2: checked; standard logical axioms only
info: Tests/TameProduct.lean:14:0: Contract BlowupDensity.Tests.checkedTameProduct: checked; standard logical axioms only
info: Tests/MainThresholds.lean:15:0: Contract BlowupDensity.Tests.checkedMainThresholds: checked; standard logical axioms only
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

### `python3 experiments/check_contracts.py --base-ref origin/erenup/integration` — exit 0

```text
{
  "registered_contracts": 32,
  "closures": {
    "R41.threshold_arithmetic": [
      "Bindings.Thresholds",
      "Contracts.V1.Thresholds",
      "NSFormalization.Paper3.Thresholds",
      "TestSupport.Axioms",
      "Tests.Thresholds"
    ],
    "I01.packet": [
      "Bindings.Packet",
      "Contracts.V1.Packet",
      "NSFormalization.Paper1.ScalarEnergy",
      "NSFormalization.Section4.I01.Energy",
      "NSFormalization.Section4.I01.Extension",
      "NSFormalization.Section4.I01.Quiet",
      "NSFormalization.Source.Insertion",
      "NSFormalization.Source.PacketEndpoint",
      "NSFormalization.Source.PacketEnergy",
[... 33608 lines omitted ...]
      "NavierStokes.ViscousPropagator",
      "NavierStokes.VolterraAnalyticBounds",
      "NavierStokes.VolterraParity",
      "NavierStokes.VolterraRegularity",
      "NavierStokes.WaveEdgeExtension",
      "NavierStokes.WaveEnvelopeTransport",
      "NavierStokes.WaveInteractionBounds",
      "NavierStokes.WaveStateRegularity",
      "NavierStokes.WeightedClasses",
      "NavierStokes.WeightedODEJets",
      "NavierStokes.WeightedQuotients",
      "NavierStokes.WeightedRadialPrimitive",
      "NavierStokes.ZerothStressIdentity",
      "TestSupport.Axioms",
      "Tests.MainThresholds"
    ]
  },
  "base_compatibility_checked": true,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
```

### `lake env lean ../research/R41/probes/rev249_endpoint.lean` — exit 1

```text
../research/R41/probes/rev249_endpoint.lean:10:2: error: Type mismatch
  mainThresholds.zeroInitialDensityIff
has type
  ∀ (ν : ℝ),
    0 < ν →
      ∀ (T : ℝ),
        0 < T →
          ∀ (q : ℝ≥0∞),
            q = 1 ∨ q = 2 →
              ∀ (s : ℝ), RelativelyDense q s forceClassR (breakdownSetRZero ν T) ↔ s < criticalOrder q.toReal
but is expected to have type
  ∀ (ν : ℝ),
    0 < ν →
      ∀ (T : ℝ),
        0 < T →
          ∀ (q : ℝ≥0∞),
            q = 1 ∨ q = 2 →
              ∀ (s : ℝ), RelativelyDense q s forceClassR (breakdownSetRZero ν T) ↔ s ≤ criticalOrder q.toReal
```

### `lake env lean ../research/R41/probes/rev249_nonvacuity.lean` — exit 0

Zero output (0 bytes).

Exact structure comparison (excluding trailing blank lines outside the declaration): `True`.

`git diff --name-only origin/erenup/integration...HEAD` — exit 0

```text
collaboration/TASKS.md
collaboration/tasks/R41.md
collaboration/work_items.json
research/R41/ATTEMPTS_CONTRACT.md
research/R41/COMPARISON.md
research/R41/REPORT_249.md
research/R41/axioms_contract.lean
verification/Bindings/MainThresholds.lean
verification/Contracts/V1/MainThresholds.lean
verification/Tests/MainThresholds.lean
verification/contracts.json
```

`git diff --stat verification/contracts.json` — exit 0

Zero output.

`git diff --stat origin/erenup/integration...HEAD -- verification/contracts.json` — exit 0

```text
 verification/contracts.json | 11 +++++++++++
 1 file changed, 11 insertions(+)
```

`git diff --check` — exit 0

Zero output.

The working-tree registry diff is empty because the worker committed it; the base-to-HEAD diff confirms 11 insertions and no deletions.

`grep -rnE 'energyConvergence|breakdownDenseR_of_subcritical|not_breakdownDenseR_zero_of_q|insertionLifespanV2_of_data' formalization/NSFormalization/Section4` — exit 0:

```text
formalization/NSFormalization/Section4/R41/NonDensity.lean:73:theorem not_breakdownDenseR_zero_of_q (thresholds : RMainThresholds) :
formalization/NSFormalization/Section4/R41/NonDensity.lean:117:  not_breakdownDenseR_zero_of_q rMainThresholds 1 (Or.inl rfl) 1 1
formalization/NSFormalization/Section4/R41/NonDensity.lean:122:  not_breakdownDenseR_zero_of_q rMainThresholds 2 (Or.inr rfl) 1 1
```

`rg -n '\b(sorry|admit|axiom|native_decide)\b|maxHeartbeats' verification/{Bindings,Contracts/V1,Tests}/MainThresholds.lean research/R41/axioms_contract.lean` — exit 0, sole output:

```text
verification/Tests/MainThresholds.lean:5:/-! Four literal Spec-field conformance checks and a transitive axiom audit. -/
```

ACCEPT — fixes: none.
