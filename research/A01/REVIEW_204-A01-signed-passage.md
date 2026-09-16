ACCEPT

## 1. What the lane claims

Reviewed commit `cf38e9a3f2103016591ac481a32241a7362e49bb`, against local remote-tracking integration `4d7725c6c2f02ac1923bfa4b8ce9d1cd4690907f`. No fetch, rebase, merge, commit, index change, or source edit was performed. Only this report and the permitted negative probe were added; command logs are outside the checkout in `/tmp/rev204_*.log`.

The three displayed statements in `research/A01/REPORT_204.md:12`, `:22`, and `:33` match `formalization/NSFormalization/Section4/A01/SignedPassage.lean:547`, `:618`, and `:630` exactly. Below, S means that SignedPassage file; L means `formalization/NSFormalization/Section4/A01/SignedLimit.lean`; P means `formalization/NSFormalization/Section4/A01/MildEnergyPremises.lean`. All abbreviated citations are file:line references to these paths.

The report correctly claims closure of the signed passage, not unconditional closure of the forcing estimate or A01. The target is the existing predicate L:98, including arbitrary strong maximal limit U, every positive epsilon, explicit interval integrability, both closed endpoints, actual cylinder forcing, and the full negative gradient square. S:547 adds no analytic assumption. All 27 module declarations and four zero-data helpers exist and are audited.

Paper fidelity: opened with `sed -n` the whole-space local-theory invocation at `paper/sections/04-whole-space.tex:50`, the local existence/continuation statement at `paper/sections/02-preliminaries.tex:105`, and the higher-order signed energy estimate and regularized norm division at `paper/sections/appendix-a-local-theory.tex:128`–145. The latter is the precise mathematical role of this auxiliary cylinder theorem. It is not a claim that the paper literally states this cylinder predicate or that the remaining tame estimate is proved. The sign, regularization, solenoidal cancellation, and order of limit then absorption agree with that argument.

## 2. What is in Lean

1. **Finite level and FTC.** `MildEnergyEnvelope.lean:72` (same A01 directory) differentiates the squared full word norm with source coefficient 2 and dissipation coefficient −2ν. S:222 invokes that exact identity and identifies its gradient sum through `toJet_word`. S:214 proves r_n²=x. S:153 differentiates sqrt(x+ε²) using `HasDerivAt.sqrt` at S:171; the divisor is 2 sqrt(x+ε²), giving exactly −ν, not a lost factor of two. Strict positivity follows from ε>0 and x≥0 at S:163. The interior derivative and continuous paths feed `intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le` at S:169. The resulting S:183 theorem states the requested finite-level inequality with −ν*d_n and its integrability.

2. **Cancellation and genuine forcing.** S:89 specializes identity-metric transport cancellation; the coefficient derivative bound is literally zero. S:124 uses this with the velocity's divergence-free constraint. S:127 uses `pressure_pairing_zero`, `regularizedWordBlock_gradient`, and `regularized_word_divergenceFree`. Opened the underlying statements at `vendor/NavierStokesAndEuler/Euler/SobolevMetricTransport.lean:72`, `Euler/EulerProof.lean:1344`, `Euler/RegularizedWordConvergence.lean:60`, and `Euler/RegularizedWordEquation.lean:73` (all under the same vendor root). Only after the exact cancellations does S:144 apply family Cauchy–Schwarz. The forcing at S:44 is exactly the source-plus-transport-plus-pressure `forcingWordPath` family. S:308 proves its strong time-L² convergence to `cylinderEnergyForcing`, not to a substitute: S:320 reindexes the same U; S:322 uses `ForcedSourceUpgrade.sourceTime_restriction` (`formalization/NSFormalization/Section4/A01/ForcedSourceUpgrade.lean:53`), S:324 uses P:92 for pressure, and S:326 uses P:250 for adjacent force restrictions. S:327 invokes `regularizedWeightedForcing_tendsto`; singleton weight one reduces the finite family and the target identification ends by rfl. Compared directly with the canonical definition P:260.

3. **Which convergences, and the dissipation sign.** S:67 uses `regularizedValueFamily_tendsto` and `metricPath_tendsto` for uniform roots. This is the singleton identity-metric specialization of the suggested `weightedMetricPath_tendsto`, not a missing convergence. Opened `vendor/NavierStokesAndEuler/Euler/RegularizedEnergyFamily.lean:44` and `:89`, and `Euler/MetricPathConvergence.lean:39` and `:60`. Lane 203's `maximal_word_square_integral_limit` (L:45) proves an unweighted whole-window fact. S:368 supplies the stronger varying-weight/subinterval fact directly from the same strong TimeLp premise, so it does not need to invoke L:45 by name.

   The full gradient is the bounded Hilbert-family map S:405. S:422 reindexes all prepended/appended words by `Fin.consEquiv` and `Fin.snocEquiv`; no coordinate is discarded and no cardinality constant appears. S:443 identifies the finite dissipation exactly, and S:465 identifies its limit almost everywhere with P:304's `energyGradientNorm U` squared. S:487 proves **equality of the weighted dissipation integral limits by strong convergence**, not lower semicontinuity. S:611 passes the finite inequalities using `hfl.sub (hgl.const_mul ν)`, retaining the negative sign without reversing an inequality.

4. **No unjustified dominated convergence.** A uniform L¹ norm bound alone is not a common pointwise majorant. The report/attempts correctly avoid that shortcut. Analytically sqrt(r_n²+ε²)≥ε>0; the code needs only nonvanishing plus continuity of the path-valued inverse at S:478 and S:505. On the compact interval this gives uniform weight convergence. S:345 proves joint multiplier continuity with the explicit estimate ‖M(c_n)v_n−M(c)v_n‖₂ ≤ ‖c_n−c‖∞‖v_n‖₂. S:376 uses Lipschitz continuity of the norm on L², S:386 obtains integrability from a product of two L² functions, and S:398 passes their subinterval inner products. Thus there is no claimed dominating function whose integrability has been omitted. The forcing product similarly uses L²×L² integrability and inner-product convergence at S:270 and S:279.

5. **Endpoints, representatives, and non-vacuity.** S:167–179 use derivatives only in (0,t), with t≤T, while continuity holds on the closed interval. S:275–288 and S:388 restrict integrability from Icc 0 T to Icc 0 t using t≥0; S:515 transfers a.e. identities to uIoc 0 t. Both t=0 and t=T are covered, including T=0. No endpoint value or derivative of an arbitrary Lp representative is assumed. S:584 assembles the requested `IntervalIntegrable H volume 0 t`. No ENNReal `.toReal` or hidden finiteness premise occurs in the new module. The target's `let _solenoidal := ha` is computationally unused, but the theorem's actual proof uses ha at S:594 through P:116, which supplies the finite cancellation premise; it is not a vacuous theorem binder. P:137 supplies existence of the strong maximal limit for genuine mild competitors; `RootComparison.lean:164` invokes it in the downstream assembly. The passage correctly quantifies over any such U rather than assuming existence without a supplier.

   `research/A01/axioms_signed_passage.lean:25` proves the zero mild equation, `:43` uses uniqueness to establish the forcing predicate for every zero-data competitor, and `:58` gives positive-horizon (S=1) finite energy. This is genuine zero-data non-vacuity, not evidence for a universal tame hypothesis. The nonzero scalar dissipating path at `:71` also compiles. The zero-horizon example at `:68` is merely a trivial integrability check; endpoint coverage of the main result comes from the proof above.

6. **Compositions and exact remaining hypotheses.** Besides the common hq, hν, a, ha, F, hF parameters, S:618 requires exactly `(hb : 0 ≤ E * ‖sobolevPath F hF (q+1)‖)` and `(hFB : ForcingFamilyBound hq hν a F hF E A)`. S:630 instead requires exactly `(hE : mildNormConstant q ≤ E)` and the same hFB. No hpass remains. L:175 derives the sign from hE and `mildNormConstant_nonneg`, explaining why it is not a separate finite-energy premise. The unchanged forcing predicate is P:314; it does not silently acquire solenoidality or a finite-level forcing estimate.

7. **Hygiene and integration.** The three-dot diff lists only the new Lean module, three new records/audit files, and the requested A3_SPLIT row edit (`research/A01/A3_SPLIT.md:73`). No existing Lean or verification module changed. The new module and its audit have no `sorry`, `admit`, `axiom`, `native_decide`, or heartbeat override. All 31 printed axiom sets are exactly `[propext, Classical.choice, Quot.sound]`; declarations were counted independently. The inherited `ForcedSourceUpgrade.lean:51` has an 800000 setting, but it is pre-existing and not introduced or modified by this lane; the ≤400000 rule is satisfied by the lane's additions.

   The branch does descend from pre-merge lane-203 commit f38bced. However, comparison with integration finds **no SignedLimit difference**: both Git blobs are `0137388d4209fa9cd8e3352d8a7ccae4e48e6e11`. Thus integration's SignedLimit content is already what was checked; no source conflict or duplicate theorem is reproduced. A later lead rebase must preserve that version and rerun gates if its dependency content changes. Reviewer did not rebase under the read-only instructions.

## 3. Gaps

No remaining analytic gap in the signed passage was found. No required lane-204 fix.

The forcing-side gap remains real and isolated. Ran the required whole-tree `grep -rnE` for `SmoothCylinderCoordinateTame|CylinderCoordinateTame|CylinderCommutatorBound|ForcingFamilyBound|weighted.*square|dissipation_limit` over `formalization/NSFormalization/Section4`. Opened the closest suppliers: `ForcingFamilyBound.lean:53`, `:146`, `:186`, L:45, and S:487. The current lane has conditional commutator-to-forcing assembly, not an unconditional commutator estimate. The report does not assert that the completed signed passage is absent from the tree. The historical claim about the vendor helper was checked against `vendor/NavierStokesAndEuler/Euler/TimeLpSubinterval.lean:74`: its statement has no dissipation slot.

**Exact end-to-end chain across current branches.** Read lane 205 through `git show erenup/205-A01-coordinate-tame:...`, without changing checkouts. Its `formalization/NSFormalization/Section4/A01/CoordinateTame.lean:135` defines the sole smooth analytic input. For each q≥6, given `SmoothCylinderCoordinateTame q hq (C q)`, `cylinderCoordinateTame` (:150) supplies the finite estimate; `cylinderCommutatorBound_recut` (:202) uses `coordinateTameA q (C q) := max (A q) (C q / 4)` (:191); `forcingFamilyBound_of_cylinder_recut` (:221) supplies `ForcingFamilyBound ... (E q) (coordinateTameA q (C q))`. `ForcingFamilyBound.lean:22` defines E q = mildNormConstant q, so S:630 applies with hE=le_rfl. This gives `FiniteMildEnergy` at every q with the enlarged A. Then `MildGronwall.lean:171` gives `MildGronwall` with coefficient `(coordinateTameA q (C q))²/(4ν)`, and `hb_of_base'` (:204) gives the all-order `HasAprioriBound` family (`hb`); `hb_of_base_inv'` (:221) gives its angle-invariant version. The explicit radius is `AprioriFamily.lean:166`, with the same E and squared/absorbed A.

This chain still takes the standard bounded base mild solution u₆, hR and h₆ on a positive local horizon, plus the stated smooth data and ν>0; these are not new analytic assumptions on the passage. Base local existence is the `exists_local_quadratic_mild` invocation in `AprioriFamily.lean:113`, while :106 exports its base bound. An estimate at only one q is insufficient for all-order hb: the smooth input must be supplied for every q≥6 (or as an existential constant family). The old-constant alternative is lane 205's `forcingFamilyBound_of_smooth` (:267), assuming `SmoothCylinderCoordinateTame q hq (4*A q)`. This is a statement-level cross-branch composition, not a claim that both branch modules were imported and jointly compiled in this checkout. Lane 205 explicitly reports its smooth estimate unproved; no claim of unconditional A01 closure is accepted.

## 4. Commands and results

Read CLAUDE.md, lane-review SKILL.md, top 40 LESSONS lines, HANDOFF §0/P7, the supplied brief, worker report/attempts, lane-203 report/attempts, and lane-201 review. Existing shared package symlink was verified; no installer was needed. Every Lake invocation was sequential, after `. scripts/lean-env.sh`, from verification/, with `LEAN_NUM_THREADS=6`. `make check`, `make test`, mutation and scripts gates ran from the worktree root. Verification was untouched, but the full gates script and explicit base contract check were run anyway. Standard Lake output replays inherited diagnostics; the new module itself is silent, and direct checking is exactly zero bytes. The gates script masks some subprocess statuses, so make test and make test-mutations were also run independently and their exit statuses checked.

**Substantive negative test:** `research/A01/probes/rev204_doubled_dissipation.lean:22` copies the finite-level theorem with its proof intact and changes only −ν*d to −(2ν)*d in its conclusion (both integrability integrand and inequality). No argument was dropped. Lean exits 1 at :79 with the expected mathematical type mismatch: H proves the ν coefficient while the target requires 2ν. The worker's nonzero scalar control at `axioms_signed_passage.lean:85` independently refutes the corresponding stronger derivative comparison. The failed probe is intentional and must not be treated as a production module.

Raw logs below quote at most the first and last 40 lines of each command; long build/check/test logs use only the first and last 10. Omission markers are editorial.

### `cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.A01.SignedPassage`

Exit 0; 219 output lines; 12820 bytes.

```text
⚠ [8927/9614] Replayed NSFormalization.Source.FiniteHilbertBochner
warning: NSFormalization/Source/FiniteHilbertBochner.lean:24:19: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
warning: NSFormalization/Source/FiniteHilbertBochner.lean:23:37: This simp argument is unused:
  PiLp.single_apply

Hint: Omit it from the simp argument list.
  [apply] simp [h]

[middle omitted]

Note: This linter can be disabled with `set_option linter.unusedVariables false`
⚠ [10241/10251] Replayed NSFormalization.Section4.A01.MildGronwall
warning: NSFormalization/Section4/A01/MildGronwall.lean:150:31: Variable name `ha` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _ha

Note: This linter can be disabled with `set_option linter.unusedVariables false`
Build completed successfully (10251 jobs).
```

### `cd verification && LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section4/A01/SignedPassage.lean`

Exit 0; 0 output lines; 0 bytes.

No output.

### `cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/A01/axioms_signed_passage.lean`

Exit 0; 51 output lines; 3705 bytes.

```text
'NSFormalization.Section4.A01.signedWordPath' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.signedApproximationRoot' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.signedApproximationDissipation' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.signedApproximationForcing' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.signedApproximationRoot_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.signedApproximationRoot_tendsto' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A01.signed_transport_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.signed_source_pairing_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.signed_scalar_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.regularized_signed_energy_inequality' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A01.signed_subintervalWeight_tendsto' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A01.signed_forcing_integral_tendsto' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A01.signedRootCoefficient' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.signedRootCoefficient_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.signedApproximationForcing_tendsto' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A01.signed_scalar_multiplier_tendsto' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A01.signed_weighted_square_limit' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.signedGradientOperator' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.signedGradientOperator_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.signedGradientOperator_norm_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.signedApproximationDissipation_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A01.signedGradientOperator_ae' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.signedInverseRoot' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.maximal_weighted_dissipation_limit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
[middle omitted]
'NSFormalization.Section4.A01.cylinderSignedEnergyPassage' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.cylinderSignedRootLimit_of_forcingBound'' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A01.finiteMildEnergy_of_forcingBound''' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'_private._stdin.0.NSFormalization.Section4.A01.zero_value' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private._stdin.0.NSFormalization.Section4.A01.zero_sob' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private._stdin.0.NSFormalization.Section4.A01.zero_mild' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private._stdin.0.NSFormalization.Section4.A01.zero_forcing' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### `make check`

Exit 0; 28234 output lines; 1159606 bytes.

```text
python3 experiments/check_formalization_plan.py --check
{
  "task_count": 30,
  "source_counts": {
    "formalization": 520,
    "vendor/NavierStokesAndEuler": 2486,
    "vendor/HeliCorgi": 129
  },
  "source_manifest_entries": 2975,
  "missing_copied_imports": [],
[middle omitted]
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.042s

OK
python3 experiments/check_work_queue.py
30 work items: ownership, contract registration and task cards consistent.
```

### `make test`

Exit 0; 344 output lines; 21755 bytes.

```text
lake -d verification test
⚠ [8778/9176] Replayed NSFormalization.Source.FiniteHilbertBochner
warning: NSFormalization/Source/FiniteHilbertBochner.lean:24:19: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
warning: NSFormalization/Source/FiniteHilbertBochner.lean:23:37: This simp argument is unused:
  PiLp.single_apply

Hint: Omit it from the simp argument list.
  [apply] simp [h]
[middle omitted]
ℹ [10568/10573] Replayed Tests.MaximalPartialV2
info: Tests/MaximalPartialV2.lean:24:0: Contract BlowupDensity.Tests.checkedMaximalPartialV2: checked; standard logical axioms only
ℹ [10571/10573] Replayed Tests.InsertionLifespanV2
info: Tests/InsertionLifespanV2.lean:32:0: Contract BlowupDensity.Tests.checkedInsertionLifespanV2: checked; standard logical axioms only
ℹ [10572/10573] Replayed Tests.TameProduct
info: Tests/TameProduct.lean:14:0: Contract BlowupDensity.Tests.checkedTameProduct: checked; standard logical axioms only
ℹ [10573/10573] Replayed Tests.EnergyAbsorptionV4
info: Tests/EnergyAbsorptionV4.lean:18:0: Contract BlowupDensity.Tests.checkedEnergyAbsorptionV4: checked; standard logical axioms only
info: Tests/EnergyAbsorptionV4.lean:19:0: Contract BlowupDensity.Bindings.energyAbsorptionPartialV3_of_v4: checked; standard logical axioms only
info: Tests/EnergyAbsorptionV4.lean:100:0: Contract BlowupDensity.Tests.energyAbsorptionV4_terminalFinite: checked; standard logical axioms only
```

### `make test-mutations`

Exit 0; 349 output lines; 21996 bytes.

```text
python3 experiments/test_contract_mutations.py
⚠ [8778/9346] Replayed NSFormalization.Source.FiniteHilbertBochner
warning: NSFormalization/Source/FiniteHilbertBochner.lean:24:19: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
warning: NSFormalization/Source/FiniteHilbertBochner.lean:23:37: This simp argument is unused:
  PiLp.single_apply

Hint: Omit it from the simp argument list.
  [apply] simp [h]
[middle omitted]
info: Tests/TameProduct.lean:14:0: Contract BlowupDensity.Tests.checkedTameProduct: checked; standard logical axioms only
ℹ [10573/10573] Replayed Tests.EnergyAbsorptionV4
info: Tests/EnergyAbsorptionV4.lean:18:0: Contract BlowupDensity.Tests.checkedEnergyAbsorptionV4: checked; standard logical axioms only
info: Tests/EnergyAbsorptionV4.lean:19:0: Contract BlowupDensity.Bindings.energyAbsorptionPartialV3_of_v4: checked; standard logical axioms only
info: Tests/EnergyAbsorptionV4.lean:100:0: Contract BlowupDensity.Tests.energyAbsorptionV4_terminalFinite: checked; standard logical axioms only
implementation_refactor: accepted
admitted_proof: rejected as required
extra_axiom: rejected as required
weakened_hypothesis: rejected as required
Mutation suite passed. This is an infrastructure check, not a PDE proof.
```

### `cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/A01/probes/rev204_doubled_dissipation.lean`

Exit 1; 34 output lines; 1671 bytes.

```text
../research/A01/probes/rev204_doubled_dissipation.lean:79:2: error: Type mismatch: After simplification, term
  H
 has type
  ∀ t ∈ Icc 0 T,
    IntervalIntegrable
        (fun s =>
          (extendPath T hT (signedApproximationRoot n u) s *
                extendPath T hT (signedApproximationForcing hq n u (sourcePath (D.comp (timeInclusion hTS)) u) p) s -
              ν * extendPath T hT (signedApproximationDissipation n u) s) /
            √(x s + ε ^ 2))
        volume 0 t ∧
      √(x t + ε ^ 2) ≤
        √(x 0 + ε ^ 2) +
          ∫ (s : ℝ) in 0..t,
            (extendPath T hT (signedApproximationRoot n u) s *
                  extendPath T hT (signedApproximationForcing hq n u (sourcePath (D.comp (timeInclusion hTS)) u) p) s -
                ν * extendPath T hT (signedApproximationDissipation n u) s) /
              √(x s + ε ^ 2)
but is expected to have type
  ∀ t ∈ Icc 0 T,
    IntervalIntegrable
        (fun s =>
          (extendPath T hT (signedApproximationRoot n u) s *
                extendPath T hT (signedApproximationForcing hq n u (sourcePath (D.comp (timeInclusion hTS)) u) p) s -
              2 * ν * extendPath T hT (signedApproximationDissipation n u) s) /
            √(x s + ε ^ 2))
        volume 0 t ∧
      √(x t + ε ^ 2) ≤
        √(x 0 + ε ^ 2) +
          ∫ (s : ℝ) in 0..t,
            (extendPath T hT (signedApproximationRoot n u) s *
                  extendPath T hT (signedApproximationForcing hq n u (sourcePath (D.comp (timeInclusion hTS)) u) p) s -
                2 * ν * extendPath T hT (signedApproximationDissipation n u) s) /
              √(x s + ε ^ 2)
```

### `scripts/gates.sh NSFormalization.Section4.A01.SignedPassage`

Exit 0; 28496 output lines; 1176904 bytes.

```text
== make check
python3 experiments/check_formalization_plan.py --check
{
  "task_count": 30,
  "source_counts": {
    "formalization": 520,
    "vendor/NavierStokesAndEuler": 2486,
    "vendor/HeliCorgi": 129
  },
  "source_manifest_entries": 2975,
[middle omitted]
info: Tests/EnergyAbsorptionV4.lean:100:0: Contract BlowupDensity.Tests.energyAbsorptionV4_terminalFinite: checked; standard logical axioms only
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

### `python3 experiments/check_contracts.py --base-ref origin/erenup/integration`

Exit 0; 28202 output lines; 1158635 bytes.

```text
{
  "registered_contracts": 29,
  "closures": {
    "R41.threshold_arithmetic": [
      "Bindings.Thresholds",
      "Contracts.V1.Thresholds",
      "NSFormalization.Paper3.Thresholds",
      "TestSupport.Axioms",
      "Tests.Thresholds"
    ],
[middle omitted]
      "NavierStokes.WeightedQuotients",
      "NavierStokes.WeightedRadialPrimitive",
      "NavierStokes.ZerothStressIdentity",
      "TestSupport.Axioms",
      "Tests.GradientL6V2"
    ]
  },
  "base_compatibility_checked": true,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
```

### Other read-only checks

`git diff --name-only origin/erenup/integration...HEAD` (exit 0):

```text
formalization/NSFormalization/Section4/A01/SignedPassage.lean
research/A01/A3_SPLIT.md
research/A01/ATTEMPTS_SIGNED_PASSAGE.md
research/A01/REPORT_204.md
research/A01/axioms_signed_passage.lean
```

`git diff --check`: exit 0, no output.

`rg -n '\b(sorry|admit|axiom|native_decide)\b|maxHeartbeats' formalization/NSFormalization/Section4/A01/SignedPassage.lean research/A01/axioms_signed_passage.lean`: exit 1, no matches.

Independent parsing/counting of the complete audit log and source:

```text
audit_count= 31 all_exact= True
new_declarations= 27
```

`git rev-parse HEAD:formalization/NSFormalization/Section4/A01/SignedLimit.lean origin/erenup/integration:formalization/NSFormalization/Section4/A01/SignedLimit.lean`:

```text
0137388d4209fa9cd8e3352d8a7ccae4e48e6e11
0137388d4209fa9cd8e3352d8a7ccae4e48e6e11
```

Whole-Section4 search (exit 0; 18 matching lines):

```text
formalization/NSFormalization/Section4/A01/RootComparison.lean:161:    (hFB : ForcingFamilyBound hq hν a F hF E A) :
formalization/NSFormalization/Section4/A01/RootComparison.lean:189:    (hFB : ForcingFamilyBound hq hν a F hF E A) :
formalization/NSFormalization/Section4/A01/MildEnergyPremises.lean:314:def ForcingFamilyBound {q : ℕ} (hq : 6 ≤ q) {ν S : ℝ} (hν : 0 < ν)
formalization/NSFormalization/Section4/A01/MildEnergyPremises.lean:370:    (hforcing : ForcingFamilyBound hq hν a F hF E A)
formalization/NSFormalization/Section4/A01/ForcingFamilyBound.lean:6:conditional on `CylinderCommutatorBound`, not asserted unconditionally. -/
formalization/NSFormalization/Section4/A01/ForcingFamilyBound.lean:53:def CylinderCommutatorBound (q : ℕ) (hq : 6 ≤ q) : Prop :=
formalization/NSFormalization/Section4/A01/ForcingFamilyBound.lean:185:/-- Exact `ForcingFamilyBound` target, conditional solely on the stated finite spatial estimate. -/
formalization/NSFormalization/Section4/A01/ForcingFamilyBound.lean:190:    (hcomm : CylinderCommutatorBound q hq) :
formalization/NSFormalization/Section4/A01/ForcingFamilyBound.lean:191:    ForcingFamilyBound hq hν a F hF (E q) (A q) := by
formalization/NSFormalization/Section4/A01/SignedLimit.lean:96:Transport/pressure cancellation and the weighted gradient-square passage still
formalization/NSFormalization/Section4/A01/SignedLimit.lean:127:    (hFB : ForcingFamilyBound hq hν a F hF E A)
formalization/NSFormalization/Section4/A01/SignedLimit.lean:172:    (hFB : ForcingFamilyBound hq hν a F hF E A)
formalization/NSFormalization/Section4/A01/SignedPassage.lean:368:theorem signed_weighted_square_limit {V : Type*} [NormedAddCommGroup V]
formalization/NSFormalization/Section4/A01/SignedPassage.lean:487:theorem maximal_weighted_dissipation_limit {q : ℕ} {T : ℝ} (hT : 0 ≤ T)
formalization/NSFormalization/Section4/A01/SignedPassage.lean:514:  obtain ⟨hi, hl⟩ := signed_weighted_square_limit hT ht hc hv
formalization/NSFormalization/Section4/A01/SignedPassage.lean:575:  obtain ⟨hgi, hgl⟩ := maximal_weighted_dissipation_limit hT u U hU hε t ht
formalization/NSFormalization/Section4/A01/SignedPassage.lean:624:    (hFB : ForcingFamilyBound hq hν a F hF E A) :
formalization/NSFormalization/Section4/A01/SignedPassage.lean:636:    (hFB : ForcingFamilyBound hq hν a F hF E A) :
```

Required fixes: none. Preserve integration's SignedLimit content in any later integration operation; rerun checks if the source/dependency base changes.
