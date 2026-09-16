REJECT

## 1. What the lane claims

Reviewed HEAD `b7a161a52a4214e55cedbfc36a6c932789d1aed5` against local remote-tracking integration `28d6c8383a7baa0aa573d8b15d5c3a7fea5efaae`; no fetch, checkout, rebase, commit, or source edits. Read CLAUDE.md, lane-review/SKILL.md, LESSONS.md first 40 lines, HANDOFF §0/P7, NEXT_SESSION, REPORT_198, REPORT_199, REPORT_201 and ATTEMPTS_ROOT_COMPARISON. REVIEW_199-A01-envelope.md is absent in this checkout, as reported (REPORT_201.md:138).

REPORT_201.md:3 accurately advertises partial analytic closure, not a forcing-bound-only proof. All eight Lean statement blocks were compared literally with source and all matched. In `formalization/NSFormalization/Section4/A01/RootComparison.lean` (R below): scalar differential comparison R:17; integral comparison R:53; closed-horizon uniqueness R:76; positive-root absorption R:94; regularization limit R:103; named residual R:126; root assembly R:150; finite-energy assembly R:177. This is seven theorems and one definition, not eight theorems.

Paper correspondence checked with `sed -n '120,150p' paper/sections/appendix-a-local-theory.tex`: eq:Rhigh at :132 retains viscosity, :138 explicitly invokes solenoidality for pressure cancellation, :140–144 performs regularized division and gives the root inequality. Appendix :60–76 discusses common-interval local theory; `paper/sections/04-whole-space.tex:53` consumes that local theory. These are supporting local-theory lemmas, not a proof of a whole-space density theorem. R:94 implements the Young constant correctly using A04/HighContinuation.lean:91 (`young_high_real`). No invented direct paper theorem citation occurs in the worker's new module.

## 2. What is in Lean

**Scalar comparison and endpoints.** R:22–49 is an explicit integrating-factor proof using Mathlib `antitoneOn_of_deriv_nonpos`, `convex_Icc`, and `intervalIntegral.integral_hasDerivAt_right`; it does not call a Grönwall theorem by that name. Interior derivatives suffice because the integrating factor is continuous on the closed interval. R:53–73 applies this to `z=c+∫(αr+b)` minus the ODE solution. It needs α≥0, but does not divide by r or require r>0. The application R:169 supplies α=k²/(4ν) and its nonnegativity. Both t=0 and t=T, including T=0, are in `Icc`. R:103–121 passes ε↓0 through the continuous square roots with `le_of_tendsto_of_tendsto`; its two nonnegativity assumptions justify sqrt(r²)=r and sqrt(c²)=c. This lemma is proved independently; it is not actually invoked by the cylinder assembly because the residual already gives the limiting integral inequality.

**Exact interfaces.** `MildEnergyPremises.lean:314` defines `ForcingFamilyBound hq hν a F hF E A` with NO ha argument. R:156 consumes this imported definition directly. R:159–160 uses one witness from `energy_maximal_limit` (Premises:137) in both hFB and hlimit. `MildEnergyEnvelope.lean:200` defines `CylinderRootComparison`; R:157 concludes that imported definition directly. Its driver, coefficient, forcing norm, initial norm and all quantifiers agree token-for-token after the explicit substitution: α(s)=(cylinderEnvelopeDriver hq hT A u s)²/(4ν), b=E*‖sobolevPath F hF (q+1)‖, c=E*‖ordinarySobolev (q+1) a.toLp a.translation_contDiff‖. The integrated inequality is an input to scalar comparison, not literally the definition's conclusion. R:174 removes the clamped extension only at subtype times. Both `CylinderRootComparison` and `cylinderEnvelopeDriver` definitions are byte-identical to integration. Premises.lean has no two-dot drift against integration.

R:184 consumes the same hFB; R:185 concludes imported `FiniteMildEnergy hq hν a ha F hF E A`, via Envelope:217. Only the finite-energy export currently takes ha. Initial normalization R:154/R:182 is explicit, load-bearing at R:167–168, and is the only additional constant constraint: there is no A≥0 assumption. It is satisfiable with `E := max 1 (mildNormConstant q)` by `le_max_right`; reviewer controls check this. This only establishes normalization, not hFB for arbitrary chosen constants. The root norm comparison is `MildGronwall.lean:38`, with finite constant defined at :22. No ENNReal `.toReal` or top-norm loophole is used.

**Non-vacuity and hygiene.** `research/A01/axioms_root_comparison.lean:27` constructs the zero mild path; :42 and :55 use `quadratic_mild_unique_window` to establish hFB and the residual for EVERY zero-data competitor and EVERY maximal limit on windows up to S=1. The finite-energy example :73 actually applies the new theorem with both inputs proved. This is genuine positive-horizon non-vacuity, not an empty interval. Examples :83–95 also cover zero horizon, y(t)=t with zero initial root, and zero-root regularization. Reviewer controls independently check t=T=1 and the normalization witness. No nonzero PDE satisfiability instance is claimed. Forbidden-token scan of the new module and audit file has no matches; there is no heartbeat override in either. The inherited Premises:270–271 override is commented, local, and 400000. No classical-solution energy theorem or all-order constructor is used by the new proof. All 13 audits have exactly [propext, Classical.choice, Quot.sound].

The requested three-dot diff lists two added Lean modules (the inherited 199 module and the new 201 module), plus records; no existing Lean module modification, and no verification/ change. The A3 split accurately says CONDITIONAL (research/A01/A3_SPLIT.md:71). Integration drift is nevertheless a blocker below. The changed-module CI helper `experiments/build_changed_lean.py:2` exists for new modules outside registered contract closures; this review explicitly built the new module.

## 3. Gaps and required fixes

1. **Blocking integration compatibility — duplicate theorem.** Integration's `MildEnergyEnvelope.lean:123` already declares `NSFormalization.Section4.A01.energyComparison_unique` (global uniqueness). R:76 declares the same name with a different closed-horizon statement. The two-dot diff shows exactly the missing upstream uniqueness block at Envelope:121–140. A scratch file importing this lane and copying integration's declaration reproduces `error: NSFormalization.Section4.A01.energyComparison_unique has already been declared` (exact diagnostic below). Fix: rebase taking integration's version of MildEnergyEnvelope.lean; rename the new local result to `energyComparison_unique_on_Icc` and update its audit/example/report references. Rebuild and rerun audits after this resolution. Reviewer has not rebased or edited the source.

2. **Blocking analytic-interface justification — solenoidality absent from the named input.** The input is quoted exactly below. It is a substantive absorbed integrated bound on the root, not a generic limit-continuity lemma: it includes the same PDE family, maximal limit, and tame bound, and assumes the principal remaining analytic conclusion. It does NOT simply assume the final explicit ODE envelope, so the scalar reduction is useful and noncircular. However, as currently quantified over arbitrary `a`, it cannot yet be certified as a restriction of the cited standard incompressible signed-energy fact. The known route needs velocity/transport solenoidality and pressure orthogonality. Premises:116–134 proves velocity solenoidality using ha; Premises:275–300 requires ha to invoke that proof. The vendor theorem `Euler/MildMajorantEnergy.lean:43–45` requires both hu and hz. Neither ha nor these conditions occur in R:126–146. A mild equation with Leray-projected source does not by itself remove the non-solenoidal component of the initial datum. The zero example does not test this issue. This is a missing justification, not a claimed formal counterexample to the predicate.

Fix: restrict the signed-limit obligation/assembly to divergence-free datum (carry ha explicitly while continuing to consume the unchanged hFB and conclude the unchanged CylinderRootComparison), or prove an alternative general-data signed estimate supplying the missing cancellation. Explain the intended nonzero-data supply in the report. Do not present a mere zero instance as certification of that stronger general-data premise.

Exact current named input (R:126–146):

```lean
def CylinderSignedRootLimit {q : ℕ} (hq : 6 ≤ q) {ν S : ℝ} (hν : 0 < ν)
    (a : SmoothL2Field Space) (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n) (E A : ℝ) : Prop :=
  ∀ (T : ℝ) (hT : 0 ≤ T) (hTS : T ≤ S)
    (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q+1))),
    (∀ t, u t = quadraticDuhamel 1 ν hν hT hTS
      (coefficients 1 hq (sobolevPath F hF q))
      (ordinarySobolev (q+1) a.toLp a.translation_contDiff) u t) →
    ∀ U : TimeLp T (SobolevSpace 1 (2+q)),
      Filter.Tendsto (fun n => pathLp T hT
        (maximalApproximation 1 q T n u)) Filter.atTop (𝓝 U) →
      (∀ᵐ r ∂timeMeasure T,
        extendPath T hT (energyRootPath u) r * cylinderEnergyForcing hq hT hTS F hF u U r ≤
          A * (16 * ‖restrictOperator 1 (Nat.succ_le_succ hq) (extendPath T hT u r)‖) *
            extendPath T hT (energyRootPath u) r * energyGradientNorm U r +
          (E * ‖sobolevPath F hF (q+1)‖) * extendPath T hT (energyRootPath u) r) →
      ∀ t ∈ Icc (0 : ℝ) T,
        extendPath T hT (energyRootPath u) t ≤ energyRootPath u ⟨0, le_rfl, hT⟩ +
          ∫ s in (0 : ℝ)..t,
            ((cylinderEnvelopeDriver hq hT A u s)^2/(4*ν) *
              extendPath T hT (energyRootPath u) s + E * ‖sobolevPath F hF (q+1)‖)
```

**Exact next-lane route and obstruction.** After resolving the solenoidality scope, reuse Premises:137 `energy_maximal_limit` and the representative construction at :289–300; begin with Envelope:72 `regularized_full_energy_hasDerivAt`, retaining the negative full gradient square. Supply the transport/pressure cancellations used in `Euler/MildMajorantEnergy.lean:95–119`. The vendor limit route is `EulerPDEMajorantLimit.weighted_pde_majorized_subinterval_limit` (`Euler/PDEMajorantLimit.lean:21`), ultimately `EulerTimeLpSubinterval.integral_energy_subinterval_limit` (`Euler/TimeLpSubinterval.lean:74`). Its current statement has NO dissipation slot, so it cannot directly prove this signed residual by replacing one theorem argument. Reuse `regularizedValueFamily_tendsto` (`Euler/RegularizedEnergyFamily.lean:44`), `weightedMetricPath_tendsto` (`Euler/MetricPathConvergence.lean:60`), and `regularizedWeightedForcing_tendsto` (`Euler/RegularizedEnergyFamily.lean:89`) while adding a signed passage retaining the gradient-square integral. Prove its convergence from the strong TimeLp maximal limit through the derivative word maps (or suitable lower semicontinuity if using weak convergence); handle the ε-regularized root denominator before ε↓0. The limiting tame estimate hFB is not a bound on every n-indexed regularized forcing family. Pass to the signed limiting energy estimate first, then absorb using R:94 with a properly justified regularized division, or supply uniform regularized bounds. This is appropriate for a dedicated signed-limit lane coordinated with lane 200; folding it into lane 200 is reasonable only if that lane supplies the stronger regularized family estimates. Lane 200's hFB alone does not close it automatically.

**Tree search before accepting gaps.** Ran `grep -rnE 'CylinderSignedRootLimit|signed.*(limit|integr)|dissipat|regularized_root|root.*comparison|energyComparison_unique|mild_energy_estimate_of_cylinder' formalization/NSFormalization/Section4` (109 matching lines), plus filename and declaration searches. Opened the closest candidates: A01/HeatGradientTrace.lean:13 retains dissipation but assumes an already differentiable low-order heat path, not this maximal-family limit; C01/EnergyBounds.lean:180 supplies scalar regularized division but not the mild signed PDE premise; A04/HighContinuation.lean:91 supplies Young algebra; A01/MildEnergyPremises.lean:275 drops dissipation; A01/MildEnergyEnvelope.lean:72 stops at the regularized identity. None directly supplies the required signed full-word limit. Thus the reported missing signed passage is accepted as an unfinished obligation, with the scope qualification above. The normalization gap is independently visible in ForcingFamilyBound:325–328 (E only multiplies the force); no claim of a nonzero PDE counterexample is needed.

## 4. Commands and results

All Lake commands ran sequentially from verification/, after `. scripts/lean-env.sh`, with `LEAN_NUM_THREADS=6`. Existing verification/.lake/packages was confirmed a symlink to the shared installed packages; no installer or git mutation was needed. Raw output below is restricted to at most the first and last 40 lines per command (usually fewer). Logs were captured before sampling, without piping Lean to head.

### `lake build NSFormalization.Section4.A01.RootComparison`

Exit 0; 219 output lines; 12820 bytes.

```text
⚠ [8927/9049] Replayed NSFormalization.Source.FiniteHilbertBochner
warning: NSFormalization/Source/FiniteHilbertBochner.lean:24:19: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
warning: NSFormalization/Source/FiniteHilbertBochner.lean:23:37: This simp argument is unused:
  PiLp.single_apply

Hint: Omit it from the simp argument list.
  [apply] simp [h]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: NSFormalization/Source/FiniteHilbertBochner.lean:39:23: This simp argument is unused:
[... middle omitted by reviewer ...]
Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _ha

Note: This linter can be disabled with `set_option linter.unusedVariables false`
⚠ [10241/10249] Replayed NSFormalization.Section4.A01.MildGronwall
warning: NSFormalization/Section4/A01/MildGronwall.lean:150:31: Variable name `ha` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _ha

Note: This linter can be disabled with `set_option linter.unusedVariables false`
Build completed successfully (10249 jobs).
```

### `lake env lean ../formalization/NSFormalization/Section4/A01/RootComparison.lean`

Exit 0; 0 output lines; 0 bytes.

No output.

### `lake env lean ../research/A01/axioms_root_comparison.lean`

Exit 0; 21 output lines; 1566 bytes.

```text
'NSFormalization.Section4.A01.scalar_differential_comparison' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.scalar_integral_comparison' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.energyComparison_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.regularized_root_comparison_limit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A01.positive_root_absorption' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.CylinderSignedRootLimit' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.cylinderRootComparison_of_forcingBound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A01.finiteMildEnergy_of_forcingBound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'_private._stdin.0.NSFormalization.Section4.A01.zero_value' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private._stdin.0.NSFormalization.Section4.A01.zero_sob' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private._stdin.0.NSFormalization.Section4.A01.zero_mild' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private._stdin.0.NSFormalization.Section4.A01.zero_forcing' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private._stdin.0.NSFormalization.Section4.A01.zero_signed_limit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### `make check (worktree root)`

Exit 0; 28234 output lines; 1159606 bytes.

```text
python3 experiments/check_formalization_plan.py --check
{
  "task_count": 30,
  "source_counts": {
    "formalization": 517,
    "vendor/NavierStokesAndEuler": 2486,
    "vendor/HeliCorgi": 129
  },
  "source_manifest_entries": 2975,
  "missing_copied_imports": [],
  "citation_interfaces_reachable": [],
  "tokens_in_copied_umbrella_closure": [
[... middle omitted by reviewer ...]
  },
  "base_compatibility_checked": false,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.043s

OK
python3 experiments/check_work_queue.py
30 work items: ownership, contract registration and task cards consistent.
```

### `bash scripts/gates.sh NSFormalization.Section4.A01.RootComparison (root)`

Exit 0; 28496 output lines; 1176905 bytes.

```text
== make check
python3 experiments/check_formalization_plan.py --check
{
  "task_count": 30,
  "source_counts": {
    "formalization": 517,
    "vendor/NavierStokesAndEuler": 2486,
    "vendor/HeliCorgi": 129
  },
  "source_manifest_entries": 2975,
  "missing_copied_imports": [],
  "citation_interfaces_reachable": [],
[... middle omitted by reviewer ...]
info: Tests/EnergyAbsorptionV4.lean:18:0: Contract BlowupDensity.Tests.checkedEnergyAbsorptionV4: checked; standard logical axioms only
info: Tests/EnergyAbsorptionV4.lean:19:0: Contract BlowupDensity.Bindings.energyAbsorptionPartialV3_of_v4: checked; standard logical axioms only
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
    "I01.packet": [
      "Bindings.Packet",
[... middle omitted by reviewer ...]
      "NavierStokes.WeightedClasses",
      "NavierStokes.WeightedODEJets",
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

### `lake test (verification/)`

Exit 0; 343 output lines; 21729 bytes.

```text
⚠ [8778/9160] Replayed NSFormalization.Source.FiniteHilbertBochner
warning: NSFormalization/Source/FiniteHilbertBochner.lean:24:19: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
warning: NSFormalization/Source/FiniteHilbertBochner.lean:23:37: This simp argument is unused:
  PiLp.single_apply

Hint: Omit it from the simp argument list.
  [apply] simp [h]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: NSFormalization/Source/FiniteHilbertBochner.lean:39:23: This simp argument is unused:
[... middle omitted by reviewer ...]
ℹ [10565/10573] Replayed Tests.HomogeneousPartialV2
info: Tests/HomogeneousPartialV2.lean:35:0: Contract BlowupDensity.Tests.checkedHomogeneousPartialV2: checked; standard logical axioms only
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

### `lake env lean ../research/A01/probes/rev201_mutation.lean`

Exit 1; 8 output lines; 282 bytes.

```text
../research/A01/probes/rev201_mutation.lean:8:38: error: Application type mismatch: The argument
  hm
has type
  r * d ≤ r * (k ^ 2 / (4 * ν) * r + b)
but is expected to have type
  r * d ≤ r * (k ^ 2 / (8 * ν) * r + b)
in the application
  (mul_le_mul_iff_right₀ hr).mp hm
```

### `lake env lean ../research/A01/probes/rev201_integration_collision.lean`

Exit 1; 1 output lines; 150 bytes.

```text
../research/A01/probes/rev201_integration_collision.lean:4:8: error: `NSFormalization.Section4.A01.energyComparison_unique` has already been declared
```

### `lake env lean ../research/A01/probes/rev201_controls.lean`

Exit 0; 0 output lines; 0 bytes.

No output.

The build is silent for the new module, but not globally silent: it replays inherited dependency warnings. Direct module checking is exactly zero output. The gates script also runs registered tests and make test-mutations; it reports refactor acceptance and rejection of the three invalid mutations. Because its make-test stage masks failures, `lake test` was rerun separately and returned 0. verification/ was untouched; the additional gates and base compatibility check were nevertheless run.

The substantive reviewer mutation changes only the final absorption denominator 4ν→8ν while retaining all arguments and the proof (probes/rev201_mutation.lean:3). The resulting mismatch is mathematical: ν=r=g=d=1, k=2, b=0 satisfies the premise but violates the stronger conclusion. `rev201_controls.lean:3` proves this numerical counterexample. The initial control draft needed explicit α/b/c instantiation for Lean inference; after that probe-only correction it passes silently. The integration probe copies the upstream theorem into the lane's imported namespace; its duplicate-name diagnostic reproduces the integration blocker without editing either module.

Additional exact checks: forbidden-token/maxHeartbeats scan of R and axioms_root_comparison has no output; `git diff --check` has no output, exit 0. The literal statement checker reports True for all eight REPORT_201 Lean blocks; the axiom parser reports `audits 13 all standard True`; both shared definitions report `byte-identical: True`.

`git diff --name-only origin/erenup/integration...HEAD` output:

```text
formalization/NSFormalization/Section4/A01/MildEnergyEnvelope.lean
formalization/NSFormalization/Section4/A01/RootComparison.lean
research/A01/A3_SPLIT.md
research/A01/ATTEMPTS_ENVELOPE.md
research/A01/ATTEMPTS_ROOT_COMPARISON.md
research/A01/REPORT_199.md
research/A01/REPORT_201.md
research/A01/axioms_envelope.lean
research/A01/axioms_root_comparison.lean
```

Required fixes: (1) rebase retaining integration's envelope module and rename the closed-horizon uniqueness theorem and references; (2) scope the signed-limit obligation to solenoidal data or prove the missing general-data cancellation, and document the signed-limit supply route; (3) rerun build, direct Lean, all 13 audits and gates after those changes. No unconditional analytic closure is requested by this review beyond the brief's permitted single honest residual.
