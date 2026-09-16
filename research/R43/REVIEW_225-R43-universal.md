ACCEPT

## 1. What the lane claims

Reviewed HEAD `8c0b4c983ee2834ea5798a08def4e325dfebda1b`. Applied `.claude/skills/lane-review/SKILL.md`; read CLAUDE.md, the lessons, brief, lane 223 report/review, and cited sources. No tracked file or git state was changed; only this report and the permitted mutation probe were added.

`research/R43/REPORT_225.md:5` claims the exact RCritical1API universal field with the existing explicit constant, nine implementation theorems (:27), the general initial-data budget (:31), and thirteen axiom audits plus zero instances (:35). It explicitly excludes registration and a bundled API instance (:46).

## 2. What is in Lean

Paths abbreviated below: Universal = `formalization/NSFormalization/Section4/R43/Universal.lean`; Endpoint, ForcePath, CriticalMomentum and MaximalEndpoint are in that same directory.

1. **Statement fidelity.** Universal:193–203 is token-for-token `research/R43/Spec.lean:211–218` after substituting `criticalConst` for `c`; an automated whitespace-token comparison returned True. Positive viscosity, arbitrary admissible datum, MemForceR, strict homogeneous ENNReal sum-smallness, and infinite maximal lifespan are all preserved. Opened `paper/sections/04-whole-space.tex:80–132` with sed: :83–88 states precisely this theorem, :100–104 its bootstrap, and :125–132 its initial-data budget and continuation. The conclusion is infinite lifespan, not merely a finite-horizon bound.

2. **All nine claimed theorems exist.** Scalar bootstrap Universal:12; classical bootstrap :44; initial-plus-prefix estimate :103; slice bound :124; slice absorption :135; maximal absorption :152; explicit H² budget :164; A04 finiteness :180; universal :193. The scalar proof uses `formalization/NSFormalization/Section4/C01/EnergyBounds.lean:180` (general initial square-root inequality) and `formalization/NSFormalization/Paper1/ScalarEnergy.lean:109` (continuous bootstrap). These statements were opened, not inferred from names. The older split's ScalarEnergy:85 locator is stale; the worker does not repeat that locator.

3. **Constants and non-vacuity.** Endpoint:17 defines the stated minimum, :22 proves strict positivity, :28 bootstrap room, and :34 absorption. These constants are independent of ν, a, f. Universal:110 proves the initial norm finite before :118 uses ofReal_toReal. Universal:48 requires 0 ≤ S < T, so the closed bootstrap interval is nonempty; :169 requires positive S for the open integral. The unused `_hc0` at :49 is harmless and explicitly marked: nonnegativity of the initial norm and forcing primitive together with hsmall and positive ν already implies it. No fallback analytic assumption is present. The final theorem contains no toReal.

4. **Analytic wiring and endpoint.** CriticalMomentum:334 supplies eq:Rcritical1 for arbitrary classical data without a named momentum input; ForcePath:292 is the zero-datum predecessor. Universal:164–177 retains exactly `32*S*energyBudget a f S^2 + 32*ν⁻¹*gradientSq a + 32*(ν⁻¹)^2*∫₀ˢ l2Sq(f(t))`. This matches the registered general budget at `verification/Contracts/V4/EnergyAbsorption.lean:83` and its binding at `verification/Bindings/EnergyAbsorptionV4.lean:31`. MaximalEndpoint:15 uses a common terminal-S budget on shorter horizons, and :37 converts it to A04 finiteness; equality S=T_max is included without evaluating u(S). Universal:201 uses `formalization/NSFormalization/Section4/A02/MaximalWiring.lean:14`; :202 uses `formalization/NSFormalization/Section4/A04/ShiftedExtension.lean:256`, whose input includes all positive S ≤ T_max. Both supplier statements were opened.

5. **Conformance.** `research/R43/axioms_universal.lean:54` copies the datum infimum of Spec:142 (only the SpatialField qualification differs); :57 proves its definitional equality; :59–71 checks the final theorem in Contracts.V1.Data vocabulary using the existing lifespan bridge. All thirteen audits passed with exactly the standard three axioms. The example at :37 proves actual zero-force smallness, and :21/:32 recover lane 223 for arbitrary small inhomogeneous force. Thus the requested non-vacuity examples already exist and pass.

6. **Hygiene and CI.** The triple-dot diff lists exactly five additions, no existing-module modification and no verification change. The forbidden-token/heartbeat scan of Universal and its audit is empty. There are no heartbeat overrides in the new module. `experiments/build_changed_lean.py --base-ref origin/erenup/integration --dry-run` reports Universal, so the changed-module build mechanism covers it.

## 3. Gaps

No blocking finding and no required fix. The worker declares no missing mathematical lemma (`research/R43/REPORT_225.md:43`), so there is no missing-tree assertion to accept. A whole-tree search was nevertheless run:

```sh
grep -rnE 'RCritical1API|universal_of_memForceR|inhomogeneousAtZero_of_memForceR' formalization/NSFormalization/Section4
```

It finds Endpoint:134, Universal:193, the R41 consumer at R41/NonDensityL1.lean:88, and the Pieces doc reference; no bundled structure instance is claimed. Contract registration remains explicitly outside scope.

**Substantive negative check:** `research/R43/probes/rev225_widened.lean:6` copies the final proof, retaining every argument, but changes the smallness radius to `2 * criticalConst * ν`. Lean rejects the call at :16 with the expected bound mismatch (exact output below). This checks sensitivity of this proof, not impossibility of every theorem with a larger constant.

The direct module check is silent; aggregate Lake build output is not, because existing dependency diagnostics are replayed. This matches the worker's explicit caveat at REPORT_225:54–57 and introduces no Universal warning. `make check` also reports pre-existing copied-source diagnostics; the new theorem's transitive axiom audit is clean.

## 4. Commands and results

Every Lean command sourced `scripts/lean-env.sh`, ran from `verification/`, and used `LEAN_NUM_THREADS=6`. Existing package symlinks were verified; no installer or git mutation was needed. The conditional `scripts/gates.sh` and base-ref contract gate are not required because `git diff --name-only origin/erenup/integration...HEAD -- verification` has zero output. The worker's additional lake test/mutation claims are not needed for this lane's listed gates and were not independently rerun.

### Module build — exit 0

```sh
. scripts/lean-env.sh
cd verification
LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.R43.Universal
```

Exact output:

```text
⚠ [8777/8859] Replayed NSFormalization.Source.FiniteHilbertBochner
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
⚠ [9866/10545] Replayed NSFormalization.Source.BoundedReferenceFlux
warning: NSFormalization/Source/BoundedReferenceFlux.lean:17:5: Variable name `hU0` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hU0

Note: This linter can be disabled with `set_option linter.unusedVariables false`
⚠ [9867/10545] Replayed NSFormalization.Source.BoundedReferenceComparison
warning: NSFormalization/Source/BoundedReferenceComparison.lean:159:34: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Source/BoundedReferenceComparison.lean:159:76: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
⚠ [10264/10545] Replayed NSFormalization.Source.RieszPotentialNearField
warning: NSFormalization/Source/RieszPotentialNearField.lean:21:17: Variable name `hR` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hR

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: NSFormalization/Source/RieszPotentialNearField.lean:21:30: Variable name `hB` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hB

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: NSFormalization/Source/RieszPotentialNearField.lean:49:4: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
⚠ [10294/10545] Replayed NSFormalization.Source.RealSobolev
warning: NSFormalization/Source/RealSobolev.lean:90:30: This simp argument is unused:
  Complex.smul_re

Hint: Omit it from the simp argument list.
  [apply] simp [Complex.smul_im]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: NSFormalization/Source/RealSobolev.lean:90:47: This simp argument is unused:
  Complex.smul_im

Hint: Omit it from the simp argument list.
  [apply] simp [Complex.smul_re]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: NSFormalization/Source/RealSobolev.lean:90:64: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
⚠ [10298/10545] Replayed NSFormalization.Paper3.SpatiallyCompactTime
warning: NSFormalization/Paper3/SpatiallyCompactTime.lean:88:19: `ContinuousLinearMap.sub_apply` has been deprecated: Use `sub_apply` instead

Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.sub_apply` to `sub_apply x`).
⚠ [10305/10545] Replayed NSFormalization.Paper3.RealPositiveDensity
warning: NSFormalization/Paper3/RealPositiveDensity.lean:67:59: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Paper3/RealPositiveDensity.lean:76:63: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Paper3/RealPositiveDensity.lean:88:59: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Paper3/RealPositiveDensity.lean:100:59: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
⚠ [10308/10545] Replayed NSFormalization.Paper3.RealVectorPositiveDensity
warning: NSFormalization/Paper3/RealVectorPositiveDensity.lean:29:5: Variable name `hc` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hc

Note: This linter can be disabled with `set_option linter.unusedVariables false`
ℹ [10311/10545] Replayed NSFormalization.Source.PhysicalBesselSobolev
info: NSFormalization/Source/PhysicalBesselSobolev.lean:134:4: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
⚠ [10316/10545] Replayed NSFormalization.Source.PacketForceExtension
warning: NSFormalization/Source/PacketForceExtension.lean:44:25: `if_pos` has been deprecated: Use `ite_eq_left` instead
⚠ [10319/10545] Replayed NSFormalization.Source.ViscosityPacket
warning: NSFormalization/Source/ViscosityPacket.lean:34:63: This simp argument is unused:
  Function.comp_def

Hint: Omit it from the simp argument list.
  [apply] simp [viscosityVelocity, dilateField, viscosityHomeomorph, Prod.map]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
⚠ [10337/10545] Replayed NSFormalization.Paper3.SobolevDirectionalDerivative
warning: NSFormalization/Paper3/SobolevDirectionalDerivative.lean:103:16: `SchwartzMap.smul_apply` has been deprecated: Use `smul_apply` instead

Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.smul_apply` to `smul_apply x`).
⚠ [10344/10545] Replayed NSFormalization.Source.BoundedViscosityUniqueness
warning: NSFormalization/Source/BoundedViscosityUniqueness.lean:21:28: This simp argument is unused:
  one_smul

Hint: Omit it from the simp argument list.
  [apply] simp only [smul_smul, h₂, smul_add, smul_sub]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
⚠ [10348/10545] Replayed Formal.R3LerayFrequencySymbol
warning: ../vendor/HeliCorgi/Formal/R3LerayFrequencySymbol.lean:43:2: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
⚠ [10351/10545] Replayed Formal.R3StokesL2Operator
warning: ../vendor/HeliCorgi/Formal/R3StokesL2Operator.lean:111:2: Try this: 
  letI̵

The goal is a proposition, so `let` is preferred over `letI`.
The difference between `let` and `letI` is that `letI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
⚠ [10352/10545] Replayed Formal.R3L2ScalarAux
warning: ../vendor/HeliCorgi/Formal/R3L2ScalarAux.lean:26:2: Try this: 
  letI̵

The goal is a proposition, so `let` is preferred over `letI`.
The difference between `let` and `letI` is that `letI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
⚠ [10360/10545] Replayed Formal.FlowMapNonextendibilityCriterion
warning: ../vendor/HeliCorgi/Formal/FlowMapNonextendibilityCriterion.lean:40:16: Variable name `ht0` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _ht0

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: ../vendor/HeliCorgi/Formal/FlowMapNonextendibilityCriterion.lean:40:30: Variable name `htT` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _htT

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: ../vendor/HeliCorgi/Formal/FlowMapNonextendibilityCriterion.lean:43:16: Variable name `ht0` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _ht0

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: ../vendor/HeliCorgi/Formal/FlowMapNonextendibilityCriterion.lean:43:30: Variable name `htT` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _htT

Note: This linter can be disabled with `set_option linter.unusedVariables false`
⚠ [10361/10545] Replayed Formal.UniformRestartContinuation
warning: ../vendor/HeliCorgi/Formal/UniformRestartContinuation.lean:36:16: Variable name `ht0` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _ht0

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: ../vendor/HeliCorgi/Formal/UniformRestartContinuation.lean:36:30: Variable name `htT` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _htT

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: ../vendor/HeliCorgi/Formal/UniformRestartContinuation.lean:39:16: Variable name `ht0` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _ht0

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: ../vendor/HeliCorgi/Formal/UniformRestartContinuation.lean:39:30: Variable name `htT` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _htT

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: ../vendor/HeliCorgi/Formal/UniformRestartContinuation.lean:95:0: Definition `FlowMapUniformRestartPackage.toContinuationPackage` is a proposition; use `theorem` instead of `def`

Note: This linter can be disabled with `set_option linter.defProp false`
⚠ [10362/10545] Replayed Formal.R3SobolevCarrier
warning: ../vendor/HeliCorgi/Formal/R3SobolevCarrier.lean:80:2: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
⚠ [10365/10545] Replayed Formal.R3CoordinateLinearAux
warning: ../vendor/HeliCorgi/Formal/R3CoordinateLinearAux.lean:10:11: Variable name `x` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _x

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: ../vendor/HeliCorgi/Formal/R3CoordinateLinearAux.lean:10:13: Variable name `y` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _y

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: ../vendor/HeliCorgi/Formal/R3CoordinateLinearAux.lean:11:12: Variable name `c` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _c

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: ../vendor/HeliCorgi/Formal/R3CoordinateLinearAux.lean:11:14: Variable name `x` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _x

Note: This linter can be disabled with `set_option linter.unusedVariables false`
⚠ [10368/10545] Replayed Formal.R3DivergencePointwise
warning: ../vendor/HeliCorgi/Formal/R3DivergencePointwise.lean:25:19: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
⚠ [10372/10545] Replayed Formal.R3LerayL2Operator
warning: ../vendor/HeliCorgi/Formal/R3LerayL2Operator.lean:34:2: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
warning: ../vendor/HeliCorgi/Formal/R3LerayL2Operator.lean:61:2: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
⚠ [10373/10545] Replayed Formal.R3LerayFourierBridge
warning: ../vendor/HeliCorgi/Formal/R3LerayFourierBridge.lean:73:2: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
⚠ [10374/10545] Replayed Formal.R3LerayComplexFiberSymbol
warning: ../vendor/HeliCorgi/Formal/R3LerayComplexFiberSymbol.lean:42:2: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
⚠ [10430/10545] Replayed NSFormalization.Section4.A01.AprioriFamily
warning: NSFormalization/Section4/A01/AprioriFamily.lean:148:31: Variable name `ha` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _ha

Note: This linter can be disabled with `set_option linter.unusedVariables false`
⚠ [10431/10545] Replayed NSFormalization.Section4.A01.MildGronwall
warning: NSFormalization/Section4/A01/MildGronwall.lean:150:31: Variable name `ha` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _ha

Note: This linter can be disabled with `set_option linter.unusedVariables false`
ℹ [10506/10545] Replayed NSFormalization.Source.RieszFourierScale
info: NSFormalization/Source/RieszFourierScale.lean:70:57: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
⚠ [10512/10545] Replayed NSFormalization.Source.RieszL2Fourier
warning: NSFormalization/Source/RieszL2Fourier.lean:31:2: Try this: 
  letI̵

The goal is a proposition, so `let` is preferred over `letI`.
The difference between `let` and `letI` is that `letI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
⚠ [10513/10545] Replayed NSFormalization.Source.FractionalRealization
warning: NSFormalization/Source/FractionalRealization.lean:60:2: Try this: 
  letI̵

The goal is a proposition, so `let` is preferred over `letI`.
The difference between `let` and `letI` is that `letI` inlines the value.
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
✔ [10545/10545] Built NSFormalization.Section4.R43.Universal (2.8s)
Build completed successfully (10545 jobs).
```

### Direct module check — exit 0, zero output

```sh
. scripts/lean-env.sh
cd verification
LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section4/R43/Universal.lean
```

### Axiom and non-vacuity audit — exit 0

```sh
. scripts/lean-env.sh
cd verification
LEAN_NUM_THREADS=6 lake env lean ../research/R43/axioms_universal.lean
```

Exact output (line wrapping preserved):

```text
'NSFormalization.Section4.R43.critical_norm_bound_general' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R43.critical_bootstrap_general' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R43.critical_initial_add_prefix_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R43.criticalNormAt_le_general' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R43.critical_absorption_general' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R43.maximal_critical_absorption_general' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.R43.maximal_h2TimeIntegral_general' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R43.maximal_squaredHTwoIntegral_general' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.R43.universal_of_memForceR' depends on axioms: [propext, Classical.choice, Quot.sound]
'universal_recovers_endpoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'UniversalConformance.dotHomogeneousENorm' depends on axioms: [propext, Classical.choice, Quot.sound]
'UniversalConformance.dotHomogeneousENorm_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'UniversalConformance.universal' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### make check — exit 0

Captured stdout followed by stderr; exact first/last 40 lines below, with the repetitive middle omitted (28234 total lines).

```text
exit: 0 lines: 28234
python3 experiments/check_formalization_plan.py --check
{
  "task_count": 30,
  "source_counts": {
    "formalization": 541,
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
  "source_hashes_match": false
}
Explicit axiom/admission tokens, all copied sources: 11
python3 experiments/check_contracts.py
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
      "Contracts.V1.Packet",
      "NSFormalization.Paper1.ScalarEnergy",
      "NSFormalization.Section4.I01.Energy",
      "NSFormalization.Section4.I01.Extension",
[... middle omitted ...]
      "NavierStokes.TransitionRamp",
      "NavierStokes.TransportPrimitive",
      "NavierStokes.TrueConeLoop",
      "NavierStokes.UniformAngularReset",
      "NavierStokes.UniformBlockBounds",
      "NavierStokes.UniformCone",
      "NavierStokes.UniformFourierAlias",
      "NavierStokes.UniformHarmonicInteraction",
      "NavierStokes.UniformPrimaryWeights",
      "NavierStokes.ValidBandGluing",
      "NavierStokes.ValidDyadicBandCover",
      "NavierStokes.VariableGaugeMean",
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
      "Tests.GradientL6V2"
    ]
  },
  "base_compatibility_checked": false,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
python3 experiments/test_contract_policy.py
python3 experiments/check_work_queue.py
30 work items: ownership, contract registration and task cards consistent.
.............
----------------------------------------------------------------------
Ran 13 tests in 0.051s

OK
```

### Mutation — expected exit 1

```sh
. scripts/lean-env.sh
cd verification
LEAN_NUM_THREADS=6 lake env lean ../research/R43/probes/rev225_widened.lean
```

Exact output:

```text
../research/R43/probes/rev225_widened.lean:16:69: error: Application type mismatch: The argument
  hsmall
has type
  dotHomogeneousENorm (1 / 2) a + forceHomogeneousENorm 1 (1 / 2) f < ENNReal.ofReal (2 * criticalConst * ν)
but is expected to have type
  dotHomogeneousENorm (1 / 2) a + forceHomogeneousENorm 1 (1 / 2) f < ENNReal.ofReal (criticalConst * ν)
in the application
  maximal_squaredHTwoIntegral_general hν ha hf hu hsmall
```

### Hygiene and statement comparison

`git diff --name-status origin/erenup/integration...HEAD` — exit 0:

```text
A	formalization/NSFormalization/Section4/R43/Universal.lean
A	research/R43/ATTEMPTS_UNIVERSAL.md
A	research/R43/COMPARISON_UNIVERSAL.md
A	research/R43/REPORT_225.md
A	research/R43/axioms_universal.lean
```

`git diff --check`: exit 0, zero output.
`git diff --name-only origin/erenup/integration...HEAD -- verification`: exit 0, zero output.

`rg -n '\b(sorry|admit|axiom|native_decide)\b|maxHeartbeats' formalization/NSFormalization/Section4/R43/Universal.lean research/R43/axioms_universal.lean`: exit 1, zero matches.

Whitespace-token comparison of Spec's universal field and Universal's final statement, substituting only `c * ν` with `criticalConst * ν`:

```text
Spec token comparison: True
```

Changed-module CI dry run, exit 0:

```text
Changed Lean modules: NSFormalization.Section4.R43.Universal
```

Required fixes: none.

