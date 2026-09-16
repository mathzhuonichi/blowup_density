ACCEPT

## 1. What the lane claims

Reviewed HEAD `049601c302db3d76f30bd328e6227f54c1716af6`, read-only except this report and the permitted negative probe. Applied `.claude/skills/lane-review/SKILL.md`; read the repository instructions, lessons, brief, reports 219/221/223, and cited mathematical sources.

`research/R43/REPORT_223.md:5` claims the exact zero-datum consequence of Proposition 4.3, with a fixed positive explicit radius, first under homogeneous and then inhomogeneous force smallness. It claims 12 endpoint declarations and no remaining analytic input (`:27`, `:53`), not the optional general-datum API.

## 2. What is in Lean

All paths below are relative to this worktree. In this section, `Endpoint.lean` means `formalization/NSFormalization/Section4/R43/Endpoint.lean`.

- **Statement fidelity:** `Endpoint.lean:134` has exactly the quantifiers, positive viscosity, `MemForceR`, strict `forceSobolevENormL1 (1 / 2)` smallness, zero datum, and infinite lifespan of `research/R43/Spec.lean:243`, substituting `criticalConst` for the spec's `c`. The literal Data-vocabulary conformance theorem at `research/R43/axioms_endpoint.lean:39` also compiles. The manuscript was opened with `sed -n '86,132p'` (and `75,90p`): `paper/sections/04-whole-space.tex:88` states precisely this consequence; `:100`, `:114`, `:125`, `:132` give bootstrap, absorption, H² assembly, and norm comparison.
- **Constants:** `Endpoint.lean:17` defines the reported minimum; `:22`, `:28`, `:34` prove positivity, bootstrap room, and the absorption gate. The constant is chosen independently of viscosity and force. C01's C₁ is `gradientL6.Csix` at `verification/Bindings/EnergyAbsorptionPartial.lean:94`, and that equals `A05.gradientL6Const` at `verification/Bindings/GradientL6.lean:43`. The embedding is `formalization/NSFormalization/Section4/A05/CriticalL3.lean:394`.
- **All reported intermediate statements exist:** force-prefix control `Endpoint.lean:47`; classical-slice bound `:55`; L³ absorption `:66`; maximal-family absorption `:83`; the exact explicit budget with both coefficients 32 `:95`; A04 integral finiteness `:110`; homogeneous endpoint `:123`; final inhomogeneous endpoint `:134`. Together with the definition and three constant lemmas these are exactly 12 declarations.
- **Bootstrap and norm comparison:** `formalization/NSFormalization/Section4/R43/ForcePath.lean:292` requires `0 ≤ S < T` and bounds every time in `Icc 0 S`. The endpoint invokes it with S=t at `Endpoint.lean:61`, where `t ∈ Ico 0 T`. Its G2 comparison at `ForcePath.lean:67` compares the actual measurable-path infima. The unused membership binder in that comparison is harmless: the inequality holds more generally.
- **Finite maximal endpoint:** `formalization/NSFormalization/Section4/R43/MaximalEndpoint.lean:15` uses one terminal-S budget for every shorter interval and obtains a horizon strictly between the shorter time and S. `formalization/NSFormalization/Section4/C01/H2TimeIntegral.lean:36` supplies that uniform budget; `:110` proves the countable directed-union estimate; `:18` proves force-square integrability. The C01 V4 registered field is `verification/Contracts/V4/EnergyAbsorption.lean:83`, implemented by `verification/Bindings/EnergyAbsorptionV4.lean:31`. There is no undefined terminal velocity evaluation.
- **Continuation and non-vacuity:** `formalization/NSFormalization/Section4/A04/ShiftedExtension.lean:256` accepts finiteness for every positive S with `ofReal S ≤ maximalLifespanR`, including equality. Its shifted-extension obligation is discharged at `:229`; the higher-order bound is proved at `A04/RestartFixedForce.lean:236`. `A02/MaximalWiring.lean:14` supplies unconditional maximal existence. `A02/Maximal.lean:85` includes positive lifespan; `A04/Continuation.lean:22` defines the genuine open-interval H² integral. The final endpoint has no `.toReal`, no unused binders, and no fallback hypothesis. The existing zero-force example at `research/R43/axioms_endpoint.lean:24` constructs a zero datum path, proves strict smallness using positivity, and invokes the final theorem; it passed.
- **Hygiene:** the triple-dot diff contains only added Lean modules, no modified existing module; only the two requested status Markdown files are modified. No `verification/` file is touched. The added implementation modules have no forbidden proof tokens. The sole heartbeat override in their ancestry is the commented declaration-local 400000 at `R43/CriticalMomentum.lean:277`; Endpoint has none. Both A04 dependency files are byte-identical to the cited lane 217 commit. `experiments/build_changed_lean.py:19` includes changed formalization modules, and its dry run lists Endpoint; CI invokes it at `.github/workflows/contracts.yml:81`.

## 3. Gaps

No blocking finding or required fix. The general-a bootstrap and complete API witness remain outside the lane, as explicitly stated at `research/R43/REPORT_223.md:54` and `research/R43/COMPARISON.md:139`.

Before accepting that scope statement, ran `grep -rnE 'sqrt_energy_le_primitive|critical.*[Bb]ootstrap|inhomogeneousAtZero|RCritical1API|homogeneousAtZero' formalization/NSFormalization/Section4`. It finds the zero-datum bootstrap and endpoint, and also `C01/EnergyBounds.lean:180` (the existing general scalar square-root estimate), whose statement was opened. Thus the scalar generalization is already available; the report correctly says the general-a endpoint was not proved **by this lane**, rather than claiming the scalar lemma is absent. No zero-datum missing-tree claim remains.

Negative check: `research/R43/probes/rev223_widened.lean:8` copies the final proof and changes only the smallness radius from cν to 2cν. Lean fails at line 14 with the expected inequality type mismatch (exact output below). This is a substantive weakening of the hypothesis, not an argument deletion; it establishes sensitivity of this proof, not falsity of every possible larger-radius theorem.

The whole build is not silent because Lake replays dependency warnings; the module's direct check has exactly zero output. This limitation was already reported honestly at `REPORT_223.md:65`. Architecture checks also report pre-existing copied-source admission notices and `source_hashes_match: false`; the endpoint's transitive axiom audit nevertheless contains exactly the standard three axioms.

## 4. Commands and results

Every Lean command sourced `. scripts/lean-env.sh`, ran from `verification/`, and used `LEAN_NUM_THREADS=6`. No installation was needed: the dependency symlink and initialized toolchain were present. No git state-changing command was run. Long repository JSON output is excerpted rather than reproduced in tens of thousands of lines, following `logs/LESSONS.md:4`; the displayed output text is exact.

### Module build (exit 0)

`lake build NSFormalization.Section4.R43.Endpoint`. Exact output:

```text
⚠ [8777/9390] Replayed NSFormalization.Source.FiniteHilbertBochner
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
⚠ [9865/10136] Replayed NSFormalization.Source.BoundedReferenceFlux
warning: NSFormalization/Source/BoundedReferenceFlux.lean:17:5: Variable name `hU0` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hU0

Note: This linter can be disabled with `set_option linter.unusedVariables false`
⚠ [9866/10136] Replayed NSFormalization.Source.BoundedReferenceComparison
warning: NSFormalization/Source/BoundedReferenceComparison.lean:159:34: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Source/BoundedReferenceComparison.lean:159:76: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
⚠ [10264/10544] Replayed NSFormalization.Source.RieszPotentialNearField
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
⚠ [10294/10544] Replayed NSFormalization.Source.RealSobolev
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
⚠ [10298/10544] Replayed NSFormalization.Paper3.SpatiallyCompactTime
warning: NSFormalization/Paper3/SpatiallyCompactTime.lean:88:19: `ContinuousLinearMap.sub_apply` has been deprecated: Use `sub_apply` instead

Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.sub_apply` to `sub_apply x`).
⚠ [10305/10544] Replayed NSFormalization.Paper3.RealPositiveDensity
warning: NSFormalization/Paper3/RealPositiveDensity.lean:67:59: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Paper3/RealPositiveDensity.lean:76:63: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Paper3/RealPositiveDensity.lean:88:59: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Paper3/RealPositiveDensity.lean:100:59: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
⚠ [10308/10544] Replayed NSFormalization.Paper3.RealVectorPositiveDensity
warning: NSFormalization/Paper3/RealVectorPositiveDensity.lean:29:5: Variable name `hc` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hc

Note: This linter can be disabled with `set_option linter.unusedVariables false`
ℹ [10311/10544] Replayed NSFormalization.Source.PhysicalBesselSobolev
info: NSFormalization/Source/PhysicalBesselSobolev.lean:134:4: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
⚠ [10316/10544] Replayed NSFormalization.Source.PacketForceExtension
warning: NSFormalization/Source/PacketForceExtension.lean:44:25: `if_pos` has been deprecated: Use `ite_eq_left` instead
⚠ [10319/10544] Replayed NSFormalization.Source.ViscosityPacket
warning: NSFormalization/Source/ViscosityPacket.lean:34:63: This simp argument is unused:
  Function.comp_def

Hint: Omit it from the simp argument list.
  [apply] simp [viscosityVelocity, dilateField, viscosityHomeomorph, Prod.map]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
⚠ [10337/10544] Replayed NSFormalization.Paper3.SobolevDirectionalDerivative
warning: NSFormalization/Paper3/SobolevDirectionalDerivative.lean:103:16: `SchwartzMap.smul_apply` has been deprecated: Use `smul_apply` instead

Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.smul_apply` to `smul_apply x`).
⚠ [10344/10544] Replayed NSFormalization.Source.BoundedViscosityUniqueness
warning: NSFormalization/Source/BoundedViscosityUniqueness.lean:21:28: This simp argument is unused:
  one_smul

Hint: Omit it from the simp argument list.
  [apply] simp only [smul_smul, h₂, smul_add, smul_sub]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
⚠ [10348/10544] Replayed Formal.R3LerayFrequencySymbol
warning: ../vendor/HeliCorgi/Formal/R3LerayFrequencySymbol.lean:43:2: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
⚠ [10351/10544] Replayed Formal.R3StokesL2Operator
warning: ../vendor/HeliCorgi/Formal/R3StokesL2Operator.lean:111:2: Try this: 
  letI̵

The goal is a proposition, so `let` is preferred over `letI`.
The difference between `let` and `letI` is that `letI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
⚠ [10352/10544] Replayed Formal.R3L2ScalarAux
warning: ../vendor/HeliCorgi/Formal/R3L2ScalarAux.lean:26:2: Try this: 
  letI̵

The goal is a proposition, so `let` is preferred over `letI`.
The difference between `let` and `letI` is that `letI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
⚠ [10360/10544] Replayed Formal.FlowMapNonextendibilityCriterion
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
⚠ [10361/10544] Replayed Formal.UniformRestartContinuation
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
⚠ [10362/10544] Replayed Formal.R3SobolevCarrier
warning: ../vendor/HeliCorgi/Formal/R3SobolevCarrier.lean:80:2: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
⚠ [10365/10544] Replayed Formal.R3CoordinateLinearAux
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
⚠ [10368/10544] Replayed Formal.R3DivergencePointwise
warning: ../vendor/HeliCorgi/Formal/R3DivergencePointwise.lean:25:19: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
⚠ [10372/10544] Replayed Formal.R3LerayL2Operator
warning: ../vendor/HeliCorgi/Formal/R3LerayL2Operator.lean:34:2: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
warning: ../vendor/HeliCorgi/Formal/R3LerayL2Operator.lean:61:2: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
⚠ [10373/10544] Replayed Formal.R3LerayFourierBridge
warning: ../vendor/HeliCorgi/Formal/R3LerayFourierBridge.lean:73:2: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
⚠ [10374/10544] Replayed Formal.R3LerayComplexFiberSymbol
warning: ../vendor/HeliCorgi/Formal/R3LerayComplexFiberSymbol.lean:42:2: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
⚠ [10430/10544] Replayed NSFormalization.Section4.A01.AprioriFamily
warning: NSFormalization/Section4/A01/AprioriFamily.lean:148:31: Variable name `ha` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _ha

Note: This linter can be disabled with `set_option linter.unusedVariables false`
⚠ [10431/10544] Replayed NSFormalization.Section4.A01.MildGronwall
warning: NSFormalization/Section4/A01/MildGronwall.lean:150:31: Variable name `ha` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _ha

Note: This linter can be disabled with `set_option linter.unusedVariables false`
ℹ [10506/10544] Replayed NSFormalization.Source.RieszFourierScale
info: NSFormalization/Source/RieszFourierScale.lean:70:57: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
⚠ [10512/10544] Replayed NSFormalization.Source.RieszL2Fourier
warning: NSFormalization/Source/RieszL2Fourier.lean:31:2: Try this: 
  letI̵

The goal is a proposition, so `let` is preferred over `letI`.
The difference between `let` and `letI` is that `letI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
⚠ [10513/10544] Replayed NSFormalization.Source.FractionalRealization
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
Build completed successfully (10544 jobs).
```

### Direct module check (exit 0)

`lake env lean ../formalization/NSFormalization/Section4/R43/Endpoint.lean`: stdout/stderr are empty (0 bytes).

### Axiom audit and non-vacuity (exit 0)

`lake env lean ../research/R43/axioms_endpoint.lean`:

```text
'NSFormalization.Section4.R43.criticalConst' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R43.criticalConst_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R43.criticalConst_lt_bootstrap' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R43.criticalConst_absorption' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R43.criticalForcePrimitive_le_criticalConst' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.R43.criticalNormAt_le_criticalConst' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.R43.critical_absorption_of_small_force' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.R43.maximal_critical_absorption' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R43.maximal_h2TimeIntegral_zero_of_small_force' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.R43.maximal_squaredHTwoIntegral_of_small_force' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.R43.homogeneousAtZero_of_memForceR' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R43.inhomogeneousAtZero_of_memForceR' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'EndpointConformance.inhomogeneousAtZero' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### make check (exit 0)

Exact final 25 lines; the architecture JSON middle is omitted:

```text
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
.............
----------------------------------------------------------------------
Ran 13 tests in 0.045s

OK
python3 experiments/check_work_queue.py
30 work items: ownership, contract registration and task cards consistent.
```

### Full gates (exit 0)

`LEAN_NUM_THREADS=6 bash scripts/gates.sh NSFormalization.Section4.R43.Endpoint`. Captured head 30 and tail 40 lines:

```text
EXIT: 0 OUTPUT LINES: 28575
== make check
python3 experiments/check_formalization_plan.py --check
{
  "task_count": 30,
  "source_counts": {
    "formalization": 537,
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
[... middle output omitted ...]
info: Tests/Thresholds.lean:13:0: Contract BlowupDensity.Tests.checkedThresholds: checked; standard logical axioms only
info: Tests/Scaling.lean:18:0: Contract BlowupDensity.Tests.checkedScaling: checked; standard logical axioms only
info: Tests/EnergyAbsorptionPartial.lean:15:0: Contract BlowupDensity.Tests.checkedEnergyAbsorptionPartial: checked; standard logical axioms only
info: Tests/Packet.lean:14:0: Contract BlowupDensity.Tests.checkedPacket: checked; standard logical axioms only
info: Tests/EnergyAbsorptionPartialV3.lean:41:0: Contract BlowupDensity.Tests.checkedEnergyAbsorptionPartialV3: checked; standard logical axioms only
info: Tests/DatumLemmasV2.lean:23:0: Contract BlowupDensity.Tests.checkedDatumLemmasV2: checked; standard logical axioms only
info: Tests/EnergyHighPartial.lean:17:0: Contract BlowupDensity.Tests.checkedEnergyHighPartial: checked; standard logical axioms only
info: Tests/EnergyAbsorptionPartialV2.lean:32:0: Contract BlowupDensity.Tests.checkedEnergyAbsorptionPartialV2: checked; standard logical axioms only
info: Tests/InsertionLifespan.lean:24:0: Contract BlowupDensity.Tests.checkedInsertionLifespan: checked; standard logical axioms only
info: Tests/InsertionFamily.lean:19:0: Contract BlowupDensity.Tests.checkedInsertionFamily: checked; standard logical axioms only
info: Tests/RegularityPartial.lean:17:0: Contract BlowupDensity.Tests.checkedRegularityPartial: checked; standard logical axioms only
info: Tests/BochnerPartial.lean:14:0: Contract BlowupDensity.Tests.checkedBochnerPartial: checked; standard logical axioms only
info: Tests/DatumLemmas.lean:14:0: Contract BlowupDensity.Tests.checkedDatumLemmas: checked; standard logical axioms only
info: Tests/BoundedRepresentative.lean:14:0: Contract BlowupDensity.Tests.checkedBoundedRepresentative: checked; standard logical axioms only
info: Tests/CorrectionV2.lean:28:0: Contract BlowupDensity.Tests.checkedCorrectionV2: checked; standard logical axioms only
info: Tests/HomogeneousPartial.lean:15:0: Contract BlowupDensity.Tests.checkedHomogeneousPartial: checked; standard logical axioms only
info: Tests/GradientL6.lean:13:0: Contract BlowupDensity.Tests.checkedGradientL6: checked; standard logical axioms only
info: Tests/GradientL6V2.lean:22:0: Contract BlowupDensity.Tests.checkedGradientL6V2: checked; standard logical axioms only
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

### Independent test and base compatibility

`cd verification && LEAN_NUM_THREADS=6 lake test`: exit 0, independently checked because the gates script filters test output. Exact final eight lines:

```text
info: Tests/InsertionLifespanV2.lean:32:0: Contract BlowupDensity.Tests.checkedInsertionLifespanV2: checked; standard logical axioms only
ℹ [10572/10573] Replayed Tests.TameProduct
info: Tests/TameProduct.lean:14:0: Contract BlowupDensity.Tests.checkedTameProduct: checked; standard logical axioms only
ℹ [10573/10573] Replayed Tests.EnergyAbsorptionV4
info: Tests/EnergyAbsorptionV4.lean:18:0: Contract BlowupDensity.Tests.checkedEnergyAbsorptionV4: checked; standard logical axioms only
info: Tests/EnergyAbsorptionV4.lean:19:0: Contract BlowupDensity.Bindings.energyAbsorptionPartialV3_of_v4: checked; standard logical axioms only
info: Tests/EnergyAbsorptionV4.lean:100:0: Contract BlowupDensity.Tests.energyAbsorptionV4_terminalFinite: checked; standard logical axioms only
```

`python3 experiments/check_contracts.py --base-ref origin/erenup/integration`: exit 0. Captured head/tail:

```text
EXIT: 0 OUTPUT LINES: 28202
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
[... middle output omitted ...]
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

### Substantive mutation (expected exit 1)

`lake env lean ../research/R43/probes/rev223_widened.lean`:

```text
../research/R43/probes/rev223_widened.lean:14:66: error: Application type mismatch: The argument
  hsmall
has type
  forceSobolevENormL1 (1 / 2) f < ENNReal.ofReal (2 * criticalConst * ν)
but is expected to have type
  forceSobolevENormL1 (1 / 2) f < ENNReal.ofReal (criticalConst * ν)
in the application
  LE.le.trans_lt (forceHomogeneousENorm_le_forceSobolevENormL1 f hf) hsmall
```

### Hygiene and provenance

`git diff --check`: exit 0, zero output. `git diff --name-status origin/erenup/integration...HEAD -- verification`: exit 0, zero output. Full triple-dot file list was inspected; six implementation Lean files are additions (four R43, two A04), and there are no modified existing Lean modules.

`rg -n '\\b(sorry|admit|axiom|native_decide)\\b|maxHeartbeats'` over those six added implementation modules returns only:

```text
formalization/NSFormalization/Section4/R43/CriticalMomentum.lean:279:set_option maxHeartbeats 400000 in
```

Byte comparison of each dependency with `git show d6f9cfd605041cb015a2119d351b6d77578c6b18:<path>`:

```text
formalization/NSFormalization/Section4/A04/RestartFixedForce.lean: byte-identical = True
formalization/NSFormalization/Section4/A04/ShiftedExtension.lean: byte-identical = True
```

`python3 experiments/build_changed_lean.py --base-ref origin/erenup/integration --dry-run` (exit 0):

```text
Changed Lean modules: NSFormalization.Section4.R43.Endpoint, NSFormalization.Section4.R43.ForcePath
```

Required fixes: none.

