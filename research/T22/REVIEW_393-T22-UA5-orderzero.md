ACCEPT-WITH-NOTES

## 1. What the lane claims

The exact target in research/T22/REPORT_393.md:15 is
```lean
theorem orderZero (Ω : Set Space) (hΩ : IsOpen Ω) (z : SpatialField)
    (hz : ContDiffOn ℝ ∞ z Ω) :
    domainSobolevENorm Ω 0 (restrictField Ω z) = eLpNorm z 2 (volume.restrict Ω)
```
This matches formalization/NSFormalization/Section3/T22/OrderZero.lean:219,
Domain.lean:59 in the same directory, and research/T22/Spec.lean:125.
I opened paper/sections/03-torus.tex:600–630 with sed: lines 603–607 define
the restriction quotient norm and identify order zero with the usual L² norm.
The open-set/local-smoothness hypotheses are exactly the reconciled target,
with no boundedness, compact-support, or MemLp premise silently added.

The report's supporting statements exist as claimed in OrderZero.lean:
conjugation_fourierInv_of_mem:58, fourierInv_ofReal_re_ae:67, fieldOf:77,
fieldOf_apply:80, memLp_fieldOf:83, orderZeroDatum_surjective:94,
restrictField_eq_ae:129, restrictDatum_eq_restrictField_of_datum:197,
sobolevENorm_zero_eq_eLpNorm:206. Implicit parameters in the report's
abbreviated supporting statements agree with the source.

## 2. What is in Lean

All paths abbreviated below are relative to formalization/NSFormalization/.

- Section3/T22/Domain.lean:26,33,38,43,47 defines interior Schwartz tests,
  distributional restriction, the actual ENNReal infimum over extensions,
  physical pairing, and literal indicator extension. These agree with
  research/T22/Spec.lean:62,72,81,89. The norm is not a restatement of the
  conclusion; no toReal or empty-interval shortcut appears.
- Section3/T22/OrderZero.lean:224 handles infinite RHS directly; :229–235
  constructs the finite zero extension and proves the upper bound.
  The lower bound at :237–248 quantifies over every extension datum.
  Surjectivity at :94 and distributional uniqueness at :129 identify
  its physical field on Ω. The empty infimum remains top, correctly.
- Opened the actual providers: Section4/D01/OrderZeroDatum.lean:96,103,118
  (constructor and realization); Section4/D01/FiniteOrderNorm.lean:69,99,114
  (Pythagoras and prior bound); Section3/T22/OrderZeroIsometry.lean:117
  (exact norm identity); Section3/T22/RestrictBridge.lean:25,48 (restriction
  and quotient inequality); Section4/D01/ForceClass.lean:286 (uniqueness);
  Section4/D01/SmoothDatum.lean:98,114 (conjugation and Fourier bridge).
- Non-vacuity: research/T22/probes/orderzero_closes.lean:31–65 uses a smooth
  compact bump, identically coordinateVector 0 on ball 0 1 (:44), nonzero
  at its center (:50), and proves equality and finite RHS (:56).
  Equality also makes the LHS finite. This meets the brief. The theorem
  does not explicitly assert positive norms, although positivity follows
  from the nonzero constant field on this open ball.
- Hygiene: token scan of both new modules finds forbidden words only in
  comments. There are no admission/axiom/native_decide commands, no new
  instances, and no named input predicates. OrderZero.lean:88 is the only
  raised budget in this module, per declaration, 400000; explanation is
  at :39–40. Inherited OrderZeroIsometry budgets are likewise per
  declaration, 400000, commented.
- The triple-dot diff lists only new Lean modules/files and the modified
  research/T22/T22_SPLIT.md; no existing Lean module or verification file
  was modified. Git warns of multiple merge bases, shown below.
  CI's .github/workflows/contracts.yml:81 calls
  experiments/build_changed_lean.py; its :18 includes formalization Lean
  paths, so this new module is covered by changed-module builds.

## 3. Gaps and exact one-line fixes

No mathematical gap in U-A5. Two documentation corrections are required;
neither requires changing a proof or statement.

1. **Incorrect provider limitation**, research/T22/REPORT_393.md:47.
   Section3/T22/T22_SPLIT's status discussion at research/T22/T22_SPLIT.md:164
   should likewise avoid implying the L² helpers are fractional-order only.
   The opened Section4-independent Paper1/LocalizationBoundary.lean:64,73
   lemmas have no s parameter or 0<s<1 premise.
   Exact replacement sentence:
   “The proof uses restricted-measure eLpNorm lemmas directly; LocalizationBoundary.domainL2Sq_le_whole and domainL2Sq_eq_whole_of_compl_eq_zero also apply at L² but require an integral-to-eLpNorm bridge.”

2. **Overbroad novelty claim**, research/T22/ATTEMPTS_UA5.md:27 and the
   “missing bridge” description in research/T22/REPORT_393.md:26.
   Whole-Section4 searches found Section4/R44/TrilinearJ.lean:181–202,
   halfDatumPhysicalComponent_real: the same Fourier-injectivity/reality
   argument for order-lowered half-order data. It is not the exact general
   order-zero surjectivity theorem. Exact replacement sentence:
   “The general order-zero realization/reality lemmas are new here; Section4/R44/TrilinearJ.lean:181 already proves the analogous inverse-Fourier reality fact for half-order data.”

Searches run over the whole formalization/NSFormalization/Section4 tree:
```sh
grep -rnE 'orderZeroDatum_surjective|conjugation_fourierInv|fourierInv_ofReal|restrictField_eq_ae|domainL2Sq|cutoffMultiplier|zeroExtensionComparison' formalization/NSFormalization/Section4
grep -rnE 'surject|fourierInv|conjugation|realSubspace' formalization/NSFormalization/Section4
grep -rnE 'fourierInv|surject' formalization/NSFormalization/Section4
```
The exact-name search returned no matches (exit 1). The broader search
located the R44 analogue above and the D01 providers already cited.
Thus the exact surjectivity theorem was not found, but the blanket
“nothing of this form existed” claim is not acceptable.
U-A3/U-Z1/U-REG are outside the requested deliverable; no corresponding
completed field theorem was found by the exact-name Section4 search.

Substantive negative check: research/T22/probes/rev393_mutation.lean:221
copies the entire module into a fresh namespace, changing only the main
conclusion's coefficient from 1 to 2, retaining every hypothesis and proof.
It fails at :245 because the unchanged lower-bound calculation starts
with eLpNorm whereas the mutated target requires 2 * eLpNorm.
The full diagnostic is pasted below. This is a mathematical statement
mutation, not a dropped-argument test.

## 4. Commands and results

All Lean shells sourced scripts/lean-env.sh; every lake invocation ran
from verification/ with LEAN_NUM_THREADS=6, one lake process at a time.
No install was needed: the existing environment successfully built and
checked the module. No git-state operation was performed.

`lake env lean ../formalization/NSFormalization/Section3/T22/OrderZero.lean`
exited 0 with **zero output**.
`lake build NSFormalization.Section3.T22.OrderZero` exited 0; no diagnostics
from this module. Its exact output (dependency replay warnings included):

```text
⚠ [9809/9931] Replayed NSFormalization.Source.FiniteHilbertBochner
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
ℹ [9829/9931] Replayed NSFormalization.Source.PhysicalBesselSobolev
info: NSFormalization/Source/PhysicalBesselSobolev.lean:134:4: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
⚠ [9836/9931] Replayed NSFormalization.Source.PacketForceExtension
warning: NSFormalization/Source/PacketForceExtension.lean:44:25: `if_pos` has been deprecated: Use `ite_eq_left` instead
⚠ [9839/9931] Replayed NSFormalization.Source.ViscosityPacket
warning: NSFormalization/Source/ViscosityPacket.lean:34:63: This simp argument is unused:
  Function.comp_def

Hint: Omit it from the simp argument list.
  [apply] simp [viscosityVelocity, dilateField, viscosityHomeomorph, Prod.map]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
⚠ [9847/9931] Replayed NSFormalization.Source.RealSobolev
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
⚠ [9851/9931] Replayed NSFormalization.Paper3.SpatiallyCompactTime
warning: NSFormalization/Paper3/SpatiallyCompactTime.lean:88:19: `ContinuousLinearMap.sub_apply` has been deprecated: Use `sub_apply` instead

Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.sub_apply` to `sub_apply x`).
⚠ [9858/9931] Replayed NSFormalization.Paper3.RealPositiveDensity
warning: NSFormalization/Paper3/RealPositiveDensity.lean:67:59: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Paper3/RealPositiveDensity.lean:76:63: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Paper3/RealPositiveDensity.lean:88:59: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Paper3/RealPositiveDensity.lean:100:59: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
⚠ [9872/9931] Replayed NSFormalization.Paper3.RealVectorPositiveDensity
warning: NSFormalization/Paper3/RealVectorPositiveDensity.lean:29:5: Variable name `hc` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hc

Note: This linter can be disabled with `set_option linter.unusedVariables false`
⚠ [9878/9931] Replayed Formal.R3LerayFrequencySymbol
warning: ../vendor/HeliCorgi/Formal/R3LerayFrequencySymbol.lean:43:2: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
⚠ [9881/9931] Replayed Formal.R3StokesL2Operator
warning: ../vendor/HeliCorgi/Formal/R3StokesL2Operator.lean:111:2: Try this: 
  letI̵

The goal is a proposition, so `let` is preferred over `letI`.
The difference between `let` and `letI` is that `letI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
⚠ [9882/9931] Replayed Formal.R3L2ScalarAux
warning: ../vendor/HeliCorgi/Formal/R3L2ScalarAux.lean:26:2: Try this: 
  letI̵

The goal is a proposition, so `let` is preferred over `letI`.
The difference between `let` and `letI` is that `letI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
⚠ [9890/9931] Replayed Formal.FlowMapNonextendibilityCriterion
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
⚠ [9891/9931] Replayed Formal.UniformRestartContinuation
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
⚠ [9892/9931] Replayed Formal.R3SobolevCarrier
warning: ../vendor/HeliCorgi/Formal/R3SobolevCarrier.lean:80:2: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
⚠ [9895/9931] Replayed Formal.R3CoordinateLinearAux
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
⚠ [9898/9931] Replayed Formal.R3DivergencePointwise
warning: ../vendor/HeliCorgi/Formal/R3DivergencePointwise.lean:25:19: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
⚠ [9902/9931] Replayed Formal.R3LerayL2Operator
warning: ../vendor/HeliCorgi/Formal/R3LerayL2Operator.lean:34:2: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
warning: ../vendor/HeliCorgi/Formal/R3LerayL2Operator.lean:61:2: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
⚠ [9903/9931] Replayed Formal.R3LerayFourierBridge
warning: ../vendor/HeliCorgi/Formal/R3LerayFourierBridge.lean:73:2: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
⚠ [9904/9931] Replayed Formal.R3LerayComplexFiberSymbol
warning: ../vendor/HeliCorgi/Formal/R3LerayComplexFiberSymbol.lean:42:2: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
⚠ [9914/9931] Replayed NSFormalization.Paper3.SobolevDirectionalDerivative
warning: NSFormalization/Paper3/SobolevDirectionalDerivative.lean:103:16: `SchwartzMap.smul_apply` has been deprecated: Use `smul_apply` instead

Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.smul_apply` to `smul_apply x`).
Build completed successfully (9931 jobs).
```


`lake env lean ../research/T22/axioms_ua5.lean` — exit 0:

```text
'NSFormalization.Section3.T22.orderZero' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T22.orderZeroDatum_surjective' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T22.restrictField_eq_ae' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T22.restrictDatum_eq_restrictField_of_datum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T22.sobolevENorm_zero_eq_eLpNorm' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T22.conjugation_fourierInv_of_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T22.fourierInv_ofReal_re_ae' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T22.memLp_fieldOf' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`lake env lean ../research/T22/probes/orderzero_closes.lean` — exit 0:

```text
'T22ProbeA5.probe_closes' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`lake env lean ../research/T22/probes/rev393_audit.lean` — exit 0:

```text
'NSFormalization.Section3.T22.fieldOf' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T22.fieldOf_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`lake env lean ../research/T22/probes/rev393_mutation.lean` — exit 1:

```text
../research/T22/probes/rev393_mutation.lean:225:23: error: typeclass instance problem is stuck
  OrderTop ?m.66

Note: Lean will not try to resolve this typeclass instance problem because the first and second type arguments to `OrderTop` are metavariables. These arguments must be fully determined before Lean will try to resolve the typeclass.

Hint: Adding type annotations and supplying implicit arguments to functions can give Lean more information for typeclass resolution. For example, if you have a variable `x` that you intend to be a `Nat`, but Lean reports it as having an unresolved type like `?m`, replacing `x` with `(x : Nat)` can get typeclass resolution un-stuck.
../research/T22/probes/rev393_mutation.lean:226:4: error: unsolved goals
case refine_1.inr.calc.step
Ω : Set Space
hΩ : IsOpen Ω
z : SpatialField
hz : ContDiffOn ℝ ∞ z Ω
hfin : eLpNorm z 2 (volume.restrict Ω) ≠ ∞
hmΩ : MeasurableSet Ω
haem : AEStronglyMeasurable z (volume.restrict Ω)
hzL2 : MemLp z 2 (volume.restrict Ω)
hE : MemLp (zeroExtension Ω z) 2 volume
⊢ eLpNorm z 2 (volume.restrict Ω) ≤ 2 * eLpNorm z 2 (volume.restrict Ω)
../research/T22/probes/rev393_mutation.lean:245:9: error: invalid 'calc' step, left-hand side is
  eLpNorm z 2 (volume.restrict Ω) : ℝ≥0∞
but is expected to be
  2 * eLpNorm z 2 (volume.restrict Ω) : ℝ≥0∞
```

`make check` — exit 0. Exact first/last 20 lines follow; the 47,563-line architecture JSON middle is omitted per logs/LESSONS.md's review-output size instruction.

```text
EXIT: 0 LINES: 47563
python3 experiments/check_formalization_plan.py --check
{
  "task_count": 45,
  "source_counts": {
    "formalization": 617,
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
[middle omitted: large architecture JSON]
      "NavierStokes.WeightedClasses",
      "NavierStokes.WeightedODEJets",
      "NavierStokes.WeightedQuotients",
      "NavierStokes.WeightedRadialPrimitive",
      "NavierStokes.ZerothStressIdentity",
      "TestSupport.Axioms",
      "Tests.Localization"
    ]
  },
  "base_compatibility_checked": false,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.047s

OK
python3 experiments/check_work_queue.py
45 work items: ownership, contract registration and task cards consistent.
```

`git diff --name-only origin/erenup/integration-section3...HEAD` — exit 0:

```text
warning: origin/erenup/integration-section3...HEAD: multiple merge bases, using 8db38fe7ef1463684285fa6f61822093ca86ec29
formalization/NSFormalization/Section3/T22/OrderZero.lean
formalization/NSFormalization/Section3/T22/OrderZeroIsometry.lean
research/T22/ATTEMPTS_UA4.md
research/T22/ATTEMPTS_UA5.md
research/T22/REPORT_387.md
research/T22/REPORT_393.md
research/T22/T22_SPLIT.md
research/T22/axioms_ua4.lean
research/T22/axioms_ua5.lean
research/T22/probes/orderzero_closes.lean
research/T22/probes/orderzero_isometry_closes.lean
```

The same diff restricted to verification/ has no paths. Accordingly,
scripts/gates.sh and check_contracts.py --base-ref
origin/erenup/integration-section3 are not triggered by the user's
“if verification/ was touched” condition. make check ran the ordinary
contract checker successfully.

Review additions are only this report and rev393_audit.lean /
rev393_mutation.lean. The intentionally failing mutation stays outside the
formalization/ CI module tree. Worker Lean and records were not changed.

Verdict: ACCEPT-WITH-NOTES. Fix the two documentation sentences in part 3.

