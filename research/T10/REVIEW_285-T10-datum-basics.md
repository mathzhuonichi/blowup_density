ACCEPT

## 1. What the lane claims

The worker report claims exact implementations of the three requested API
fields, the reusable component-integrability lemma, the Fourier/zero-mode
supporting lemmas, and no residual hypothesis or proof gap
(`research/T10/REPORT_285.md:3`, `research/T10/REPORT_285.md:25`,
`research/T10/REPORT_285.md:40`).  Those claims are accurate.

- `datum_unique` is stated at
  `formalization/NSFormalization/Section3/T10/DatumBasics.lean:134` and is
  token-for-token the canonical API field at
  `research/T10/probes/api_on_canonical.lean:43`.  The closure assignment is at
  `research/T10/probes/datum_basics_closes.lean:13`.
- `datum_real` is stated at
  `formalization/NSFormalization/Section3/T10/DatumBasics.lean:146` and is
  token-for-token the canonical API field at
  `research/T10/probes/api_on_canonical.lean:56`.  The closure assignment is at
  `research/T10/probes/datum_basics_closes.lean:18`.
- `meanZero_datum` is stated at
  `formalization/NSFormalization/Section3/T10/DatumBasics.lean:155` and is
  token-for-token the canonical API field at
  `research/T10/probes/api_on_canonical.lean:134`.  The closure assignment is
  at `research/T10/probes/datum_basics_closes.lean:24`.
- `IsPeriodicDatum.integrable_component` has the requested statement at
  `formalization/NSFormalization/Section3/T10/DatumBasics.lean:28`.

The mathematics matches the cited sources.  The paper defines the exact
weighted Fourier coefficients and vector norm at
`paper/sections/01-introduction.tex:83`, the omitted zero mode/mean-zero
convention at `paper/sections/01-introduction.tex:105`, real-field conjugate
symmetry at `paper/sections/02-preliminaries.tex:72`, and the physical
subtraction of the mean at `paper/sections/03-torus.tex:395`.  The canonical
Lean definitions use the same weight and coefficient equation at
`formalization/NSFormalization/Section3/T10/PeriodicData.lean:58` and
`formalization/NSFormalization/Section3/T10/PeriodicData.lean:102`, the real
carrier at `formalization/NSFormalization/Section3/T10/PeriodicData.lean:70`,
and literal mean subtraction/zero-mode membership at
`formalization/NSFormalization/Section3/T10/PeriodicData.lean:116` and
`formalization/NSFormalization/Section3/T10/PeriodicData.lean:133`.

## 2. What is in Lean

`datum_unique` uses the two explicit coefficient equations and extensionality
of the real `WithLp` carrier
(`formalization/NSFormalization/Section3/T10/DatumBasics.lean:137`).
`datum_real` exposes exactly the defining carrier membership
(`formalization/NSFormalization/Section3/T10/DatumBasics.lean:150`).  Its datum
hypothesis is intentionally redundant because every `PeriodicSobolev s`
already lies in `realPeriodicSubmodule`; that binder comes from the verbatim API
field rather than being an added or dishonest premise.

`meanZero_datum` subtracts the three `lp.single` zero modes
(`formalization/NSFormalization/Section3/T10/DatumBasics.lean:161`), proves
periodicity and integrability at lines 164--169, identifies scalar component
integrability at line 171, proves the Fourier subtraction formula at lines
175--192, and proves zero-mode membership at lines 193--196.  The lead-amended
integrability conjunct is materially used by `integrable_component` at line 34,
by vector subtraction at line 169, and by Fourier linearity at lines 171--185;
there is no added `.toReal`, finiteness, positivity, or interval premise.

The support declarations are real lemmas, not assumptions:
`integral_mFourier` at line 38, `periodicFourierCoeff_const` at line 48,
`periodicFourierCoeff_sub` at line 58,
`periodicFourierCoeff_zero_eq_mean_component` at line 102,
`periodicZeroModePart` at line 117, and `periodicZeroModePart_mem` at line 121.
The concrete zero-field datum at lines 201--212 supplies the brief's requested
non-vacuity witness for every real order.

The substantive negative probe changes mean subtraction to addition at
`research/T10/probes/rev285_meanZero_sign_mutation.lean:12`.  It fails for the
expected mathematical mismatch, not from removing an argument:

```text
exit_code=1
../research/T10/probes/rev285_meanZero_sign_mutation.lean:18:2: error: Type mismatch
  meanZero_datum
has type
  ∀ (s : ℝ) (z : SpatialField) (A : ↥(PeriodicSobolev s)),
    IsPeriodicDatum s z A → ∃ B, IsPeriodicDatum s (meanZeroPartT z) B ∧ B ∈ meanZeroPeriodicSobolev s
but is expected to have type
  ∀ (s : ℝ) (z : SpatialField) (A : ↥(PeriodicSobolev s)),
    IsPeriodicDatum s z A → ∃ B, IsPeriodicDatum s (fun x => z x + meanT z) B ∧ B ∈ meanZeroPeriodicSobolev s
```

## 3. Gaps and hygiene

There is no mathematical or Lean gap and no residual named hypothesis.  The
report therefore makes no gap-style “not in the tree” claim.  For completeness,
the attempts file's narrower search claim at
`research/T10/ATTEMPTS_DATUM_BASICS.md:19` was rechecked with `grep -rn` over
all of `formalization/NSFormalization/Section4`, the named Paper1 files, and the
four named Mathlib files: `mFourierCoeff_const` produced no output and exit 1.
The needed upstream facts do exist where cited: `lp.single_apply_self` and
`lp.single_apply_ne` are at
`verification/.lake/packages/mathlib/Mathlib/Analysis/Normed/Lp/lpSpace.lean:1029`,
and `eval_integral_piLp` is at
`verification/.lake/packages/mathlib/Mathlib/MeasureTheory/SpecificCodomains/WithLp.lean:44`.

The forbidden-token/heartbeat scan over the delivered Lean module, closure
probe, axioms file, and reviewer probe produced no output.  `git diff --check
origin/erenup/integration-section3...HEAD` also produced no output.  The exact
base diff is:

```text
formalization/NSFormalization/Section3/T10/DatumBasics.lean
research/T10/ATTEMPTS_DATUM_BASICS.md
research/T10/REPORT_285.md
research/T10/axioms_datum_basics.lean
research/T10/probes/datum_basics_closes.lean
```

Thus no existing module was modified.  The same command restricted to
`verification/` produced no output, so the user-specified conditional
`scripts/gates.sh` and `check_contracts.py --base-ref
origin/erenup/integration-section3` gates do not apply.

## 4. Commands and results

Environment for every Lean command: `. scripts/lean-env.sh`; all `lake`
commands ran from `verification/` with `LEAN_NUM_THREADS=6`.

```text
$ lake build NSFormalization.Section3.T10.DatumBasics
exit_code=0
⚠ [8778/9048] Replayed NSFormalization.Source.FiniteHilbertBochner
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
⚠ [9318/9353] Replayed NSFormalization.Source.RealSobolev
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
⚠ [9322/9353] Replayed NSFormalization.Paper3.SpatiallyCompactTime
warning: NSFormalization/Paper3/SpatiallyCompactTime.lean:88:19: `ContinuousLinearMap.sub_apply` has been deprecated: Use `sub_apply` instead

Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.sub_apply` to `sub_apply x`).
⚠ [9329/9353] Replayed NSFormalization.Paper3.RealPositiveDensity
warning: NSFormalization/Paper3/RealPositiveDensity.lean:67:59: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Paper3/RealPositiveDensity.lean:76:63: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Paper3/RealPositiveDensity.lean:88:59: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Paper3/RealPositiveDensity.lean:100:59: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
⚠ [9332/9353] Replayed NSFormalization.Paper3.RealVectorPositiveDensity
warning: NSFormalization/Paper3/RealVectorPositiveDensity.lean:29:5: Variable name `hc` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hc

Note: This linter can be disabled with `set_option linter.unusedVariables false`
⚠ [9342/9353] Replayed NSFormalization.Source.PacketForceExtension
warning: NSFormalization/Source/PacketForceExtension.lean:44:25: `if_pos` has been deprecated: Use `ite_eq_left` instead
⚠ [9345/9353] Replayed NSFormalization.Source.ViscosityPacket
warning: NSFormalization/Source/ViscosityPacket.lean:34:63: This simp argument is unused:
  Function.comp_def

Hint: Omit it from the simp argument list.
  [apply] simp [viscosityVelocity, dilateField, viscosityHomeomorph, Prod.map]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
Build completed successfully (9353 jobs).
```

All warnings are replayed upstream warnings; the reviewed module itself is
silent under direct Lean:

```text
$ lake env lean ../formalization/NSFormalization/Section3/T10/DatumBasics.lean
exit_code=0
(no output; 0 bytes)

$ lake env lean ../research/T10/probes/datum_basics_closes.lean
exit_code=0
(no output; 0 bytes)
```

The axioms audit output was exactly:

```text
$ lake env lean ../research/T10/axioms_datum_basics.lean
exit_code=0
'NSFormalization.Section3.T10.IsPeriodicDatum.integrable_component' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T10.integral_mFourier' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T10.periodicFourierCoeff_const' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T10.periodicFourierCoeff_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T10.periodicFourierCoeff_zero_eq_mean_component' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T10.periodicZeroModePart' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T10.periodicZeroModePart_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T10.datum_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T10.datum_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T10.meanZero_datum' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`make check` exited 0.  In accordance with the repository instruction not to
paste tens of thousands of JSON lines (`logs/LESSONS.md:15`), its exact first
12 and last 16 lines are recorded below; the complete captured output had
42,730 lines / 1,759,574 bytes and SHA-256
`5eb5778f1a0b982146384f32c4a01983caabff26d294c974ce33047774625da3`.

```text
$ make check
exit_code=0
python3 experiments/check_formalization_plan.py --check
{
  "task_count": 45,
  "source_counts": {
    "formalization": 552,
    "vendor/NavierStokesAndEuler": 2486,
    "vendor/HeliCorgi": 129
  },
  "source_manifest_entries": 2975,
  "missing_copied_imports": [],
  "citation_interfaces_reachable": [],
  "tokens_in_copied_umbrella_closure": [
...
      "NavierStokes.ZerothStressIdentity",
      "TestSupport.Axioms",
      "Tests.CompletedDensity"
    ]
  },
  "base_compatibility_checked": false,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.046s

OK
python3 experiments/check_work_queue.py
45 work items: ownership, contract registration and task cards consistent.
```

No fixes are required.
