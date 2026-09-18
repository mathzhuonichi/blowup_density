ACCEPT-WITH-NOTES

## 1. What the lane claims

Reviewed commit `1da578c1` against `origin/erenup/integration-section3`, read-only except for this report and two permitted reviewer probes. Read `CLAUDE.md`, `.claude/skills/lane-review/SKILL.md`, the first 40 lines of `logs/LESSONS.md`, the brief, `REPORT_391.md`, `REPORT_386.md`, and `T22_SPLIT.md` §0/U-A2/U-A3.

`research/T22/REPORT_391.md:9`–30 claims weighted integrability for every Schwartz function, a complex Schwartz representative of a real compact smooth cutoff, weighted integrability of its angular and cycles Fourier transforms, and finite ENNReal kernel mass. These are the correct U-A2 obligations, not a claim to have finished U-A3's multiplier theorem.

The paper was opened with `sed -n '600,630p' paper/sections/03-torus.tex` and `sed -n '85,96p' paper/sections/01-introduction.tex`. The rapid-decay step at `paper/sections/03-torus.tex:623`–624 supplies exactly the weighted L¹ kernel needed by Young's inequality. The normalization at `paper/sections/01-introduction.tex:91` agrees with `formalization/NSFormalization/Source/FourierConvention.lean:23`–29. The consumer is `research/T22/Spec.lean:140`–144, with the complexified cutoff multiplication defined at `research/T22/Spec.lean:99`–104.

## 2. What is in Lean

Let `K` abbreviate the path `formalization/NSFormalization/Section3/T22/CutoffKernel.lean` in the citations below. All six public declarations match the report's displayed statements:

| Declaration | Location | Verified statement |
| --- | --- | --- |
| `integrable_weighted_schwartz` | `K:68` | For every real `s` and `ψ : SchwartzMap Space ℂ`, `Integrable (fun ζ => (1 + ‖ζ‖ ^ 2) ^ (|s| / 2) * ‖ψ ζ‖)`. |
| `cutoffSchwartz` | `K:114` | A `SchwartzMap Space ℂ`, given only `ContDiff ℝ ∞ χ` and `HasCompactSupport χ`. |
| `cutoffSchwartz_apply` | `K:120` | `cutoffSchwartz hχ hc x = (χ x : ℂ)`. |
| `integrable_weighted_fourier_cutoff` | `K:131` | The same weight times `‖angularFourier (fun x => (χ x : ℂ)) ζ‖` is integrable, for all real `s`. |
| `integrable_weighted_fourier_cutoff_mathlib` | `K:145` | The same statement with Mathlib `𝓕`. |
| `lintegral_weighted_fourier_cutoff_ne_top` | `K:157` | The `lintegral` of `ENNReal.ofReal` of the angular weighted norm is not `⊤`. |

The proof is substantive: `K:70` chooses `k > |s| + 3`; `K:74` proves the dimensional tail condition; `K:87` proves the weight comparison; `K:93` obtains genuine Schwartz decay; `K:104` supplies the integrable domination. No named analytic inputs, unused hypotheses, empty-domain restrictions, or `.toReal` are present. Smoothness and compact support both feed the concrete Schwartz construction at `K:116`–118. The nonnegative integrand makes the ENNReal formulation honest (`K:161`–163).

Opened and checked the reused declarations, rather than relying on names:

- `vendor/NavierStokesAndEuler/NavierStokes/R3/CompactSchwartz.lean:24` and `:37`: bounded weighted derivatives and the actual compact-support Schwartz construction.
- `formalization/NSFormalization/Paper3/AngularFourierDilation.lean:18`, `:27`, `:209`: the amplitude/dilation and its exact angular Fourier coercion.
- `verification/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:482`: the seminorm decay estimate, including its constants.
- `verification/.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/JapaneseBracket.lean:137`: integrability of `(1+‖x‖)^(-r)` for `finrank < r`.
- `verification/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Fourier.lean:51`, `:86`, `:98`: Schwartz Fourier construction, named Fourier instance, and coercion identity.
- `formalization/NSFormalization/Paper3/SobolevHilbertModel.lean:24`: the datum's Bessel weight is exactly the complex coercion of `(1+‖ξ‖²)^(s/2)`.
- `formalization/NSFormalization/Section4/D01/SmoothDatum.lean:237`: the datum uses `angularRealization`; `Section4/D01/HomogeneousWitness.lean:99`, `:109` confirm the related angular Schwartz and weighted-integrability constructions.
- `formalization/NSFormalization/Paper3/CompactFourier.lean:54`: the cited earlier result is weighted L², not the new L¹ statement.

Non-vacuity is already supplied by `research/T22/probes/cutoff_kernel_closes.lean:18`–24: the explicit radii-1-and-2 `ContDiffBump` is smooth and compactly supported. It takes value 1 at the origin by `ContDiffBump.one_of_mem_closedBall` (`Mathlib/Analysis/Calculus/BumpFunction/Basic.lean:137`). All six examples at orders `1/2` and `-2` typecheck. There are no new instance declarations requiring explicit names.

## 3. Gaps and exact one-line fixes

No mathematical gap in U-A2. Four minor record/audit corrections:

1. **Audit completeness**, `research/T22/axioms_ua2.lean:11`: insert `#print axioms cutoffSchwartz_apply`. It is the sixth public declaration and the reviewer independently verified its exact standard-three-axiom output.
2. **Count**, `research/T22/REPORT_391.md:45`: replace `5 public` with `6 public`.
3. **Citation**, `K:18` and `research/T22/ATTEMPTS_UA2.md:43`: replace `Spec.lean:118-128` with `Spec.lean:99-104` (the former is the order-zero field commentary, not `IsCutoffDatum`).
4. **Scan report**, `research/T22/REPORT_391.md:81`: replace `none found` with `no forbidden Lean declarations; the word axiom occurs only in the audit docstring`. A literal word scan does match `research/T22/axioms_ua2.lean:4`.

The report does not claim a missing in-tree lemma for U-A2. Its deferred scalar/vector convolution discussion (`REPORT_391.md:67`) was nevertheless checked by whole-tree searches:

```sh
grep -rnE 'convolution|fourier_smul|fourier_mul' formalization/NSFormalization/Section4
grep -rnE 'weighted.*fourier|fourier.*weighted|fourier.*(mul|smul)|convolution' formalization/NSFormalization/Section4
```

The potentially misleading hit `Section4/B02/LowHigh.lean:56` was opened: `fourier_mul_formula` is integral self-adjointness, not the Fourier product/convolution theorem. The A01 hits are time convolutions; A05/B02 scalar-multiplication hits do not construct the U-A3 cutoff datum. This supports deferring U-A3; it does not assert that no useful lemma exists anywhere outside Section4.

Hygiene: no forbidden proof terms, heartbeat overrides, or existing Lean module edits. The changed existing files are only the explicitly requested lesson/status records. The module is selected by `experiments/build_changed_lean.py:18` and that checker is invoked by `.github/workflows/contracts.yml:81`.

## 4. Commands and results

Every Lean invocation used `. scripts/lean-env.sh`, ran Lake from `verification/`, and set `LEAN_NUM_THREADS=6`. One Lake invocation at a time. Existing dependencies were already available; no installer, git mutation, or lane-source edit was performed.

### Build

`lake build NSFormalization.Section3.T22.CutoffKernel`: exit 0. Exact output:

```text
⚠ [8798/8812] Replayed NSFormalization.Source.RealSobolev
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
⚠ [8802/8812] Replayed NSFormalization.Paper3.SpatiallyCompactTime
warning: NSFormalization/Paper3/SpatiallyCompactTime.lean:88:19: `ContinuousLinearMap.sub_apply` has been deprecated: Use `sub_apply` instead

Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.sub_apply` to `sub_apply x`).
⚠ [8809/8812] Replayed NSFormalization.Paper3.RealPositiveDensity
warning: NSFormalization/Paper3/RealPositiveDensity.lean:67:59: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Paper3/RealPositiveDensity.lean:76:63: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Paper3/RealPositiveDensity.lean:88:59: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Paper3/RealPositiveDensity.lean:100:59: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
Build completed successfully (8812 jobs).
```

`lake env lean ../formalization/NSFormalization/Section3/T22/CutoffKernel.lean` and `lake env lean ../research/T22/probes/cutoff_kernel_closes.lean`: zero output, successful; no warnings in the module itself.

`lake env lean ../research/T22/axioms_ua2.lean`: successful, exact output:

```text
'NSFormalization.Section3.T22.integrable_weighted_schwartz' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T22.cutoffSchwartz' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T22.integrable_weighted_fourier_cutoff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T22.integrable_weighted_fourier_cutoff_mathlib' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T22.lintegral_weighted_fourier_cutoff_ne_top' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

`lake env lean ../research/T22/probes/rev391_audit.lean`: successful, exact output:

```text
'NSFormalization.Section3.T22.cutoffSchwartz_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Substantive negative check

`research/T22/probes/rev391_mutation.lean:7` copies the entire master proof, changing only the integrand from weighted `‖ψ ζ‖` to weighted `(‖ψ ζ‖ + 1)`. No argument is dropped. This introduces a nondecaying constant tail; at `s = 0`, `ψ = 0`, the false conclusion would assert integrability of 1 on ℝ³.

`lake env lean ../research/T22/probes/rev391_mutation.lean`: exit 1, exact expected error:

```text
../research/T22/probes/rev391_mutation.lean:42:9: error: invalid 'calc' step, left-hand side is
  (1 + ‖ζ‖ ^ 2) ^ (|s| / 2) * ‖ψ ζ‖ : ℝ
but is expected to be
  (1 + ‖ζ‖ ^ 2) ^ (|s| / 2) * (‖ψ ζ‖ + 1) : ℝ
```

### Repository checks

`make check`: exit 0, independently run twice (second run to capture bounded output after the first tool output was truncated). The second combined output is 1,963,045 bytes, SHA256 `2c2df22073f05542ee2d7530ed800b7449870ff8ba11af993e980ae7f1c0f2da`. Exact first 10 and last 20 lines are pasted below; the large JSON middle is omitted explicitly.

```text
python3 experiments/check_formalization_plan.py --check
{
  "task_count": 45,
  "source_counts": {
    "formalization": 616,
    "vendor/NavierStokesAndEuler": 2486,
    "vendor/HeliCorgi": 129
  },
  "source_manifest_entries": 2975,
  "missing_copied_imports": [],
```

```text
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
Ran 13 tests in 0.081s

OK
python3 experiments/check_work_queue.py
45 work items: ownership, contract registration and task cards consistent.
```

`scripts/gates.sh` and the additional base-aware `check_contracts.py` were not required by the review brief's `verification/`-touched condition: no file under `verification/` changed. The ordinary contract checker did run inside `make check` (42 registered contracts). No claim of a full contract test/mutation suite rerun is made.

`git diff --name-only origin/erenup/integration-section3...HEAD`: exact output:

```text
formalization/NSFormalization/Section3/T22/CutoffKernel.lean
logs/LESSONS.md
research/T22/ATTEMPTS_UA2.md
research/T22/REPORT_391.md
research/T22/T22_SPLIT.md
research/T22/axioms_ua2.lean
research/T22/probes/cutoff_kernel_closes.lean
```

`git diff --name-status` confirms the sole Lean module is added, not modified. `git diff --check origin/erenup/integration-section3...HEAD`: exit 0, zero output.

`rg -n '\b(sorry|admit|axiom|native_decide)\b|maxHeartbeats|^instance'` on the module, worker probe, and audit finds only:

```text
research/T22/axioms_ua2.lean:4:Transitive-axiom audit for T22 U-A2 (`Section3/T22/CutoffKernel.lean`).
```

No proof fix is required. Apply the four record/audit corrections above.
