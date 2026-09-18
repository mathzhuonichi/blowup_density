ACCEPT-WITH-NOTES

## 1. What the lane claims

The worker report claims the exact U3 reverse-localization estimate, with a fixed explicit positive real constant, together with the two Gagliardo identities, the difference split, and the two localization bounds (`research/T12/REPORT_377.md:5-7`). It also claims a nonzero smooth mean-zero periodic witness (`research/T12/REPORT_377.md:9-10`) and no residual U3 gap (`research/T12/REPORT_377.md:12-13`).

This is the mathematics requested by the lane brief and the U3 split: the required target is stated at `research/T12/T12_SPLIT.md:71-80`, and U4 consumes exactly this physical-cube `L²` spelling at `research/T12/T12_SPLIT.md:100-109`. The manuscript supplies the whole-space and torus Gagliardo identities at `paper/sections/03-torus.tex:40-72`; the critical torus embedding for mean-zero fields is at `paper/sections/appendix-b-embeddings.tex:11-24` and its spectral-gap reduction is at `paper/sections/appendix-b-embeddings.tex:75-94`.

Citation note: the reverse estimate proved here is an internal U3 lemma, not the forward periodization estimate literally stated in the paper at `paper/sections/03-torus.tex:22-30,79-95`. The final theorem docstring at `formalization/NSFormalization/Section3/T12/CutoffGagliardo.lean:969-974` should cite `research/T12/T12_SPLIT.md:71-80` as the direct statement source and describe the two paper files as ingredients/consumer.

## 2. What is in Lean

The main theorem exists with the requested statement exactly:

```lean
theorem cutoff_gagliardo_half (v : SpatialField) (hv : SmoothPeriodicT v)
    (hmean : IsMeanZeroT v) :
    dotHomogeneousENorm (1 / 2) (cutoffMul v)
      ≤ ENNReal.ofReal cutoffGagliardoConst
        * (eLpNorm v 2 (volume.restrict fundamentalCube)
            + periodicHomogeneousENorm (1 / 2) v)
```

This is `formalization/NSFormalization/Section3/T12/CutoffGagliardo.lean:975-982`, matching the report at `research/T12/REPORT_377.md:6` and U3 at `research/T12/T12_SPLIT.md:71-80`. The constant is exactly

```lean
max (Real.sqrt (2 * 343))
  (Real.sqrt (2 * cbConst * (cFrac (1 / 2)).toReal⁻¹))
```

at `formalization/NSFormalization/Section3/T12/CutoffGagliardo.lean:961-962`, and strict positivity is proved at `formalization/NSFormalization/Section3/T12/CutoffGagliardo.lean:965-967`. Its second coefficient is honest: `Jval` and `cbConst = 686 * Jval.toReal` are defined at `formalization/NSFormalization/Section3/T12/CutoffGagliardo.lean:816-827`, and `Jval < ⊤` is proved there. The inverse of `(cFrac (1/2)).toReal` is not a `⊤.toReal = 0` escape: positivity and finiteness are proved at `formalization/NSFormalization/Section3/T12/CutoffGagliardo.lean:68-79` from the tree theorem `constant_pos_finite`.

The report's supporting statements also exist with the claimed statements:

- `ireal_cutoffMul_eq` is at `formalization/NSFormalization/Section3/T12/CutoffGagliardo.lean:84-88` and applies the exact tree theorem `wholeSpace_identity` (`formalization/NSFormalization/Section3/T13/WholeSpaceIdentity.lean:509-513`) using cutoff smoothness/compact support from `formalization/NSFormalization/Section3/T12/Cutoff.lean:176-183`.
- `itorus_meanZero_eq` is at `formalization/NSFormalization/Section3/T12/CutoffGagliardo.lean:92-96` and applies `torus_identity_smooth` (`formalization/NSFormalization/Section3/T13/TorusIdentity.lean:1100-1102`) after `meanZeroPartT_eq_self` (`CutoffGagliardo.lean:59-63`).
- The split `IReal ≤ 2*IA + 2*IB` is at `formalization/NSFormalization/Section3/T12/CutoffGagliardo.lean:228-271`.
- `iA_bound : IA v ≤ ofReal 343 * ITorus (1/2) v` is at `formalization/NSFormalization/Section3/T12/CutoffGagliardo.lean:565-604`; its fold uses the cited `lintegral_cube_periodicKernel` at `CutoffGagliardo.lean:481-495` and its finite `7³` count is at `CutoffGagliardo.lean:509-564`.
- `iB_bound : IB v ≤ ofReal cbConst * eLpNorm ... ^ 2` is at `formalization/NSFormalization/Section3/T12/CutoffGagliardo.lean:889-955`; the Lipschitz estimate is at `CutoffGagliardo.lean:699-719`, kernel finiteness at `CutoffGagliardo.lean:608-697`, and the ball tiling estimate at `CutoffGagliardo.lean:750-798`.
- The algebraic assembly is at `formalization/NSFormalization/Section3/T12/CutoffGagliardo.lean:278-317`; both `hv` and `hmean` are passed into load-bearing results in the final proof at `CutoffGagliardo.lean:981-982`. There are no named `Prop` inputs or repackaged target hypotheses.

The hypotheses are jointly non-vacuous. The shipped probe constructs `probeMZ`, proves it smooth-periodic, mean-zero, and nonzero at `research/T12/probes/cutoff_gagliardo_closes.lean:96-137`, and instantiates the exact theorem at `research/T12/probes/cutoff_gagliardo_closes.lean:139-147`. That probe typechecks with zero output.

Hygiene is clean in the Lean source: no `sorry`, `admit`, `axiom`, `native_decide`, or `maxHeartbeats` occurs in any changed `.lean` file. The module contains 67 top-level declarations (53 theorems and 14 definitions). My exhaustive scratch audit, `research/T12/probes/rev377_axioms_all.lean`, prints all 67 with exactly `[propext, Classical.choice, Quot.sound]`.

The three-dot diff against the requested base is:

```text
A formalization/NSFormalization/Section3/T12/CutoffGagliardo.lean
A research/T12/ATTEMPTS_U3.md
A research/T12/REPORT_377.md
M research/T12/T12_SPLIT.md
A research/T12/axioms_u3.lean
A research/T12/probes/cutoff_gagliardo_closes.lean
```

Thus no pre-existing formalization module was modified; the only modified pre-existing file is the required U3 status record `research/T12/T12_SPLIT.md`. Nothing under `verification/` was touched.

## 3. Gaps and exact fixes

There is no mathematical or build gap in U3. The report declares no missing tree lemma (`research/T12/REPORT_377.md:12-13`), so the mandatory Section4 whole-tree search for a claimed absent lemma is inapplicable; a search of the report/attempts found no “not in the tree” claim.

The negative test substantively changes the main statement's constant from `cutoffGagliardoConst` to `cutoffGagliardoConst / 2` in `research/T12/probes/rev377_negative_constant.lean:15-20`. Reusing the original proof fails, as required:

```text
../research/T12/probes/rev377_negative_constant.lean:20:2: error: Type mismatch
  cutoff_gagliardo_half v hv hmean
has type
  dotHomogeneousENorm (1 / 2) (cutoffMul v) ≤
    ENNReal.ofReal cutoffGagliardoConst *
      (eLpNorm v 2 (volume.restrict T13.fundamentalCube) + periodicHomogeneousENorm (1 / 2) v)
but is expected to have type
  dotHomogeneousENorm (1 / 2) (cutoffMul v) ≤
    ENNReal.ofReal (cutoffGagliardoConst / 2) *
      (eLpNorm v 2 (volume.restrict fundamentalCube) + periodicHomogeneousENorm (1 / 2) v)
```

Exact fixes required for a fully clean record:

1. `research/T12/axioms_u3.lean`: add `#print axioms` for the 46 omitted top-level declarations, so the shipped audit covers all 67 declarations rather than 21; `research/T12/probes/rev377_axioms_all.lean` is the verified complete list.
2. `research/T12/REPORT_377.md:3,10`: replace “21 declarations” / “axioms_u3.lean (21)” with “67 declarations, all audited”; after fix 1 this is exact.
3. `research/T12/REPORT_377.md:16`: replace “lake build ... 0 warnings” with “exit 0; dependency oleans replayed pre-existing warnings, while direct `lake env lean` on CutoffGagliardo produced 0 output.”
4. `formalization/NSFormalization/Section3/T12/CutoffGagliardo.lean:969`: make the direct citation `research/T12/T12_SPLIT.md:71-80`, with `03-torus.tex:40-72` and `appendix-b-embeddings.tex:11-24` identified as ingredients/consumer rather than the verbatim source of this reverse estimate.

## 4. Commands and results

Environment for every Lean command: `. scripts/lean-env.sh`; Lake was invoked only from `verification/`; `LEAN_NUM_THREADS=6` was set.

`lake build NSFormalization.Section3.T12.CutoffGagliardo` exited 0. The raw output was 223 lines / 13,482 bytes. It contained only replayed warnings/info from imported pre-existing modules (none from `CutoffGagliardo`) and ended exactly:

```text
warning: NSFormalization/Paper1/PeriodicLocalLifespan.lean:400:26: `dif_pos` has been deprecated: Use `dite_eq_left` instead
warning: NSFormalization/Paper1/PeriodicLocalLifespan.lean:587:13: Variable name `hS` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hS

Note: This linter can be disabled with `set_option linter.unusedVariables false`
Build completed successfully (9998 jobs).
```

`lake env lean ../formalization/NSFormalization/Section3/T12/CutoffGagliardo.lean`:

```text
<no output; exit 0>
```

`lake env lean ../research/T12/probes/cutoff_gagliardo_closes.lean`:

```text
<no output; exit 0>
```

`lake env lean ../research/T12/axioms_u3.lean` exited 0 with exactly these 21 audit results:

```text
'NSFormalization.Section3.T12.meanZeroPartT_eq_self' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.cFrac_half_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.cFrac_half_lt_top' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.cFrac_half_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.cFrac_half_ne_top' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.ireal_cutoffMul_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.itorus_meanZero_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.enn_sqrt_div_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.lintegral_two_add_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.measurable_gA_pair' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.measurable_gB_pair' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.ireal_cutoffMul_le_split' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.dotHomogeneousENorm_cutoffMul_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T12.iA_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.iB_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.cutoffLip' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.Jval' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.cbConst' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.cutoffGagliardoConst' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.cutoffGagliardoConst_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.cutoff_gagliardo_half' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The exhaustive reviewer audit command on `rev377_axioms_all.lean` gave:

```text
lean_exit_code=0
axiom_lines=67
nonstandard_lines=0
```

`make check` exited 0. Its exact raw output was 45,708 lines / 1,884,845 bytes because `check_contracts.py` prints contract closures; to avoid embedding 1.8 MB, here are the exact captured first and last 25 lines:

```text
python3 experiments/check_formalization_plan.py --check
{
  "task_count": 45,
  "source_counts": {
    "formalization": 608,
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
...
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
      "Tests.PacketImport"
    ]
  },
  "base_compatibility_checked": false,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.042s

OK
python3 experiments/check_work_queue.py
45 work items: ownership, contract registration and task cards consistent.
```

Hygiene commands:

```text
$ rg '^(def|theorem|lemma|instance|axiom) ' CutoffGagliardo.lean | wc -l
67
$ rg '^#print axioms ' research/T12/axioms_u3.lean | wc -l
21
$ rg -n '\b(sorry|admit|axiom|native_decide)\b|maxHeartbeats' <changed Lean files>
<no output>
$ git diff --check origin/erenup/integration-section3...HEAD
<no output; exit 0>
```

Neither `scripts/gates.sh` nor `check_contracts.py --base-ref origin/erenup/integration-section3` was required or run, because `git diff --name-only origin/erenup/integration-section3...HEAD` contains no path under `verification/`.
