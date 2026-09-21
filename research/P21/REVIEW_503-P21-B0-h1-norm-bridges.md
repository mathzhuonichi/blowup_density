ACCEPT-WITH-NOTES

## 1. What the lane claims

Reviewed HEAD `3ebf245ab122869044388d20806fbad6e53ae072`, read-only. Scope is B0 as explicitly briefed: compactly supported smooth whole-space fields, smooth periodic fields, finite fixed-force caps, and four unproved target definitions. `research/P21/REPORT_503.md:3` correctly leaves P6 Partial. The claim is not support-free whole-space energy identities or a completed B0+B1 assembly.

Read CLAUDE.md, the lane-review skill, the top 40 LESSONS lines, common brief, ASSESSMENT, REPORT_499, ATTEMPTS_B0, and worker report. The three rev503 probes were already untracked at entry; inspected and reran them without changing them. No Lean source, existing record, or git state was changed.

Paper checked with `sed -n '1,38p'` and `sed -n '149,182p' paper/revised/sections/02-preliminaries.tex`: lines 3–10 specify angular whole-space weight and unit-period torus weight; lines 149–156 state integral continuation; lines 178–182 use uniform restart after high-order bounds. The separate H¹-uniform targets are correctly treated as research obligations, not a displayed clause of the revised proposition.

## 2. What is in Lean

Here R denotes `formalization/NSFormalization/Section4/A04/H1Bridges.lean`, T denotes `formalization/NSFormalization/Section3/T11/H1Bridges.lean`; all abbreviated citations below are file:line citations to these paths.

- **Whole space:** R:45,49,54 define sums of component value, first-partial, and all ordered second-partial squared integrals. R:141,151,174 prove exactly H¹²=L+G, H²²=L+2G+H, and H²²=H¹²+G+H, with only smoothness and compact support. R:111 is the general real-order Fourier identity. The coefficient 2 is necessary. `Source/AngularGradientIdentity.lean:45,61` cancels the 2π multiplier under the angular change of variables and proves the successor recurrence; `Paper1/PeriodicScalarForceEndpoints.lean:30,38` supplies Parseval and order one. Thus κ=1, not (2π)⁻².
- **No hidden infinity:** R:68,85 constructs a genuine finite-norm datum at every real order; R:115 rewrites the registered infimum to its norm using `Section4/A03/VectorTameProduct.lean:71`. Compact support gives integrability of all derivatives through Schwartz representatives. The real-valued conclusions do not exploit top.toReal=0.
- **Torus:** T:30,35,40 define normalized cube energies; T:49,70,82,94 prove the exact natural-order identity and the same H¹/H² formulas. `Section3/T10/PeriodicData.lean:68` uses 1+4π²Σkᵢ²; the exponent in the squared energy is s. `Paper1/PeriodicHigherSobolev.lean:28,148` supplies the physical H² expansion and integer-order Parseval. Finiteness is constructed by `Section3/T10/ForcePaths.lean:25`, used at T:54, then `Section3/T17/Sobolev.lean:71`. No zero-mean or finiteness assumption was added; the low mode remains.
- **Force caps:** R:184,198 and T:106,110 define actual ENNReal suprema on [0,S+1] and prove them finite. R:229,238,248 and T:139,148,158 give pointwise, iterated-supremum, and shifted-force bounds over [0,S]×[0,1]. For S≥0 these intervals are nonempty, including S=0. The cap depends only on f,S. The unused `_hS` in each finiteness proof is harmless: on negative empty windows the supremum is zero; it does not make the stated nonnegative-window result vacuous. Order-zero path continuity is used explicitly, not assumed as an extra input. Compare the existing model `Section4/A04/RestartFixedForce.lean:21`.
- **Shifted torus forces:** T:166 proves global smoothness and periodicity only. `Section3/T10/PeriodicData.lean:239,245` shows MemForceT is exactly membership in forceClassT and requires compact time support inside (0,∞); positive shifts need not preserve it. No such membership conclusion appears.
- **Targets:** `research/P21/Targets.lean:26,38,51,63` type-check. A whitespace/comment-normalized comparison against the four ASSESSMENT §1 expressions returned True for all four. δ precedes both restart time and datum; K≠top, positive viscosity/duration, strict whole-space lifespan, and both torus overlap equalities are retained. These are Prop definitions, not proofs.
- **Hygiene:** no forbidden proof tokens or heartbeat overrides in either new module. All 23 theorems are included in `research/P21/axioms_b0.lean:4` onward, and all print exactly the standard three axioms. `formalization/blueprint/entrypoints.json:15,42` registers both modules. The three-dot diff lists only two added proof modules, six added research deliverables, and modifications to entrypoints/AXIOM_AUDIT; no existing Lean module or verification file changed.
- **Negative/non-vacuity:** `research/P21/probes/rev503_h2_coefficient_mutation.lean:16` changes the recurrence gradient coefficient from 1 to 2, supplies every original argument, and fails at line 21 with the expected conclusion mismatch. `research/P21/probes/rev503_nonvacuity.lean:18,20,29,35` constructs a smooth bump times coordinateVector 0, proves it nonzero at zero, and verifies finite H¹/H² norms and the recurrence. This is a concrete nonzero compact smooth field (inner radius 1, outer radius 2).

## 3. Gaps and exact notes

**Key B1/B4 integration result: B0 does not discharge any of the three B1 hypotheses verbatim.** REPORT_504 is absent locally; inspected it and its Lean module using read-only `git show erenup/504-P21-B1-enstrophy-r3:...`, at commit `c772bc65fd17881ecf779e76f15b8d5ed86feccb`. Sibling citations refer to that commit.

1. `research/P21/REPORT_504.md:58–67` and sibling `Section4/A04/EnstrophyInequality.lean:416–427` fix κ=(2π)⁻². B0 correctly supplies κ=1. The fixed H¹ equality cannot be obtained by merely increasing an estimate constant. Use the parameterized theorem at sibling :347 with κ=1, then recompute/specialize Cν. The delivered norm convention must not be changed to fit the incorrect fixed wrapper.
2. B1 consumes classical velocity slices on all interior times; R:142 requires compact support. `Section4/A05/SmoothJets.lean:44` defines SmoothL2 without compact support. A support-free registered-norm identity is still required. `rev503_b1_handoff.lean:24,30` reproduces the missing-support and coefficient mismatches; this is integration diagnostics, not the substantive mutation test.
3. B0 component energies are not verbatim `C01.l2Sq`, `gradientSq`, `laplacianSq` (definitions at `C01/ForceSlices.lean:83`, `C01/EnergyBounds.lean:65`, `C01/Trilinear.lean:72`). Finite-sum/integral and component derivative adapters remain, plus the gradTensor L²-to-sqrt-gradientSq statement. The Hessian–Laplacian analysis **already exists** at `Section4/A05/HessianLaplacian.lean:89`; do not relabel it missing analysis. `A05/GradientL6.lean:45` supplies the Frobenius tensor. Thus B4 needs convention, regularity-scope, and carrier adapters, not just one constant rewrite.

These do not invalidate the explicitly requested compact-core B0 delivery, but must be recorded before anyone treats B0+B1 as assembled.

**Whole-tree gap search:** ran `grep -rnE` over all `formalization/NSFormalization/Section4`, capturing the complete results before summarizing:
- `convection.*(interpol|sobolev)|young_quartic|enstrophy_differential`: 0 matches.
- `[Bb]arrier|monotone.*(integr|limit)|lintegral.*iSup`: 0 matches.
- `h1Restart|H1.*restart|restart.*H1`: 3 matches; inspected `A01/Continuation.lean:242–260`: its q≥6 cylinder theorem is not H¹ restart.
- `maximalLifespan|squaredHTwoIntegral`: 124 matches; existing `A04/Continuation.lean:72` and `RestartFixedForce.lean:331` provide conditional maximality machinery, not the H¹ barrier supplier.
- `gradientSq|laplacianSq|gradTensor`: 169 matches; inspected the C01/A05 declarations above. `C01/H2TimeIntegral.lean:35` has an explicit critical-smallness assumption. `C01/EnstrophyIdentityRaw.lean:19` describes strict-interior integrability, which does not establish the required endpoint estimate. `Section3/T20/H1Energy.lean:7` likewise explicitly assumes critical smallness and is not used by B0.

Accept REPORT_503:73 onward as “not proved by this lane / not assembled here,” not a blanket library absence claim. B1's sibling delivery also means the local “B1 pending” ledger is not a current cross-lane inventory.

**Exact one-line fixes (documentation only):**
- Add to `research/P21/P6_SPLIT.md:34`: “B0 proves compact-core R³ identities with κ=1; B1 consumption still needs support-free/carrier adapters and specialization of enstrophy_differential_of_norm_bridges at κ=1, not its fixed (2π)⁻² wrapper.”
- Add to each new module's header (R:9, T:6): “Source: paper/revised/sections/02-preliminaries.tex:3–10 (norm conventions), :178–182 (fixed force on [0,S+1]); internal Route B bridge, not a proof of Proposition 2.1.”

## 4. Commands and results

All Lean commands used `. scripts/lean-env.sh`, exported `LEAN_NUM_THREADS=6`, and ran Lake from verification/. One Lake command at a time. Build output is upstream replay warnings only, with no diagnostics from either H1Bridges module. Outputs below are exact; long output is restricted to its first/last 40 lines. Empty output is explicitly marked.


### `lake build NSFormalization.Section4.A04.H1Bridges NSFormalization.Section3.T11.H1Bridges`

Exit 0; 346 output lines.

```text
⚠ [9809/10072] Replayed NSFormalization.Source.FiniteHilbertBochner
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
⚠ [9820/10072] Replayed NSFormalization.Paper1.PeriodicSobolevHilbert
info: NSFormalization/Paper1/PeriodicSobolevHilbert.lean:60:55: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
warning: NSFormalization/Paper1/PeriodicSobolevHilbert.lean:60:51: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
⚠ [9821/10072] Replayed NSFormalization.Paper1.LocalizationBoundary
warning: NSFormalization/Paper1/LocalizationBoundary.lean:355:36: `if_pos` has been deprecated: Use `ite_eq_left` instead
warning: NSFormalization/Paper1/LocalizationBoundary.lean:361:8: `if_neg` has been deprecated: Use `ite_eq_right` instead
⚠ [9828/10072] Replayed Formal.EndpointSafeTwoSpacePicard
warning: ../vendor/HeliCorgi/Formal/EndpointSafeTwoSpacePicard.lean:126:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
[middle omitted]
⚠ [10027/10072] Replayed NSFormalization.Paper1.PeriodicDensityFiber
warning: NSFormalization/Paper1/PeriodicDensityFiber.lean:85:5: Variable name `hT` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hT

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: NSFormalization/Paper1/PeriodicDensityFiber.lean:118:5: Variable name `hT` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hT

Note: This linter can be disabled with `set_option linter.unusedVariables false`
⚠ [10031/10072] Replayed NSFormalization.Paper1.PeriodicLocalLifespan
warning: NSFormalization/Paper1/PeriodicLocalLifespan.lean:100:23: Variable name `U` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _U

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: NSFormalization/Paper1/PeriodicLocalLifespan.lean:325:24: Variable name `V` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _V

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: NSFormalization/Paper1/PeriodicLocalLifespan.lean:335:24: Variable name `V` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _V

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: NSFormalization/Paper1/PeriodicLocalLifespan.lean:400:26: `dif_pos` has been deprecated: Use `dite_eq_left` instead
warning: NSFormalization/Paper1/PeriodicLocalLifespan.lean:587:13: Variable name `hS` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hS

Note: This linter can be disabled with `set_option linter.unusedVariables false`
Build completed successfully (10072 jobs).
```

### `lake env lean ../formalization/NSFormalization/Section4/A04/H1Bridges.lean`

Exit 0; 0 output lines.

(zero output)

### `lake env lean ../formalization/NSFormalization/Section3/T11/H1Bridges.lean`

Exit 0; 0 output lines.

(zero output)

### `lake env lean ../research/P21/Targets.lean`

Exit 0; 0 output lines.

(zero output)

### `lake env lean ../research/P21/probes/b0_closes.lean`

Exit 0; 0 output lines.

(zero output)

### `lake env lean ../research/P21/axioms_b0.lean`

Exit 0; 47 output lines.

```text
'NSFormalization.Section4.A04.realSymmetry_angularDatum' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A04.compactAngularDatumR_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A04.isSobolevDatum_compactAngularDatumR' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A04.compactAngularDatumR_norm_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A04.sobolevENorm_toReal_sq_eq_angular' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A04.angularSobolevSq_two_eq_physical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A04.sobolevENorm_one_toReal_sq_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A04.sobolevENorm_two_toReal_sq_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A04.sobolevENorm_two_eq_one_add_gradient_hessian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A04.forceSlice_contDiffR' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A04.forceL2CapR_ne_top' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A04.force_slice_le_forceL2CapR' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A04.iSup_shifted_force_slice_le_forceL2CapR' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A04.timeShift_force_slice_le_forceL2CapR' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T11.periodicSobolevENorm_nat_toReal_sq_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T11.periodicSobolevENorm_one_toReal_sq_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T11.periodicSobolevENorm_two_toReal_sq_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T11.periodicSobolevENorm_two_eq_one_add_gradient_hessian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T11.forceL2CapT_ne_top' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T11.force_slice_le_forceL2CapT' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T11.iSup_shifted_force_slice_le_forceL2CapT' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T11.timeShiftT_force_slice_le_forceL2CapT' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T11.timeShiftT_smooth_periodic' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### `lake env lean ../research/P21/probes/rev503_h2_coefficient_mutation.lean`

Exit 1; 10 output lines.

```text
../research/P21/probes/rev503_h2_coefficient_mutation.lean:21:2: error: Type mismatch
  NSFormalization.Section4.A04.sobolevENorm_two_eq_one_add_gradient_hessian hz hc
has type
  (sobolevENorm 2 z).toReal ^ 2 =
    (sobolevENorm 1 z).toReal ^ 2 + NSFormalization.Section4.A04.gradientEnergyR z +
      NSFormalization.Section4.A04.hessianEnergyR z
but is expected to have type
  (sobolevENorm 2 z).toReal ^ 2 =
    (sobolevENorm 1 z).toReal ^ 2 + 2 * NSFormalization.Section4.A04.gradientEnergyR z +
      NSFormalization.Section4.A04.hessianEnergyR z
```

### `lake env lean ../research/P21/probes/rev503_nonvacuity.lean`

Exit 0; 0 output lines.

(zero output)

### `lake env lean ../research/P21/probes/rev503_b1_handoff.lean`

Exit 1; 17 output lines.

```text
../research/P21/probes/rev503_b1_handoff.lean:24:2: error: Type mismatch
  NSFormalization.Section4.A04.sobolevENorm_one_toReal_sq_eq (NSFormalization.Section4.A05.SmoothL2.contDiff hz)
has type
  HasCompactSupport z →
    (sobolevENorm 1 z).toReal ^ 2 =
      NSFormalization.Section4.A04.l2EnergyR z + NSFormalization.Section4.A04.gradientEnergyR z
but is expected to have type
  (sobolevENorm 1 z).toReal ^ 2 =
    NSFormalization.Section4.A04.l2EnergyR z + NSFormalization.Section4.A04.gradientEnergyR z
../research/P21/probes/rev503_b1_handoff.lean:30:2: error: Type mismatch
  NSFormalization.Section4.A04.sobolevENorm_one_toReal_sq_eq hz hc
has type
  (sobolevENorm 1 z).toReal ^ 2 =
    NSFormalization.Section4.A04.l2EnergyR z + NSFormalization.Section4.A04.gradientEnergyR z
but is expected to have type
  (sobolevENorm 1 z).toReal ^ 2 =
    NSFormalization.Section4.A04.l2EnergyR z + 1 / (2 * Real.pi) ^ 2 * NSFormalization.Section4.A04.gradientEnergyR z
```

### Article audit

`python3 experiments/audit_article_axioms.py --build --output-dir tmp/article-audit --workers 2`

Exit 0. Only ignored audit artifacts written; tracked audit record untouched.

```text
Bindings.CompletedDensity: 8 declarations checked
NSFormalization.Section3.T21.MainAssembly: 33 declarations checked
NavierStokes.ComparatorR3Theorem: 2 declarations checked
Bindings.BoundaryInsertionV2: 4 declarations checked
NSFormalization.Source.PacketBreakdown: 1 declarations checked
Bindings.LocalTheoryV2: 1 declarations checked
Bindings.TorusLocalTheory: 1 declarations checked
Bindings.AffineVariation: 1 declarations checked
NSFormalization.Section3.T24.MultipleAssembly: 1 declarations checked
NSFormalization.Section3.T24.ConservativeAssembly: 1 declarations checked
NSFormalization.Section4.R43.Universal: 1 declarations checked
Bindings.ForceClasses: 1 declarations checked
Bindings.GridObservations: 1 declarations checked
56 declarations; 27 article entries; 0 forbidden-axiom results
```

### make check (after audit)

Exit 0; also passed before audit, without stale-source rejection.

```text
python3 experiments/check_formalization_plan.py --check
Blueprint: 41 proof nodes, 27 article/guide mappings; 2241 source modules; local imports and package paths resolve.
Static packaging checks only; no Lean build or mathematical certification.
python3 experiments/check_contracts.py --summary
{
  "registered_contracts": 29,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
python3 experiments/test_contract_policy.py
...........
----------------------------------------------------------------------
Ran 11 tests in 0.003s

OK
```

`git diff --check`: exit 0, zero output. `git diff --name-only origin/erenup/core...HEAD`: the ten paths listed in REPORT_503 §2; name-status confirms both proof modules are added, not modifications. `rg -n 'sorry|admit|\\baxiom\\b|native_decide|maxHeartbeats'` on both new modules: exit 1, zero matches. `make test` and `make test-mutations` were not required by this review's conditional gate because verification/ was untouched; neither was run. No installation was needed: the pinned workspace built successfully.

---
**Lead ruling (2026-09-21 06:25Z):** merged with the two documentation notes applied (module-header source citations; B0/κ=1 note in `P6_SPLIT.md`, already superseded in substance by lanes 507/508 which built the support-free adapters and re-instantiated B1 at κ=1). Comment-only edits; no Lean statement or proof changed.
