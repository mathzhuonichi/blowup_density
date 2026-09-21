# U05 — Porting HeliCorgi's R³ mild-solution modules into this package

Lane 010, task U05 part 2. Date: 2026-09-13. Worktree: `.claude/worktrees/010-U05-port`.
Inputs: `research/U05/REPORT.md` (probe) and `research/U05/REVIEW.md` (review).

**Result: all 88 modules of the four targets' import closure now build under this
repository's pin** (`leanprover/lean4:v4.34.0-rc2`, Mathlib
`85e3a25e006c35636f0e53b0e9296caca2685bc0`). 84 of them are compiled *in place* out of
`vendor/HeliCorgi` by a new `Formal` library whose `srcDir` points there; the remaining 4
are patched copies in a new `FormalPatched` library. `vendor/` is byte-identical to HEAD.

The patch needed is **one proof hunk in one file**, not the ~42-line `NNReal.mk`
substitution the probe estimated, and it is **fully confined to the four copies** — no
statement in any of the 84 good modules had to change. See §4.

---

## 1. Step 1 — the 84 modules that compile unchanged

### 1.1 How the list was derived

Reproducible, not transcribed from the probe's table:

1. Parse every `Formal/*.lean` under `vendor/HeliCorgi` (128 files) with
   `experiments/check_formalization_plan.py`'s own `uncomment()` so that `import` lines
   inside block comments and strings are ignored — the same parser `make check` uses.
2. Depth-first post-order traversal from the four targets
   (`Formal.R3EndpointSafeProjectedLocalExistence`, `Formal.R3MildContinuation`,
   `Formal.R3NavierStokesEquation`, `Formal.R3HelmholtzPressure`), following only
   `Formal.*` imports. This yields **88** modules in topological build order; the
   sequence is identical to the table in `REPORT.md` §(b), which is the independent
   confirmation that the two derivations agree.
3. Subtract the 4 modules the probe found broken or unreached:
   `Formal.R3RealLocalMildSolution`, `Formal.R3QuantitativeLifespan`,
   `Formal.EndpointSafeTwoSpaceUniqueness`, `Formal.R3MildContinuation`.
   **84** remain.
4. Assert that no remaining module imports a removed one (0 such edges), so the 84 are
   import-closed and the library is buildable on its own.

### 1.2 The lakefile change

`roots`, never a glob: a glob such as `Formal.+` would sweep in all 128 vendored modules
including the 4 broken ones. `srcDir` is relative to the package directory
(`formalization/`), so `"../vendor/HeliCorgi"`. `vendor/HeliCorgi/lakefile.lean` sits
inside that `srcDir` and is *not* read — a `srcDir` creates no path dependency, so
HeliCorgi's own `require mathlib @ "v4.32.1"` is never seen.

```diff
diff --git a/formalization/lakefile.toml b/formalization/lakefile.toml
index defb123..593c3df 100644
--- a/formalization/lakefile.toml
+++ b/formalization/lakefile.toml
@@ -8,3 +8,115 @@ path = "../vendor/NavierStokesAndEuler"
 
 [[lean_lib]]
 name = "NSFormalization"
+
+# Vendored HeliCorgi R3 mild-solution sources, compiled in place under this
+# repository's pin (Lean 4.34.0-rc2 / Mathlib 85e3a25e006c35636f0e53b0e9296caca2685bc0).
+# `srcDir` keeps vendor/HeliCorgi byte-identical: no file there is copied or edited.
+# The list is the import closure of Formal.R3EndpointSafeProjectedLocalExistence,
+# Formal.R3NavierStokesEquation, Formal.R3HelmholtzPressure and Formal.R3MildContinuation
+# (88 modules) minus the four modules that do not compile at this pin, which are
+# maintained as patched copies in the FormalPatched library below.
+# Explicit `roots` on purpose: a glob would sweep in all 128 vendored modules.
+# Do not add `warningAsError` here; the vendored sources emit 52 benign warnings.
+# Evidence: research/U05/REPORT.md, research/U05/REVIEW.md, research/U05/PORT.md.
+[[lean_lib]]
+name = "Formal"
+srcDir = "../vendor/HeliCorgi"
+roots = [
+  "Formal.EndpointSafeTwoSpaceDuhamel",
+  "Formal.R3LerayFrequencySymbol",
+  "Formal.R3StokesFrequencySymbol",
+  "Formal.R3StokesL2Operator",
+  "Formal.R3CoordinateLinearAux",
+  "Formal.R3L2ScalarAux",
+  "Formal.FlowMapFTC",
+  "Formal.FlowMapChainRule",
+  "Formal.FlowMapOperatorContinuity",
+  "Formal.FlowMapContDiffOne",
+  "Formal.FlowMapLocalContDiff",
+  "Formal.PDEBridgeAdapter",
+  "Formal.NavierStokesTimeBridge",
+  "Formal.FlowMapNonextendibilityCriterion",
+  "Formal.UniformRestartContinuation",
+  "Formal.R3SobolevCarrier",
+  "Formal.R3SolenoidalSobolevCarrier",
+  "Formal.R3NormalizedFrequencyLpTop",
+  "Formal.R3L2CoordinateAux",
+  "Formal.R3NormalizedDivergenceTerm",
+  "Formal.R3DivergencePointwise",
+  "Formal.R3NormalizedDivergenceFrequency",
+  "Formal.R3ClosedSolenoidalCarrier",
+  "Formal.R3SolenoidalCarrierCompleteness",
+  "Formal.R3LerayL2Operator",
+  "Formal.R3SchwartzConvection",
+  "Formal.R3SchwartzSobolevCore",
+  "Formal.R3SchwartzConvectionSobolevReduction",
+  "Formal.R3H2BesselWeightGeometry",
+  "Formal.R3H2WeightedConvolutionKernel",
+  "Formal.R3H2AdditiveConvolutionWeight",
+  "Formal.R3YoungL1L2Bochner",
+  "Formal.R3SchwartzSobolevMonotonicity",
+  "Formal.R3H2YoungWeightedBridge",
+  "Formal.R3H2FourierL1Bound",
+  "Formal.R3LerayFourierBridge",
+  "Formal.R3LerayComplexFiberSymbol",
+  "Formal.R3LerayComplexDivergenceBridge",
+  "Formal.R3LerayPointwiseL2",
+  "Formal.R3LerayPointwiseProjectionIdentification",
+  "Formal.R3H2LerayBridge",
+  "Formal.R3SchwartzProductConvolution",
+  "Formal.R3SchwartzConvectionH2FrequencyMajorant",
+  "Formal.R3SchwartzConvectionScalarMajorants",
+  "Formal.R3YoungRealL1L2Bochner",
+  "Formal.R3SchwartzNormFieldL2",
+  "Formal.R3YoungRealSetIntegralBridge",
+  "Formal.R3YoungRealConvolutionCommutativity",
+  "Formal.R3SchwartzMajorantYoungRepresentative",
+  "Formal.R3SchwartzScalarMajorantL2",
+  "Formal.R3SchwartzConvectionH2L2Majorant",
+  "Formal.R3H2VelocityFourierL1Bound",
+  "Formal.R3H2CoordinateFourierBounds",
+  "Formal.R3H3DerivativeWeightGeometry",
+  "Formal.R3SchwartzDerivativeFrequencyBound",
+  "Formal.R3SchwartzDerivativeH3LpBounds",
+  "Formal.R3SchwartzConvectionH3Closure",
+  "Formal.R3SchwartzConvectionSobolevEstimate",
+  "Formal.R3SchwartzSobolevDensity",
+  "Formal.R3SobolevConvectionExtension",
+  "Formal.R3ProjectedSobolevConvection",
+  "Formal.R3StokesDivergenceCommutation",
+  "Formal.R3StokesSolenoidalPreservation",
+  "Formal.R3StokesH2H3Smoothing",
+  "Formal.R3StokesH3Evolution",
+  "Formal.R3EndpointSafeProjectedDuhamel",
+  "Formal.EndpointSafeTwoSpacePicard",
+  "Formal.R3EndpointSafeProjectedLocalExistence",
+  "Formal.R3ConjugationReflection",
+  "Formal.R3FourierConjugationBridge",
+  "Formal.R3StokesConjugationEquivariance",
+  "Formal.R3LerayConjugationEquivariance",
+  "Formal.R3ConvectionConjugationEquivariance",
+  "Formal.EndpointSafeTwoSpaceRestart",
+  "Formal.EndpointSafeTwoSpaceConcatenation",
+  "Formal.R3CoordinateIncompressibility",
+  "Formal.R3ClassicalIncompressibility",
+  "Formal.R3DecoderFrequencyBridge",
+  "Formal.R3InversionConsistency",
+  "Formal.R3HelmholtzPressure",
+  "Formal.R3ConvectionSourceIdentification",
+  "Formal.R3ProjectedMomentumDuhamelInfrastructure",
+  "Formal.R3ProjectedMomentumEquation",
+  "Formal.R3NavierStokesEquation"
+]
+
+# Patched copies of the four modules that fail at this pin. Same Lean namespaces
+# and declaration names as upstream, module path renamed so nothing collides with
+# the in-place `Formal` library. See research/U05/PORT.md for the exact diff.
+[[lean_lib]]
+name = "FormalPatched"
+roots = [
+  "FormalPatched.R3RealLocalMildSolution",
+  "FormalPatched.R3QuantitativeLifespan",
+  "FormalPatched.EndpointSafeTwoSpaceUniqueness",
+  "FormalPatched.R3MildContinuation"
+]
```

### 1.3 The 84 modules, in build order

 1. `Formal.EndpointSafeTwoSpaceDuhamel`
 2. `Formal.R3LerayFrequencySymbol`
 3. `Formal.R3StokesFrequencySymbol`
 4. `Formal.R3StokesL2Operator`
 5. `Formal.R3CoordinateLinearAux`
 6. `Formal.R3L2ScalarAux`
 7. `Formal.FlowMapFTC`
 8. `Formal.FlowMapChainRule`
 9. `Formal.FlowMapOperatorContinuity`
10. `Formal.FlowMapContDiffOne`
11. `Formal.FlowMapLocalContDiff`
12. `Formal.PDEBridgeAdapter`
13. `Formal.NavierStokesTimeBridge`
14. `Formal.FlowMapNonextendibilityCriterion`
15. `Formal.UniformRestartContinuation`
16. `Formal.R3SobolevCarrier`
17. `Formal.R3SolenoidalSobolevCarrier`
18. `Formal.R3NormalizedFrequencyLpTop`
19. `Formal.R3L2CoordinateAux`
20. `Formal.R3NormalizedDivergenceTerm`
21. `Formal.R3DivergencePointwise`
22. `Formal.R3NormalizedDivergenceFrequency`
23. `Formal.R3ClosedSolenoidalCarrier`
24. `Formal.R3SolenoidalCarrierCompleteness`
25. `Formal.R3LerayL2Operator`
26. `Formal.R3SchwartzConvection`
27. `Formal.R3SchwartzSobolevCore`
28. `Formal.R3SchwartzConvectionSobolevReduction`
29. `Formal.R3H2BesselWeightGeometry`
30. `Formal.R3H2WeightedConvolutionKernel`
31. `Formal.R3H2AdditiveConvolutionWeight`
32. `Formal.R3YoungL1L2Bochner`
33. `Formal.R3SchwartzSobolevMonotonicity`
34. `Formal.R3H2YoungWeightedBridge`
35. `Formal.R3H2FourierL1Bound`
36. `Formal.R3LerayFourierBridge`
37. `Formal.R3LerayComplexFiberSymbol`
38. `Formal.R3LerayComplexDivergenceBridge`
39. `Formal.R3LerayPointwiseL2`
40. `Formal.R3LerayPointwiseProjectionIdentification`
41. `Formal.R3H2LerayBridge`
42. `Formal.R3SchwartzProductConvolution`
43. `Formal.R3SchwartzConvectionH2FrequencyMajorant`
44. `Formal.R3SchwartzConvectionScalarMajorants`
45. `Formal.R3YoungRealL1L2Bochner`
46. `Formal.R3SchwartzNormFieldL2`
47. `Formal.R3YoungRealSetIntegralBridge`
48. `Formal.R3YoungRealConvolutionCommutativity`
49. `Formal.R3SchwartzMajorantYoungRepresentative`
50. `Formal.R3SchwartzScalarMajorantL2`
51. `Formal.R3SchwartzConvectionH2L2Majorant`
52. `Formal.R3H2VelocityFourierL1Bound`
53. `Formal.R3H2CoordinateFourierBounds`
54. `Formal.R3H3DerivativeWeightGeometry`
55. `Formal.R3SchwartzDerivativeFrequencyBound`
56. `Formal.R3SchwartzDerivativeH3LpBounds`
57. `Formal.R3SchwartzConvectionH3Closure`
58. `Formal.R3SchwartzConvectionSobolevEstimate`
59. `Formal.R3SchwartzSobolevDensity`
60. `Formal.R3SobolevConvectionExtension`
61. `Formal.R3ProjectedSobolevConvection`
62. `Formal.R3StokesDivergenceCommutation`
63. `Formal.R3StokesSolenoidalPreservation`
64. `Formal.R3StokesH2H3Smoothing`
65. `Formal.R3StokesH3Evolution`
66. `Formal.R3EndpointSafeProjectedDuhamel`
67. `Formal.EndpointSafeTwoSpacePicard`
68. `Formal.R3EndpointSafeProjectedLocalExistence`
69. `Formal.R3ConjugationReflection`
70. `Formal.R3FourierConjugationBridge`
71. `Formal.R3StokesConjugationEquivariance`
72. `Formal.R3LerayConjugationEquivariance`
73. `Formal.R3ConvectionConjugationEquivariance`
74. `Formal.EndpointSafeTwoSpaceRestart`
75. `Formal.EndpointSafeTwoSpaceConcatenation`
76. `Formal.R3CoordinateIncompressibility`
77. `Formal.R3ClassicalIncompressibility`
78. `Formal.R3DecoderFrequencyBridge`
79. `Formal.R3InversionConsistency`
80. `Formal.R3HelmholtzPressure`
81. `Formal.R3ConvectionSourceIdentification`
82. `Formal.R3ProjectedMomentumDuhamelInfrastructure`
83. `Formal.R3ProjectedMomentumEquation`
84. `Formal.R3NavierStokesEquation`

### 1.4 The smoke module

`formalization/NSFormalization/Section4/HeliCorgiPort.lean` imports the three targets that
need no patch and type-checks six references to their key declarations
(`r3EndpointSafeProjected_exists_localMildSolution`,
`r3EndpointSafeProjected_localMildSolution_equation`, `r3HelmholtzPressure`,
`r3HelmholtzPressure_gradient`, `r3EndpointSafeProjectedMild_navierStokes`,
`exists_r3EndpointSafeProjectedMild_navierStokes`) as `example := @MNS2.…`.

Its purpose is CI coverage: `experiments/build_changed_lean.py` compiles changed `.lean`
files under `formalization/` **by module name**, and a lakefile-only change compiles
nothing at all. With this file present, any change to the port is actually elaborated by
the `lean-contracts` job. It adds no mathematics and is not a contract, binding or test.

One correction was needed while writing it: `example := @MNS2.r3HelmholtzPressure` failed
with `failed to compile definition, consider marking it as 'noncomputable'`, because the
upstream definition is `noncomputable`; the line now reads
`noncomputable example := @MNS2.r3HelmholtzPressure`.

---

## 2. Step 2 — the four patched copies

`formalization/FormalPatched/` holds copies of the four modules renamed into the
`FormalPatched.*` module namespace. Lean *namespaces inside the files are unchanged*, so
every declaration keeps its upstream name (`MNS2.r3EndpointSafeProjected_blowup_dichotomy`
and so on). Each file carries an 8-line provenance header pointing back here.

Declared in `formalization/lakefile.toml` as a second `[[lean_lib]]` with the default
`srcDir` and explicit `roots` (see the diff in §1.2).

---

## 3. The exact diffs

Each is `diff -u vendor/HeliCorgi/Formal/<M>.lean formalization/FormalPatched/<M>.lean`.
The 8-line provenance header at the top of every copy is elided from the discussion below;
it is the first hunk of each diff and carries no Lean content.

### 3.1 `R3RealLocalMildSolution`

```diff
--- vendor/HeliCorgi/Formal/R3RealLocalMildSolution.lean	2026-09-13 00:51:51.451613661 -0400
+++ formalization/FormalPatched/R3RealLocalMildSolution.lean	2026-09-13 01:05:50.137637186 -0400
@@ -1,3 +1,12 @@
+-- Port of `vendor/HeliCorgi/Formal/R3RealLocalMildSolution.lean` (task U05, step 2).
+-- Verbatim copy of the vendored source except for the hunks recorded in
+-- `research/U05/PORT.md`: the mutual imports of the four ported modules are
+-- redirected to `FormalPatched.*`, and one `rw` that no longer matches at Lean
+-- 4.34.0-rc2 is replaced by a term-mode application of the same lemma.  Lean
+-- namespaces and declaration names are unchanged from upstream.  `vendor/` is
+-- not edited; the other 84 modules of the closure are compiled in place from
+-- `vendor/HeliCorgi` by the `Formal` library in `formalization/lakefile.toml`.
+
 import Formal.R3ConvectionConjugationEquivariance
 import Formal.R3EndpointSafeProjectedLocalExistence
 
@@ -58,6 +67,15 @@
     obtain ⟨hint_u, heq_u⟩ :=
       r3EndpointSafeProjectedMild_equation_at_time hnu ⟨hT0, hucont, hu0eq, humild⟩ ht
     have hpt := r3L2Conj_r3EndpointSafeProjectedDuhamelIntegrand hnu t u
+    -- Port note (U05). At Lean 4.34.0-rc2 `rw` type-checks the target at `implicit`
+    -- transparency, where neither `ℝ≥0 = {r : ℝ // 0 ≤ r}` nor `t ∈ Icc 0 T` unfolds, so
+    -- `rw [r3L2Conj_r3StokesH3Evolution]` can no longer abstract the pattern out of the
+    -- upstream-spelled initial term `r3StokesH3Evolution hnu.le ⟨t, ht.1⟩ u0`.  The same
+    -- lemma applied in term mode at that explicit time needs no pattern match.
+    have hconj : r3L2Conj (r3StokesH3Evolution hnu.le ⟨t, ht.1⟩ u0) =
+        r3StokesH3Evolution hnu.le ⟨t, ht.1⟩ u0 :=
+      (r3L2Conj_r3StokesH3Evolution hnu.le ⟨t, ht.1⟩ u0).trans
+        (congrArg (fun g => r3StokesH3Evolution hnu.le ⟨t, ht.1⟩ g) hu0')
     have heq_v : (fun τ => r3L2Conj (u τ)) t =
         r3StokesH3Evolution hnu.le ⟨t, ht.1⟩ u0 -
           ∫ s in (0 : ℝ)..t,
@@ -73,8 +91,7 @@
         _ = r3StokesH3Evolution hnu.le ⟨t, ht.1⟩ u0 -
               ∫ s in (0 : ℝ)..t,
                 r3L2Conj (r3EndpointSafeProjectedDuhamelIntegrand hnu t u s) := by
-            rw [r3L2Conj_r3StokesH3Evolution, hu0',
-              ← r3L2Conj.intervalIntegral_comp_comm hint_u]
+            rw [hconj, ← r3L2Conj.intervalIntegral_comp_comm hint_u]
         _ = r3StokesH3Evolution hnu.le ⟨t, ht.1⟩ u0 -
               ∫ s in (0 : ℝ)..t,
                 r3EndpointSafeProjectedDuhamelIntegrand hnu t
```

**Hunk 2 (`have hconj`, +9 lines) and hunk 3 (the `rw`, +1/−2) are the whole port.**

Reason. Upstream line 76 is
`rw [r3L2Conj_r3StokesH3Evolution, hu0', ← r3L2Conj.intervalIntegral_comp_comm hint_u]`.
Under 4.34.0-rc2 the first rewrite fails:

```
error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  r3L2Conj ((r3StokesH3Evolution ?hnu ?t) ?g)
in the target expression
  r3L2Conj ((r3StokesH3Evolution ⋯ ⟨t, ⋯⟩) u0) - …
Note: The target expression is not type-correct under the `implicit` transparency level …
Full error:
  Application type mismatch: The argument ht has type t ∈ Icc 0 T
  but is expected to have type 0 ≤ t ∧ t ≤ T in the application ht.left
```

Two semireducible definitions are being abused as definitional equalities in the *upstream
statements* that produce this goal — `ℝ≥0 = { r : ℝ // 0 ≤ r }` (so `⟨t, _⟩ : ℝ≥0`
elaborates to `Subtype.mk`) and `t ∈ Set.Icc 0 T = (0 ≤ t ∧ t ≤ T)` (so `ht.1` elaborates
to `And.left ht`). `kabstract`, which `rw` uses to abstract the pattern, now runs its
type-correctness check at `implicit` transparency, where neither unfolds, so the pattern
is not found. The offending spelling `⟨t, ht.1⟩` comes from
`MNS2.IsMildSolutionOn` (`EndpointSafeTwoSpaceDuhamel.lean:613`) and
`MNS2.r3EndpointSafeProjectedMild_equation_at_time`
(`R3EndpointSafeProjectedDuhamel.lean:171`) — both in the 84 good modules, i.e. in the
goal we are *given*, not in text we may rewrite.

The fix therefore does not touch the spelling at all. `r3L2Conj_r3StokesH3Evolution` is
simply *applied in term mode at that explicit time*, where elaboration runs at default
transparency and `⟨t, ht.1⟩ : ℝ≥0` is perfectly well typed:

```lean
have hconj : r3L2Conj (r3StokesH3Evolution hnu.le ⟨t, ht.1⟩ u0) =
    r3StokesH3Evolution hnu.le ⟨t, ht.1⟩ u0 :=
  (r3L2Conj_r3StokesH3Evolution hnu.le ⟨t, ht.1⟩ u0).trans
    (congrArg (fun g => r3StokesH3Evolution hnu.le ⟨t, ht.1⟩ g) hu0')
```

`hconj` also absorbs the second rewrite of the original list (`hu0' : r3L2Conj u0 = u0`)
via `congrArg`. `rw [hconj, …]` then needs no unification: `hconj`'s left-hand side is a
closed term that occurs syntactically in the goal.

This is strictly better than the probe's proposed `⟨x, h⟩ → NNReal.mk x h` substitution.
That substitution changes the *shape of shared statements*, which is exactly why the
probe's experiment 2 produced two new failures at `EndpointSafeTwoSpacePicard.lean:832`
and `R3ProjectedMomentumDuhamelInfrastructure.lean:779` — both inside the 84 good modules.
Applying it would have forced vendor edits and blown the "confined to the four copies"
constraint. **No `NNReal.mk` substitution is used anywhere in this port.**

### 3.2 `R3QuantitativeLifespan`

```diff
--- vendor/HeliCorgi/Formal/R3QuantitativeLifespan.lean	2026-09-13 00:51:51.451586118 -0400
+++ formalization/FormalPatched/R3QuantitativeLifespan.lean	2026-09-13 01:05:50.137773635 -0400
@@ -1,4 +1,13 @@
-import Formal.R3RealLocalMildSolution
+-- Port of `vendor/HeliCorgi/Formal/R3QuantitativeLifespan.lean` (task U05, step 2).
+-- Verbatim copy of the vendored source except for the hunks recorded in
+-- `research/U05/PORT.md`: the mutual imports of the four ported modules are
+-- redirected to `FormalPatched.*`, and one `rw` that no longer matches at Lean
+-- 4.34.0-rc2 is replaced by a term-mode application of the same lemma.  Lean
+-- namespaces and declaration names are unchanged from upstream.  `vendor/` is
+-- not edited; the other 84 modules of the closure are compiled in place from
+-- `vendor/HeliCorgi` by the `Formal` library in `formalization/lakefile.toml`.
+
+import FormalPatched.R3RealLocalMildSolution
 import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
 
 /-!
```

Import redirect only. This module was never elaborated under 4.34.0-rc2 before (the probe
could not reach it); it compiles with zero source changes and zero warnings.

### 3.3 `EndpointSafeTwoSpaceUniqueness`

```diff
--- vendor/HeliCorgi/Formal/EndpointSafeTwoSpaceUniqueness.lean	2026-09-13 00:51:51.449695155 -0400
+++ formalization/FormalPatched/EndpointSafeTwoSpaceUniqueness.lean	2026-09-13 01:05:50.137864878 -0400
@@ -1,6 +1,15 @@
+-- Port of `vendor/HeliCorgi/Formal/EndpointSafeTwoSpaceUniqueness.lean` (task U05, step 2).
+-- Verbatim copy of the vendored source except for the hunks recorded in
+-- `research/U05/PORT.md`: the mutual imports of the four ported modules are
+-- redirected to `FormalPatched.*`, and one `rw` that no longer matches at Lean
+-- 4.34.0-rc2 is replaced by a term-mode application of the same lemma.  Lean
+-- namespaces and declaration names are unchanged from upstream.  `vendor/` is
+-- not edited; the other 84 modules of the closure are compiled in place from
+-- `vendor/HeliCorgi` by the `Formal` library in `formalization/lakefile.toml`.
+
 import Formal.EndpointSafeTwoSpacePicard
 import Formal.EndpointSafeTwoSpaceRestart
-import Formal.R3RealLocalMildSolution
+import FormalPatched.R3RealLocalMildSolution
 
 /-!
 # Unrestricted uniqueness for the endpoint-safe two-space mild equation
```

Import redirect only — and note that the other two imports stay on `Formal.*`, because
`EndpointSafeTwoSpacePicard` and `EndpointSafeTwoSpaceRestart` are good modules built in
place from `vendor/`. Compiles with zero source changes and zero warnings.

### 3.4 `R3MildContinuation`

```diff
--- vendor/HeliCorgi/Formal/R3MildContinuation.lean	2026-09-13 00:51:51.451243740 -0400
+++ formalization/FormalPatched/R3MildContinuation.lean	2026-09-13 01:05:50.137919982 -0400
@@ -1,6 +1,15 @@
-import Formal.R3QuantitativeLifespan
+-- Port of `vendor/HeliCorgi/Formal/R3MildContinuation.lean` (task U05, step 2).
+-- Verbatim copy of the vendored source except for the hunks recorded in
+-- `research/U05/PORT.md`: the mutual imports of the four ported modules are
+-- redirected to `FormalPatched.*`, and one `rw` that no longer matches at Lean
+-- 4.34.0-rc2 is replaced by a term-mode application of the same lemma.  Lean
+-- namespaces and declaration names are unchanged from upstream.  `vendor/` is
+-- not edited; the other 84 modules of the closure are compiled in place from
+-- `vendor/HeliCorgi` by the `Formal` library in `formalization/lakefile.toml`.
+
+import FormalPatched.R3QuantitativeLifespan
 import Formal.EndpointSafeTwoSpaceConcatenation
-import Formal.EndpointSafeTwoSpaceUniqueness
+import FormalPatched.EndpointSafeTwoSpaceUniqueness
 
 /-!
 # Uniform-step extension and the blow-up dichotomy
```

Import redirects only (`EndpointSafeTwoSpaceConcatenation` stays on `Formal.*`).
Compiles with zero source changes and zero warnings.

### 3.5 Patch size

| file | lines changed vs vendor | of which Lean content |
|---|---:|---|
| `R3RealLocalMildSolution.lean` | +18 / −2 | +9 / −2 (one `have`, one shortened `rw`) |
| `R3QuantitativeLifespan.lean` | +9 / −1 | +0 / −0 (1 import redirect) |
| `EndpointSafeTwoSpaceUniqueness.lean` | +9 / −1 | +0 / −0 (1 import redirect) |
| `R3MildContinuation.lean` | +10 / −2 | +0 / −0 (2 import redirects) |

The 8-line provenance header accounts for +8 of every file's count.
**The patch is confined to the four copies.** No statement in any of the 84 good modules
needed to change, so Step 2 did not have to be abandoned.

---

## 4. Build results

Environment for every command:

```sh
cd .claude/worktrees/010-U05-port
. scripts/lean-env.sh
export LEAN_NUM_THREADS=6
export http_proxy=http://127.0.0.1:9 https_proxy=http://127.0.0.1:9 GIT_TERMINAL_PROMPT=0
```

The dead-proxy variables are the network interlock; no lake command ever tried to fetch.
Lake 5.0.0 has no `-j` flag; parallelism comes from `LEAN_NUM_THREADS`.
All builds run from `verification/`, which is where `../formalization` and the shared
prebuilt Mathlib resolve.

| # | command | wall | result |
|---:|---|---:|---|
| 1 | `lake build NSFormalization.Section4.HeliCorgiPort` (first attempt) | 3 m 31.5 s | **exit 1** — 77 `Formal` oleans built, smoke module failed: `r3HelmholtzPressure` is `noncomputable` |
| 2 | same, after adding `noncomputable` | 6.0 s | exit 0 |
| 3 | `lake build NSFormalization/Formal` (all 84 roots) | 34.8 s | exit 0, **84 oleans** in `formalization/.lake/build/lib/lean/Formal/` |
| 4 | `lake build FormalPatched.R3MildContinuation`, copies with imports redirected only | 5.8 s | **exit 1** — the single probe error, reproduced at `FormalPatched/R3RealLocalMildSolution.lean:76:16` |
| 5 | `lake build FormalPatched.R3RealLocalMildSolution`, after the `hconj` hunk | — | exit 0 |
| 6 | `lake build FormalPatched.R3MildContinuation` | 8.4 s | exit 0 — `R3QuantitativeLifespan` 2.9 s, `EndpointSafeTwoSpaceUniqueness` 3.2 s, `R3MildContinuation` 3.1 s, all first-ever elaborations at this pin, **no further errors** |
| 7 | `lake build FormalPatched.R3MildContinuation NSFormalization.Section4.HeliCorgiPort` after adding provenance headers | 11.6 s | exit 0 |
| 8 | cold rebuild of the port through the CI path (oleans for `Formal/`, `FormalPatched/`, `NSFormalization/Section4/` deleted first) | **2 m 07.4 s**, 306 % CPU, 6.99 GB max RSS | exit 0, 8851 jobs, **0 errors**, 84 + 4 oleans |

Warnings in the cold build: **52 distinct, in 20 modules, all of them in
`../vendor/HeliCorgi/Formal/*.lean`** — exactly the probe's and the review's count.
`FormalPatched/*.lean` and `NSFormalization/Section4/HeliCorgiPort.lean` emit **zero**.

### 4.1 Axiom footprint

`lake env lean` over a scratch file importing `FormalPatched.R3MildContinuation` and the
smoke module:

```
'MNS2.r3EndpointSafeProjected_blowup_dichotomy'                  [propext, Classical.choice, Quot.sound]
'MNS2.r3EndpointSafeProjected_exists_realLocalMildSolution'      [propext, Classical.choice, Quot.sound]
'MNS2.r3EndpointSafeProjectedMildSolution_unique'                [propext, Classical.choice, Quot.sound]
'MNS2.r3EndpointSafeProjected_exists_realMildSolutionOn_mildLifespan' [propext, Classical.choice, Quot.sound]
'MNS2.r3EndpointSafeProjectedMild_navierStokes'                  [propext, Classical.choice, Quot.sound]
'MNS2.r3HelmholtzPressure_gradient'                              [propext, Classical.choice, Quot.sound]
'MNS2.r3EndpointSafeProjected_exists_localMildSolution'          [propext, Classical.choice, Quot.sound]
```

Only the three allowed axioms; no `sorryAx`, no assumed PDE axiom. This says the ported
proofs are complete, not that they certify any manuscript theorem — nothing here is a
registered contract.

### 4.2 Repository validation

| command | wall | result |
|---|---:|---|
| `make check` | 8.4 s | pass — **no checker complaint about the new libraries** |
| `make test` | 0.8 s | pass — `Tests.Thresholds` replayed, standard axioms only |
| `make test-mutations` | 7.7 s | pass — refactor accepted; admission, extra axiom, weakened hypothesis all rejected |

`make check` needed no change, but two of its invariants are worth naming because the new
libraries pass them only by construction:

* `check_formalization_plan.py` and `check_contracts.py` both build one flat module table
  over `verification`, `formalization`, `vendor/NavierStokesAndEuler` **and
  `vendor/HeliCorgi`**, and assert no duplicate module name. Copying the four files as
  `Formal.*` inside `formalization/` would have tripped `Duplicate module`. The
  `FormalPatched.*` rename is what avoids it.
* `check_formalization_plan.py` asserts that every import beginning `Formal.` resolves to
  a file it found. The `FormalPatched` copies import `Formal.EndpointSafeTwoSpacePicard`,
  `Formal.EndpointSafeTwoSpaceRestart`, `Formal.EndpointSafeTwoSpaceConcatenation`,
  `Formal.R3ConvectionConjugationEquivariance` and
  `Formal.R3EndpointSafeProjectedLocalExistence`; all five exist under `vendor/HeliCorgi`.

### 4.3 CI's changed-module job

`experiments/build_changed_lean.py` diffs `--base-ref` against **`HEAD`**, so in a
worktree that is forbidden to commit it reports `none`:

```
$ python3 experiments/build_changed_lean.py --base-ref erenup/integration --dry-run
Changed Lean modules: none
```

(`HEAD` = `9ca0480`, `erenup/integration` = `33ecb407`; the committed difference between
them touches only `PLAN.md` and `logs/AGENT_RUNS.csv`.) The port is entirely in the
working tree. It was therefore exercised through a stand-in that imports the script's own
`targets()` function and issues the same `lake build` from `verification/`, over the union
of the committed diff, the tracked working-tree diff and the untracked additions:

```
Changed Lean modules: FormalPatched.EndpointSafeTwoSpaceUniqueness,
  FormalPatched.R3MildContinuation, FormalPatched.R3QuantitativeLifespan,
  FormalPatched.R3RealLocalMildSolution, NSFormalization.Section4.HeliCorgiPort
```

— five modules, the ones the deliverable requires, and the real build of them is row 8 of
the table above (exit 0). Once the branch is committed the unmodified script will produce
the same list. Note also that `targets()` raises on any path under `vendor/HeliCorgi/`;
our change set contains none, so that guard does not trip.

### 4.4 Shared-package integrity

```
$ git -C /data_8T/ping/blowup_density/verification/.lake/packages/mathlib rev-parse HEAD
85e3a25e006c35636f0e53b0e9296caca2685bc0
$ git -C … status --porcelain | wc -l
0
```

No `lake update` was run; no `lake-manifest.json` was modified.

`vendor/` is untouched:

```
$ git status --porcelain vendor/     # empty
$ git diff --stat HEAD -- vendor/    # empty
```

Working tree at the end of the task:

```
 M collaboration/tasks/U05.md
 M formalization/lakefile.toml
?? formalization/FormalPatched/
?? formalization/NSFormalization/Section4/
?? research/U05/PORT.md
```

No file under `vendor/`, `paper/`, `formalization/blueprint/`,
`verification/Contracts/`, `verification/Tests/` or `verification/Bindings/` was touched,
and no git write command was run.

---

## 5. Gaps and risks

1. **`make snapshot` now fails.** `formalization/lakefile.toml` is one of the 2975 files
   in `logs/FORMALIZATION_SOURCE_MANIFEST.json`, so editing it flips
   `source_hashes_match` to `false` and `check_formalization_plan.py --snapshot --check`
   asserts on `['formalization/lakefile.toml']`. `make check` (no `--snapshot`) is
   unaffected and `CONTRIBUTING.md` states the snapshot identity check "is deliberately
   not a normal proof-PR requirement", but whoever merges this should decide whether to
   re-snapshot. Not done here: the manifest was out of scope for this task.
2. **`warningAsError`.** The 84 vendored modules emit 52 warnings. The new libraries
   deliberately carry no `leanOptions`, and `formalization/` sets none. If anything ever
   imports `Formal.*` or `FormalPatched.*` from `verification`'s `Tests` library, which
   sets `warningAsError = true`, all 52 become errors. The same applies to
   `vendor/NavierStokesAndEuler`'s `Euler`. A binding or contract that wants to cite a
   HeliCorgi theorem must therefore either fix the 52 warnings (6 mechanical classes, 3
   deprecated aliases; ~1–2 h per the probe) or route through a library that does not set
   the flag.
3. **Duplicate declarations if upstream fixes the bug.** `FormalPatched.*` re-declares the
   same `MNS2.*` names as `vendor/HeliCorgi/Formal/{R3RealLocalMildSolution,
   R3QuantitativeLifespan, EndpointSafeTwoSpaceUniqueness, R3MildContinuation}.lean`. Today
   that is harmless: those four are *not* in the `Formal` library's `roots`, and with an
   explicit `roots` list Lake refuses them outright — `lake build
   Formal.R3RealLocalMildSolution` reports `unknown target`, and an `import` of one would
   fail as a bad import. The failure mode is not silent. But the moment HeliCorgi is
   re-vendored with a fix, the four names must be moved back into the `Formal` roots and
   `FormalPatched/` deleted in the same commit, or a module importing both spellings will
   get genuinely duplicated declarations. Keep the two lists adjacent in the lakefile so
   this is visible.
4. **The patch is one hunk, so it is cheap to upstream.** Send `hconj` to HeliCorgi;
   the four copies then disappear. Note the *better* upstream fix is the one the probe
   recommended — spell the shared statements with `NNReal.mk` and `Set.mem_Icc` instead of
   abusing the two definitional equalities — but that is a vendor-wide change (~42 sites,
   10 files) and belongs in a HeliCorgi PR, not here.
5. **CI runtime.** A cold build of the port is **2 m 07 s** at `LEAN_NUM_THREADS=6` with
   Mathlib already cached, ~7 GB peak RSS. That is the cost the `lean-contracts` job pays
   whenever any of the five new modules changes. It is *not* paid on unrelated PRs:
   `build_changed_lean.py` only compiles changed files, and `make test` still touches only
   `Tests.Thresholds` (0.8 s).
6. **Three modules had never been elaborated at this pin before today.** `REPORT.md` flagged
   `R3QuantitativeLifespan`, `EndpointSafeTwoSpaceUniqueness` and `R3MildContinuation` as
   possibly hiding further breakage. They do not: all three compile with zero source
   changes and zero warnings. That risk is now closed.
7. **Nothing here certifies anything.** These are upstream proofs made importable. No
   contract is registered, no binding written, no acceptance test added; the smoke module
   is `example`s only. `IsR3EndpointSafeProjectedMildSolutionOn` lives on the complex
   Bessel-coordinate carrier and HeliCorgi's own scope guards (no Clay statement, pressure
   determined up to harmonic terms, realness not transported to the decoded field) carry
   over verbatim.
