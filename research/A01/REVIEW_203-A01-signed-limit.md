ACCEPT

## 1. What the lane claims

Reviewed lane commit `f38bced4f531835bc698dd249a7a32ae3be5ae8e`, against the currently available `origin/erenup/integration` at `518674f5e3e89add890ca964c2c8c6ab85d2da86`. Acceptance is for the explicitly conditional reduction, under the brief's permission for one honest analytic residual, not unconditional completion of A01.

`research/A01/REPORT_203.md:5` accurately describes six theorems and one definition. All five literal Lean blocks in the report match the source after whitespace normalization. The two other theorems are correctly described in prose. The report explicitly acknowledges the additional scalar sign and initial normalization at :12 and :137; it does not claim the literal hFB-only goal was achieved.

Paper checked with `sed -n '120,150p' paper/sections/appendix-a-local-theory.tex`: :132–137 is the signed high-order energy inequality, :138 requires solenoidality for pressure cancellation, and :140–144 performs positive square-root regularization and Young absorption. This lane supplies supporting finite-order cylinder lemmas toward that argument, not a whole-space density theorem. Also checked `paper/sections/04-whole-space.tex:100` and :117–121 for the zero-root regularization and ordinary-energy use. There is no fabricated direct paper citation in the new module.

## 2. What is in Lean

Paths abbreviated below: S = `formalization/NSFormalization/Section4/A01/SignedLimit.lean`; P = same directory `MildEnergyPremises.lean`; R = `RootComparison.lean`; E = `MildEnergyEnvelope.lean`; F = `ForcingFamilyBound.lean`. Vendor paths below are relative to `vendor/NavierStokesAndEuler/`.

**Strong convergence and its exact scope.** S:17 proves norm-square integral convergence in `TimeLp`; S:26 transports strong convergence through a continuous linear map and explicitly reconciles a.e. representatives at :33–40. S:45 is exactly:

```lean
theorem maximal_word_square_integral_limit {q m : ℕ} {T : ℝ} (hT : 0 ≤ T)
    (hm : m ≤ 2+q) (w : Fin m → Fin 4)
    (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q+1)))
    (U : TimeLp T (SobolevSpace 1 (2+q)))
    (hU : Filter.Tendsto (fun n => pathLp T hT (maximalApproximation 1 q T n u))
      Filter.atTop (𝓝 U)) :
    Filter.Tendsto (fun n => ∫ s,
      ‖word 1 (extendPath T hT (maximalApproximation 1 q T n u) s) hm w‖^2
        ∂timeMeasure T) Filter.atTop
      (𝓝 (∫ s, ‖word 1 (U s) hm w‖^2 ∂timeMeasure T))
```

The hypothesis matches `energy_maximal_limit` (P:137). The bounded word map used at S:55–58 is the genuine `Euler/MildTopWord.lean:46` boundedWordBlock and :51 boundedWordBlock_value. It includes all words through q+2, hence the derivative of every energy word through q+1. **It is not literally a theorem whose RHS is `∫ (energyGradientNorm U s)^2`.** That norm is the square root of the finite double sum in P:304–308, using the reindexed representative. Finite summation, derivative-word identification, and a.e. reindexing still have to assemble that full dissipation; restriction to subintervals and the varying inverse-root weight are also absent from S:45. The report correctly limits the claim at REPORT_203:73–77. Its proof supplies the bounded-map strong convergence needed to extend the result, not just weak convergence.

**Signed absorption.** S:73–91 proves
`(r*z-ν*g^2)/sqrt(r^2+ε^2) ≤ k^2/(4*ν)*r+b`
under `ν>0`, `r≥0`, `b≥0`, `ε>0`, and `r*z≤k*r*g+b*r`. The completed square at :77 gives Young's exact coefficient; :82 proves the denominator positive, :83 establishes `r≤sqrt(r²+ε²)`, and :86 makes multiplication monotone. No division by the possibly zero r occurs. This is the same algebra as `MildGronwall.lean:105` (and R:94), although S reproves it directly rather than calling lane 196's theorem. Substituting `k=A*(16*low)` yields precisely `A²/(4ν)*256*low²`.

**Assembly.** S:121 concludes the imported, unchanged `CylinderSignedRootLimit hq hν a ha F hF E A` (R:127), conditional on `hb`, `hFB`, and `hpass`. The report's statement is exact. P:314 confirms hFB has no ha parameter. S:144 obtains both integrability and the signed estimate, :147 applies integral monotonicity on the correct `[0,t]` restriction, :152 absorbs, and :156–163 sends ε down to zero. The redundant incoming tame-bound binder at :130 is harmless: the proof obtains the identical bound from its stronger universally quantified hFB at :148. The analytic assumption is actually used.

S:166 concludes the imported `FiniteMildEnergy`, retaining `hE : mildNormConstant q ≤ E`. Its :177 proves `hb` from `mildNormConstant_nonneg` and norm nonnegativity. In particular E≥0 suffices. Lane 200 defines `E q := mildNormConstant q` at F:22 and proves `E_nonneg` at :28. The reviewer reran `probes/rev203_constants.lean:8` and :19: the root theorem specializes with `mul_nonneg (E_nonneg q) (norm_nonneg _)`, and the finite-energy theorem with `le_rfl`. Thus no extra sign obligation remains for the intended constants. The b=-1 zero-root counterexample in `axioms_signed_limit.lean:116` justifies the scalar restriction, but is not a PDE counterexample to an unrestricted root theorem. The initial normalization is independently visible at R:169–173; hFB loses all dependence on E when F=0.

**Exact remaining named input (S:98–117).**

```lean
def CylinderSignedEnergyPassage {q : ℕ} (hq : 6 ≤ q) {ν S : ℝ} (hν : 0 < ν)
    (a : SmoothL2Field Space) (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n) : Prop :=
  let _solenoidal := ha
  ∀ (T : ℝ) (hT : 0 ≤ T) (hTS : T ≤ S)
    (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q+1))),
    (∀ t, u t = quadraticDuhamel 1 ν hν hT hTS
      (coefficients 1 hq (sobolevPath F hF q))
      (ordinarySobolev (q+1) a.toLp a.translation_contDiff) u t) →
    ∀ U : TimeLp T (SobolevSpace 1 (2+q)),
      Filter.Tendsto (fun n => pathLp T hT (maximalApproximation 1 q T n u))
        Filter.atTop (𝓝 U) →
    ∀ ε : ℝ, 0 < ε →
      let r := extendPath T hT (energyRootPath u)
      let H := fun s => (r s * cylinderEnergyForcing hq hT hTS F hF u U s -
        ν * (energyGradientNorm U s)^2) / Real.sqrt ((r s)^2+ε^2)
      ∀ t ∈ Icc (0 : ℝ) T,
        IntervalIntegrable H volume 0 t ∧
        Real.sqrt ((r t)^2+ε^2) ≤ Real.sqrt ((r 0)^2+ε^2) + ∫ s in (0 : ℝ)..t, H s
```

This is an unabsorbed signed regularized integral inequality for the actual mild competitor and the SAME strong maximal limit. It retains the complete negative `ν*(energyGradientNorm U)^2` term. It explicitly includes `IntervalIntegrable H`; it also asks for every positive ε, not merely an unregularized formal inequality. These are genuine remaining obligations, not hidden comparison or forcing-bound assumptions. E, A, hFB and an all-order constructor do not occur.

`ha` is already a real typed parameter at S:99. The unused `let _solenoidal := ha` at :102 makes that parameter syntactically occur but reduces away; it does not establish a cancellation inside the proposition. This is an honest scope restriction: supplying the interface requires a proof that this datum is solenoidal, and a theorem constructing the premise may use that proof. It is not a false assumption or a vacuity trick, and it need not be replaced by another binder. The proof term itself appropriately does not affect the energy expression. R:129–132 uses the same convention.

**Non-vacuity and hygiene.** `research/A01/axioms_signed_limit.lean:56` proves zero_passage for every competitor and maximal limit with S=1, using mild uniqueness (:65) and uniqueness of the strong limit (:78). The positive-horizon finite-energy example at :106 actually applies the export. This is genuine zero-data satisfiability, not certification for general data. Its scalar nonzero example at :119 also compiles. No ENNReal `.toReal` occurs in S, so there is no infinity-to-zero escape. T≥0 and t∈[0,T] are preserved; degenerate T=0 is allowed but not the only case. There are no forbidden proof tokens or heartbeat overrides in either new Lean file. All 12 audits at axioms_signed_limit:123–134 have exactly `[propext, Classical.choice, Quot.sound]`.

The lane commit adds S and three new records, plus the requested two-line A3_SPLIT addition; it modifies no existing Lean module and no verification file. The requested three-dot diff is now empty because HEAD is already an ancestor of the current integration ref. `git show --name-status HEAD` independently confirms the original lane scope. The brief's stale pre-#205 rebase warning is resolved in the inspected state: `git diff origin/erenup/integration HEAD -- formalization/NSFormalization/Section4/A01/RootComparison.lean` is empty. Integration's RootComparison must remain authoritative in future conflict resolution; no rebase or git mutation was performed here.

## 3. Gaps and concrete route

At this lane's HEAD, the remaining obligation is exactly S:98. It is the expected restriction of the signed regularized-energy fact for solenoidal mild solutions, after cancellations and passage to the strong maximal limit. E:72 supplies the signed level-n derivative identity, not yet the quotient integral estimate. P:289–300 supplies the source/pressure representatives and divergence facts. `Euler/MildMajorantEnergy.lean:95–119` shows the cancellation/regularized-family assembly to reuse. Integrating the derivative of `sqrt(r_n²+ε²)` should give

`R_n(t) ≤ R_n(0) + ∫₀ᵗ (r_n Z_n - ν D_n)/R_n`, where `R_n=sqrt(r_n²+ε²)`.

Here `Z_n` must be the actual regularized forcing norm after transport/pressure rearrangement, and `D_n` the complete gradient-word square sum. Cauchy–Schwarz gives the unabsorbed `r_n Z_n` bound. Lane 200's `cylinderEnergyForcing_ae` (F:146) identifies the LIMIT forcing; it is not a level-n identification. Reuse the vendor `forcingWordPath_equation` invocation at `Euler/MildMajorantEnergy.lean:121` and its `regularized_forcing_path_eq` at :115 for that level.

For the passage, use `regularizedValueFamily_tendsto` (`Euler/RegularizedEnergyFamily.lean:44`) and `weightedMetricPath_tendsto` (`Euler/MetricPathConvergence.lean:60`) for uniform root convergence; positive ε bounds the inverse root by 1/ε. Use `regularizedWeightedForcing_tendsto` (`Euler/RegularizedEnergyFamily.lean:89`) for strong L² forcing convergence. Uniform convergence of `r_n/R_n` and strong forcing convergence give L¹ convergence of the forcing product on finite subintervals. For dissipation, map the strong maximal limit through the finite gradient-word family; strong L² convergence gives L¹ convergence of squared norms. Multiply by the uniformly converging inverse roots and restrict to [0,t]. This also proves the explicit integrability of H. Apply hFB only after this signed limit, then S:73 and ε↓0 as S:121 already does.

Thus **a uniform-in-n tame forcing bound is not the real necessary remaining obstacle on this route**. The missing work was the signed cancellation assembly, weighted square/product passage, and integrability. If one instead absorbs before passing n→∞, a new bound for the actual regularized forcing family is required. `CylinderCommutatorBound` (F:53) would help only after proving the appropriate regularized forcing identification and the exact restriction relation required by that spatial estimate. Merely substituting the level-n approximation into F:186 is invalid: its competitor solves the given nonlinear mild equation, which a heat regularization does not automatically solve. The vendor `Euler/TimeLpSubinterval.lean:74` has no dissipation slot and cannot directly close this by replacing one argument.

The worker reports no unresolved compiler failure (REPORT_203:145). Its five quoted diagnostics at :148–152 are resolved elaboration/tactic errors, not evidence of an impossible product-convergence or integrability theorem. ATTEMPTS_SIGNED_LIMIT:36–43 explicitly identifies the unfinished varying-denominator/subinterval work. I therefore do not invent a reproducing compiler error for that analytic gap.

**Whole-tree check.** Ran `grep -rnE` over ALL `formalization/NSFormalization/Section4` for signed passage/limit, regularized forcing/tame bounds, square_integral, and IntervalIntegrable/sqrt primitives (commands below). Opened the closest hits: P:275 drops dissipation; E:72 stops before passage; F:146 and :186 concern the limiting family; `A04/Regularized.lean:134` requires interior derivatives and continuous coefficients; `A01/HeatGradientTrace.lean:13` is a different differentiable heat-path estimate; `C01/EnergyBounds.lean:180` is a scalar primitive estimate. None supplies S:98 in this checkout. This supports the historical gap, not a universal claim that no composition is possible.

**Current integration update.** Read-only `git show` reveals that the newer integration ref already contains `A01/SignedPassage.lean:547`, theorem `cylinderSignedEnergyPassage`, with exactly this interface and no hFB/commutator premise. Its :183, :260, and :487 provide the regularized signed inequality, forcing-integral convergence, and weighted dissipation passage respectively. These later results are outside this lane's build/review scope, but confirm that the historical lane-204 route no longer needs to be assigned from scratch. Lane 202's newer `A01/CommutatorBound.lean:106` still requires `CylinderCoordinateTame` and a numerical constant comparison; :118 composes it into lane 200's bound. It is not an unconditional commutator proof, nor an automatic uniform regularized bound.

Required fixes: none for the honestly conditional result. Preserve that scope when describing this lane; unconditional hFB-only closure is not a result of SignedLimit.lean alone.

## 4. Commands and results

All Lean shells source `. scripts/lean-env.sh`, export `LEAN_NUM_THREADS=6`, and invoke lake only after `cd verification`. One lake process at a time. Existing package symlink was verified; no installer or git-state change was needed. The three `rev203_{mutation,controls,constants}.lean` probes were present at entry and left unchanged. This review added only `rev203_original_proof_mutation.lean` and this report.

The new probe copies the complete proof of S:73 and changes only the conclusion's coefficient from `k²/(4ν)` to `k²/(8ν)` (probe:7). It fails with the expected remaining false comparison, without dropping any argument. The existing mutation application fails with a type mismatch. `rev203_controls.lean:7` independently proves the mutant false at ν=r=g=ε=1, k=z=2, b=0 (1/√2 > 1/2). Both that control and the intended-constant specialization compile silently.

Read-only checks: `git diff --check` exit 0/no output; `git diff --name-only origin/erenup/integration...HEAD` exit 0/no output; RootComparison two-dot comparison exit 0/no output; forbidden-token/heartbeat `rg` on S and the audit file has no matches (exit 1). Statement normalization check: all five report blocks match. Axiom-output parsing: 12 entries, all exact.

Search commands (both exit 0):

```sh
grep -rnE 'CylinderSignedEnergyPassage|signed.*(limit|passage)|regularized.*(bound|integr)|IntervalIntegrable|sqrt.*primitive' formalization/NSFormalization/Section4
grep -rnE 'regularized.*(forcing|tame)|forcing.*regularized|square_integral|signed.*(passage|limit)|CylinderSignedEnergyPassage' formalization/NSFormalization/Section4
```

Gate outputs follow verbatim, capped at first/last 40 lines per command. Empty output is explicitly marked. Full raw logs are session-local `/tmp/rev203_*.log`; none are pasted in full when over 80 lines. Build warnings originate in dependencies; SignedLimit itself emits none. Standalone make test was run as well as gates.sh, so the script's filtering cannot mask a test failure here.

### `lake build NSFormalization.Section4.A01.SignedLimit`

Exit 0; 219 output lines.

First 40 lines:

```text
⚠ [8927/9675] Replayed NSFormalization.Source.FiniteHilbertBochner
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
⚠ [10092/10250] Replayed Formal.R3LerayFrequencySymbol
warning: ../vendor/HeliCorgi/Formal/R3LerayFrequencySymbol.lean:43:2: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
⚠ [10112/10250] Replayed NSFormalization.Source.RealSobolev
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
```

Last 40 lines:

```text
⚠ [10153/10250] Replayed Formal.R3LerayComplexFiberSymbol
warning: ../vendor/HeliCorgi/Formal/R3LerayComplexFiberSymbol.lean:42:2: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
ℹ [10168/10250] Replayed NSFormalization.Source.PhysicalBesselSobolev
info: NSFormalization/Source/PhysicalBesselSobolev.lean:134:4: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
⚠ [10173/10250] Replayed NSFormalization.Source.PacketForceExtension
warning: NSFormalization/Source/PacketForceExtension.lean:44:25: `if_pos` has been deprecated: Use `ite_eq_left` instead
⚠ [10176/10250] Replayed NSFormalization.Source.ViscosityPacket
warning: NSFormalization/Source/ViscosityPacket.lean:34:63: This simp argument is unused:
  Function.comp_def

Hint: Omit it from the simp argument list.
  [apply] simp [viscosityVelocity, dilateField, viscosityHomeomorph, Prod.map]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
⚠ [10190/10250] Replayed NSFormalization.Paper3.SobolevDirectionalDerivative
warning: NSFormalization/Paper3/SobolevDirectionalDerivative.lean:103:16: `SchwartzMap.smul_apply` has been deprecated: Use `smul_apply` instead

Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.smul_apply` to `smul_apply x`).
⚠ [10240/10250] Replayed NSFormalization.Section4.A01.AprioriFamily
warning: NSFormalization/Section4/A01/AprioriFamily.lean:148:31: Variable name `ha` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _ha

Note: This linter can be disabled with `set_option linter.unusedVariables false`
⚠ [10241/10250] Replayed NSFormalization.Section4.A01.MildGronwall
warning: NSFormalization/Section4/A01/MildGronwall.lean:150:31: Variable name `ha` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _ha

Note: This linter can be disabled with `set_option linter.unusedVariables false`
Build completed successfully (10250 jobs).
```

### `lake env lean ../formalization/NSFormalization/Section4/A01/SignedLimit.lean`

Exit 0; 0 output lines.

(0 output bytes.)

### `lake env lean ../research/A01/axioms_signed_limit.lean`

Exit 0; 22 output lines.

```text
'NSFormalization.Section4.A01.strong_time_square_integral_limit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A01.mapped_time_square_integral_limit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A01.maximal_word_square_integral_limit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A01.signed_quotient_absorption' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.CylinderSignedEnergyPassage' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.cylinderSignedRootLimit_of_forcingBound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A01.finiteMildEnergy_of_forcingBound'' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'_private._stdin.0.NSFormalization.Section4.A01.zero_value' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private._stdin.0.NSFormalization.Section4.A01.zero_sob' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private._stdin.0.NSFormalization.Section4.A01.zero_mild' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private._stdin.0.NSFormalization.Section4.A01.zero_forcing' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private._stdin.0.NSFormalization.Section4.A01.zero_passage' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### `make check`

Exit 0; 28234 output lines.

First 40 lines:

```text
python3 experiments/check_formalization_plan.py --check
{
  "task_count": 30,
  "source_counts": {
    "formalization": 519,
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
```

Last 40 lines:

```text
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
.............
----------------------------------------------------------------------
Ran 13 tests in 0.041s

OK
python3 experiments/check_work_queue.py
30 work items: ownership, contract registration and task cards consistent.
```

### `make test`

Exit 0; 344 output lines.

First 40 lines:

```text
lake -d verification test
⚠ [8778/9447] Replayed NSFormalization.Source.FiniteHilbertBochner
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
⚠ [9876/10573] Replayed NSFormalization.Source.BoundedReferenceFlux
warning: NSFormalization/Source/BoundedReferenceFlux.lean:17:5: Variable name `hU0` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hU0

Note: This linter can be disabled with `set_option linter.unusedVariables false`
⚠ [9877/10573] Replayed NSFormalization.Source.BoundedReferenceComparison
warning: NSFormalization/Source/BoundedReferenceComparison.lean:159:34: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Source/BoundedReferenceComparison.lean:159:76: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
ℹ [10242/10573] Replayed Tests.Thresholds
info: Tests/Thresholds.lean:13:0: Contract BlowupDensity.Tests.checkedThresholds: checked; standard logical axioms only
⚠ [10248/10573] Replayed NSFormalization.Source.RieszPotentialNearField
warning: NSFormalization/Source/RieszPotentialNearField.lean:21:17: Variable name `hR` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hR
```

Last 40 lines:

```text

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
ℹ [10548/10573] Replayed Tests.GradientL6V2
info: Tests/GradientL6V2.lean:22:0: Contract BlowupDensity.Tests.checkedGradientL6V2: checked; standard logical axioms only
ℹ [10553/10573] Replayed Tests.EnergyHighPartialV2
info: Tests/EnergyHighPartialV2.lean:30:0: Contract BlowupDensity.Tests.checkedEnergyHighPartialV2: checked; standard logical axioms only
ℹ [10556/10573] Replayed Tests.DatumLemmasV3
info: Tests/DatumLemmasV3.lean:31:0: Contract BlowupDensity.Tests.checkedDatumLemmasV3: checked; standard logical axioms only
ℹ [10557/10573] Replayed Tests.Correction
info: Tests/Correction.lean:19:0: Contract BlowupDensity.Tests.checkedCorrection: checked; standard logical axioms only
ℹ [10558/10573] Replayed Tests.MaximalPartial
info: Tests/MaximalPartial.lean:16:0: Contract BlowupDensity.Tests.checkedMaximalPartial: checked; standard logical axioms only
ℹ [10559/10573] Replayed Tests.Uniqueness
info: Tests/Uniqueness.lean:16:0: Contract BlowupDensity.Tests.checkedUniqueness: checked; standard logical axioms only
ℹ [10560/10573] Replayed Tests.HomogeneousNorm
info: Tests/HomogeneousNorm.lean:17:0: Contract BlowupDensity.Tests.checkedHomogeneousNorm: checked; standard logical axioms only
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

### `make test-mutations`

Exit 0; 349 output lines.

First 40 lines:

```text
python3 experiments/test_contract_mutations.py
⚠ [8778/9392] Replayed NSFormalization.Source.FiniteHilbertBochner
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
⚠ [9876/10573] Replayed NSFormalization.Source.BoundedReferenceFlux
warning: NSFormalization/Source/BoundedReferenceFlux.lean:17:5: Variable name `hU0` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hU0

Note: This linter can be disabled with `set_option linter.unusedVariables false`
⚠ [9877/10573] Replayed NSFormalization.Source.BoundedReferenceComparison
warning: NSFormalization/Source/BoundedReferenceComparison.lean:159:34: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Source/BoundedReferenceComparison.lean:159:76: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
ℹ [10242/10573] Replayed Tests.Thresholds
info: Tests/Thresholds.lean:13:0: Contract BlowupDensity.Tests.checkedThresholds: checked; standard logical axioms only
⚠ [10248/10573] Replayed NSFormalization.Source.RieszPotentialNearField
warning: NSFormalization/Source/RieszPotentialNearField.lean:21:17: Variable name `hR` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hR
```

Last 40 lines:

```text
Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: NSFormalization/Source/FractionalRealization.lean:104:2: Try this: 
  letI̵

The goal is a proposition, so `let` is preferred over `letI`.
The difference between `let` and `letI` is that `letI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
ℹ [10548/10573] Replayed Tests.GradientL6V2
info: Tests/GradientL6V2.lean:22:0: Contract BlowupDensity.Tests.checkedGradientL6V2: checked; standard logical axioms only
ℹ [10553/10573] Replayed Tests.EnergyHighPartialV2
info: Tests/EnergyHighPartialV2.lean:30:0: Contract BlowupDensity.Tests.checkedEnergyHighPartialV2: checked; standard logical axioms only
ℹ [10556/10573] Replayed Tests.DatumLemmasV3
info: Tests/DatumLemmasV3.lean:31:0: Contract BlowupDensity.Tests.checkedDatumLemmasV3: checked; standard logical axioms only
ℹ [10557/10573] Replayed Tests.Correction
info: Tests/Correction.lean:19:0: Contract BlowupDensity.Tests.checkedCorrection: checked; standard logical axioms only
ℹ [10558/10573] Replayed Tests.MaximalPartial
info: Tests/MaximalPartial.lean:16:0: Contract BlowupDensity.Tests.checkedMaximalPartial: checked; standard logical axioms only
ℹ [10559/10573] Replayed Tests.Uniqueness
info: Tests/Uniqueness.lean:16:0: Contract BlowupDensity.Tests.checkedUniqueness: checked; standard logical axioms only
ℹ [10560/10573] Replayed Tests.HomogeneousNorm
info: Tests/HomogeneousNorm.lean:17:0: Contract BlowupDensity.Tests.checkedHomogeneousNorm: checked; standard logical axioms only
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
implementation_refactor: accepted
admitted_proof: rejected as required
extra_axiom: rejected as required
weakened_hypothesis: rejected as required
Mutation suite passed. This is an infrastructure check, not a PDE proof.
```

### `python3 experiments/check_contracts.py --base-ref origin/erenup/integration`

Exit 0; 28202 output lines.

First 40 lines:

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
      "Contracts.V1.Packet",
      "NSFormalization.Paper1.ScalarEnergy",
      "NSFormalization.Section4.I01.Energy",
      "NSFormalization.Section4.I01.Extension",
      "NSFormalization.Section4.I01.Quiet",
      "NSFormalization.Source.Insertion",
      "NSFormalization.Source.PacketEndpoint",
      "NSFormalization.Source.PacketEnergy",
      "NSFormalization.Source.PacketForceExtension",
      "NSFormalization.Source.PacketPressure",
      "NSFormalization.Source.PacketScaling",
      "NSFormalization.Source.ParabolicScaling",
      "NSFormalization.Source.SelectedPacketEnergy",
      "NSFormalization.Source.ViscosityPacket",
      "NSFormalization.Source.ViscosityScaling",
      "NavierStokes.ActivationBounds",
      "NavierStokes.ActivationCone",
      "NavierStokes.ActivationContinuation",
      "NavierStokes.ActivationHolomorphic",
      "NavierStokes.ActivationStocks",
      "NavierStokes.ActiveAnnulusWeight",
      "NavierStokes.ActualBaseResidual",
      "NavierStokes.ActualBaseVelocityBounds",
      "NavierStokes.ActualCandidateAssembly",
      "NavierStokes.ActualCandidateConstruction",
      "NavierStokes.ActualCarrierGeometry",
      "NavierStokes.ActualCarrierTransport",
      "NavierStokes.ActualCarrierTransportBase",
```

Last 40 lines:

```text
      "NavierStokes.TerminalEdgeFactor",
      "NavierStokes.TerminalHistoryBridge",
      "NavierStokes.TerminalPressure",
      "NavierStokes.TerminalStress",
      "NavierStokes.TimeLocalization",
      "NavierStokes.TorusAverages",
      "NavierStokes.TorusInverse",
      "NavierStokes.TorusMeanRequestRebase",
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
  "base_compatibility_checked": true,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
```

### `bash scripts/gates.sh NSFormalization.Section4.A01.SignedLimit`

Exit 0; 28496 output lines.

First 40 lines:

```text
== make check
python3 experiments/check_formalization_plan.py --check
{
  "task_count": 30,
  "source_counts": {
    "formalization": 519,
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
```

Last 40 lines:

```text
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

### `lake env lean ../research/A01/probes/rev203_original_proof_mutation.lean`

Exit 1; 15 output lines.

```text
../research/A01/probes/rev203_original_proof_mutation.lean:7:57: error: unsolved goals
case calc.step
ν k r g z b ε : ℝ
hν : 0 < ν
hr : 0 ≤ r
hb : 0 ≤ b
hε : 0 < ε
h : r * z ≤ k * r * g + b * r
hsq : 0 ≤ (2 * ν * g - k * r) ^ 2
hden : 0 < 4 * ν
hy : r * z - ν * g ^ 2 ≤ k ^ 2 / (4 * ν) * r ^ 2 + b * r
hs : 0 < √(r ^ 2 + ε ^ 2)
hrs : r ≤ √(r ^ 2 + ε ^ 2)
hk : 0 ≤ k ^ 2 / (4 * ν) * r + b
⊢ (k ^ 2 / (4 * ν) * r + b) * √(r ^ 2 + ε ^ 2) ≤ (k ^ 2 / (8 * ν) * r + b) * √(r ^ 2 + ε ^ 2)
```

### `lake env lean ../research/A01/probes/rev203_mutation.lean`

Exit 1; 6 output lines.

```text
../research/A01/probes/rev203_mutation.lean:10:2: error: Type mismatch
  signed_quotient_absorption hν hr hb hε h
has type
  (r * z - ν * g ^ 2) / √(r ^ 2 + ε ^ 2) ≤ k ^ 2 / (4 * ν) * r + b
but is expected to have type
  (r * z - ν * g ^ 2) / √(r ^ 2 + ε ^ 2) ≤ k ^ 2 / (8 * ν) * r + b
```

### `lake env lean ../research/A01/probes/rev203_controls.lean`

Exit 0; 0 output lines.

(0 output bytes.)

### `lake env lean ../research/A01/probes/rev203_constants.lean`

Exit 0; 0 output lines.

(0 output bytes.)
