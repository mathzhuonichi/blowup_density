ACCEPT

## 1. What the lane claims

Acceptance is for the explicitly conditional, partial delivery permitted by the satisfiability rule, not completion of the unconditional analytic deliverable. `research/A01/REPORT_202.md:5` and `:73` accurately leave that deliverable open; `research/A01/A3_SPLIT.md:70` does too. No proof correction is required.

Reviewed HEAD `2b6e8ea9fb49541bfb26a85076dec84dda79f349`; local integration ref `518674f5e3e89add890ca964c2c8c6ab85d2da86`. Read CLAUDE.md, lane-review skill, LESSONS first 40 lines, HANDOFF §0/§2 P7, REPORT_200 §3, REVIEW_200 §3, REPORT_202, and ATTEMPTS. Used the already installed, shared dependency environment; did not run an installer or change git state.

Notation below: CB = `formalization/NSFormalization/Section4/A01/CommutatorBound.lean`; FFB = the adjacent `ForcingFamilyBound.lean`; V = `vendor/NavierStokesAndEuler/Euler/`. These abbreviations always refer to files in this checkout.

The paper was opened with `sed -n '7,18p;127,145p' paper/sections/appendix-a-local-theory.tex`: :9 gives the two-term physical tame product bound, :17 the self-product specialization, :132 the signed high-energy estimate, and :139 the regularization/Young passage. The lane provides a cylinder commutator reduction supporting that route, not a proof of those physical statements or of their exact constants.

## 2. What is in Lean

Every theorem claimed in REPORT_202 exists with the reported statement:

| Declaration | Exact content and source |
| --- | --- |
| `cylinderWordGradient` | CB:23: square root of the sum over all `Fin 4` directions and all words of orders ≤q+1, of squared L² derivative norms of V restricted to order (q+1)+1. |
| `cylinderCoordinateCommutator` | CB:29: scalar coefficient times derivative of word block, minus the word of the coefficient–derivative product; coefficient is `velocityComponents 1 0 i`. |
| `cylinderCommutator_eq_sum` | CB:43: for every q, hq, v, V, full commutator equals `∑ i : Fin 4, cylinderCoordinateCommutator hq v V i`, without compatibility. |
| `cylinderCoordinateCommutator_empty` | CB:57: for every q, hq, v, V, i, coordinate residual at `emptyWord (q+1)` equals zero, without compatibility. |
| `cylinderCommutator_empty` | CB:67: corresponding full-family empty word equals zero, without compatibility. |
| `CylinderCoordinateTame` | CB:75: the uniform compatible finite-carrier estimate quoted below. |
| `cylinderCommutator_le` | CB:82: `CylinderCoordinateTame q hq C` and `restrictOperator 1 _ V = v` imply `familyNorm (cylinderCommutator hq v V) ≤ (4*C)*‖restrictOperator 1 (Nat.succ_le_succ hq) v‖*cylinderWordGradient V`. |
| `cylinderCommutatorBound_exists` | CB:96: **assuming** `∃ C : ℝ, CylinderCoordinateTame q hq C`, produces a real family constant uniform in compatible v,V; the witness is `4*C` (CB:103). |
| `cylinderCommutatorBound` | CB:106: `CylinderCoordinateTame q hq C → C ≤ 4*A q → CylinderCommutatorBound q hq`. |
| `forcingFamilyBound_of_cylinder'` | CB:118: q,hq,ν,S,hν,a,F,hF with exactly FFB:186's types, plus `CylinderCoordinateTame q hq (4*A q)`, yield `ForcingFamilyBound hq hν a F hF (E q) (A q)`. |

**Exact decomposition and cancellation.** Opened V`AsymmetricTransport.lean:20` and `:27`, V`TransportL2Time.lean:23` and `:30`, and V`LiftedTransportComponents.lean:13`. Both actual transport maps are sums over the same four coefficient functionals; CB:47 explicitly maps the subtype sum through word evaluation, and CB:51 distributes subtraction. No term is dropped. At κ=1,m=0 the angular transport coefficient is zero, but differentiated words and G still include angular derivatives. Keeping four coordinates is correct. The factor four is the triangle-inequality cost, not a claim of optimality.

The empty-word proof CB:60 unfolds both finite products and invokes V`SobolevProduct.lean:50` (`productHq_value`). Both sides then are literally the same scalar product, so CB:64 is `sub_self`. This is actual cancellation of the two transport forms, not empty indexing or zero-data specialization. CB:70 sums these cancellations.

**Hypothesis audit.** The remaining input, verbatim CB:75–79, is:

```lean
def CylinderCoordinateTame (q : ℕ) (hq : 6 ≤ q) (C : ℝ) : Prop :=
  ∀ (v : SobolevSpace 1 (q+1)) (V : SobolevSpace 1 (2+q)),
    restrictOperator 1 (by omega : q+1 ≤ 2+q) V = v →
    ∀ i : Fin 4, familyNorm (cylinderCoordinateCommutator hq v V i) ≤
      C * ‖restrictOperator 1 (Nat.succ_le_succ hq) v‖ * cylinderWordGradient V
```

It is exactly the desired per-coordinate commutator estimate on compatible finite cylinder elements. It packages, rather than proves, the mixed-product interpolation and finite-element identification. There is no hidden extra additive term, smoothness premise, divergence condition, time condition, or data-dependent constant. The low norm is at order seven and has first power. Both sides scale quadratically. Compatibility is essential to consolidate the usual two tame contributions for self-transport. Each surviving Leibniz term differentiates the coefficient at least once and the transported field at least once; thus the full high gradient G is the appropriate factor without an added zero-order high norm. This is a credible estimate in shape; its precise constant remains uncertified.

All norms here are norms of finite Sobolev/L² elements, with finite sums and a real square root (CB:23, :75); there is no `⊤.toReal` trap. The spatial theorems have no intervals. The forcing wrapper preserves lane 200's time quantifiers; `ForcingFamilyBound` at `MildEnergyPremises.lean:314` includes `0 ≤ T ≤ S`. Degenerate choices of S do not replace its nonempty cases. CB:107's comparison is an honest separate arithmetic requirement; CB:122 folds it into the one fixed-API analytic input.

**Non-vacuity and axioms.** `research/A01/axioms_commutator_bound.lean:10` proves compatibility and the coordinate inequality on zero finite elements, :17 proves the full zero inequality, and :24 checks the signed-pairing counterexample. These compile without the universal tame hypothesis. They are genuine zero instances, but do not prove that the universal input is satisfiable on all nonzero data. All ten declarations at :26–35 audit to exactly `[propext, Classical.choice, Quot.sound]` (line wrapping in Lean's output is immaterial).

**Hygiene/provenance.** CB:40–41 is the sole heartbeat override: commented, local to one declaration, 400000. No prohibited proof tokens in CB or its conformance file. `git show --format= --name-status HEAD` shows one new Lean module, three new records, and only the authorized edit to A3_SPLIT. No verification file was touched. The requested triple-dot diff is empty because this local integration ref already contains the lane commit; that alone would not establish the original change scope, hence the commit audit. Merge #206 (`0271695`) is already an ancestor of HEAD, and FFB has zero diff against integration. The lead's historical pre-#206 warning is resolved in this checkout: no rebase is needed for that issue, and any future conflict must preserve integration's FFB. The module is eligible for changed-module CI discovery (`experiments/build_changed_lean.py:18`); the ordinary registered-contract suite alone does not establish its direct typecheck.

## 3. Gaps and route for lane 205

No unconditional tame constant, complete mixed Leibniz expansion on finite elements, or unconditional forcing theorem is claimed or proved (CB:73, :95, :117; ATTEMPTS_COMMUTATOR_BOUND.md:23–30). The satisfiability exception permits this explicit analytic boundary. Acceptance must not mark A3-M2 closed.

**Whole-tree search.** Ran `grep -rnE 'commutator|Commutator|[Tt]ame|[Ii]nterpol|[Ll]eibniz|[Dd]ensity|[Ss]moothing' formalization/NSFormalization/Section4` (316 matching lines), covering each reported analytic gap. Inspected the closest results: `A03/ScalarTameProduct.lean:254`, `A03/OuterTameProduct.lean:177`, `A03/RealAngularProduct.lean:14`, `A04/HighEnergy.lean:136` and :163, `B01/Spatial.lean:5`, and `A01/OrderTwoCap.lean:195`. These supply physical R³ products, datum density or signed energy bounds, not the missing finite cylinder commutator estimate. “Angular” Fourier normalization in A03 is not an extra periodic cylinder variable. No existing theorem found discharges the reported gap. This is a scoped search conclusion, not a claim that the library lacks smoothing or useful product lemmas.

**Expansion.** V`H6NonlinearProduct.lean:146` (`fieldDerivative_smul`) gives the product rule; V`BaseTransportCommutator.lean:48` (`scalarCommutator_recurrence`) recursively places a derivative on the coefficient. V`ExternalTransportCommutator.lean:18` commutes constant word derivatives with the transported derivative, and :38 sums the scalar commutators. Beware sign: that vendor commutator is derivative-of-product minus transport-of-derivative (:30), the negative of CB:29. The norm is unchanged. These are smooth cylinder identities, not the missing estimate. V`MixedWordProduct.lean:16` is a cylinder mixed-product model but only for total order ≤5. V`SobolevTransportCommutator.lean:70` requires n+6≤s, confirming the top-word mismatch recorded at ATTEMPTS:48.

**Interpolation and limit passage.** V`OrdinaryTameProduct.lean:63` (`coordinateProduct_tame`) controls two differentiated factors from the same ordinary `SmoothL2Field Space`; :83 (`tame_outer_product`) propagates the finite Leibniz factor. V`OrdinaryWordInterpolation.lean:52` (`wordMaximum_product_le`) supplies the low/high interpolation model. All use `Fin 3`, so none can be directly applied to arbitrary angular-dependent CB inputs. ATTEMPTS:38–43 correctly illustrates the obstruction with a spatial bump times a nonconstant smooth periodic angular function; :34–37 correctly rejects lowering the high coefficient norm via a restriction estimate in the wrong direction; :50–55 correctly rejects signed-pairing control of a norm and the cubic low-norm replacement.

For the full cylinder route, establish the smooth mixed-product bound and finite word-family constants first. Existing V`SobolevSmoothApproximation.lean:44`, :49, :81, :101 provides smooth approximants, their restriction identity, convergence in the original norm, and smooth representatives. Approximate V at its top order and define v_n by restriction of V_n; compatibility then holds identically, instead of approximating the two inputs independently. Use V`SobolevRestriction.lean:45` (composition) and :61 (derivative commutation), continuity of the actual bilinear maps in CB:32–38, and continuity of finite family norms/G to pass the smooth estimate to the limit. V`SobolevProductApproximation.lean:34` and :50 provide a useful product-continuity model. The worker's “missing passage” means its assembly for this estimate, not absence of the approximation infrastructure.

**Recommended honest simplification.** It is reasonable to restrict the next analytic input to the ordinary-lift subspace. Define `Inv k z := ∀ θ : AddCircle (1 : ℝ), sobolevTranslation 1 k (0, θ) z = z`, and recut the displayed input to

```lean
∀ (v : SobolevSpace 1 (q+1)) (V : SobolevSpace 1 (2+q)),
  restrictOperator 1 (by omega : q+1 ≤ 2+q) V = v →
  Inv (q+1) v → Inv (2+q) V →
  ∀ i : Fin 4, familyNorm (cylinderCoordinateCommutator hq v V i) ≤
    C * ‖restrictOperator 1 (Nat.succ_le_succ hq) v‖ * cylinderWordGradient V
```

This is a proposed interface, not a new theorem in this review. Selected lane-192 pairs do carry precisely this angular invariance (`A01/LerayBridge.lean:331–343` reproduces their hpairs). However FFB:192 introduces an arbitrary mild competitor, not one of those selected witnesses. To retain lane 200's conclusion unchanged, prove invariance of every such competitor using translation equivariance of the equation with ordinary initial data/force and `A01/MildUniqueness.lean:144` (`quadratic_mild_unique`); handle T=0 directly. Do not use hpairs whose construction already depends on the a-priori bound being proved. At almost every time, FFB:193 supplies restriction compatibility; invariance of V follows from invariance of v, restriction–translation commutation (V`SobolevRestriction.lean:69`), and injectivity of the value map (restriction preserves the value, :31). Thus no independent all-order competitor premise is needed. Supply those facts where FFB:197 currently calls hcomm, then the same forcing calculation accepts the restricted estimate. This requires a new composition lemma, not direct application of the current all-cylinder `CylinderCommutatorBound`. Ordinary approximation must preserve invariance and the exact norm comparisons; angular-word vanishing cannot be assumed for general cylinder data.

**Constants.** Prefer proving `∃ C, CylinderCoordinateTame ... C` (or its invariant version), with C chosen before v,V, rather than asserting C=4*A q. The current A (FFB:26) contains physical tensor and family constants but no demonstrated accounting for cylinder embeddings, mixed derivative splittings and all word multiplicities. For coordinate constant C, the family constant is K=4*C, and recut `A' q := max (A q) (C/4)`; equivalently `max (A q) (K/16)`. The elementary inequality `C ≤ 4*A' q` is the needed arithmetic comparison. Generalize the spatial/composition lemma to A', yielding `ForcingFamilyBound ... (E q) (A' q)`; its consumer is already parameterized by A (`MildEnergyPremises.lean:314`). Merely increasing A does not discharge the analytic premise. CB:88–103 proves the exact factor-four and existential composition already available for this route.

## 4. Commands and results

All Lean shells sourced `. scripts/lean-env.sh` and exported `LEAN_NUM_THREADS=6`. Direct Lake commands ran in verification; root make/gates commands use the repository's verification workspace. No git mutation or existing source/record edit was made. A pre-existing untracked `rev202_sign_mutation.lean` was left untouched.

The new `research/A01/probes/rev202_coordinate_constant.lean:17` changes the main estimate's factor from 4*C to 3*C and retains the whole original proof, including all arguments. Lean rejects it at :29 on the expected equality `... * 4 = ... * 3`. This tests proof sensitivity, not optimality: the zero angular coefficient may allow a separately proved sharper bound. The worker's zero examples were independently rerun in the axioms gate; no additional zero example was needed.

Output excerpts below are verbatim, capped at first/last 40 lines per command. Empty direct output means exactly zero bytes. Copied-source informational findings in make check are pre-existing and outside this module's closure; the ten axiom audits check the actual imported declarations.

**`lake build NSFormalization.Section4.A01.CommutatorBound` — exit 0; 12820 bytes, 219 lines.**

First 40 lines:

```text
⚠ [8927/9499] Replayed NSFormalization.Source.FiniteHilbertBochner
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
⚠ [10092/10249] Replayed Formal.R3LerayFrequencySymbol
warning: ../vendor/HeliCorgi/Formal/R3LerayFrequencySymbol.lean:43:2: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
⚠ [10112/10249] Replayed NSFormalization.Source.RealSobolev
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
⚠ [10153/10249] Replayed Formal.R3LerayComplexFiberSymbol
warning: ../vendor/HeliCorgi/Formal/R3LerayComplexFiberSymbol.lean:42:2: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
ℹ [10168/10249] Replayed NSFormalization.Source.PhysicalBesselSobolev
info: NSFormalization/Source/PhysicalBesselSobolev.lean:134:4: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
⚠ [10173/10249] Replayed NSFormalization.Source.PacketForceExtension
warning: NSFormalization/Source/PacketForceExtension.lean:44:25: `if_pos` has been deprecated: Use `ite_eq_left` instead
⚠ [10176/10249] Replayed NSFormalization.Source.ViscosityPacket
warning: NSFormalization/Source/ViscosityPacket.lean:34:63: This simp argument is unused:
  Function.comp_def

Hint: Omit it from the simp argument list.
  [apply] simp [viscosityVelocity, dilateField, viscosityHomeomorph, Prod.map]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
⚠ [10190/10249] Replayed NSFormalization.Paper3.SobolevDirectionalDerivative
warning: NSFormalization/Paper3/SobolevDirectionalDerivative.lean:103:16: `SchwartzMap.smul_apply` has been deprecated: Use `smul_apply` instead

Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.smul_apply` to `smul_apply x`).
⚠ [10240/10249] Replayed NSFormalization.Section4.A01.AprioriFamily
warning: NSFormalization/Section4/A01/AprioriFamily.lean:148:31: Variable name `ha` is not explicitly referenced.

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

**`lake env lean ../formalization/NSFormalization/Section4/A01/CommutatorBound.lean` — exit 0; 0 bytes, 0 lines.**

(No output.)

**`lake env lean ../research/A01/axioms_commutator_bound.lean` — exit 0; 1172 bytes, 14 lines.**

```text
'NSFormalization.Section4.A01.cylinderWordGradient' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.cylinderCoordinateCommutator' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.cylinderCommutator_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.cylinderCoordinateCommutator_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A01.cylinderCommutator_empty' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.CylinderCoordinateTame' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.cylinderCommutator_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.cylinderCommutatorBound_exists' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.cylinderCommutatorBound' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.forcingFamilyBound_of_cylinder'' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

**`lake env lean ../research/A01/probes/rev202_coordinate_constant.lean` — exit 1; 845 bytes, 19 lines.**

```text
Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
../research/A01/probes/rev202_coordinate_constant.lean:29:20: error: unsolved goals
q : ℕ
hq : 6 ≤ q
C : ℝ
htame : CylinderCoordinateTame q hq C
v : ↥(SobolevSpace 1 (q + 1))
V : ↥(SobolevSpace 1 (2 + q))
hV : (restrictOperator 1 ⋯) V = v
h :
  ∑ x, ‖familyHilbertMap (cylinderCoordinateCommutator hq v V x)‖ ≤
    ∑ i, C * ‖(restrictOperator 1 ⋯) v‖ * cylinderWordGradient V
⊢ C * ‖(restrictOperator 1 ⋯) v‖ * cylinderWordGradient V * 4 =
    C * ‖(restrictOperator 1 ⋯) v‖ * cylinderWordGradient V * 3
```

**`make check` — exit 0; 1159606 bytes, 28234 lines.**

First 40 lines:

```text
python3 experiments/check_formalization_plan.py --check
{
  "task_count": 30,
  "source_counts": {
    "formalization": 520,
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
Ran 13 tests in 0.040s

OK
python3 experiments/check_work_queue.py
30 work items: ownership, contract registration and task cards consistent.
```

**`lake test (verification/)` — exit 0; 21729 bytes, 343 lines.**

First 40 lines:

```text
⚠ [8778/9046] Replayed NSFormalization.Source.FiniteHilbertBochner
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

**`make test` — exit 0; 21755 bytes, 344 lines.**

First 40 lines:

```text
lake -d verification test
⚠ [8778/8820] Replayed NSFormalization.Source.FiniteHilbertBochner
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
⚠ [9875/10298] Replayed NSFormalization.Source.BoundedReferenceFlux
warning: NSFormalization/Source/BoundedReferenceFlux.lean:17:5: Variable name `hU0` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hU0

Note: This linter can be disabled with `set_option linter.unusedVariables false`
⚠ [9876/10298] Replayed NSFormalization.Source.BoundedReferenceComparison
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

**`bash scripts/gates.sh NSFormalization.Section4.A01.CommutatorBound` — exit 0; 1176906 bytes, 28496 lines.**

First 40 lines:

```text
== make check
python3 experiments/check_formalization_plan.py --check
{
  "task_count": 30,
  "source_counts": {
    "formalization": 520,
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

**`python3 experiments/check_contracts.py --base-ref origin/erenup/integration` — exit 0; 1158635 bytes, 28202 lines.**

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

Lake build is silent for this module, but not globally silent: it replays dependency diagnostics and a success banner. Direct module checking is genuinely silent. The extra gates and explicit base-contract check were run even though no verification file was touched. `scripts/gates.sh` masks the make-test pipeline status, so the independent successful `make test` above is the authoritative test result. Its mutation suite reports infrastructure mutations only; the separate coordinate-constant probe supplies the mathematical mutation required here.

`git diff --name-only origin/erenup/integration...HEAD`: exit 0.

(No output.)

`git show --format= --name-status HEAD`: exit 0.

```text
A	formalization/NSFormalization/Section4/A01/CommutatorBound.lean
M	research/A01/A3_SPLIT.md
A	research/A01/ATTEMPTS_COMMUTATOR_BOUND.md
A	research/A01/REPORT_202.md
A	research/A01/axioms_commutator_bound.lean
```

`git diff origin/erenup/integration HEAD -- formalization/NSFormalization/Section4/A01/ForcingFamilyBound.lean`: exit 0.

(No output.)

`git merge-base --is-ancestor 0271695 HEAD`: exit 0.

(No output.)

`git diff --check`: exit 0.

(No output.)

Hygiene search: `rg -n '\b(sorry|admit|axiom|native_decide)\b|maxHeartbeats' formalization/NSFormalization/Section4/A01/CommutatorBound.lean research/A01/axioms_commutator_bound.lean` returned only:

```text
formalization/NSFormalization/Section4/A01/CommutatorBound.lean:41:set_option maxHeartbeats 400000 in
```

Required fixes: none. Lane 205 must supply the analytic proof and any invariant-consumer/constant recut described above before claiming unconditional closure.
