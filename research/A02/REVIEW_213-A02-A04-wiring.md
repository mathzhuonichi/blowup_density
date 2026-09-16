REJECT

## 1. What the lane claims

Reviewed HEAD `488f809af6ce971f6c548d2260549ac919917bc1`, using CLAUDE.md and `.claude/skills/lane-review/SKILL.md`, the requested lessons, brief, HANDOFF P7/P9, specs/comparisons, A01 review, and worker report. Read-only review: no source/record corrections or git mutations. The only new artifacts are this review and `probes/rev213_independent_interval.lean`; the three other rev213 probes were already untracked at entry and were replayed unchanged.

`research/A02/REPORT_213.md:5` claims unconditional A02 maximal existence and restart prerequisites; `:9` explicitly admits the unconditional A04 chain is incomplete. All claimed new theorems exist and are sound on replay. REJECT is against completion of the supplied full brief, not a finding of a false proved theorem. The missing deliverables require proofs, not one-line fixes: `restartBeyond'`, `extendsBeyond'`, `lifespanInfiniteOfLocallyFinite'` are unknown identifiers (reproduction below).

## 2. What is in Lean

Paths below beginning A01/, A02/, A04/ are under `formalization/NSFormalization/Section4/`.

| Claim | Checked declaration and fidelity |
|---|---|
| Exact maximal-existence field | A02/MaximalWiring.lean:14–19 has exactly research/A02/Spec.lean:421–423, instantiated with `exists_maximal_of_localSolution A01.localHorizon' (fun ν a f hν ha hf => (A01.localCarrier ν a f hν ha hf).w)`. No local-existence hypothesis remains. Source theorem A02/Maximal.lean:157. |
| Horizon bound and positive lifespan | A02/MaximalWiring.lean:22 and :28; retain positive viscosity, admissible data/force. Positive horizon is a field of ClassicalSolutionR (A02/SolutionClass.lean:120). |
| Representative beyond a presingular time | A02/MaximalWiring.lean:36; midpoint is positive and strictly below the supremum. Equality of velocity and pressure is literal; no endpoint equality is smuggled in. |
| Admissible restart slice | A02/MaximalWiring.lean:48 and :59, matching Spec.lean:512. Uses `D01.contDiff_slice` (D01/DatumToJets.lean:366), `w.sobolev m`, `w.divergence t ht`, i.e. A02/SolutionClass.lean:122, :128, :133. Lane 209's stronger `sobolev_smooth` is unnecessary for slice membership. Valid on Ico, not Icc. The unused `_hν/_ha/_hf` in the accessor preserve the spec; the stronger representative hypothesis already suffices, so they do not create vacuity. |
| Full force shift | A04/RestartWiring.lean:17 and :37 prove measure domination and all of MemForceR: smoothness, every-order paths, L¹ and L². A02/SolutionClass.lean:100 gives the exact predicate. Lane 160's A04/ForceShift.lean:39 supplies only the L¹ Sobolev norm inequality, not full membership; this lane correctly proves the latter. |
| Actual local restart | A04/RestartWiring.lean:54; all presingular times, original slice, `timeShift t₀ f`, selected positive horizon, no additional analytic premise. It is a shifted local solution, not yet a concatenation. |
| Smooth Sobolev path | A04/RestartWiring.lean:64 obtains the path for the very same selected solution from A01/LocalTheoryBundle.lean:310 and :101, ultimately A01/ManuscriptRegularity.lean:247. |
| Uniform H⁷ local restart | A04/RestartWiring.lean:71 fixes ν, f, t₀, finite K before δ, then quantifies over data; exactly what the report claims. A01/LocalTheoryBundle.lean:342 and A02/Restrict.lean:60 supply it. K≠⊤ protects the underlying `.toReal` conversion (LocalTheoryBundle.lean:357); positive δ prevents empty intervals. |
| Unchanged uniqueness | A02/Maximal.lean:192 matches research/A02/Spec.lean:429; not changed by lane commit, standard axiom audit replayed. |

Paper checked with sed: `paper/sections/02-preliminaries.tex:105–117`, `appendix-a-local-theory.tex:115–157`. Maximal existence/uniqueness agrees with the stated classes; MemForceR is the Section 4 global integrability class, narrower than the preliminary proposition's bare compact-time force regularity. Appendix :147–153 explicitly uses a common duration, bounded force on [0,S+1], and overlap uniqueness. The H⁷ variant is a sufficient route to this continuation conclusion after all-order bounds, but is not the paper's literal H¹ quantitative field.

Non-vacuity: `research/A02/axioms_wiring.lean:14` proves actual maximal existence at ν=1,a=f=0; :17 checks a slice of A04.zeroSol on positive horizon 1. `research/A04/axioms_restart_wiring.lean:14` checks translated zero force and :17 an actual local solution from its slice. All replay. There is no added named unproved hypothesis in the eleven new theorems.

Hygiene: no sorry/admit/axiom/native_decide or maxHeartbeats in either new module. All twelve audits (eleven new theorems plus maximal_unique) give exactly the three required axioms. The requested triple-dot diff is empty because current origin/erenup/integration already contains HEAD; it cannot alone certify the historical lane diff. `git show --format= --name-status HEAD` independently shows exactly seven additions (two modules, five records), no existing module or verification file changed. CI's `experiments/build_changed_lean.py:14` recognizes both formalization paths and `.github/workflows/contracts.yml:81` invokes it; research audit files are not automatic contract tests.

## 3. Gaps and lane 215 interfaces

**Blocking 1 — incomplete full brief.** `research/A02/REPORT_213.md:32` accurately disclaims all three requested unconditional A04 theorems. No single named datum/force input is outstanding: those prerequisites are proved. The old universal Restart and HigherOrderBound still remain inputs at A04/Continuation.lean:197 and :223. Reproduction is the missing-identifiers probe in part 4.

The exact existing definitions (A04/Continuation.lean:101 and :186) are:

```lean
def Restart : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ K : ℝ≥0∞, K ≠ ⊤ →
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (a : SpatialField) (f u : SpaceTimeField) (p : SpaceTimeScalar),
        a ∈ initialClassR → MemForceR f → IsMaximalSolution ν a f u p →
          ∀ t₀ ∈ presingularTimes ν a f,
            sobolevENorm 1 (fun x : Space => u (t₀, x)) ≤ K →
            forceSobolevENormL1 1 (timeShift t₀ f) ≤ K →
              ENNReal.ofReal (t₀ + δ) ≤ maximalLifespanR ν a f

def HigherOrderBound : Prop :=
  ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField),
    0 < ν → a ∈ initialClassR → MemForceR f → MemL1Hm f →
      ∀ S : ℝ, 0 < S → ∀ (u : SpaceTimeField) (p : SpaceTimeScalar),
        SolvesBelow ν a f S u p → squaredHTwoIntegral S u ≠ ⊤ →
          ∀ m : ℕ, ∃ M : ℝ≥0∞, M ≠ ⊤ ∧
            ∀ t ∈ Ico (0 : ℝ) S,
              sobolevENorm (m : ℝ) (fun x : Space => u (t, x)) ≤ M
```

**Correction 2 — distinguish fixed-force uniformity from the old universal H¹ field.** REPORT_213.md:22–25 correctly rejects a direct application to the unchanged Restart. However, dependency on t₀ in the current theorem is not an analytic obstruction for a fixed f. For t₀∈[0,S] and r∈[0,1], r+t₀∈[0,S+1]. A continuous order-6 cylinder force path on this compact interval has a finite sup B; the shifted reference path has norm ≤B. Prove identification of the datum/jet paths under translation, then use ContinuousMap's sup bound. A01/LocalTheoryBundle.lean:187 gives monotonicity in the force bound; :283 rewrites the selected horizon and :324 controls cylinder datum radius. Thus

`δ := uniformHorizon ν (datumRadiusConstant * K.toReal) B > 0`

works for all admissible restart data in the H⁷ ball and all t₀∈[0,S]. The force norm here is the order-6 **cylinder** norm of :263, so a bare physical H⁶ assertion must be bridged to that path/norm, not silently identified. Compact-time smoothness from MemForceR supplies the needed finite bound. This repeats the compact-force logic of appendix :147–150 at the available H⁷ level; it does not prove universal H¹ uniformity over all forces.

A precise proposed local interface, **not a theorem already in this tree**, is:

```lean
RestartFixedForce :=
  ∀ ν, 0 < ν → ∀ f, MemForceR f → ∀ S : ℝ, 0 ≤ S →
    ∀ K : ℝ≥0∞, K ≠ ⊤ → ∃ δ : ℝ, 0 < δ ∧
      ∀ t₀ ∈ Icc (0 : ℝ) S, ∀ a' : SpatialField,
        a' ∈ initialClassR → sobolevENorm 7 a' ≤ K →
          Nonempty (ClassicalSolutionR ν a' (timeShift t₀ f) δ)
```

δ precedes both time and datum; f and the compact-time ceiling S precede δ. LocalCarrier plus the force-sup translation bridge can inhabit this. For the lifespan form, add the proved concatenation/overlap lemma taking a maximal solution and the restart local witness to `ofReal (t₀+δ) ≤ maximalLifespanR ν a f`. It is essential not to call the local interface itself that lifespan theorem.

**Consumer inspection.** A04/Continuation.lean:148–164 always applies restart to the same f; :203–219 fixes ν,a,f,S before choosing a bound and duration; :234 only calls extendsBeyond. So the fixed-force H⁷ re-cut suffices for the final extendsBeyond/lifespanInfinite conclusions: use HigherOrderBound at m=7 instead of m=1. It is conservative for those final continuation conclusions. It is NOT a statement-preserving replacement for `restartBeyond` at :170: that public intermediate theorem chooses δ before *all f and S*, and assumes only H¹ bounds. A new fixed-force/H⁷ intermediate theorem must reorder its quantifiers and change its bound. Preserve the old conditional theorem rather than claiming its stronger conclusion from the weaker input.

**Correction 3 — carrier availability and the actual remaining Grönwall bridge.** A01/GronwallEndpoint.lean:16–26 asks for w, its smooth Sobolev paths, a closed-interval cylinder/ordinary pair, angular invariance, slice agreement INCLUDING T, and ‖u‖≤R. Lane 192's A01/CylinderWiring.lean:36 supplies carrier pairs conditional on a-priori bounds. Lane 211's LocalCarrier at LocalTheoryBundle.lean:31–68 retains these for its selected solution: choose q=6 from hpairs, R=‖u‖, use velocity_eq to transport hslice and c.regularity.sobolev_smooth. Existing probe rev213_bundle.lean, replayed here with zero output, applies `highOrder_bddAbove_all_orders_Ico_full` using exactly this data. Thus the bundle-to-lane-179 bridge already works on its own horizon; it is not missing for that carrier.

What is not established is such a carrier for the *same arbitrary SolvesBelow family* up to S with a bound uniform as shorter horizons approach S. A family of local bounds with R depending on the shorter horizon is insufficient. Do not assume closed-endpoint regularity at a possibly singular S to prove continuation. A more direct route is A01/GronwallInstance.lean:68: transfer smooth Sobolev paths to shorter representatives, convert the finite nonnegative ENNReal squaredHTwoIntegral to a common real integral cap (with finiteness justified), then apply its cap form uniformly on shorter horizons. Convert real norms back using each slice's finite datum and lower from order ≥3 for m=0,1,2. Lane 179 already has H¹ lowering at GronwallEndpoint.lean:57, so 'low-order lowering absent' would overstate the gap; all-order assembly/transport is what remains.

Whole-tree negative-claim audit: executed `grep -rnE` over ALL `formalization/NSFormalization/Section4` in three searches, not just A01/A04: (1) Restart/restartBeyond/extendsBeyond/lifespanInfinite/HorizonLowerBoundH1: 26 matches; (2) timeShift/restart_datum/restart_force/concat/patch: 35; (3) HigherOrderBound/highOrder_bddAbove/hOne_uniform/cylinderPair_of_bounds/LocalCarrier/HasSmoothSobolevPath: 67. Opened the candidate lemmas above. A02/Patch.lean:87 takes same initial datum/force and horizon max; its proof selects the longer zero-origin solution. It does not concatenate shifted solutions. A04/ForceShift.lean:39 is the tail norm bound. ManuscriptHorizonLowerBoundH1 at LocalTheoryBundle.lean:372 is a definition only. No proved instance of the old Restart or HigherOrderBound was found by these searches; the useful existing GronwallInstance and bundle composition are explicitly accounted for, rather than dismissed as absent.

| Lane 215 interface | Available supplier | Remaining proof / requirement |
|---|---|---|
| Restart slice and shifted force membership | MaximalWiring:48/:59; RestartWiring:37 | Done; reuse without new analytic assumptions. |
| RestartFixedForce local witnesses | LocalTheoryBundle:187/:283/:324/:342; RestartWiring:71 | Uniform order-6 referenceForce bound over t₀∈[0,S], then select δ before t₀/data. |
| Lifespan increase at t₀ | Local witnesses; existing uniqueness | Shift/restrict the original solution, identify overlap, glue velocity and gauge-compatible pressure into a classical solution on [0,t₀+δ). A02.patch is not this lemma. |
| Uniform H⁷ bound for SolvesBelow | GronwallInstance:68; GronwallEndpoint:32; bundle regularity | Transport to the same solution; common cap from finite H² integral; finite ENNReal conversion. Local bundle's own full-horizon result already replays. |
| Fixed-force restartBeyond | Continuation:45/:148 | Fix f,S before δ; use H⁷ velocity bound; preserve old universal H¹ theorem as conditional. |
| extendsBeyond / infinite lifespan | Continuation:197/:223 | Consume fixed-force result at m=7; keep their final conclusions unchanged. |

Required fixes: complete the above A04 chain (or explicitly obtain a reduced-scope acceptance from the lead); revise §3/ATTEMPTS to record compact-shift uniformity and the already-available bundle-to-Grönwall composition. A records-only change cannot satisfy the original full brief.

## 4. Commands and results

All Lean commands source scripts/lean-env.sh, export LEAN_NUM_THREADS=6, and execute lake from verification/. Shared dependency symlink was checked; no installer/git mutation was needed. `verification/` was not touched, so the conditional scripts/gates.sh/base-ref contract gates are not required; make check, lake test, and the mutation suite were replayed directly. The shell gates wrapper was not used because its Makefile test target invokes lake from root; the direct `cd verification; lake test` obeys the review constraint. Output below is exact stdout/stderr, capped to first/last 40 lines per command. Exit statuses are recorded separately. Existing legacy warnings / copied-source diagnostics in make check and lake test are not warnings from either new module.

The negative probe changes the actual main slice statement from Ico to Icc, keeps its proof, and fails on the three endpoint-membership uses. This is a substantive interval mutation, not an omitted-argument test. The missing-name probe separately reproduces the incomplete deliverables; the bundle probe is positive interface evidence.

`lake -q --log-level=error build NSFormalization.Section4.A02.MaximalWiring NSFormalization.Section4.A04.RestartWiring` (cwd verification), exit 0, 0 output lines.

```text

```

`lake env lean ../formalization/NSFormalization/Section4/A02/MaximalWiring.lean` (cwd verification), exit 0, 0 output lines.

```text

```

`lake env lean ../formalization/NSFormalization/Section4/A04/RestartWiring.lean` (cwd verification), exit 0, 0 output lines.

```text

```

`lake env lean ../research/A02/axioms_wiring.lean` (cwd verification), exit 0, 11 output lines.

```text
'NSFormalization.Section4.A02.exists_maximal'' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A02.horizon_le_lifespan'' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A02.maximalLifespanR_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A02.IsMaximalSolution.exists_solution_after' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A02.ClassicalSolutionR.restart_datum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A02.restart_datum' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A02.maximal_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`lake env lean ../research/A04/axioms_restart_wiring.lean` (cwd verification), exit 0, 7 output lines.

```text
'NSFormalization.Section4.A04.map_forceTimeMeasure_shift_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A04.restart_force' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A04.local_restart' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A04.localCarrier_hasSmoothSobolevPath' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A04.uniform_local_restart_H7' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`lake env lean ../research/A02/probes/rev213_bundle.lean` (cwd verification), exit 0, 0 output lines.

```text

```

`lake env lean ../research/A02/probes/rev213_independent_interval.lean` (cwd verification), exit 1, 24 output lines.

```text
../research/A02/probes/rev213_independent_interval.lean:9:48: error: Application type mismatch: The argument
  ht
has type
  t ∈ Icc 0 T
but is expected to have type
  t ∈ Ico 0 T
in the application
  D01.contDiff_slice w.velocity_smooth ht
../research/A02/probes/rev213_independent_interval.lean:12:21: error: Application type mismatch: The argument
  ht
has type
  t ∈ Icc 0 T
but is expected to have type
  t ∈ Ico 0 T
in the application
  hG t ht
../research/A02/probes/rev213_independent_interval.lean:13:25: error: Application type mismatch: The argument
  ht
has type
  t ∈ Icc 0 T
but is expected to have type
  t ∈ Ico 0 T
in the application
  w.divergence t ht
```

`lake env lean ../research/A02/probes/rev213_missing.lean` (cwd verification), exit 1, 3 output lines.

```text
../research/A02/probes/rev213_missing.lean:2:7: error(lean.unknownIdentifier): Unknown identifier `NSFormalization.Section4.A04.restartBeyond'`
../research/A02/probes/rev213_missing.lean:3:7: error(lean.unknownIdentifier): Unknown identifier `NSFormalization.Section4.A04.extendsBeyond'`
../research/A02/probes/rev213_missing.lean:4:7: error(lean.unknownIdentifier): Unknown identifier `NSFormalization.Section4.A04.lifespanInfiniteOfLocallyFinite'`
```

`make check` (cwd .), exit 0, 28234 output lines.

```text
python3 experiments/check_formalization_plan.py --check
{
  "task_count": 30,
  "source_counts": {
    "formalization": 531,
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
[middle omitted by reviewer; total 28234 lines]
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
Ran 13 tests in 0.044s

OK
python3 experiments/check_work_queue.py
30 work items: ownership, contract registration and task cards consistent.
```

`lake test` (cwd verification), exit 0, 343 output lines.

```text
⚠ [8778/9196] Replayed NSFormalization.Source.FiniteHilbertBochner
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
⚠ [9875/10301] Replayed NSFormalization.Source.BoundedReferenceFlux
warning: NSFormalization/Source/BoundedReferenceFlux.lean:17:5: Variable name `hU0` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hU0

Note: This linter can be disabled with `set_option linter.unusedVariables false`
⚠ [9876/10301] Replayed NSFormalization.Source.BoundedReferenceComparison
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

[middle omitted by reviewer; total 343 lines]

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

`python3 experiments/test_contract_mutations.py --skip-build` (cwd .), exit 0, 5 output lines.

```text
implementation_refactor: accepted
admitted_proof: rejected as required
extra_axiom: rejected as required
weakened_hypothesis: rejected as required
Mutation suite passed. This is an infrastructure check, not a PDE proof.
```

`git diff --name-only origin/erenup/integration...HEAD` (cwd .), exit 0, 0 output lines.

```text

```

`git show --format= --name-status HEAD` (cwd .), exit 0, 7 output lines.

```text
A	formalization/NSFormalization/Section4/A02/MaximalWiring.lean
A	formalization/NSFormalization/Section4/A04/RestartWiring.lean
A	research/A02/ATTEMPTS_WIRING.md
A	research/A02/REPORT_213.md
A	research/A02/axioms_wiring.lean
A	research/A04/ATTEMPTS_RESTART_WIRING.md
A	research/A04/axioms_restart_wiring.lean
```

`git diff --check` (cwd .), exit 0, 0 output lines.

```text

```

`python3 experiments/build_changed_lean.py --base-ref HEAD^ --dry-run` (cwd .), exit 0, 1 output lines.

```text
Changed Lean modules: NSFormalization.Section4.A02.MaximalWiring, NSFormalization.Section4.A04.RestartWiring
```

`rg -n 'sorry|admit|axiom|native_decide|maxHeartbeats' formalization/NSFormalization/Section4/A02/MaximalWiring.lean formalization/NSFormalization/Section4/A04/RestartWiring.lean`, exit 1 (no matches).

```text
```


---
**Lead note (2026-09-16 11:30Z):** the REJECT asked for the unconditional A04 chain (fixed-force uniform restart, shifted gluing, Grönwall transport). Lanes 215 (#219) and 217 (#220) delivered exactly that after this review started; no change to 213 is required.
