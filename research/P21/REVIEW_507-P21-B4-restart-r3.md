ACCEPT

# Independent review of lane 507-P21-B4-restart-r3

## 1. What the lane claims

The lane claims an unconditional whole-space B4 result: a fixed `MemForceR`
force and a finite H¹ datum ball admit one positive restart duration chosen
before both the restart time and smooth datum.  The claimed local statement is
displayed in `research/P21/REPORT_507.md:8-22`; the claimed support-free bridges,
maximal-lifespan argument, regularity bundle, exact target transport, and B5
handoff are summarized at `research/P21/REPORT_507.md:24-57`.

This is the correct scope.  The revised paper itself states maximal smooth local
existence and the finite-H²-integral continuation criterion at
`paper/revised/sections/02-preliminaries.tex:147-156`; it does not display the
stronger H¹-uniform sentence.  The separate research target is recorded at
`research/P21/Targets.lean:25-35`, and the assessment explicitly identifies it
as a smooth-data, fixed-force target rather than rough-H¹ existence at
`research/P21/ASSESSMENT.md:23-55`.

The worker also claims five theorems in `H1BridgesSmooth.lean` and twelve in
`H1Restart.lean`, for 17 exported theorems total.  The corresponding audit list
does contain exactly those 17 declarations at `research/P21/axioms_b4.lean:4-37`.

## 2. What is in Lean

### Statement fidelity and mathematics

- The local implementation statement at
  `formalization/NSFormalization/Section4/A04/H1Restart.lean:261-267` has the
  same quantifier order, positivity assumptions, `Icc 0 S`, H¹ bound, shifted
  force, solution horizon, and regularity conclusion as the registered target
  at `research/P21/Targets.lean:26-35`.  The structure types are intentionally
  distinct; the kernel-checked transport uses the existing solution and
  regularity conversions at `research/P21/probes/b4_closes.lean:17-25`, whose
  field-by-field regularity conversion is at
  `verification/Bindings/LocalTheoryV2.lean:70-79`.

- The duration is genuinely uniform.  `uniform_hOne_lifespan` quantifies `d`
  before `t₀` and `a` at
  `formalization/NSFormalization/Section4/A04/H1Restart.lean:227-234`, and
  `h1RestartR` preserves that order at lines 268-274.  The H¹ assumption is used
  in the initial barrier bound at lines 158-162 and then in the endpoint
  contradiction at lines 232-255; `K ≠ ⊤` is used in the `toReal` comparison.
  No hidden selected-horizon lower bound occurs.

- The support-free bridge is real, not a compact-support hypothesis in disguise.
  `sobolevEnergy_succ_smooth` assumes only a `SmoothL2Field` and derives the
  raised datum from weak derivatives at
  `formalization/NSFormalization/Section4/A04/H1BridgesSmooth.lean:18-35`.
  The exact H¹ and H² identities are at lines 43-80.  The H² conversion uses the
  existing whole-space identity `‖D²z‖₂² = ‖Δz‖₂²`, whose statement and proof
  start at `formalization/NSFormalization/Section4/A05/HessianLaplacian.lean:87-100`.

- The normalization correction κ=1 is correct.  The angular Fourier derivative
  lemma explicitly cancels Mathlib's `2π` factor at
  `formalization/NSFormalization/Source/AngularGradientIdentity.lean:34-55`.
  Consequently the support-free identity is
  `H¹² = L²² + gradientSq` at
  `formalization/NSFormalization/Section4/A04/H1BridgesSmooth.lean:43-50`, and
  `enstrophy_differential_on_Icc'` instantiates B1 with `κ := 1` at
  `formalization/NSFormalization/Section4/A04/H1Restart.lean:39-51`.

- `enstrophy_differential_on_Icc'` has no norm-bridge or analytic-oracle
  hypotheses.  Its complete inputs are the classical solution, `MemForceR`,
  positive viscosity, positive left endpoint, and upper endpoint below the
  horizon at `formalization/NSFormalization/Section4/A04/H1Restart.lean:27-36`.
  Its H² bridge is the exact `L² + 2 gradient + laplacian` identity, and the
  Frobenius gradient equality is proved at
  `formalization/NSFormalization/Section4/A04/H1BridgesSmooth.lean:82-95`.

- The force cap is squared at the correct point:
  `l2Sq ≤ (forceL2CapR f S).toReal ^ 2` is proved at
  `formalization/NSFormalization/Section4/A04/H1Restart.lean:60-72` and is used
  uniformly only on the unit restart window at lines 165-172.

- The endpoint contradiction follows the required route.  The endpoint theorem
  bounds `squaredHTwoIntegral` at
  `formalization/NSFormalization/Section4/A04/H1Restart.lean:190-224`; the
  maximal solution is selected at line 246; and
  `extendsBeyond_of_memForceR'` is applied with endpoint finiteness at lines
  253-258.  The continuation theorem consumed there has exactly the required
  finite `squaredHTwoIntegral` premise at
  `formalization/NSFormalization/Section4/A04/ShiftedExtension.lean:246-253`.

- The full regularity bundle is genuinely constructed at
  `formalization/NSFormalization/Section4/A04/H1Restart.lean:74-81`.
  Its smooth Sobolev path comes from the overlap/uniqueness argument in
  `formalization/NSFormalization/Section4/A04/RestartFixedForce.lean:144-183`,
  while the other three fields are filled by the existing pressure/projected
  adapters.  No named regularity supplier remains in `h1RestartR`.

- `h1RestartAt` has the B5 consumer shape at
  `formalization/NSFormalization/Section4/A04/H1Restart.lean:276-290`: it uses
  `w.restart_datum` and `shiftedLocalExtension` and returns
  `ofReal (t₀ + δ) ≤ maximalLifespanR`.  This matches the input of
  `restartBeyond_of_restartAt` at
  `formalization/NSFormalization/Section4/A04/Continuation.lean:41-62`.

- The statement is non-vacuous.  The probe constructs `MemForceR` for zero
  force, proves zero datum membership, and instantiates `ν=1`, `S=1`, `K=0` at
  `research/P21/probes/b4_closes.lean:27-49`.  Thus neither the time interval nor
  the datum class is being made empty, and no `⊤.toReal = 0` shortcut appears.

### Hygiene and branch isolation

The two new proof modules contain no `sorry`, `admit`, `axiom`,
`native_decide`, or `set_option maxHeartbeats`.  Both are registered as proof
modules at `formalization/blueprint/entrypoints.json:57-63`.  There is no
contract, binding, test, registry, `proof_graph.json`, blueprint-status, or
paper-source change in the lane-only delta; the other blueprint changes are the
generated audit and dependency graph described in the worker report.

The requested source comparisons are empty:

```text
$ git diff --name-only erenup/503-P21-B0-h1-norm-bridges -- formalization/NSFormalization/Section4/A04/H1Bridges.lean formalization/NSFormalization/Section3/T11/H1Bridges.lean
$ git diff --name-only origin/erenup/504-P21-B1-enstrophy-r3 -- formalization/NSFormalization/Section4/A04/EnstrophyInequality.lean
$ git diff --name-only erenup/506-P21-B3-ode-barrier -- formalization/NSFormalization/Section4/A04/EnstrophyBarrier.lean
```

Therefore lane 507 did not modify the B0, B1, or B3 Lean modules.  The remote
503 ref named in the lead note is not present locally, so the available local
tip `erenup/503-P21-B0-h1-norm-bridges` was used; it is commit `3ebf245a` and the
comparison is empty.  The cited paper lines and tree lemmas above all match the
claims made from them.

The required composite-branch command reports the inherited B0/B1/B3 additions
as well as B4 (Git warns that this history has multiple merge bases):

```text
$ git diff --name-only origin/erenup/core...HEAD
formalization/NSFormalization/Section3/T11/H1Bridges.lean
formalization/NSFormalization/Section4/A04/EnstrophyBarrier.lean
formalization/NSFormalization/Section4/A04/EnstrophyInequality.lean
formalization/NSFormalization/Section4/A04/H1Bridges.lean
formalization/NSFormalization/Section4/A04/H1BridgesSmooth.lean
formalization/NSFormalization/Section4/A04/H1Restart.lean
formalization/blueprint/AXIOM_AUDIT.json
formalization/blueprint/DEPENDENCY_GRAPH.md
formalization/blueprint/entrypoints.json
research/P21/ATTEMPTS_B0.md
research/P21/ATTEMPTS_B1.md
research/P21/ATTEMPTS_B3.md
research/P21/ATTEMPTS_B4.md
research/P21/P6_SPLIT.md
research/P21/REPORT_503.md
research/P21/REPORT_504.md
research/P21/REPORT_506.md
research/P21/REPORT_507.md
research/P21/Targets.lean
research/P21/axioms_b0.lean
research/P21/axioms_b1.lean
research/P21/axioms_b3.lean
research/P21/axioms_b4.lean
research/P21/probes/b0_closes.lean
research/P21/probes/b1_closes.lean
research/P21/probes/b3_closes.lean
research/P21/probes/b4_closes.lean
```

The lane-only delta from the final upstream merge (`5d1be985..HEAD`) adds only
the two B4 proof modules and B4 records, plus generated audit/dependency files
and `entrypoints.json`; no pre-existing Lean module appears in it.

## 3. Gaps and negative checks

There is no B4 proof gap or residual hypothesis.  The worker's excluded torus,
rough-H¹, broader-force, and final-registration results are scope boundaries,
not alleged missing lemmas needed by this proof.  As required, the complete
Section4 tree was searched before accepting those statements:

```text
$ grep -RInE 'h1RestartT|h1UniformEndpointR|h1UniformEndpointT' formalization/NSFormalization/Section4
(no output)
$ grep -RIn 'h1RestartR' formalization/NSFormalization/Section4
formalization/NSFormalization/Section4/A04/H1Restart.lean:261:theorem h1RestartR :
formalization/NSFormalization/Section4/A04/H1Restart.lean:283:  obtain ⟨δ, hδ, hr⟩ := h1RestartR ν hν f hf S hS K hK
$ grep -RInE 'HorizonLowerBoundH1|horizon_lower_bound_H1|lower_bound_H1' formalization/NSFormalization/Section4
formalization/NSFormalization/Section4/A01/HorizonUniform.lean:23:def HorizonLowerBoundH1 (horizon : ℝ → SpatialField → SpaceTimeField → ℝ) : Prop :=
```

The last hit is only the explicitly unresolved cross-force `Prop` definition
(`formalization/NSFormalization/Section4/A01/HorizonUniform.lean:21-29`); the
tree has no theorem witnessing it.  This is consistent with, and distinct from,
the fixed-force smooth-data theorem reviewed here.  Final contract registration
is repository metadata rather than a Section4 lemma.

The worker's bound-clearing test is useful but is not the substantive statement
mutation requested for this review.  I therefore widened the main restart-time
interval from `Icc 0 S` to `Icc (-1) S` in
`research/P21/probes/rev507_widened_interval.lean:16-26`.  Reusing the proved
supplier fails for the expected reason—the widened interval no longer supplies
the nonnegative-time guard needed by `restart_force`:

```text
$ cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/P21/probes/rev507_widened_interval.lean
../research/P21/probes/rev507_widened_interval.lean:26:14: error: Application type mismatch: The argument
  ht₀
has type
  t₀ ∈ Icc (-1) S
but is expected to have type
  t₀ ∈ Icc 0 S
in the application
  hr t₀ ht₀
```

Exit status was 1, as required.  This changes a substantive interval in the
main statement and does not merely omit an argument.  The positive non-vacuity
probe cited above exits 0.

## 4. Commands and results

Every Lean command sourced `. scripts/lean-env.sh`, used
`LEAN_NUM_THREADS=6`, and invoked Lake from `verification/`.

1. Main build:

   Exact first and last output lines are below; the intervening output consists
   only of replayed dependency warnings.

   ```text
   $ lake build NSFormalization.Section4.A04.H1Restart
   ⚠ [9809/10507] Replayed NSFormalization.Source.FiniteHilbertBochner
   Build completed successfully (10507 jobs).
   ```

   Exit 0.  The build was not globally silent because Lake replayed pre-existing
   dependency warnings; neither new module emitted a warning.  Direct checks
   were silent:

   ```text
   $ lake env lean ../formalization/NSFormalization/Section4/A04/H1Restart.lean
   (no output; exit 0)
   $ lake env lean ../formalization/NSFormalization/Section4/A04/H1BridgesSmooth.lean
   (no output; exit 0)
   ```

2. Literal target and positive probe:

   ```text
   $ lake env lean -R .. -o ../tmp/research/P21/Targets.olean ../research/P21/Targets.lean
   (no output; exit 0)
   $ LEAN_PATH="../tmp:$LEAN_PATH" lake env lean ../research/P21/probes/b4_closes.lean
   (no output; exit 0)
   ```

3. Axiom audit:

   The exact first two declarations and last two declarations are quoted below;
   the other 13 declaration pairs have the same exact three-axiom set.

   ```text
   $ lake env lean ../research/P21/axioms_b4.lean
   'NSFormalization.Section4.A04.sobolevEnergy_succ_smooth' depends on axioms: [propext, Classical.choice, Quot.sound]
   Contract NSFormalization.Section4.A04.sobolevEnergy_succ_smooth: checked; standard logical axioms only
   'NSFormalization.Section4.A04.sobolevEnergy_zero_smooth' depends on axioms: [propext, Classical.choice, Quot.sound]
   Contract NSFormalization.Section4.A04.sobolevEnergy_zero_smooth: checked; standard logical axioms only
   'NSFormalization.Section4.A04.h1RestartR' depends on axioms: [propext, Classical.choice, Quot.sound]
   Contract NSFormalization.Section4.A04.h1RestartR: checked; standard logical axioms only
   'NSFormalization.Section4.A04.h1RestartAt' depends on axioms: [propext, Classical.choice, Quot.sound]
   Contract NSFormalization.Section4.A04.h1RestartAt: checked; standard logical axioms only
   ```

   Exit 0.  All 17 `#print axioms` results are exactly
   `[propext, Classical.choice, Quot.sound]`.

4. Fresh article axiom audit:

   ```text
   $ python3 experiments/audit_article_axioms.py --build --output-dir tmp/article-audit --workers 2
   NSFormalization.Section3.T17.ArticleScope: 9 declarations checked
   NSFormalization.Section3.T21.MainAssembly: 30 declarations checked
   Bindings.ForceAmplitude: 6 declarations checked
   Bindings.CompletedDensity: 8 declarations checked
   Bindings.MultipleRegionsV2: 5 declarations checked
   Bindings.PeriodicInsertionV2: 2 declarations checked
   Bindings.BoundaryInsertionV2: 2 declarations checked
   NavierStokes.ComparatorR3Theorem: 2 declarations checked
   Bindings.LocalTheoryV2: 1 declarations checked
   NSFormalization.Source.PacketBreakdown: 1 declarations checked
   Bindings.AffineVariation: 1 declarations checked
   NSFormalization.Section3.T24.ConservativeAssembly: 1 declarations checked
   NSFormalization.Section3.T24.ConservativeOmega: 1 declarations checked
   NSFormalization.Section4.R43.Universal: 1 declarations checked
   Bindings.ForceClasses: 1 declarations checked
   Bindings.GridObservations: 1 declarations checked
   72 declarations; 27 article entries; 0 forbidden-axiom results
   ```

   Exit 0.

5. Owner check:

   ```text
   $ make check
   python3 experiments/check_formalization_plan.py --check
   Blueprint: 41 proof nodes, 27 article/guide mappings; 2271 source modules; local imports and package paths resolve.
   Static packaging checks only; no Lean build or mathematical certification.
   python3 experiments/check_contracts.py --summary
   {
     "registered_contracts": 34,
     "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
   }
   python3 experiments/test_contract_policy.py
   ...........
   ----------------------------------------------------------------------
   Ran 11 tests in 0.003s

   OK
   ```

   Exit 0; no stale-source audit rerun was requested by this gate.

6. Contract tests and mutations (run even though lane 507 did not touch
   `verification/`):

   Exact first and last output lines are quoted; the middle is replayed warnings
   and individual contract checks.

   ```text
   $ make test
   lake -d verification test
   ℹ [11027/11027] Replayed Tests.TorusMain
   info: Tests/TorusMain.lean:21:0: Contract BlowupDensity.Tests.checkedTorusMain: checked; standard logical axioms only
   ```

   Exit 0.

   ```text
   $ make test-mutations
   python3 experiments/test_contract_mutations.py
   implementation_refactor: accepted
   admitted_proof: rejected as required
   extra_axiom: rejected as required
   weakened_hypothesis: rejected as required
   Mutation suite passed. This is an infrastructure check, not a PDE proof.
   ```

   Exit 0.

7. Paper/reader gate:

   Exact first and final output lines are quoted; the two intervening `latexmk`
   blocks report that both PDF targets are up-to-date.

   ```text
   $ make paper
   make -C paper readers
   make[1]: Entering directory '/data_8T/ping/blowup_density/.claude/worktrees/507-P21-B4-restart-r3/paper'
   python3 ../experiments/check_reader_documents.py
   Source inventory: 18 works; missing full text: none. Chapter-only coverage is explicitly marked.
   26 numbered article statements and their guide mappings checked.
   27 article results mapped, including the numbered remark; proof declaration kinds and source line numbers verified.
   86 article labels resolved.
   16 bibliography entries resolved; 34 registry declarations found; guide code paths verified.
   Both PDF build logs are clean. Scope: structural checks, not a new proof certification.
   make[1]: Leaving directory '/data_8T/ping/blowup_density/.claude/worktrees/507-P21-B4-restart-r3/paper'
   ```

   Exit 0.

8. Hygiene:

   ```text
   $ rg -n "sorry|admit|axiom|native_decide|set_option maxHeartbeats" formalization/NSFormalization/Section4/A04/H1BridgesSmooth.lean formalization/NSFormalization/Section4/A04/H1Restart.lean research/P21/probes/b4_closes.lean || true
   (no output)
   $ git diff --check origin/erenup/core...HEAD
   (no output; exit 0)
   ```

No fixes are required.
