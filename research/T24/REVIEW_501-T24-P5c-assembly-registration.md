ACCEPT-WITH-NOTES

## 1. What the lane claims

The worker claims that the bounded-domain half of revised Proposition 3.16 is
now assembled from the P5.1--P5.4 components, that the raw canonical existence
statement is proved without an API/solution premise, and that the retained torus
statement and the new bounded-domain statement are registered together as
`T04.multiple_regions_v2` (`research/T24/REPORT_501.md:5-25`).  It also claims
that the bounded-domain record has thirty fields, the V2 statement is the exact
registered-vocabulary version of `SpecOmega.lean`, a concrete unit-box instance
is inhabited, and node `M316_B` plus the article row are Closed
(`research/T24/REPORT_501.md:27-42`).

The target article passage really says: prescribed finitely many disjoint
interior balls, fixed positive viscosity and terminal time, a smooth forced
solution from zero data with finite energy and dissipation, separate limsup
blow-up in every ball, and homogeneous no-slip in the bounded-domain branch
(`paper/revised/sections/03-torus.tex:511-518`).  Its proof uses scaled packets,
the literal finite sums, disjoint supports, the displayed energy/dissipation
sum, and boundary-collar vanishing (`paper/revised/sections/03-torus.tex:520-535`).

## 2. What is in Lean

### Statement fidelity and assembly

- The canonical bounded-domain structure has exactly the claimed thirty fields,
  from `T_pos` through `no_slip`
  (`formalization/NSFormalization/Section3/T24/MultipleOmega.lean:48-147`).
  In particular, it carries an actual zero-data `ClassicalSolutionOmega`, its
  sum pins and force membership (`MultipleOmega.lean:117-127`), separate
  `SpeedUnboundedAtOn` in every ball (`MultipleOmega.lean:128-135`), finite
  ENNReal energy and exact dissipation bounds (`MultipleOmega.lean:136-143`),
  and pointwise no-slip (`MultipleOmega.lean:145-147`).  The blow-up predicate
  has witnesses in every left neighbourhood of `T`, in the prescribed ball,
  above every positive amplitude; it is not a merely unbounded global norm
  (`formalization/NSFormalization/Section3/T24/Multiple.lean:29-35`).

- The raw canonical statement quantifies the packet clauses, then the prescribed
  domain-class witness, `T > 0`, `N > 0`, positive radii, closed-ball containment
  in `Omega`, and pairwise disjointness before returning `Nonempty` of the
  record (`MultipleOmega.lean:149-201`).  Thus `Ioo 0 T` is not forced empty,
  the region family is nonempty, and the energy conclusions use `ENNReal.ofReal`
  bounds rather than a vacuous `top.toReal = 0`.  The registered domain class is
  a genuine open, bounded, nonempty box-or-regular-level class
  (`verification/Contracts/V1/BoundaryInsertion.lean:229-262`), while the
  solution record really contains neighbourhood smoothness on `[0,T)`, zero
  initial data on the domain, divergence, the momentum equation, and no-slip
  (`BoundaryInsertion.lean:305-341`).

- `multipleRegionsOmegaAPI` fills all thirty fields directly
  (`formalization/NSFormalization/Section3/T24/MultipleOmegaAssembly.lean:20-56`).
  The four P5b fields are not accepted as conclusions: `region_agreement` and
  `region_blowup` receive concrete disjointness, support, component pins,
  positive scales, the time bound and packet blow-up, while `energy_bound` and
  `dissipation_bound` receive the concrete packet, placements, pins, interior
  containment and relevant placement equalities (`MultipleOmegaAssembly.lean:48-55`).
  These are exactly the hypotheses exposed by the unit theorems
  (`formalization/NSFormalization/Section3/T24/MultipleOmegaRegions.lean:32-70`,
  `MultipleOmegaRegions.lean:210-226`, and
  `MultipleOmegaRegions.lean:308-343`).  `RegionsOmegaData` contains packet and
  geometry data, not an API or desired solution premise
  (`formalization/NSFormalization/Section3/T24/MultipleOmegaComponents.lean:20-46`).

- `multipleRegionsOmegaStatement_holds` introduces the full raw statement,
  builds `RegionsOmegaData`, maps `hr`, `hQ`, and `hd` directly to radius
  positivity, interior containment, and disjointness, and returns the constructed
  API (`MultipleOmegaAssembly.lean:59-97`).  Some raw packet clauses have
  underscore names because the stronger registered extension clauses already
  supply what this construction uses; they are the pre-existing packet
  vocabulary, not new assumptions or a disguised conclusion.  The proof remains
  load-bearing on disjointness, as the negative check below demonstrates.

- The two local assembled-velocity spellings are definitionally the same
  finite sum (`formalization/NSFormalization/Section3/T24/MultipleOmegaAssembled.lean:52-62`
  and `MultipleOmegaRegions.lean:28-30`).  No dedupe or unit-lane source edit was
  needed, and this is explicitly recorded
  (`research/T24/ATTEMPTS_P5C.md:3-7`).

### V2 contract and registration

- The registered record again has the same thirty named fields
  (`verification/Contracts/V2/MultipleRegions.lean:43-142`).  After the declared
  vocabulary substitutions (`DomainPlacementData P.toPacketAPI`, packet-indexed
  scaled fields, and registered `spatialGradient`), a comment/whitespace-free
  token comparison of that record plus its domain statement against
  `research/T24/SpecOmega.lean:49-165` returned 843 tokens on each side and
  `MATCH=True`.  The norm bridges are whole-function `rfl`, both fieldwise
  conversions cover all fields, and both round trips are `rfl`
  (`verification/Bindings/MultipleRegionsV2.lean:13-18` and
  `MultipleRegionsV2.lean:20-107`).

- `multipleRegionsStatementV2` is literally the conjunction of retained V1 and
  the bounded-domain statement (`verification/Contracts/V2/MultipleRegions.lean:144-162`),
  and the binding proves it from the existing torus theorem and the new domain
  theorem (`verification/Bindings/MultipleRegionsV2.lean:151-169`).  The test
  checks that conjunction and both projections (`verification/Tests/MultipleRegionsV2.lean:7-14`).
  The V1 registry entry remains at `verification/contracts.json:302-310`; the V2
  entry, declaration, and required both-branch scope are at
  `verification/contracts.json:324-332`.

- The concrete probe selects the registered packet at viscosity one, constructs
  the unit-box domain and one radius-`1/4` ball, and builds canonical data
  (`research/T24/probes/multiple_omega_nonvacuity.lean:16-90`).  It then projects
  canonical and registered `region_blowup 0` and `no_slip` from actual
  inhabitants (`multiple_omega_nonvacuity.lean:92-110`).  Its rerun produced no
  output and exit 0.

### Blueprint and hygiene

- `M316_B` is Closed with evidence for the four proof modules and V2 binding,
  and solid dependencies on exactly `M316` and `B314`
  (`formalization/blueprint/proof_graph.json:408-424`).  The schema currently
  indexes `completion_from` on every node, so the retained value is the empty
  list; there is no completion edge, as confirmed by the generated solid edges
  (`formalization/blueprint/DEPENDENCY_GRAPH.md:98-116`).  Proposition 3.16 is
  Closed in `RESULT_MAP.md` (`formalization/blueprint/RESULT_MAP.md:29`), the
  guide names both branches and the V2 theorem
  (`paper/formalization_guide.tex:115-118`), the inventory is 22 Closed / 5
  Partial (`README.md:35-42`), and the proof/test entrypoints include the new
  modules (`formalization/blueprint/entrypoints.json:35-39,79-80`).

- The prohibited-token and `maxHeartbeats` scans over all P5 source, contract,
  binding, test, non-vacuity, and axiom files returned no matches.  The requested
  `git diff --name-only --diff-filter=M origin/erenup/core...HEAD -- '*.lean'`
  returned no modified Lean file (Git did warn that the moving core now gives
  multiple merge bases).  All relevant Lean files are additions on the selected
  comparison base; the authorised changes to registry/blueprint/guide records
  are not existing Lean-module edits.

## 3. Gaps and reviewer checks

There is no mathematical, assembly, contract, registration, or non-vacuity gap.
The worker reports no missing tree lemma (`research/T24/REPORT_501.md:48-52`).
For completeness, the only resolved missing-name diagnostic was searched across
the whole `formalization/NSFormalization/Section4` tree and returned no
`fundamentalCube_compact` or `isCompact_fundamentalCube`; the actual proved
replacement is in `formalization/NSFormalization/Section3/T18/Lifespan.lean:230`.

The required substantive negative mutation is
`research/T24/probes/rev501_drop_regions_disjoint.lean:14-28`: it removes the
pairwise-disjointness premise from the existence statement without changing the
conclusion.  Lean rejects it at line 27 because the constructor is still a
function waiting for exactly the missing `Pairwise ... Disjoint ...` witness:

```text
../research/T24/probes/rev501_drop_regions_disjoint.lean:27:9: error: Application type mismatch: The argument
  BlowupDensity.Bindings.MultipleRegionsV2.multipleRegionsOmega P Ω hΩ T hT N hN regionCenter regionRadius hr hQ
has type
  (Pairwise fun i j =>
      Disjoint (Metric.ball (regionCenter i) (regionRadius i)) (Metric.ball (regionCenter j) (regionRadius j))) →
    BlowupDensity.Contracts.V2.MultipleRegions.MultipleRegionsOmegaAPI P T Ω hΩ regionCenter regionRadius
but is expected to have type
  BlowupDensity.Contracts.V2.MultipleRegions.MultipleRegionsOmegaAPI P T Ω hΩ regionCenter regionRadius
in the application
  Nonempty.intro
    (BlowupDensity.Bindings.MultipleRegionsV2.multipleRegionsOmega P Ω hΩ T hT N hN regionCenter regionRadius hr hQ)
EXIT_CODE=1
```

One hygiene note prevents an unqualified ACCEPT: the worker reports
`git diff --check: PASS` (`research/T24/REPORT_501.md:92-94`), but the mandated
rerun returns exit 2:

```text
warning: origin/erenup/core...HEAD: multiple merge bases, using 6d71344a99e154328f2be0ecf5f7447d2486aa3c
formalization/NSFormalization/Section3/T24/MultipleOmegaRegions.lean:346: new blank line at EOF.
DIFF_CHECK_EXIT=2
```

Exact fix: delete the extra blank line(s) after the final `end` in
`formalization/NSFormalization/Section3/T24/MultipleOmegaRegions.lean:345-347`
so `git diff --check origin/erenup/core...HEAD` exits 0.  No theorem statement or
proof needs changing.

## 4. Commands and results

All Lean commands used `. scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`, and Lake
only from `verification/`.

1. `lake build NSFormalization.Section3.T24.MultipleOmegaAssembly` — exit 0.
   The exact tail was inherited replay warnings only; no warning names the lane
   module:

   ```text
   warning: NSFormalization/Source/BoundedViscosityUniqueness.lean:21:28: This simp argument is unused:
     one_smul

   Hint: Omit it from the simp argument list.
     [apply] simp only [smul_smul, h₂, smul_add, smul_sub]

   Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
   Build completed successfully (10137 jobs).
   EXIT_CODE=0
   ```

2. `lake env lean ../formalization/NSFormalization/Section3/T24/MultipleOmegaAssembly.lean`
   — exactly zero output, exit 0.

3. `lake build Tests.MultipleRegionsV2` — exit 0; exact tail:

   ```text
   info: Tests/MultipleRegionsV2.lean:11:0: Contract BlowupDensity.Tests.checkedMultipleRegionsV2: checked; standard logical axioms only
   Build completed successfully (10801 jobs).
   EXIT_CODE=0
   ```

4. `lake env lean ../research/T24/axioms_p5c.lean` — exit 0.  Every one of the
   twelve outputs is exactly the allowed set (line wrapping preserved):

   ```text
   'NSFormalization.Section3.T24.multipleRegionsOmegaAPI' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T24.multipleRegionsOmegaStatement_holds' depends on axioms: [propext,
    Classical.choice,
    Quot.sound]
   'BlowupDensity.Bindings.MultipleRegionsV2.energyEssSupOmega_eq' depends on axioms: [propext,
    Classical.choice,
    Quot.sound]
   'BlowupDensity.Bindings.MultipleRegionsV2.energyGradientOmega_eq' depends on axioms: [propext,
    Classical.choice,
    Quot.sound]
   'BlowupDensity.Bindings.MultipleRegionsV2.ofContract' depends on axioms: [propext, Classical.choice, Quot.sound]
   'BlowupDensity.Bindings.MultipleRegionsV2.toContract' depends on axioms: [propext, Classical.choice, Quot.sound]
   'BlowupDensity.Bindings.MultipleRegionsV2.to_of' depends on axioms: [propext, Classical.choice, Quot.sound]
   'BlowupDensity.Bindings.MultipleRegionsV2.of_to' depends on axioms: [propext, Classical.choice, Quot.sound]
   'BlowupDensity.Bindings.MultipleRegionsV2.regionsOmegaData' depends on axioms: [propext, Classical.choice, Quot.sound]
   'BlowupDensity.Bindings.MultipleRegionsV2.multipleRegionsOmega' depends on axioms: [propext,
    Classical.choice,
    Quot.sound]
   'BlowupDensity.Bindings.MultipleRegionsV2.multipleRegionsOmegaStatement_holds' depends on axioms: [propext,
    Classical.choice,
    Quot.sound]
   'BlowupDensity.Bindings.MultipleRegionsV2.multipleRegionsStatementV2_holds' depends on axioms: [propext,
    Classical.choice,
    Quot.sound]
   EXIT_CODE=0
   ```

5. `lake env lean ../research/T24/probes/multiple_omega_nonvacuity.lean` —
   exactly zero output, exit 0.  The reviewer mutation output is quoted in part 3.

6. Independent token and field checks:

   ```text
   research_tokens= 843 contract_tokens= 843 MATCH= True
   formalization/NSFormalization/Section3/T24/MultipleOmega.lean 30 T_pos,N_pos,regionRadius_pos,region_interior,regions_disjoint,placement,placement_time,placement_chart,ε,eps_admissible,eps_time,component,component_pin,component_support,component_force_support,assembled_velocity,assembled_velocity_formula,assembled_pressure,assembled_pressure_formula,assembled_force,assembled_force_formula,solution,solution_pin,force_mem,rest,region_agreement,region_blowup,energy_bound,dissipation_bound,no_slip
   verification/Contracts/V2/MultipleRegions.lean 30 T_pos,N_pos,regionRadius_pos,region_interior,regions_disjoint,placement,placement_time,placement_chart,ε,eps_admissible,eps_time,component,component_pin,component_support,component_force_support,assembled_velocity,assembled_velocity_formula,assembled_pressure,assembled_pressure_formula,assembled_force,assembled_force_formula,solution,solution_pin,force_mem,rest,region_agreement,region_blowup,energy_bound,dissipation_bound,no_slip
   ```

7. `make check` — exact complete output, exit 0:

   ```text
   python3 experiments/check_formalization_plan.py --check
   Blueprint: 41 proof nodes, 27 article/guide mappings; 2246 source modules; local imports and package paths resolve.
   Static packaging checks only; no Lean build or mathematical certification.
   python3 experiments/check_contracts.py --summary
   {
     "registered_contracts": 30,
     "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
   }
   python3 experiments/test_contract_policy.py
   ...........
   ----------------------------------------------------------------------
   Ran 11 tests in 0.003s

   OK
   EXIT_CODE=0
   ```

8. `python3 experiments/audit_article_axioms.py --build --output-dir
   tmp/article-audit-review-501 --workers 2` — exact complete output, exit 0:

   ```text
   Bindings.CompletedDensity: 8 declarations checked
   NSFormalization.Section3.T21.MainAssembly: 33 declarations checked
   Bindings.MultipleRegionsV2: 6 declarations checked
   Bindings.BoundaryInsertionV2: 2 declarations checked
   NavierStokes.ComparatorR3Theorem: 2 declarations checked
   NSFormalization.Source.PacketBreakdown: 1 declarations checked
   Bindings.LocalTheoryV2: 1 declarations checked
   Bindings.AffineVariation: 1 declarations checked
   NSFormalization.Section4.R43.Universal: 1 declarations checked
   NSFormalization.Section3.T24.ConservativeAssembly: 1 declarations checked
   Bindings.ForceClasses: 1 declarations checked
   Bindings.GridObservations: 1 declarations checked
   58 declarations; 27 article entries; 0 forbidden-axiom results
   EXIT_CODE=0
   ```

   The independent `report.json` equals the tracked audit byte-for-data after
   JSON parsing: both have 2257 source files, source SHA-256
   `31e7a784e14c64081144cea4b15cf4024f7b15472fbc903e24b693c4a9c64cdb`, 58
   targets, 27 rows, and an empty prohibited-source-token list.

9. `make test` — exit 0.  Exact last lines:

   ```text
   info: Tests/BoundedDomainNorm.lean:33:0: Contract BlowupDensity.Tests.checkedBoundedDomainNormStatement: checked; standard logical axioms only
   info: Tests/PeriodicInsertion.lean:15:0: Contract BlowupDensity.Tests.checkedPeriodicInsertion: checked; standard logical axioms only
   info: Tests/TorusNonDensity.lean:24:0: Contract BlowupDensity.Tests.checkedTorusNonDensity: checked; standard logical axioms only
   info: Tests/TorusMain.lean:21:0: Contract BlowupDensity.Tests.checkedTorusMain: checked; standard logical axioms only
   EXIT_CODE=0
   ```

10. `make test-mutations` — exit 0; exact final output:

    ```text
    implementation_refactor: accepted
    admitted_proof: rejected as required
    extra_axiom: rejected as required
    weakened_hypothesis: rejected as required
    Mutation suite passed. This is an infrastructure check, not a PDE proof.
    EXIT_CODE=0
    ```

11. `make paper` — exit 0.  Both PDFs were already current; the exact checker
    tail was:

    ```text
    python3 ../experiments/check_reader_documents.py
    Source inventory: 18 works; missing full text: none. Chapter-only coverage is explicitly marked.
    26 numbered article statements and their guide mappings checked.
    27 article results mapped, including the numbered remark; proof declaration kinds and source line numbers verified.
    86 article labels resolved.
    16 bibliography entries resolved; 30 registry declarations found; guide code paths verified.
    Both PDF build logs are clean. Scope: structural checks, not a new proof certification.
    make[1]: Leaving directory '/data_8T/ping/blowup_density/.claude/worktrees/501-T24-P5c-assembly-registration/paper'
    EXIT_CODE=0
    ```

12. Hygiene scans returned `PROHIBITED_EXIT=1` and `HEARTBEAT_EXIT=1`, meaning
    `rg` found no prohibited token and no `maxHeartbeats`.  `git diff --check`
    is the sole failing gate, reproduced in part 3.
