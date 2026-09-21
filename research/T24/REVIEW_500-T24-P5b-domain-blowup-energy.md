ACCEPT-WITH-NOTES

## 1. What the lane claims

The worker claims four P5.3/P5.4 fields: regional agreement, a separate
terminal-time speed blow-up in every prescribed ball, the squared restricted
energy upper bound, and exact restricted dissipation additivity
(`research/T24/REPORT_500.md:5-17`).  It explicitly leaves P5.1/P5.2 and P5.5
assembly/registration to their assigned lanes (`research/T24/REPORT_500.md:37-52`).
That is the approved parallel-lane interface, not a gap.

The mathematical source says exactly this: the proposition prescribes finitely
many disjoint interior balls in a torus or bounded domain and separate regional
limsup blow-up (`paper/revised/sections/03-torus.tex:511-518`); the proof uses
scaled packets supported in the balls (`paper/revised/sections/03-torus.tex:520-526`),
identifies the sum with its component on each ball and states the energy `≤` and
dissipation `=` formulas with constants `M² Σε_j` and `D² Σε_j`
(`paper/revised/sections/03-torus.tex:528-531`).  The article expressly permits
different blow-up sequences in different balls (`paper/revised/sections/03-torus.tex:535`).
The report's citations and mathematical description are therefore accurate.

## 2. What is in Lean

### Exact target statements

The canonical vocabulary is the physical restricted norm
`energyEssSupOmega` (`formalization/NSFormalization/Section3/T24/MultipleOmega.lean:31-37`)
and the restricted full I02 Euclidean gradient norm `energyGradientOmega`
(`formalization/NSFormalization/Section3/T24/MultipleOmega.lean:39-45`).  The
four canonical record fields are at
`formalization/NSFormalization/Section3/T24/MultipleOmega.lean:128-143`.

Each reported theorem exists and has the exact field conclusion:

- `region_agreement` is at
  `formalization/NSFormalization/Section3/T24/MultipleOmegaRegions.lean:40-49`,
  matching the record at `MultipleOmega.lean:129-131`.  The field-shaped probe
  substitutes the assembled-velocity formula and closes by `exact` at
  `research/T24/probes/p5b_closes.lean:33-37`.
- `region_blowup` is at
  `formalization/NSFormalization/Section3/T24/MultipleOmegaRegions.lean:52-70`,
  matching `MultipleOmega.lean:133-135`; its exact probe is
  `research/T24/probes/p5b_closes.lean:39-43`.
- `energy_bound` is at
  `formalization/NSFormalization/Section3/T24/MultipleOmegaRegions.lean:210-226`,
  with the same relation, exponent, `ENNReal.ofReal`, constant, and finite sum as
  `MultipleOmega.lean:136-139`; its exact probe is
  `research/T24/probes/p5b_closes.lean:56-61`.
- `dissipation_bound` is at
  `formalization/NSFormalization/Section3/T24/MultipleOmegaRegions.lean:308-343`,
  with the required equality and exact `D² Σε_j` right side from
  `MultipleOmega.lean:140-143`; its exact probe is
  `research/T24/probes/p5b_closes.lean:63-68`.

The local `assembledVelocity` is definitionally `finiteVelocitySum`
(`MultipleOmegaRegions.lean:28-30`), whose canonical body is the pointwise
finite sum (`formalization/NSFormalization/Section3/T24/Multiple.lean:17-19`).
Thus the assembly lane's `rfl` reconciliation is genuine.

### Hypothesis audit and proof route

The P5.3 inputs are only pairwise disjointness and global component support
(`MultipleOmegaRegions.lean:32-35`), the exact raw velocity pin, positive scale,
time placement, and raw packet blow-up (`MultipleOmegaRegions.lean:52-56`).
They are used to obtain a scaled witness and force that nonzero witness into its
own ball (`MultipleOmegaRegions.lean:57-70`).  The underlying transfer lemmas
have the advertised statements at
`formalization/NSFormalization/Source/PacketScaling.lean:177-184` and
`:276-282`.  This is neither an assumed conclusion nor a periodized argument.

P5.4 takes the existing eight-clause `PacketData`, whose fields are concrete
smoothness, compact support, integrability, least-upper-bound, and dissipation
facts (`formalization/NSFormalization/Section4/I03/Energy.lean:95-118`).  It also
takes the exact P5.1 placement/pin/support facts (`MultipleOmegaRegions.lean:94-102`).
The velocity and full-gradient restriction lemmas are proved from support
inside `Ω` (`MultipleOmegaRegions.lean:142-165`), and the two finite-sum
additivity lemmas are proved at `:167-188` and `:228-255`.  The I03 suppliers
have their advertised statements at `Section4/I03/Energy.lean:211-216`,
`:249-266`, and `:302-309`.  The stronger placement inequality is the actual
`DomainPlacementData.eps_time` field (`Section3/T23/Placement.lean:100-112`) and
is derived inside the component dissipation proof (`MultipleOmegaRegions.lean:281-306`),
not added as a residual.

No target theorem has a conclusion-shaped premise, `⊤.toReal = 0`, or an empty
interval premise.  Although the unit theorems are deliberately more general
than the final record, the final record already supplies `T_pos`, `N_pos`,
positive radii, positive scales, and region containment
(`MultipleOmega.lean:51-79`).  The reviewer non-vacuity probe goes further: it
proves that the open unit box is a bounded box domain, contains the closed
one-region ball, and constructs a real registered packet and domain placement
(`research/T24/probes/rev500_nonvacuity.lean:22-94`).  It then instantiates all
four lane theorems at `N = 1`, `T = 1` (`rev500_nonvacuity.lean:96-116`) and
exhibits an index, time, and point in the ball and unit box (`:118-122`).

### Axioms and hygiene

There are 17 theorem declarations and 17 corresponding `#print axioms` commands
(`research/T24/axioms_p5b.lean:3-19`).  Every declaration, and every concrete
reviewer instance, prints exactly `[propext, Classical.choice, Quot.sound]`.
There is no `sorry`, `admit`, `axiom`, `native_decide`, or `maxHeartbeats` in the
new module or worker probes.  The baseline diff marks
`MultipleOmegaRegions.lean` as added; no pre-existing Lean module was edited.
The only pre-existing formalization files changed are the required JSON audit
and entrypoint metadata, and the module is registered at
`formalization/blueprint/entrypoints.json:35`.

The substantive negative probe changes the dissipation right-hand constant from
`D² Σε_j` to `D² Σε_j + 1` (`research/T24/probes/rev500_wrong_dissipation.lean:44-49`).
It fails with the expected type mismatch, rather than by dropping an argument.

## 3. Gaps and findings

There is no P5.3/P5.4 mathematical gap.  In particular, the lead-approved
P5.1/P5.2 inputs remain explicit hypotheses of their exact upstream types and
are all discharged by the field probe; they are not placeholders and are not a
reason to reject this lane.

The worker makes no "not in the tree" analytical-lemma claim.  The mandated
whole-Section4 search instead confirms that all named I03 suppliers are present:

```text
formalization/NSFormalization/Section4/I03/Energy.lean:61:theorem eLpNorm_spatialGradient_sq_slice {w : VelocityField} {t : ℝ}
formalization/NSFormalization/Section4/I03/Energy.lean:211:theorem eLpNorm_scaled_slice (hP : PacketData U K M D) (x₀ : Space) (hε : 0 < ε)
formalization/NSFormalization/Section4/I03/Energy.lean:232:theorem energyEssSup_scaled_le (hP : PacketData U K M D) (x₀ : Space) (hε : 0 < ε)
formalization/NSFormalization/Section4/I03/Energy.lean:249:theorem scaled_dissipation_integrableOn (hP : PacketData U K M D) (x₀ : Space)
formalization/NSFormalization/Section4/I03/Energy.lean:262:theorem scaled_total_dissipation (hP : PacketData U K M D) (x₀ : Space)
formalization/NSFormalization/Section4/I03/Energy.lean:304:theorem energyGradient_scaled_eq (hP : PacketData U K M D) (x₀ : Space) (hε : 0 < ε)
```

Two non-blocking exact fixes justify `ACCEPT-WITH-NOTES`:

1. Delete the extra blank line at EOF after
   `formalization/NSFormalization/Section3/T24/MultipleOmegaRegions.lean:345`;
   `git diff --check` currently reports line 346.
2. In both lane-status bullets, replace the nonexistent prefix
   `MultipleOmegaRegions.OmegaRegions` with
   `NSFormalization.Section3.T24.OmegaRegions`
   (`research/T24/T24_SPLIT.md:424,428`).

## 4. Commands and results

All Lean commands below used `. scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`, and
ran Lake only from `verification/`.

### Build and direct checks

`lake build NSFormalization.Section3.T24.MultipleOmegaRegions` exited 0.  The
new module itself emitted no warning or information line.  Lake replayed only
pre-existing dependency warnings; exact head/tail excerpt (middle omitted under
the raw-output rule):

```text
⚠ [8778/9175] Replayed NSFormalization.Source.FiniteHilbertBochner
warning: NSFormalization/Source/FiniteHilbertBochner.lean:24:19: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
warning: NSFormalization/Source/FiniteHilbertBochner.lean:23:37: This simp argument is unused:
  PiLp.single_apply

Hint: Omit it from the simp argument list.
  [apply] simp [h]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: NSFormalization/Source/FiniteHilbertBochner.lean:39:23: This simp argument is unused:
```

[middle dependency-warning lines omitted]

```text
Note: This linter can be disabled with `set_option linter.unusedVariables false`
⚠ [10126/10132] Replayed NSFormalization.Source.BoundedViscosityUniqueness
warning: NSFormalization/Source/BoundedViscosityUniqueness.lean:21:28: This simp argument is unused:
  one_smul

Hint: Omit it from the simp argument list.
  [apply] simp only [smul_smul, h₂, smul_add, smul_sub]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
Build completed successfully (10132 jobs).
```

`lake env lean ../formalization/NSFormalization/Section3/T24/MultipleOmegaRegions.lean`:

```text
[0 output; exit 0]
```

`lake env lean ../research/T24/probes/p5b_closes.lean`:

```text
[0 output; exit 0]
```

`lake env lean ../research/T24/axioms_p5b.lean` exited 0 with exact output:

```text
'NSFormalization.Section3.T24.OmegaRegions.region_agreement' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T24.OmegaRegions.region_blowup' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T24.OmegaRegions.disjoint_enorm_sq_sum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T24.OmegaRegions.component_slice_contDiff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T24.OmegaRegions.component_tsupport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T24.OmegaRegions.component_gradient_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T24.OmegaRegions.gradient_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T24.OmegaRegions.component_norm_restrict' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T24.OmegaRegions.component_gradient_restrict' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T24.OmegaRegions.slice_energy_additive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T24.OmegaRegions.component_energy_slice_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T24.OmegaRegions.energy_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T24.OmegaRegions.slice_gradient_additive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T24.OmegaRegions.component_gradient_rate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T24.OmegaRegions.energyGradientOmega_sq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T24.OmegaRegions.component_dissipation_sq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T24.OmegaRegions.dissipation_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Reviewer probes

`lake env lean ../research/T24/probes/rev500_nonvacuity.lean` exited 0:

```text
'Rev500Nonvacuity.concrete_region_agreement' depends on axioms: [propext, Classical.choice, Quot.sound]
'Rev500Nonvacuity.concrete_region_blowup' depends on axioms: [propext, Classical.choice, Quot.sound]
'Rev500Nonvacuity.concrete_energy_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Rev500Nonvacuity.concrete_dissipation_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Rev500Nonvacuity.domains_inhabited' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`lake env lean ../research/T24/probes/rev500_wrong_dissipation.lean` exited 1,
as required, with exact output:

```text
../research/T24/probes/rev500_wrong_dissipation.lean:48:2: error: Type mismatch
  dissipation_bound hd placement
    { extension_smooth := hext, carrier_compact := hK, support := hu, square_int := hsi, zero_initial := hz,
      energy_isLUB := hM, dissipation_int := hdi, dissipation_eq := hD }
    hpt hpc he (fun j => (hp j).left) hΩ
has type
  energyGradientOmega Ω T (assembledVelocity fun j => (component j).velocity) ^ 2 = ENNReal.ofReal (D ^ 2 * ∑ j, ε j)
but is expected to have type
  energyGradientOmega Ω T (finiteVelocitySum fun j => (component j).velocity) ^ 2 =
    ENNReal.ofReal (D ^ 2 * ∑ j, ε j + 1)
```

### Repository gates

`. scripts/lean-env.sh && LEAN_NUM_THREADS=6 make check` exited 0.  Exact
head/tail excerpt (the full make-check log is intentionally not reproduced):

```text
python3 experiments/check_formalization_plan.py --check
Blueprint: 41 proof nodes, 27 article/guide mappings; 2240 source modules; local imports and package paths resolve.
Static packaging checks only; no Lean build or mathematical certification.
```

[middle make-check lines omitted]

```text
python3 experiments/test_contract_policy.py
...........
----------------------------------------------------------------------
Ran 11 tests in 0.003s

OK
```

The fresh article audit command
`python3 experiments/audit_article_axioms.py --build --output-dir <fresh-temp-dir> --workers 2`
exited 0 with exact stdout:

```text
Bindings.CompletedDensity: 8 declarations checked
NSFormalization.Section3.T21.MainAssembly: 33 declarations checked
NavierStokes.ComparatorR3Theorem: 2 declarations checked
Bindings.BoundaryInsertionV2: 4 declarations checked
Bindings.LocalTheoryV2: 1 declarations checked
NSFormalization.Source.PacketBreakdown: 1 declarations checked
Bindings.AffineVariation: 1 declarations checked
Bindings.TorusLocalTheory: 1 declarations checked
NSFormalization.Section3.T24.MultipleAssembly: 1 declarations checked
NSFormalization.Section3.T24.ConservativeAssembly: 1 declarations checked
NSFormalization.Section4.R43.Universal: 1 declarations checked
Bindings.ForceClasses: 1 declarations checked
Bindings.GridObservations: 1 declarations checked
56 declarations; 27 article entries; 0 forbidden-axiom results
```

`git diff --name-status origin/erenup/core...HEAD` exited 0:

```text
A	formalization/NSFormalization/Section3/T24/MultipleOmegaRegions.lean
M	formalization/blueprint/AXIOM_AUDIT.json
M	formalization/blueprint/entrypoints.json
A	research/T24/ATTEMPTS_P5B.md
A	research/T24/REPORT_500.md
M	research/T24/T24_SPLIT.md
A	research/T24/axioms_p5b.lean
A	research/T24/probes/p5b_closes.lean
```

The verification-touch test printed exactly:

```text
verification_touched=no
```

Therefore `scripts/gates.sh` and
`experiments/check_contracts.py --base-ref origin/erenup/core` are not applicable
under the review brief's conditional verification gate.

The forbidden-token/heartbeat search had no output (exit 1: no matches).
`git diff --check origin/erenup/core...HEAD` produced the sole hygiene note:

```text
formalization/NSFormalization/Section3/T24/MultipleOmegaRegions.lean:346: new blank line at EOF.
```
