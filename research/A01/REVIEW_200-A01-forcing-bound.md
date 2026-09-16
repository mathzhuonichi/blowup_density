ACCEPT-WITH-NOTES

## 1. What the lane claims

Reviewed HEAD `494e1d4d9c9fdbef78405eac5adb866eba56c3d0`; local
`origin/erenup/integration` = `5ca3bea7dfa3fc5124ea42914594555fb484d3aa`.
No fetch, checkout, rebase, commit, or tracked-source edit was performed.
The only reviewer additions are this report and two `rev200_*.lean` probes.

The report explicitly claims a conditional result, not an unconditional
general-data forcing estimate (`research/A01/REPORT_200.md:5`, :23, :135).
That is permitted by the brief's single-named-input exception. Its displayed
constants and theorem statements agree with the checked Lean declarations.

Hereafter FFB means
`formalization/NSFormalization/Section4/A01/ForcingFamilyBound.lean`;
MEP means the neighboring `MildEnergyPremises.lean`; V means
`vendor/NavierStokesAndEuler/Euler/`. All abbreviated citations use these paths.

The relevant paper statements were opened with `sed -n`:
`paper/sections/appendix-a-local-theory.tex:7-18` gives the tame product estimate;
:127-145 gives the signed high-energy inequality and Young absorption.
The paper does not state this precise cylinder forcing-family norm estimate.
The lane proves an intermediate sufficient condition with a stronger low
Sobolev norm, and correctly leaves the analytic commutator bound open.

## 2. What is in Lean

**Declaration fidelity.** All 14 reported declarations exist:

| Declaration | FFB line | Checked content |
|---|---:|---|
| E | 22 | exactly mildNormConstant q |
| A | 26 | exactly mildNormConstant q * (1 + A03.outerTameConst (q+1)) |
| E_nonneg, A_nonneg | 28, 30 | nonnegativity, no analytic sufficiency assertion |
| cylinderCommutator | 35 | transport of word minus word of asymmetric transport |
| source_pressure_cancel | 45 | Leray residual plus gradient projection equals residual |
| CylinderCommutatorBound | 53 | the single universal compatible-carrier inequality quoted below |
| energyRawTime_ae | 63 | force minus asymmetric transport, a.e. |
| energyForcingNorm_ae | 83 | exact source + transport(word) + pressure word family norm |
| sourceTime_add_pressureTime_ae | 114 | exact unprojected residual, a.e. |
| forcing_array_rearrange | 133 | exact array identity with the minus sign |
| cylinderEnergyForcing_ae | 146 | exact force-array plus commutator norm |
| force_word_norm_le | 174 | family norm bounded by E times the original force-path sup norm |
| forcingFamilyBound_of_cylinder | 187 | literal imported ForcingFamilyBound, conditional on hcomm |

**Z identification and cancellation.** MEP:178-188 uses the literal
`weightedForcingTime` and `forcingFamilyTime`. V`WeightedForcingTime.lean:29-49`,
V`RegularizedForcingWord.lean:74-83` (the current definition begins at 74;
the brief's 82-94 overlaps its end and the next convergence theorem), and
V`RegularizedForcingRepresentative.lean:48` were opened.
FFB:92-109 specializes the representative to Unit/full words, unit weights,
and the identity metric, with no unproved multiplicative constant.

The cancellation is the definition
`leray = id - sobolevGradientProjection`
(`formalization/NSFormalization/Source/ForcedCylinderLocal.lean:26`).
The higher projected source is
`Section4/A01/ForcedSourceUpgrade.lean:22-31`; the pressure is precisely its
gradient complement (MEP:55-61). Thus FFB:114-130 reconstructs the raw
residual before taking norms. This uses neither a separate pressure bound nor
an orthogonality assumption on the force.

FFB:146-171 handles the actual U and the identical
`reindexMaximalTime`, including the a.e. representative equality from
`coeFn_compLpL`. FFB:194 invokes
V`SobolevMaximalRegularity.lean:36-42`, so the limit is the genuine maximal
approximation limit, not an arbitrarily chosen higher field.
FFB:174-183 uses `euclideanWordNorm_bounds`
(`Section4/A01/MildGronwall.lean:38`) and the continuous-map sup norm.
Its application at FFB:212-213 is exactly
`E q * ‖sobolevPath F hF (q+1)‖`.

**Composition and the ha discrepancy.** FFB:187-192 is exactly the theorem
printed at REPORT_200:26-31. MEP:314-329 in BOTH this checkout and the inspected
origin ref has binders `hq hν a F hF E A`, with NO `ha`.
The two-dot diff of that entire module is empty. The lead's assertion that
this particular predicate already takes `ha` is not borne out by these refs;
the neighboring `mild_energy_estimate_of_cylinder` does take it (MEP:275-278).
No interface rejection is justified against the actual inspected definition.
A later ref with a changed predicate must be checked again; no such later ref
was fetched during this read-only review.

The proof intentionally does not use `_hu` (FFB:193): the spatial bound plus
maximal-limit compatibility proves a stronger assertion. This is not a
vacuity device. E meets lane 201's stated constraint by definitional equality:
`mildNormConstant q ≤ E q` reduces to reflexivity (FFB:22).
The low restriction in FFB:57 is literally order 7, i.e. the carrier used for
mild order 6; it is not literally an H6 norm.

**Non-vacuity and hygiene.** The zero-data examples use S=1 and ν=1
(`research/A01/axioms_forcing_bound.lean:25-58`), and finite mild uniqueness
forces every competitor to zero; this is not an empty-interval construction.
The spatial zero commutator and zero inequality are separately verified at
:61-71. These are genuine zero instances, but do not establish the globally
quantified CylinderCommutatorBound. The main statements use finite real norms,
not ENNReal.toReal. No hidden infinity-to-zero conversion occurs.

The new module has no sorry/admit/axiom/native_decide tokens. Its three
heartbeat settings are declaration-local, commented, and exactly 400000
(FFB:80-81, :111-112, :142-143). The 18 axiom audits (14 declarations plus
four zero helpers) all print exactly the required three axioms.
Existing imported files have larger historical heartbeat settings, e.g.
A03/ScalarTameProduct.lean:249; this lane did not introduce them.

The requested three-dot diff lists only new Lean modules (including the
inherited lane-199 envelope module), and the authorized research record change.
No verification files were touched. The changed-module selector handles
formalization modules (`experiments/build_changed_lean.py:18-24`).
The two-dot comparison shows this branch lacks integration's
`energyComparison_unique`
(`origin/erenup/integration:formalization/NSFormalization/Section4/A01/MildEnergyEnvelope.lean:123`).
The lead must retain integration's version when reconciling the branch.

## 3. Gaps, analytic assessment, and lane 202 route

The ONE named analytic input, verbatim from FFB:53-60, is:

```lean
def CylinderCommutatorBound (q : ℕ) (hq : 6 ≤ q) : Prop :=
  ∀ (v : SobolevSpace 1 (q+1)) (V : SobolevSpace 1 (2+q)),
    restrictOperator 1 (by omega : q+1 ≤ 2+q) V = v →
    familyNorm (cylinderCommutator hq v V) ≤
      A q * (16 * ‖restrictOperator 1 (Nat.succ_le_succ hq) v‖) *
        Real.sqrt (∑ i : Fin 4, ∑ w : SobolevWord (q+1),
          ‖(derivativeOperator 1 (q+1) i
            (restrictOperator 1 (by omega : (q+1)+1 ≤ 2+q) V)).val w‖^2)
```

This is the compatible self-transport specialization of a Kato–Ponce/Moser
word-commutator bound, with the opposite commutator sign (irrelevant to its
norm). It is a credible standard estimate in SHAPE, not an already verified
standard estimate with this exact numerical constant. Compatibility identifies
the two fields; it is essential when consolidating the two usual tame terms.

There is no apparent missing zero-order additive term: the empty-word
commutator vanishes, and the Leibniz expansion of every other word has a
derivative on the coefficient and on the transported field. Standard
interpolation/tame estimates can bound these products by a low inhomogeneous
norm times the full gradient high norm. The order-7 low norm supplies more
than the embedding regularity needed on the four-dimensional cylinder.
The low norm has the correct first power: both sides are quadratic under
(v,V) ↦ (λv,λV). No divergence-free assumption is needed for a commutator norm
estimate (unlike signed transport cancellation).

Fin 4 is correct: cylinder words include the angle direction and three
spatial directions. `velocityComponents 1 0` has zero angle coefficient
(V`LiftedTransportComponents.lean:13`), but the high word and gradient family
still includes angle derivatives. This is precisely MEP:304-307, not a
mistaken spatial Fin 3 sum. The factor 16 is the inherited normalization;
the physical order-two cap needs its own descent hypotheses
(`Section4/A01/OrderTwoCap.lean:195-207`), which have not been asserted for
arbitrary cylinder fields.

**Exact constant:** `A q = mildNormConstant q * (1 + outerTameConst (q+1))`
is plausible as a candidate but its sufficiency is not established by these
proofs or by the cited R³ tensor estimate. Cylinder embeddings, derivative
splittings, word multiplicities and comparisons must all be accounted for.
I cannot certify the fixed-A proposition as true merely from its standard
shape. The conditional theorem honestly includes this obligation in hcomm;
acceptance here is of that conditional theorem. For an unconditional lane
202 result, first prove an existential finite C(q), or parameterize the
spatial bound by C, then derive an explicit C and prove it ≤16*A q if keeping
this exact API. Do not label the displayed A as a proved Kato–Ponce constant.

**Whole-tree gap search.** Ran `grep -rn -E
'CylinderCommutatorBound|cylinderCommutator|commutator|Commutator'
formalization/NSFormalization/Section4`: only this new module matches.
Also searched the entire Section4 tree for
`tame|Tame|outer_tame_low|MemHmVector|sobolevENorm.*ne_top`.
Opened the closest hits: A03/OuterTameProduct:166-185,
A03/ScalarTameProduct:254-272, A04/HighEnergy:136-180,
A01/MildGronwall:114-126, and A01/OrderTwoCap:195-207.
The latter routes supply tensor or signed pairing bounds and explicit
finiteness premises, not this exact cylinder word-family inequality.
This supports the narrow gap claim, not a claim that tame estimates or
finite-carrier infrastructure are absent. The reported missing review-199
file is a historical checkout observation, not an analytic gap.

**Concrete route for lane 202.** Start with the actual maps
`asymmetricTransport_apply` (V AsymmetricTransport:27) and
`transportL2Bilinear`/`transportL2Bilinear_apply`
(V TransportL2Time:23, :30). Expand each word using
`fieldDerivative_smul` (V H6NonlinearProduct:146) and
`scalarCommutator_recurrence` (V BaseTransportCommutator:48);
`word_derivative_comm` and `transportCommutator_eq_sum`
(V ExternalTransportCommutator:18, :38) give the exact transport identity.
Bound the mixed derivative products with a cylinder tame/interpolation
lemma; A03's `tameProductScalar` (the actual name, not
`scalarTameProduct`, ScalarTameProduct:254) and `outerProductTame`
(OuterTameProduct:177) are R³ datum estimates, so using them requires a
proved cylinder extension or restricting the analytic hypothesis to the
ordinary-lift subspace and proving that restriction for competitors.
One cannot silently descend arbitrary angular-dependent V to R³.
The vendor's `coordinateProduct_tame` and `tame_outer_product`
(OrdinaryTameProduct:63, :83) and `wordMaximum_product_le`
(OrdinaryWordInterpolation:52) are useful interpolation models, also with
ordinary smooth carriers. Prove the cylinder version and pass by smoothing/
density to compatible finite Sobolev elements, preserving restriction.
Sum the full word family and identify the exact gradient norm, then use
FFB:187 without changing any time or pressure objects.
V SobolevTransportCommutator:34, :70, :111 supplies useful bridges but
retains n+6≤s and smooth-representative conditions; V BaseTransportL2:42
only treats n≤6. Neither directly closes the top q+1 family.
For a separate signed-energy route, A04/HighEnergy:164
`outerSobolevNormAt_le` requires both finite norms, and :136
`inner_energy_Rhigh` consumes a signed pairing bound. It cannot be used
to infer the stronger forcing-family norm bound.

**Exact one-line fixes / integration notes:**

1. Replace REPORT_200:34-35 with: “At reviewed HEAD 494e1d4 and origin/erenup/integration 5ca3bea, ForcingFamilyBound has no ha binder; recheck this signature after updating the integration base.”
2. Add to REPORT_200's merge notes: “Retain integration's MildEnergyEnvelope.lean, including energyComparison_unique, when reconciling this branch; rerun the module and axiom gates afterward.”

No proof-source fix is required for the conditional result at the reviewed refs.

## 4. Commands and results

Read CLAUDE.md, the lane-review skill, NEXT_SESSION, HANDOFF §0/P7, the
first 40 LESSONS lines, REPORT_198/199/200, REVIEW_198's gap discussion, and
the cited paper/tree statements. The existing shared package symlink was
verified; reinstalling dependencies was unnecessary. All Lean shells sourced
`. scripts/lean-env.sh`; all Lake invocations were sequential, in
`verification/`, with `LEAN_NUM_THREADS=6`.

Build: exit 0, no diagnostics from this module; dependency warnings mean
the whole Lake invocation is not literally silent. Direct module Lean:
exit 0, zero output. Axioms: exit 0, exactly 18 expected audits.
make check, scripts/gates.sh (including tests and mutations), and explicit
base-contract checking: exit 0. The last two were run additionally although
verification was untouched. The standard gate script filters test output
and has pipeline masking behavior (`scripts/gates.sh:11-13`); no errors
were observed in its reported output. The direct module and audit checks
are independent of that filtering.

Repository-wide make check still reports historical copied-source tokens
and source_hashes_match=false; these are its existing informational output,
not admissions in this module's checked dependency closure. The 18 kernel
audits are the relevant transitive-axiom evidence.

**Substantive negative checks.** The baseline main identity is checked in
the module. In `research/A01/probes/rev200_forcing_sign.lean:22` onward,
changed its force-array PLUS commutator to MINUS commutator, leaving every
binder, premise and proof step intact. Lean exits 1 at :50 with the expected
conclusion mismatch. The auxiliary `rev200_sign.lean:6` flips the sign in
the array algebra and fails at :11. Neither probe merely drops an argument;
these demonstrate proof sensitivity, not a separately proved counterexample.
The existing non-vacuity examples were rerun with the axiom file.

Raw output excerpts below contain no more than the first and last 40 lines
of any command; “[middle omitted]” is a reviewer marker. Large commands
were captured with Python subprocess.run and excerpted after completion,
so no head/pipe terminated a gate early.

### Direct module check

```text
$ cd verification && LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section4/A01/ForcingFamilyBound.lean
[exit 0; zero output]
```

### Module build

Exit 0.

```text
COMMAND: lake build NSFormalization.Section4.A01.ForcingFamilyBound
EXIT: 0
LINES: 219
⚠ [8927/9629] Replayed NSFormalization.Source.FiniteHilbertBochner
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
⚠ [10092/10248] Replayed Formal.R3LerayFrequencySymbol
warning: ../vendor/HeliCorgi/Formal/R3LerayFrequencySymbol.lean:43:2: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
⚠ [10112/10248] Replayed NSFormalization.Source.RealSobolev
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
[middle omitted]
⚠ [10153/10248] Replayed Formal.R3LerayComplexFiberSymbol
warning: ../vendor/HeliCorgi/Formal/R3LerayComplexFiberSymbol.lean:42:2: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
ℹ [10168/10248] Replayed NSFormalization.Source.PhysicalBesselSobolev
info: NSFormalization/Source/PhysicalBesselSobolev.lean:134:4: Try this:
  [apply] ring_nf

  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.

  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
⚠ [10173/10248] Replayed NSFormalization.Source.PacketForceExtension
warning: NSFormalization/Source/PacketForceExtension.lean:44:25: `if_pos` has been deprecated: Use `ite_eq_left` instead
⚠ [10176/10248] Replayed NSFormalization.Source.ViscosityPacket
warning: NSFormalization/Source/ViscosityPacket.lean:34:63: This simp argument is unused:
  Function.comp_def

Hint: Omit it from the simp argument list.
  [apply] simp [viscosityVelocity, dilateField, viscosityHomeomorph, Prod.map]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
⚠ [10190/10248] Replayed NSFormalization.Paper3.SobolevDirectionalDerivative
warning: NSFormalization/Paper3/SobolevDirectionalDerivative.lean:103:16: `SchwartzMap.smul_apply` has been deprecated: Use `smul_apply` instead

Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.smul_apply` to `smul_apply x`).
⚠ [10240/10248] Replayed NSFormalization.Section4.A01.AprioriFamily
warning: NSFormalization/Section4/A01/AprioriFamily.lean:148:31: Variable name `ha` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _ha

Note: This linter can be disabled with `set_option linter.unusedVariables false`
⚠ [10241/10248] Replayed NSFormalization.Section4.A01.MildGronwall
warning: NSFormalization/Section4/A01/MildGronwall.lean:150:31: Variable name `ha` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _ha

Note: This linter can be disabled with `set_option linter.unusedVariables false`
Build completed successfully (10248 jobs).
```

### Axiom file: lake env lean ../research/A01/axioms_forcing_bound.lean

Exit 0.

```text
'NSFormalization.Section4.A01.E' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.A' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.E_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.A_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.cylinderCommutator' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.source_pressure_cancel' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.CylinderCommutatorBound' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.energyRawTime_ae' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.energyForcingNorm_ae' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.sourceTime_add_pressureTime_ae' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.forcing_array_rearrange' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.cylinderEnergyForcing_ae' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.force_word_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.forcingFamilyBound_of_cylinder' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private._stdin.0.NSFormalization.Section4.A01.zero_value' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private._stdin.0.NSFormalization.Section4.A01.zero_sob' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private._stdin.0.NSFormalization.Section4.A01.zero_mild' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private._stdin.0.NSFormalization.Section4.A01.zero_forcing' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### make check

Exit 0.

```text
COMMAND: make check
EXIT: 0
LINES: 28234
python3 experiments/check_formalization_plan.py --check
{
  "task_count": 30,
  "source_counts": {
    "formalization": 517,
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
[middle omitted]
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
Ran 13 tests in 0.048s

OK
python3 experiments/check_work_queue.py
30 work items: ownership, contract registration and task cards consistent.
```

### scripts/gates.sh NSFormalization.Section4.A01.ForcingFamilyBound

Exit 0.

```text
COMMAND: scripts/gates.sh NSFormalization.Section4.A01.ForcingFamilyBound
EXIT: 0
LINES: 28496
== make check
python3 experiments/check_formalization_plan.py --check
{
  "task_count": 30,
  "source_counts": {
    "formalization": 517,
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
[middle omitted]
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

### python3 experiments/check_contracts.py --base-ref origin/erenup/integration

Exit 0.

```text
COMMAND: python3 experiments/check_contracts.py --base-ref origin/erenup/integration
EXIT: 0
LINES: 28202
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
[middle omitted]
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

### Main forcing-sign mutation

Exit 1.

```text
../research/A01/probes/rev200_forcing_sign.lean:50:2: error: Type mismatch
  forcing_array_rearrange (↑↑(ForcedSourceUpgrade.sourceTime hq hT hTS f u V) r)
    (↑↑(energyPressureTime hq hT hTS f u V) r) (extendPath T hT (f.comp (timeInclusion hTS)) r)
    (((asymmetricTransport 1 (Decidable.byContradiction fun a => rev200_forcing_sign._proof_1_2 hq a)
          (velocityComponents 1 0)
          (velocityComponents_norm 1 0
            (Mathlib.Meta.NormNum.isNat_le_true
              (Mathlib.Meta.NormNum.isNat_abs_nonneg (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one))
              (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one) (Eq.refl true))
            (of_eq_true (Eq.trans (congrFun' (congrArg LE.le norm_zero) 1) zero_le_one._simp_1))))
        (extendPath T hT u r))
      ((restrictOperator 1 (Decidable.byContradiction fun a => rev200_forcing_sign._proof_1_1 a)) (↑↑U r)))
    ?m.317 (Eq.trans hc hb)
has type
  (fun w =>
      ↑(↑↑(ForcedSourceUpgrade.sourceTime hq hT hTS f u V) r) w + ?m.317 w +
        ↑(↑↑(energyPressureTime hq hT hTS f u V) r) w) =
    ↑(extendPath T hT (f.comp (timeInclusion hTS)) r) +
      (?m.317 -
        ↑(((asymmetricTransport 1 ⋯ (velocityComponents 1 0) ⋯) (extendPath T hT u r))
            ((restrictOperator 1 ⋯) (↑↑U r))))
but is expected to have type
  (fun w =>
      ↑(↑↑(ForcedSourceUpgrade.sourceTime hq hT hTS f u V) r) w +
          ((transportL2Bilinear 1 ⋯ 1 0) (extendPath T hT u r)) ((boundedWordBlock 1 1 ↑w.fst ⋯ w.snd) (↑↑U r)) +
        ↑(↑↑(energyPressureTime hq hT hTS f u V) r) w) =
    ↑(extendPath T hT ((sobolevPath F hF (q + 1)).comp (timeInclusion hTS)) r) -
      cylinderCommutator hq (extendPath T hT u r) (↑↑U r)
```

### Array-sign mutation

Exit 1.

```text
../research/A01/probes/rev200_sign.lean:11:2: error: 'change' tactic failed, pattern
  ?m.124 = ↑f w + (t w - ↑b w)
is not definitionally equal to target
  ↑s w + t w + ↑p w = (↑f + (t + ↑b)) w
```

### Diff and hygiene checks

`git diff --name-only origin/erenup/integration...HEAD` (exit 0):

```text
formalization/NSFormalization/Section4/A01/ForcingFamilyBound.lean
formalization/NSFormalization/Section4/A01/MildEnergyEnvelope.lean
research/A01/A3_SPLIT.md
research/A01/ATTEMPTS_ENVELOPE.md
research/A01/ATTEMPTS_FORCING_BOUND.md
research/A01/REPORT_199.md
research/A01/REPORT_200.md
research/A01/axioms_envelope.lean
research/A01/axioms_forcing_bound.lean
```

`git diff --check`: exit 0, zero output.
`rg -n '\b(sorry|admit|axiom|native_decide)\b|maxHeartbeats' formalization/NSFormalization/Section4/A01/ForcingFamilyBound.lean`:

```text
81:set_option maxHeartbeats 400000 in
112:set_option maxHeartbeats 400000 in
143:set_option maxHeartbeats 400000 in
```
