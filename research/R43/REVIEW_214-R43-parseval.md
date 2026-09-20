ACCEPT

## 1. What the lane claims

Reviewed commit `7f699a9` (`erenup/214-R43-parseval`), using the lane-review workflow in `.claude/skills/lane-review/SKILL.md`, with the user's read-only restrictions taking precedence. Read CLAUDE.md, HANDOFF §0/§2 P5, the top 40 LESSONS lines, REPORT_214, ATTEMPTS_PARSEVAL, lane 182's review and lane 191's report.

The report correctly claims four supporting lemmas and four exports, all in `formalization/NSFormalization/Section4/R43/Parseval.lean`: `homogeneous_slice_angular_ae` (:27), `angular_real_parseval` (:39), `component_real_pairing` (:48), `half_order_parseval` (:60), `pairing_identity_of_hcrit` (:104), `criticalAdvectionLpBridge_of_hcrit` (:123), `criticalTrilinearEstimate_of_hcrit'` (:131), and `rcritical1_of_hcrit'` (:139). Their actual statements match the report; the constructor is correctly a `def`.

Opened `paper/sections/04-whole-space.tex:85-110` using `sed -n`; lines 97–99 are exactly:

```tex
\begin{equation}\label{eq:Rcritical1}
 \tfrac12(y^2)'+(\nu-C_0y)z^2\le by.
\end{equation}
```

`CriticalPairing.lean:51`, `:55`, and `:59` define the physical homogeneous norms y, z, b. `Trilinear.lean:319` proves `trilinearConst = 16 * A05.criticalL3Const ^ 3`; its positivity is at :326. The new derivative-and-inequality conjunction reproduces eq:Rcritical1 with precisely this constant, conditional on the named datum path. It does not claim unconditional R43.

## 2. What is in Lean

Paths abbreviated below as `R43/`, `D01/`, `A04/`, `A05/` mean `formalization/NSFormalization/Section4/` followed by that path.

1. **Weights and datum pairing.** `D01/HomogeneousWitness.lean:131` defines the forward profile as `|ξ|^s` times the normalized angular Fourier transform. Its exact datum predicate at :234 instead identifies the distribution with `|ξ|^(-s) G`; the vector/slice predicates are at :246/:251. Thus each half-order datum carries one `|ξ|^(1/2)` factor. `D01/RealPairing.lean:77` identifies the subtype inner product with the ambient real L² inner product, and :66 identifies that with the real part of the complex L² inner product. `Parseval.lean:69-79` unfolds those definitions and uses `L2.inner_def`. This is the requested weighted integral, not an inhomogeneous Bessel pairing. `D01/HalfOrder.lean:120` is an inhomogeneous path-lowering tool, not the definition of this homogeneous weight.

2. **Symbol and cancellation.** `A05/RieszShift.lean:637` (`homogeneousDatum_angularFourier_ae`) proves the inverse-weight identification for arbitrary real s by distributional uniqueness. `Parseval.lean:27-36` applies it to the canonical physical component classes. `A05/RieszShift.lean:697` (`angular_rieszLambda_component_ae`) has exactly the multiplier `‖ξ‖`, not its square and not `2π‖ξ‖`. The angular rescaling cancels the cycles-frequency constant at :723-730. `Parseval.lean:81-92` proves `‖ξ‖ * (‖ξ‖^(-1/2) * ‖ξ‖^(-1/2)) = 1` away from the null singleton {0}. This is precisely moving the combined half weights onto the velocity factor.

3. **Actual L² Plancherel.** `Parseval.lean:39-44` uses `MeasureTheory.Lp.inner_fourier_eq` (`verification/.lake/packages/mathlib/Mathlib/Analysis/Fourier/LpSpace.lean:93`) and `angularFrequencyDilation.inner_map_map`; the dilation is a linear isometric equivalence (`formalization/NSFormalization/Paper3/AngularFourierDilation.lean:81`). Both transforms are actual L² elements, not potentially undefined pointwise Fourier integrals. The advection L² witness is explicitly `A03.SmoothL2.memLp (D01.advection_slice_smoothL2 w ht)` at Parseval :116-117; the supplying theorem is `D01/Pressure.lean:291`. This is the direct tree route, rather than a new application of `A04/NonlinearDatum.lean:186`. The independent homogeneous advection datum is `hcrit.advectionHalf_isDatum t ht` on Ioo (`R43/CriticalPairing.lean:177`). Velocity regularity is supplied at Parseval :118. Lambda's L² witness is `A05/RieszShift.lean:460`; its stronger all-order regularity is `rieszLambda_memHInfty` at :468, packaged at :973. `Parseval.lean:99-101` proves component products integrable before commuting the sum and integral. No default-zero nonintegrable integral is used.

4. **Real parts and conjugation.** The proof takes real parts of complex Plancherel, with the correct real L² instance (`D01/RealPairing.lean:66`). At Parseval :89 it explicitly uses `map_mul` and `Complex.conj_ofReal`; its integrand is B times conjugate A, consistent with Lean's convention. `component_real_pairing` (:48-56) returns the real physical product. Fourier reflection symmetry `f̂(-ξ)=conj(f̂(ξ))` is not needed in this pairing step; the real physical fields are complexified componentwise and real parts suffice. Realness of the chosen Riesz representative is already supplied by lane 191.

5. **Exact bridge and corollaries.** `R43/Trilinear.lean:298-310` has exactly two bridge fields. `Parseval.lean:127-128` fills them with lane 191's shifted constructor and the new identity. `R43/ShiftedData.lean:36-41` selects `A05.shiftedCriticalData_of_memHInfty`; `A05/RieszShift.lean:972` makes its lambda definitionally `rieszLambda`. The stationary lift advection is definitionally the original slice, as the successful exact proof at Parseval :115 verifies. No extra bridge premise, estimate, or hidden named analytic hypothesis appears.

Exact exported statements and constructor (verbatim from Parseval :104-151):

```lean
theorem pairing_identity_of_hcrit
    {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    {w : ClassicalSolutionR ν a f T} {hf : MemForceR f}
    (hcrit : CriticalDatumPath w hf) :
    ∀ t (ht : t ∈ Ioo (0 : ℝ) T),
      ⟪hcrit.advectionHalf t, hcrit.velocityHalf t⟫ =
        ∫ x : Space, (inner ℝ
          (advection (NSFormalization.Section4.C01.lift
            (fun y => w.velocity (t, y))) 0 x)
          ((criticalAdvectionLpBridge_shifted hcrit t ht).lambda x) : ℝ) := by
  intro t ht
  exact half_order_parseval
    (NSFormalization.Section4.A03.SmoothL2.memLp
      (NSFormalization.Section4.D01.advection_slice_smoothL2 w ht))
    (NSFormalization.Section4.C01.velocity_slice_memHInfty w (Ioo_subset_Ico_self ht))
    (hcrit.advectionHalf_isDatum t ht)
    (hcrit.velocityHalf_isDatum t (Ioo_subset_Ico_self ht))

/-- The complete S1b bridge, with no input beyond the critical datum path. -/
def criticalAdvectionLpBridge_of_hcrit
    {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    {w : ClassicalSolutionR ν a f T} {hf : MemForceR f}
    (hcrit : CriticalDatumPath w hf) : CriticalAdvectionLpBridge hcrit where
  shifted := criticalAdvectionLpBridge_shifted hcrit
  pairing_identity := pairing_identity_of_hcrit hcrit

/-- S1b with the carrier and Parseval obligations discharged. -/
theorem criticalTrilinearEstimate_of_hcrit'
    {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    {w : ClassicalSolutionR ν a f T} {hf : MemForceR f}
    (hcrit : CriticalDatumPath w hf) :
    CriticalTrilinearEstimate (C₀ := trilinearConst) hcrit :=
  criticalTrilinearEstimate_of_hcrit hcrit (criticalAdvectionLpBridge_of_hcrit hcrit)

/-- The critical differential inequality, conditional on `hcrit` alone. -/
theorem rcritical1_of_hcrit'
    {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    {w : ClassicalSolutionR ν a f T} (hf : MemForceR f)
    (hcrit : CriticalDatumPath w hf) :
    (∀ t ∈ Ioo (0 : ℝ) T,
      HasDerivAt (fun r => criticalNormAt w.velocity r ^ 2)
        (criticalEnergyDerivative hcrit t) t) ∧
      ∀ t ∈ Ioo (0 : ℝ) T,
        criticalEnergyDerivative hcrit t / 2 +
            (ν - trilinearConst * criticalNormAt w.velocity t) *
              criticalDissipationAt w.velocity t ^ 2
          ≤ criticalForceAt f t * criticalNormAt w.velocity t :=
  rcritical1_of_hcrit hf hcrit (criticalAdvectionLpBridge_of_hcrit hcrit)
```

6. **Non-vacuity and hygiene.** `A02/SolutionClass.lean:120` requires `horizon_pos : 0 < T`, so the interior is nonempty. `CriticalPairing.lean:64-91` identifies each supplied homogeneous ENorm with a finite datum norm; the `.toReal` quantities cannot exploit `⊤.toReal = 0`. The hcrit fields at :164-201 are genuine datum, smoothness, momentum and symbol obligations; no conclusion estimate is assumed. `research/R43/axioms_parseval.lean:25-99` constructs every field for `A04.zeroSol 1 2`; :105-132 invokes the actual new bridge and both corollaries at t=1. All examples compile. This proves satisfiability, not construction for every nonzero solution. No added hypothesis restricts the Parseval lemma to zero fields.

Static scan of both new Lean files found no `sorry`, `admit`, `axiom`, `native_decide`, or heartbeat override. The audit prints exactly the required three axioms for all eight module declarations and the zero constructor. No existing Lean module or verification file was modified. The existing `R43_SPLIT.md` change is the explicit deliverable requested by the brief, so is not a violation of its new-module rule. Changed-module CI discovery includes Parseval (`experiments/build_changed_lean.py:18`); the dry-run prints `Changed Lean modules: NSFormalization.Section4.R43.Parseval`.

## 3. Gaps

No blocking findings; no fixes required. The remaining general `CriticalDatumPath` constructor is correctly outside this lane.

Before accepting that gap, ran whole-tree `grep -rnE` searches for `CriticalDatumPath|homogeneousLeSobolev|endpoint|momentum.*[Hh]alf|half.*momentum` and `homogeneous.*[Cc]onstruct|[Hh]omogeneous.*[Mm]omentum|[Cc]ritical.*[Pp]ath|homogeneousLeSobolev` under `formalization/NSFormalization/Section4`, plus filename searches for Homogeneous/Critical/Momentum/HalfOrder. The hits show consumers and the structure, no general producer. Inspected the closest candidates: `D01/HalfOrder.lean:120`, `D01/HomogeneousWitness.lean:443`, `A04/MomentumDatum.lean:138`, and `B02/SeparatedAssembly.lean:26` (compact separated fields, not a general classical path). The report declares no other missing analytic lemma.

For the lead, G3/G4/path construction still needs:

- Integer-order physical data and paths lowered to fractional inhomogeneous order (`D01/HalfOrder.lean:93`, :103, :120), then the angular real-vector homogeneous multiplier bridge U3 (`homogeneousLeSobolev`). The scalar contraction exists at `formalization/NSFormalization/Source/BesselFractionalData.lean:12`, :45, :55; the generic Section4 constructor is not exported. Path continuity/smoothness and force time-integrability must also be transported, not inferred from isolated slice existence.
- Endpoint order 3/2 existence for the velocity: U1 uniqueness already works at every real order (`D01/HomogeneousWitness.lean:443`); lane 191's identification at `A05/RieszShift.lean:637` also includes the endpoint. U4 (`rieszLambda_halfDatum`, :735) consumes an existing order-3/2 datum and supplies lambda's half datum; it does not construct the initial endpoint datum. Use the physical weighted L² transform to establish existence, with the integrability clause of :234 verified.
- Transport the integer datum momentum equation (`A04/MomentumDatum.lean:138`, requiring m≥2 and actual datum paths) through a continuous linear homogeneous half-order map, commuting time differentiation. Supply the six data, half-path smoothness, order shift, Laplacian symbol, divergence/transversality and pressure-range identities listed at `R43/CriticalPairing.lean:164-201`. G4 additionally requires the homogeneous force norm's time-integrability; the current lane proves only the interior differential inequality.

## 4. Commands and results

All Lean commands sourced `. scripts/lean-env.sh`; every lake command ran from `verification/` with `LEAN_NUM_THREADS=6`, sequentially. Existing installation was used without running the mutating installer. The ordinary build replays dependency warnings but none originate in Parseval; the quiet build and direct module check each produced **zero output** (exit 0):

```sh
lake -q --log-level=error build NSFormalization.Section4.R43.Parseval
lake env lean ../formalization/NSFormalization/Section4/R43/Parseval.lean
```

`git diff --check`: exit 0, zero output. Static scan: exit 1, zero matches. `git diff --name-status origin/erenup/integration...HEAD`:

```text
A formalization/NSFormalization/Section4/R43/Parseval.lean
A research/R43/ATTEMPTS_PARSEVAL.md
M research/R43/R43_SPLIT.md
A research/R43/REPORT_214.md
A research/R43/axioms_parseval.lean
```

The substantive mutation in `research/R43/probes/rev214_mutation.lean:65` changes the main general identity to `⟪A,B⟫ = 2 * ∫ ...`, leaving all hypotheses and the proof intact (namespace changed only to isolate the probe). It fails at the integral equality and then at its specialization, exactly because of the added factor. No argument was dropped.

Command outputs below are exact excerpts: at most the first and last 40 lines of each output, with omission markers outside the quoted output. Full build/check logs are not pasted.

`lake build NSFormalization.Section4.R43.Parseval`: exit 0, 262 output lines.

First 40 lines:

```text
⚠ [8779/8885] Replayed NSFormalization.Source.FiniteHilbertBochner
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
⚠ [10070/10268] Replayed NSFormalization.Source.RieszPotentialNearField
warning: NSFormalization/Source/RieszPotentialNearField.lean:21:17: Variable name `hR` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hR

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: NSFormalization/Source/RieszPotentialNearField.lean:21:30: Variable name `hB` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hB

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: NSFormalization/Source/RieszPotentialNearField.lean:49:4: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
⚠ [10106/10268] Replayed NSFormalization.Source.RealSobolev
warning: NSFormalization/Source/RealSobolev.lean:90:30: This simp argument is unused:
  Complex.smul_re

Hint: Omit it from the simp argument list.
  [apply] simp [Complex.smul_im]
```

[Middle output omitted.]

Last 40 lines:

```text
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
⚠ [10233/10268] Replayed NSFormalization.Source.RieszL2Fourier
warning: NSFormalization/Source/RieszL2Fourier.lean:31:2: Try this: 
  letI̵

The goal is a proposition, so `let` is preferred over `letI`.
The difference between `let` and `letI` is that `letI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
⚠ [10234/10268] Replayed NSFormalization.Source.FractionalRealization
warning: NSFormalization/Source/FractionalRealization.lean:60:2: Try this: 
  letI̵

The goal is a proposition, so `let` is preferred over `letI`.
The difference between `let` and `letI` is that `letI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: NSFormalization/Source/FractionalRealization.lean:83:2: Try this: 
  letI̵

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
Build completed successfully (10268 jobs).
```

`lake env lean ../research/R43/axioms_parseval.lean`: exit 0, 13 output lines.

```text
'NSFormalization.Section4.R43.homogeneous_slice_angular_ae' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R43.angular_real_parseval' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R43.component_real_pairing' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R43.half_order_parseval' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R43.pairing_identity_of_hcrit' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R43.criticalAdvectionLpBridge_of_hcrit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.R43.criticalTrilinearEstimate_of_hcrit'' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.R43.rcritical1_of_hcrit'' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R43.zeroCriticalDatumPathParseval' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`make check`: exit 0, 28234 output lines.

First 40 lines:

```text
python3 experiments/check_formalization_plan.py --check
{
  "task_count": 30,
  "source_counts": {
    "formalization": 529,
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

[Middle output omitted.]

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
Ran 13 tests in 0.045s

OK
python3 experiments/check_work_queue.py
30 work items: ownership, contract registration and task cards consistent.
```

`bash scripts/gates.sh NSFormalization.Section4.R43.Parseval`: exit 0, 28539 output lines.

First 40 lines:

```text
== make check
python3 experiments/check_formalization_plan.py --check
{
  "task_count": 30,
  "source_counts": {
    "formalization": 529,
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

[Middle output omitted.]

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

`python3 experiments/check_contracts.py --base-ref origin/erenup/integration`: exit 0, 28202 output lines.

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

[Middle output omitted.]

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

`lake test (independent exit-code check because gates.sh filters this output)`: exit 0, 343 output lines.

First 40 lines:

```text
⚠ [8778/9168] Replayed NSFormalization.Source.FiniteHilbertBochner
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
⚠ [9875/10104] Replayed NSFormalization.Source.BoundedReferenceFlux
warning: NSFormalization/Source/BoundedReferenceFlux.lean:17:5: Variable name `hU0` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hU0

Note: This linter can be disabled with `set_option linter.unusedVariables false`
⚠ [9876/10104] Replayed NSFormalization.Source.BoundedReferenceComparison
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

[Middle output omitted.]

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

`lake env lean ../research/R43/probes/rev214_mutation.lean`: exit 1, 28 output lines.

```text
../research/R43/probes/rev214_mutation.lean:96:4: error: Tactic `apply` failed: could not unify the conclusion of `@integral_congr_ae`
  ∫ (a : ?α), ?f a ∂?μ = ∫ (a : ?α), ?g a ∂?μ
with the goal
  ∫ (a : Space), ∑ i, (u a).ofLp i * (rieszLambda v hv a).ofLp i = 2 * ∫ (x : Space), ⟪u x, rieszLambda v hv x⟫

Note: The full type of `@integral_congr_ae` is
  ∀ {α : Type ?u.226} {G : Type ?u.225} [inst : NormedAddCommGroup G] [inst_1 : NormedSpace ℝ G] {m : MeasurableSpace α}
    {μ : Measure α} {f g : α → G}, f =ᵐ[μ] g → ∫ (a : α), f a ∂μ = ∫ (a : α), g a ∂μ

u v : SpatialField
hu : MemLp u 2 volume
hv : MemHInfty v
A B : RealVectorSobolev (1 / 2)
hA : IsHomogeneousSliceDatum (1 / 2) u A
hB : IsHomogeneousSliceDatum (1 / 2) v B
hscalar : ∀ (i : Fin 3), ⟪A.ofLp i, B.ofLp i⟫ = ⟪componentLp hu i, componentLp ⋯ i⟫
⊢ ∫ (a : Space), ∑ i, (u a).ofLp i * (rieszLambda v hv a).ofLp i = 2 * ∫ (x : Space), ⟪u x, rieszLambda v hv x⟫
../research/R43/probes/rev214_mutation.lean:115:2: error: Type mismatch
  half_order_parseval (A03.SmoothL2.memLp (D01.advection_slice_smoothL2 w ht))
    (C01.velocity_slice_memHInfty w (Ioo_subset_Ico_self ht)) (hcrit.advectionHalf_isDatum t ht)
    (hcrit.velocityHalf_isDatum t (Ioo_subset_Ico_self ht))
has type
  ⟪hcrit.advectionHalf t, hcrit.velocityHalf t⟫ =
    2 * ∫ (x : Space), ⟪advection w.velocity t x, rieszLambda (fun x => w.velocity (t, x)) ⋯ x⟫
but is expected to have type
  ⟪hcrit.advectionHalf t, hcrit.velocityHalf t⟫ =
    ∫ (x : Space),
      ⟪advection (C01.lift fun y => w.velocity (t, y)) 0 x, (criticalAdvectionLpBridge_shifted hcrit t ht).lambda x⟫
```

Final verdict: ACCEPT. Fixes: none. Only this review and the permitted mutation probe were added; no lane source, existing record, index, commit, or branch state was changed.
