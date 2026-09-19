# T21 proof-lane split — cor:nondensity + thm:main

Lead-facing, 2026-09-19. Target: nine-field `NonDensityAPI` and five-field `MainTheoremAPI`, their paper-order statements and assembly signatures.
Target: `research/T21/Spec.lean`; approved design: `research/T21/RECONCILIATION.md` §0.
Twin: Section4/R41. House style: T18/T20 splits.
Size legend: **S** ≤ approximately 100 lines; **M** one bounded lemma with a known route; **L** a multi-file campaign, which must be peeled before assignment. Model legend: **codex-sol = bookkeeping/transport, codex-astra = analytic core/planning**.

## 0. Ground rules

**Peeling rule.** Every N-unit ends in a theorem with the verbatim field type below, or a helper directly consumed by that field. If an M unit grows into a multi-file campaign, stop and split its exact residual into smaller helper theorems; do not introduce a named input, placeholder field, extra axiom, or stronger hypothesis to conceal it. T21 has **no named inputs**: everything is threaded from `CriticalRegularityTAPI` / `PeriodicDensityAPI`, proved by the units below, or registered.

**Threaded versus inhabited.** A theorem taking `K : CriticalRegularityTAPI` may be proved before a closed K exists. The analogous rule applies to T19 density. These parameterized theorems can start now; unconditional statements and registration wait for the actual suppliers. T20's canonical record is `Section3/T20/CriticalRegularity.lean:139`, with `c:145`, `hc:150`, `globalRegularity:365`. The consumed T19 record is `research/T19/Spec.lean:192`, copied in T21 `Spec.lean:115`; its `fixedInitialDensity` is at T19 `:207` / T21 `:130`. Do not import either blind draft or make another copy of T20/T12. T19's copied declaration is an interim Spec arrangement, not a second production record.

**Layering.** Analytic helpers belong under canonical `Section3/T21/` and use canonical T10 vocabulary. Verbatim registered-field probes and the lifespan conversion belong under `verification/` (temporary probes may live under `research/T21/probes/`). Do not import Contracts or Bindings into formalization. The final contract uses registered vocabulary and imports only permitted contract dependencies. Registered `forceClassT` / `forceSobolevENormT` have definitional bridges (`Bindings/TorusLocalTheory.lean:57,67`); lifespan needs the propositional bridge (`:270`). The explicit checked seam is T21 `Spec.lean:637-643`. Proposed module names below are destinations, not claims that those modules exist.

**Scope.** Preserve all nine `NonDensityAPI` fields (`Spec.lean:269-431`) and all five `MainTheoremAPI` fields (`:467-559`), both Prop-valued under lead approval (`RECONCILIATION.md` §0). The paper fixes q = 1, the threshold 1/2, positive viscosity/horizon, and the zero-datum converse (`paper/sections/03-torus.tex:6-16,506-525`, read with sed). Keep unrestricted real orders in monotonicity and the biconditional, including negative subcritical orders. No Section 4 q = 2 branch or regular-reference rider; compare `Contracts/V1/MainThresholds.lean:23,40,54,79`.

**Execution.** Work only in the lane worktree; no push, merge, or rebase. This delivery edits Markdown only. Future proof workers source `. scripts/lean-env.sh`, run lake only from `verification/` with `LEAN_NUM_THREADS=6`, provide exact-field probes and standard-axiom audits, and run required gates. Commit incremental sections. Registration/registry changes are confined to final assembly.

**Citation convention.** `Spec.lean` without a prefix means `research/T21/Spec.lean`; `Section3/`, `Section4/`, `Paper1/` mean `formalization/NSFormalization/`; `Contracts/`, `Bindings/`, `Tests/` mean `verification/`. Source observations below are from this checkout; lane progress supplied by the task brief is a scheduling snapshot, not a claim of a new local implementation.

## 1. Units and lane bundles

Eight lane bundles: **Z** (N4,N5,N12; S), **D** (N1,N2; M), **F** (N3; M), **T** (N6; M), **B** (N7,N10; S), **C** (N0,N8,N9; S), **M** (N11,N13,N14,N15; S), **A** (final assembly; M). Each N has one owner; B may stage N7 before N10's dependencies arrive. No bundle requires more than one worker. Shared module ownership is serial within a bundle.

**N0 — T20 bridge** (transport; lane C). New module: `verification/Bindings/TorusNonDensity.lean` (final destination); pre-registration seam probe under `research/T21/probes/`.

Target (verbatim, `Spec.lean:280`):
```lean
  hc : 0 < c
```
Target (verbatim, `Spec.lean:300`):
```lean
  criticalGlobalRegularity : ∀ ν : ℝ, 0 < ν →
    ∀ g : SpaceTimeField, g ∈ forceClassT →
      forceSobolevENormT 1 (1 / 2) g < ENNReal.ofReal (c * ν) →
        maximalLifespanT ν (fun _ : Space ↦ 0) g = ⊤
```

Route. With K threaded, take `K.hc`; rewrite registered lifespan with `Bindings/TorusLocalTheory.lean:270`, then apply `K.globalRegularity` (`Section3/T20/CriticalRegularity.lean:365`). The full checked term is `Spec.lean:637-643`; the critical norm is definitionally identified at `:231-233`. Never attempt an rfl lifespan bridge.

**Size, model:** S, codex-sol. **Deps:** threaded K only; no T20 U13 needed for this conditional proof.

**N1 — datum order-lowering contraction** (analytic helper; lane D). New module: `Section3/T21/OrderLowering.lean`.


Route. Direct helper for N2 (`Spec.lean:363`) and N3 (`:381`):
`∀ s t : ℝ, s ≤ t → ∀ A : PeriodicSobolev t, ∀ B : PeriodicSobolev s, IsPeriodicReweight t s A B → ‖B‖ ≤ ‖A‖`.
Also construct B and prove `IsPeriodicDatum t z A → IsPeriodicDatum s z B`.
Use symbol `periodicFrequencyWeight k ^ ((s-t)/2)`. The definition at `Contracts/V1/TorusData.lean:81` gives weight ≥ 1; its reweight relation is `:228`, datum relation `:125`, and real submodule `:93`. Prove the real even symbol has absolute value ≤ 1, preserving conjugate reflection. Instantiate the existing multiplier/norm estimate (`Section3/T11/LocalExistenceProbe.lean:61`); equality with any B follows coefficientwise. The pointwise contractivity template is `Section4/R41/NonDensityL1.lean:16-38`. Do not discard the datum's integrability conjunct.

**Size, model:** M, codex-astra. **Deps:** registered/canonical T10 coefficient vocabulary; T11 multiplier implementation; no upstream witness.

**N2 — slice Sobolev monotonicity** (analytic transport; lane D). New module: `Section3/T21/OrderLowering.lean`.

Target (verbatim, `Spec.lean:363`):
```lean
  sliceSobolevMonotone : ∀ s : ℝ, 1 / 2 ≤ s → ∀ z : SpatialField,
    periodicSobolevENorm (1 / 2) z ≤ periodicSobolevENorm s z
```

Route. Apply N1 to every representing datum at order s, choose its order-1/2 image in the left infimum, and use `le_iInf` on the right. Empty representative sets retain ⊤ automatically (`Contracts/V1/TorusData.lean:134`). `Paper1/PeriodicCriticalRegularity.lean:33` is the smooth TestForce analogue, not the unconditional field; it must not supply an extra smoothness hypothesis.

**Size, model:** S, codex-sol. **Deps:** N1.

**N3 — force Sobolev monotonicity via a CLM** (analytic transport; lane F). New module: `Section3/T21/ForceMonotonicity.lean`.

Target (verbatim, `Spec.lean:381`):
```lean
  forceSobolevMonotone : ∀ s : ℝ, 1 / 2 ≤ s → ∀ f : SpaceTimeField,
    forceSobolevENormT 1 (1 / 2) f ≤ forceSobolevENormT 1 s f
```

Route. Package N1's general inhomogeneous symbol as `PeriodicSobolev t →L[ℝ] PeriodicSobolev s` using `Section3/T11/LocalExistence.lean:63` (`torusMultiplierCLM`), with pointwise norm bound and operator norm ≤ 1. The exact ready-made construction pattern is lane 428 `Section3/T20/YBound.lean:86-91` (`critLower`). **Its symbol is not reusable unchanged**: `:56` and `:96-98` send an inhomogeneous order-one datum to a homogeneous mean-zero order-half datum. Use N1's weight ratio instead.
For every admissible higher-order path G, transport the path relation by N1 and AE strong measurability by the CLM's continuity. Use `eLpNorm_mono` then `le_iInf` / `iInf_le` exactly as `Section4/R41/NonDensityL1.lean:42-55`; the whole-space CLM is defined at `Section4/D01/HalfOrder.lean:103`. Registered path/norm definitions are `Contracts/V1/TorusLocalTheory.lean:82,89`. This proves the unconditional field even when no path exists. `Paper1/PeriodicCriticalRegularity.lean:47` is only a comparison template.

**Size, model:** M, codex-astra. **Deps:** N1; T11 multiplier CLM; not T20 U13.

**N4 — zero force membership** (bookkeeping helper; lane Z). New module: `Section3/T21/Zero.lean`.


Route. Direct helper for `zeroMemBall` (`Spec.lean:319`): `(0 : SpaceTimeField) ∈ forceClassT`. Unfold `Contracts/V1/TorusLocalTheory.lean:103,109`; use constant smoothness, reflexive periodicity, and empty compact time support K = ∅. Compare `Section4/R41/NonDensityL1.lean:101`. No spatial compactness is required.

**Size, model:** S, codex-sol. **Deps:** registered force-class definition.

**N5 — zero norm and zero ball membership** (transport/bookkeeping; lane Z). New module: `Section3/T21/Zero.lean`.

Target (verbatim, `Spec.lean:319`):
```lean
  zeroMemBall : ∀ ν : ℝ, 0 < ν → ∀ s : ℝ,
    (0 : SpaceTimeField) ∈ criticalBallT c ν s
```

Route. Reuse `Section3/T19/Bookkeeping.lean:238` (`torusForceSobolevENorm_zero`) for all q,s via the definitional norm bridge `Bindings/TorusLocalTheory.lean:57`. The helper is `∀ q s, forceSobolevENormT q s 0 = 0`. With N4 and an explicit `hc : 0 < c`, `mul_pos hc hν` and `ENNReal.ofReal_pos` close the exact field. This supplies nonemptiness; there is no separate `ballNonempty` API field.

**Size, model:** S, codex-sol. **Deps:** N4; proved T19 U6; positivity hc (scalar hypothesis, later K.hc).

**N6 — L¹ force-norm triangle inequality** (analytic helper; lane T). New module: `Section3/T21/ForceTriangle.lean` (or reuse lane 445 supplier).


Route. Direct helper for `ballRelativelyOpen` (`Spec.lean:337-341`):
`∀ (s : ℝ) (f g : SpaceTimeField), forceSobolevENormT 1 s (f + g) ≤ forceSobolevENormT 1 s f + forceSobolevENormT 1 s g`.
First prove joint additivity of the datum relation (`Contracts/V1/TorusData.lean:125`), preserving periodicity and Haar integrability; Fourier coefficient additivity uses those integrability hypotheses. Sum representing paths (`Contracts/V1/TorusLocalTheory.lean:82,89`), sum their AE measurability proofs, and apply `eLpNorm_add_le` at q=1. Descend through both infima using ENNReal addition/infimum order laws, handling an empty path set (⊤) explicitly. Alternatively datum uniqueness (`Section3/T10/DatumBasics.lean:129`) identifies admissible paths AE on the positive-time measure and gives an attained-norm route; do not assert attainment without proving it.
`Paper1/PeriodicForceTopology.lean:123` is a weaker profile-level triangle with explicit measurability and pointwise hypotheses, not this registered helper. **Coordinate with T18 U11 lane 445:** lead assigns one supplier; whichever version lands first is reused, with a registered-shape probe. Do not create mutually importing T18/T21 modules; the generic helper may be housed in a shared T10 extension by its implementation lane.

**Size, model:** M, codex-astra. **Deps:** T10 datum/path definitions and Mathlib eLpNorm; independent of N1 and upstream witnesses.

**N7 — ball openness bookkeeping** (bookkeeping; lane B). New module: `Section3/T21/Ball.lean`.

Target (verbatim, `Spec.lean:337`):
```lean
  ballRelativelyOpen : ∀ ν : ℝ, 0 < ν → ∀ s : ℝ,
    ∀ g ∈ criticalBallT c ν s,
      ∃ r : ℝ≥0∞, 0 < r ∧
        ∀ f ∈ forceClassT, forceSobolevENormT 1 s (f - g) < r →
          f ∈ criticalBallT c ν s
```

Route. Let R = `ENNReal.ofReal (c*ν)` and n = `forceSobolevENormT 1 s g`; membership gives n < R < ⊤. Set r = R - n, prove r > 0, use N6 on `(f-g)+g`, strict addition with finite n, and `(R-n)+n = R`. Keep the ambient `f ∈ forceClassT` conjunct. N5 provides nonemptiness separately. This is the ball language in paper `03-torus.tex:511-519`; R41 `NonDensityL1.lean:82-109` supplies separation/density bookkeeping but does **not** state an openness lemma.

**Size, model:** S, codex-sol. **Deps:** N6; ball definition Spec:215; N5 only for accompanying nonemptiness.

**N8 — critical ball disjointness** (bookkeeping; lane C). New module: `Section3/T21/Disjointness.lean`.

Target (verbatim, `Spec.lean:397`):
```lean
  criticalBallDisjoint : ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
    Disjoint (criticalBallT c ν (1 / 2)) (breakdownSetTZero ν T)
```

Route. Use `Set.disjoint_left`. A ball member has lifespan ⊤ by N0; a breakdown member has lifespan ≤ ofReal T by `Contracts/V1/TorusLocalTheory.lean:215,221` and `Spec.lean:203`. Contradict `ENNReal.ofReal_ne_top`. Follow `Section4/R41/NonDensityL1.lean:82-90` or `Paper1/PeriodicCriticalRegularity.lean:81-94`. The canonical proof uses K.globalRegularity; the registered probe crosses the N0 bridge.

**Size, model:** S, codex-sol. **Deps:** N0 (threaded K, not a closed witness).

**N9 — higher-order ball disjointness** (bookkeeping; lane C). New module: `Section3/T21/Disjointness.lean`.

Target (verbatim, `Spec.lean:413`):
```lean
  ballDisjoint : ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T → ∀ s : ℝ, 1 / 2 ≤ s →
    Disjoint (criticalBallT c ν s) (breakdownSetTZero ν T)
```

Route. N3 and `lt_of_le_of_lt` give inclusion of the s-ball in the half-order ball; restrict N8 with `Disjoint.mono_left`. Same radius cν, no extra multiplicative constant. Compare the monotonicity step `Section4/R41/NonDensityL1.lean:90` and `Paper1/PeriodicCriticalRegularity.lean:90-91`.

**Size, model:** S, codex-sol. **Deps:** N3,N8.

**N10 — non-density** (bookkeeping; lane B). New module: `Section3/T21/NonDensity.lean`.

Target (verbatim, `Spec.lean:430`):
```lean
  nonDensity : ∀ ν : ℝ, 0 < ν → ∀ s : ℝ, 1 / 2 ≤ s → ∀ T : ℝ, 0 < T →
    ¬ RelativelyDenseT 1 s forceClassT (breakdownSetTZero ν T)
```

Route. Assume `RelativelyDenseT`, unfold its positive-radius form (`Contracts/V1/TorusLocalTheory.lean:226`), and test at zero (N4) and ofReal(cν)>0. The resulting f is in the breakdown set and, after `sub_zero`, in the ball, contradicting N9. Follow `Section4/R41/NonDensityL1.lean:105-111` line by line; `Paper1/PeriodicMain.lean:32-39` has the same separation contradiction. This proof does not consume N6/N7, but the full nine-field API does.

**Size, model:** S, codex-sol. **Deps:** N4,N9,hc; not N7.

**N11 — threshold value** (transport; lane M). New module: `Section3/T21/Main.lean`.

Target (verbatim, `Spec.lean:483`):
```lean
  thresholdValue : criticalOrder 1 = (1 : ℝ) / 2
```

Route. Reuse `Section3/T19/Bookkeeping.lean:55` verbatim through the canonical/registered definition; no density witness needed.

**Size, model:** S, codex-sol. **Deps:** proved T19 U1.

**N12 — zero initial class** (transport; lane Z). New module: `Section3/T21/Zero.lean`.

Target (verbatim, `Spec.lean:496`):
```lean
  zeroInitialClass : (fun _ : Space ↦ 0) ∈ initialClassT
```

Route. Already proved as `Section3/T20/CriticalEnergy.lean:402-407` (`zero_mem_initialClassT`), contrary to the older reconciliation N12 status. Transport with `Bindings/TorusLocalTheory.lean:61` (`initialClassT_eq`). If that import makes a small helper unnecessarily heavy, reproduce the six-line constant/periodic/divergence proof against `Contracts/V1/TorusLocalTheory.lean:97`; do not move or edit the existing module in this planning lane.

**Size, model:** S, codex-sol. **Deps:** proved T20 zero datum lemma or the registered definition; no T20 U13.

**N13 — fixed initial density** (transport; lane M). New module: `verification/Bindings/TorusMain.lean` (registered assembly destination).

Target (verbatim, `Spec.lean:514`):
```lean
  fixedInitialDensity :
    ∀ a : SpatialField, a ∈ initialClassT →
      ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
        ∀ s : ℝ, s < 1 / 2 →
          RelativelyDenseT 1 s forceClassT (breakdownSetT ν a T)
```

Route. Take the threaded density record field verbatim: `research/T19/Spec.lean:207-211`, copied at T21 `Spec.lean:130-134`. Preserve a-first binders. Follow paper `03-torus.tex:523`; T19 absorbs insertion, so T21 does not consume T18 directly.

**Size, model:** S, codex-sol. **Deps:** threaded PeriodicDensityAPI.fixedInitialDensity; closed supplier waits for T19 density/registration.

**N14 — zero-datum density iff subcritical** (bookkeeping; lane M). New module: `verification/Bindings/TorusMain.lean`.

Target (verbatim, `Spec.lean:536`):
```lean
  zeroInitialDensityIff : ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T → ∀ s : ℝ,
    RelativelyDenseT 1 s forceClassT (breakdownSetTZero ν T) ↔ s < 1 / 2
```

Route. Backward: specialize N13 at zero using N12 and unfold `breakdownSetTZero` (`Spec.lean:203`). Forward: if s is not < 1/2, `le_of_not_lt` feeds N10, contradicting density. `Paper1/PeriodicMain.lean:44-53` is the exact order argument; R41 `NonDensityL1.lean:105` supplies its negative half, and `Contracts/V1/MainThresholds.lean:40` records the whole-space iff shape. No nonzero-datum converse is claimed.

**Size, model:** S, codex-sol. **Deps:** N12,N13,N10; may prove now against threaded density and NonDensityAPI.

**N15 — explicit zero-datum non-density** (bookkeeping; lane M). New module: `verification/Bindings/TorusMain.lean`.

Target (verbatim, `Spec.lean:557`):
```lean
  zeroInitialNonDensity : ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
    ∀ s : ℝ, 1 / 2 ≤ s →
      ¬ RelativelyDenseT 1 s forceClassT (breakdownSetTZero ν T)
```

Route. Apply `NonDensityAPI.nonDensity` (`Spec.lean:430`) with ν,s,T reordered to ν,T,s. This is the negative assertion named by paper `03-torus.tex:523`; keep it even though N14 implies it. R41 `NonDensityL1.lean:105-111` supplies the parallel negative result.

**Size, model:** S, codex-sol. **Deps:** N10 or threaded NonDensityAPI.nonDensity.

**A — assembly + Nonempty statements + contract/bindings/tests** (assembly/registration; lane A). New modules: `Section3/T21/Assembly.lean` for canonical packaging as needed; proposed `Contracts/V1/TorusNonDensity.lean`, `Contracts/V1/TorusMain.lean`, corresponding `Bindings/` and new `Tests/` modules. Final names/registry IDs are selected by the registration owner.

Targets (verbatim arrow-type definitions, `Spec.lean:595,602,613`):

```lean
def nonDensityOfCritical : Prop :=
  ∀ K : NSFormalization.Section3.T20.CriticalRegularityTAPI, NonDensityAPI K.c
```

```lean
def mainOfDensityAndNonDensity : Prop :=
  ∀ c : ℝ,
    BlowupDensity.T19.PeriodicDensityAPI → NonDensityAPI c → MainTheoremAPI
```

```lean
def mainOfInputs : Prop :=
  BlowupDensity.T19.PeriodicDensityAPI →
    NSFormalization.Section3.T20.CriticalRegularityTAPI →
      MainTheoremAPI
```

Prove inhabitants of these propositions under fresh theorem names (the Spec names are definitions of Prop, not existing constructors). Assemble all nine fields from N0–N10 and all five from N11–N15. Extract `nonDensityStatement` (`Spec.lean:436-438`) from `.nonDensity` and `mainStatement` (`:570-577`) as the conjunction of `.fixedInitialDensity` and `.zeroInitialDensityIff`.

With closed upstream witnesses obtain `Nonempty (NonDensityAPI K.c)` and `Nonempty MainTheoremAPI`, plus the two unconditional paper statements. For a witness-independent non-density package use `∃ c, Nonempty (NonDensityAPI c)`; do not claim `∀ c, Nonempty (NonDensityAPI c)`. These are additional non-vacuity checks, not replacements for the two Spec statement defs.

Route. `Spec.lean:637-643` verifies the only nondefinitional seam; `Paper1/PeriodicCriticalRegularity.lean:99-110` and `Paper1/PeriodicMain.lean:59-73` model two-input assembly but retain their own vocabulary and premises. Reuse their argument, not an unproved equivalence between force/lifespan representations. Replace the copied T19 record with its single registered source; move the *use* of the existing lifespan bridge to Bindings. Every local restated definition gets a drift bridge; contracts never import Bindings or canonical implementation modules outside permitted policy. Supply exact nine/five-field type probes, zero and critical-order specialization probes, the three assembly types, both statement types, and transitive axiom audits (`propext`, `Classical.choice`, `Quot.sound` only). Add registry entries and run `make check`, targeted builds, `make test`, and mutation checks from the prescribed environment; no changes to existing frozen contracts/tests.

**Size, model:** M, codex-sol. **Deps:** every N; final registration gated on **T19 → T20 → T21** and inhabited upstream APIs. Conditional assembly may be prepared earlier; it is not completion of this unit.

## 2. Dependency ledger

Pending source-verified field-level ledger. Separate proofs with threaded records from closed registered witnesses.

## 3. Waves

At most three concurrent lanes. Start independent helpers and parameterized assembly before upstream registration; closed assembly waits for suppliers.

## 4. Risks

Resolve Prop-versus-Type with owner; preserve registration order T19 → T20 → T21 and the lifespan bridge in Bindings. N6 is a real analytic obligation, shared with T18 U11 lane 445. Verify lane 428 critLower before assigning N3.
