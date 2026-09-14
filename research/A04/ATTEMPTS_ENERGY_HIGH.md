# ATTEMPTS — lane 128 (A04 unit G1 assembly: eq:Rhigh `energyIdentityHigh`)

Target: `research/A04/Spec.lean:424-434` field `energyIdentityHigh`
(manuscript eq:Rhigh, `paper/sections/appendix-a-local-theory.tex:132-137`).
Deliverable: `formalization/NSFormalization/Section4/A04/EnergyIdentityHigh.lean`.

## What was built (no analytic gap — assembly + bookkeeping only)

* `def Chigh (m : ℕ) : ℝ := A03.outerTameConst m`; `Chigh_pos m := A03.outerTameConst_pos m`.
  The probe's core uses `outerTameConst m` directly (`= 6·vectorTameConst m`), so `Chigh` is
  defined to that constant.
* `energyIdentityHigh_core` — the lane-121 reviewer's reconstruction
  (`research/A04/probes/energy_identity_high_probe.lean`, itself `REVIEW_HPR.md` §5 +
  appendix D) **promoted verbatim** into namespace `NSFormalization.Section4.A04`.  Credit
  in the docstring.  Stated with `outerTameConst m` (verbatim).
* `energyIdentityHigh` — the spec field **token-for-token** in formalization vocabulary, with
  `Chigh m` in the RHS.  Proved `by intro …; exact energyIdentityHigh_core hν hf w hpath m hm ht`.
  `Chigh` is a plain (reducible-by-default) `def`, so `Chigh m` unfolds to `outerTameConst m` and
  `exact` closes the goal by defeq — no `simp only [Chigh]` / `show` needed (tried the bare `exact`
  first, it worked).

## Paths tried / decisions

1. **`HasSmoothSobolevPath` — no restatement needed.**  The briefing said to restate it in the new
   module *if* it lives only in `Spec.lean`.  It does not: it is a formalization def at
   `formalization/NSFormalization/Section4/A04/DerivNorm.lean:87` (the same `def` Spec.lean:247
   mirrors).  So the module just imports `A04.DerivNorm` and uses it unqualified inside the A04
   namespace.  Likewise `sobolevNormAt` (`A04/Forcing.lean:74`), `gradientSobolevNormAt`
   (`A04/LaplacianDatum.lean:86`), `MemForceR` (`D01/ForceClass.lean:158`), `initialClassR`
   (`A02/SolutionClass.lean:97`), `ClassicalSolutionR` (A02) all live in formalization modules —
   none required restating.  The opens mirror the probe's exactly (`A02 (SpaceTimeField SpatialField
   ClassicalSolutionR MemHInfty initialClassR)`, `D01`, `Paper3 (RealVectorSobolev)`,
   `A03 (outerTameConst MemHmVector)`, `open scoped ContDiff RealInnerProductSpace`), with
   `initialClassR` added to the A02 list for the spec-shaped theorem.
2. **`import A03.OuterTameProduct` added explicitly** even though it is already in the closure via
   `A04.HighEnergy` (`import NSFormalization.Section4.A03.OuterTameProduct`), because `Chigh`/`Chigh_pos`
   name `A03.outerTameConst`/`A03.outerTameConst_pos` directly.

## Which spec-field hypotheses are load-bearing in the core

| hypothesis | load-bearing? | where / why |
|---|---|---|
| `0 < ν` | **yes** (not tight) | only as `le_of_lt hν` → `inner_energy_Rhigh`'s `hν : 0 ≤ ν`; mathematically `0 ≤ ν` suffices, kept `0 < ν` for spec fidelity |
| `a ∈ initialClassR` | **no** | unused on this route; carried in the spec-shaped theorem for fidelity only (matches `REVIEW_HPR.md` finding 13 / probe docstring) |
| `MemForceR f` | **yes** | `exists_isSobolevDatum_pressureGradient_slice w hf …`, `hf.2 m` (force datum), `momentum_datum w hf …`, `pressure_drop w hf …` |
| `HasSmoothSobolevPath T w.velocity` | **yes** | `obtain ⟨G, hGd, hGc⟩ := hpath m` — the datum path, the whole differentiability input |
| `3 ≤ m` | **yes** (not tight) | only via `have hm2 : 2 ≤ m := by omega`; this route needs only `m ≥ 2`, kept `3 ≤ m` per manuscript `:129` |
| `t ∈ Ioo 0 T` | **yes** | slice data (`ht`), and `ht' : t ∈ Ico 0 T` for the datum path evaluations |

So only `a ∈ initialClassR` is genuinely unused; it and the slack in `0 < ν`/`3 ≤ m` are kept
because the spec states them (do not drop from the field statement).

## Failures

None.  The core promoted verbatim and compiled first try; the spec-shaped wrapper closed with a
bare `exact`; the conformance file elaborated; `make check` passed.  (No `sorry`/`admit`/`axiom`/
`native_decide`/`maxHeartbeats`/`set_option` anywhere.)

## Two stale probe imports fixed (lane-121 leftovers)

`research/A04/probes/hpr_probe1.lean:2` and `hpr_probe2.lean:2` imported
`NSFormalization.Section4.A04.RealPairing`, which lane 123 moved to `D01.RealPairing`
(the A04 copy is gone).  Both now `import NSFormalization.Section4.D01.RealPairing`; both compile
silently under `lake env lean` (exit 0).

## What the A04 partial contract should register next

There is **no** registered A04 partial contract yet (A04 appears only in other contracts' "NOT
asserted" clauses).  The field is **contract-ready**: `energyIdentityHigh` is token-identical to
`Spec.lean:424-434`.  A follow-up SPEC/contract lane should:

* add a new `Contracts/V1/EnergyHighPartial.lean` (shaped like `Contracts/V1/EnergyAbsorptionPartial.lean`):
  a constant field `Chigh : ℕ → ℝ` with `Chigh_pos : ∀ m, 0 < Chigh m`, and the `energyIdentityHigh`
  field restated in Contracts.V1.Data vocabulary token-for-token;
* bind it in `Bindings/` with `Chigh := A04.Chigh`, `energyIdentityHigh := A04.energyIdentityHigh`
  (moving the solution across the two `ClassicalSolutionR` copies field-by-field via the existing
  `Bindings.uniqueness_toA02`, as `EnergyAbsorptionPartial`'s `velocityJets` does; `Chigh_eq :
  Contract.Chigh = A04.Chigh := rfl` as the drift bridge, and `sobolevNormAt`/`gradientSobolevNormAt`/
  `HasSmoothSobolevPath` bridged by rfl since their field types are defeq);
* add a `Tests/` module asserting standard-three axioms.
