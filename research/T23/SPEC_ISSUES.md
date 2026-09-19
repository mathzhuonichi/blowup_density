# T23 (`cor:boundary`) — specification issues and lead rulings

## G0 — `boundaryInsertionStatement` quantifies an arbitrary cutoff (lane 449 audit, lead ruling 2026-09-19 15:55Z)

- **Finding (lane 449, `T23_SPLIT.md` §0/§4).** `research/T23/Spec.lean:1037-1050` universally quantifies a raw `D : CutoffData` (seven data fields, no compatibility or positivity hypothesis) and concludes `Nonempty (BoundaryInsertionAPI … D …)`, whose fields `eps_pos`/`eps_time` require `0 < D.ε₀`. With `D.ε₀ = 0` the statement is unsatisfiable for admissible data: a false universal, not a missing proof. `RECONCILIATION.md` §3 intended the cutoff to be *the* cutoff of the consumed correction (I02/I03 route), but the Spec quantifies it independently. Raw `r` is likewise unconstrained.
- **Ruling (lead).** Same pattern as T17 G4/G5: the statement is repaired at the canonical level, the reconciled record is unchanged. Lane U2 (477) formalises the counterexample (`not_boundaryInsertionStatement` for the literal Spec statement, or the exact false instance) and states the repaired statement `boundaryInsertionStatement'` that **existentially** produces the cutoff/correction from the consumed whole-space correction (`∃ D, … ∧ Nonempty (BoundaryInsertionAPI … D …)`), with `0 < r` and the ball hypotheses spelled out — mirroring `Section3/T17/Assembly.lean:correctionStatementAmended`. Registration (U9) uses the repaired statement; the V1 wording amendment is **owner-pending** (same list as T17 G4).
- **Owner-pending decisions blocking registration (from `T23_SPLIT.md` §4).** Domain record placement (`ClassicalSolutionOmega` canonical location / registration), smooth-domain encoding (regular-level domains + boxes), gauge/scope of the no-slip corollary. Wave-0/1 proof units do not depend on these; only U9 does.

## Wave-0 lanes opened 2026-09-19 (lead)
- 476 U1 (geometry, sol), 477 U2 (local correction supplier + G0 counterexample/repair, astra), 478 U7 (domain no-slip uniqueness, astra). T23 is not on the `thm:main` critical path (T21); it runs alongside.

## G0 addendum — lane 477 (checked partial, 2026-09-19)

`research/T23/probes/g0_counterexample.lean` contains a verbatim copy of the
original Spec (including literal `boundaryInsertionStatement`), followed by
the exact false-instance theorem below. It does **not** refute a surrogate API.
No admissibility assumption is needed to refute an API instance whose cutoff
threshold is zero; this is the lead-authorised exact-instance alternative,
not a claimed proof of `¬ boundaryInsertionStatement`.

The repaired declaration existentially chooses the consumed correction `C` and
all seven matching cutoff fields. Its positive radius and both closed-ball
inclusions are explicit. It is a **definition only**, with proof left open.
Its full-slab agreement on the requested inner ball will require spatial
extension from a larger interior ball; the proved U2 window extension agrees
on a smaller ball and is used for the quantitative local construction.

**Location gap:** the exact literal/repaired declarations remain in the research
probe, because the contract-free implementation tree has no canonical
`BoundaryInsertionAPI`/`ClassicalSolutionOmega` at this snapshot. The search
`grep -rnE 'structure BoundaryInsertionAPI|def boundaryInsertionStatement|structure ClassicalSolutionOmega' formalization/NSFormalization verification/Contracts --include='*.lean'`
returned no matches. We did not create a competing placement or domain API.
`Section3/T23/StatementRepair.lean` exports the actual raw zero cutoff and its
threshold obstruction only; moving the full literal and repaired declaration
there remains an explicit unfinished deliverable, not a claimed completion.

Exact checked Lean text (namespace `BlowupDensity.T23.Spec`, opening
`Set MeasureTheory`, `BlowupDensity.Contracts.V1`, its `Data` namespace,
`BlowupDensity.T16.Draft`, and `BlowupDensity.T22.Draft`):

```lean
theorem boundaryInsertionAPI_zero_cutoff
    (ν : ℝ) (P : PacketImportAPI ν) (place : DomainPlacementData P.toPacketAPI)
    (Ω : Set Space) (norms : BoundedDomainNormAPI)
    (a : SpatialField) (g : SpaceTimeField) (r δ : ℝ)
    (D : CutoffData) (reference : ClassicalSolutionOmega ν Ω a g (place.T + δ))
    (hD : D.ε₀ = 0) :
    ¬ Nonempty (BoundaryInsertionAPI ν P place Ω norms a g r δ D reference) := by
  rintro ⟨A⟩
  have hp := A.eps_pos
  have hl := A.eps_le_cutoff
  rw [hD] at hl
  exact (not_lt_of_ge hl) hp

/-- G0 repair at the exact Spec vocabulary. The correction is chosen jointly
with its matching whole-space supplier, whose reference agrees on the interior
cylinder. Proving existence of this supplier/extension is still U2 work. -/
def boundaryInsertionStatement' : Prop :=
  ∀ (ν : ℝ), 0 < ν → ∀ (P : PacketImportAPI ν)
    (place : DomainPlacementData P.toPacketAPI)
    (Ω : Set Space) (norms : BoundedDomainNormAPI)
    (a : SpatialField) (g : SpaceTimeField) (r δ : ℝ)
    (reference : ClassicalSolutionOmega ν Ω a g (place.T + δ)),
    IsBoundedBoxOrSmoothDomain Ω → 0 < δ → 0 < r →
      g ∈ forceClassOmega Ω → a ∈ initialClassOmega Ω →
      closure (Metric.ball place.x₀ r) ⊆ Metric.ball place.chartCenter place.chartRadius →
      closure (Metric.ball place.chartCenter place.chartRadius) ⊆ Ω →
      ∃ (C : CorrectionAPI ν P.toPacketAPI) (D : CutoffData),
        C.T = place.T ∧ C.δ = δ ∧ C.x₀ = place.x₀ ∧ C.r = r ∧
        (∀ t ∈ Ioo (0 : ℝ) (place.T + δ), ∀ x ∈ Metric.ball place.x₀ r,
          C.v (t, x) = reference.velocity (t, x)) ∧
        D.θ = C.θ ∧ D.η = C.η ∧ D.plateau = C.plateau ∧
        D.θRadius = C.θRadius ∧ D.ε₀ = C.ε₀ ∧
        D.potential = C.potential ∧ D.correction = C.correction ∧
        Nonempty (BoundaryInsertionAPI ν P place Ω norms a g r δ D reference)

```

The false-instance theorem's guarded axiom audit is exactly
`[propext, Classical.choice, Quot.sound]`. Owner approval of the V1 amendment
and U9 registration remain pending.
## G1 — no-slip uniqueness on smooth-level domains needs a divergence theorem Mathlib may lack (lane 478, lead note 2026-09-19 16:12Z)
- Lane 478 (astra) proved the canonical domain record and the box integration by parts on `Icc` in `Fin 3 → ℝ`, energy integrability, zero-energy ⇒ equality and uniform derivative bounds, but not `noSlip_uniqueness`; its search found no regular-level-domain integration-by-parts theorem in Mathlib. Lead priority for the continuation: close the **box** branch completely; expose the smooth branch's missing identity as one explicit hypothesis (`IBP Ω`) and record the exact missing theorem here. Pending that result, V1 of `cor:boundary` may register the box case only (owner decision, same list as G0).
