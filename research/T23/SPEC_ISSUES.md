# T23 (`cor:boundary`) — specification issues and lead rulings

## G0 — `boundaryInsertionStatement` quantifies an arbitrary cutoff (lane 449 audit, lead ruling 2026-09-19 15:55Z)

- **Finding (lane 449, `T23_SPLIT.md` §0/§4).** `research/T23/Spec.lean:1037-1050` universally quantifies a raw `D : CutoffData` (seven data fields, no compatibility or positivity hypothesis) and concludes `Nonempty (BoundaryInsertionAPI … D …)`, whose fields `eps_pos`/`eps_time` require `0 < D.ε₀`. With `D.ε₀ = 0` the statement is unsatisfiable for admissible data: a false universal, not a missing proof. `RECONCILIATION.md` §3 intended the cutoff to be *the* cutoff of the consumed correction (I02/I03 route), but the Spec quantifies it independently. Raw `r` is likewise unconstrained.
- **Ruling (lead).** Same pattern as T17 G4/G5: the statement is repaired at the canonical level, the reconciled record is unchanged. Lane U2 (477) formalises the counterexample (`not_boundaryInsertionStatement` for the literal Spec statement, or the exact false instance) and states the repaired statement `boundaryInsertionStatement'` that **existentially** produces the cutoff/correction from the consumed whole-space correction (`∃ D, … ∧ Nonempty (BoundaryInsertionAPI … D …)`), with `0 < r` and the ball hypotheses spelled out — mirroring `Section3/T17/Assembly.lean:correctionStatementAmended`. Registration (U9) uses the repaired statement; the V1 wording amendment is **owner-pending** (same list as T17 G4).
- **Owner-pending decisions blocking registration (from `T23_SPLIT.md` §4).** Domain record placement (`ClassicalSolutionOmega` canonical location / registration), smooth-domain encoding (regular-level domains + boxes), gauge/scope of the no-slip corollary. Wave-0/1 proof units do not depend on these; only U9 does.

## Wave-0 lanes opened 2026-09-19 (lead)
- 476 U1 (geometry, sol), 477 U2 (local correction supplier + G0 counterexample/repair, astra), 478 U7 (domain no-slip uniqueness, astra). T23 is not on the `thm:main` critical path (T21); it runs alongside.

## G1 — smooth-domain boundary IBP (lane 478 continuation, 2026-09-19)

**Box U7 is proved.** `noSlip_uniqueness_box` uses exactly `IsBoxDomain Ω`
and the original viscosity, data, force, solution and common-time binders.
The weaker assumptions `IsOpen Ω` and boundedness are derived from the box.
`ibp_box` transfers the existing closed coordinate-box identity to the Spec's
open Euclidean box, including the null boundary, coordinate derivative chain
rule and no-slip factor on `frontier Ω`.

**The sole remaining analytic theorem for unrestricted U7 is the following.**
This is an unproved statement, not an axiom or declaration in delivered Lean:

```lean
∀ (Ω : Set Space), IsOpen Ω → Bornology.IsBounded Ω →
  IsRegularLevelDomain Ω → IBP Ω
```

The one named identity is defined in `Section3/T23/DomainSolution.lean`:

```lean
def IBP (Ω : Set Space) : Prop :=
  ∀ (f g : Space → ℝ),
    (∀ x ∈ closure Ω, ContDiffAt ℝ 1 f x) →
    (∀ x ∈ closure Ω, ContDiffAt ℝ 1 g x) →
    (∀ x ∈ frontier Ω, f x = 0) → ∀ j : Fin 3,
    (∫ x in Ω, f x * fderiv ℝ g x (coordinateVector j)) =
      -(∫ x in Ω, fderiv ℝ f x (coordinateVector j) * g x)
```

The pressure field need not vanish on the boundary: the first scalar factor is
a component of the no-slip difference. The transport and viscous identities
are proved consequences of the same scalar identity. No connectedness or
pressure equality is assumed. `noSlip_uniqueness_of_ibp` proves the complete U7
velocity conclusion under this explicit identity, authorized in the continuation
request. It derives energy differentiation, both cancellations, viscous
negativity, the compact-subslab convection bound, and Grönwall from the original
solution fields. Thus an energy-identity premise is not hidden in `IBP`.

**Mathlib search evidence.** Repeated the following full-tree search on the
pinned dependency; inspected the returned theorem statements with `sed -n`:

```sh
grep -rnEi 'theorem.*(divergence|stokes)|integral.*(regularLevel|regular_level)' \
  verification/.lake/packages/mathlib/Mathlib --include='*.lean'
sed -n '260,345p' verification/.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/DivergenceTheorem.lean
sed -n '252,278p' verification/.lake/packages/mathlib/Mathlib/Analysis/BoxIntegral/DivergenceTheorem.lean
```

The relevant hits were:

- `MeasureTheory/Integral/DivergenceTheorem.lean:266`,
  `integral_divergence_of_hasFDerivAt_off_countable`: integrates on `Icc a b`
  in coordinate space and has face integrals as boundary terms.
- The variant at `:296` changes the vector-field spelling; `:313`,
  `integral_divergence_of_hasFDerivAt_off_countable_of_equiv`, still integrates
  on an order interval and requires an order-compatible, volume-preserving
  continuous linear equivalence. It is not a regular-level-domain theorem.
- The remaining hits in that file (`:427`, `:482`, `:503`, `:550`) concern
  two-dimensional products of intervals.
- `Analysis/BoxIntegral/DivergenceTheorem.lean:265`,
  `hasIntegral_GP_divergence_of_forall_hasDerivWithinAt`, is likewise a theorem
  on `Box.Icc I`, for the Henstock–Kurzweil-style box integral.
- The Cauchy integral file only points back to the box divergence theorem.

No directly applicable regular-level-domain divergence/IBP theorem was found.
This records search evidence, not a claim that no alternative proof can exist.
A future proof of the displayed residual and the domain-class case split would
close unrestricted `noSlip_uniqueness`. That declaration is deliberately absent.
The lead/owner still decides whether V1 registers only the proved box branch.
