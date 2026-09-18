# REPORT — lane 398 (T24a / Ua3): the `momentum` field of `AffineVariationAPI` (`eq:affine` ①)

## 1. What was proved
The `eq:affine` momentum obligation of `prop:affine` (whole space, raw packet fields): for the
Theorem 1.1 packet `(U,P,F)` and any admissible perturbation `b`, the affine velocity `U+b` with
the packet pressure `P` solves the forced Navier–Stokes equation with the six-term modified force
`F̃ = F + ∂ₜb − νΔb + (U·∇)b + (b·∇)U + (b·∇)b`, at every interior time `t ∈ (0,1)`.

Exact statement (`NSFormalization.Section3.T24.momentum`):
```
theorem momentum {ν : ℝ} {U F : VelocityField} {P : PressureField}
    (c : Space) (r τ₀ τ₁ : ℝ)
    (hvelocity_smooth : ContDiffOn ℝ ∞ U preSingularDomain)
    (hnavier_stokes : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x : Space,
        NavierStokesR3.ProblemStatement.navierStokesResidual ν U P t x = F (t, x)) :
    ∀ b : VelocityField, AffineAdmissible c r τ₀ τ₁ b →
      ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x : Space,
        NavierStokesR3.ProblemStatement.navierStokesResidual ν
            (affineVelocity U b) (affinePressure P) t x =
          affineForce ν U F b (t, x)
```
The two hypotheses are exactly the `PacketAPI` fields `velocity_smooth` and `navier_stokes`; there
is **no named input, no pressure-smoothness hypothesis, no placeholder**. Route as briefed: the
six-term residual expansion via bilinearity of advection and the packet's `navier_stokes` clause.

Supporting lemma (`NSFormalization.Section3.T24.navierStokesResidual_affine_expand`):
```
navierStokesResidual ν (affineVelocity U b) (affinePressure P) t x =
  navierStokesResidual ν U P t x + temporalDerivative b t x − ν • spatialLaplacian b t x
    + crossAdvection U b t x + crossAdvection b U t x + crossAdvection b b t x
```
(given interior differentiability of the `U`- and `b`-slices).

## 2. What exists in Lean now
- `formalization/NSFormalization/Section3/T24/AffineMomentum.lean` (namespace
  `NSFormalization.Section3.T24`): **imports the T24a affine vocabulary** (`affineCylinder`,
  `AffineAdmissible`, `crossAdvection`, `affineVelocity`, `affinePressure`, `affineForce`) from the
  canonical `NSFormalization.Section3.T24.AffineBasics` (lane 392, PR #357), and adds the expansion
  lemma `navierStokesResidual_affine_expand` and `momentum`.
  Builds with 0 errors; both theorems print exactly `[propext, Classical.choice, Quot.sound]`.
  Reuses the vendored `NavierStokes.ResidualCalculus` operator-algebra lemmas
  (`temporalDerivative_add`, `advection_add`, `spatialLaplacian_add`) and interior-smoothness
  helpers (`temporal_differentiable_of_presingular_smooth`, `spatial_contDiff_of_presingular_smooth`)
  and the registered residual `NavierStokes.R3.ProblemStatement.navierStokesResidual`
  (defeq to `Contracts.V1.navierStokesResidual`, verified by `rfl`).
- `research/T24/probes/affine_momentum_closes.lean`: restates the affine vocabulary in the
  **registered** `Contracts.V1` vocabulary and discharges the `AffineVariationAPI.momentum`
  obligation on the selected packet `Bindings.packet ν hν` (`momentum_on_canonical`), feeding the
  packet's own `velocity_smooth`/`navier_stokes`. Non-vacuity: `zero_admissible` (`b=0` admissible ⇒
  admissible class inhabited), `affineVelocity_zero`/`affineForce_zero` (`b=0` recovers `(U,P,F)`, so
  `momentum` specializes to the packet PDE — non-tautological). All four decls print
  `[propext, Classical.choice, Quot.sound]`.
- `research/T24/probes/affine_momentum_nonzero.lean`: a concrete **nonzero** admissible witness
  `bWitness := spatialCurl A` for `A(t,x) = θ(t) φ(x) e₁` (`θ`, `φ` `ContDiffBump`s) on the cylinder
  `ball 0 1 × (1/4, 3/4)`. Proves `bWitness_admissible : AffineAdmissible 0 1 (1/4) (3/4) bWitness`
  (smooth via `contDiff_spatialCurl`; compact support via `spatialCurl_tsupport_subset`; support in
  the cylinder; `∇·b = 0` via `spatialDivergence_spatialCurl`), `bWitness_ne_zero` (if `∇×A ≡ 0`
  then `∂₃φ ≡ 0`, so `φ` is constant along the `e₃`-line through `0`, forcing `φ ≡ 0` against
  `φ(0)=1`), and `nonzero_admissible_momentum` (the proved `momentum` at this witness on the
  registered packet). This is the single-bump witness of unit **Ua7**. All three print
  `[propext, Classical.choice, Quot.sound]`.
- `research/T24/axioms_ua3.lean`: transitive-axiom audit for the two module theorems, with a note
  pointing to the nonzero-witness self-audit in the probe.

## 3. Gap
- None blocking `momentum`. The registered field is discharged on the canonical packet, and the
  admissible class contains an explicit nonzero element. The full `infinite_dimensional` field
  (Ua7: a countable `ℝ`-linearly independent admissible family from disjoint balls) is a separate
  T24a unit; this lane delivers the single-bump witness it builds on. No residual lemma about
  `momentum` is left open, and everything attempted compiles (no error text).

## 4. Commands and results
- `cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T24.AffineMomentum`
  → `Build completed successfully (2617 jobs).` (0 errors)
- `cd verification && lake env lean ../formalization/NSFormalization/Section3/T24/AffineMomentum.lean`
  → no output (0 errors)
- `cd verification && lake env lean ../research/T24/probes/affine_momentum_closes.lean`
  → all four `#print axioms` = `[propext, Classical.choice, Quot.sound]`
- `cd verification && lake env lean ../research/T24/axioms_ua3.lean`
  → `navierStokesResidual_affine_expand` and `momentum` both = `[propext, Classical.choice, Quot.sound]`
- `make check` → EXIT 0 (contract architecture + policy + work-queue checks all pass)

## Addendum (follow-up: import AffineBasics from lane 392)
After lane 392 (PR #357) merged `Section3/T24/AffineBasics.lean` into
`origin/erenup/integration-section3`, I merged the integration branch into this
worktree (no conflicts) and replaced the in-module restated affine vocabulary by
`import NSFormalization.Section3.T24.AffineBasics`, deleting my six duplicate defs.
**All six of 392's definitions are definitionally identical to the ones this lane
needs after the registered field/scalar aliases** — 392 spells the fields as
`VelocityField`/`PressureField` while `research/T24/Spec.lean` uses
`SpaceTimeField`/`SpaceTimeScalar`, which are definitionally equal
(`Contracts/V1/Data.lean:104-108`) — same namespace `NSFormalization.Section3.T24`,
same signatures and bodies, so the `momentum` and `navierStokesResidual_affine_expand`
proofs are unchanged. 392 additionally supplies `affineCkSeminorm` and the Ua1 kinematic
theorems (`radius_pos`, `window`, `zero_initial`, `late_agreement`, `distinct`),
none of which collide with this module. Re-ran all gates after the switch:
- `lake build NSFormalization.Section3.T24.AffineMomentum` → `Build completed successfully (3007 jobs).`
- `lake env lean` on module / probe / axioms_ua3 → 0 errors; every decl `[propext, Classical.choice, Quot.sound]`
- `make check` → EXIT 0
The probe keeps its own `BlowupDensity.T24.Probe` restatement in the registered
`Contracts.V1` vocabulary (a different namespace, no collision).
