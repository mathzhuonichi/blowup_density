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
  `NSFormalization.Section3.T24`): the T24a raw-field affine vocabulary restated verbatim from
  `research/T24/Spec.lean:961-990` (`affineCylinder`, `AffineAdmissible`, `crossAdvection`,
  `affineVelocity`, `affinePressure`, `affineForce`), the expansion lemma, and `momentum`.
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
- `research/T24/axioms_ua3.lean`: transitive-axiom audit for the two module theorems.

## 3. Gap
- A concrete **nonzero** admissible `b` (smooth, compactly supported in the cylinder,
  divergence-free, nonzero) is **not** constructed here: it is the curl-bump construction of unit
  **Ua7** (`NavierStokes.SpatialCurl.spatialDivergence_spatialCurl` for `∇·(∇×A)=0`, a compactly
  supported vector potential, a time bump in `(τ₀,τ₁)`). Reproducing it in Ua3 would duplicate Ua7,
  so the probe's non-vacuity covers only `b=0`. Because `momentum` is `∀ b` admissible and fully
  proved, it consumes any nonzero witness Ua7 delivers — no residual lemma about `momentum` is left
  open. There is no error text: everything attempted compiles.
- The canonical `Section3/T24/AffineBasics.lean` (lane 392) had not landed on this base, so the
  affine vocabulary is restated in-module; the assembly lane must deduplicate against 392's copy
  (identical definitions, same names/namespace).

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
