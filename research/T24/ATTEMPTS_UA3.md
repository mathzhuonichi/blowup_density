# Ua3 (T24a `momentum`, `eq:affine` ①) — attempts & findings (lane 398, Opus)

Target: `AffineVariationAPI.momentum` (`research/T24/Spec.lean:1047`), raw-field form.
Result: proved. Notes on route selection and the dead ends.

## What worked
- Core identity `navierStokesResidual_affine_expand`: unfold the ν-residual
  (`NavierStokesR3.ProblemStatement.navierStokesResidual`, defeq to
  `Contracts.V1.navierStokesResidual`), rewrite the three **velocity** operators with the
  vendored `NavierStokes.ResidualCalculus.{temporalDerivative_add, advection_add,
  spatialLaplacian_add}`, leave the pressure gradient of the shared `P` untouched, then
  `simp only [crossAdvection, advection, smul_add]` + `abel`.
- `(b·∇)b = crossAdvection b b = advection b` definitionally, so `advection_add`'s
  self-advection term is exactly the last `affineForce` token — after unfolding both
  `advection` and `crossAdvection` to `spatialDerivative`, `abel` matches all three
  transport terms across the two orderings.
- Interior differentiability of the packet velocity comes free from the vendored helpers
  `temporal_differentiable_of_presingular_smooth` / `spatial_contDiff_of_presingular_smooth`
  applied to `velocity_smooth`; for `b` the same helpers are fed `hb_smooth.contDiffOn`
  (`ContDiff ℝ ∞ b` ⇒ `ContDiffOn` on any set).
- Final step of `momentum`: after the expansion and `rw [hnavier_stokes …]`, both sides are
  `F(t,x) + ∂ₜb − νΔb + (U·∇)b + (b·∇)U + (b·∇)b` in the same left-assoc grouping, so `rfl`
  closes (the `(t,x).1/.2` projections reduce).

## Dead ends / corrections
1. **`Source.Insertion.corrected_background` / `residual_add` demand pressure differentiability.**
   Both split the pressure as `p + 0` internally (`pressureGradient_add … 0`), so they carry a
   `DifferentiableAt (fun y => p(t,y)) x` hypothesis. `prop:affine` keeps `P̃ = P` unchanged, so
   pressure smoothness is mathematically unnecessary (the two `∇P` cancel). Using those lemmas
   would have forced an unwanted `pressure_smooth` named input, violating "no named input".
   Resolution: expand only the velocity operators; the pressure token is literally identical on
   both sides. Hence `momentum` needs *only* `velocity_smooth` + `navier_stokes`.
2. **`NavierStokes.ResidualCalculus.navierStokesResidual_add_sub` is viscosity 1.** It expands the
   `NavierStokes.ProblemStatement.navierStokesResidual` (no ν, ν multiplies nothing), so it cannot
   produce the `− ν • Δb` term of `affineForce`. Wrote the ν-residual expansion directly instead.
3. **`simp only [affineVelocity]` does not unfold a function passed as an argument.** The generated
   equation lemma is the eta-applied point form `affineVelocity U b z = U z + b z`, which does not
   match `temporalDerivative (affineVelocity U b) t x` (no trailing `z`). Fixed with `unfold
   affineVelocity` (delta), which rewrites the function head. `affinePressure` and `crossAdvection`
   are fully applied in the goal, so `simp only` fires on them.
4. **`HasCompactSupport.zero` / `hasCompactSupport_zero` are not usable here** (`.zero` rejects the
   `M`/`α` names at this pin; `hasCompactSupport_zero` is an unknown identifier). Proved
   `HasCompactSupport (fun _ => 0)` via `tsupport (fun _ => 0) = ∅` (`simp [tsupport]`) +
   `isCompact_empty`, using `HasCompactSupport f ≡ IsCompact (tsupport f)`.

## Gap
None blocking `momentum`. The registered field is discharged on the canonical packet and the
admissible class contains an explicit nonzero element (below). The full `infinite_dimensional`
field (Ua7) — a countable `ℝ`-linearly independent admissible family — is a separate T24a unit.

## Follow-up (lane 392 AffineBasics landed)
Switched the module to `import NSFormalization.Section3.T24.AffineBasics` and deleted the six
in-module defs. 392's spellings are definitionally identical to the ones this lane needs after
the registered field/scalar aliases (392 spells `VelocityField`/`PressureField`, `Spec.lean` uses
`SpaceTimeField`/`SpaceTimeScalar`, defeq via `Data.lean:104-108`), so no proof adaptation was
needed. Gates re-run green.

## Follow-up (nonzero admissible witness, `affine_momentum_nonzero.lean`)
Built the single-bump witness (the Ua7 core) after review. `A(t,x) = θ(t) φ(x) e₁` with
`θ φ : ContDiffBump`; `b := spatialCurl A`.
- **Smooth**: `contDiff_spatialCurl` (loses one derivative; `∞ + 1 ≤ ∞` by `simp`).
- **Compact support in the cylinder**: `OscillatoryCurl.spatialCurl_tsupport_subset` gives
  `tsupport b ⊆ tsupport A`; `tsupport A ⊆ closedBall(1/2,1/8) ×ˢ closedBall(0,3/4)` (closed carrier,
  proved by `closure_minimal`), which sits inside `Ioo(1/4,3/4) ×ˢ ball 0 1` (`Icc_subset_Ioo`,
  `closedBall_subset_ball`).
- **Divergence-free**: `SpatialCurl.spatialDivergence_spatialCurl` (curl is solenoidal on a `C²`
  slice).
- **Nonzero** (the crux): if `spatialCurl A ≡ 0`, then on the plateau slice `t=1/2` (`θ(1/2)=1`)
  `curl(φ • e₁) ≡ 0`; its `e₂`-component is `∂₃φ` (`curl_component_one`, via `fderiv_smul_const` +
  `curlLinear_apply_one`), so `∂₃φ ≡ 0`; then `s ↦ φ(s • e₃)` has zero derivative
  (`is_const_of_deriv_eq_zero`), hence `φ(e₃) = φ(0) = 1`, but `‖e₃‖ = 1 > 3/4 = rOut` puts `e₃`
  outside `tsupport φ`, so `φ(e₃) = 0` — contradiction.

Pitfalls: (1) `spaceBump.contDiff` leaves the smoothness order a metavariable, so `.differentiable
(by simp)` degenerates to `¬?n = 0`; pin it with `have : ContDiff ℝ ∞ ⇑spaceBump := spaceBump.contDiff`.
(2) `rw [(HasFDerivAt.comp_hasDerivAt …).deriv]` fails to match the `fun s => φ(s•e₃)` head (it is
`⇑φ ∘ (…)`); rewrite the `deriv` hypothesis and `exact` it up to defeq. (3) `spaceBump.rOut < 1`
needs `norm_num [spaceBump]` to unfold the projection to `3/4`.
