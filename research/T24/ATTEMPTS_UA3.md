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

## Gap (documented, not stubbed)
- A **nonzero** admissible `b` (smooth, compactly supported inside the cylinder, divergence-free)
  is the curl-bump construction of unit **Ua7**
  (`NavierStokes.SpatialCurl.spatialDivergence_spatialCurl` gives `∇·(∇×A)=0`, plus a compactly
  supported vector potential and a time bump in `(τ₀,τ₁)`). Constructing it here would duplicate
  Ua7, so it is not done. `momentum` is `∀ b` admissible and fully proved, so it consumes whatever
  witness Ua7 produces; the probe covers `b=0` admissibility and the `b=0`⇒packet-PDE reduction.
