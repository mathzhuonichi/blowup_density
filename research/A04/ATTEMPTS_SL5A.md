# SL5 row 5a — attempts / route (lane 100)

**Goal.** Divergence-free pointwise divergence form of the advection term, in the
exact shape row 5c consumes: `(u·∇)u(t,·) = ∑ⱼ ∂ⱼ(u_j·u)` as functions of `x`,
`z := u(t,·)`.

**Module.** `formalization/NSFormalization/Section4/A04/AdvectionDivergence.lean`.

## Route taken (worked first try)

1. **Bridge (step i), was `rfl`.** `convectionDivergence_eq_sum_partialDeriv_outerColumn`
   `: convectionDivergence u t x = ∑ j, partialDeriv j (outerColumn z z j) x` closed by
   `rfl`. Reason it is definitional: unfolding
   `partialDeriv j v x = spatialDerivative (lift v) 0 x eⱼ = fderiv ℝ (fun y => v ((0,y).2)) x eⱼ`
   (`(0,y).2` reduces to `y` by iota, then eta) gives `fderiv ℝ v x eⱼ`; with
   `v = outerColumn z z j = fun x' => (z x' j) • z x'` and `z = fun y => u(t,y)`, each
   summand beta-reduces to `fderiv ℝ (fun y => (u(t,y) j) • u(t,y)) x eⱼ`, which is exactly
   lane 093's `convectionDivergence` summand (`ConvectionDivergence.lean:60-62`). No
   `Finset.sum_congr`/`funext` needed — the two `fun j => …` bodies are defeq uniformly in `j`.
2. **Row 5a proper.** `advection_eq_sum_partialDeriv_outerColumn`, function identity:
   `funext x; rw [← convectionDivergence_eq_advection u t x (hdiff x) (hdiv x)]; exact (bridge) x`.
   Reuses lane 093's divergence-free specialization `convectionDivergence_eq_advection`
   (`ConvectionDivergence.lean:113`, hyps `DifferentiableAt ℝ (fun y => u(t,y)) x` and
   `spatialDivergence u t x = 0`) — the Leibniz rule was NOT re-proved.
3. **`ClassicalSolutionR` corollary.** `advection_slice_eq_sum_partialDeriv_outerColumn`.
   Space-differentiability of the slice from `contDiff_slice w.velocity_smooth ht`
   (`D01/DatumToJets.lean:366`) → `.differentiable (by simp)` (`1 ≤ ∞` side goal, same
   `by simp` the codebase uses, e.g. `TimeDerivative.lean:204`) → `.differentiableAt` per
   point; divergence directly from `w.divergence t ht`.

## Failed approaches

None. The three declarations went in on the first compile; `rfl` for the bridge was the
first thing tried and it closed. No `simp only [convectionDivergence, partialDeriv,
outerColumn, lift, spatialDerivative]` fallback was needed, no `maxHeartbeats` bump.

## Types / reuse notes

- `SpaceTimeField` (A02, `SolutionClass.lean:67`) is `abbrev … := VelocityField`, so passing
  `u : SpaceTimeField` where lane 093's `VelocityField`-typed lemmas expect an argument is
  reducible-defeq and needs no coercion.
- No definition was restated. Imports: `A01.ConvectionDivergence`, `A03.OuterTameProduct`,
  `A02.SolutionClass`, `D01.DatumToJets`.

## Commands / results

- `lake build NSFormalization.Section4.A04.AdvectionDivergence` → `✔ Built … (3.1s)`,
  `Build completed successfully`. (Warnings printed are all *replayed* from unrelated
  upstream modules, none from this file.)
- `lake env lean ../formalization/NSFormalization/Section4/A04/AdvectionDivergence.lean` →
  silent, exit 0.
- `lake env lean ../research/A04/axioms_sl5a.lean` → each of the three public declarations
  `depends on axioms: [propext, Classical.choice, Quot.sound]`, exit 0.
