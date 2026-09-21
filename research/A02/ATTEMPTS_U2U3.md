# A02 units U2 (`velocity_unique`) and U3 (`pressure_gauge`) — attempts

Lane 052 (stacked on 049).  New module
`formalization/NSFormalization/Section4/A02/Uniqueness.lean`.  Both fields of
`UniquenessAPI` (`research/A02/Spec.lean:263-281`) proved fully, no `sorry`.
Axiom audit `research/A02/axioms_u2u3.lean` = `propext, Classical.choice,
Quot.sound` on all four public declarations, and both verbatim conformance
`example`s typecheck.

## 1. Module structure: `Restrict` reused directly (deviation resolved)

`Uniqueness.lean` imports `A02.Energy`, `A02.Bounds`, `A02.Restrict` and
`Source.BoundedViscosityUniqueness`, and reuses `Restrict`'s
`spatialDerivative_eq_of_eqOn` / `temporalDerivative_eq_of_eqOn` (its
`section Congr`, `Restrict.lean:125,142`; `slice_eq_of_eqOn:111` is their shared
dependency) for U3's velocity-part-of-residual step.

Historical note (now moot): before lane 040 was merged, `A02/Restrict.lean` still
carried its **own** §0 restatement of the D01 objects while `Energy`/`Bounds`
used the extracted `A02/SolutionClass.lean`, so importing `Restrict` together
with `Energy`/`Bounds` was rejected (`environment already contains
'NSFormalization.Section4.A02.futureTimes' from … SolutionClass`), and I
temporarily re-proved the two generic congruence lemmas as `private` helpers.
After the lead rebased lane 052 onto the deduped `erenup/integration` (lane 040:
`Restrict.lean` imports `SolutionClass.lean`, `Energy.lean` rewired to D01), the
conflict is gone: the three modules co-import cleanly, the `private` helpers were
deleted, and the two call sites now use `Restrict`'s public lemmas.  The lemma
shapes match verbatim (`{u v : SpaceTime → Space}`, `T` a section variable
inferred as `min T₁ T₂` at the call), so no call-site adaptation was needed.

(I did **not** need `pressureGradient_sub_basepoint` / `contDiffOn_basepoint` /
`normalizePressure_gauge_invariant` — those are U4's normalization facts; U3's
gauge does not use them.  The two remaining `private` helpers in `Uniqueness.lean`,
`pressure_slice_differentiableAt` and `pressure_time_continuousOn`, are genuinely
new — no equivalent exists in `Restrict`.)

## 2. U2 `velocity_unique` — the route that worked (row U2, I2)

`velocity_unique_core`: for `t ∈ Ico 0 (min T₁ T₂)`, pick
`T' = (t + min T₁ T₂)/2` so that `0 < T'`, `t < T' < min T₁ T₂`, then apply
`Source.BoundedViscosityUniqueness.classical_uniqueness_on_Icc` on `Icc 0 T'`
and evaluate at `t ∈ Icc 0 T'`.  This *is* implication I2 (`Ico 0 (min) =
⋃_{T'<min} Icc 0 T'`) done pointwise, avoiding any set-union lemma.

Hypotheses discharged:
- smoothness `ContDiffOn … (Comparison.slab 0 T')`: `velocity_smooth.mono` /
  `pressure_smooth.mono` (`Comparison.slab 0 T' = Icc 0 T' ×ˢ univ`, abbrev, so
  `Icc 0 T' ×ˢ univ ⊆ Ico 0 Tᵢ ×ˢ univ` via `T' < Tᵢ`);
- `UniformFiniteEnergy (Icc 0 T')`: lane 049 `ClassicalSolutionR.uniformFiniteEnergy`;
- `hB0/hB`, `hG0/hG`: lane 049 `exists_velocity_bound` / `exists_gradient_bound`
  (both from `u₁`, the first argument — the theorem needs sup-bounds for one
  solution only);
- divergence on `Ioo 0 T'`: `divergence` (interval monotonicity);
- equal residuals on `Ioo 0 T'`: **`residual ν u p t x =
  NavierStokesR3.ProblemStatement.navierStokesResidual ν u p t x` by `rfl`**
  (verified: both are `temporalDerivative + advection - ν • spatialLaplacian +
  pressureGradient`), so `u₁.momentum` and `u₂.momentum` (both `= f (t,x)`)
  give equal `residual`s by a two-`rfl` `calc`;
- equal data at `t = 0`: `initial` on both, transitivity through `a`.

## 3. U3 `pressure_gauge` — the route that worked (row U3, I3)

`pressure_gauge_core` builds `c t := u₂.pressure (t,0) - u₁.pressure (t,0)` and
proves `u₂.pressure (t,x) = u₁.pressure (t,x) + c t` on `Ico 0 (min T₁ T₂)`.
The heart is that the difference `D t x = u₂.pressure (t,x) - u₁.pressure (t,x)`
is constant in `x`, in two steps.

**Interior `t ∈ Ioo 0 (min T₁ T₂)`.**
1. From `u₁.momentum`/`u₂.momentum` (both `= f`), the *full* residuals are
   equal.  U2 gives `u₁.velocity = u₂.velocity` on the slab, so the velocity
   part of the residual agrees at interior times (via `Restrict`'s
   `spatialDerivative_eq_of_eqOn`/`temporalDerivative_eq_of_eqOn`, exactly as
   `Restrict.navierStokesResidual_eq_of_eqOn` does for `advection`/`spatialLaplacian`).
   Unfolding `navierStokesResidual` and cancelling the equal velocity part with
   `add_left_cancel` yields `pressureGradient u₁.pressure t y =
   pressureGradient u₂.pressure t y` for **all** `y`.
2. `NavierStokes.PeriodicUniqueness.inner_pressureGradient`
   (`vendor/…/PeriodicUniqueness.lean:307`): `⟪w, pressureGradient p t x⟫_ℝ =
   fderiv ℝ (p-slice) x w`.  Pairing with every `w` turns equal gradients into
   equal spatial Fréchet derivatives: `fderiv (u₁.pressure-slice) y =
   fderiv (u₂.pressure-slice) y`.  (No basis/orthonormality argument needed —
   this lemma already packages it.)
3. Slice differentiability at interior `t`: `pressure_smooth.contDiffAt` at the
   interior point `(t,y)` of the slab (`Ico_mem_nhds_iff.mpr`), composed with
   `z ↦ (t,z)` (pattern copied from `R42/Assembly.lean:151-159`).
4. `fderiv (D-slice) = fderiv(u₂-slice) - fderiv(u₁-slice) = 0` (`fderiv_fun_sub`),
   and `is_const_of_fderiv_eq_zero` (Mathlib, MeanValue.lean:565) gives
   `D t x = D t 0`.

**Endpoint `t = 0`.**  `momentum` holds only on `Ioo`, so `t = 0` is a separate
continuity step (as the spec docstring and COMPARISON row U3 warn).  Fixing `x`,
the function `φ s = (D s x) - (D s 0)` is continuous on `Ico 0 (min T₁ T₂)`
(time-slices of `pressure` are `ContinuousOn` there), vanishes on
`Ioo 0 (min T₁ T₂)` by the interior step, and `0 ∈ closure (Ioo 0 (min))`, so
`𝓝[Ioo 0 (min)] 0` is `NeBot`; `tendsto_nhds_unique` of the two limits
(`ContinuousWithinAt` value `φ 0`, and the eventually-`0` limit `0`) gives
`φ 0 = 0`, i.e. `D 0 x = D 0 0`.  Combining interior + endpoint by
`rcases (0 ≤ t).lt_or_eq` closes the gauge relation with `linarith`.

## 4. Failed / discarded approaches

- **Import `A02.Restrict`** — on the pre-rebase branch this was a hard import
  error (§1); worked around by temporarily re-proving the two generic lemmas as
  `private` helpers.  After the lead's rebase onto the deduped integration branch
  the conflict is gone, the helpers were deleted, and `Restrict`'s lemmas are
  reused directly.
- **`Filter.Tendsto.congr' (eventually_nhdsWithin_of_forall …) tendsto_const_nhds`
  with the `EventuallyEq` left implicit** — "don't know how to synthesize
  placeholder `b`": the higher-order unification `(fun _ => 0) x = φ x ↦ f₁ = …`
  is ambiguous.  Fixed by annotating the `EventuallyEq` witness's type
  explicitly (`(fun _ => 0) =ᶠ[l] φ`) so `f₁` is pinned.
- **`Ico_subset_Ico le_rfl (min_le_left _ _)` in the four continuity `have`s** —
  the trailing `T₂` metavariable in `min_le_left _ _` was uninferable inside an
  un-annotated `have` (the `.mono` target set was undetermined).  Fixed by
  passing `min_le_left T₁ T₂` / `min_le_right T₁ T₂` explicitly.

## 5. Commands

- `cd verification && lake build NSFormalization.Section4.A02.{Restrict,Energy,Bounds,Order,Uniqueness}`
  — all `Build completed successfully`; `Uniqueness` builds with no warnings of
  its own.
- `cd verification && lake env lean ../research/A02/axioms_u2u3.lean` —
  `velocity_unique_core`, `velocity_unique`, `pressure_gauge_core`,
  `pressure_gauge` each `depends on axioms: [propext, Classical.choice,
  Quot.sound]`; both conformance `example`s elaborate with no error.
