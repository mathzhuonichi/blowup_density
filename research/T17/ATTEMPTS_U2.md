# T17 U2 — attempts log (lane 373)

Target: `Section3/T17/Transport.lean` = concrete `correctionData`, the verbatim
T17 `correctionForce`, `force_eq` (force-operator transport through the lattice
lift), `correctionForce_periodic`.

## What worked (final route)

`force_eq` is proved **pointwise, by cases on `x ∈ periodicSet (ball x₀ r)`**,
which reuses T16 maximally and needs no finite-sum / double-sum bookkeeping:

* **inside**: periodicity of the lift + `latticeLift_eq_of_ball` give a single
  active translate germ `latticeLift W =ᶠ[𝓝 (t,x)] translate W k`; the force is a
  germ-local operator (`source_correctionForce_congr`); each operator is
  translation-equivariant (`temporalDerivative/spatialDerivative/spatialLaplacian/
  advection_translate`, modelled on T16 `spatialDivergence_translate`); the two
  `v`-cross terms are matched by periodicity of `v`'s value and (on the reference
  cylinder, where `v` is smooth) of its derivative.
* **outside**: `latticeLift_sliceSupport` makes the lift locally zero and
  `source_correctionForce_support` makes the single copy zero, so both sides are 0.

Only `Source.correctionForce`'s two middle summands differ in order from the T17
spelling; `correctionForce_eq_source` bridges them by `abel`.

## Dead ends / lessons

* **Finite-sum route (rejected).** Rewriting `latticeLift W =ᶠ ∑_{box} translate
  W n` via `periodize_locally_eq_sum` forces the *nonlinear* advection term into a
  double sum `∑ₙ∑ₘ (Wₙ·∇)Wₘ` whose off-diagonal terms must be killed by
  disjointness. The single-active-copy germ (available directly from T16's
  `latticeLift_eq_of_ball` + `latticeLift_periodic`) avoids the double sum
  entirely — the quadratic term never sees two distinct copies.

* **`v` is only `ContDiffOn` the cylinder, not globally smooth.** The only place
  the reference's *derivative* must be periodized is the cross term
  `spatialDerivative v t x (W(t,x−k))`. It is handled by a case split: when
  `W(t,x−k)=0` both sides are `L(0)=0`; when `W(t,x−k)≠0`, the full support of `W`
  (`physical_support`) puts `t ∈ Ioo(T−2ε²)(T+2ε²) ⊆ Ioo 0 (T+δ)`, i.e. inside the
  cylinder where `v` is smooth, so `v` is `DifferentiableAt (t, x−k)` and
  `spatialDerivative v t x = spatialDerivative v t (x−k)` follows from the
  functional periodicity `v(t,·)=v(t,·−k)` (funext) + chain rule.

* **`translate` is ambiguous** with a `_root_.translate` (group action); must be
  written fully qualified `NavierStokes.PeriodicLocalization.translate`.

* **`fderiv`/`ContDiff` metavariable stalls.** `hspace.fderiv` and
  `ContDiff.clm_apply` leave the field/module as a metavariable; pin them with a
  typed `have` (`fderiv ℝ … =ᶠ[𝓝 x] fderiv ℝ …`) and by running
  `simp only [spatialDerivative]` *before* `clm_apply` so the goal is in the exact
  `(f x) (g x)` shape.

* **`HasFDerivAt.comp` gives the `∘` form**, which does not `rw`-match
  `fun y => v(t, y−k)`; convert with `rw [show … ∘ … = fun y => … from rfl] at hc0`.

## Gates

`lake build NSFormalization.Section3.T17.Transport` — 0 errors (module is
warning-clean). `#print axioms` on every declaration = `[propext,
Classical.choice, Quot.sound]`. `lake env lean` on module / probe / axioms file.
`make check` — OK.
