# T24a Ua4 — `force_smooth` + `force_support` (lane 414): route, alternatives, negatives

Target: `research/T24/Spec.lean:1025` / `:1032`, over raw packet fields.
Landed in `formalization/NSFormalization/Section3/T24/AffineForce.lean`.

## What decided the route

The whole unit turned on one reconnaissance result: the **vendored**
`vendor/NavierStokesAndEuler/NavierStokes/ResidualRegularity.lean` already has both
halves of the analytic work, and neither is in `ResidualCalculus` (the file lane 398
used), so a `grep` restricted to `ResidualCalculus` would have missed it:

* regularity on an **open** set — `contDiffOn_temporalDerivative:49`,
  `contDiffOn_spatialDerivative:54`, `contDiffOn_spatialLaplacian:75` (all built on
  `contDiffOn_space_fderiv` / `contDiffOn_time_fderiv`, which are the
  "partial derivative of a jointly smooth function is smooth" lemmas);
* locality — `temporalDerivative_congr`, `spatialDerivative_congr`,
  `spatialLaplacian_congr`, each taking only `u =ᶠ[𝓝 z] v` and **no**
  differentiability hypothesis.

With those, the two-open-set gluing is ~40 lines and the module compiled on the
first `lake build`. The honest record is therefore short on Lean failures: the cost
was in reading, not in iterating.

## Hypotheses actually consumed (and what is *not*)

* `force_smooth`: `velocity_smooth` (`ContDiffOn ℝ ∞ U preSingularDomain`),
  `force_smooth` (`ContDiff ℝ ∞ F`), plus `0 < τ₀` and `τ₁ < 1`.
* `force_support`: `force_support` (`CompactPositiveTimeSupport F`) plus `0 < τ₀`
  **only**. `τ₁ < 1` is genuinely unused there (the support statement never looks at
  `U`), so it is not taken as a hypothesis — checked by compiling without it.
* Neither theorem uses `0 < ν`, the packet pressure, `divergence_free`, or the
  divergence clause of `AffineAdmissible`. `ν` is an arbitrary real.

**`τ₁ < 1` cannot come from `AffineAdmissible`.** `AffineAdmissible c r τ₀ τ₁ b`
(`AffineBasics.lean:26`) constrains `b` *relative to* the cylinder; it says nothing
about where the cylinder sits. It is satisfiable with `τ₁ ≥ 1` — e.g. `b = 0`, whose
`tsupport` is empty and so is a subset of every cylinder. So the parameter
hypotheses `0 < τ₀`, `τ₁ < 1` of `affineVariationStatement` (`Spec.lean:1117`, the
`window` field `:1019`) are carried **explicitly**, exactly as lane 403
`AffineSpeed.lean` carries `hτ₁ : τ₁ < 1`. Carrying them is not a weakening: the
probe `affine_force_closes.lean` supplies them from the statement's own binders.

## Negative / rejected routes

1. **Using `preSingularDomain` directly for `ContDiffAt`.** Dead end by
   construction: `preSingularDomain = Ico 0 1 ×ˢ univ` is **not open** (the `t = 0`
   face), so `ContDiffOn.contDiffAt` cannot fire on it and neither can
   `ResidualRegularity.contDiffOn_*`, every one of which takes `IsOpen s`. The fix is
   to pass to the open `Ioo 0 1 ×ˢ univ ⊆ preSingularDomain` first (`ContDiffOn.mono`).
   This is exactly why `0 < τ₀` is needed for the *smoothness* clause and not only
   for the support clause.
2. **Proving smoothness of `∂ₜb`/`Δb` by hand** via
   `fderiv ℝ (fun s => b (s,x)) t = (fderiv ℝ b (t,x)).comp (ContinuousLinearMap.inl ℝ ℝ Space)`
   and then `ContDiff.fderiv_right` + `clm_apply`. Correct but redundant once
   `contDiffOn_time_fderiv` was found; abandoned before writing Lean. Recorded because
   it is the route a lane that only greps `ResidualCalculus` will take.
3. **`HasCompactSupport.add` on `F` and a separately-named correction term** (the
   route the brief sketched). Rejected: it forces a new definition
   `affineCorrection ν U b := affineForce ν U F b - F` in the canonical module — a
   definition `Spec.lean` does not have, hence drift — and then needs
   `HasCompactSupport` of that correction proved separately anyway. The single
   inclusion `tsupport (affineForce ν U F b) ⊆ tsupport F ∪ tsupport b`
   (`tsupport_affineForce_subset`) gives both halves of
   `CompactPositiveTimeSupport` at once, from `closure_minimal` + `IsCompact.union` +
   `IsCompact.of_isClosed_subset`, with no new definition. Note the inclusion needs
   **no** smoothness hypothesis at all.
4. **A `Prop`-level "named input" for the smooth zero-extension** (e.g. a
   `BoundedDerivativesNearCylinder U` predicate). Explicitly forbidden for this unit,
   and unnecessary: the paper's "bounded derivatives of every fixed order on a
   neighbourhood of the cylinder" phrasing is a *quantitative* paraphrase of what is
   here a purely qualitative gluing — the correction is identically zero off a compact
   set that sits strictly inside the region where `U` is smooth, so no bound is ever
   extracted.

## Two Lean details worth keeping

* `affineForce_eq_of_notMem_tsupport` is where the "extends smoothly by zero across
  `t = 1`" content actually lives, and it needs `b =ᶠ[𝓝 z] 0` (not just `b z = 0`):
  the derivative terms see a whole neighbourhood. `(isClosed_tsupport b).isOpen_compl.mem_nhds`
  supplies it. The term `crossAdvection b U` is the only one that survives on the
  value of `b` alone (`spatialDerivative U z.1 z.2 (b z)`, killed by `map_zero`), which
  is why that term needs no smoothness of `U` anywhere.
* `contDiff_iff_contDiffAt` + `ContDiffAt.congr_of_eventuallyEq` is the gluing pair;
  the second takes the eventual equality in the direction
  `f₁ =ᶠ[𝓝 x] f` with `h : ContDiffAt 𝕜 n f x`, i.e. `hforce_smooth.contDiffAt.congr_of_eventuallyEq h`
  with `h : affineForce ν U F b =ᶠ[𝓝 z] F`.

## Mutation checks (hypotheses are load-bearing, not decoration)

Two scratch mutations run with `lake env lean` (kept out of the tree; reproduce by
copying the module proof and deleting the hypothesis):

1. `force_smooth` **without** `hτ₁ : τ₁ < 1` — fails at the step placing `tsupport b`
   inside the open slab, with

   ```
   error: linarith failed to find a contradiction
   … hz : z ∉ Ioo 0 1 ×ˢ univ   hmem : z ∈ tsupport b   a✝ : 1 ≤ τ₁  ⊢ False
   ```

   i.e. with `τ₁ ≥ 1` the perturbation may live where `U` is not known to be smooth,
   and the gluing has no second open set to fall back on.
2. `force_support` **without** `hτ₀ : 0 < τ₀` — fails at the positive-time inclusion,
   with

   ```
   error: linarith failed to find a contradiction
   … hb_supp : tsupport b ⊆ affineCylinder c r τ₀ τ₁   a✝ : τ₀ ≤ 0  ⊢ False
   ```

   and this one is not merely a proof-route artefact: at `τ₀ = -1` a `b` supported in
   `Ioo (-1) 0 ×ˢ ball c r` makes the corrected force genuinely nonzero at negative
   times, so the conclusion is *false* without it.

## Gates run

* `lake build NSFormalization.Section3.T24.AffineForce` — 0 errors.
* `lake env lean` on the module — no output.
* `lake env lean ../research/T24/axioms_ua4.lean` — all 7 module declarations print
  `[propext, Classical.choice, Quot.sound]`.
* `lake env lean ../research/T24/probes/affine_force_closes.lean` and
  `../research/T24/probes/affine_force_nonzero.lean` — all probe declarations print the
  same three axioms.
* `make check` — exit 0.
