# ATTEMPTS — T11/U6 transport (lane 331)

Positive and negative record for `formalization/NSFormalization/Section3/T11/Transport.lean`.
Not a generated file.

## 0. Shape of the constructor (decision)

The brief's change of variables is `(t,x) ↦ (α t, β x + X(t))`. Every use in T11 has `β = 1`
(the two viscosity rescalings dilate time only; the Galilean transform translates only), so the
constructor was built for

```
v (t,x) = α • u (α t, x + X t) - c t,  q (t,x) = α² p (α t, x + X t),
g (t,x) = α² • f (α t, x + X t) - d t,  c = X', d = X'',  ν ↦ α ν,  α T' = T.
```

The residual algebra forces `c = X'` exactly: the time derivative of `v` produces
`α • (D_x u)(X'(t))` and the advection of `v` produces `-α • (D_x u)(c t)`; they cancel iff
`c = X'`, which is *why* the Galilean force is `f(t,·+X) - forceMeanT f` and not something else
(`navierStokesResidual_transport`, closed by `module`).

The transported fields are **parameters** with pointwise defining equations
(`hv`, `hq`, `hg`, `ha'`) rather than definitions. Reason: the target fields are
`galileanVelocityT a f u` / `unitViscosityVelocityT ν u`, which are only *propositionally*
equal to a canonical `fun z ↦ α • u (α z.1, z.2 + X z.1) - c z.1` (`1 • x = x`, `1 * t = t`,
`x + 0 = x` are not `rfl` on `EuclideanSpace`). With the fields as parameters, each instance's
`velocity`/`pressure` equation is `rfl` and the three API conclusions need no transport of a
structure along an equality.

## 1. Traps hit (with the exact error)

1. `subst` inside the constructor blocks the projections. The first version began with
   `subst hν'` (from `hν' : ν' = α * ν`), which put an `Eq.ndrec` in front of the structure;
   `(classicalSolutionT_toUnit hν w).velocity = unitViscosityVelocityT ν w.velocity := rfl` then
   failed with `Type mismatch: rfl has type ?m = ?m`. Fix: keep `ν'` abstract and `subst` only
   inside the `momentum` field, which is the only field mentioning the viscosity.
2. `fderiv_comp_add_right` never matches by unification: `rewrite failed: did not find an
   occurrence of the pattern fderiv ?m (fun x => ?m (x + ?a)) ?m` in
   `α • fderiv ℝ (fun x => u (s, x + Y)) x = …`. Every use must pin
   `(𝕜 := ℝ) (f := fun y : Space ↦ u (s, y)) (x := x) Y`.
3. `Finset.sum_congr` cannot start on `∑ … = α • ∑ …`; `rw [Finset.smul_sum]` first
   (`typeclass instance problem is stuck AddCommMonoid ?m`).
4. `Continuous.comp_continuousOn` into the submodule carrier `PeriodicSobolev s` hit
   `(deterministic) timeout at whnf, maximum number of heartbeats (200000)` when it was written
   inline inside the constructor. Extracting it as the standalone lemma
   `continuousOn_transport_datumPath` (same proof) elaborates in seconds. Likewise
   `simpa using hc.tendsto (y₀, A₀)` times out on `‖A₀ - A₀‖`; use
   `have h0 : ‖A₀ - A₀‖ = 0 := by rw [sub_self, norm_zero]; exact h0 ▸ …`.
   **No `set_option maxHeartbeats` was needed anywhere in the module.**
5. `HasFDerivAt.sum` cannot infer its implicit family from a `refine … ?_`
   (`typeclass instance problem is stuck Module ?m ℝ`); use `HasFDerivAt.fun_sum` with
   `(u := Finset.univ) (A := …) (A' := …)` given explicitly, and add `Function.comp_def` to the
   closing `simpa` (`(fun x => x.ofLp i) ∘ …` does not match the lambda otherwise).
6. `rw` with `Section4.A01.convectionDivergence_eq_advection` does not fire on a goal spelled
   with the `abbrev` `convectionDivergenceT` (`did not find an occurrence of the pattern
   Section4.A01.convectionDivergence v t y`). State the instance as a `have e1 :
   convectionDivergenceT v t y = advection v t y := …` and `rw [e1]`.
7. `hasFDerivAt_const 0 x` and `HasFDerivAt … 0 x` both need the type of `0` pinned
   (`NormedSpace ?m ?m` / `Module ?m ℝ` stuck).

## 2. What had to be re-proved locally

`GalileanClasses.lean` keeps `torusPoint`, `periodicFourierCoeff_translate`,
`translatePeriodicDatum`, `isPeriodicDatum_translate` and `translatePeriodicDatum_norm`
**private**, so they are not importable. They are re-proved in `Transport.lean` (same proofs,
public, with `MeanIdentity.torusLift_translate` and
`MeanIdentity.integrable_torusLift_translate_iff` reused instead of the private copies).
`ForcePaths.datum_sub` and `DatumBasics.periodicFourierCoeff_const` *are* public and are reused.
`torusConstantDatum` exists in `LocalExistenceProbe.lean`, but that module imports
`Formal.EndpointSafeTwoSpacePicard` (HeliCorgi), which no `verification/Tests` module may
import (`warningAsError`), so a local `constantDatum` with its own `IsPeriodicDatum` proof,
norm identity and continuity was written instead.

## 3. The residual, precisely

`PeriodicLocalRegularity ν a f T w` is **not** derivable from `w : ClassicalSolutionT ν a f T`:
`ClassicalSolutionT.sobolev` gives only `ContinuousOn G (Ico 0 T)`, while
`PeriodicLocalRegularity.sobolev_smooth` demands `ContDiffOn ℝ ∞ G (Ico 0 T)` for an
`lp`-valued path. Nothing in the tree produces a `C^∞` datum path
(`grep -rn "ContDiffOn ℝ ∞ G" formalization/NSFormalization/Section3` finds only the two
statements of the record itself; `T10.ForcePaths.continuous_datum_path` stops at continuity and
additionally needs a *globally* `ContDiff` spacetime field, which a slab solution is not).
Hence the three target fields, which quantify over an arbitrary `ClassicalSolutionT`, cannot be
closed with the regularity conjunct; the lane proves them from the source's regularity instead.

Additionally, for the Galilean instance even the *conditional* `sobolev_smooth` is out of reach
with the present infrastructure: the transported path is
`t ↦ T_{X t}(G t) - constantDatum (c t)` where `T_y` is multiplication by `e^{2πi k·y}`.
`t ↦ T_{X t} A` is norm-continuous (proved here: `continuous_translatePeriodicDatum`,
`continuous_translate_pair`) but it is **not** norm-differentiable in `H^m`: the formal
derivative multiplies the coefficient by `2πi (k · X'(t))`, which leaves `H^m` and lands in
`H^{m-1}`. A `C^∞` statement at order `m` therefore needs the order-`m+n` paths for every `n`
plus the multiplier `H^{s+1} →L H^s` as a bounded operator and an induction over the
differentiability order — a separate unit, not this one. The pure rescalings have `X = 0` and
are unaffected (`periodicLocalRegularity_toUnit` / `_fromUnit` are complete).

## 4. Dead ends

* Deriving the `sobolev` field of the transported solution from
  `ForcePaths.continuous_datum_path` (its hypothesis is `ContDiff ℝ ∞ f` on **all** of
  spacetime; a solution is `ContDiffOn` on `Ico 0 T ×ˢ univ` only, and the norm identity
  `‖G u - G t‖ = √(periodicIntegerEnergy m (…))` it relies on needs
  `Paper1.continuous_periodicIntegerEnergy_time`, which has the same global hypothesis).
  Replaced by the algebraic route: translate + rescale + subtract the constant mode, with
  strong continuity of the translation family proved from Tannery's theorem
  (`tendsto_tsum_of_dominated_convergence`, bound `4‖A k‖²`).
* Proving `pressure_poisson` for the transported solution *without* the source's — it would need
  the divergence of the momentum equation at `t = 0`, i.e. a one-sided limit of third
  derivatives on the slab; not attempted, and not needed once the source record is assumed.
