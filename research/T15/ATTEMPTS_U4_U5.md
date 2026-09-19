# T15 U4 + U5 — attempts, dead ends, and design decisions (lane 439, 2026-09-18)

Targets: the five canonical `ScalingAPI` fields `energySlices_memLp`,
`packetEnergyIdentity`, `packetDissipationIdentity`
(`formalization/NSFormalization/Section3/T15/Scaling.lean:341,352,363`) and
`mixed_memLp`, `packetMixedScaling` (`:376,390`).
Delivered in `Section3/T15/Energy.lean` and `Section3/T15/Mixed.lean`.

## 1. Design decisions that worked

**D1 — the chart lands in the closed cube, so single copy is a *pointwise* lift
identity.** `Paper1.torusLift g z = g (toSpace ((measurableEquivPiIoc 0 z).val))`
and the representative has every coordinate in `Ioc 0 1 ⊆ [0,1] = fundamentalCube`
(`Energy.lean:torusChart_mem_fundamentalCube`).  Hence, for any two fields
agreeing on `fundamentalCube`, `torusLift g = torusLift h` **as functions**, not
merely a.e. (`torusLift_congr_cube`).  Combined with U3's `velocity_singleCopy` /
`force_singleCopy` this removes every measure-theoretic step from the `MemLp`
guards and from the mixed-norm slice reduction: the periodized field's lift *is*
the rescaled field's lift.  This is why `energySlices_memLp`'s velocity half and
all of `Mixed.lean` never mention `periodize`'s regularity.

**D2 — the gradient half does need `periodize` smooth.** `spatialGradient` of the
periodization at a boundary chart point is *not* the rescaled field's gradient
(they differ on the cube frontier), so D1 does not apply.  Route taken: vendor
`NavierStokes.PeriodicLocalization.contDiff_periodize` read through the lane-352
bridge `Bridges.periodize_eq_vendor` and U3's
`supportedInCube_of_tsupport_subset_interior`, giving
`contDiff_periodize_of_subset_interior`.  Then `I02.continuous_spatialGradient`
on the constant-in-time extension.

**D3 — no time-interval transport was needed.** The brief anticipated that an
I03 lemma might be stated on the wrong interval.  It is not:
`I03.energyEssSup_scaled_eq` (`Energy.lean:487`) and
`I03.energyGradient_scaled_eq` (`:304`) are both over
`volume.restrict (Ioo 0 T)` / `∫⁻ t in Ioo 0 T`, which is *literally* the
interval in T10's `energyEssSupT` / `energyGradientT`
(`Section3/T10/PeriodicData.lean:328,334`).  The `Ioo`/`Ioc` endpoint question
never arises.  The only interface work is `essSup_congr_ae` /
`setLIntegral_congr_fun` over that same `Ioo`.

**D4 — the `p = ∞` endpoint is handled once, by a pushforward, not by cases.**
`HaarBridge.eLpNorm_torusLift_restrict` is exponent-2 and its proof is an
`lintegral` manipulation, which cannot reach the essential supremum.  Instead
`Mixed.lean` §1 proves `Measure.map torusChart periodicTorusMeasure =
volume.restrict fundamentalCube` (`map_torusChart`) from the exponent-free
`lintegral_comp_torusChart` applied to set indicators, and then
`eLpNorm_map_measure` gives `eLpNorm_torusLift_eq_restrict` for **every**
`r : ℝ≥0∞`, `⊤` included, with no endpoint branch.  `alphaT p q =
-3 + 3/p.toReal + 2/q.toReal` matches `I03.positiveMixedNorm_parabolicForce`'s
exponent verbatim (`alphaT_formula` is `rfl`), and `(⊤ : ℝ≥0∞).toReal = 0`
makes the endpoint values fall out of the same formula.

**D5 — `Bindings` cannot be imported, so its two infimum lemmas were re-proved
on the canonical side.** The dependency direction is `verification →
formalization`, so `Bindings/Scaling.lean:296 mixedLebesgueENorm_eq` and
`:318 mixedLebesgueENorm_scaledForce` are unreachable from
`formalization/NSFormalization/Section3/T15/`.  `Mixed.lean` §2 re-does the
first on T15's own `mixedLebesgueENorm` (same proof: one admissible path from
`I02.slice_memLp` + `I02.continuous_slicePath` for `≤`,
`I03.eLpNorm_slicePath_eq` for the value, and `Lp.enorm_def` + the slice
congruence for `≥`), and §4 proves its torus twin `mixedLebesgueENormT_eq`.  §5
then routes straight through `I03.positiveMixedNorm_parabolicForce` rather than
through the binding.

**D6 — the torus slice path is easier than the Euclidean one.** The torus is a
probability space, so the `(volume B)^(1/p)` factor of
`I02.continuous_slicePath` collapses: `eLpNorm_le_of_ae_bound` plus
`measure_univ` gives `‖G a - G b‖ ≤ sup‖H(a,·)-H(b,·)‖` directly
(`continuous_torusSlicePath`), and the uniform continuity of the compactly
supported `scaledForce` finishes it.

**D7 — the packet hypothesis bundle.** `packetEnergyIdentity` and
`packetDissipationIdentity` take `NSFormalization.Section4.I03.PacketData` (an
existing Section 4 `Prop` structure), not eight loose clauses.  That is reuse,
not a named input: probe Part 1b builds it from the eight verbatim
`scalingStatement` clauses (`Scaling.lean:466-489`), so nothing is smuggled in.

## 2. What failed, and why

**F1 — `fun_prop` on the periodized gradient's continuity.**
```
error: fun_prop bug: function expected, got `periodize fun x =>
  scaledVelocity u place.x₀ place.T ε (t, x) : SpatialField, type ctor const
```
`SpatialField` is an `abbrev` for `Space → Space`, and `fun_prop` choked on the
`periodize` application at that type.  Replaced by an explicit
`I02.continuous_spatialGradient` call on the constant-in-time extension
`fun z : SpaceTime => periodize g z.2` (defeq to the goal's field).

**F2 — rewriting the identities directly on the `energyEssSupT` goal times out.**
The first version of `packetEnergyIdentity` was
`rw [← I03.sqrt_mul_eq_rpow_half …, ← I03.energyEssSup_scaled_eq …]` followed by
`essSup_congr_ae`.  Result:
```
error: (deterministic) timeout at `isDefEq`, maximum number of heartbeats (200000) has been reached
error: (deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached
```
Backwards-rewriting a large `essSup` term into the goal forced repeated
`whnf`/`isDefEq` on the unfolded `energyEssSupT`.  Fix: a `show` that spells the
unfolded `essSup …` form once, a separate `have key : essSup … = essSup …` doing
the a.e. congruence, then *forward* `rw [key, energyEssSup_scaled_eq,
sqrt_mul_eq_rpow_half]`.  Both identities now elaborate well inside the default
200000 heartbeats — **no `set_option maxHeartbeats` anywhere in either module**.

**F3 — `rw [torusSlicePath]`.**
```
error: Failed to rewrite using equation theorems for `torusSlicePath`
```
`torusSlicePath` is a plain `def` whose body is a `MemLp.toLp`; the generated
equation lemma would not fire under the `‖·‖ₑ` motive.  Fix: the explicit bridge
`enorm_torusSlicePath`, proved by `rw [show torusSlicePath … = … from rfl,
Lp.enorm_toLp]`, used at both call sites.

**F4 — implicit slice spelling.** Writing the slice's continuity as
`hH.comp (continuous_const.prodMk continuous_id)` makes Lean infer the lemma's
implicit field as `H ∘ fun x => (t, id x)`, so later `rw`s report
```
error: Did not find an occurrence of the pattern
  eLpNorm (torusLift (scaledForce f place.x₀ place.T ε ∘ fun x => (t, id x))) r periodicTorusMeasure
```
Fix: the helper `continuous_slice hH t : Continuous (fun x : Space => H (t, x))`,
whose *statement* pins the `fun x => H (t, x)` spelling the norms are written in.

**F5 — `iInf_le` with holes inside the anonymous constructor.** `refine le_trans
(iInf_le _ ⟨path, ?_, meas⟩) ?_` reordered the goals so the `·` bullets landed on
the wrong ones (`introN failed: There are no additional binders`).  Fix: prove
`hpath : IsPeriodicLebesgueSlicePath …` as a standalone `have` first.

**F6 — probe: `fderiv_const_smul` on `fun y => emVel (t, y)`.** Direct
application gave a type mismatch with two different instance paths for the
`Space` module structure (`PiLp.normedAddCommGroup` vs `WithLp.instAddCommGroup`)
because the scalar was left as a metavariable.  Fix: `rw [show (fun y : Space =>
emVel (t, y)) = fun y : Space => emTimeBump t • emField y from rfl]` first, then
`fderiv_const_smul (𝕜 := ℝ) … (emTimeBump t : ℝ)` with the scalar explicit.

**F7 — probe: `rw` under an unreduced image lambda.** In the `IsLUB` goal the
element is `(fun t => √(l2Sq emVel t)) (1/2)`, so `rw [hval]` reported
`Did not find an occurrence of the pattern √(l2Sq emVel ?t)`.  Fix: a `show`
beta-reducing the application.

**F8 — probe: `emPacketData` declared as `def`.** `PacketData` is a `Prop`
structure, so the linter demanded `theorem`.

## 3. Not attempted / remaining

- Nothing in U4/U5 is left open: all five fields are closed unconditionally from
  the raw packet clauses plus `PlacementData`, and the probe fires all five on an
  explicit non-vacuous geometry (nonzero `M`, nonzero force).
- The two modules do **not** discharge `PlacementData` itself; a caller must
  still exhibit the compact `K_*` and the chart ball (needs-a-lemma ② of
  `COMPARISON.md`), exactly as for U2/U3.
- `mixed_memLp`'s whole-space half asserts `MemMixedLebesgueR q p f` for the raw
  source force at *every* exponent pair; it is discharged by
  `Source.compact_mixed_memLp`, which already covers both `∞` endpoints, so no
  extra hypothesis on `f` beyond `ContDiff ℝ ∞ f` and
  `CompactPositiveTimeSupport f` is used.

## 4. Commands run

```
cd verification && LEAN_NUM_THREADS=6 lake build \
  NSFormalization.Section3.T15.Energy NSFormalization.Section3.T15.Mixed
  -> Build completed successfully (10009 jobs).
cd verification && lake env lean ../formalization/NSFormalization/Section3/T15/Energy.lean   -> 0 output
cd verification && lake env lean ../formalization/NSFormalization/Section3/T15/Mixed.lean    -> 0 output
cd verification && lake env lean ../research/T15/probes/energy_mixed_closes.lean             -> 0 output
cd verification && lake env lean ../research/T15/axioms_u4_u5.lean
  -> 29 declarations, each `[propext, Classical.choice, Quot.sound]`
make check -> architecture checks OK, 13 contract-policy tests OK, work queue consistent
```


> Lead correction after review 439 (D2): the gradient guard is obtained from smoothness of the periodization; the value-level single-copy identity alone does not supply a derivative statement, which is why regularity is supplied separately (the "differ on the cube frontier" explanation above is withdrawn — both gradients vanish there).
