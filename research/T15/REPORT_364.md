# Lane 364 — T15 U-TB1: energy Haar/Lebesgue single-copy bridges — REPORT

## 1. What was proved (theorems, exact statements)

Module `formalization/NSFormalization/Section3/T15/HaarBridge.lean`, namespace
`NSFormalization.Section3.T15`. Builds with 0 errors; every declaration has
axioms exactly `[propext, Classical.choice, Quot.sound]`.

Core (measure-free change of variables; the reusable Haar↔Lebesgue bridge):

    theorem eLpNorm_torusLift_restrict {F : Type*} [NormedAddCommGroup F] (g : Space → F) :
        eLpNorm (torusLift g) 2 periodicTorusMeasure
          = eLpNorm g 2 (volume.restrict fundamentalCube)

Goal 1 (energy identity for `periodize f`):

    theorem eLpNorm_torusLift_periodize (f : SpatialField) (_hf : ContDiff ℝ ∞ f)
        (hsupp : tsupport f ⊆ interior fundamentalCube) :
        eLpNorm (torusLift (periodize f)) 2 periodicTorusMeasure = eLpNorm f 2 volume

Goal 2 (gradient companion; the two identified norms are
`eLpNorm (torusLift (fun x ↦ spatialGradient _ t x)) 2 periodicTorusMeasure`
[T10 `energyGradientT` spelling] and `T13.gradientENorm f volume`):

    theorem eLpNorm_torusLift_spatialGradient_periodize
        (f : SpatialField) (hf : ContDiff ℝ ∞ f) (t : ℝ)
        (hsupp : tsupport f ⊆ interior fundamentalCube) :
        eLpNorm (torusLift
            (fun x => spatialGradient (fun p : SpaceTime => periodize f p.2) t x)) 2
            periodicTorusMeasure = gradientENorm f volume

Goal 3 (time-slice form for `energyEssSupT`):

    theorem eLpNorm_torusLift_periodize_slice (F : SpaceTimeField) (t : ℝ)
        (hf : ContDiff ℝ ∞ (fun x : Space => F (t, x)))
        (hsupp : tsupport (fun x : Space => F (t, x)) ⊆ interior fundamentalCube) :
        eLpNorm (torusLift (periodize (fun x => F (t, x)))) 2 periodicTorusMeasure
          = eLpNorm (fun x => F (t, x)) 2 volume

Supporting lemmas in the same module (all with the standard 3 axioms):
`lintegral_enorm_torusLift` (the raw `∫⁻ ‖·‖ₑ^q` bridge, any `q`, any field);
`eLpNorm_gradientVector_eq_gradientENorm` (the `energyGradientT`-vs-`gradientENorm`
identity `eLpNorm (fun x ↦ WithLp.toLp 2 (fun i ↦ fderiv ℝ f x (coordinateVector i))) 2 μ = gradientENorm f μ`,
any `μ`, `ContDiff` `f`); `gradientENorm_restrict_eq` (support: `gradientENorm f (volume.restrict fundamentalCube) = gradientENorm f volume`);
`eLpNorm_periodize_restrict_eq` (single copy on the cube, interior hypothesis);
`periodize_eq_of_mem_interior`, `periodize_eventuallyEq_interior` (interior-hypothesis
generalisations of `T13.eq_zero_of_mem_cube` / `T13.periodize_eventuallyEq`).

Hypothesis outcome (brief invited weakening): Goal 1 uses **only**
`tsupport f ⊆ interior fundamentalCube` — smoothness is unused. The whole bridge
`eLpNorm_torusLift_restrict` needs **no** regularity or measurability. Goal 2 uses
`ContDiff ℝ ∞ f` (needed only for `∇f` measurability in the gradient-norm identity),
never any regularity of `periodize f`.

## 2. What exists in Lean now

- `formalization/NSFormalization/Section3/T15/HaarBridge.lean` — the shipped module (10 named theorems).
- `research/T15/probes/haar_bridge_closes.lean` — non-vacuity: all three goals
  instantiated at the lane-344 `ContDiffBump` nonzero packet (`probeField`
  supported in `ball probeCenter (3/8) ⊆ interior fundamentalCube`). `lake env lean` clean.
- `research/T15/axioms_utb1.lean` — `#print axioms` for all 10 declarations; all print `[propext, Classical.choice, Quot.sound]`.
- `research/T15/ATTEMPTS_UTB1.md`, status entry in `research/T15/T15_SPLIT.md` §4.

Downstream (U4/U5) consume `eLpNorm_torusLift_restrict` and the three goals; the
interior hypothesis is discharged from a ball placement by
`hsupp.trans (subset_closure.trans hball)`.

## 3. Gaps

None for U-TB1. All three goals plus the gradient-norm identity are proved outright.

Deliberately avoided (not gaps for this unit): the module never proves
`periodize f` smooth (that is lane 365/U1's vendor `rfl` bridge to
`contDiff_periodize`). Goal 2 is designed to not need it — the gradient of
`periodize f` is replaced a.e.-on-the-cube by `∇f` (they agree on the interior;
the frontier is null), so the smooth `f` carries the `gradientENorm` identity.
If a later consumer wants the `T13.endpoint_one_eq`-style statement phrased on
`gradientENorm (periodize f) (restrict cube)` directly, that route would require
`periodize f ∈ C¹` and thus U1.

## 4. Commands run and results

- `cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T15.HaarBridge`
  → `✔ Built NSFormalization.Section3.T15.HaarBridge`, exit 0 (only unrelated
  pre-existing warnings in `Paper3.*`/`Source.*`; none in this module).
- `cd verification && lake env lean ../research/T15/axioms_utb1.lean`
  → every declaration `[propext, Classical.choice, Quot.sound]`.
- `cd verification && lake env lean ../research/T15/probes/haar_bridge_closes.lean`
  → exit 0 (all three non-vacuity examples type-check).
- `make check` → exit 0 (`check_formalization_plan`, `check_contracts`,
  `test_contract_policy` 13/13, `check_work_queue` all green).

First failed attempt (fixed): `rw [torusLift_coe ...]` inside
`setLIntegral_congr_fun` — error `Did not find an occurrence of the pattern
Paper1.torusLift g fun i => ↑(y i)` because the goal carried the defeq T10 abbrev
`torusLift`. Replaced with `congrArg (fun a => ‖a‖ₑ ^ q) (torusLift_coe ...)`
(exact, defeq-tolerant). Probe first failed on `probeBump.rOut` not reducing to
`1/4` for `linarith` (added `have hr : probeBump.rOut = 1/4 := rfl; rw [hr]`) and
a missing `open ... (spatialGradient)`; both fixed.
