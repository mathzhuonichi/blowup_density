# A2b / A3 row A2b-a′ — attempts, paths, decisions (lane 126)

Module: `formalization/NSFormalization/Section4/A01/Continuation.lean`
(namespace `NSFormalization.Section4.A01`).  Build: `lake build
NSFormalization.Section4.A01.Continuation` → `Build completed successfully (3941 jobs)`.
All six declarations `#print axioms` = `[propext, Classical.choice, Quot.sound]`
(`research/A01/axioms_a2b.lean`).

> **Revised after the lane-126 review (`research/A01/REVIEW_A2B.md`).**  The earlier gap
> section here was materially overstated on both counts; see §"Gap (corrected)".

## What went through

* **(S) `forced_global_mild_of_bound`** — verbatim from `research/A01/REVIEW_A3.md` §3
  (lane 122's review; note: this file lives on `origin/erenup/integration`, not in this
  lane's merge-base — the earlier `tmp/REVIEW_A3_for_126.md` pointer was a scratch copy and is
  dead, per `logs/LESSONS.md`).  One-line proof term
  `EulerBoundedMildContinuation.exists_global_mild_of_bound 1 q ν hν S hS R hR _ hu₀
   (coefficients 1 hq (sobolevPath F hF q)) hbound`.  The vendor theorem
  (`vendor/NavierStokesAndEuler/Euler/BoundedMildContinuation.lean:39`) takes exactly
  `exists_local`'s carrier (`SobolevSpace 1 (q+1)`), `Coefficients` bundle and Duhamel
  form, so no adapter is needed — confirming reviewer F5 of `REVIEW_A3.md`.
* **(2a) `forced_mild_divergenceFree`** — divergence-freeness of the continued solution.
  Template `EulerCorrectionContinuation.correction_mild_divergenceFree`
  (`Euler/CorrectionContinuation.lean:17`) via
  `EulerDivergenceFreeHeat.mild_solution_preserves_gradient_zero`
  (`Euler/DivergenceFreeHeat.lean:110`).  Key facts:
  - `quadraticDuhamel 1 ν hν hS.le le_rfl C u₀ u t` is **definitionally** the
    `heatOperator … u₀ + ∫ heatKernel … (C.apply (timeInclusion le_rfl (projIcc …)) (u …))`
    form, and `(C.comp (timeInclusion le_rfl)).apply t v = C.apply (timeInclusion le_rfl t) v`
    by `Coefficients.comp_apply` (rfl); so `hsol` is passed **directly** into the preservation
    lemma (as `correction_mild_divergenceFree` does).
  - The source-gradient-zero side is `leray_gradient_zero`
    (`Source/ForcedCylinderLocal.lean:32`) after `rw [source_eq]`, holding for **every** input.
    Hence the div-free clause is pointwise and needs **no** contraction/uniqueness, so it holds
    on all of `[0,S]`.  Initial datum div-freeness from `OrdinaryForcedLocal.initial_divergenceFree`.
* **(2c) `forced_ordinary_descent`** — the descent to `U : C(Icc 0 S, EulerMeanSolenoidal.L2)`,
  literally the last eight lines of `exists_local` (`ordinaryValue`, `ordinaryValue_lift`,
  `Source/OrdinaryCylinderDescent.lean:56,60`), with `U 0 = a.toLp` via `ordinaryLift.injective`
  + `ordinarySobolev_value`.  **Conditional on the angle-invariance of `u`** as a hypothesis,
  because `ordinaryValue_lift` (`OrdinaryCylinderDescent.lean:60`) *consumes* it.
* **`forced_global_of_bound`** — final theorem in `exists_local`'s conclusion shape on `S`,
  assembling step-1 + (2a) + (2c), with the angle-invariance clause (2b) exposed as the
  hypothesis `hinv` (the isolated gap).  **`forced_global_of_bound'`** (reviewer F4) is the
  preferred form: `hinv` additionally carries `‖u‖ ≤ R`.  This strictly weakens the hypothesis
  (strictly strengthens the theorem) at zero proof cost — `hinv` is applied only to the `u`
  from `forced_global_mild_of_bound`, which already has `‖u‖ ≤ R` — and it is the exact shape
  the window-uniqueness route (below) discharges.  Both keep the standard three axioms.
* **(H1 lead) `forced_uniform_restart_time`** — direct specialization of
  `EulerUniformHeatLocal.exists_uniform_restart_time` (`Euler/UniformHeatLocal.lean:29`) to
  `coefficients 1 hq (sobolevPath F hF q)`.  **Not literally H1** (`A01_SPLIT.md:147`): the
  window `δ` here depends on the order-`q+1` cylinder-norm bound `R` and the coefficient bundle,
  whereas H1 wants `δ` as a function of `‖a‖_{H¹}` and `‖f‖_{L¹H¹}` only.  Recorded as a lead.

## Gap (corrected) — (2b) angle-invariance is not restored *in this lane*; the remaining work is an M, not an L

Goal: `∀ θ t, sobolevTranslation 1 (q+1) (0,θ) (u t) = u t` for the continued `u`, so `hinv`
can be dropped from `forced_global_of_bound`.

**What is genuinely true (kept from the first draft):** there is **no pointwise route** — the
Leray-projected source `leray (f − advection u u)` is *covariant*, not invariant
(`ForcedCylinderInvariant.lean:19-26`): angle-invariant only when `u` is.  So a *uniqueness*
step is needed (`v := (translate)∘u` solves the same Duhamel equation ⟹ `v = u`).  And
`EulerVolterraConvolution.mild_solution_unique` (`Euler/VolterraUniqueness.lean:22`) is genuinely
the only mild uniqueness in the vendor's `Euler/` tree; `inviscid_correction_unique`
(`Euler/InviscidCorrectionUniqueness.lean:25`) is genuinely the inviscid *strong* equation.

**What was WRONG in the first draft (corrected per `REVIEW_A2B.md` §F6):**
* **No *global* mild uniqueness is required.**  `exists_global_mild_of_bound` is built by
  iterating windows whose length `δ` comes from `exists_positive_time_budget`
  (`Euler/VolterraUniqueness.lean:69`), and that `δ` *guarantees*
  `(δ + 2·parabolicConstant ν·√δ)·L < 1`, i.e. `kernelMass δ · L < 1` (identification already
  in-repo at `Source/ForcedCylinderInvariant.lean:104-105`, and used at
  `Euler/UniformHeatLocal.lean:42-54`).  **The continuation's own windows are exactly the
  uniqueness regime of `mild_solution_unique`.**  `kernelMass S · L < 1` being false for large
  `S` is irrelevant — nobody needs it on `[0,S]`.  Per-window invariance is proved
  **unconditionally** (contraction *discharged*, not assumed) in
  `research/A01/probes/probe_window_invariance.lean` (needs `maxHeartbeats 400000`) and
  `research/A01/probes/probe_restart_window_invariance.lean` (`600000`) — reviewer probes,
  both standard three axioms.  Probe 2 is the restart shape the continuation induction consumes.
* **`set_option maxHeartbeats` is NOT forbidden in this repo.**  `CLAUDE.md` does not mention
  it; `.claude/hooks/post_lean.py:14-17` strips block comments and greps only for
  `sorry|admit|native_decide|axiom`.  Ten merged modules use it (e.g.
  `Source/ForcedCylinderInvariant.lean:5` `800000`, `Section4/A03/ScalarTameProduct.lean:249`
  `1200000`).  The brief's "no maxHeartbeats" was a no-chasing rule, not a ban.  The `[0,S]`
  covariance/uniqueness port needs only `300000` (bisected: 200000/250000 fail, 300000 OK),
  **not** 800000.  See `research/A01/probes/a2b_invariant_port.lean` — the earlier
  "unsolved goals" was a **missing `rfl`** (the `hfree` goal
  `heatOperator … u₀ = freeHeatPath … s` is `rfl`, since `freeHeatPath` is *defined* as
  `heatOperator …`, `Euler/SobolevHeatVolterra.lean:50-53`), not a resource wall.

**Remaining work — row A2b-b, size M (≈150–190 lines), one lane** (delete `hinv` from
`forced_global_of_bound`; A3 then takes `T₀ := S` from the bound alone):
1. **`exists_uniform_restart_time_invariant`** (S–M, ≈80 lines): merge the 20-line body of
   `EulerUniformHeatLocal.exists_uniform_restart_time` (`UniformHeatLocal.lean:41-62`;
   `exists_positive_time_budget` is public) with the verified body of `probe_restart_window_invariance`.
2. **`gluePath_invariant`** (S, ≈10 lines): `EulerTimePathGluing.gluePath` is invariant when both
   pieces are — case split on `t ≤ a` with `glueFunction_left`/`glueFunction_right`
   (`Euler/TimePathGluing.lean:46,51`), unfold `extendPath`.
3. **`forced_global_mild_invariant_of_bound`** (M, ≈60 lines): fork the ~45-line induction of
   `exists_global_mild_of_bound` (`BoundedMildContinuation.lean:48-72`; `advance_time_eq`/
   `advance_grid` reusable) carrying the invariance clause — base datum invariance from
   `ordinarySobolev_angle`, restart datum from the IH, step from (1), glue from (2).
   Do **not** open an L campaign for a Grönwall mild uniqueness (F6b shows it is off-path).

## F9 — one uniqueness the vendor-`Euler/` sweep missed (informational)

The local tree has `formalization/NSFormalization/Source/BoundedViscosityUniqueness.lean:23
classical_uniqueness_on_Icc` — a genuine Grönwall-type uniqueness **under an a-priori bound**
(`‖u‖ ≤ B`, `‖∇u‖ ≤ G`), and `Source/OrdinaryViscousUniqueness.lean:26 velocity_unique`.  Both
are on the **classical** R³ PDE (smooth fields, `residual ν u p`), not the cylinder mild
equation, so reaching them needs the C1b/C1c bridge — **not a shortcut here**, but worth one
line so the next lane does not re-run the (Euler-only) sweep.

## Commands run

```
lake build NSFormalization.Source.OrdinaryForcedLocal Euler.BoundedMildContinuation \
  Euler.CorrectionContinuation   → Build completed successfully (3940 jobs)
lake build NSFormalization.Section4.A01.Continuation → Build completed successfully (3941 jobs)
lake env lean …/Section4/A01/Continuation.lean       → silent, exit 0
lake env lean research/A01/axioms_a2b.lean           → all 6 decls [propext, Classical.choice,
                                                        Quot.sound]; both zeroField non-vacuity
                                                        examples typecheck (autoImplicit false)
lake env lean research/A01/probes/probe_window_invariance.lean          → exit 0 (maxHeartbeats 400000)
lake env lean research/A01/probes/probe_restart_window_invariance.lean  → exit 0 (maxHeartbeats 600000)
lake env lean research/A01/probes/a2b_invariant_port.lean               → exit 0 (maxHeartbeats 300000)
make check → test_contract_policy 13 tests OK; check_work_queue 30 items consistent
```
