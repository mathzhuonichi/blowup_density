# REPORT_439 — T15 U4 energy + U5 mixed (Opus; transcribed by lead from the agent message, report-file guard)

Lane 439 is complete. Full four-part report:

---

## 1. What was proved

All five canonical `ScalingAPI` fields of units U4 and U5, unconditionally, from the raw packet clauses of `scalingStatement` plus the canonical `PlacementData`. Exact statements (namespace `NSFormalization.Section3.T15`):

**U4 — `Section3/T15/Energy.lean`**

```lean
theorem energySlices_memLp
    {u f : VelocityField} {p : PressureField} {K : Set Space}
    (hext : ContDiffOn ℝ ∞ (zeroPastField u) (Iio (1 : ℝ) ×ˢ (univ : Set Space)))
    (hK : IsCompact K)
    (hu : ∀ t ∈ Ico (0 : ℝ) 1, tsupport (fun x : Space => u (t, x)) ⊆ K)
    (place : PlacementData u p f K) :
    ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
      EnergySlicesMemLpT place.T (periodizedScaledVelocity u place.x₀ place.T ε)

theorem packetEnergyIdentity
    {u f : VelocityField} {p : PressureField} {K : Set Space} {M D : ℝ}
    (hP : NSFormalization.Section4.I03.PacketData u K M D)
    (hu : ∀ t ∈ Ico (0 : ℝ) 1, tsupport (fun x : Space => u (t, x)) ⊆ K)
    (place : PlacementData u p f K) :
    ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
      energyEssSupT place.T (periodizedScaledVelocity u place.x₀ place.T ε) =
        ENNReal.ofReal (ε ^ ((1 : ℝ) / 2) * M)

theorem packetDissipationIdentity   -- same signature
    ... energyGradientT place.T (periodizedScaledVelocity u place.x₀ place.T ε) =
        ENNReal.ofReal (ε ^ ((1 : ℝ) / 2) * D)
```

**U5 — `Section3/T15/Mixed.lean`**

```lean
theorem mixed_memLp (hf : ContDiff ℝ ∞ f)
    (hfc : NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport f)
    (place : PlacementData u pfield f K) :
    ∀ (r q : ℝ≥0∞) [Fact (1 ≤ r)], 1 ≤ q →
      MemMixedLebesgueR q r f ∧
        ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
          MemMixedLebesgueT q r (periodizedScaledForce f place.x₀ place.T ε)

theorem packetMixedScaling (hf : ContDiff ℝ ∞ f)
    (hfc : NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport f)
    (place : PlacementData u pfield f K) :
    ∀ (r q : ℝ≥0∞) [Fact (1 ≤ r)], 1 ≤ q → ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
      mixedLebesgueENormT q r (periodizedScaledForce f place.x₀ place.T ε) =
        ENNReal.ofReal (ε ^ alphaT r q) * mixedLebesgueENorm q r f
```

These are literally the field types of `Scaling.lean:341,352,363,376,390` (the exponent binders are renamed `r q` only to avoid clashing with the pressure field `p`; the types are alpha-equivalent, and the probe closes each field type verbatim by a bare `exact`).

Three things are worth flagging as substance, not bookkeeping:

- **No time-interval transport was needed.** The brief anticipated an I03 lemma on the wrong interval. There is none: `I03.energyEssSup_scaled_eq` and `I03.energyGradient_scaled_eq` are already over `Ioo 0 T`, literally T10's interval in `energyEssSupT`/`energyGradientT`. The `Ioo`/`Ioc` endpoint question never arises.
- **`p = ∞` is handled once, not by cases.** `HaarBridge`'s bridge is exponent-2 and `lintegral`-based, so it cannot reach an essential supremum. I proved instead `Measure.map torusChart periodicTorusMeasure = volume.restrict fundamentalCube` and applied `eLpNorm_map_measure`, which is exponent-generic.
- **The chart lands in the closed cube.** `torusLift g z = g (toSpace ((measurableEquivPiIoc 0 z).val))` and that representative has every coordinate in `Ioc 0 1 ⊆ [0,1]`. So U3's single copy makes the Haar lift of the periodization *pointwise equal*, not merely a.e. equal, to the lift of the rescaled slice. That removes all measure theory from the `MemLp` guards and the whole mixed reduction.

## 2. What exists in Lean now

New files (absolute paths):

- `/data_8T/ping/blowup_density/.claude/worktrees/439-T15-U4-U5-energy-mixed/formalization/NSFormalization/Section3/T15/Energy.lean` — 250 lines, 8 declarations. Besides the three fields: `torusChart_mem_fundamentalCube`, `torusLift_congr_cube`, `contDiff_periodize_of_subset_interior` (vendor `contDiff_periodize` through the lane-352 `rfl` bridge), `memLp_torusLift_gradientVector` (`MemLp.of_eval_piLp` on `WithLp 2 (Fin 3 → Space)`), `scaledVelocity_slice_contDiff`.
- `/data_8T/ping/blowup_density/.claude/worktrees/439-T15-U4-U5-energy-mixed/formalization/NSFormalization/Section3/T15/Mixed.lean` — 383 lines, 21 declarations: §1 `torusChart`/`measurable_torusChart`/`torusChart_coe`/`lintegral_comp_torusChart`/`map_torusChart`/`eLpNorm_torusLift_eq_restrict`/`eLpNorm_torusLift_eq_volume`; §2 `mixedLebesgueENorm_eq`; §3 `continuous_slice`/`torusSlicePath`/`enorm_torusSlicePath`/`continuous_torusSlicePath`; §4 `mixedLebesgueENormT_eq`; §5 the force helpers and the two fields.
- `/data_8T/ping/blowup_density/.claude/worktrees/439-T15-U4-U5-energy-mixed/research/T15/probes/energy_mixed_closes.lean` — 429 declarations. Part 1: five field types copied verbatim, each closed by `exact`. Part 1b: `I03.PacketData` rebuilt from the eight verbatim `scalingStatement` clauses, so the packet bundle smuggles in nothing. Part 2: the `placement_closes.lean` geometry (cube centre, spatial bump radius `1/4`, chart ball `3/8`, `T = 1`, `ε₀ = 1/2`) with a **nonzero** packet — spatial bump times a time bump supported in `[1/4,3/4] ⊆ (0,∞)` — a complete `PlacementData` and a complete `I03.PacketData`; `energy_mixed_closes` fires all five fields at `ε = 1/2`, plus two non-vacuity examples (`0 < emM`, force nonzero at `t = 1/2`).
- `/data_8T/ping/blowup_density/.claude/worktrees/439-T15-U4-U5-energy-mixed/research/T15/axioms_u4_u5.lean` — 29 `#print axioms`, all three standard axioms.
- `/data_8T/ping/blowup_density/.claude/worktrees/439-T15-U4-U5-energy-mixed/research/T15/ATTEMPTS_U4_U5.md` — design decisions D1–D7, failures F1–F8 with exact error text.
- Modified: `/data_8T/ping/blowup_density/.claude/worktrees/439-T15-U4-U5-energy-mixed/research/T15/T15_SPLIT.md` — U4 and U5 bullet status lines plus a `### U4 / U5 status (lane 439)` section.

No `sorry`/`admit`/`axiom`/`native_decide`, no named input, no `set_option maxHeartbeats` anywhere. Committed on `erenup/439-T15-U4-U5-energy-mixed` as `0f7e2237`; nothing pushed, merged, or rebased; no existing module edited.

## 3. Gaps

No residual statement — all five fields closed. What remains outside the unit:

- Neither module discharges `PlacementData` itself. A caller must still exhibit the compact `K_*` and the chart ball with `closure B ⊆ interior Q` (needs-a-lemma ② of `COMPARISON.md`), exactly as for U2/U3.
- `packetEnergyIdentity`/`packetDissipationIdentity` take `NSFormalization.Section4.I03.PacketData` rather than eight loose hypotheses. That is an existing Section 4 `Prop` structure, and probe Part 1b proves it is constructible from eight verbatim `scalingStatement` clauses, so it is reuse rather than an extra assumption — but a reviewer who wants the clauses spelled out inline should know this is the one place where they are bundled.
- `Bindings/Scaling.lean:296 mixedLebesgueENorm_eq` and `:318 mixedLebesgueENorm_scaledForce` cannot be imported from `formalization/` (dependency direction is `verification → formalization`), so the first was re-proved on the canonical `mixedLebesgueENorm` and §5 routes through `I03.positiveMixedNorm_parabolicForce` directly. The binding layer and the canonical layer now carry the same proof twice; that duplication is structural, not something I could avoid here.

Failed approaches (full text in `ATTEMPTS_U4_U5.md`):

- `fun_prop` on the periodized gradient's continuity: `fun_prop bug: function expected, got 'periodize fun x => scaledVelocity u place.x₀ place.T ε (t, x) : SpatialField, type ctor const'`. Replaced by `I02.continuous_spatialGradient` on the constant-in-time extension.
- Rewriting `← I03.energyEssSup_scaled_eq` backwards into the `energyEssSupT` goal: `(deterministic) timeout at 'isDefEq'` and `at 'whnf'`, 200000 heartbeats. Fixed by a `show` that spells the unfolded `essSup` form, a separate `have key` for the a.e. congruence, then forward `rw`s — not by raising heartbeats.
- `rw [torusSlicePath]`: `Failed to rewrite using equation theorems for 'torusSlicePath'`. Fixed by the explicit `enorm_torusSlicePath` bridge.
- Writing slice continuity as `hH.comp (continuous_const.prodMk continuous_id)` makes Lean infer the implicit field as `H ∘ fun x => (t, id x)`, so later rewrites fail with `Did not find an occurrence of the pattern eLpNorm (torusLift (scaledForce f place.x₀ place.T ε ∘ fun x => (t, id x))) r periodicTorusMeasure`. Fixed by a `continuous_slice` helper whose statement pins the spelling.
- `refine le_trans (iInf_le _ ⟨path, ?_, meas⟩) ?_` reorders goals so bullets land wrong (`introN failed: There are no additional binders`). Fixed by hoisting the path proof into a `have`.
- Probe: `fderiv_const_smul` applied directly to `fun y => emVel (t, y)` gave a type mismatch between two instance paths for `Space` (`PiLp.normedAddCommGroup` vs `WithLp.instAddCommGroup`) because the scalar was a metavariable; fixed with a `rfl`-`show` rewrite plus explicit `(𝕜 := ℝ)` and scalar. `rw` under the unreduced image lambda `(fun t => √(l2Sq emVel t)) (1/2)` failed with `Did not find an occurrence of the pattern √(l2Sq emVel ?t)`; fixed with `show`. `emPacketData` as `def` tripped the `linter.defProp`; changed to `theorem`.

## 4. Commands run and results

All from `/data_8T/ping/blowup_density/.claude/worktrees/439-T15-U4-U5-energy-mixed`, after `. scripts/lean-env.sh`, `lake` from `verification/` with `LEAN_NUM_THREADS=6`.

- `lake build NSFormalization.Section3.T15.Energy NSFormalization.Section3.T15.Mixed` — after deleting both oleans and rebuilding: `✔ [10008/10009] Built NSFormalization.Section3.T15.Energy (2.6s)`, `✔ [10009/10009] Built NSFormalization.Section3.T15.Mixed (3.5s)`, `Build completed successfully (10009 jobs).` 0 errors.
- `lake env lean ../formalization/NSFormalization/Section3/T15/Energy.lean` — 0 output.
- `lake env lean ../formalization/NSFormalization/Section3/T15/Mixed.lean` — 0 output.
- `lake env lean ../research/T15/probes/energy_mixed_closes.lean` — 0 output.
- `lake env lean ../research/T15/axioms_u4_u5.lean` — 29 declarations; `grep -c propext` = 29, and `grep -vc "propext\|Classical.choice\|Quot.sound"` = 0, i.e. every declaration prints exactly `[propext, Classical.choice, Quot.sound]`.
- `make check` — architecture checks emitted their JSON report, `Ran 13 tests ... OK` (contract policy), `45 work items: ownership, contract registration and task cards consistent.`
- `grep -nE "sorry|admit|native_decide|^axiom |maxHeartbeats"` over the four new files — only the two doc-comment occurrences of the string "No `sorry`, no named input, no new mathematical alias."
- `git commit` on `erenup/439-T15-U4-U5-energy-mixed` → `0f7e2237`. No push, no merge, no rebase.


## Lead notes after review 439 (ACCEPT-WITH-NOTES; records corrected)

1. **Gradient guard wording (D2).** The claim that the two gradients differ on the cube frontier is false under smoothness and strict interior support (both vanish there). Correct statement: "The gradient guard is obtained from smoothness of the periodization; the value-level single-copy identity alone does not supply a derivative statement, which is why regularity is supplied separately." Applied in `ATTEMPTS_U4_U5.md` (D2) and `T15_SPLIT.md` U5 line.
2. Canonical field citations corrected to `Scaling.lean:341,352,363,376,390` (declaration starts).
3. Probe description corrected: all five U4/U5 fields are closed (comment-only edit).
4. "29 lines" → "29 declarations" (four audit entries wrap).
