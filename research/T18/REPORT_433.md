# REPORT_433 — T18 U5 cross-transport + U6 momentum (Opus; transcribed by lead from the agent message, report-file guard)

Lane 433 complete — both units closed, no gaps, no named inputs.

## 1. What was proved

**U5 — the two vanishing cross-transport terms** (`eq:bgzero`, `paper/sections/03-torus.tex:322-328`). Both Spec fields, with types equal to `research/T18/Spec.lean:1838` / `:1848` under the `InsertionData` projections:

```lean
theorem crossTransport_background_advects_packet (data : InsertionData) :
    ∀ ε ∈ Ioc (0 : ℝ) (ε₀ data), ∀ t ∈ Ico (0 : ℝ) data.place.T, ∀ x : Space,
      spatialDerivative
          (periodizedScaledVelocity data.packetVelocity data.place.x₀ data.place.T ε) t x
          (correctedBackground data.reference.velocity data.D.correction ε (t, x)) = 0

theorem crossTransport_packet_advects_background (data : InsertionData) :
    ∀ ε ∈ Ioc (0 : ℝ) (ε₀ data), ∀ t ∈ Ico (0 : ℝ) data.place.T, ∀ x : Space,
      spatialDerivative
          (correctedBackground data.reference.velocity data.D.correction ε) t x
          (periodizedScaledVelocity data.packetVelocity data.place.x₀ data.place.T ε (t, x)) = 0
```

**U6 — the exact momentum equation** (`Spec.lean:1774`):

```lean
theorem momentum (data : InsertionData) : ∀ ε ∈ Ioc (0 : ℝ) (ε₀ data),
    ∀ t ∈ Ioo (0 : ℝ) data.place.T, ∀ x : Space,
      NavierStokesR3.ProblemStatement.navierStokesResidual data.ν
        (velocity data ε) (pressure data ε) t x = force data ε (t, x)
```

Routes actually used: the case split for U5 is at exactly `t_ε = T − ε²` — below it the periodized packet *slice* is the constant zero function (the parabolic source time `(ε⁻¹)²(t−(T−ε²))` is non-positive and `zeroPastField` is the `if 0 < z.1` conditional), at and above it `correction.potential.correction_cancels` hands over the open removal set, and the Section 4 lemma `NSFormalization.Source.cross_advection_eq_zero` closes both terms including the outside-the-support half. Two facts made this cheap and are worth reusing: `T16.periodicScaledPacket` and `T15.periodizedScaledVelocity` are `rfl`-equal, and `NSFormalization.Source.residual ν` is `rfl`-equal to `NavierStokesR3.ProblemStatement.navierStokesResidual ν`, so the whole Section 4 residual calculus (`residual_add`, `corrected_background`) applies to the torus statement with no transport lemma. Both mean-zero pressure gauges (the inserted `normalizePressureT (π + P_ε)` and the packet's pinned `normalizedScaledPressure`) are removed by one **hypothesis-free** lemma `pressureGradient_normalizePressureT` via `fderiv_sub_const` — no integrability is needed, unlike lane 426's `pressure_smooth`.

## 2. What exists in Lean now

- `/data_8T/ping/blowup_density/.claude/worktrees/433-T18-U5-U6-cross-transport-momentum/formalization/NSFormalization/Section3/T18/CrossTransport.lean` (97 lines) — `periodicScaledPacket_eq`, `packet_slice_zero`, `crossTransport_pair`, and the two Spec-field theorems.
- `.../formalization/NSFormalization/Section3/T18/Momentum.lean` (192 lines) — `contDiff_two_of_smooth`, `slice_contDiff`, `slice_contDiff_two`, `slab_temporal_differentiable`, `pressureGradient_normalizePressureT`, `residual_normalizePressureT`, `reference_interior_time`, `corrected_background_momentum`, `momentum`.
- `.../research/T18/probes/u5_u6_closes.lean` (277 lines) — the three Spec-spelled field types (`Spec.PeriodicInsertionU5U6Fields`) discharged by the canonical theorems through the lane-422/426 U1 conversions.
- `.../research/T18/axioms_u5_u6.lean` — 14 `#print axioms`, all exactly `[propext, Classical.choice, Quot.sound]`.
- `.../research/T18/ATTEMPTS_U5_U6.md`, status lines for U5/U6 in `.../research/T18/T18_SPLIT.md`.
- Commit `58e94178` on `erenup/433-T18-U5-U6-cross-transport-momentum`. No existing module was edited; no push/merge/rebase.

## 3. Gaps

None for the three targeted fields — they are proved outright from the threaded `scaling` / `correction` / `reference` records, with no named input, no added hypothesis and no `sorry`. The only residual is the one U1–U4 already carry: end-to-end non-vacuity of the whole `PeriodicInsertionAPI` still waits on the T15 U15 and T17 U12 assembly witnesses, which are out of this lane's scope.

Four failed approaches, all recorded in `ATTEMPTS_U5_U6.md`:
- `Source.exact_insertion` proves the U6 goal in one step but demands the *neighbourhood-removal* hypothesis, strictly stronger than the two Spec cross-transport fields — using it would make U6 re-derive U5 rather than consume it. Rejected on design grounds, not compilation.
- `simp only [spatialDerivative, hz, fderiv_const]` left `⊢ fderiv ℝ (fun x => 0) x = 0` — at this pin `fderiv_const` is the funext form, so the applied form also needs `Pi.zero_apply`. Error text: `Tactic 'rfl' failed: The left-hand side fderiv ℝ (fun x => 0) x is not definitionally equal to the right-hand side 0`.
- `ContDiff.of_le (by exact_mod_cast le_top)` for `∞ → 2`: `error: mod_cast has type ?m.57 ≤ ⊤ but is expected to have type 2 ≤ ∞` (three sites). `∞` is `((⊤ : ℕ∞) : WithTop ℕ∞)`, not the top of `WithTop ℕ∞`; the `ResidualCalculus` spelling `WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)` works and is isolated as `contDiff_two_of_smooth`.
- `slice_contDiff` stated only for `SpaceTimeField` cannot serve the pressure slices: `error: Type mismatch … has type DifferentiableAt ℝ (fun y => ?m.285 (t, y)) x but is expected to have type DifferentiableAt ℝ (fun y => data.reference.pressure (t, y)) x`. Fixed by generalizing the codomain to any `NormedSpace ℝ V`.
- `rw [show pressure data ε = normalizePressureT … from rfl]` before `residual_normalizePressureT` left an unsolvable metavariable (`Eq.symm (residual_normalizePressureT data.ν (velocity data ε) ?m.699 t x)` vs the goal): the two velocity arguments are defeq but not syntactically equal. An explicit `show … = _` that unfolds the whole LHS works.
- `push_neg` is deprecated at this pin (`Prefer using push Not`); replaced by `rw [not_lt]`.

## 4. Commands run and results

All from the worktree, after `. scripts/lean-env.sh`, `lake` from `verification/` with `LEAN_NUM_THREADS=6`:

- `lake build NSFormalization.Section3.T18.CrossTransport NSFormalization.Section3.T18.Momentum` → `Build completed successfully (10021 jobs).`, 0 errors, 0 warnings from either new module.
- `lake env lean ../formalization/NSFormalization/Section3/T18/CrossTransport.lean` → no output, exit 0.
- `lake env lean ../formalization/NSFormalization/Section3/T18/Momentum.lean` → no output, exit 0.
- `lake env lean ../research/T18/probes/u5_u6_closes.lean` → no output, exit 0 (the Spec-form fields close).
- `lake env lean ../research/T18/axioms_u5_u6.lean` → 14 lines, every one `depends on axioms: [propext, Classical.choice, Quot.sound]`.
- `make check` → contract/architecture checks pass, `Ran 13 tests … OK`, `45 work items: ownership, contract registration and task cards consistent.`
- `grep` for `sorry|admit|native_decide|axiom` over the five new/changed files → no hits other than the `#print axioms` lines.
- Duplicate-name check across all six `Section3/T18/*.lean` (`awk`+`uniq -d`) → empty, so no clash with lanes 422/426.


> Lead notes after review 433: the report's "Four failed approaches" list actually enumerates six (count corrected here); `58e94178` is the implementation commit and `324c1cb1` the (lead-transcribed) report commit; the base-aware contract gate failed only because the worktree predates #392's `AffineVariation.lean` — the merge into integration below refreshes the base, and the lane touches no `verification/` file.
