# REPORT_428 — T20 U9 `yBound` (Opus; transcribed by lead from the agent message, report-file guard)

Lane 428 is complete. U9 closed with no residual — the force-path continuity/FTC was **not** the long pole.

## 1. What was proved

`eq:ybound` (`paper/sections/03-torus.tex:446-458`) — the continuity-bootstrap conclusion of `prop:critical` — as the `yBound` field of `CriticalRegularityTAPI` **verbatim**, at an explicit smallness constant:

```lean
theorem yBound : ∀ (ν : ℝ), 0 < ν →
    ∀ (g : SpaceTimeField), g ∈ forceClassT →
      criticalRho g < ENNReal.ofReal (criticalSmallness * ν) →
        ∀ (T : ℝ) (w : ClassicalSolutionT ν (fun _ : Space ↦ 0) g T),
          ∀ t ∈ Ico (0 : ℝ) T,
            criticalY (meanFreeVelocity g w.velocity) t ≤
                ∫⁻ s in Ioc (0 : ℝ) t, criticalB (meanFreeForce g) s ∧
              (∫⁻ s in Ioc (0 : ℝ) t, criticalB (meanFreeForce g) s) ≤
                criticalRho g
```

**The constant.** `criticalSmallness = 1 / (8 * criticalTrilinearConst)` — that is `c = 1/(8 C₀)` with `C₀` lane 413/415's `criticalTrilinearConst`, the same constant U8 installs. Two facts are exported for U13: `criticalSmallness_pos : 0 < criticalSmallness` and `criticalSmallness_lt_quarter : criticalSmallness < 1 / (4 * criticalTrilinearConst)` — the latter is the structure's **strict** field `c_lt_C₀`, so U13 installs `c := criticalSmallness`, `C₀ := criticalTrilinearConst` directly. I chose `1/(8 C₀)` rather than the paper's borderline `1/(4 C₀)` precisely because the structure field is strict; the *proof* only needs `c ≤ 1/(2 C₀)`, and that weaker form is exported as `yBound_of_le {c} (hc : c ≤ 1 / (2 * criticalTrilinearConst))` with the identical conclusion, so U13 may instead instantiate at any smaller `c` it needs for the `c < 1/(4 C₁)` (U10) shrinking without reproving anything.

No named input, no placeholder, no goal repackaging, no `maxHeartbeats` override, no edits to existing modules. All 36 declarations print exactly `[propext, Classical.choice, Quot.sound]`.

The route in one paragraph: a single bounded even symbol `critSymbol k = |2πk|^{1/2}/(1+4π²|k|²)^{1/2}`, packaged by T11's `torusMultiplierCLM` as a contraction `critLower : PeriodicSobolev 1 →L[ℝ] PeriodicSobolev (1/2)`, sends an order-one *inhomogeneous* datum of any periodic field to the order-`1/2` *homogeneous* datum of its mean-free part (the torus copy of `R43/ForcePath.lean`'s two-step Bessel lowering). Fed lane 312's `T10.force_coefficient_path`, it makes `b(t) = ‖h(t)‖_{Ḣ^{1/2}}` continuous on **all** of `ℝ`, so `N(t) = ∫₀ᵗ b` is everywhere differentiable with `N' = b` by `intervalIntegral.integral_hasDerivAt_right`. Fed `w.sobolev 1`, the same map gives continuity of `y` on `Ico 0 T` and `y(0) = 0`. The scalar core is `Paper1.critical_norm_bound` applied to the clamped profile `ŷ s = y (min (max s 0) t)` at `K = ν/(2C₀)`, followed by a **second** pass through `Paper1.sqrt_energy_le_primitive` to upgrade its `y ≤ ρ` into the paper's `y(t) ≤ N(t)`. The `∫₀ᵗ b ≤ ρ` half is U3 `bIntegral` plus `lintegral_mono_set Ioc_subset_Ioi_self`.

**Finding worth the lead's attention:** the brief and the split both flagged "the critical-primitive FTC is the analytic residue". It is not. `force_coefficient_path` (lane 312) already delivers a globally continuous, compactly supported order-one datum path, so the whole force path — slice continuity, interval integrability, primitive FTC — is four short lemmas with no new analysis. What actually cost a design decision was the scalar interface: `critical_norm_bound` demands `Continuous y` on all of `ℝ` while T11 only gives `ContinuousOn … (Ico 0 T)`, and its conclusion is the *weaker* `y ≤ ρ`, not the paper's `y ≤ ∫₀ᵗ b`.

## 2. What exists in Lean now

- `/data_8T/ping/blowup_density/.claude/worktrees/428-T20-U9-ybound/formalization/NSFormalization/Section3/T20/YBound.lean` (514 lines, 36 declarations). Reusable beyond U9, and I expect U10/U11/U13 to want all of them: `critSymbol` / `critLower` / `critLower_isHomogeneousDatum` (order-1 → homogeneous-1/2 datum transport); `criticalForceProfileT`, `criticalForcePrimitiveT` and their API (`exists_criticalForcePath`, `criticalB_ne_top`, `criticalB_eq_ofReal`, `criticalForceProfileT_continuous`, `criticalForcePrimitiveT_hasDerivAt`, `criticalForcePrimitiveT_continuous`, `lintegral_criticalB_eq`, `criticalForcePrimitiveT_le_rho`); `criticalYProfileT` and its API (`exists_velocityOrderOnePath`, `criticalY_eq_enorm`, `criticalY_ne_top`, `criticalY_eq_ofReal`, `continuousOn_criticalYProfileT`, `criticalYProfileT_zero`); and the general-purpose `homENorm_zero`.
- `/data_8T/ping/blowup_density/.claude/worktrees/428-T20-U9-ybound/research/T20/probes/ybound_closes.lean` — checks `example (API : CriticalRegularityTAPI) : yBoundFieldType API.c := API.yBound` (so the spelling is the structure field, not a paraphrase), `example : yBoundFieldType criticalSmallness := yBound`, and `0 < criticalSmallness ∧ criticalSmallness < 1/(4*criticalTrilinearConst)`; plus non-vacuity at lane 415's zero-force zero-solution instance, including a proof that the **smallness hypothesis itself is satisfiable** (`zero_criticalRho_le : criticalRho 0 ≤ 0`, so `ρ = 0 < c·ν`) — without that the field would be vacuously true on the only instance in the tree.
- `/data_8T/ping/blowup_density/.claude/worktrees/428-T20-U9-ybound/research/T20/axioms_u9.lean`, `/data_8T/ping/blowup_density/.claude/worktrees/428-T20-U9-ybound/research/T20/ATTEMPTS_U9.md`, the U9 status block in `/data_8T/ping/blowup_density/.claude/worktrees/428-T20-U9-ybound/research/T20/T20_SPLIT.md`, one line at the top of `/data_8T/ping/blowup_density/.claude/worktrees/428-T20-U9-ybound/logs/LESSONS.md`.
- Committed as `d8b62d68` on `erenup/428-T20-U9-ybound`; working tree clean; nothing pushed, merged or rebased.

## 3. Gap

None for U9 — the field is closed outright. Three notes for the consumer (U13):

- Non-vacuity is again the zero force with the zero solution (lane 415's sanctioned fallback). A nonzero-force instance still needs a concrete compactly-time-supported bump in `forceClassT` plus T11 local existence; neither is assembled anywhere in the tree, so I did not manufacture one.
- U9 fixes `C₀ = criticalTrilinearConst` through U8 (`criticalEnergy` is used as-is). U13 must install that same `C₀` and a `c ≤ 1/(2 C₀)`; `yBound_of_le` covers any such `c`.
- `y(0) = 0` is derived from `w.initial` (zero initial datum) via `meanFreeVelocity_slice_eq`. It is specific to the from-rest solution class the field quantifies over; there is nothing to fix, but a later restart-based argument would need its own version.

Failed approaches, all recorded in `ATTEMPTS_U9.md`: re-deriving `continuous_bootstrap` with `ContinuousOn` (abandoned for the clamp, which reuses the scalar lemmas verbatim in ten lines); trying to get `y ≤ ∫₀ᵗ b` out of `critical_norm_bound` alone (impossible — its last step `.trans (hNbound t ht)` discards `N`); `exact_mod_cast` and `simpa only [Nat.cast_one]` for `IsPeriodicDatum ((1:ℕ):ℝ) → IsPeriodicDatum (1:ℝ)` (both fail at this pin; `have hcast := Nat.cast_one; rw [hcast] at h` works); `rw [eLpNorm_zero]` in the probe (does not unify through the submodule norm now that `eLpNorm_zero` is stated over the generic `ENorm` carrier — `eLpNorm_zero'` closes it); `ENNReal.zero_toReal` (does not exist; `rfl`); `positivity` on `criticalTrilinearConst` (opaque `def`, as in lanes 405/413).

## 4. Commands run and results

All from the worktree, `. scripts/lean-env.sh`, `lake` from `verification/` with `LEAN_NUM_THREADS=6`.

- `lake build NSFormalization.Section3.T20.CriticalEnergy NSFormalization.Section3.T20.BIntegral NSFormalization.Paper1.ScalarEnergy NSFormalization.Section3.T10.ForcePaths NSFormalization.Section3.T11.LocalExistence` → `Build completed successfully (10649 jobs).`
- `lake build NSFormalization.Section3.T20.YBound` → `Build completed successfully (10650 jobs).` (0 errors; only pre-existing upstream `linter.style.haveILetI` / `linter.unusedSimpArgs` warnings replayed from `NSFormalization/Source/*` and `vendor/HeliCorgi/Formal/*`)
- `lake env lean ../formalization/NSFormalization/Section3/T20/YBound.lean` → no output, exit 0
- `lake env lean ../research/T20/probes/ybound_closes.lean` → no output, exit 0
- `lake env lean ../research/T20/axioms_u9.lean` → 36 declarations, every one `depends on axioms: [propext, Classical.choice, Quot.sound]` (verified by script after whitespace normalisation: `declarations: 36`, `bad: []`)
- `grep -nE "sorry|admit|axiom|native_decide" …/YBound.lean` → no matches
- `make check` → `OK` … `Ran 13 tests … OK` … `45 work items: ownership, contract registration and task cards consistent.`
- Intermediate failures, one round each: `YBound.lean:72 Application type mismatch: Paper1.one_le_periodicFrequencyWeight k has type 1 ≤ Paper1.periodicFrequencyWeight k but is expected to have type 1 ≤ periodicFrequencyWeight k` (T10 and Paper1 have distinct `periodicFrequencyWeight` defs — I proved a two-line local `one_le_periodicFrequencyWeight'`); `Type mismatch: After simplification, term hG t has type IsPeriodicDatum (↑1) … but is expected to have type IsPeriodicDatum 1 …` (twice, the `Nat.cast_one` trap); `simp made no progress` on `‖(0 : PeriodicSobolev s)‖ₑ = 0`; `unsolved goals ⊢ ENNReal.toReal 0 = 0`; and in the probe `Tactic rewrite failed: Did not find an occurrence of the pattern eLpNorm 0 ?p ?μ in the target expression eLpNorm 0 1 forceTimeMeasure ≤ 0`.

Two instance probes were used and deleted before committing (`tmp_probe_inst.lean` confirmed that `torusMultiplierCLM` and the `PeriodicSobolev` norm are usable from a fresh T20 module without re-declaring the `local instance`s that every T11 module carries; `tmp_probe_cast.lean` isolated the `Nat.cast_one` rewrite). Both are noted in `ATTEMPTS_U9.md`.
