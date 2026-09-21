# REPORT_415 — T20 U8 `criticalEnergy` (Opus; transcribed by lead from the agent message, report-file guard)

Lane 415 is complete. U8 closed with no residual.

## 1. What was proved

`eq:criticalenergy` (`paper/sections/03-torus.tex:420-440`) — the critical energy differential inequality of `prop:critical` — as the `criticalEnergy` field of `CriticalRegularityTAPI` **verbatim**, with `C₀` instantiated at lane 413's explicit `criticalTrilinearConst`:

```lean
theorem criticalEnergy : ∀ (ν : ℝ), 0 < ν →
    ∀ (g : SpaceTimeField), g ∈ forceClassT →
      ∀ (T : ℝ) (w : ClassicalSolutionT ν (fun _ : Space ↦ 0) g T),
        ∀ t ∈ Ioo (0 : ℝ) T,
          ∃ E' : ℝ,
            HasDerivAt
                (fun s ↦ (criticalY (meanFreeVelocity g w.velocity) s).toReal ^ 2)
                E' t ∧
              E' / 2 +
                  (ν - criticalTrilinearConst *
                    (criticalY (meanFreeVelocity g w.velocity) t).toReal) *
                    (criticalZ (meanFreeVelocity g w.velocity) t).toReal ^ 2 ≤
                (criticalB (meanFreeForce g) t).toReal *
                  (criticalY (meanFreeVelocity g w.velocity) t).toReal
```

No named input, no placeholder, no goal repackaging, no `maxHeartbeats` override. All 21 declarations print exactly `[propext, Classical.choice, Quot.sound]`.

The route is Fourier-side throughout except the nonlinear term. `y(r)² = ∑ₖ |2πk| ∑ᵢ|û_i(k,r)|²` comes from lane 389's mean formula (`v(r,·) = meanZeroPartT (u(r,·))`) plus `T13.exists_homogeneous_datum`; it is differentiated by T11's `hasDerivAt_torusSobolevNormAt_sq` template transplanted to the homogeneous order-1/2 weight (the one new input being `homogeneousDatumWeight (1/2) k ^ 2 = √(4π²|k|²) ≤ periodicFrequencyWeight k ^ (1:ℝ)`, so T11's order-1 majorant dominates unchanged). The pressure term is already gone in T11's `freqEnergyDerivT_split` at order 0. The force term is `T11.torusRealPairing_le` on the order-1/2 homogeneous data. The nonlinear term is lane 413's `criticalTrilinear_pairing`, reached through a new torus Parseval for the real `L²` pairing and `T12.lambda_exists`.

**One finding worth the lead's attention: U8 does not depend on U5.** The physical skew-adjointness route for `⟪(m·∇)v, Λv⟫ = 0` would need both U5 (`constantTransportCommutesLambda`, unproved) and self-adjointness of `Λ` (nowhere in the tree). On the Fourier side it is three lines — the symbol `∑ⱼ mⱼ·2πikⱼ` is purely imaginary and `∑ᵢ conj(ĉᵢ)ĉᵢ` is real. U4 `constantTransportSkew` is likewise not used by U8.

## 2. What exists in Lean now

- `/data_8T/ping/blowup_density/.claude/worktrees/415-T20-U8-critical-energy/formalization/NSFormalization/Section3/T20/CriticalEnergy.lean` (753 lines, 21 declarations). Reusable beyond U8: `hasSum_periodicPairing` (torus Parseval for the real `L²` pairing of two smooth periodic vector fields), `periodicFourierCoeff_fderiv_dir` / `re_sum_conj_fderiv_dir_zero` (the constant-transport symbol and its drop), `hasDerivAt_tsum_critFreqEnergy` (order-1/2 homogeneous energy differentiability), `homENorm_toReal_eq_norm` / `homENorm_toReal_sq`, `meanFreeVelocity_slice_eq`, `advection_mean_split`, `rawEnergyDeriv_split`.
- `/data_8T/ping/blowup_density/.claude/worktrees/415-T20-U8-critical-energy/research/T20/probes/critical_energy_closes.lean` — checks `example (API : CriticalRegularityTAPI) : criticalEnergyFieldType API.C₀ := API.criticalEnergy` (so the spelling is the structure field, not a paraphrase) and `example : criticalEnergyFieldType criticalTrilinearConst := criticalEnergy`; plus a non-vacuity instance (`g = 0 ∈ forceClassT`, an explicitly constructed `ClassicalSolutionT 1 (fun _ ↦ 0) 0 1`, `t = 1/2`) producing an actual real derivative witness.
- `/data_8T/ping/blowup_density/.claude/worktrees/415-T20-U8-critical-energy/research/T20/axioms_u8.lean`, `.../research/T20/ATTEMPTS_U8.md`, U8 status block in `.../research/T20/T20_SPLIT.md`, one line at the top of `.../logs/LESSONS.md`.
- Committed as `66176d3d` on `erenup/415-T20-U8-critical-energy`; working tree clean; nothing pushed, merged or rebased; no existing module edited.

## 3. Gap

None for U8 — the field is closed outright. Two caveats for the consumer (U13):

- The non-vacuity instance is the zero force with the zero solution (the brief's sanctioned fallback). A nonzero-force instance needs a concrete compactly-time-supported bump in `forceClassT` plus T11 local existence; neither is assembled anywhere in the tree today, so I did not manufacture one.
- U8 fixes `C₀ = criticalTrilinearConst`. U13 must install that same constant (it is positive by `criticalTrilinearConst_pos`) and pick `c < 1/(4·criticalTrilinearConst)`.

Failed approaches, all recorded in `ATTEMPTS_U8.md`: the physical skew route (needs U5 + `Λ` self-adjointness); the polarization route for the pairing Parseval (prepared, unnecessary — Mathlib's `UnitAddTorus.hasSum_prod_mFourierCoeff` is direct); building an order-1/2 `PeriodicSobolev` datum for the convection (blocked, the convection field is not mean-zero so `IsPeriodicHomogeneousDatum` does not apply). Three pin-specific compile failures cost one round each: `rw [← integral_ofReal]` does not match `Complex.ofReal` (use `integral_complex_ofReal`); `IsPeriodicHomogeneousDatum`'s coefficient clause is a **ℂ**-smul so `Complex.real_smul` fails and `smul_eq_mul` is needed; and `rw`'s closing `rfl` does not see through `velocityCoeffT`, so crossing that spelling needs `exact`/type ascription.

## 4. Commands run and results

All from the worktree, `. scripts/lean-env.sh`, `lake` from `verification/` with `LEAN_NUM_THREADS=6`.

- `lake build NSFormalization.Section3.T20.CriticalTrilinear NSFormalization.Section3.T20.MeanReduction NSFormalization.Section3.T13.TorusIdentity` → `Build completed successfully (10647 jobs).`
- `lake build NSFormalization.Section3.T20.CriticalEnergy` → `Build completed successfully (10648 jobs).` (0 errors; only pre-existing upstream `linter.style.haveILetI` warnings from `NSFormalization/Source/FractionalRealization.lean`)
- `lake env lean ../formalization/NSFormalization/Section3/T20/CriticalEnergy.lean` → no output, exit 0
- `lake env lean ../research/T20/probes/critical_energy_closes.lean` → no output, exit 0
- `lake env lean ../research/T20/axioms_u8.lean` → 21 lines, every one `depends on axioms: [propext, Classical.choice, Quot.sound]`
- `make check` → `OK` … `45 work items: ownership, contract registration and task cards consistent.`
- Intermediate failures before the fixes: `CriticalEnergy.lean:555 unsolved goals`, `:599 / :604 Tactic rewrite failed: Did not find an occurrence of the pattern` (the `velocityCoeffT`-defeq and `Complex.real_smul` issues above), plus a deprecation on `continuous_finset_sum` → `continuous_finsetSum`.

Three sub-pieces (the pairing Parseval, the transport drop, the order-1/2 derivative) were developed in parallel as scratch files and merged verbatim into the single module; the scratch files were deleted after merging, which is noted in `ATTEMPTS_U8.md`.
