# REPORT_396 — T12 U4 `velocityCriticalL3` (Opus; transcribed by lead from the agent message, report-file guard)

Committed as `ab7567b829c286a524fe7bfa53e813f1d343ca37`. Everything builds clean and audits to the standard three axioms.

---

# Lane 396 — T12 U4 `velocityCriticalL3` (mean-zero `Ḣ^{1/2}(T³) ↪ L³(T³)`)

Commit **`ab7567b829c286a524fe7bfa53e813f1d343ca37`** on branch `erenup/396-T12-U4-velocity-critical-l3`. No `sorry`/`admit`/`axiom`/`native_decide`, no `maxHeartbeats` override, new files only.

## 1. What was proved (exact statements + constant)

Main theorem (`velocityCriticalL3` verbatim in LHS/RHS, under the smoothness its inputs require):
```
theorem velocityCriticalL3_smooth (v : SpatialField) (hv : SmoothPeriodicT v)
    (hmean : IsMeanZeroT v) :
    periodicLpENorm 3 v ≤ ENNReal.ofReal CcriticalHalf * periodicHomogeneousENorm (1 / 2) v
```
Constant: `def CcriticalHalf : ℝ := criticalL3Const * cutoffGagliardoConst * (gapConst (1/2) + 1)`, with `theorem CcriticalHalf_pos : 0 < CcriticalHalf` (`criticalL3Const` = A05 whole-space critical constant, `cutoffGagliardoConst` = lane 377's U3 constant, `gapConst (1/2)` = spectral-gap constant).

Supporting theorems (both new, both consumed by the main proof), plus the norm bridge:
- `periodicSobolevENorm_zero_le_half (v) : periodicSobolevENorm 0 v ≤ periodicSobolevENorm (1/2) v` (physical `L²(T³)` ≤ inhomogeneous `H^{1/2}(T³)`, via a bounded even `reweightDatum`).
- `l2Q_le_homogeneous_half (v) (SmoothPeriodicT v) (MemPeriodicHomogeneous (1/2) v) : eLpNorm v 2 (volume.restrict fundamentalCube) ≤ ENNReal.ofReal (gapConst (1/2)) * periodicHomogeneousENorm (1/2) v`.
- `a05_dotHomogeneousENorm_eq : A05.dotHomogeneousENorm = D01.dotHomogeneousENorm` (the rfl spelling bridge, reproved locally because `formalization/` cannot import `verification/Bindings`).

Route (exactly T12_SPLIT U4): `periodicLpENorm 3 v = eLpNorm v 3 (restrict Q)` (HaarCube) `= eLpNorm (cutoffMul v) 3 (restrict Q)` (`cutoffMul = v` on `Q`) `≤ eLpNorm (cutoffMul v) 3 volume` (`Measure.restrict_le_self`) `≤ ofReal criticalL3Const · dotHomogeneousENorm (1/2) (cutoffMul v)` (registered `A05.velocityCriticalL3` + `memHInfty_cutoffMul` + the rfl bridge) `≤ ofReal criticalL3Const · (ofReal cutoffGagliardoConst · (‖v‖_{L²(Q)} + periodicHomogeneousENorm (1/2) v))` (lane 377's `cutoff_gagliardo_half`); the `‖v‖_{L²(Q)}` remainder is absorbed by `l2Q_le_homogeneous_half` (order-zero Parseval `T15.periodicSobolevENorm_zero_eq` + `periodicSobolevENorm_zero_le_half` + `SpectralGap.spectralGap`); ℝ≥0∞ semiring algebra collapses the three constants to `CcriticalHalf`. `periodicHomogeneousENorm (1/2) v = ⊤` ⇒ RHS `= ⊤`, trivial (`ENNReal.mul_top`).

## 2. What exists in Lean now (absolute paths)
- `/data_8T/ping/blowup_density/.claude/worktrees/396-T12-U4-velocity-critical-l3/formalization/NSFormalization/Section3/T12/CriticalL3.lean` — 6 declarations, builds 0 errors / 0 warnings.
- `/data_8T/ping/blowup_density/.claude/worktrees/396-T12-U4-velocity-critical-l3/research/T12/probes/critical_l3_closes.lean` — closes the smooth API form by `exact`, non-vacuous on `probeMZ = meanZeroPartT (x ↦ cos(2π x₀)·e₀)`.
- `/data_8T/ping/blowup_density/.claude/worktrees/396-T12-U4-velocity-critical-l3/research/T12/axioms_u4.lean` — all 6 print `[propext, Classical.choice, Quot.sound]`.
- `/data_8T/ping/blowup_density/.claude/worktrees/396-T12-U4-velocity-critical-l3/research/T12/ATTEMPTS_U4.md`, and U4 status added to `.../research/T12/T12_SPLIT.md`.

## 3. Gap (exact residual)
The verbatim API field quantifies over `MemPeriodicHomogeneous (1/2) v`, which carries **no smoothness** (`MeanZeroCalculus.lean:60` = periodicity + `MemLp 2` + mean-zero + finite homogeneous norm). Both analytic inputs need smoothness (`memHInfty_cutoffMul` needs `ContDiff ℝ ∞ v`; `cutoff_gagliardo_half` needs `SmoothPeriodicT v`), so the general case genuinely requires torus density, not reindexing. Residual not proved:
```
theorem velocityCriticalL3 (v : SpatialField) (hv : MemPeriodicHomogeneous (1 / 2) v) :
    periodicLpENorm 3 v ≤ ENNReal.ofReal CcriticalHalf * periodicHomogeneousENorm (1 / 2) v
```
It needs: (i) periodic mollification `v_ε` (smooth, periodic, mean-zero); (ii) `periodicHomogeneousENorm (1/2) v_ε ≤ periodicHomogeneousENorm (1/2) v` (mollifier symbol `|φ̂_ε(k)| ≤ 1`); (iii) `v_ε → v` a.e. + Fatou/lower-semicontinuity of `eLpNorm · 3` giving `periodicLpENorm 3 v ≤ liminf periodicLpENorm 3 v_ε`; (iv) `velocityCriticalL3_smooth` on each `v_ε`, pass to `liminf`. The L³ lower semicontinuity of the LHS (whose finiteness is the conclusion) is the crux — a separate `L` lane. **U6 uses U4 only on smooth `∂_j v`, `Lv`, so `velocityCriticalL3_smooth` unblocks U6 now.** No residual *errors* — the smooth theorem compiles with 0 errors; the gap is the missing density lane above.

Pitfalls (in ATTEMPTS_U4.md): `mul_le_mul_left'` is `unknown identifier` here → used `gcongr` (which also auto-discharges the absorb leaf from `hL`); `reweightDatum_enorm_le`, `periodicFrequencyWeight_pos/_neg`, `ParsevalZero.memLp_torusLift_smooth` are **private** → reconstructed from public `reweightDatum_norm_le`+`ofReal_norm`, `one_le_fourierWeight`/`fourierWeight_neg`, `T10.memLp_torusLift_vector`; the iInf-leaf subtype-norm equality is defeq-not-syntactic → split off `hnorm` and closed by `exact` (mirroring `homogeneous_le_sobolev`).

## 4. Commands and results
- `cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T12.CriticalL3` → `✔ Built NSFormalization.Section3.T12.CriticalL3`, 0 errors.
- `lake env lean ../formalization/NSFormalization/Section3/T12/CriticalL3.lean` → empty (0 warnings).
- `lake env lean ../research/T12/probes/critical_l3_closes.lean` → empty (all `example`s close).
- `lake env lean ../research/T12/axioms_u4.lean` → 6 declarations, each `[propext, Classical.choice, Quot.sound]`.
- `make check` → OK (13 contract-policy tests pass; 45 work items consistent).
