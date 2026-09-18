# Lane 377 — T12 U3: the cutoff–Gagliardo comparison at `a = 1/2` (Opus prover; transcribed by the lead from the agent's final message — report-file guard)

Commit `d2af95ee0576a5f6581eb9e12b9d6614318d68fd` on `erenup/377-T12-U3-cutoff-gagliardo`. No `sorry`/`admit`/`axiom`/`native_decide`, no `maxHeartbeats` override; 21 declarations, all `[propext, Classical.choice, Quot.sound]`.

## 1. What was proved (`Section3/T12/CutoffGagliardo.lean`, 984 lines)
`theorem cutoff_gagliardo_half (v) (hv : SmoothPeriodicT v) (hmean : IsMeanZeroT v) : dotHomogeneousENorm (1/2) (cutoffMul v) ≤ ENNReal.ofReal cutoffGagliardoConst * (eLpNorm v 2 (volume.restrict fundamentalCube) + periodicHomogeneousENorm (1/2) v)`, with `cutoffGagliardoConst = max (√(2·343)) (√(2·cbConst·(cFrac (1/2)).toReal⁻¹))`, `cbConst = 686·Jval.toReal`, `Jval = ∫⁻ h, min(ofReal(cutoffLip²‖h‖²)) 1 · fractionalRadialKernel (1/2) h < ⊤`; `cutoffGagliardoConst_pos`.
Route: `wholeSpace_identity` (s = 1/2) and `torus_identity` (`meanZeroPartT v = v`); the split `χ(x+h)v(x+h) − χ(x)v(x) = χ(x+h)(v(x+h) − v(x)) + (χ(x+h) − χ(x))v(x)` gives `IReal ≤ 2·IA + 2·IB`; `iA_bound : IA v ≤ 343 · ITorus (1/2) v` (change of variables + fold onto the cube via `lintegral_cube_periodicKernel` + lattice tiling, `343 = 7³`) and `iB_bound : IB v ≤ cbConst · ‖v‖²_{L²(Q)}` (`cutoffLip` Lipschitz bound + `Jval_lt_top` + tiling); divide by `0 < cFrac (1/2) < ⊤` and take the monotone `ℝ≥0∞` square root (`enn_sqrt_div_bound`). Supporting: `ireal_cutoffMul_eq`, `itorus_meanZero_eq`, `meanZeroPartT_eq_self`, `cFrac_half_*`, `gA/gB/IA/IB`, `ireal_cutoffMul_le_split`, `dotHomogeneousENorm_cutoffMul_le`, `lattice_count_le`, ~30 lemmas.

## 2. Files
`formalization/NSFormalization/Section3/T12/CutoffGagliardo.lean`; `research/T12/probes/cutoff_gagliardo_closes.lean` (target closed verbatim; nonzero smooth mean-zero witness `probeMZ = meanZeroPartT (cos(2πx₀)·e₀)`); `research/T12/axioms_u3.lean` (21); `research/T12/ATTEMPTS_U3.md`.

## 3. Gap
None for U3 (constants honest, not sharp). Feeds U4 `velocityCriticalL3` (`dotHomogeneousENorm` here is `Section4.D01.dotHomogeneousENorm`; U4 bridges A05's spelling).

## 4. Commands and results
`lake build NSFormalization.Section3.T12.CutoffGagliardo` → success (9998 jobs), 0 errors/0 warnings; module / probe / axioms `lake env lean` → clean, 21 × standard; `make check` → OK. Pitfalls (ATTEMPTS): `rw [lintegral_add_left …]` on `gA` times out (the `ContDiffBump` cutoff unfolds under `whnf`) — abstract linearity lemma `lintegral_two_add_two`; `ℝ≥0∞` `a² ≤ b² → a ≤ b` via `ENNReal.rpow_le_rpow_iff` after `rpow_two`; pin renames (`mul_le_mul_right/left` swapped, `measurable_prodMk_left`, `Convex.norm_image_sub_le_of_norm_fderiv_le`, `Set.indicator_of_notMem`, `PiLp.single_apply`, `contDiff_piLp_apply`).
