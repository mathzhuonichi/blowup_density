# Lane 377-T12-U3-cutoff-gagliardo — T12 U3 (analytic core): the cutoff–Gagliardo comparison at `a = 1/2`, `dotHomogeneousENorm (1/2) (χ·v) ≤ C · (‖v‖_{L²(Q)} + periodicHomogeneousENorm (1/2) v)` for smooth mean-zero periodic `v`

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/377-T12-U3-cutoff-gagliardo` (git branch `erenup/377-T12-U3-cutoff-gagliardo`, based on `origin/erenup/integration-section3` after #336:
`Section3/T12/Cutoff.lean` (lane 365: `cutoff`, `largerCube`, `cutoffMul`, derivative bounds), `Section3/T13/{Localization,ConstantEndpoints,TorusIdentity,WholeSpaceIdentity,LocalizationKernel,KernelComparison}.lean`
(`wholeSpace_identity`, `torus_identity`, `cFrac`, `constant_pos_finite`, `periodicKernel_split`, `latticeTail_le_tailGeomConst`, `iTorus_singular_le` — the kernel machinery of lanes 344–354),
`Section3/T15/HaarBridge.lean` (`eLpNorm_torusLift_restrict`), `Section3/T12/{MeanZeroCalculus,SpectralGap}.lean` (`meanZeroPartT`, `IsMeanZeroT`, `spectralGap`)). Read `CLAUDE.md`,
**`research/T12/T12_SPLIT.md` §0 and unit U3 (and U4 for how it is consumed)**, `research/T13/REPORT_{348,345,354,359}.md` (the identities and the kernel-comparison technique —
U3 is the *reverse* comparison: whole-space Gagliardo integral of the cutoff piece vs the torus Gagliardo integral of `v`), `paper/sections/appendix-b-embeddings.tex`, and the top
40 lines of `logs/LESSONS.md` (**name every instance explicitly**; the `mul_le_mul_*` renames; the `tsum_subtype` defeq note).

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only.
- **No placeholders, no aliases, no named inputs, no goal repackaging.** A `def X : Prop := <goal>` or a hypothesis equal to the target is a stub and will be discarded without review;
  an honest partial with the exact residual statement and error text is fine.
- Every declaration must print exactly `[propext, Classical.choice, Quot.sound]`.

## Goal
New module `formalization/NSFormalization/Section3/T12/CutoffGagliardo.lean` (namespace `NSFormalization.Section3.T12`):
`theorem cutoff_gagliardo_half (v : SpatialField) (hv : SmoothPeriodicT v) (hmean : IsMeanZeroT v) : dotHomogeneousENorm (1/2) (cutoffMul v) ≤ ENNReal.ofReal cutoffGagliardoConst * (eLpNorm v 2 (volume.restrict fundamentalCube) + periodicHomogeneousENorm (1/2) v)`
with an explicit positive `cutoffGagliardoConst` (verify the exact norm spellings against `research/T12/probes/api_on_canonical.lean:148-151` and the T13 modules; if the `L²` term is
more natural as `eLpNorm (torusLift v) 2 periodicTorusMeasure` use `HaarBridge.eLpNorm_torusLift_restrict` to state both). Route (T12_SPLIT U3): `wholeSpace_identity` gives
`IReal (1/2) (χv) = cFrac (1/2) · dotHomogeneousENorm (1/2) (χv)²` (needs `χv` smooth compactly supported: `Cutoff.lean`); `torus_identity` gives `ITorus (1/2) v = cFrac (1/2) · periodicHomogeneousENorm (1/2) (meanZeroPartT v)²`
with `meanZeroPartT v = v` for mean-zero `v`; bound `IReal (1/2) (χv) ≤ C (ITorus (1/2) v + ‖v‖²_{L²(Q)})` by the split `χ(x)v(x) − χ(y)v(y) = χ(x)(v(x) − v(y)) + (χ(x) − χ(y)) v(y)`:
the first term's double integral over `ℝ³ × ℝ³` reduces (support of `χ` in `largerCube`, periodicity of `v`) to finitely many translates of the cube-cube integral, which is
`≤ ITorus (1/2) v` up to the kernel comparison `fractionalRadialKernel ≤ periodicKernel` (trivial direction: the `n = 0` term of the lattice sum) — careful: the `x` in `largerCube`, `y` anywhere;
split `y` by the lattice cell and use periodicity; the second term uses the Lipschitz bound `|χ(x) − χ(y)| ≤ L‖x − y‖` (bounded `fderiv`, `Cutoff.lean`) and `|χ(x) − χ(y)| ≤ 1`, giving
`∫∫ min(L²‖h‖², 1) ‖h‖^{-4} … ≤ C_L ∫ |v(y)|²` over `y ∈ largerCube`-neighbourhood (finitely many cube translates) — the kernel `min(L²‖h‖²,1)‖h‖^{-4}` is integrable on ℝ³ (`cFracRadial`-style majorant,
lane 344's `constant_pos_finite` technique). Divide by `cFrac (1/2) > 0` (finite: `constant_pos_finite`) and take the monotone `ℝ≥0∞` square root (`enn_le_of_sq_le`-style, lane 359).

## Deliverables
1. `Section3/T12/CutoffGagliardo.lean`; 2. probe `research/T12/probes/cutoff_gagliardo_closes.lean` (instantiate on the two-mode field of `research/T12/probes/tame_product_closes.lean`);
3. `research/T12/ATTEMPTS_U3.md`, `research/T12/axioms_u3.lean`, status in `research/T12/T12_SPLIT.md` U3, report `research/T12/REPORT_377.md` (if a guard blocks the write, put the
full report in your final message).

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T12.CutoffGagliardo` (0 errors), `lake env lean` on module / probe / axioms file; `make check`.

## Report
Commit on your branch; end with four parts (theorems with exact statements and the constant / files / gaps with exact error text / commands and results).
