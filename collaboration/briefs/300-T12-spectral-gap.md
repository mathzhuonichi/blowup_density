# Lane 300-T12-spectral-gap — T12 fields `spectralGap` and `homogeneous_le_sobolev` (mean-zero `H^s ≍ Ḣ^s` on the torus)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/300-T12-spectral-gap` (git branch `erenup/300-T12-spectral-gap`, based on `origin/erenup/integration-section3`: it contains the canonical modules
`formalization/NSFormalization/Section3/T10/PeriodicData.lean` (+ the proof modules `PhysicalBridge`, `DatumBasics`, `Parseval`, `Leray` — note: until lane 296 lands, `Parseval`/`DatumBasics`/`PhysicalBridge`
cannot be imported together; import at most one of them, or none) and `Section3/T12/MeanZeroCalculus.lean`, and the probe `research/T12/probes/api_on_canonical.lean` stating the Type-valued
`MeanZeroSobolevCalculusAPI` over them). Read `CLAUDE.md`, `research/T12/Spec.lean` docstrings of `spectralGap`/`homogeneous_le_sobolev`, `research/T12/RECONCILIATION.md` §0/§3,
`research/T10/RECONCILIATION.md` §5 (amendment 1), `research/T12/CANONICAL.md`, and the top 40 lines of `logs/LESSONS.md` (**name every instance explicitly**).

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. New files only; no edits to existing modules.
- The target statements are **exactly** the two fields of `research/T12/probes/api_on_canonical.lean` with the constant `Cgap` instantiated by your explicit `gapConst : ℝ → ℝ`
  (positivity `∀ s, 0 ≤ s → 0 < gapConst s` proved too). A probe `research/T12/probes/spectral_gap_closes.lean` must show this by `example`s whose statements are the field
  statements with `Cgap := gapConst` substituted verbatim.
- Every declaration prints exactly `[propext, Classical.choice, Quot.sound]`; include a non-vacuity `example` (e.g. a single nonzero Fourier mode, or the zero field).

## Goal
- `homogeneous_le_sobolev : ∀ s, 0 ≤ s → ∀ v, MemPeriodicHomogeneous s v → periodicHomogeneousENorm s v ≤ periodicSobolevENorm s v` (constant 1): from an inhomogeneous datum `A`
  (`IsPeriodicDatum s v A`), build the homogeneous datum `B` with `B i k := (homogeneousDatumWeight s k / periodicFrequencyWeight k ^ (s/2)) • A i k` (zero at `k = 0`); show `B ∈ lp 2` and
  real (weight ratio in `[0,1]`), `IsPeriodicHomogeneousDatum s v B` (needs `IsMeanZeroT v` from the hypothesis, and the amended integrability conjunct carried over), and `‖B‖ ≤ ‖A‖`; then
  compare the two infima (`iInf_le`-style). If the spec's `MemPeriodicHomogeneous` hypothesis does not by itself provide an inhomogeneous datum, handle the `⊤` case (`x ≤ ⊤` is trivial).
- `spectralGap : ∀ s, 0 ≤ s → ∀ v, MemPeriodicHomogeneous s v → periodicSobolevENorm s v ≤ ENNReal.ofReal (gapConst s) * periodicHomogeneousENorm s v` with
  `gapConst s := (1 + 1/(4π²))^(s/2)` (for `k ≠ 0`, `|k|² ≥ 1` so `1 + 4π²|k|² ≤ (1 + 1/(4π²))·4π²|k|²`; the `k = 0` mode of a mean-zero field has coefficient `0` — use
  `Section3/T10/DatumBasics.lean`'s zero-mode/mean lemmas if you import that module, or prove the needed one-liner locally): from a homogeneous datum `B` build the inhomogeneous datum `A`
  with `A i k := (periodicFrequencyWeight k ^ (s/2) / homogeneousDatumWeight s k) • B i k` for `k ≠ 0` and `A i 0 := 0`; show membership, reality, `IsPeriodicDatum s v A` (coefficient at
  `k = 0` is `0` because `v` is mean-zero and integrable), and `‖A‖ ≤ gapConst s · ‖B‖`.
Also export the reusable weight comparison lemmas (`homogeneousDatumWeight_le_periodicFrequencyWeight_rpow`, `periodicFrequencyWeight_rpow_le_gap_mul_homogeneous`) and the
`lp` reweighting construction (`reweightDatum`), which later T12/T13 lanes will reuse.

## Deliverables
1. New module `formalization/NSFormalization/Section3/T12/SpectralGap.lean` (namespace `NSFormalization.Section3.T12`); the probe above; conformance `research/T12/axioms_spectral_gap.lean`.
2. Records `research/T12/ATTEMPTS_SPECTRAL_GAP.md` (paths tried, exact error text, any residual named hypothesis with its exact statement); report `research/T12/REPORT_300.md`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T12.SpectralGap` (0 errors), `lake env lean` on the module, the probe and the axioms file, `make check` from the worktree root.

## Report
Commit on your branch (`[300-T12] SpectralGap`); end with four parts (theorems with exact statements and constants / files / gaps with error text / commands and results).
