# Lane 345-T13-torus-identity — T13 the torus Gagliardo identity `torus_identity` of `LocalizationAPI`: `ITorus s f = cFrac s · ‖f‖²_{Ḣ^s(T³)}`

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/345-T13-torus-identity` (git branch `erenup/345-T13-torus-identity`, based on `origin/erenup/integration-section3`: canonical modules
`formalization/NSFormalization/Section3/T10/{PeriodicData,PhysicalBridge,DatumBasics,Parseval,Leray,FourierCalculus}.lean` (FourierCalculus only if lane 305 has landed — check `ls`),
`Section3/T13/Localization.lean` (the T13 vocabulary: `fundamentalCube`, `SupportedInBall`, `latticeVector`, `periodize`, `fractionalRadialKernel`, `cFrac`, `periodicKernel`, `latticeTail`, `IReal`, `ITorus`, `gradientENorm`; read `research/T13/CANONICAL.md`), `Section3/T10/{PeriodicData,FourierCalculus,ForcePaths,Parseval,DatumBasics,PhysicalBridge}.lean`, `Section3/T12/{MeanZeroCalculus,SpectralGap}.lean`, `Section3/T11/{ClassicalRegularity,PairingBound,MildPressure}.lean` (Bernstein bounds, lattice summability, periodic convolution theorem), `Section4/D01/{HomogeneousNorm,HomogeneousWitness}.lean` (the ℝ³ homogeneous norm `dotHomogeneousENorm` and its witnesses), and the target statements `research/T13/probes/api_on_canonical.lean` (`LocalizationAPI : Prop`, six fields; read every field's exact statement and docstring in `research/T13/Spec.lean`, the paper `03-torus.tex:22-98`, and `research/T13/COMPARISON.md` §"Proof dependencies"/"Needs a lemma"), the registered contract `verification/Contracts/V1/TorusData.lean` (`T01.torus_data`), and the proof targets
`research/T13/probes/api_on_canonical.lean`). Read `CLAUDE.md` (hard rules; "结构体例外"), **`research/T13/RECONCILIATION.md` and `research/T13/COMPARISON.md`**,
`research/T11/RECONCILIATION.md` §0–§3, `research/T11/IMPLEMENTATION_CANDIDATES.md`, and the top 40 lines of `logs/LESSONS.md` (**name every instance explicitly**; no anonymous `local instance`).

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. New files only; no edits to existing modules.
- **Satisfiability / peeling rule** (`T11_SPLIT.md` §0): if your unit must assume something not yet proved, name exactly ONE input hypothesis with its exact statement as a `def … : Prop`
  (the split names it where applicable), prove everything else from it, and record it; never weaken a target statement. Target statements are the fields of
  `research/T13/probes/api_on_canonical.lean` (or the bridge lemmas the split states) — copy them verbatim; a probe `research/T13/probes/torus_identity_closes.lean` must show each target closes.
- Before claiming a lemma is "not in the tree", `grep -rn` `formalization/NSFormalization/Paper1/Periodic*.lean`, `Section3/`, `Section4/{A01,A02,A04,D01}`, `vendor/HeliCorgi/Formal/`.
  Every declaration prints exactly `[propext, Classical.choice, Quot.sound]`; include a non-vacuity `example`.

## Goal
Prove the `torus_identity` field of `research/T13/probes/api_on_canonical.lean` verbatim: for `0 < s < 1` and the field's exact hypotheses on `f` (smooth mean-zero periodic, or as stated), the torus difference integral `ITorus s f` (read its definition: `∫_{T³}∫_{T³} |f(x) − f(y)|² K_s^{per}(x − y)` with the periodized kernel, or as spelled in `Section3/T13/Localization.lean`) equals `cFrac s * periodicHomogeneousENorm s f ^ 2`-type (the coefficient-side `Ḣ^s(T³)` norm with weight `|2πk|^{2s}`, zero mode dropped). Route (`03-torus.tex:22-98`, the paper's proof): expand `f(x) − f(y)` in Fourier series (`FourierCalculus.periodic_component_eq_tsum`, absolute convergence from rapid decay), `|f(x) − f(y)|² = |∑ f̂(k) e^{2πik·x}(1 − e^{2πik·(y−x)})|²`, integrate over `x` (orthogonality of characters on the torus: Parseval for fixed `h = y − x`), then integrate over `h` against the periodized kernel: `∫_{T³} |1 − e^{2πik·h}|² K^{per}_s(h) dh = ∫_{ℝ³} |1 − e^{2πik·h}|² K_s(h) dh` (unfolding the periodization: `∑_{n} ∫_{cube} g(h + n) = ∫_{ℝ³} g` for nonnegative `g`, Mathlib `MeasureTheory.integral_tsum`/`lintegral_tsum` + the lattice translation structure — this is the "single-copy" step) `= cFrac s · |2πk|^{2s}` by the scaling of the kernel (`h ↦ h/|2πk|`, rotation invariance — a change of variables in `ℝ³` with `MeasureTheory.Measure.map_smul`/`integral_comp_smul`; for the direction dependence use rotation invariance of Lebesgue measure `Measure.map_linearIsometryEquiv` or reduce to `cFrac` defined as the integral for a fixed unit direction — read how `cFrac` is spelled and match it). Interchanges of sum and integral by `lintegral_tsum` on nonnegative terms / dominated convergence. **No named input**; honest partial with the exact obstacle (e.g. the kernel scaling identity) if stuck. (L+, Opus.)

## Deliverables
1. New module `formalization/NSFormalization/Section3/T13/TorusIdentity.lean` (namespace `NSFormalization.Section3.T13`); the probe; conformance `research/T13/axioms_torus_identity.lean`.
2. Records `research/T13/ATTEMPTS_TORUS_IDENTITY.md` (paths tried, exact error text, any residual named input with its exact statement); report `research/T13/REPORT_345.md`; update your unit's row in
   `research/T13/COMPARISON.md` §1 with a one-line status (append only).

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T13.TorusIdentity` (0 errors), `lake env lean` on the module, the probe and the axioms file, `make check` from the worktree root.

## Report
Commit on your branch (`[345-T11] TorusIdentity`); end with four parts (theorems with exact statements / files / gaps with error text / commands and results).
