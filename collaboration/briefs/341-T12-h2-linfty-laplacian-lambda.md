# Lane 341-T12-h2-linfty-laplacian-lambda — T12 the Fourier-side fields `boundedRepresentative` (H² ↪ L^∞), `hTwo_le_laplacian`, `lambda_exists` of `MeanZeroSobolevCalculusAPI`

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/341-T12-h2-linfty-laplacian-lambda` (git branch `erenup/341-T12-h2-linfty-laplacian-lambda`, based on `origin/erenup/integration-section3`: canonical modules
`formalization/NSFormalization/Section3/T10/{PeriodicData,PhysicalBridge,DatumBasics,Parseval,Leray,FourierCalculus}.lean` (FourierCalculus only if lane 305 has landed — check `ls`),
`Section3/T12/{MeanZeroCalculus,SpectralGap}.lean` (the T12 vocabulary and the proved spectral-gap fields), `Section3/T10/{PeriodicData,FourierCalculus,ForcePaths,Parseval,DatumBasics}.lean`, `Section3/T11/{ClassicalRegularity,PairingBound,ConvolutionBoundReal,MildPressure,MildMomentum,EnergyIdentity}.lean` (lane 339's Bernstein bound `W(k)^N‖ĝ(k)‖ ≤ 2^N(sup|g| + sup|Δ^N g|)` and slab machinery; lane 336's `torusInverseWeight_summable` (`∑ W^{-r} < ∞` for real `r > 3/2`), `torusWeightPeetre`, trilinear convolution; the periodic convolution theorem `periodicFourierCoeff_mul`), and the target statements `research/T12/probes/api_on_canonical.lean` (the Type-valued `MeanZeroSobolevCalculusAPI`: constants as data fields; read every field's exact statement and docstring in `research/T12/Spec.lean`), the registered contract `verification/Contracts/V1/TorusData.lean` (`T01.torus_data`), and the proof targets
`research/T12/probes/api_on_canonical.lean`). Read `CLAUDE.md` (hard rules; "结构体例外"), **`research/T12/RECONCILIATION.md` §0–§3 and `research/T12/COMPARISON.md` §"Proof dependencies"**,
`research/T11/RECONCILIATION.md` §0–§3, `research/T11/IMPLEMENTATION_CANDIDATES.md`, and the top 40 lines of `logs/LESSONS.md` (**name every instance explicitly**; no anonymous `local instance`).

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. New files only; no edits to existing modules.
- **Satisfiability / peeling rule** (`T11_SPLIT.md` §0): if your unit must assume something not yet proved, name exactly ONE input hypothesis with its exact statement as a `def … : Prop`
  (the split names it where applicable), prove everything else from it, and record it; never weaken a target statement. Target statements are the fields of
  `research/T12/probes/api_on_canonical.lean` (or the bridge lemmas the split states) — copy them verbatim; a probe `research/T12/probes/fourier_embeddings_closes.lean` must show each target closes.
- Before claiming a lemma is "not in the tree", `grep -rn` `formalization/NSFormalization/Paper1/Periodic*.lean`, `Section3/`, `Section4/{A01,A02,A04,D01}`, `vendor/HeliCorgi/Formal/`.
  Every declaration prints exactly `[propext, Classical.choice, Quot.sound]`; include a non-vacuity `example`.

## Goal
Prove three fields of `research/T12/probes/api_on_canonical.lean` verbatim (with explicit constants substituted for the API's data fields `Cinfty`, `CHtwo`; a probe shows each `example` closes the field with your constant):
(1) `boundedRepresentative`: for `v` with an order-2 datum (`MemPeriodicHmVector 2 v` / the field's exact hypothesis), `periodicLpENorm ⊤ v ≤ ENNReal.ofReal Cinfty * periodicSobolevENorm 2 v` — route: the essential sup is bounded by `∑' ‖v̂(k)‖ ≤ (∑' W(k)^{-2})^{1/2} (∑' W(k)^2 ‖v̂(k)‖²)^{1/2}` (Cauchy–Schwarz; `torusInverseWeight_summable` at `r = 2`; `FourierCalculus.norm_component_le_tsum_norm_periodicFourierCoeff` / `periodic_component_eq_tsum` for the pointwise inversion of a field with summable coefficients — if the hypothesis is only `H²` membership (not smooth), use the `L²`-Fourier inversion a.e.: `Parseval.lean`'s Hilbert-basis representation + absolute convergence ⇒ the continuous representative equals `v` a.e., so the ess-sup of `v` is bounded); `Cinfty = (∑' W^{-2})^{1/2}` explicit.
(2) `hTwo_le_laplacian`: `SmoothPeriodicT v → IsMeanZeroT v → periodicSobolevENorm 2 v ≤ ENNReal.ofReal CHtwo * periodicLpENorm 2 (laplacian v)` — coefficientwise: `W(k)^2 ≤ CHtwo² (4π²|k|²)²` for `k ≠ 0` (`CHtwo = 1 + 1/(4π²)`), the zero mode vanishes by mean zero, `‖Δv‖_{L²}² = ∑ (4π²|k|²)² ‖v̂(k)‖²` by `FourierCalculus.periodicFourierCoeff_laplacian` + Parseval (`ForcePaths.gradientTensor_parseval` shows the pattern).
(3) `lambda_exists`: `SmoothPeriodicT v → ∃ Lv, IsPeriodicLambda v Lv` — construct `Lv` by the multiplier `|2πk|` on the coefficients and invert (`FourierCalculus` summability/decay of smooth coefficients ⇒ the multiplied series converges absolutely with all derivatives ⇒ `Lv` smooth periodic; 339's Bernstein bound gives the decay uniformly), and prove `IsPeriodicLambda v Lv` (read the predicate in `Section3/T12/MeanZeroCalculus.lean`: coefficient identity + regularity).
**No named input**; honest partial with the exact obstacle if stuck. (L, Opus.)

## Deliverables
1. New module `formalization/NSFormalization/Section3/T12/FourierEmbeddings.lean` (namespace `NSFormalization.Section3.T12`); the probe; conformance `research/T12/axioms_fourier_embeddings.lean`.
2. Records `research/T12/ATTEMPTS_FOURIER_EMBEDDINGS.md` (paths tried, exact error text, any residual named input with its exact statement); report `research/T12/REPORT_341.md`; update your unit's row in
   `research/T12/COMPARISON.md` §1 with a one-line status (append only).

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T12.FourierEmbeddings` (0 errors), `lake env lean` on the module, the probe and the axioms file, `make check` from the worktree root.

## Report
Commit on your branch (`[341-T12] FourierEmbeddings`); end with four parts (theorems with exact statements / files / gaps with error text / commands and results).
