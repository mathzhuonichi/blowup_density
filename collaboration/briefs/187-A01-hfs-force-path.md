# Lane 187-A01-hfs-force-path — A01 B1 supply: the cylinder force path is `C^∞` in time (discharge `hfs`)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/187-A01-hfs-force-path` (git branch `erenup/187-A01-hfs-force-path`,
based on `origin/erenup/integration`). Read `CLAUDE.md`, `collaboration/HANDOFF.md` §0 and §2 P8,
`research/A01/B1_LADDER.md` §R3/R4, `Section4/D01/ForceClass.lean:141-166` (`MemForceR`: for every order `m` a datum path
`G : ℝ → RealVectorSobolev m` with `IsSobolevPath m f G`, `ContDiffOn ℝ ∞ G futureTimes`), `Section4/C01/JetPaths.lean:86-110`
(`forcePath hf : Icc 0 S → SmoothL2Field Space` and `forcePath_jetLp_continuous`, whose proof identifies
`(forcePath hf t).jetLp n = D01.jetOfDatum n n (le_refl n) (G t.1)` and composes with `jetOfDatum_continuous`),
`Section4/A01/ForceBridge.lean:60-70` (`forcePath_of_memForceR`, continuity only), `Section4/A01/Horizon.lean:106-153`
(where `sobolevPath F hF q` enters the Duhamel equation), the vendor definitions
`vendor/NavierStokesAndEuler/Euler/SmoothFieldSobolevTime.lean:40` (`sobolevPath (A : K → SmoothL2Field Space) …`) and
`vendor/NavierStokesAndEuler/Euler/VolterraConvolution.lean:20` (`extendPath`), and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`,
  commented. No edits to existing modules; new files only.
- Before claiming a lemma is "not in the tree", `grep -rn` all of `Section4/{A01,C01,D01}`, `Source/`, and the vendor
  `Euler/` directory. Every declaration must print exactly `[propext, Classical.choice, Quot.sound]`; include a
  non-vacuity `example` (`f := 0`, which is in `MemForceR` — check for the tree's zero-force lemma, e.g. in `A04`/`C01`).

## Goal (the consumer's exact hypothesis)
Lane 178 (`Section4/A01/DatumPathSmooth.lean` on branch `erenup/178-A01-b1-ladder-r3`, review confirmed the gap is
genuine) and lane 186 both take as input
```lean
hfs : ∀ q (hq : 6 ≤ q), ContDiffOn ℝ ∞ (extendPath S hS.le (sobolevPath F hF q)) (Icc (0:ℝ) S)
```
for the canonical force carrier `F := C01.forcePath hf` with `hF := C01.forcePath_jetLp_continuous hf`
(`hf : D01.MemForceR f`). Prove it: `theorem forcePath_sobolevPath_contDiffOn (hf : D01.MemForceR f) (hS : 0 < S) (q : ℕ) :
ContDiffOn ℝ ∞ (extendPath S hS.le (sobolevPath (C01.forcePath hf) (C01.forcePath_jetLp_continuous hf) q)) (Icc (0:ℝ) S)`
(state it for all `q`, `6 ≤ q` not needed if the proof doesn't use it). Route: unfold `sobolevPath` — it reconstructs the
cylinder element from the jets `(A t).jetLp n` (or from the field directly) through a fixed continuous-linear
reconstruction; identify `(forcePath hf t).jetLp n` with `jetOfDatum … (G t)` as in `forcePath_jetLp_continuous`, so the
cylinder path is `(continuous linear map) ∘ G` restricted to `Icc 0 S`; `ContDiffOn` of `G` on `futureTimes ⊇ Icc 0 S`
composed with a bounded linear map gives the claim (`ContinuousLinearMap.contDiff.comp_contDiffOn`). Handle `extendPath`
(`projIcc`) on `Icc 0 S` where it is the identity (`ContDiffOn.congr`). If `sobolevPath`'s reconstruction is not
manifestly linear in the jets, prove the needed linearity/continuity lemma for it as a separate theorem (vendor file
untouched — new lemmas only in your module).

## Deliverables
1. New module `formalization/NSFormalization/Section4/A01/ForcePathSmooth.lean` (namespace `NSFormalization.Section4.A01`):
   the reconstruction lemma(s), `forcePath_sobolevPath_contDiffOn`, and the packaged
   `theorem forcePath_of_memForceR_smooth : ∃ F, F = C01.forcePath hf ∧ (∀ n, Continuous fun t => (F t).jetLp n) ∧ A04.MemL1Hm f ∧ ∀ q (hq : 6 ≤ q), ContDiffOn ℝ ∞ (extendPath S hS.le (sobolevPath F (…) q)) (Icc 0 S)`
   (the lane-167 package extended by the `hfs` clause; keep the first three clauses token-identical to `ForceBridge.forcePath_of_memForceR`).
2. Records `research/A01/ATTEMPTS_HFS.md`; update `research/A01/B1_LADDER.md` (R3/R4 inputs: `hfs` discharged);
   conformance `research/A01/axioms_hfs.lean`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.A01.ForcePathSmooth` (silent), `lake env lean`
on the module (0 output), the axioms file, `make check` from the worktree root.

## Report
Commit on your branch; end with four parts (theorems with exact statements / files / gaps with error text / commands).
Also write it to `research/A01/REPORT_187.md`.
