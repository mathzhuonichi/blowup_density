# Rework for lane 167-A01-force-bridge — reorient row (v) per the review (REJECT)

Worktree: `/data_8T/ping/blowup_density/.claude/worktrees/167-A01-force-bridge` (branch
`erenup/167-A01-force-bridge`, your commit `989e9ab`). Work only here; never `git push`, merge or rebase;
committing on this branch is allowed. Lean: `. scripts/lean-env.sh`; `lake` only from `verification/`
with `LEAN_NUM_THREADS=6`. Rules as before (no `sorry`/`admit`/`axiom`/`native_decide`; new files or
this lane's own files only; standard three axioms for every declaration).

Read `research/A01/REVIEW_167-A01-force-bridge.md` in full (verdict REJECT) and its probe
`research/A01/probes/rev167_endpoint.lean`: it proves
`¬ ForcePathSmoothness (C01.forcePath hf)` for a concrete nonzero `f ∈ F_R` (the zero extension is not
smooth at `t = S`), so the carrier-to-physical direction `F ↦ f'` is the wrong direction for the
constructor. The consumer direction is: the paper's global force `f` with `hf : MemForceR f` is given;
the cylinder path is `F := C01.forcePath hf` (`Section4/C01/JetPaths.lean`, jet-continuous by
`forcePath_jetLp_continuous`); the constructor keeps `f' := f`. The probe shows this direction
compiles without `ForcePathSmoothness` (`rev167_endpoint.lean:95-102`).

Apply exactly the review's four fixes:
1. **Reorient row (v)**: rewrite `formalization/NSFormalization/Section4/A01/ForceBridge.lean` so its
   public theorems are the consumer direction — e.g. `forcePath_of_memForceR` packaging
   `(C01.forcePath hf, forcePath_jetLp_continuous hf)` as the `(F, hF)` pair that `HasAprioriBound` /
   `localTheory_on_prescribed_horizon` take, plus the identity `forceOfPath (C01.forcePath hf) = f` on
   `Icc 0 S` (a.e. or pointwise, whichever holds) if `forceOfPath` is kept; keep
   `initialClassR_of_smoothL2` (with fix 4). Delete `ForcePathSmoothness` and the theorems that only
   hold under it, or keep them clearly marked as the *flat subclass* (docstring) — do not export a
   theorem whose hypothesis is unsatisfiable in general.
2. Remove the dead `hF` premise wherever the review shows it is logically unused, or make it load-bearing.
3. Correct `research/A01/REPORT_167.md`, `ATTEMPTS_FORCE_BRIDGE.md`, and the lane-167 note in
   `research/A01/A3_SPLIT.md`: the endpoint-smoothness claim and the direction of row (v).
4. `initialClassR_of_smoothL2`: state the divergence input as the external bridge from lane 162
   (`Section4/A01/ConstructorDivergence.lean`, now on `origin/erenup/integration`; you may `git fetch`
   and read it in the root's `formalization/…` only via `git show origin/erenup/integration:…` —
   do not check it out into this worktree unless you `git merge origin/erenup/integration` on your
   branch, which is allowed) with its required hypotheses, instead of a bare pointwise divergence.

Then update `research/A01/axioms_force_bridge.lean` (all declarations, non-vacuity), rerun
`lake build NSFormalization.Section4.A01.ForceBridge` (silent), `lake env lean` on the module (0 output),
the axioms file, `make check`; commit; end with the four-part report (exact final statements).
Also overwrite `research/A01/REPORT_167.md` with the corrected report.
