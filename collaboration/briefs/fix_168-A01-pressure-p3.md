# Fix for lane 168-A01-pressure-p3 — apply the three review notes

Worktree: `/data_8T/ping/blowup_density/.claude/worktrees/168-A01-pressure-p3` (branch
`erenup/168-A01-pressure-p3`, your commit `b8f644f`). Work only here; never `git push`, merge or rebase;
committing on this branch is allowed. Lean: `. scripts/lean-env.sh`; `lake` only from `verification/`
with `LEAN_NUM_THREADS=6`. Rules as before (no `sorry`/`admit`/`axiom`/`native_decide`; standard three
axioms for every declaration; this lane's own files only).

Read `research/A01/REVIEW_168-A01-pressure-p3.md` (ACCEPT-WITH-NOTES) and the probe
`research/A01/probes/rev168_projected_redundant.lean`. Apply exactly:
- **N1**: in `formalization/NSFormalization/Section4/A01/ConstructorPressure.lean`, remove the redundant
  pointwise `hprojected` binder of `momentum_of_projected` (the probe shows it is implied by the other
  hypotheses) and correct the docstring's description of the projected equation accordingly. Do not weaken
  any other statement.
- **N2**: in the docstring of `pressure_smooth_of_velocity_smooth` (and in `REPORT_168.md` /
  `ATTEMPTS_PRESSURE_P3.md`), describe `hjoint` as an *additional* global, endpoint-compatible regularity
  hypothesis on `G`, not as implied by c3 plus `MemForceR`.
- **N3**: add to `ATTEMPTS_PRESSURE_P3.md` and the lane-168 note in `research/A01/A3_SPLIT.md` that
  `ConstructorPressure` must join the next registered A01 contract closure (it is in no contract closure now,
  so `make test` does not compile it).
Then rerun `lake build NSFormalization.Section4.A01.ConstructorPressure` (silent), `lake env lean` on the
module (0 output), `lake env lean ../research/A01/axioms_pressure_p3.lean` (all standard; update it if the
signature changed), `make check`; commit; end with a short report (final statement of
`momentum_of_projected`, gate outputs). Overwrite `research/A01/REPORT_168.md` accordingly.
