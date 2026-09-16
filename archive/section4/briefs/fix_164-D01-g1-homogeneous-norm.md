# Fix for lane 164-D01-g1-homogeneous-norm — put the definition in a NEW V1 contract file (no shim)

Worktree: `/data_8T/ping/blowup_density/.claude/worktrees/164-D01-g1-homogeneous-norm` (branch
`erenup/164-D01-g1-homogeneous-norm`, your previous commit `0c7b2b0`). Work only here; never `git push`,
merge or rebase; committing on this branch is allowed. Lean: `. scripts/lean-env.sh`; `lake` only from
`verification/` with `LEAN_NUM_THREADS=6`.

Your registration used a declaration-free `verification/Contracts/V1/HomogeneousNorm.lean` shim that
imports the real definition from `Contracts/V2/HomogeneousNorm.lean`. That misreads the freeze rule:
`CLAUDE.md` freezes **existing** `Contracts/V1/*` files; **creating a new V1 file is allowed and is the
normal way to register version 1 of a new component** (see `verification/Contracts/V1/GradientL6.lean`,
registered by lane 019). The registry's `specification` must be the file that actually states the
mathematics.

Do exactly this:
1. Move the contents of `verification/Contracts/V2/HomogeneousNorm.lean` (the verbatim restatement of
   `dotHomogeneousENorm`, `IsHomogeneousSliceDatum` if restated there, and any helper defs) into
   `verification/Contracts/V1/HomogeneousNorm.lean`, replacing the shim; keep the import policy
   (only `Mathlib`/`Lean`/`Init`/`Contracts.*` + the whitelist in `experiments/check_contracts.py`).
2. Delete `verification/Contracts/V2/HomogeneousNorm.lean` (`git rm`).
3. Update `verification/Bindings/HomogeneousNorm.lean` and `verification/Tests/HomogeneousNorm.lean`
   to import `Contracts.V1.HomogeneousNorm`; the `rfl` bridge and `checkedHomogeneousNorm` stay.
4. `verification/contracts.json`: the entry `D01.homogeneous_norm` keeps `version: 1` and
   `specification: verification/Contracts/V1/HomogeneousNorm.lean` (already so); fix the scope text if
   it mentions the shim. Keep `ensure_ascii=False`.
5. Update `research/D01/ATTEMPTS_G1.md` and `research/D01/REPORT_164.md` to describe the final layout
   (remove the shim explanation).
6. Rerun and paste: `cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.D01.HomogeneousNorm`
   (silent), `lake env lean ../research/D01/axioms_g1.lean` (9 declarations, standard 3 axioms),
   `scripts/gates.sh NSFormalization.Section4.D01.HomogeneousNorm` from the worktree root
   (`== gates OK`), `python3 experiments/check_contracts.py --base-ref origin/erenup/integration`
   (`registered_contracts: 27`, `base_compatibility_checked: true`), `git diff --stat verification/contracts.json`.
7. Commit on the branch. End with a short report: files now, gate outputs, and confirmation that no
   pre-existing `Contracts/V1/*` or `Tests/*` file was modified (`git diff --name-only origin/erenup/integration...HEAD`).
