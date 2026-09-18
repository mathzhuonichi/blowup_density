# Lane 362-T15-U1-bridges — T15 U1: the rescaling definitions of `prop:scaling` as a canonical module + `rfl` bridges to the registered `I03.scaling` spellings (and lane 352's `periodize` bridge)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/362-T15-U1-bridges` (git branch `erenup/362-T15-U1-bridges`, based on `origin/erenup/integration-section3`).
Read `CLAUDE.md`, **`research/T15/T15_SPLIT.md` §0 and unit U1**, `research/T15/Spec.lean` (the reconciled statement; the rescaling definitions and its `example … := rfl`
drift checks at `:411-419,453-467,493-496,551-552`), `research/T15/RECONCILIATION.md` §3, the registered `verification/Contracts/V1/Scaling.lean` (`scaledPacket :107`,
`scaledPressure`, `scaledForce :115`, `alpha`), `verification/Bindings/Scaling.lean`, `Section3/T13/Localization.lean:42` (`periodize`), `Section3/T16/LatticeLift.lean`
(`latticeLift_eq_periodize`, lane 352: `latticeLift w = NavierStokes.PeriodicLocalization.periodize w` by `rfl`), and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only.
- **No placeholders, no aliases, no named inputs, no goal repackaging.** A `def X : Prop := <goal>` or a hypothesis equal to the target is a stub and will be discarded without review;
  an honest partial with the exact residual statement and error text is fine.
- Before claiming a lemma is "not in the tree", `grep -rn` `Section3/T10`, `Section3/T13`, `Section4/I03`, `verification/Contracts/V1/Scaling.lean`, `verification/Bindings/Scaling.lean`.
  Every declaration must print exactly `[propext, Classical.choice, Quot.sound]`.

## Goal
Create the T15 canonical module `formalization/NSFormalization/Section3/T15/Bridges.lean` (namespace `NSFormalization.Section3.T15`): restate, over the canonical T10 vocabulary
(`Section3/T10/PeriodicData.lean` etc. — import, never copy T10), the T15 rescaling definitions of `research/T15/Spec.lean` that the `rfl` examples concern (`scaledVelocity`,
`scaledPressure`, `scaledForce`, `alphaT`, `normalizedScaledPressure`, `periodicScaledPacket`/`periodicScaledPressure`/`periodicScaledForce` if they are defined there — copy the
Spec's definitions verbatim, only the namespace changes), and promote every `example … := rfl` of the Spec to a `theorem` against the registered spellings:
`scaledVelocity = Contracts.V1.scaledPacket`-shaped statements are impossible in `formalization/` (it cannot import `Contracts.*`), so state the bridges against the
**upstream** objects the contract binds to (`Bindings/Scaling.lean` tells you which `NSFormalization.Section4.I03.…` / `NavierStokes.…` declarations `Contracts.V1.scaledPacket`
etc. are `rfl`-bound to; bridge to those), plus the lane-352 bridge `theorem periodize_eq_vendor : (T13.periodize f) = fun x => NavierStokes.PeriodicLocalization.periodize (fun z => f z.2) (t, x)`-shaped
(find the exact shape that is `rfl`; if it is not `rfl` for the T13 `periodize` of a *spatial* field, prove the pointwise equality). Then a probe
`research/T15/probes/api_on_canonical.lean` restating the Spec's definitions token-for-token and proving each equals the module's by `rfl`, plus the contract-side bridges
`Contracts.V1.scaledPacket = <module>` etc. (probes may import `Contracts.*`/`Bindings.*`).

## Deliverables
1. `Section3/T15/Bridges.lean`; 2. `research/T15/probes/api_on_canonical.lean`; 3. `research/T15/ATTEMPTS_U1.md`, `research/T15/axioms_u1.lean`, status in `research/T15/T15_SPLIT.md` U1 and
`research/T15/COMPARISON.md`, report `research/T15/REPORT_362.md`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T15.Bridges` (0 errors), `lake env lean` on module / probe / axioms file; `make check`.

## Report
Commit on your branch; end with four parts (theorems with exact statements / files / gaps / commands and results). Also write it to `research/T15/REPORT_362.md`.
