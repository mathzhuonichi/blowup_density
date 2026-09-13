# U05 part 2 — reviewer report on the HeliCorgi port (lane 010)

Reviewing `fad2ab1` on `erenup/010-U05-port`, base `erenup/integration`. 2026-09-13. No file was
modified and no git write command was run; this file is the only output.

## Verdict: ACCEPT-WITH-NOTES

Every testable claim in `research/U05/PORT.md` reproduced, several to the second. The §7 notes are a
disclosed merge-time decision and one incomplete parenthetical — not defects.

## 1. Changed files

`git diff --stat erenup/integration..HEAD` lists 13 paths, but 5 are base drift: the lane branched
at `9ca0480` and integration advanced since. The lane's true change (`9ca0480..HEAD`) is **8 files**
— `M collaboration/tasks/U05.md`; `M formalization/lakefile.toml` (+112); `A
formalization/FormalPatched/{R3RealLocalMildSolution (131), R3QuantitativeLifespan (245),
EndpointSafeTwoSpaceUniqueness (255), R3MildContinuation (167)}.lean`; `A
.../NSFormalization/Section4/HeliCorgiPort.lean` (49); `A research/U05/PORT.md` (669). The 5 drift
entries (`PLAN.md`, `logs/AGENT_RUNS.csv`, `research/D01/{COMPARISON_B.md,DraftB.lean,REVIEW_B.md}`)
are integration-side additions the lane never touched; a 3-way merge will not revert them, and `git
merge-tree --write-tree erenup/integration HEAD` exits 0 — **the merge is conflict-free**. Nothing
under `vendor/`, `verification/`, `lake-manifest.json`, `paper/` or `formalization/blueprint/`; `git
status --porcelain -- vendor/` empty before and after the build; no `sorry`/`admit`/`axiom`/
`native_decide`/`unsafe` in any new file.

## 2. Patch minimality — confirmed

`diff -u vendor/HeliCorgi/Formal/X.lean formalization/FormalPatched/X.lean` yields exactly three
kinds of change and nothing else. Each of the four gets a 9-line provenance header. Import
redirects: 0 in `R3RealLocalMildSolution` (both imports correctly stay `Formal.*`), 1 in
`R3QuantitativeLifespan`, 1 in `EndpointSafeTwoSpaceUniqueness`, 2 in `R3MildContinuation` — every
redirect targets one of the four ported modules only; `EndpointSafeTwoSpacePicard`, `…Restart`,
`…Concatenation`, `R3ConvectionConjugationEquivariance` stay on `Formal.*`. Lean-content change:
**the single `hconj` hunk** in `R3RealLocalMildSolution` (+9 `have`, `rw` +1/−2), nothing else in
any file. That hunk is semantics-preserving — `(r3L2Conj_r3StokesH3Evolution hnu.le ⟨t,ht.1⟩
u0).trans (congrArg _ hu0')` is the term-mode composition of the same two rewrites upstream's `rw
[r3L2Conj_r3StokesH3Evolution, hu0', …]` performed; no new lemma is invoked.

**Namespaces and declaration names unchanged.** Extracting every `namespace`/`end` line and every
`theorem`/`lemma`/`def`/`abbrev`/`structure`/`instance`/`class`/`axiom`/`opaque` signature from each
pair and diffing the lists: **identical in all four** (9, 9, 13, 5 entries), all in `namespace
MNS2`. **PORT.md fidelity:** all five ```diff fences in `research/U05/PORT.md` were extracted and
compared programmatically against the real `git diff` / `diff -u` output — **all five match
exactly** (modulo `---`/`+++`/`index` headers); its §3.5, §4, §4.1, §4.2 and §4.4 prose matches
what I measured.

## 3. Roots and closure — confirmed independently

`Formal` has **84** roots and `srcDir = "../vendor/HeliCorgi"`; `FormalPatched` has **4**; no
duplicates; **none of the four patched names appears in the `Formal` roots**. Recomputing the
closure from vendor sources rather than trusting `REPORT.md` — DFS from the four targets over
`Formal.*` imports — gives **88** modules, no missing files; `88 − 4 = 84` and that set is
**exactly** the lakefile's roots (0 in one and not the other). No module among the 84 imports a
patched module, so `Formal` is import-closed. Matches REPORT.md §(b).

## 4. Cold CI-path build — reproduced

After `rm -rf formalization/.lake/build`, the unmodified CI script. Dry run listed exactly the five
required modules. Real run:

```
python3 experiments/build_changed_lean.py --base-ref erenup/integration
EXIT=0   8851 jobs   wall 2:08.48   308 % CPU   user 329.5 s   max RSS 6.98 GB
```

PORT.md row 8 claims 2 m 07.4 s / 306 % / 6.99 GB — reproduced within noise. oleans: `Formal/`
**84**, `FormalPatched/` **4** (the expected names), `NSFormalization/` 1. **0 errors.** **52
warning lines, 100 % from `../vendor/HeliCorgi/Formal/*.lean`** across 20 modules; **zero** from
`FormalPatched/` or `NSFormalization/`. Mathlib at `85e3a25e006c35636f0e53b0e9296caca2685bc0`,
`status --porcelain` = 0, before and after. PORT.md risk 3 verified live: `lake build
Formal.R3RealLocalMildSolution` → `error: unknown target` — that failure mode is loud, not silent.

## 5. Axioms — all standard

`lake env lean` on a scratch file (since deleted) under `verification/`. The four required
declarations each report **exactly `[propext, Classical.choice, Quot.sound]`**:

```
MNS2.r3EndpointSafeProjected_blowup_dichotomy          [propext, Classical.choice, Quot.sound]
MNS2.r3EndpointSafeProjectedMild_navierStokes          [propext, Classical.choice, Quot.sound]
MNS2.r3EndpointSafeProjected_exists_localMildSolution  [propext, Classical.choice, Quot.sound]
MNS2.r3HelmholtzPressure_gradient                      [propext, Classical.choice, Quot.sound]
```

The other five declarations in PORT.md §4.1's table give the same three axioms, no `sorryAx`; §4.1
is accurate.

## 6. Repository checks

`make check` **exit 0** (4 sub-checks; work queue consistent) · `make test` **exit 0**
(`Tests.Thresholds` replayed, standard axioms only) · `make test-mutations` **exit 0** (refactor
accepted; admission, extra axiom and weakened hypothesis all rejected) · `check_contracts.py
--base-ref erenup/integration` **exit 0** with `base_compatibility_checked: true`.

`make snapshot` **exit 2**, failing with exactly `AssertionError: ['formalization/lakefile.toml']` —
a one-element list, the lakefile and nothing else. Per `CONTRIBUTING.md` this check "is deliberately
not a normal proof-PR requirement", so it is not a defect. The `sorry` at
`NSFormalization/Paper1/BoundaryCorollary.lean:90` that `make check` reports is pre-existing on
`erenup/integration`.

## 7. Notes (non-blocking)

1. **Snapshot manifest.** `formalization/lakefile.toml` is in
   `logs/FORMALIZATION_SOURCE_MANIFEST.json`, so `make snapshot` keeps failing until someone
   re-snapshots. The lane disclosed this (PORT.md §5.1) and left it out of scope; the merger should
   decide.
2. **PORT.md §4.3 parenthetical is incomplete** — the `9ca0480`→integration difference also adds the
   three `research/D01/` files. Harmless: `targets()` ignores `research/`, so `DraftB.lean` is
   correctly not compiled. §4.3's `Changed Lean modules: none` held only pre-commit; post-commit the
   script emits the five expected modules, as §4.3 predicted.
3. **`warningAsError` (PORT.md risk 2) stands.** Neither new library sets `leanOptions`;
   `verification`'s `Tests` lib sets `warningAsError = true`. Any future binding or contract
   importing `Formal.*` from `Tests` turns the 52 vendored warnings into errors — worth a comment in
   the `Tests` lib, not only in the lakefile.
4. **Duplicate names on re-vendoring (PORT.md risk 3) stands**, well mitigated: the two `roots`
   lists are adjacent and commented, and the failure is a hard `unknown target`. Re-vendoring must
   move the four names back and delete `FormalPatched/` in one commit.
5. **Integration moved during this review** (`33ecb40`→`cf8d04a`, bookkeeping only); no
   `formalization/` or `vendor/` change on that side since the merge-base, so §1's clean-merge
   result still holds.
