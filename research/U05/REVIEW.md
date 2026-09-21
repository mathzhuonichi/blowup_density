# U05 review — lane 004 reviewer report

2026-09-13. Reviewed: `research/U05/REPORT.md` + `build.log`, `build-after-fix.log`, `probe/`.
No git write command; `vendor/`, `formalization/`, `verification/` untouched; the only file
written is this one (scratch dir deleted).

## Verdict: **ACCEPT-WITH-NOTES**
Every measurable claim reproduced exactly. One quotation in section (c) is misattributed (§6);
the diagnosis it supports is corroborated by the real logs. The headline recommendation was
tested and **works as written**.

## 1. Reproduction (report vs. review)
I ran `make_probe.sh`, then **wiped `.lake/build`** and rebuilt cold — the worker's `build.log`
is warm (8 of 88 modules cached from an earlier smoke run: only 71 `Built` + 5 `Replayed` lines),
so "84 built" is not readable off it directly. Cold log `/tmp/u05-review-clean.log`.

| quantity | REPORT | review | ok |
|---|---:|---:|:-:|
| exit code / distinct source errors | 1 / 1 | 1 / 1 | ✔ |
| error location | `R3RealLocalMildSolution.lean:76:16` | same | ✔ |
| error block vs `build.log` (40 lines) | — | **byte-identical**, `diff` silent | ✔ |
| `.olean`s after build / cold `Built Formal.*` | 84 | 84 / 84 | ✔ |
| closure of the 4 targets | 88 | 88 | ✔ |
| targets built | 3 (`…LocalExistence`, `…HelmholtzPressure`, `…NavierStokesEquation`) | same | ✔ |
| target not built | `R3MildContinuation` | same, plus `R3QuantitativeLifespan`, `EndpointSafeTwoSpaceUniqueness` (no olean) | ✔ |
| warnings / modules warning | 52 / 20 | 52 / 20 | ✔ |
| wall time | 1 m 53.4 s (warm) | 2 m 06.4 s cold, 303 % CPU, 6.98 GB RSS | ✔ |
| `sorry` in `probe/Formal/` | 0 | 0 | ✔ |
| `diff -rq vendor/HeliCorgi/Formal probe/Formal` | silent | silent | ✔ |

Line 76 is `rw [r3L2Conj_r3StokesH3Evolution, hu0', ← …]`; the logged pattern
`r3L2Conj ((r3StokesH3Evolution ?hnu ?t) ?g)` (`?t : ℝ≥0`) vs target `r3StokesH3Evolution ⋯ ⟨t, ⋯⟩`
is as described. `build-after-fix.log` does contain the two claimed follow-on errors
(`EndpointSafeTwoSpacePicard.lean:832:12`, `R3ProjectedMomentumDuhamelInfrastructure.lean:779:8`).

## 2. Closure size — verified independently
Own Python pass over `import Formal.…` lines: **closure 88**, 128 `.lean` files, 40 outside,
**14 223** closure lines / **21 524** total — all four exact. External imports inside the closure:
**28 distinct**, `Mathlib` 13×, `…Function.L2Space` 4×, `…Fourier.LpSpace` 3×, `…Function.Holder`
3×, `…JapaneseBracket` 3×, 23 used once or twice — the report's table verbatim, nothing
non-Mathlib. The "42 anonymous-constructor lines in 10 files" grep reproduces per file too
(16/12/5/2/2/1/1/1/1/1).

## 3. Mathlib gap — verified, 826
HeliCorgi's `lake-manifest.json` pins mathlib `520045ab14e26149ee970e2e617ca04b09bde5d6`
(`inputRev v4.32.1`, *chore: bump toolchain to v4.32.1*, 2026-07-23), toolchain `v4.32.1`.
`git -C <shared>/mathlib log --oneline 520045ab…..85e3a25e… | wc -l` → **826**. Matches.

## 4. Feasibility of the `srcDir` recommendation — **CONFIRMED**
Tested in `research/U05/review-scratch/` (deleted) with throwaway packages built like the probe
(toolchain `v4.34.0-rc2`, mathlib pinned to `85e3a25e…`, `.lake/packages` symlinked to the shared
tree, borrowed manifest, dead-proxy interlock).

* **pkgA**, `srcDir = "../src"` (outside the package root): `lake build Formal.R3SobolevCarrier`
  → **exit 0**, 8775 jobs. Lake accepts an out-of-package `srcDir`; diagnostics carry the
  `../src/Formal/…` prefix, `.olean`s land in the package's own `.lake/build`. **No symlink
  workaround needed** (the pkgB symlink variant was prepared but never required).
* **pkgC**, the recommendation in its exact shape — srcDir straight at the vendored tree plus an
  explicit list of the 84 good modules: **exit 0, 0 errors, 84 `.olean`s, 8847 jobs, 124 s.**

```toml
name = "HeliCorgiInPlace"
defaultTargets = ["Formal"]
[[require]]
name = "mathlib"
scope = "leanprover-community"
git = "https://github.com/leanprover-community/mathlib4.git"
rev = "85e3a25e006c35636f0e53b0e9296caca2685bc0"
[[lean_lib]]
name = "Formal"
srcDir = "../../../../vendor/HeliCorgi"   # from formalization/ this is "../vendor/HeliCorgi"
roots = ["Formal.EndpointSafeTwoSpaceConcatenation", …, "Formal.R3NavierStokesEquation"]  # 84
```

For the implementer:
1. Use **`roots = [...]`**, not `globs = ["Formal.+"]` — a glob sweeps in all 128 modules,
   including the 4 broken ones.
2. `srcDir` resolves **relative to the package directory**. One `../` short fails with
   `error: Formal: some modules have bad imports or could not be read` plus one
   `error: no such file or directory (error code: 2)` per module.
3. Both report caveats hold: `vendor/HeliCorgi/lakefile.lean` sits inside the `srcDir` and was
   **not** read (a `srcDir` creates no path dependency); `formalization/` carries no
   `warningAsError` (`verification`'s `Tests` and `NavierStokesAndEuler`'s `Euler` do).
4. No collision: existing libs are `NSFormalization`, `NavierStokes`, `Euler`,
   `ComparatorChallenges`, `Contracts`, `Bindings`, `TestSupport`, `Tests`; no `Formal/` root.

## 5. "A 4.32.1 bridge would need axioms" — correct
`.olean` files carry a toolchain-specific header and 4.34.0-rc2 will not import oleans built by
4.32.1; there is no cross-toolchain linking. Independently, the two trees sit 826 Mathlib commits
apart, so their ambient declarations are not the same objects — consuming a separate 4.32.1
checkout's conclusions means restating them as axioms/hypotheses, which `U05.md` forbids.

## 6. Inaccuracies
1. **Misattributed quotation (the one real defect).** Section (c) prints a `Full error:` block
   attributed to `build.log` line 338 reading *"The argument `⟨t, ⋯⟩` has type `{ r // 0 ≤ r }`
   but is expected to have type `ℝ≥0`"*. That text is in **neither** `build.log` **nor**
   `build-after-fix.log` (`grep "r // 0 ≤ r"` → no hit). The genuine `Full error:` there is
   *"The argument `ht` has type `t ∈ Icc 0 T` but is expected to have type `0 ≤ t ∧ t ≤ T` in the
   application `ht.left`"*. Per the report's own experiment-1 note the `ℝ≥0` wording came from an
   unlogged run, so this is a splice, not an invented finding — the subtype/`ℝ≥0` mismatch **is**
   visible in the pattern-vs-target part of the real message. Fix: label the quote as
   experiment 1, or use the verbatim `build.log` text.
2. **Citation slip.** The `NNReal.mk` docstring came from Mathlib PR **#39409**
   (*doc(Data/NNReal): document the defeq footgun*, 2026-05-15), not #37609 (2026-04-04), which
   added `NNReal.mk` itself. Both predate HeliCorgi's pin, so the substantive point stands;
   `Defs.lean:71` is right.
3. **Presentational.** `build.log` is partly warm, so its "84 built" is only checkable by
   counting `.olean`s or rebuilding cold (done here). Worth a sentence in the report.

Nothing else in sections (a)–(f) diverged from measurement.

## 7. Shared-package integrity
`git -C <shared>/mathlib rev-parse HEAD` = `85e3a25e006c35636f0e53b0e9296caca2685bc0` and
`status --porcelain | wc -l` = `0` at all four checkpoints: before any build, after the warm
reproduce, after the cold rebuild, after the pkgA/pkgC scratch builds. No `lake update`; every
lake command ran with `http_proxy`/`https_proxy` on dead port 9. `git -C WT status --porcelain`
shows `?? research/U05/` only.
