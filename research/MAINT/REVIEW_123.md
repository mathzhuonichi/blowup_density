# REVIEW — lane 123-MAINT-pairing-home

Reviewer run 2026-09-13, worktree `.claude/worktrees/123-MAINT-pairing-home`,
branch `erenup/123-MAINT-pairing-home`, one commit `6600a8a` on top of merge-base
`bbe0fdf43b501481dacfcca18deab1bc5a49e451`.  Probes in `/tmp/rev123/`.
Env: `. scripts/lean-env.sh` (Lean 4.34.0-rc2), all `lake` from `verification/`, `LEAN_NUM_THREADS=6`.

## Verdict: **ACCEPT-WITH-NOTES**

The move is exactly what it claims: two files relocated, bodies byte-identical, namespace
unchanged, the D01 → A04 reverse module edge genuinely removed, everything green.  Three notes,
none blocking; one of them (Finding 3) is a **merge prerequisite** for the lead.

---

## Finding 1 — Byte identity: CONFIRMED (severity: none, PASS)

```
$ git diff -M bbe0fdf HEAD --name-status
M	formalization/NSFormalization/Section4/A04/LaplacianAssembly.lean
M	formalization/NSFormalization/Section4/A04/NonlinearPairing.lean
R099	formalization/NSFormalization/Section4/A04/LaplacianPairing.lean	formalization/NSFormalization/Section4/D01/LaplacianPairing.lean
M	formalization/NSFormalization/Section4/D01/LerayLowering.lean
R099	formalization/NSFormalization/Section4/A04/RealPairing.lean	formalization/NSFormalization/Section4/D01/RealPairing.lean
M	research/A04/ATTEMPTS_SIMP.md
M	research/A04/ATTEMPTS_SL3_PAIRING.md
M	research/A04/ATTEMPTS_SL3_REAL.md
M	research/A04/axioms_sl3_pairing.lean
M	research/A04/axioms_sl3_real.lean
A	research/MAINT/ATTEMPTS_123.md
A	research/MAINT/probes/closure_123.py
```

Both moved files are detected as renames at `similarity index 99%`.  The complete diff of each
moved file is **one hunk, one line — the import**.  Nothing else, docstring header included:

```
--- a/.../Section4/A04/LaplacianPairing.lean
+++ b/.../Section4/D01/LaplacianPairing.lean
@@ -1,4 +1,4 @@
-import NSFormalization.Section4.A04.LaplacianDatum
+import NSFormalization.Section4.D01.DerivativeDatum

--- a/.../Section4/A04/RealPairing.lean
+++ b/.../Section4/D01/RealPairing.lean
@@ -1,4 +1,4 @@
-import NSFormalization.Section4.A04.LaplacianPairing
+import NSFormalization.Section4.D01.LaplacianPairing
 import NSFormalization.Section4.D01.DerivativeDatum
```

Independent body hashes (line 3 onward = the entire docstring + every declaration):

```
$ git show bbe0fdf:.../A04/LaplacianPairing.lean | tail -n +3 | sha256sum
dbb0e1d9c5514c79df82946be44546527dbd1cdeb8119d91cf439fbcc1d37f62  -
$ tail -n +3 .../D01/LaplacianPairing.lean | sha256sum
dbb0e1d9c5514c79df82946be44546527dbd1cdeb8119d91cf439fbcc1d37f62  -

$ git show bbe0fdf:.../A04/RealPairing.lean | tail -n +3 | sha256sum
c8053e17c53611e83e99c7454287663d19383f139b27faf556e566e401705970  -
$ tail -n +3 .../D01/RealPairing.lean | sha256sum
c8053e17c53611e83e99c7454287663d19383f139b27faf556e566e401705970  -
```

Line counts unchanged (199 / 199 and 225 / 225).  21 top-level declarations total
(10 in `LaplacianPairing`, 11 in `RealPairing`, counted by grep), exactly the 21 audited by the two
`axioms_*` files.  No `sorry` / `admit` / `axiom` / `native_decide` / `maxHeartbeats` /
`set_option` in either file.

(Note: `git status` initially showed ten files as "modified" — a stale-stat artifact; `git diff`
is empty and the tree is clean.  Both `research/MAINT/ATTEMPTS_123.md` and
`research/MAINT/probes/closure_123.py` **are** in the commit.)

## Finding 2 — Compiles / gates: ALL GREEN (severity: none, PASS)

| command (from `verification/` unless noted) | result |
|---|---|
| `lake build …D01.{LaplacianPairing,RealPairing,LerayLowering} …A04.{NonlinearPairing,LaplacianAssembly,NonlinearBound} …D01.PressureJets` | `Build completed successfully (9945 jobs).`, 0 errors (only pre-existing vendor `Formal.*` linter warnings) |
| `lake env lean ../formalization/.../D01/LaplacianPairing.lean` | **silent, exit 0** (0 bytes of output) |
| `lake env lean ../formalization/.../D01/RealPairing.lean` | **silent, exit 0** (0 bytes) |
| `lake env lean ../formalization/.../D01/LerayLowering.lean` | **silent, exit 0** |
| `lake env lean ../formalization/.../A04/NonlinearPairing.lean` | **silent, exit 0** |
| `lake env lean ../formalization/.../A04/LaplacianAssembly.lean` | **silent, exit 0** |
| `lake env lean ../research/A04/axioms_sl3_pairing.lean` | 10 decls, each `[propext, Classical.choice, Quot.sound]`, exit 0 |
| `lake env lean ../research/A04/axioms_sl3_real.lean` | 11 decls, each `[propext, Classical.choice, Quot.sound]`, exit 0 |
| `make check` (repo root) | `Ran 13 tests … OK`; `30 work items: ownership, contract registration and task cards consistent.`; exit 0 |
| `make test` | 21 × `checked; standard logical axioms only`, 0 errors, exit 0 |
| `bash scripts/gates.sh <96 Section4 modules>` | `Build completed successfully (10119 jobs).`; `make test` 21 contracts; `Mutation suite passed.`; then **fails at `check_contracts`** — see Finding 3 |

The three repointed importers were elaborated directly, not merely replayed, because their import
closures **shrank**: `D01.LaplacianPairing` no longer pulls in `A04.LaplacianDatum`→`A04.HighEnergy`,
so `D01/LerayLowering` and `A04/NonlinearPairing` (whose only import is the pairing module) lost
access to those names.  All three are silent — nothing was being borrowed transitively.

Tail of `make test`:
```
ℹ [10074/10075] Replayed Tests.TameProduct
info: Tests/TameProduct.lean:14:0: Contract BlowupDensity.Tests.checkedTameProduct: checked; standard logical axioms only
ℹ [10075/10075] Replayed Tests.InsertionLifespanV2
info: Tests/InsertionLifespanV2.lean:32:0: Contract BlowupDensity.Tests.checkedInsertionLifespanV2: checked; standard logical axioms only
```

**No code file references the old module paths.**
```
$ grep -rn '^import .*Section4\.A04\.\(LaplacianPairing\|RealPairing\)' --include='*.lean' formalization verification research
(none)
$ grep -rn 'A04\.LaplacianPairing\|A04\.RealPairing' --include='*.lean' research
(none)
```
The only two remaining occurrences in `.lean` files are docstring prose — Finding 4.

## Finding 3 — `scripts/gates.sh` fails at `check_contracts`; branch is behind integration (severity: **low, but a merge prerequisite**)

```
$ bash scripts/gates.sh <96 modules>          # GATES_EXIT=1
== check_contracts
Traceback (most recent call last):
  File ".../experiments/check_contracts.py", line 153, in <module>
    print(json.dumps(check(base=args.base_ref), indent=2))
  File ".../experiments/check_contracts.py", line 143, in check
    check_compatibility(root, base, contracts)
  File ".../experiments/check_contracts.py", line 62, in check_compatibility
    assert (root / path).is_file(), f'Removed stable specification: {path}'
AssertionError: Removed stable specification: verification/Contracts/V3/DatumLemmas.lean
```

**Not a defect of this lane.**  `gates.sh` defaults `BASE_REF=origin/erenup/integration`, and this
branch is 1-ahead / **12-behind** that ref.  `verification/Contracts/V3/DatumLemmas.lean` was added
to integration *after* this lane branched, by lane 120 / PR #122
(`1c1835b [120-D01] D01.datum_lemmas V3: register P2 … (22nd contract)`), so the checker sees it as
deleted.  Against the lane's true base it passes:

```
$ python3 experiments/check_contracts.py --base-ref bbe0fdf43b501481dacfcca18deab1bc5a49e451 | tail -3
  "base_compatibility_checked": true,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}                                                            # EXIT=0
```

`research/MAINT/ATTEMPTS_123.md` records `check_contracts` as OK — true when the lane ran it,
stale now.  **Action for the lead:** rebase onto current `erenup/integration` and re-run
`scripts/gates.sh` before merging; the rebase is trivial (this lane touches no registry or ledger
file — `PLAN.md`, `work_items.json`, `TASKS.md`, `contracts.json`, `AGENT_RUNS.csv` are all
untouched, so there is nothing to three-way merge).

## Finding 4 — Two stale module-path references left in `.lean` docstrings (severity: low, cosmetic)

Byte-identity was chosen over docstring accuracy — the right trade for a relocation lane (the hash
equality is the stronger reviewer guarantee), but it leaves the prose wrong in two places:

- `formalization/NSFormalization/Section4/D01/RealPairing.lean:13` — "Lane 076
  (`Section4/A04/LaplacianPairing.lean`) proved the adjointness/self-adjointness facts …"; the
  sibling now lives at `Section4/D01/LaplacianPairing.lean`.
- `formalization/NSFormalization/Section4/A04/NonlinearPairing.lean:20` — "a corollary of lane 082
  (`A04.RealPairing`)"; now `D01.RealPairing`.

Both moved files also still open with `# A04 unit G1, sub-lemma SL3, …`.  That title is defensible
(it names the *consuming* unit, not the file's directory) and I would leave it; only the two file
paths above are factually wrong.  Suggested follow-up: a two-line cosmetic commit, deliberately
*after* this lane so the byte-identity evidence stands on its own.  `.md` history files that name
the old paths are correctly left alone as history.

## Finding 5 — Orphaned oleans make "it builds" useless as repoint evidence (severity: low; **candidate LESSONS line**)

`git mv` does not remove the old build products.  Still present, both here and in the root checkout:

```
$ ls formalization/.lake/build/lib/lean/NSFormalization/Section4/A04/ | grep -iE 'laplacianpairing|realpairing'
LaplacianPairing.ilean  LaplacianPairing.ilean.hash  LaplacianPairing.olean
LaplacianPairing.olean.hash  LaplacianPairing.trace
RealPairing.ilean  RealPairing.ilean.hash  RealPairing.olean  RealPairing.olean.hash  RealPairing.trace
```

So the **old import path still resolves locally**:

```
$ cat /tmp/rev123/stale_olean.lean
import NSFormalization.Section4.A04.LaplacianPairing
#check @NSFormalization.Paper3.inner_angularDirectionalDerivative_right

$ lake env lean /tmp/rev123/stale_olean.lean
NSFormalization.Paper3.inner_angularDirectionalDerivative_right : ∀ (s : ℝ) (a : NavierStokes.ProblemStatement.Space)
  (f g : ↥(MeasureTheory.Lp ℂ 2 MeasureTheory.volume)),
  inner ℂ f ((NSFormalization.Paper3.angularDirectionalDerivative s a) g) =
    -inner ℂ ((NSFormalization.Paper3.angularDirectionalDerivative s a) f) g
EXIT=0
```

A missed importer would therefore have compiled green locally and only broken in CI's fresh
checkout.  The lane's conclusion is still sound — but the *grep* is what establishes it, not the
build.  I ran that grep (Finding 2): zero remaining import references anywhere.  No action needed
on this lane; the generalisable rule is "after a `git mv` of a Lean module, the local green build
proves nothing about importers — grep, or wipe `.lake/build` for that directory."

## Finding 6 — Layering: reverse edge genuinely removed (severity: none, PASS)

I ran the lane's probe and an independently written one (`/tmp/rev123/mygraph.py`, 435 modules,
parses every `import` line rather than only `NSFormalization.*` ones) — they agree.

```
$ python3 research/MAINT/probes/closure_123.py            # PROBE_EXIT=0
=== D01 modules whose import-closure reaches A04 (reverse edge) ===
  NONE — no Section4.D01.* module imports any Section4.A04.* module.
  NSFormalization.Section4.D01.LaplacianPairing imports: ['NSFormalization.Section4.D01.DerivativeDatum']
  NSFormalization.Section4.D01.RealPairing imports: ['NSFormalization.Section4.D01.LaplacianPairing', 'NSFormalization.Section4.D01.DerivativeDatum']
  NSFormalization.Section4.A04.LaplacianPairing present as file? False
  NSFormalization.Section4.A04.RealPairing present as file? False

$ python3 /tmp/rev123/mygraph.py                          # MY_EXIT=0
modules scanned: 435
--- (a) Section4.D01.* reaching Section4.A04.* (transitive) ---   NONE
--- (b1) Paper3.* reaching Section4.* (transitive) ---            NONE
--- (b2) Source.* reaching Section4.* (transitive) ---            NONE
--- (b3) Paper1.* reaching Section4.* (transitive) ---            NONE
--- who imports the moved modules (direct) ---
   …D01.LaplacianPairing <- ['…Section4.D01.LerayLowering', '…Section4.D01.RealPairing']
   …D01.RealPairing      <- ['…Section4.A04.LaplacianAssembly', '…Section4.A04.NonlinearPairing', '…Section4.D01.LerayLowering']
--- cycle check over whole NSFormalization graph ---   cycles: NONE
```

(a) and (b) both hold, transitively, and there are no import cycles anywhere in
`NSFormalization`.  The reverse importer set is exactly the five files the lane repointed plus the
moved `RealPairing` itself.  The two surviving edges into A04-land,
`A04.{NonlinearPairing,LaplacianAssembly} → D01.RealPairing`, are **forward** (A04 → D01), which the
DAG allows.

## Finding 7 — The 115 reviewer's `Paper3/` home really is infeasible (severity: none, PASS)

Definitions located by grep over `formalization/NSFormalization` — each of the four blockers is in
a `Section4.D01.*` module (they sit inside a `namespace NSFormalization.Paper3` block, which is why
the 115 reviewer's "uses no A04 declaration" claim was correct yet led to the wrong home):

| name | defining module:line |
|---|---|
| `angularDirectionalDerivative` | `Section4/D01/DerivativeDatum.lean:62` |
| `angularDirectionalDerivativeReal` | `Section4/D01/DerivativeDatum.lean:134` |
| `angularDirectionalDerivativeReal_coe` | `Section4/D01/DerivativeDatum.lean:141` |
| `lowering_symbol_real` | `Section4/D01/DerivativeDatum.lean:175` |
| `mid_symbol_imaginary` | `Section4/D01/DerivativeDatum.lean:183` |

(`angularOrderLowering`, by contrast, *is* Paper3-native — `Paper3/AngularTameProduct.lean:39` — so
these five are the whole obstruction.)

**Negative probe, reproduced independently.**  I rebuilt it from scratch (moved file's body, line 1
replaced by the six Paper3 helper imports) and it came out **byte-identical** to the lane's
`tmp/probe123/probe_lap_paper3.lean` (`diff` empty).

```
$ lake env lean /tmp/rev123/neg_lap_paper3.lean      # EXIT=1, 11 errors
/tmp/rev123/neg_lap_paper3.lean:67:4: error: Function expected at
  angularDirectionalDerivative
but this term has type
  ?m.1
…
Hint: The identifier `angularDirectionalDerivative` is unknown, and Lean's `autoImplicit` option
causes an unknown identifier to be treated as an implicitly bound variable with an unknown type. …
/tmp/rev123/neg_lap_paper3.lean:100:15: error(lean.unknownIdentifier): Unknown identifier `mid_symbol_imaginary`
/tmp/rev123/neg_lap_paper3.lean:177:15: error(lean.unknownIdentifier): Unknown identifier `lowering_symbol_real`
```
(`The identifier ... is unknown` × 3 for `angularDirectionalDerivative`; literal
`Unknown identifier` for the other two.)

And a minimal, cascade-free version giving the literal message for all three:

```
$ cat /tmp/rev123/neg_names.lean     # six Paper3 imports + open NSFormalization.Paper3
#check @lowering_symbol_real
#check @mid_symbol_imaginary
#check @angularDirectionalDerivative

$ lake env lean /tmp/rev123/neg_names.lean           # EXIT=1
/tmp/rev123/neg_names.lean:8:8: error(lean.unknownIdentifier): Unknown identifier `lowering_symbol_real`
/tmp/rev123/neg_names.lean:9:8: error(lean.unknownIdentifier): Unknown identifier `mid_symbol_imaginary`
/tmp/rev123/neg_names.lean:10:8: error(lean.unknownIdentifier): Unknown identifier `angularDirectionalDerivative`
```

Positive probe: the lane's `tmp/probe123/probe_lap.lean` is byte-identical to the committed
`Section4/D01/LaplacianPairing.lean` (`diff` empty), which elaborates silently — so the
`D01.DerivativeDatum`-only import genuinely suffices.  **Home decision is correct: `Section4/D01/`,
not `Paper3/`.**

*Reviewer trap for the record:* `lake env lean … 2>&1 | tee log | head -40` SIGPIPEs Lean mid-write;
my first log stopped at 107 lines and `lowering_symbol_real` appeared **not** to be flagged, which
would have been a false discrepancy against the lane's claim.  Redirect to a file, then filter.

## Finding 8 — Bare-name ambiguity risk (lane-109 lesson): NIL (severity: none, PASS)

Each of the 21 relocated names was grepped for `def`/`theorem`/`lemma`/`abbrev`/`alias`/`instance`
definitions across all of `formalization/NSFormalization` **and** `vendor/`:

```
angularDirectionalMid                            1
angularDirectionalDerivative_eq_dilation_mid     1
angularDirectionalMid_coeFn                      1
inner_angularDirectionalMid                      1
inner_angularDirectionalDerivative_right         1
angularOrderLoweringMid                          1
angularOrderLowering_eq_dilation_mid             1
angularOrderLoweringMid_coeFn                    1
inner_angularOrderLoweringMid                    1
inner_angularOrderLowering                       1
real_inner_eq_re_complex                         1
realSobolev_inner_eq_ambient                     1
real_inner_angularDirectionalDerivative          1
real_inner_angularDirectionalDerivativeReal      1
lowering_mid_symbol_eq                           1
lowering_mid_symbol_order_indep                  1
angularOrderLoweringMid_self                     1
angularOrderLowering_self                        1
inner_loweringMid_pairing                        1
inner_lowering_pairing_complex                   1
real_inner_lowering_pairing                      1
```

Exactly one definition each, all in `NSFormalization.Paper3`.  The lane-109 failure mode needs
*two* namespaces exporting the same bare name; here the namespace is unchanged, every FQN is
unchanged, **no `alias`/shim was left at the old A04 paths** (both old modules are gone as source
files), and the diff introduces no new `open`.  So no module can now `open` two namespaces both
defining one of these 21 names.  Consistent with the observation that each of the 21
`#print axioms` printed exactly one interpretation.

*One methodological nit in the record:* `ATTEMPTS_123.md` writes "Confirmed post-move by the two
`axioms_*` conformance files elaborating with no unknown-identifier / ambiguity errors."  Per
`logs/LESSONS.md`, `#print axioms` on an ambiguous name prints **both** interpretations instead of
erroring, so that is not by itself evidence of non-ambiguity.  The grep-uniqueness check — which
the lane also did, and which I redid above — is the real evidence.  Harmless overstatement here.

## Finding 9 — Records honesty: VERIFIED (severity: none, PASS)

All five `DerivativeDatum.lean` citations in `ATTEMPTS_123.md` are exact:

```
  62: def angularDirectionalDerivative (s : ℝ) (a : Space) :
 134: def angularDirectionalDerivativeReal (s : ℝ) (a : Space) :
 141: @[simp] theorem angularDirectionalDerivativeReal_coe (s : ℝ) (a : Space)
 175: theorem lowering_symbol_real (s r : ℝ) (ξ : Space) :
 183: theorem mid_symbol_imaginary (s : ℝ) (a ξ : Space) :
```

The three note edits are each a **single added line** (plus a blank):
`research/A04/ATTEMPTS_SL3_PAIRING.md` and `ATTEMPTS_SL3_REAL.md` get a one-line relocation
blockquote at the top; `research/A04/ATTEMPTS_SIMP.md` gets a one-line **DONE — lane 123** entry in
its MAINT list closing reviewer Finding 6.  The importer table, the probe outputs and the
"Failures / dead ends: None" claim all check out.  Registry and ledger files untouched.

The only stale line is the `check_contracts` row of the commands table (Finding 3), and one
methodological overstatement (Finding 8) — neither affects the result.

---

## Commands run (reviewer)

```
git diff -M bbe0fdf HEAD --stat / --name-status / -- <each moved file>
git show bbe0fdf:<old path> | tail -n +3 | sha256sum     (× 2, vs tail -n +3 <new path>)
. scripts/lean-env.sh                                     (Lean 4.34.0-rc2)
cd verification && lake build <7 modules>                 → Build completed successfully (9945 jobs)
cd verification && lake env lean ../formalization/.../D01/{LaplacianPairing,RealPairing}.lean        → silent, 0
cd verification && lake env lean ../formalization/.../{D01/LerayLowering,A04/NonlinearPairing,A04/LaplacianAssembly}.lean → silent, 0
cd verification && lake env lean ../research/A04/axioms_sl3_{pairing,real}.lean                      → 10 + 11 decls, 3 std axioms
cd verification && lake env lean /tmp/rev123/stale_olean.lean        → EXIT=0 (orphan olean, Finding 5)
cd verification && lake env lean /tmp/rev123/neg_lap_paper3.lean     → EXIT=1, 11 errors (Finding 7)
cd verification && lake env lean /tmp/rev123/neg_names.lean          → EXIT=1, 3 unknown identifiers
make check                                                → OK
make test                                                 → 21 contracts, standard axioms, 0 errors
bash scripts/gates.sh <96 Section4 modules>               → build 10119 jobs OK, test OK, mutations passed,
                                                             check_contracts AssertionError (Finding 3)
python3 experiments/check_contracts.py --base-ref bbe0fdf → base_compatibility_checked: true, EXIT=0
python3 research/MAINT/probes/closure_123.py              → EXIT=0, no reverse edge
python3 /tmp/rev123/mygraph.py                            → EXIT=0, 435 modules, (a)+(b) clean, no cycles
grep -rn '^import .*Section4\.A04\.\(LaplacianPairing\|RealPairing\)' over formalization/ verification/ research/  → none
grep per-name definition count for all 21 names over formalization/ + vendor/                                      → 1 each
diff tmp/probe123/probe_lap.lean       .../D01/LaplacianPairing.lean   → identical
diff tmp/probe123/probe_lap_paper3.lean /tmp/rev123/neg_lap_paper3.lean → identical
```

## Recommendation to the lead

Merge, after a rebase onto current `erenup/integration` plus one re-run of `scripts/gates.sh`
(Finding 3 — the only gate that is red, and only because of the stale base; nothing to three-way
merge since no registry file is touched).  Findings 4 and 5 are follow-ups, not blockers;
Finding 5 is worth a line in `logs/LESSONS.md`.
