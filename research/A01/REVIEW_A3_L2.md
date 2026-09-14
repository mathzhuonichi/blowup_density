# REVIEW — lane 139-A01-a3-l2-horizon (unit A3, row A3-L2: `horizon := S`)

Reviewer run 2026-09-13, worktree `.claude/worktrees/139-A01-a3-l2-horizon`,
branch `erenup/139-A01-a3-l2-horizon` @ `dc00cef`, merge-base with
`origin/erenup/integration` = `9a68411`.  Probes in `/tmp/rev139/`.

## Verdict: **ACCEPT-WITH-NOTES**

The Lean is correct, clean, first-try-compiling and honestly axiom-audited; the two
statement-fidelity questions (is `HasAprioriBound` *the* `hbound`? is the conclusion *the*
`exists_local` clause block?) both come back **exactly yes**, verified by `rfl`/`Iff.rfl` and by
zero-line machine diffs.  The notes are about **claims around the Lean**, not the Lean: one
over-stated modelling sentence in the docstring (F5), one corollary that is weaker than it looks
(F6), and three merge-time bookkeeping items the lead must handle (F8–F10), including a real
**module-name collision** with the lane the previous review already reserved `Horizon.lean` for.

---

## 1. Compiles / axioms / hygiene — **PASS**

```
$ . scripts/lean-env.sh; cd verification
$ LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.A01.ContinuationInvariant \
    Euler.OrdinaryCauchyInterpolation Euler.OrdinaryH3Norms Euler.SmoothL2Series Euler.LpSmoothFieldAlgebra
Build completed successfully (4692 jobs).            # EXIT=0
$ LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.A01.Horizon
Build completed successfully (3943 jobs).            # EXIT=0
$ LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section4/A01/Horizon.lean
                                                     # EXIT=0, 0 bytes — silent, no warning
$ LEAN_NUM_THREADS=6 lake env lean ../research/A01/axioms_a3_l2.lean    # EXIT=0
'…A01.HasAprioriBound'                     depends on axioms: [propext, Classical.choice, Quot.sound]
'…A01.horizonOf'                           depends on axioms: [propext, Classical.choice, Quot.sound]
'…A01.horizonOf_eq'                        depends on axioms: [propext, Classical.choice, Quot.sound]
'…A01.localTheory_on_prescribed_horizon'   depends on axioms: [propext, Classical.choice, Quot.sound]
'…A01.exists_local_shape_of_aprioriBound'  depends on axioms: [propext, Classical.choice, Quot.sound]
$ cd .. && make check                                # EXIT=0
… Ran 13 tests in 0.041s / OK
… 30 work items: ownership, contract registration and task cards consistent.
```

The two zero-data non-vacuity `example`s inside `axioms_a3_l2.lean` (`ha` for `zeroField`, `hu₀`
for every `R ≥ 0`) are part of that clean run.

Hygiene grep over the two new Lean files:

```
$ grep -nE 'sorry|admit|axiom|native_decide|maxHeartbeats|set_option' \
    formalization/NSFormalization/Section4/A01/Horizon.lean research/A01/axioms_a3_l2.lean
research/A01/axioms_a3_l2.lean:13-17: #print axioms …            (the audit itself)
research/A01/axioms_a3_l2.lean:36:    set_option autoImplicit false   (a strengthening)
```

`Horizon.lean` itself: **zero** hits — no `sorry`, no `admit`, no `axiom`, no `native_decide`,
no `set_option`, no heartbeat bump.  Notable given the parent `ContinuationInvariant.lean` needs
`maxHeartbeats 600000`; this module is pure repackaging and costs nothing.

## 2. Statement fidelity

### F1 (a) `HasAprioriBound` **is** `forced_global_of_bound_unconditional`'s `hbound` — PASS

`/tmp/rev139/fidelity.lean` §(a), two `example`s whose right-hand side is copy-pasted from
`ContinuationInvariant.lean:285-289`, closed by `rfl` and by `Iff.rfl` respectively.  Both
elaborate (`lake env lean /tmp/rev139/fidelity.lean`, EXIT=0, no error output).  So the named
predicate is *definitionally* the binder, not a paraphrase, and the quantifier order the
docstring advertises (`R` before `T`, before `u`) is the binder's own order — confirmed by
`#check @HasAprioriBound` and by `#check @forced_global_of_bound_unconditional` printing the same
`∀ (T : ℝ) (hT : 0 ≤ T) (hTS : T ≤ S) (u : C(↑(Icc 0 T), ↥(SobolevSpace 1 (q+1)))), … → ‖u‖ ≤ R`
under the fixed `R`.

### F2 (b) the conclusions are `exists_local`'s, clause for clause — PASS

Machine diff, `exists_local`'s conclusion block (`Source/OrdinaryForcedLocal.lean:36-47`) after
the substitution `T := S`, `hT.le := hS.le`, `hTS := le_rfl`, norm clause `:= R`:

```
A) localTheory_on_prescribed_horizon  vs  exists_local[T:=S, norm:=R]
   IDENTICAL — 0 differing lines (11 lines each)
B) exists_local_shape_of_aprioriBound vs  exists_local[norm:=R]
   IDENTICAL — 0 differing lines (12 lines each; only the proof term line differs)
```

Independent Lean-level confirmation (`/tmp/rev139/fidelity.lean` §(b)): a goal **copy-pasted
verbatim** from `exists_local`'s source (norm clause `‖u‖ ≤ ‖u₀‖+1` included, unmodified) is
discharged by

```lean
obtain ⟨T, hT, hTS, u, U, hu, rest⟩ := exists_local_shape_of_aprioriBound hq hν hS hR a ha F hF hu₀ hb
exact ⟨T, hT, hTS, u, U, hu.trans hRle, rest⟩
```

The reuse of the untouched tail `rest` type-checks only if clauses 2–7 are *syntactically the
same types*; only the norm clause moves.  §(c) additionally shows the conclusion also holds
stated on `Icc 0 (horizonOf hν a F)` by `rfl` defeq, so a `horizonOf`-facing consumer loses
nothing.

### F3 **(MEDIUM)** (c) `horizonOf := S` does **not** realise `LocalTheoryAPI.horizon`; the docstring's `horizon` bullet overstates

The spec field is

```lean
horizon : ℝ → SpatialField → SpaceTimeField → ℝ        -- Spec.lean:283
-- SpatialField := Space → Space, SpaceTimeField := VelocityField (Contracts/V1/Data.lean:99,104)
```

whereas `#check @horizonOf` prints

```
@horizonOf : {ν S : ℝ} → 0 < ν → SmoothL2Field Space → (↑(Icc 0 S) → SmoothL2Field Space) → ℝ
```

Three gaps, all real:

1. **Wrong type.**  It takes a *proof* `0 < ν` (not `ν : ℝ`), a bundled `SmoothL2Field Space`
   (not `SpatialField`), and a path on a *prescribed interval* `Icc 0 S` (not a
   `SpaceTimeField` on all of time).  It is the cylinder-carrier analogue, not the field.
2. **`S` is an input, not an output.**  `horizonOf` reads `S` off the *type index* of `F`; it
   computes nothing.  `LocalTheoryAPI.horizon` must *produce* a number from `(ν,a,f)`, and `f`
   there carries no `S`.  So "`horizon := S`" is only meaningful once someone hands over an `S`
   **together with** `HasAprioriBound` for that `S`.
3. **The conditionality is on the wrong bullet.**  The docstring writes
   "`horizon` (`Spec.lean:283`) — **modelled** by `horizonOf hν a F = S`" unconditionally, and
   puts "conditional on `HasAprioriBound`" only on the `solution` bullet.  But it is exactly the
   horizon that is conditional: without the bound there is no reason the solution reaches `S`.

What an eventual `LocalTheoryAPI` witness must therefore supply, precisely:

* **the bound** — `HasAprioriBound` for the datum at hand, i.e. A3-M2 (Grönwall integral step,
  after 138) + A3-L1·k (order-2 cap, still blocked on `D-euler-pairing`) **plus** the mild⟹energy
  bridge, since `hbound` quantifies over *mild* solutions while eq:Rhigh is an energy identity;
* **a choice of `S` as a function of the datum** — `S = S(ν,a,f)`, the largest endpoint for which
  that bound is available; a *constant* `S` is not admissible (it would make `solution` a global
  existence claim);
* **the datum bridge** (rows B1/B2) — `SpatialField`/`SpaceTimeField` ⟶
  `SmoothL2Field Space` / `Icc 0 S → SmoothL2Field Space` in, and the cylinder pair `(u,U)` ⟶
  `ClassicalSolutionR ν a f (horizon ν a f)` out;
* and `regularity` (A2/T1) and `horizon_lower_bound` (H1) still separately.

The module docstring states items 1 (bound), 3 (bridge), and the two remaining fields correctly
and in the right places; it does **not** state item 2, and its `horizon` bullet reads
unconditional.  **Recommendation (cheap, `Horizon.lean` is not frozen):** change the `horizon`
bullet to say that `horizonOf` is the *cylinder-carrier* analogue of the field, that its value is
the prescribed input `S` rather than a computed horizon, and that a real `LocalTheoryAPI.horizon`
must choose `S` per datum.  Not a blocker — nothing in Lean is wrong — but it is the kind of
sentence that gets copied forward (cf. `LESSONS.md`, "论文行号引用会代代相传").

### F4 **(LOW–MEDIUM)** `exists_local_shape_of_aprioriBound` is vacuous content when `‖u₀‖ + 1 ≤ R`

Probe `/tmp/rev139/strength.lean` proves the corollary's **full** conclusion from
`Source.OrdinaryForcedLocal.exists_local` **alone** — no `HasAprioriBound`, no `hu₀`, no `hR`:

```lean
obtain ⟨T, hT, hTS, u, U, hu, rest⟩ := exists_local hq hν hS a ha F hF
exact ⟨T, hT, hTS, u, U, hu.trans hRbig, rest⟩       -- hRbig : ‖u₀‖ + 1 ≤ R
```
`lake env lean /tmp/rev139/strength.lean` → EXIT=0, 0 bytes.

So in the regime `R ≥ ‖u₀‖+1` the `∃ T` corollary carries **none** of A3-L2's content; its new
content lives only in `R < ‖u₀‖+1`, and even there the fact that `T` may be taken `= S` is
invisible in the type.  The lane's `ATTEMPTS` already argues this direction ("Pinning `T = S` is
not visible in a bare `∃ T` type, which is exactly why the primary deliverable is
`localTheory_on_prescribed_horizon`") — good — but neither the docstring nor `ATTEMPTS` says the
corollary is *derivable without the hypothesis* in the natural regime.  **Recommendation:** one
sentence in the corollary's docstring: "for `R ≥ ‖u₀‖+1` this follows from `exists_local` alone;
consumers that need the horizon pinned must use `localTheory_on_prescribed_horizon`."

### F5 (INFO) non-vacuity of `HasAprioriBound` — correctly and prominently stated

`HasAprioriBound` occurs **only** in `Horizon.lean` and `research/A01/axioms_a3_l2.lean`
(`grep -rn` over `formalization/`, `research/`, `verification/`), and is **never instantiated**,
on zero data or otherwise.  Consequently `localTheory_on_prescribed_horizon` currently has no
instance at all: it inherits exactly the status of its parent
`forced_global_of_bound_unconditional`.  The lane says this in three places — the module
docstring ("Supplying it is A3's remaining job"), `ATTEMPTS_A3_L2.md` §"The residual", and the
audit file's own comment, which even cites lane 134's finding F5 (zero data would itself need
the global uniqueness the continuation stack avoids).  This is exactly the honesty standard.
Recorded here so the lead does not read "A3-L2 DONE" as new mathematical reach: **nothing became
provable that was not provable before this lane**; the lane names things and fixes `T = S`.

## 3. Consistency — **PASS** with process notes

* **Imports**: `Horizon.lean` imports exactly `NSFormalization.Section4.A01.ContinuationInvariant`
  — one line, nothing else.  Not a `Contracts/` file, so the import policy does not apply;
  `make check` (which runs `check_contracts.py` / `test_contract_policy.py`) is green.
* **No restated definitions**: the module defines only the two new names; everything else comes
  through the import.  `grep -rniE 'horizonOf|HasAprioriBound|def horizon' formalization/` outside
  `A01/Horizon.lean` → **empty**.  The repeated `local instance : Fact (0 < (1:ℝ))` is required
  (the parent's is `local` and does not leak) and is the same idiom as
  `Continuation.lean`/`ContinuationInvariant.lean`.
* **No duplication**: `Continuation.lean` has `forced_global_of_bound` / `forced_global_of_bound'`
  and `ContinuationInvariant.lean` has `forced_global_of_bound_unconditional`, all of which state
  the conclusion on the *literal* `[0,S]` with an explicit `hbound` binder.  **None** of them has
  the `∃ T` shape, so `exists_local_shape_of_aprioriBound` is new (if thin, see F4), and
  `localTheory_on_prescribed_horizon` is a renaming of the `hbound` slot, not a second copy.
* **Naming**: `horizonOf` vs the spec's `horizon` — the suffix is correct and deliberate (the
  spec name belongs to the `LocalTheoryAPI` field, and F3 shows this is not that field).
  `horizonOf`/`horizonOf_eq` currently have **no consumer**: `horizonOf` reduces to
  `fun _ _ _ => S` and `horizonOf_eq` is `rfl`, `@[simp]`-tagged (harmless, terminating).  Two
  lines of zero mathematical content, honestly described as "the horizon selector"; keep.

### F6 (INFO) process note (i) — `REVIEW_A3_FORCE.md` was **not** missed

It is on `origin/erenup/integration`, added by `8e32153 [137-A01] A3-L1·f …` (PR #140), i.e.
**after** this lane's merge-base `9a68411` — so the lane genuinely could not see it.  I read it:
its §5.2 item 3 ("A3-L2 (`horizon := S`) — ready now, size S, no dependencies … `horizon` is a
definition plus a one-line lemma") is *exactly* what this lane built, and the lane's deliverable
is a superset (it also names `HasAprioriBound` and adds the `∃ T` corollary).  **Nothing
mathematical was missed.**  One non-mathematical thing was — see F7.

### F7 **(MEDIUM, process)** module-name collision: `Section4/A01/Horizon.lean` was already reserved for a *different* lane

`REVIEW_A3_FORCE.md:258` (and, merged into integration by 137, `A3_SPLIT.md` §3.5):

> **Recommended next A01 lane (S)**: `Section4/A01/Horizon.lean` instantiating
> `gronwall_bddAbove_Ico` on a `ClassicalSolutionR`.

That is a *different* deliverable (the per-order uniform bound, whose only hole is `Kbnd` =
A3-L1·k).  Lane 139 has taken the filename for the A3-L2 packaging.  The next lane will collide.
**Lead action at merge:** pick one — either rename 139's module (e.g.
`Section4/A01/PrescribedHorizon.lean`) or, cheaper, retarget the Grönwall lane's filename (e.g.
`Section4/A01/UniformBound.lean`) — and fix the pointer in `A3_SPLIT.md` §3.5 and in
`REVIEW_A3_FORCE.md:258`, `:305`.

### F8 **(MEDIUM, process)** `research/A01/A3_SPLIT.md` conflicts with 137 — **one hunk**, trivial resolution

```
$ git merge-tree --write-tree origin/erenup/integration dc00cef            # EXIT=1
Auto-merging research/A01/A3_SPLIT.md
CONFLICT (content): Merge conflict in research/A01/A3_SPLIT.md
```
Only that one file, and inside it only **one** hunk: the three-row block at base lines **70–72**
(`A3-L1·k`, `A3-L1·f`, `A3-L2`).  137 rewrote rows `A3-L1·k` and `A3-L1·f` (the latter to
**DONE (lane 137)**); 139 rewrote row `A3-L2`.

**Resolution:** take **integration's** `A3-L1·k` and `A3-L1·f` lines verbatim, then **139's**
`A3-L2` line verbatim.  Nothing else in the file conflicts — the lane's §3b prose insert
(base `:78-84`) and its `A01_SPLIT.md:88` edit both auto-merge.  (Verified by a three-way
`git merge-file --diff3`: exactly one `<<<<<<<` marker, at merged line 70.)

### F9 **(LOW, process)** two stale bookkeeping lines the lane did not (and could not) update

* `A3_SPLIT.md` §(d) "Pure-bookkeeping rows", line `:194`:
  "**A3-L2** — dissolved by A2b-a′ (`horizon := S`); no analysis." — now stale; the lane updated
  the row table and §3b but not this bullet.
* On integration only, `A3_SPLIT.md` §3.5 table + "Suggested order: **A3-L2** (S, ready) → …" —
  A3-L2 is no longer "ready", it is done.  Same for `REVIEW_A3_FORCE.md:272,:305` (historical
  record; leave it, but the §3.5 pointer should be refreshed together with F7).

### F10 (INFO) process note (ii) — "A2b-b" wording: **already fixed by lane 134; the cited line numbers are wrong**

```
$ git show origin/erenup/integration:research/A01/A3_SPLIT.md | grep -n 'A2b-b'
66: | **A2b-a** = reviewer §3 **A2b-b** | …
67: | **A2b-c** (was A2b-b) | … **Renamed A2b-b→A2b-c** so "A2b-b" matches the reviewer's §3 name …
79: **DONE (lane 126)** … A2b-a (= reviewer §3 A2b-b,
```
All three surviving occurrences are the *deliberate* alias to the reviewer's §3 naming, with the
rename explained inline at `:67` — lane 134's merged rename did fix it, and **no action is
needed**.  The lane's citation `A3_SPLIT.md:168/:192` points at "…the one file that mattered."
and "* **A3-S2′ / lowestOrderSq** …" in both the worktree and integration copies — i.e. the line
numbers are simply wrong.  Flagged only because `LESSONS.md` already has an entry about stale
line citations propagating.

## 4. Honesty of `ATTEMPTS_A3_L2.md` — **PASS**

`ATTEMPTS` claims "No failed Lean approaches … compiled on the first `lake build`", so there is
no failure to reproduce.  Everything checkable in it checks out, including the job counts:

| claim in `ATTEMPTS` | reproduced |
|---|---|
| `lake build … Horizon` = `Build completed successfully (3943 jobs)` | **exact** — `3943` |
| the four `Euler.*` modules build = `Build completed successfully (4682 jobs)` | **exact** — `4682` |
| `lake env lean` on the module silent, 0 bytes, no warning | **yes**, EXIT=0, 0 bytes |
| every `#print axioms` = the standard 3 | **yes**, all five |
| `make check` green | **yes** |
| no `set_option`, default heartbeats | **yes** |
| `hb` unifies with the `∀`-shaped `hbound` slot by `isDefEq`, no `unfold` | **yes** (F1) |

The one recorded non-Lean snag — `lake env lean ../research/A01/axioms_a3_l2.lean` failing with
`object file … .olean does not exist` unless the four `Euler.*` modules are built first — was
**not reproduced directly** (it would require deleting oleans under the shared, symlinked
`verification/.lake/packages`, which would cost every worktree a rebuild).  Its premise is
confirmed indirectly: `Horizon`'s own closure is 3943 jobs while the four `Euler.*` modules are
4682, so they are **not** in `Horizon`'s import closure and a bare `lake build Horizon` does
leave them unbuilt.  Consistent with the identical note in lane 134's audit.

## 5. Summary for the lead

Merge it.  Before/at merge: resolve the one `A3_SPLIT.md` hunk as in **F8**; settle the
`Horizon.lean` filename collision in **F7**; refresh the two stale lines in **F9**.  Ask the
lane (or take it as a lead edit, the module is not frozen) for the two one-sentence docstring
amendments in **F3** and **F4**.  Nothing here blocks the A3 chain, and nothing here advances it:
the chain's live blocker is unchanged — `D-euler-pairing` ⟶ A3-L1·k ⟶ `Kbnd` ⟶ `HasAprioriBound`.

## Commands run (all from the worktree)

```
. scripts/lean-env.sh
cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.A01.ContinuationInvariant \
    Euler.OrdinaryCauchyInterpolation Euler.OrdinaryH3Norms Euler.SmoothL2Series Euler.LpSmoothFieldAlgebra
cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.A01.Horizon
cd verification && LEAN_NUM_THREADS=6 lake build Euler.OrdinaryCauchyInterpolation Euler.OrdinaryH3Norms \
    Euler.SmoothL2Series Euler.LpSmoothFieldAlgebra
cd verification && LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section4/A01/Horizon.lean
cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/A01/axioms_a3_l2.lean
cd verification && LEAN_NUM_THREADS=6 lake env lean /tmp/rev139/fidelity.lean     # F1, F2
cd verification && LEAN_NUM_THREADS=6 lake env lean /tmp/rev139/strength.lean     # F4
make check
grep -nE 'sorry|admit|axiom|native_decide|maxHeartbeats|set_option' <the two new .lean files>
grep -rniE 'horizonOf|HasAprioriBound|def horizon' formalization/NSFormalization/
git merge-tree --write-tree origin/erenup/integration dc00cef
git merge-file --diff3 -L integration -L base -L lane139 <integ> <base> <lane>   # F8
git show origin/erenup/integration:research/A01/A3_SPLIT.md | grep -n 'A2b-b'    # F10
git show origin/erenup/integration:research/A01/REVIEW_A3_FORCE.md | sed -n '250,312p'  # F6, F7
```

Probe sources: `/tmp/rev139/fidelity.lean`, `/tmp/rev139/strength.lean` (ephemeral — the two
statements that matter are reproduced inline in F1/F2/F4 above).
