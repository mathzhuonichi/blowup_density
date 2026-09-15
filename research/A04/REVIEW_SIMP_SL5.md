# REVIEW — lane 118 (SIMP-A04-nonlinear: simplifier + tester pass over the SL5 cluster)

Reviewer: opus, 2026-09-13.  Worktree `.claude/worktrees/118-SIMP-A04-nonlinear`, HEAD `2d05159`,
base = `git merge-base HEAD origin/erenup/integration` = `728ac3e` (integration has moved on; all
diffs below are against `728ac3e`).  Light/strict review, Lean run by the reviewer.

## Verdict: **ACCEPT-WITH-NOTES**

The lane does exactly what it claims: 12 dead `open`/`open scoped` targets removed (−2 lines), every
exported statement byte-identical, all conformance/axiom probes still clean, and the committed
negative-check file compiles silently with **two genuinely machine-checked refutations** (the `hdiv`
counterexample is a real one, not a strawman).  Nothing in the shipped Lean is wrong.

The notes are all in the accompanying prose:

* finding 5 (**medium, non-blocking**) — the ATTEMPTS says a refutation of the `hdiff`-dropped
  statement "needs a nowhere-differentiable field" and is out of scope.  That is too strong: the
  weakened statement **is false**, and an explicit witness that is smooth off the single plane
  `{x₀ = 0}` is given below, together with a cheap proof route through the existing `rfl` bridge.
  `hdiff` should be recorded as *mathematically load-bearing (witness known, not yet
  machine-checked)*, not merely "could not prove without";
* findings 6–7 (**low**) — two file:line citations in the MAINT section are off/misattributed.

---

## 1. Commands and results (all `lake` from `WT/verification`, `LEAN_NUM_THREADS=6`, one at a time)

| # | command | result |
|---|---|---|
| 1 | `git diff 728ac3e HEAD -- formalization/` + `grep -E '^[+-]' \| grep -vE '^[+-]\s*(open \|  \()'` | **empty** — every changed line in `formalization/` is an `open`/`open scoped` line (or its continuation) |
| 2 | `git diff --numstat 728ac3e HEAD -- formalization/` | `2/3`, `3/4`, `2/2`, `1/1` → **+8 / −10 = −2 lines**, matching the claim; `AdvectionDivergence.lean` absent from the diff |
| 3 | `lake build NSFormalization.Section4.A04.NonlinearBound` | `Build completed successfully (9903 jobs).`, exit 0 (only pre-existing `Source.*` / `Paper3/SobolevDirectionalDerivative.lean:103` warnings; none on the five modules) |
| 4 | `lake env lean` on each of the five SL5 modules | all **silent**, exit 0 |
| 5 | signature probe `/tmp/rev118/sig.lean` (26 exported decls, `pp.fullNames true`) run **before** (root worktree = `728ac3e` sources) and **after** (lane worktree), then `diff` | `181` lines each, **IDENTICAL** — see §2 |
| 6 | `lake env lean ../research/A04/negative_simp_sl5.lean` | exit 0, **0 bytes** of output |
| 7 | `lake env lean ../research/A04/axioms_sl5{,a,c,_columns}.lean` | exit 0; `7 / 3 / 9 / 7` `depends on axioms` lines; the *only* distinct axiom list over all four files is `[propext, Classical.choice, Quot.sound]` (`cat axioms_*.out \| tr -d '\n' \| grep -o 'depends on axioms: \[[^]]*\]' \| sort -u` → one line); `axioms_sl5c`'s conformance `example` (feeding `inner_advection_bound_slice` into `inner_energy_assembly`'s `hnl` slot) still elaborates |
| 8 | `make check` (repo root) | exit 0 — `Ran 13 tests … OK`; `30 work items: ownership, contract registration and task cards consistent.` |
| 9 | `make test` (repo root; **not** `verification/`, see finding 4) | exit 0 — `[10070/10070] Replayed Tests.InsertionLifespanV2`, every `Tests.*` "checked; standard logical axioms only" |
| 10 | `AdvectionDivergence` "NEEDED" probes (`/tmp/rev118/adv_{noset,nocontdiff}.lean`) | reproduced the lane's two errors verbatim, see §3 |
| 11 | route-(ii) `exact?` probe reproduced (`/tmp/rev118/rii_c.lean`) | ``error: `exact?` could not close the goal. Try `apply?` to see partial suggestions.`` — matches the pasted transcript |

`git status --porcelain` in the worktree is empty; the branch is a single commit touching exactly the
6 claimed files.  `grep -n 'sorry\|admit\|axiom\|native_decide' research/A04/negative_simp_sl5.lean`
is empty.

---

## 2. Finding 1 — diff discipline: PASS, and strengthened (severity: none, evidence added)

A grep over the changed lines (command 1) confirms the "only `open` lines" claim.  But that grep does
**not** by itself establish "statements unchanged": removing an `open` can in principle re-resolve a
bare identifier to a *different* constant that happens to typecheck (cf. `logs/LESSONS.md`
2026-09-14, `MomentumSlice` exporting `D01.MemForceR` instead of `A02.MemForceR`, and the
`Ambiguous term` entry).  So I ran the stronger check:

```
/tmp/rev118/sig.lean :  #check @X  for all 26 exported declarations of the five modules
                        (3 in `namespace NSFormalization.Paper3`, 23 in `…Section4.A04`),
                        set_option pp.fullNames true
before: run in /data_8T/ping/blowup_density        (root = integration; `git diff 728ac3e f4f366d`
                                                    over the five files is EMPTY, so root carries the
                                                    pre-lane sources, and its `formalization/.lake`
                                                    is a *separate* build dir — md5 of
                                                    `NonlinearBound.olean` differs from the
                                                    worktree's, so this is a real before/after)
after:  run in the lane worktree
diff /tmp/rev118/sig_before.txt /tmp/rev118/sig_after.txt   →   IDENTICAL   (181 lines each)
```

So all 26 exported types elaborate to the *same terms with the same fully-qualified constants* before
and after.  Together with the axiom probes (command 7) this closes the "byte-identical statements"
claim properly.

Manual confirmation of the 12 removed targets (why each was dead):

| module | removed | why it was dead |
|---|---|---|
| `NonlinearBound` | `open scoped ContDiff ENNReal` (whole line), `MemHInfty`, `FourierData` | `ContDiff`/`ℝ≥0∞` notation never typed; `MemHInfty` occurs only in the docstrings at `:41,43,180,181`; `FourierData` 0 occurrences |
| `NonlinearColumns` | `Set`, `MeasureTheory`, `open scoped ENNReal` (whole line), `columnsSobolevENorm`, `angularDirectionalDerivativeReal` | no `Set.`/`MeasureTheory` identifier; the 4 `ENNReal` hits are fully-qualified `ENNReal.mul_ne_top` / `ENNReal.toReal_nonneg` (need no scoped open), and no `ℝ≥0∞` is typed; `columnsSobolevENorm` (the A03 *def*) appears only in docstrings and inside the *different* identifiers `le_columnsSobolevENorm` (still opened) and the lane-109 alias `columnsSobolevENorm_toReal_sq_eq_sum` (declared locally at `:134`); `angularDirectionalDerivativeReal` only in the `:102` docstring |
| `NonlinearDatum` | `MeasureTheory`, `ENNReal` | 0 occurrences each |
| `NonlinearPairing` | `ENNReal` | 0 occurrences |

---

## 3. Finding 2 — compiles / axioms: PASS (severity: none)

Commands 3, 4, 6, 7 above.  Importer check: `grep -rn "import NSFormalization.Section4.A04.(Nonlinear…|AdvectionDivergence)"`
over `formalization/ verification/ research/` finds **no importer outside the cluster itself**
(`NonlinearBound ← NonlinearDatum ← {NonlinearColumns, AdvectionDivergence}`, plus `NonlinearPairing`).
In particular `HighEnergy.lean` does *not* import them — the only place the two meet is
`research/A04/axioms_sl5c.lean`, which imports both and whose conformance `example` still
type-checks (command 7).

The lane's "NEEDED, so `AdvectionDivergence` left untouched" determinations reproduce exactly:

```
/tmp/rev118/adv_noset.lean:92:55: error: Function expected at
  Ico
but this term has type
  ?m.1
/tmp/rev118/adv_nocontdiff.lean:97:13: error: type expected, got
  (ContDiff ℝ : WithTop ℕ∞ → (?m.39 → ?m.42) → Prop)
/tmp/rev118/adv_nocontdiff.lean:97:24: error: expected token
```

## 4. Finding 3 — `make test` does not cover this cluster (severity: low, informational)

`grep -rn "Section4.A04" verification/` is **empty**: no `Bindings/` or `Tests/` module reaches the
SL5 cluster (no A04 contract is registered yet).  So command 9 passing is *not* evidence about these
five files; the compile evidence is command 3 (`lake build …NonlinearBound`, 9903 jobs) plus the five
`lake env lean` runs and the four axioms probes.  Worth remembering when the lead reads the gate log.
(Also: the ATTEMPTS "Commands run" table writes `cd verification && make test` — the `test` target
lives in the **root** Makefile (`lake -d verification test`); from `verification/` it is
`make: *** No rule to make target 'test'.  Stop.`  Cosmetic, but it means that row was not run as
written.)

---

## 5. Finding 4 — quality of the negative checks (severity: low; verdict: the two refutations are genuine)

### 4a. `hdiv` dropped from `advection_eq_sum_partialDeriv_outerColumn` — **genuine counterexample**

The weakened statement in `negative_simp_sl5.lean` is the original

```
theorem advection_eq_sum_partialDeriv_outerColumn {u : SpaceTimeField} {t : ℝ}
    (hdiff : ∀ x, DifferentiableAt ℝ (fun y => u (t, y)) x)
    (hdiv  : ∀ x, spatialDivergence u t x = 0) :
    (fun x => advection u t x) = fun x => ∑ j : Fin 3, partialDeriv j (outerColumn … j) x
```

with **exactly `hdiv` removed**, the same conclusion, `hdiff` kept, `u`/`t` turned from implicit into
explicit `∀`-binders, under `set_option autoImplicit false in` — i.e. route (a) of the
`logs/LESSONS.md` 2026-09-14 entry, not the discredited "omit the argument and re-apply" route.  The
refutation is a real `¬`-proof closed by the kernel (`u(t,x) = x`, `∇·u = 3`, the two sides differ by
`3 • e₀`), no `sorry`.  **`hdiv` is proven load-bearing.**

### 4b. The two ℓ² factors — genuine, but a different kind of check

`sum_inner_le_sqrt_mul_sqrt` / `abs_sum_inner_le_sqrt_mul_sqrt` have no hypotheses beyond the
typeclasses, so what is tested is a **strengthened conclusion** (RHS `√(∑‖a‖²)·√(∑‖b‖²)` → `√(∑‖a‖²)`),
not a dropped hypothesis.  The ATTEMPTS table labels this correctly ("hypothesis dropped / conclusion
strengthened").  The refutations are machine-checked (`E = ℝ`, `ι = Unit`, `a ≡ 1`, `b ≡ 2`: `2 ≤ 1`
is false) and are sound — note the weakened statements quantify over `{E : Type}` rather than
`Type*`, which makes them *weaker* than the originals, so refuting them is more than enough.  Their
evidential value is low (the second factor is obviously not droppable), but nothing is overstated.

### 4c. The witness-heavy ones — honestly labelled, but the evidence is near-zero

`exact?` timing out at 200000 heartbeats (`isDefEq` / `whnf`) and `simp` reporting "made no progress"
are **not** evidence that a hypothesis is necessary; they are evidence that the goal is big.  The
ATTEMPTS does label these "could not prove without" and never claims more, and it pastes the error
text into the md rather than relying on the (now-deleted) `/tmp` probes — both correct per
`logs/LESSONS.md`.  I reproduced the `hdiff` transcript verbatim (command 11), so the transcripts are
real.  My only ask is the relabelling in finding 5.

Reviewer's analysis of *why* these three are hard, which sharpens the MAINT entries:

* `advection_slice_datum_eq`, `hN` dropped — the weakened statement has the shape `∀ N, N = c` with
  `N` a free variable of `RealVectorSobolev (m:ℝ)` that nothing else constrains.  So it is false as
  soon as (i) some `ClassicalSolutionR ν a f T` is inhabited (the zero solution would do) and
  (ii) `RealVectorSobolev (m:ℝ)` is shown non-subsingleton.  `grep -rn "ClassicalSolutionR"` finds
  **no inhabitant anywhere in the tree**, which is the real obstruction — not any doubt about the
  falsity.  Recommended MAINT item: a `ClassicalSolutionR` zero-solution instance; it would unlock
  this and several other non-vacuity checks.
* `inner_advection_bound`, `hN` dropped — here a degenerate witness genuinely *cannot* refute:
  with the zero field, `hG` + `isSobolevDatum_unique` force `G = 0`, hence `−⟪G,N⟫ = 0 ≤ RHS` for
  every `N` and the weakened statement holds.  A refutation needs a field with a **non-zero** datum,
  i.e. exactly the Schwartz/Gaussian witness the lane declines to build.  The lane's judgement is
  correct here.

### 4d. Non-vacuity

The closing `example` (constant field `u ≡ e₀`, `‖e₀‖ = 1 ≠ 0`, `hdiff` by `differentiableAt_const`,
`hdiv` by `fderiv_const`) is a real non-vacuity witness for `advection_eq_sum_partialDeriv_outerColumn`.
The honest caveat about the datum-carrier exports (zero field inhabits the classes but is the vacuous
case) is stated in the ATTEMPTS and is accurate.

---

## 6. Finding 5 (MEDIUM, non-blocking) — `hdiff` **is** refutable; the "nowhere-differentiable field" claim is too strong

ATTEMPTS says: *"a concrete refutation needs a nowhere-differentiable field"* and files `hdiff` under
"could not prove without".  The weakened statement is in fact **false**, and the witness need only
fail to be differentiable on one plane:

```
ε : ℝ → ℝ,  ε r = if 0 ≤ r then 1 else -1                       -- so ε² ≡ 1
U : Space → Space,  U y = ![y 1, y 0, 1]                        -- affine, div-free
u : SpaceTimeField,  u (t, y) = ε (y 0) • U y
```

* **`hdiv` holds at every `x`.**  On the open half-spaces `{y 0 > 0}` / `{y 0 < 0}` we have
  `u (t, ·) =ᶠ ±U`, so `fderiv u = ±fderiv U` and `spatialDivergence = ±(∂₀U₀ + ∂₁U₁ + ∂₂U₂) = 0`.
  On the plane `{y 0 = 0}`, `u` is **discontinuous** (the jump is `2 U x ≠ 0`, because `U`'s third
  component is the constant `1`), hence not differentiable, hence `fderiv = 0` by Mathlib's junk
  convention (`spatialDerivative` is literally `fderiv`, `ProblemStatement.lean:59`) and
  `spatialDivergence = 0` there too.
* **LHS `= 0` at `x = e₁`.**  `advection u t x = spatialDerivative u t x (u (t,x))`
  (`ProblemStatement.lean:63`) and `x 0 = 0`, so the junk `fderiv = 0` gives `advection u t e₁ = 0`.
* **RHS `= e₁ ≠ 0` at `x = e₁`.**  `outerColumn z z j = fun y => (z y j) • z y` with `z = ε•U` is
  `ε² (U_j • U) = U_j • U` — a *polynomial* field, the `ε` cancels.  Hence
  `∑ⱼ ∂ⱼ (outerColumn z z j) = ∑ⱼ ∂ⱼ (U_j U) = (U·∇)U + (∇·U) U = (y 0, y 1, 0)`, which at
  `x = e₁ = (0,1,0)` is `(0,1,0) ≠ 0`.

So `hdiff` is load-bearing for the same "junk-`fderiv`" reason `REVIEW_SL5A.md` gives — but the
counterexample is cheap to *state*; only its Lean proof costs anything.  A cheap proof route exists
and is worth recording, because it avoids all coordinate-level `fderiv` computation of the quadratic
columns:

1. the columns of `u` and of `U` are equal as functions (`funext` + `ε² = 1`), so the RHS for `u`
   equals the RHS for the smooth field `U`;
2. `A04.convectionDivergence_eq_sum_partialDeriv_outerColumn` is `rfl` and **unconditional**, so that
   RHS *is* `convectionDivergence U t x`;
3. `A01.convectionDivergence_eq_advection_add_smul_div` applies to `U` (smooth) and, with `∇·U = 0`,
   reduces it to `advection U t x = fderiv U x (U x) = A (U x)` with `A` the linear part — one CLM
   application, no product rule.

Remaining Lean cost: `Filter.EventuallyEq.fderiv_eq` on the two half-spaces, one discontinuity
argument on the plane, and `fderiv` of an affine map.  Estimated 80–120 lines — real work, correctly
out of scope for a SIMP lane, but it should be filed as a MAINT/negative-check item rather than
described as needing "a nowhere-differentiable field".  **Requested (non-blocking) edit:** in
`ATTEMPTS_SIMP.md` change the `hdiff` verdict from "could not prove without" to "mathematically
false — witness above; machine-checked refutation deferred", and add the witness.

---

## 7. Finding 6 (LOW) — MAINT list: one off-by-one citation

All five `NonlinearPairing.lean` citations are exact (`:62`, `:92`, `:108`, `:163`, `:176`, verified
by grep), as is `RealPairing.lean:168` (`inner_loweringMid_pairing`).  One is off by one:

| claimed | actual |
|---|---|
| `outerSobolevENorm_toReal_sq_eq_sum` — `NonlinearColumns.lean:140` | `NonlinearColumns.lean:139` (`:137–138` is its docstring) |

## 8. Finding 7 (LOW) — the deferred docstring nit is misattributed (and still open elsewhere)

ATTEMPTS says *"`REVIEW_SL5_COLUMNS.md` #4 flags the `NonlinearColumns.lean:9` docstring citing
`HighEnergy.lean:101,106` (actual `:100`/`:136`)"*.  That was true when the review was written, but
`NonlinearColumns.lean:9` **already says `HighEnergy.lean:100,136`** (fixed in the SL5-columns review
pass), as does `NonlinearBound.lean:10`.  The stale citation now lives at

* `formalization/NSFormalization/Section4/A04/NonlinearPairing.lean:7` — `HighEnergy.lean:101,106`
  (actual: `inner_energy_assembly` `:100`, `inner_energy_Rhigh` `:136`), and
* `research/A04/SL5_SPLIT.md:4` (the source of the copy).

i.e. in a file this lane *did* touch.  Fixing it is a docstring-only edit that changes no statement,
so it would have been in scope; leaving it is also fine, but the ATTEMPTS pointer should be corrected
so the next lane looks in the right file.

## 9. Finding 8 — MAINT proposals are sound: no import cycles, no name collisions (severity: none)

* **`inner_loweringMid_transfer` / `inner_lowering_transfer_complex` / `real_inner_lowering_transfer`
  (namespace `Paper3`) and `sum_real_inner_angularDirectionalDerivative{,Real}` (namespace `A04`)
  → `Section4/A04/RealPairing.lean`.**  `NonlinearPairing.lean`'s *only* import is
  `NSFormalization.Section4.A04.RealPairing`, so the move goes strictly **up** the chain: no cycle is
  possible, and every constant those five proofs mention is by construction already in
  `RealPairing`'s import closure.  ✔
* **`outerSobolevENorm_toReal_sq_eq_sum` → `Section4/A03/OuterTameProduct.lean`.**  That file already
  contains `outerColumn` (`:68`), `columnsSobolevENorm` (`:75`), `outerSobolevENorm` (`:79`) and the
  source theorem `columnsSobolevENorm_toReal_sq_eq_sum` (`:97`); A03 is upstream of A04, so again no
  cycle.  ✔  One practical note: the only consumer outside `NonlinearColumns.lean` is
  `research/A04/axioms_sl5_columns.lean:13`, which resolves the name through `open …A04`, so the move
  must leave an `A04` alias behind (the lane-109 pattern already used two lines above) or the probe
  must be updated in the same commit.
* **Collisions:** `grep -rn "^(theorem|lemma|alias|def) <name>"` over all of `formalization/` returns
  exactly one hit for each of the six names — the declaration being proposed for the move.  No
  existing `A03.outerSobolevENorm_toReal_sq_eq_sum`, no existing `Paper3.sum_real_inner_*`.  ✔

---

## 10. Summary of hypothesis status (what this lane actually established)

| export | hypothesis / factor | status after this lane |
|---|---|---|
| `advection_eq_sum_partialDeriv_outerColumn` | `hdiv` | **proven load-bearing** (machine-checked counterexample `u(t,x)=x`) |
| `advection_eq_sum_partialDeriv_outerColumn` | `hdiff` | **mathematically load-bearing** — statement false, witness `ε(y₀)•![y₁,y₀,1]` given in §6; refutation not yet machine-checked (lane recorded it only as "could not prove without") |
| `sum_inner_le_sqrt_mul_sqrt`, `abs_…` | 2nd ℓ² factor | **proven necessary** (machine-checked, `a≡1`, `b≡2`) |
| `advection_slice_datum_eq` | `hN` | "could not prove without"; falsity reduces to a `ClassicalSolutionR` inhabitant + non-subsingleton carrier (§4c) |
| `inner_advection_bound` | `hN` | "could not prove without"; genuinely needs a non-zero-datum field — degenerate witnesses provably cannot refute (§4c) |

## 11. Recommendation

**ACCEPT-WITH-NOTES** — mergeable as is.  Requested follow-ups, none blocking:

1. (finding 5) relabel the `hdiff` verdict in `ATTEMPTS_SIMP.md` and record the §6 witness + proof
   route as a negative-check MAINT item;
2. (findings 6–7) fix the `:140` → `:139` citation and re-point the docstring nit at
   `NonlinearPairing.lean:7` / `SL5_SPLIT.md:4`;
3. (finding 4c) file "inhabit `ClassicalSolutionR` with the zero solution" as a MAINT item — it is
   the shared blocker for several deferred negative checks;
4. (finding 3, cosmetic) the ATTEMPTS command table should say `make test` from the repo root.
