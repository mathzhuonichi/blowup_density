# Review — lane 083, R42 item 1f (`pressure_gradient` for `p_ε = π + P_ε`)

Reviewer: opus (lane-review). Date: 2026-09-13.
Branch `erenup/083-R42-pressure-gradient`, commit `10b7918`, worktree
`.claude/worktrees/083-R42-pressure-gradient`.
Files reviewed: `formalization/NSFormalization/Section4/R42/PressureGradient.lean`,
`research/R42/ATTEMPTS_PRESSURE.md`, `research/R42/axioms_pressure.lean`.

## Verdict: **ACCEPT-WITH-NOTES**

The Lean is correct, non-vacuous, axiom-clean, and — verified end to end — directly
consumable from `InsertionFamilyAPI`. The notes are one inaccurate negative example
in `ATTEMPTS_PRESSURE.md` (with a 3-line simplification it hides) and three
informational items for the assembly lane. Nothing blocks the merge.

---

## Findings

### 1. `ATTEMPTS_PRESSURE.md` "failed approach 4" is not reproducible — *minor (honesty)*

**Location** `research/R42/ATTEMPTS_PRESSURE.md`, "Failed / adjusted approaches", item 4;
the code it justifies is `PressureGradient.lean:181-186`.

**Claim recorded**: with `heq : p = fun z => π z + (p z − π z)`, `rw [heq]` "loops:
`rw` replaces every `p`, including the `p` inside the RHS", hence the detour through
the reversed `heq` + `hgoal` + `rw [← hgoal]`.

**What actually happens**: `rw` abstracts occurrences in the *goal* only and substitutes
the RHS once; the `p` inside the RHS is not re-rewritten. I reproduced the corollary
verbatim with the "failing" orientation and it compiles with no error and no warning
(`/tmp/r42rev/snag4.lean`, exit 0). The tail of the proof shrinks from five lines

```lean
  have heq : (fun z : ℝ × Space => π z + (p z - π z)) = p := by funext z; ring
  have hgoal : (fun x : Space => pressureGradient (fun z : ℝ × Space => π z + (p z - π z)) t x)
      = (fun x : Space => pressureGradient p t x) := by funext x; rw [heq]
  rw [← hgoal]
  exact hadd
```

to two

```lean
  have heq : p = (fun z : ℝ × Space => π z + (p z - π z)) := by funext z; ring
  rw [heq]
  exact hadd
```

I also tested the plausible alternative cause — a pointwise `heq : ∀ z, p z = π z + (p z − π z)`
driven by `simp only` — and that does not loop either; it reports `simp made no progress`.

**Fix** (author, follow-up commit or next R42 lane): correct item 4 of
`ATTEMPTS_PRESSURE.md` to say the orientation is *not* the problem, and either
shorten `memLp_pressureGradient_of_difference_support` as above or record why the
longer form was kept. Rule 4 of `CLAUDE.md` makes the negative examples load-bearing
for later lanes; a wrong one costs more than no entry.

Snags 1, 2, 3 and 5 of the same file **are** real — each reproduced:

* **1** `ContDiff.continuous_fderiv`/`ContDiff.differentiable` take `n ≠ 0`, not `1 ≤ n`.
  `le_top` gives `Application type mismatch: le_top has type ?m ≤ ⊤ but is expected to
  have type ∞ ≠ 0`. Signatures confirmed by `#check`.
* **2** without `(f := fun x : Space => P (t, x))` the elaborator unifies `f := P`,
  `x := (t,y)`: `hy has type y ∈ (tsupport fun x => P (t, x))ᶜ but is expected to have
  type (t, y) ∉ tsupport P`.
* **3** `rw [hz.fderiv_eq, fderiv_const]` fails: `Did not find an occurrence of the
  pattern fderiv ?m (Function.const ?m ?c) in the target fderiv ℝ (fun x => 0) x = 0`.

### 2. Statement fidelity — *no defect*

Printed with `pp.fullNames`, the `ClassicalSolutionR.pressure_gradient` field at a
fixed `t` is

```
MeasureTheory.MemLp (fun x => NavierStokes.ProblemStatement.pressureGradient self.pressure t x) 2
  MeasureTheory.MeasureSpace.volume
```

and the corollary's conclusion is the same term with `self.pressure` replaced by the
bound `p`. Token-identical. Confirmed constructively: `w.pressure_gradient t ht`
closes a goal written out by hand in that exact shape (test 4 of `/tmp/r42rev/fidelity.lean`).

`pressureGradient` is the **vendor's** definition, not a local mirror —
`#print` gives `NavierStokes.ProblemStatement.pressureGradient = fun p t x =>
∑ i, (fderiv ℝ (fun y => p (t, y)) x) (coordinateVector i) • coordinateVector i`,
i.e. `vendor/NavierStokesAndEuler/NavierStokes/ProblemStatement.lean:71` verbatim.
`Space` is `NavierStokes.ProblemStatement.Space` throughout, and `2`/`volume` match.

`Ico 0 T` is the right interval (the field quantifies over `Ico 0 T`), and `t = 0` is
genuinely covered: `contDiff_slice` composes the `ContDiffOn` on the closed-at-zero
slab with the affine inclusion `x ↦ (t,x)` whose image lies in the slab, so the slice
is `ContDiff` on `univ` — the same argument already accepted as
`D01/DatumToJets.lean:378 contDiff_slice_scalar` (byte-identical proof).

Lemma 1 is **not** satisfiable by a wrong implementation. `HasCompactSupport` really
does follow: `tsupport` of the slice is closed and inside `ball x₀ r ⊆ closedBall x₀ r`,
which is compact in `EuclideanSpace ℝ (Fin 3)` (`isCompact_closedBall` applies —
proper space), and `HasCompactSupport.of_support_subset_isCompact` only needs
`IsCompact K` + `support f ⊆ K` in an `R1Space`. The support transfer
`support (∇ slice) ⊆ tsupport slice` is proved honestly via
`Filter.EventuallyEq.fderiv_eq` against the locally-zero slice, not by a
degenerate/vacuous route. The hypotheses are jointly satisfiable non-trivially
(any bump), so the lemma is not vacuous.

### 3. Consumability from `InsertionFamilyAPI` — *verified, ~10 lines of glue* (informational)

I wrote and compiled the full assembly step (`/tmp/r42rev/consume.lean`, 0 errors):
from `F : InsertionFamilyAPI ν Pk`, `ε ∈ Ioc 0 F.ε₀`, `0 < S < F.scaling.correction.T`,
it produces `∀ t ∈ Ico 0 S, MemLp (pressureGradient (F.pressure ε) t ·) 2 volume`
with no extra hypotheses. Instantiate the lemma's `T` at `F.scaling.correction.T`
(not at `S`); then

* `hp` = `F.pressure_smooth ε hε` — **verbatim**, no restriction
  (`InsertionFamily.lean:200`, already on `Ico 0 T`).
* `hsupp` = `F.pressureDifference_support ε hε t htT` — **verbatim**
  (`InsertionFamily.lean:255`).
* `ht` — widen `t ∈ Ico 0 S` to `Ico 0 T` (and to `Ico 0 (T+δ)`) by
  `Ico_subset_Ico_right`, using `margin_pos : 0 < δ` (`Correction.lean:207`). 2 lines.
* `hπ` — **not** one line: three.
  `F.reference.pressure_smooth` is on `Ico 0 (T+δ)` and is about `reference.pressure`,
  so: `rw [F.reference_pressure] at this` then
  `this.mono (Set.prod_mono (Ico_subset_Ico_right (by linarith)) subset_rfl)`.
* `h1` — two lines: `F.reference.pressure_gradient t htTδ` then `rwa [F.reference_pressure]`.

**Trap for the assembly lane** (severity: informational, would cost a session if hit):
the `π` smoothness must come from `InsertionFamilyAPI.reference.pressure_smooth`
(the `Data.ClassicalSolutionR` field, on the **half-open** `Ico 0 (T+δ)`), *not* from
`CorrectionAPI.reference_pressure_smooth`, which lives on the **open** slab
`Ioo 0 (T+δ)` (`Correction.lean:226`, flagged in `InsertionFamily.lean:53-54`) and
therefore cannot reach `t = 0`, exactly the point `Ico` needs.

Note the lemmas are stated about bare functions, not about either copy of the
structure, so the same corollary serves `Contracts.V1.Data.ClassicalSolutionR` (used
in the test above) and `A02.ClassicalSolutionR` with no transport.

### 4. The inlined `contDiff_slice` — *justified; minor naming note*

`R42.contDiff_slice` (`:69`) is a byte-identical copy of `D01.contDiff_slice_scalar`
(`DatumToJets.lean:378`). Measured import closures (local `NSFormalization.*` +
vendor `NavierStokes.*` modules, transitive):

| module | local modules in closure |
|---|---|
| `Section4.A02.SolutionClass` | 50 |
| `Section4.R42.PressureGradient` (as committed) | 51 |
| `Section4.D01.DatumToJets` | 597 |

So `import NSFormalization.Section4.D01.DatumToJets` would take **this module** from
51 to 599 local modules (**+548**), on top of a much larger Mathlib surface — an
11× blowup to reuse a 10-line helper. Inlining is right, and it follows the repo's
own precedent: `A02/SolutionClass.lean:44-50` refuses the D01 import for exactly this
reason, and `D01/DivergenceTime.lean` (lane 074) applies the same policy.

For completeness: at the *assembly* level the marginal cost is small — the R42 siblings
already import `D01.ForceClass` (598-module closure), and `DatumToJets` adds only
**2** modules on top of `R42.CorrectionPath`'s closure (`A05.SmoothJets`,
`DatumToJets`). So if the assembly module ends up importing D01 anyway, a later lane
could drop the copy. Not worth a change now (rule 1).

Two cosmetic notes, no action required:
* `R42.contDiff_slice` is the **scalar** lemma but carries D01's **vector** name
  (`D01.contDiff_slice` is `v : ℝ × Space → Space`). A module that opens both
  namespaces gets an ambiguous `contDiff_slice`. `contDiff_slice_scalar` would have
  matched D01.
* The docstring (`:29`) says lane 074's `DivergenceTime.lean` carries "the same
  inlined slice-smoothness argument". It carries the same *import policy* and its own
  local `fderiv_spatial_slice`/`deriv_time_slice` helpers, but no `contDiff_slice`
  copy. Harmless imprecision.

### 5. Consistency / hygiene — *clean*

* Single import `NSFormalization.Section4.A02.SolutionClass` (+ Mathlib transitively). ✓
* No `sorry` / `admit` / `axiom` / `native_decide` / `maxHeartbeats`. ✓
* No `Contracts/V1/*` or `Tests/*` touched; the commit adds three new files only. ✓
* No contract registered by this lane, so `verification/contracts.json` and
  `work_items.json` are untouched — `check_work_queue.py` stays consistent. ✓

---

## Commands run and results

All from the lane worktree, after `bash scripts/lean-install.sh` (idempotent; ended
`== OK`, replaying every registered `Tests.*` with "standard logical axioms only"),
`. scripts/lean-env.sh`, `export LEAN_NUM_THREADS=6`, one lake process at a time.

| command | result |
|---|---|
| `cd verification && lake build NSFormalization.Section4.R42.PressureGradient` | `Build completed successfully (8815 jobs).` (only pre-existing `Paper3/RealVectorPositiveDensity.lean:29` unused-variable warning) |
| `lake env lean ../formalization/NSFormalization/Section4/R42/PressureGradient.lean` | **no output**, exit 0 |
| `lake env lean ../research/R42/axioms_pressure.lean` | 4 declarations, each `[propext, Classical.choice, Quot.sound]`: `contDiff_slice`, `memLp_pressureGradient_of_compact`, `memLp_pressureGradient_add`, `memLp_pressureGradient_of_difference_support` |
| `grep -nE 'sorry\|admit\|axiom\|native_decide\|maxHeartbeats' …/PressureGradient.lean` | no match (exit 1) |
| `make check` | exit 0 — architecture checks, `test_contract_policy.py` 13/13 OK, `check_work_queue.py` "30 work items: ownership, contract registration and task cards consistent." |
| `lake env lean /tmp/r42rev/fidelity.lean` | field type and corollary printed with `pp.fullNames`; the hand-written field goal is closed by `w.pressure_gradient t ht` (only error: my deliberately wrong `D01.contDiff_slice_scalar` full name) |
| `lake env lean /tmp/r42rev/consume.lean` | **0 errors** — end-to-end `pressure_gradient` clause derived from `InsertionFamilyAPI` (see finding 3) |
| `lake env lean /tmp/r42rev/snags.lean` | signatures of the 6 cited Mathlib lemmas; `le_top` negative test fails exactly as recorded (snag 1) |
| `lake env lean /tmp/r42rev/snag24.lean`, `snag3.lean`, `snag4.lean`, `snag4b.lean` | snags 2 and 3 reproduce exactly; snag 4 does **not** reproduce (finding 1) |

Scratch test files were written under `/tmp/r42rev/`, outside the repo; no file in the
worktree was modified other than this review.

---

## Where R42 item 1 stands

Item 1 of `research/R42/LIFESPAN_SPLIT.md` — `sol_on_shorter`, i.e. an inhabitant of
`Data.ClassicalSolutionR ν a g_ε S` for every `0 < S < family.T`, which is what
`maximalLifespanR`'s `⨆ over Nonempty` needs — now has all of its clauses except one.
`horizon_pos`, `velocity_smooth`, `pressure_smooth`, `initial`, `divergence`,
`momentum` are guard shuffling off `InsertionFamilyAPI` (`Ico 0 S ⊆ Ico 0 T`,
`Ioo 0 S ⊆ Ioo 0 T`); `sobolev`'s pieces 1b, 1c are registered R42 lemmas, 1d is
`reference.sobolev`, 1e-ii is D01's `isSobolevDatum_add`/`isSobolevPath_add`; and this
lane closes **1f** `pressure_gradient`, with the assembly glue measured at about ten
mechanical lines (finding 3) and already compiled once against the real contract.

The single remaining residual for item 1 is **1e-i** (M): time-continuity on `Ico 0 S`
of the correction's Sobolev datum path — the cutoff-in-time + `D01.contDiff_angularPath`
+ `isSobolevDatum_unique` route sketched at `LIFESPAN_SPLIT.md:120-131`, with the
`Ico 0 S` vs `Ici 0` domain bookkeeping as the actual work. Beyond item 1, the R42
assembly still owes item 2a (pointwise blow-up ⟹ `essSup` lower bound via
`IsOpenPosMeasure`) and the two contract-shape residuals recorded at
`LIFESPAN_SPLIT.md:228-234` (the `RegularThrough ν a g (T+δ)` strengthening for #6,
and `hg : MemForceR g` for item d), which are V2 questions for the owner, not proofs.
