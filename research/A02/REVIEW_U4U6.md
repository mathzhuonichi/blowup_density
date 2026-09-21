# A02 units U4 + U6 review — restriction, congruence, pressure gauge, lifespan order theory

Lane `032-A02-restrict-order`, worktree HEAD `c257c21`
("[032-A02] Units U4 and U6: …"), branched off `erenup/integration`.
Read-only pass: nothing the lane committed was modified; the only file written
by this review is the present one.  Under review:

* `formalization/NSFormalization/Section4/A02/Restrict.lean` (404 lines, U4);
* `formalization/NSFormalization/Section4/A02/Order.lean` (163 lines, U6);
* `research/A02/AxiomsU4U6.lean` (axiom audit + conformance block);
* `research/A02/ATTEMPTS_U4U6.md` (the lane record).

`git status --short` in the worktree is empty; `git show --stat c257c21` touches
exactly those four files and nothing else.  `research/A02/Spec.lean` is
untouched and still elaborates.

## Verdict: **ACCEPT-WITH-NOTES**

The Lean is clean and, on the two points where a silent deviation would have
been fatal, it is *verifiably* clean rather than plausibly clean:

* all fifteen §0 restatements are **token-for-token** identical to
  `verification/Contracts/V1/Data.lean` (same binder names, same `Ico`/`Ioo`,
  same `ℝ≥0∞`, same structure fields in the same order), and, independently of
  the text, a field-by-field bridge `A02.ClassicalSolutionR ⇄
  Contracts.V1.Data.ClassicalSolutionR` typechecks in **both** directions with
  zero errors, and the nine non-structure objects are *definitionally* the
  contract's (`rfl` / `Iff.rfl`).  Finding-free.
* all eight claimed spec fields are discharged by a theorem whose type is the
  spec field's **verbatim** string, with no hypothesis beyond the explicit
  ⟪A01:LocalTheoryAPI.solution⟫ argument in `horizon_le_lifespan`.
  Finding-free.
* 25 declarations, every one on exactly `[propext, Classical.choice,
  Quot.sound]`; hygiene grep empty; `make check` green; both modules build with
  zero warnings of their own.

The three findings are all in the lane **record**, not in the code, and none
changes what was proved.  Finding 1 is the only substantive one: it
*overstates* the cost of the binding layer, and the lead is being asked in that
same paragraph to make an architectural decision on the strength of it.

## 1. Findings

### Finding 1 — **Medium (record only)** — `research/A02/ATTEMPTS_U4U6.md` §1, the `rfl`-bridge warning is wrong for four of the six `def`s

The paragraph headed **Negative / warning for the lead** says:

> For the six `def`s (`maximalLifespanR`, `RegularThrough`,
> `PressureGaugeEquivOn`, `initialClassR`, `MemForceR`, `IsSobolevPath`) a
> `rfl` bridge *is* available only once the two `ClassicalSolutionR`s are
> identified, which they are not — so those, too, need transport rather than
> `rfl`.

Four of those six do not mention `ClassicalSolutionR` at all, and their `rfl`
bridges are available **today**.  Checked in Lean (file 3 of §3 below, exit 0):

```lean
example : initialClassR = BlowupDensity.Contracts.V1.Data.initialClassR := rfl
example : ∀ f, MemForceR f ↔ …Data.MemForceR f := fun _ => Iff.rfl
example : ∀ I p q, PressureGaugeEquivOn I p q ↔ …Data.PressureGaugeEquivOn I p q := fun _ _ _ => Iff.rfl
example : ∀ s f G, IsSobolevPath s f G ↔ …Data.IsSobolevPath s f G := fun _ _ _ => Iff.rfl
```

all typecheck, as do the same for `IsSobolevDatum`, `MemHInfty`,
`IsSolenoidal`, `futureTimes`, `forceTimeMeasure`.  Only the two `def`s that
*quantify over the solution class* resist, exactly as the mechanism predicts —
and they do resist, confirmed by the deliberate-failure file (exit 1, two
errors, no more):

```
NegBridge.lean:7:15: error: Type mismatch … maximalLifespanR … = …Data.maximalLifespanR …
NegBridge.lean:9:17: error: Type mismatch … RegularThrough … ↔ …Data.RegularThrough …
```

**Why it matters.** The sentence is load-bearing for the lead's decision in the
next sentence ("worth the lead deciding whether `ClassicalSolutionR` should
move into a canonical local module … With that, all bridges become `rfl`").
As written it makes the duplication look six times more expensive than it is.
The real cost is: two conversion functions for the structure, plus an
`iSup`/`Nonempty` congruence step for `maximalLifespanR` and one `Iff` for
`RegularThrough`.  Everything else is already `rfl`.

**Fix.** Replace "the six `def`s (…)" with "the two `def`s that quantify over
the solution class (`maximalLifespanR`, `RegularThrough`)", and note that
`PressureGaugeEquivOn`, `initialClassR`, `MemForceR`, `IsSobolevPath`,
`IsSobolevDatum`, `MemHInfty` and `IsSolenoidal` already bridge by `rfl` /
`Iff.rfl`.  The architectural question to the lead stands on its own merits and
should be kept.

### Finding 2 — **Low (record only)** — stale line citations into `Restrict.lean`, uniformly +7

`ATTEMPTS_U4U6.md` cites `Restrict.lean` at four places and its size once.  All
five are off by the same amount, i.e. the file grew by seven lines after the
record was written:

| record says | actual |
|---|---|
| "`Restrict.lean` (397 lines)" | 404 |
| `ClassicalSolutionR.congr` (`Restrict.lean:281`) | 288 |
| `pressureGradient_sub_basepoint` (`Restrict.lean:336`) | 343 |
| `contDiffOn_basepoint` (`:345`) | 352 |
| `normalizePressure_gauge_invariant` (`:386`) | 393 |

For contrast, every `Order.lean` citation is exact: `horizon_le_lifespan` `:48`,
`horizon_le_lifespan_of_localSolution` `:56`,
`exists_horizon_gt_of_lt_lifespan` `:124`, `regularThrough_iff` `:135`,
`referenceLifespan` `:152`, and "163 lines".  So this is a one-file staleness,
not a habit.  **Fix.** Re-derive the five `Restrict.lean` numbers.

### Finding 3 — **Nit (record only)** — `ATTEMPTS_U4U6.md` §2's import-list sentence is narrower than the file's own docstring

§2 says `Restrict.lean`'s import list "is exactly `Contracts/V1/Data.lean`'s
(minus `Paper3.GridGeometry` and `Source.FourierConvention`…)".  It is also
minus the two `Mathlib` imports (`Analysis.SpecialFunctions.Pow.NNReal`,
`MeasureTheory.Integral.IntervalIntegral.Basic`).  `Restrict.lean`'s own §0
docstring states this correctly ("minus `Paper3.GridGeometry`,
`Source.FourierConvention` and the two `Mathlib` modules"), so only the record
needs the two extra words.

## 2. What was checked, and what it showed

### 2.1 Restatement fidelity — **clean**

The fifteen objects of `Restrict.lean` §0 were diffed against `Data.lean` with
doc comments stripped and whitespace collapsed, i.e. a genuine token compare
that preserves order:

| object | `Data.lean` | cited as | token compare |
|---|---|---|---|
| `SpatialField` | 99 | `:99` | identical |
| `SpaceTimeField` | 104 | `:104` | identical |
| `SpaceTimeScalar` | 108 | `:108` | identical |
| `futureTimes` | 113 | `:113` | identical |
| `forceTimeMeasure` | 118 | `:118` | identical |
| `IsSobolevDatum` | 160 | `:160` | identical |
| `IsSobolevPath` | 174 | `:174` | identical |
| `MemHInfty` | 495 | `:495` | identical |
| `IsSolenoidal` | 504 | `:504` | identical |
| `initialClassR` | 509 | `:509` | identical |
| `MemForceR` | 544 | `:544` | identical |
| `PressureGaugeEquivOn` | 589 | `:589` | identical |
| `ClassicalSolutionR` | 624 | `:624-648` | identical, all ten fields in order |
| `maximalLifespanR` | 657 | `:657` | identical |
| `RegularThrough` | 664 | `:664` | identical |

Every cited line number is correct.  The ten `ClassicalSolutionR` fields are in
`Data.lean`'s order with `Data.lean`'s names, binder names and doc comments:
`velocity`, `pressure`, `horizon_pos`, `velocity_smooth`, `pressure_smooth`,
`initial`, `divergence`, `momentum`, `sobolev`, `pressure_gradient`; the
`Ico 0 T` / `Ioo 0 T` split is preserved exactly (`momentum` on `Ioo`, the other
eight clauses on `Ico`), and `maximalLifespanR` is `ℝ≥0∞` with the same double
`iSup`.

Text is not proof, because name resolution could differ between
`BlowupDensity.Contracts.V1.Data` (which additionally has
`open NSFormalization.Source (angularFourier)`) and
`NSFormalization.Section4.A02`.  So the restatement was also checked
*semantically*, by building the bridge the lane's docstring promises:
`toContract` and `ofContract`, each written field-by-field with no coercion and
no tactic, both typecheck; and nine `rfl` / `Iff.rfl` equalities between the
two copies of the non-structure objects typecheck.  A single `Ico`↔`Ico`,
`ℝ`↔`ℝ≥0∞` or resolution difference in any field would have failed there.
**No finding.**  The lane's "Positive" claim in §1 of the record is confirmed:
the binding layer is unblocked.

### 2.2 Spec conformance — **clean**

The eight spec fields were extracted from `research/A02/Spec.lean` and compared
against the `example` types in `AxiomsU4U6.lean` after whitespace
normalization.  Seven are *string-identical*:

| spec field | `Spec.lean` | discharged by | type compare |
|---|---|---|---|
| `restrict` | 345-348 | `exists_restrict` | identical |
| `pressure_normalization` | 399-403 | `exists_pressure_normalization` | identical |
| `lifespan_le_iff` | 443-446 | `lifespan_le_iff` | identical |
| `lifespan_le_iff_no_extension` | 451-455 | `lifespan_le_iff_no_extension` | identical |
| `lifespan_ge_of_forall_shorter` | 463-466 | `lifespan_ge_of_forall_shorter` | identical |
| `regularThrough_iff` | 476-478 | `regularThrough_iff` | identical |
| `referenceLifespan` | 500-504 | `referenceLifespan` | identical |

The eighth, `horizon_le_lifespan` (`Spec.lean:372-375`), is the one that rests
on A01.  Its `example` takes two binders and nothing else:

* `(horizon : ℝ → SpatialField → SpaceTimeField → ℝ)` — the structure field
  `MaximalSolutionAPI.horizon`, verbatim;
* `(localSolution : …)` — ⟪A01:LocalTheoryAPI.solution⟫ (`Spec.lean:319-321`),
  verbatim, including `0 < ν → a ∈ initialClassR → MemForceR f →`;

and its conclusion is the spec field verbatim.  It is discharged by
`horizon_le_lifespan_of_localSolution localSolution`, applied to *nothing* else.
So the lane's "**A01 is not assumed anywhere**" is exact: the A01 dependency is
one explicit argument, not an ambient hypothesis, and no second A01 field
(`horizonLowerBound`, `uniqueness`, `patch`, …) leaked in.  **No finding.**

Every theorem's own argument list is explicit and matches the example's use
with no leftover implicits beyond the intended ones
(`horizon_le_lifespan_of_localSolution`'s `{horizon}`, unified from
`localSolution`; the `{ν T a f}` of `exists_eq_fields_of_agree`).

### 2.3 The congruence lemma's shape against `IsMaximalSolution` — **clean**

`Spec.lean:210-214` needs, for each `S` below the lifespan, a solution whose
fields are *literally* the global `(u,p)`:

```lean
∃ w : ClassicalSolutionR ν a f S, w.velocity = u ∧ w.pressure = p
```

`exists_eq_fields_of_agree` produces exactly that from a solution `w` on `S`
plus pointwise agreement `u (t,x) = w.velocity (t,x)`, `p (t,x) = w.pressure (t,x)`
for `t ∈ Ico 0 S` — the hypothesis in the direction and spelling U7 will have
it, and it typechecks against the restated clause in `AxiomsU4U6.lean`'s last
`example`.  `exists_eq_fields_of_eqOn` is the same on the slab
`Ico 0 S ×ˢ univ`, and `ClassicalSolutionR.congr` is the underlying
constructor.  This is the right shape, and the choice recorded in §4 of the
lane record (a *constructor*, not an extensionality claim, which would be
false) is the correct reading of the spec.  **No finding.**

### 2.4 Honesty of the lane record — three claims spot-checked, plus one more

1. **"`Set.Ico_subset_Ico_right` *does not exist* for `Set` (only for `Finset`,
   `Order/Interval/Finset/Basic.lean:176`).  Use `Ico_subset_Ico le_rfl hST`
   (`Order/Interval/Set/Basic.lean:281`)."** — **True, both line numbers
   exact.**  A repo-wide grep of the pinned Mathlib finds `Ico_subset_Ico_right`
   at exactly one place, `Mathlib/Order/Interval/Finset/Basic.lean:176`, in the
   `Finset` namespace; the `Set` file has `Ico_subset_Ico` at `:281`,
   `Ico_subset_Ico_left` at `:285`, and no `_right` variant.
2. **"`fderiv_sub_const` (`Mathlib/Analysis/Calculus/FDeriv/Add.lean:790`) is
   **unconditional** — no differentiability hypothesis."** — **True, line number
   exact.**  The statement is
   `theorem fderiv_sub_const (c : F) : fderiv 𝕜 (fun y => f y - c) x = fderiv 𝕜 f x`;
   its only argument is the constant, and the neighbouring
   `Differentiable.sub_const` at `:783` carries its `hf` explicitly, so `f` is a
   plain section variable.  `pressureGradient_sub_basepoint` therefore has no
   side condition, and `momentum` / `pressure_gradient` transfer by rewriting,
   as claimed.
3. **"If D01 had imposed `momentum` on `Ico 0 T` instead of `Ioo 0 T`, this
   lemma would be false as stated (no neighbourhood at `t = 0`)."** — **True,
   and load-bearing.**  `NavierStokes.ProblemStatement.temporalDerivative`
   (`vendor/NavierStokesAndEuler/NavierStokes/ProblemStatement.lean:55`) is
   `fderiv ℝ (fun s : ℝ => u (s, x)) t 1` — an unrestricted *two-sided* Fréchet
   derivative in time, with no `within`.  At `t = 0` its value is not determined
   by `u` on `Ico 0 T`, so the `Filter.EventuallyEq.fderiv_eq` step in
   `temporalDerivative_eq_of_eqOn` genuinely requires the open `Ioo 0 T` and
   `Ioo_mem_nhds`.  The other three residual terms (`advection`,
   `spatialLaplacian`, `pressureGradient`) are spatial `fderiv`s at fixed `t`
   and need only the slice, which is why the helper lemmas are correctly split
   between `Ico`-hypotheses and `Ioo`-hypotheses.  The record's field-by-field
   table in §4 is accurate row by row.
4. **Bonus check, §1: "`grep -rn "ClassicalSolutionR" formalization/ vendor/`
   hits only two docstring mentions in `Section4/D01/SmoothDatum.lean` (`:42`,
   `:384`)."** — **True, exactly those two lines**, and the cited D01 precedent
   for restating a contract object is real (`def IsSobolevDatum` at
   `Section4/D01/SmoothDatum.lean:237`, with the "definitionally equal … discharge
   one by the other with `exact`" docstring).

Against those four, findings 1-3 above are the inaccuracies found.

## 3. Commands and results

All from the worktree `.claude/worktrees/032-A02-restrict-order` (WT), with
`. scripts/lean-env.sh` and `LEAN_NUM_THREADS=6`, no `-j`; every `lake`
invocation from `WT/verification`.

| # | command | result |
|---|---|---|
| 1 | `cd WT && bash scripts/lean-install.sh` | exit 0, ends `== OK`; 9406 jobs replayed; the five `Tests.*` contracts print `checked; standard logical axioms only` |
| 2 | `cd WT/verification && lake build NSFormalization.Section4.A02.Restrict NSFormalization.Section4.A02.Order` | **exit 0**, `Build completed successfully (8815 jobs).` |
| 3 | `grep -n 'A02\|sorry\|declaration uses' <build log>` | **no matches** (exit 1) — no `sorry` warning anywhere, and neither A02 module emits a warning of its own.  Every warning in the log is pre-existing (`Source/RealSobolev.lean`, `Source/FiniteHilbertBochner.lean`, `Paper3/RealPositiveDensity.lean`, `Paper3/SpatiallyCompactTime.lean`, `Paper3/RealVectorPositiveDensity.lean`) |
| 4 | `cd WT/verification && lake env lean ../research/A02/AxiomsU4U6.lean` | **exit 0**.  All **25** declarations print exactly `[propext, Classical.choice, Quot.sound]` — nothing else, no `sorryAx`.  No errors, so the nine-`example` conformance block typechecks |
| 5 | `grep -n 'sorry\|admit\|native_decide\|axiom' formalization/NSFormalization/Section4/A02/*.lean` | **no output** (exit 1) — not even inside comments |
| 6 | `cd WT && make check` | **exit 0**.  `check_formalization_plan --check`, `check_contracts`, `test_contract_policy` (`Ran 13 tests … OK`), `check_work_queue` (`30 work items: … consistent.`).  `source_hashes_match: false` and the `Paper1/BoundaryCorollary.lean:90` `sorry` token are pre-existing on base and untouched by this lane |
| 7 | `cd WT/verification && lake env lean /tmp/a02rev/Bridge.lean` (review-only, outside WT) | **exit 0**, silent.  `toContract` / `ofContract` both typecheck field-by-field; nine `rfl` / `Iff.rfl` equalities between the A02 and `Contracts.V1.Data` copies typecheck |
| 8 | `cd WT/verification && lake env lean /tmp/a02rev/NegBridge.lean` (review-only, deliberate failure) | exit 1 with **exactly two** errors, `maximalLifespanR` and `RegularThrough` — confirming the lane's warning that those two, and only those two, need transport rather than `rfl` (finding 1) |
| 9 | `cd WT/verification && lake env lean ../research/A02/Spec.lean` | **exit 0** — the spec still elaborates and was not modified by the lane |
| 10 | `cd WT && git status --short` | empty.  `git show --stat c257c21` = the four expected files, `903 insertions(+)`, no deletions |

### The 25 audited declarations (command 4)

U4 (17): `ClassicalSolutionR.restrict`, `ClassicalSolutionR.nonempty_restrict`,
`exists_restrict`, `slice_eq_of_eqOn`, `scalarSlice_eq_of_eqOn`,
`spatialDerivative_eq_of_eqOn`, `pressureGradient_eq_of_eqOn`,
`temporalDerivative_eq_of_eqOn`, `navierStokesResidual_eq_of_eqOn`,
`ClassicalSolutionR.congr`, `exists_eq_fields_of_eqOn`,
`exists_eq_fields_of_agree`, `pressureGradient_sub_basepoint`,
`contDiffOn_basepoint`, `ClassicalSolutionR.normalizePressure`,
`exists_pressure_normalization`, `normalizePressure_gauge_invariant`.

U6 (8): `horizon_le_lifespan`, `horizon_le_lifespan_of_localSolution`,
`lifespan_le_iff`, `lifespan_le_iff_no_extension`,
`lifespan_ge_of_forall_shorter`, `exists_horizon_gt_of_lt_lifespan`,
`regularThrough_iff`, `referenceLifespan`.

## 4. Notes for the lead (no action required of the lane)

* **The binding layer is cheap, and cheaper than the record says.**  Once
  `Bindings` carries the two field-by-field conversions for
  `ClassicalSolutionR` (both verified to typecheck here), `initialClassR`,
  `MemForceR`, `PressureGaugeEquivOn`, `IsSobolevPath`, `IsSobolevDatum`,
  `MemHInfty` and `IsSolenoidal` are already `rfl`.  Only `maximalLifespanR`
  (an `iSup` congruence through `Nonempty`) and `RegularThrough` (one `Iff`)
  need a written step.  The architectural question the record raises — moving
  `ClassicalSolutionR` to a canonical local module so `Data.lean` V2 imports it
  — is still worth answering, but on its own merits, not on the inflated cost.
* **Lane 033 collision.**  The record's warning stands: A02 unit U1a needs the
  same §0 restatement.  Keeping this file's §0 and having U1a import
  `NSFormalization.Section4.A02.Restrict` is the right merge resolution, and
  this review adds a reason: §0 is now *verified* equal to the contract in both
  the textual and the semantic sense, so a second, unverified copy would be a
  strict regression.
* **`referenceLifespan`'s middle conjunct** (`∃ S, T + δ < S ∧ Nonempty …`) is
  what lets R42 read its reference on the closed `Icc 0 (T+δ)`.  It is carried
  by the original witness `S := T + δ₀`, so the single halving really does
  serve all three conjuncts, as §6 of the record claims.
