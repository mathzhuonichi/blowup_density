# Review — lane 064, A02 unit U7 (`exists_maximal`, `maximal_unique`)

Reviewer: independent opus reviewer, lane 064.
Worktree: `.claude/worktrees/064-A02-unit-u7`, commit `f5e747c`.
Module under review: `formalization/NSFormalization/Section4/A02/Maximal.lean`
(236 lines, new).  Conformance harness: `research/A02/axioms_u7.lean`.
Record: `research/A02/ATTEMPTS_U7.md`.

## Verdict

**ACCEPT-WITH-NOTES**

The Lean is correct and complete: both spec fields are proved, the axiom set is
the standard three, the module emits zero diagnostics, and the directed-union
construction is sound — including the two places it could plausibly have cheated
(the pressure gauge and the literal-total-function field equality), which it does
not.  The two notes below are a misdiagnosed entry in the friction record and an
observation about CI reach.  **No code change is required.**

## 1. Commands and results

All run with `. scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`, no `-j`, lake only
from `verification/`, one lake at a time.

```
$ bash scripts/lean-install.sh
…
== OK                                                            (exit 0)

$ cd verification && lake build NSFormalization.Section4.A02.Maximal
Build completed successfully (9942 jobs).                        (exit 0)
# full output grepped for `Section4/A02`: NO diagnostics
# (the warnings in the log are pre-existing, from Source/* and Paper3/*)

$ cd verification && lake env lean ../formalization/NSFormalization/Section4/A02/Maximal.lean
(no output)                                                      (exit 0)
# fresh elaboration of the file alone: zero warnings, zero info, zero errors

$ cd verification && lake env lean ../research/A02/axioms_u7.lean
'NSFormalization.Section4.A02.uField_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A02.pField_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A02.exists_maximal_of_localSolution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A02.maximal_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
                                                                 (exit 0)
# all 4 exactly the standard three; both spec-typed `example`s typecheck
# (an `example` that failed to elaborate would be an error, not a warning)

$ grep -nE 'sorry|admit|native_decide|axiom|maxHeartbeats|set_option' \
    formalization/NSFormalization/Section4/A02/Maximal.lean research/A02/axioms_u7.lean
research/A02/axioms_u7.lean:3:/-! Transitive-axiom audit …      (comment)
research/A02/axioms_u7.lean:13:-- U7 axiom audit                 (comment)
# nothing in the module; nothing outside comments anywhere

$ make check
python3 experiments/check_formalization_plan.py --check   OK
python3 experiments/check_contracts.py                    OK
python3 experiments/test_contract_policy.py               Ran 13 tests … OK
python3 experiments/check_work_queue.py                   30 work items: … consistent.
                                                                 (exit 0)
```

`attribute [local instance] Classical.propDecidable` (`Maximal.lean:71`) does
**not** change the axiom list — the four `#print axioms` above are taken with
that attribute in force and print exactly `[propext, Classical.choice,
Quot.sound]`.  (`Classical.propDecidable` is itself built from
`Classical.choice`, which the construction already uses via `Exists.choose` and
`Nonempty.some`, so nothing new enters.)

## 2. Spec conformance — verified by textual diff, not by eye

| object | spec | module | result |
|---|---|---|---|
| `presingularTimes` | `Spec.lean:168-169` | `Maximal.lean:78-79` | `diff` empty — **byte-identical** |
| `IsMaximalSolution` | `Spec.lean:210-214` | `Maximal.lean:85-89` | `diff` empty — **byte-identical** |
| `exists_maximal` conclusion | `Spec.lean:421-423` | `axioms_u7.lean:37-39` | identical modulo the trailing ` :=` |
| `maximal_unique` | `Spec.lean:429-434` | `axioms_u7.lean:50-55` | identical modulo the trailing ` :=` |

```
$ diff <(sed -n '168,169p' research/A02/Spec.lean) \
       <(grep -A1 '^def presingularTimes' …/Maximal.lean)        # empty
$ diff <(sed -n '210,214p' research/A02/Spec.lean) \
       <(grep -A4 '^def IsMaximalSolution' …/Maximal.lean)       # empty
$ diff <(sed -n '421,423p' Spec.lean | sed 's/^ *//; s/^exists_maximal : //') \
       <(sed -n '37,39p' axioms_u7.lean | sed 's/^ *//')
3c3
< ∃ (u : SpaceTimeField) (p : SpaceTimeScalar), IsMaximalSolution ν a f u p
---
> ∃ (u : SpaceTimeField) (p : SpaceTimeScalar), IsMaximalSolution ν a f u p :=
$ diff <(sed -n '429,434p' Spec.lean | sed 's/^ *//; s/^maximal_unique : //') \
       <(sed -n '50,55p' axioms_u7.lean | sed 's/^ *//; s/^example : //')
6c6   (same, trailing ` :=` only)
```

**The A01 clause has the sanctioned shape.**  `exists_maximal_of_localSolution`
takes

```lean
(horizon : ℝ → SpatialField → SpaceTimeField → ℝ)
(localSolution : ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField),
  0 < ν → a ∈ initialClassR → MemForceR f → ClassicalSolutionR ν a f (horizon ν a f))
```

which is token-for-token the hypothesis `Contracts/V1/MaximalPartial.lean:155-158`
carries inside `horizon_le_lifespan`, and the same one
`Order.lean:56-60`'s `horizon_le_lifespan_of_localSolution` uses.  A01 will
discharge both by supplying `LocalTheoryAPI.horizon` / `LocalTheoryAPI.solution`
in one identical step.  (Cosmetic difference only: `Order.lean` makes `horizon`
implicit, `Maximal.lean` explicit.  Not a finding — explicit is the better choice
here, since `horizon` does not occur in the conclusion.)

**`maximal_unique` carries no A01 hypothesis, and the spec field has no A01
input.**  Checked directly against `Spec.lean:429-434`: the field's type is
`∀ ν a f, 0 < ν → a ∈ initialClassR → MemForceR f → ∀ u₁ u₂ p₁ p₂, … ` with no
`horizon`/`localSolution` binder anywhere.  The lane's claim that this is the
weaker-hypothesis true form is **correct**, and the module states it as the plain
spec field (`Maximal.lean:192-203`), with no `localSolution` argument.  The proof
does not use `ha`/`hf` either (bound as `_ha`/`_hf`) — a further, harmless
strengthening.  `COMPARISON.md:170` lists `⟪A01:solution⟫` as a U7 dependency;
that is accurate for `exists_maximal` and conservative for `maximal_unique`, and
`ATTEMPTS_U7.md` records the discrepancy explicitly.  Good.

## 3. The construction — the important part

### (a) Well-definedness of `uField`

`uField ν a f z = if h : SolExists ν a f z.1 then (chosenSol h).velocity z else 0`
with `SolExists ν a f t := ∃ S, t < S ∧ Nonempty (ClassicalSolutionR ν a f S)` and
`chosenSol h := h.choose_spec.2.some : ClassicalSolutionR ν a f h.choose`.

Three things had to hold and all three do.

1. **The dite branch is a function of the time slot only.** `SolExists ν a f z.1`
   mentions only `z.1`, and `chosenSol h` depends on `h` only through
   `Exists.choose`, which Lean's definitional proof irrelevance makes independent
   of *which* proof of `SolExists ν a f t` is supplied.  So `uField` genuinely
   defines one field, and `dite_eq_left hex` (`Maximal.lean:124`) is a sound
   rewrite for the `hex` manufactured from `w`.  No hidden dependence on `x`.

2. **The chosen solution's horizon strictly exceeds `t`.**
   `hex.choose_spec.1 : t < hex.choose` is used verbatim as the left half of
   `lt_min hex.choose_spec.1 ht.2` (`Maximal.lean:127`), so the overlap interval
   handed to `velocity_unique_core` is `Ico 0 (min hex.choose S)` and `t` is
   strictly inside it.  This is exactly the guarantee the task asked me to check,
   and it is present, not assumed.

3. **The overlap argument covers every presingular time.**  `uField_eq` is stated
   for `t ∈ Ico 0 S` and *any* `w : ClassicalSolutionR ν a f S`; `exists_maximal`
   invokes it on the slab of the restricted `wS` for each `S < T_max`.  The union
   of those slabs over `0 < S` with `ofReal S < maximalLifespanR` is precisely
   `presingularTimes ν a f`: for `t` with `0 ≤ t` and `ofReal t < T_max`,
   `exists_horizon_gt_of_lt_lifespan` (`Order.lean:124-130`) hands back `S' > t`
   carrying a solution, and `horizon_le_lifespan` puts `ofReal S'` under `T_max`,
   so some admissible `S ∈ (t, S']` exists.  In particular `SolExists ν a f t`
   holds at *every* presingular `t` including `t = 0` (`ofReal 0 = 0 < T_max`),
   so the `else 0` branch is never taken there.  Coverage: complete.

   Off the slab — `t < 0`, or `t ≥ T_max` — `uField` is arbitrary garbage.  That
   is harmless and is the point of (c) below.

   `velocity_unique_core` (`Uniqueness.lean:81-84`) is the genuine U2 statement
   on `Ico 0 (min T₁ T₂)`, not a weakened variant.

### (b) The pressure

`pField ν a f z = (chosenSol h).pressure z − (chosenSol h).pressure (z.1, 0)` —
the basepoint-`0` normalization, not the raw pressure.  This is the step that
makes the construction possible at all, and it is done correctly:

* `pressure_gauge_core hν (chosenSol hex) w` (`Uniqueness.lean:133-135`) gives
  `PressureGaugeEquivOn (Ico 0 (min hex.choose S)) (chosenSol hex).pressure w.pressure`,
  i.e. `∃ c : ℝ → ℝ, ∀ t ∈ I, ∀ x, w.pressure (t,x) = (chosenSol hex).pressure (t,x) + c t`
  (`PressureGaugeEquivOn`, `SolutionClass.lean:109-110`).
* `normalizePressure_gauge_invariant` (`Restrict.lean:280-287`) is exactly the
  fact the task asked me to confirm: from `PressureGaugeEquivOn I p q` it
  concludes `∀ t ∈ I, ∀ x, q (t,x) − q (t,x₀) = p (t,x) − p (t,x₀)`.  Its proof
  is `rw [hc t ht x, hc t ht x₀]; ring` — the `c t` cancels in the difference.
  **Two gauge-equivalent pressures have the same basepoint normalization**, hence
  the normalized representative is unique, hence `pField` is well-defined across
  the choice.  Confirmed.
* `pField_eq` (`Maximal.lean:134-148`) therefore proves
  `pField ν a f (t,x) = w.pressure (t,x) − w.pressure (t,0)` for *every* solution
  `w` on a horizon past `t`, which is the coherence needed.
* **`pField` is a genuine normalized representative, not an ad-hoc formula.**
  `exists_maximal` applies the congruence constructor not to `wS` but to
  `wS.normalizePressure (0 : Space)` (`Maximal.lean:176`), whose `pressure` field
  is literally `fun z => wS.pressure z − wS.pressure (z.1, 0)` and which is a
  bona fide `ClassicalSolutionR` by `ClassicalSolutionR.normalizePressure`
  (`Restrict.lean:247-265`) — the spec field `pressure_normalization`
  (`Spec.lean:399-403`, discharged as `exists_pressure_normalization`,
  `Restrict.lean:269-273`).  So the docstring claim that `exists_maximal` rests on
  `pressure_normalization` is honoured in the proof term, not just in prose.
  I checked `normalizePressure`'s own field transport: `momentum` and
  `pressure_gradient` go through `pressureGradient_sub_basepoint`
  (`Restrict.lean:230-234`, `fderiv_sub_const`), `pressure_smooth` through
  `contDiffOn_basepoint` with the slab-stability side condition
  `fun _ hz => ⟨hz.1, mem_univ x₀⟩`.  Sound.

The same normalization argument is reused for `maximal_unique`'s pressure clause
with the *global* gauge `c s := p₂ (s,0) − p₁ (s,0)` (`Maximal.lean:223`) — one
function of time serving all presingular `t`, as `PressureGaugeEquivOn` demands.
Orientation checked: `hgi` after `rw [hw1p, hw2p]` reads
`p₂ (t,x) − p₂ (t,0) = p₁ (t,x) − p₁ (t,0)`, and the goal
`p₂ (t,x) = p₁ (t,x) + (p₂ (t,0) − p₁ (t,0))` follows by `linarith`.  Correct.

### (c) The literal-fields clause — `exists_eq_fields_of_agree`

Read `Restrict.lean:213-218` and the `ClassicalSolutionR.congr` it delegates to
(`Restrict.lean:175-210`).

```lean
theorem exists_eq_fields_of_agree (w : ClassicalSolutionR ν a f T)
    (u : SpaceTimeField) (p : SpaceTimeScalar)
    (hu : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Space, u (t, x) = w.velocity (t, x))
    (hp : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Space, p (t, x) = w.pressure (t, x)) :
    ∃ w' : ClassicalSolutionR ν a f T, w'.velocity = u ∧ w'.pressure = p
```

* **It does not secretly require agreement outside the slab.**  Both hypotheses
  quantify over `t ∈ Ico 0 T` only; the `_of_eqOn` form it forwards to uses
  `Ico 0 T ×ˢ (univ : Set Space)`, the slab, and nothing else.  Confirmed by
  reading, not inferred.
* **The returned fields are literally `u` and `p` as total functions on
  `ℝ × Space`**: `congr` sets `velocity := u`, `pressure := p` and the two
  conjuncts are closed by `rfl` (`Restrict.lean:218` → `⟨w.congr hu hp, rfl, rfl⟩`).
  This is what `IsMaximalSolution` demands, and it is why the global `u`, `p`
  never have to match any particular `wS` off its slab.  The "germ-only fallback"
  was genuinely not needed.
* **Every other field is transported correctly**, checked one by one:
  `horizon_pos := w.horizon_pos`; `velocity_smooth`/`pressure_smooth` by
  `ContDiffOn.congr` on `Ico 0 T ×ˢ univ`, so smoothness is on the right set;
  `initial` re-reads `hu (0,x)` using `0 ∈ Ico 0 T` from `w.horizon_pos`;
  `divergence` via `spatialDerivative_eq_of_eqOn` at `t ∈ Ico`; `momentum` via
  `navierStokesResidual_eq_of_eqOn` at `t ∈ Ioo` — correctly the *open* interval,
  because `temporalDerivative_eq_of_eqOn` (`Restrict.lean:143-153`) needs an open
  neighbourhood `Ioo_mem_nhds ht.1 ht.2` to move `fderiv` along an `EventuallyEq`;
  `sobolev` via `slice_eq_of_eqOn`, rebuilding the same `G`; `pressure_gradient`
  via `pressureGradient_eq_of_eqOn`.  Nothing is dropped or weakened.

The two side goals in `exists_maximal` are discharged by `show … ; exact …`
against `wS.normalizePressure 0`'s field projections (`Maximal.lean:179-183`),
which reduce by defeq — I confirmed the `show`n statements are exactly the
conclusions of `uField_eq` / `pField_eq`.

### (d) Positivity

```lean
have hpos : 0 < maximalLifespanR ν a f :=
  lt_of_lt_of_le (ENNReal.ofReal_pos.mpr u₀.horizon_pos) (horizon_le_lifespan u₀)
```

`u₀ := localSolution ν a f hν ha hf : ClassicalSolutionR ν a f (horizon ν a f)`,
`u₀.horizon_pos : 0 < horizon ν a f`, and `horizon_le_lifespan`
(`Order.lean:48-51`, `le_iSup_of_le S (le_iSup_of_le ⟨u⟩ le_rfl)`) gives
`ENNReal.ofReal (horizon ν a f) ≤ maximalLifespanR ν a f`.  Correct, and it is
the only use of the A01 hypothesis — matching the docstring's claim that
positivity is precisely what A01 buys.

### (e) `maximal_unique`'s `common` helper

`common t ht0 htlt` produces `S := (t + S') / 2` with `0 < S`, `t < S`,
`ofReal S < T_max` (`Maximal.lean:203-213`).  Arithmetic checked: `S' > t ≥ 0`
gives `t + S' > 0`; `t < (t+S')/2 < S'`; and
`ENNReal.ofReal_lt_ofReal_iff_of_nonneg` plus `horizon_le_lifespan hne'.some`
puts `ofReal S` strictly under `T_max`.  Both `IsMaximalSolution` hypotheses are
then instantiated at the *same* `S`, so `velocity_unique_core` is applied to two
solutions on a common horizon (`min S S`).  Correct — and note this is why no A01
input is needed: the horizon comes from U6's order lemma, which is purely
order-theoretic.

## 4. Findings

### Finding 1 — MINOR (record accuracy, not code): the `ht.1` snag does not reproduce

`ATTEMPTS_U7.md` §"What failed / friction", second bullet:

> Destructuring `ht : t ∈ presingularTimes ν a f` via `ht.1` does not resolve —
> dot-notation projection does not unfold `Set.mem`/`setOf` to reach the `And`.

**This is not true at this pin.**  Dot-notation projection *does* whnf through the
`def` + `Set.mem`/`setOf` layers at default transparency.  Both of these
elaborate with no error and no warning:

```lean
example {ν a f t} (ht : t ∈ presingularTimes ν a f) : (0:ℝ) ≤ t := ht.1
example {ν a f t} (ht : t ∈ presingularTimes ν a f) :
    ENNReal.ofReal t < maximalLifespanR ν a f := ht.2
```

I went further and rewrote the whole velocity branch of `maximal_unique` using
`ht.1`/`ht.2` throughout instead of `obtain ⟨ht0, htlt⟩ := ht` and threading the
components — it compiles clean (`lake env lean /tmp/u7_snag2.lean`, exit 0, no
output).  So the recorded diagnosis is a misattribution: whatever the original
error was, it was not this.

**Impact:** none on correctness.  `obtain` is equivalent and the shipped proof is
fine.  **Fix:** correct or delete that bullet in `ATTEMPTS_U7.md` so the next lane
does not inherit a false belief about `Set`-membership projections.  Do not touch
`Maximal.lean`.

### Finding 2 — CONFIRMED (no action): the `dif_pos` deprecation snag is real

`ATTEMPTS_U7.md` first bullet claims `dif_pos` is deprecated in favour of
`dite_eq_left`, a drop-in with the identical signature.  Reproduced exactly:

```lean
example … : uField ν a f (t, x) = (chosenSol hex).velocity (t, x) := dif_pos hex
-- warning: `dif_pos` has been deprecated: Use `dite_eq_left` instead   (exit 0)
```

Both halves confirmed: the deprecation is real (so the switch was *necessary* to
keep the file warning-free), and `dif_pos` is a drop-in for `dite_eq_left` at this
call site (it still elaborates, with only the warning).  The record is honest.

### Finding 3 — INFORMATIONAL (no action in this lane): the module is not yet on any build target

`formalization/NSFormalization.lean` (the `NSFormalization` lean_lib root) does
not import `Section4.A02.Maximal`, and nothing under `verification/Bindings`,
`verification/Contracts` or `verification/Tests` imports it either — the A02
modules reachable from `verification`'s default targets stop at
`Bindings/MaximalPartial.lean:3`, which imports `Section4.A02.Patch` (and thence
`Restrict`, `Order`, `SolutionClass`).  Consequence: `make test`
(`lake -d verification test`, defaultTargets `Tests`/`Contracts`) does **not**
compile `Maximal.lean`; only the explicit `lake build
NSFormalization.Section4.A02.Maximal` does.

This is expected — the U7 fields are not in the `MaximalPartial` contract record
(`Contracts/V1/MaximalPartial.lean` fixes ten *other* fields and its scope note
explicitly excludes "existence and uniqueness of the maximal solution
(`IsMaximalSolution`, `exists_maximal`, `maximal_unique`)"), and registration is a
separate lane.  Noted only so the integrator knows a regression in `Maximal.lean`
is not currently caught by `make test`, and so the follow-up registration lane is
not forgotten.

## 5. What I checked and did not find

* No `sorry`, `admit`, `native_decide`, `axiom`, `maxHeartbeats` or `set_option`
  in the module — the only grep hits repo-wide for U7 are two comment lines in
  `axioms_u7.lean`.
* No weakened restatement: `presingularTimes` and `IsMaximalSolution` are
  byte-identical to `Spec.lean`, so the theorems cannot be true "for a different
  predicate".
* No smuggled hypothesis: `maximal_unique` takes no `localSolution`, and does not
  even use `a ∈ initialClassR` or `MemForceR f`.
* No circularity: the module imports only `Section4.A02.Uniqueness` and
  `Section4.A02.Order`, both already merged, and nothing from `Contracts`.
* The `else 0` branch of `uField`/`pField` is unreachable on `presingularTimes`
  and irrelevant elsewhere, because `exists_eq_fields_of_agree` constrains only
  the slab.
