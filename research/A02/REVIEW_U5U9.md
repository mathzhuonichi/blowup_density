# Review — lane 058, task A02, units U5 (`patch`) and U9 (`lifespan_le_of_unbounded`)

Reviewer run on worktree `.claude/worktrees/058-A02-units-u5-u9` at commit
`9169733`. Module under review:
`formalization/NSFormalization/Section4/A02/Patch.lean` (new, 172 lines);
conformance harness `research/A02/axioms_u5u9.lean` (new);
notes `research/A02/ATTEMPTS_U5U9.md` (new). No other file is touched by the lane
(`git diff --stat HEAD~1 HEAD`: 3 files, 335 insertions, 0 deletions).

## Verdict: **ACCEPT**

Both spec fields are proved, sorry-free, on standard axioms only, with
statements token-for-token identical to `research/A02/Spec.lean`. The U9
mathematics is correct on every point the brief flagged. No blocking or
non-blocking defects were found; findings 4–6 below are observations recorded
for downstream lanes, not requests for change.

## 1. Commands and results

All commands run from the worktree with `. scripts/lean-env.sh`,
`LEAN_NUM_THREADS=6`, no `-j`, one lake at a time, lake invoked only from
`verification/`.

| # | Command | Result |
|---|---|---|
| C1 | `bash scripts/lean-install.sh` | `== OK` |
| C2 | `cd verification && lake build NSFormalization.Section4.A02.Patch` | `Build completed successfully (9942 jobs).` **EXIT=0** |
| C3 | C2 output filtered `grep -iE 'Section4/A02\|Section4\.A02'` | no matches (grep exit 1) — **no diagnostic of any kind attributable to the A02 modules**; every warning in the transcript is a cached replay from `NSFormalization/Source/*` and `NSFormalization/Paper3/*` |
| C4 | `cd verification && lake env lean ../formalization/NSFormalization/Section4/A02/Patch.lean` | **zero output, EXIT=0** — fresh elaboration of the file produces no errors, no warnings, no `info` |
| C5 | `cd verification && lake env lean ../research/A02/axioms_u5u9.lean` | **EXIT=0**; six `#print axioms` lines, each exactly `[propext, Classical.choice, Quot.sound]`; both conformance `example`s elaborate with no error (see §2) |
| C6 | `grep -nE 'sorry\|admit\|native_decide\|axiom\|maxHeartbeats\|set_option'` on `Patch.lean` | no matches (exit 1) |
| C7 | same grep on `research/A02/axioms_u5u9.lean` | only the six `#print axioms` commands (lines 13–18) and two prose mentions in the header comment (lines 3, 5). No `axiom` declaration, no `set_option`, no `sorry` |
| C8 | `make check` | **EXIT=0** — `check_formalization_plan.py --check`, `check_contracts.py`, `test_contract_policy.py` (13 tests OK), `check_work_queue.py` (`30 work items: ownership, contract registration and task cards consistent.`) |

C5 verbatim:

```
'NSFormalization.Section4.A02.PressureGaugeEquivOn.refl' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A02.PressureGaugeEquivOn.symm' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A02.PressureGaugeEquivOn.mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A02.patch' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A02.speedENorm_le_ofReal' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A02.lifespan_le_of_unbounded' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 2. Spec conformance

Mechanical whitespace-normalised comparison (`tr -d ' \n'` on the extracted
regions, string equality):

| Spec region | Module restatement | Harness `example` | Result |
|---|---|---|---|
| `Spec.lean:357-367` `MaximalSolutionAPI.patch` | `Patch.lean:87-98` | `axioms_u5u9.lean:29-39` | **IDENTICAL** (both) |
| `Spec.lean:576-582` `MaximalSolutionAPI.lifespan_le_of_unbounded` | `Patch.lean:129-136` | `axioms_u5u9.lean:44-50` | **IDENTICAL** (both) |
| `Spec.lean:135-136` `limsupLeft` + `:148-149` `speedENorm` | `Patch.lean:55-56, 60-61` | — | **IDENTICAL** |

Both `example`s are discharged in term mode by the bare theorem name — `:= patch`
and `:= lifespan_le_of_unbounded` — with **no `by`, no extra arguments, no extra
hypotheses**.

The conformance examples are not vacuous. A deliberately mutated example
(`maximalLifespanR ν a f < ENNReal.ofReal T` instead of `≤`) was checked against
`lifespan_le_of_unbounded` in a scratch file outside the worktree
(`/tmp/rev058/mutation.lean`) and is **correctly rejected** with a type mismatch
that displays the two statements side by side. So the `:=` checks are real.

`limsupLeft` and `speedENorm` are not defined anywhere else in
`formalization/` — no shadowing or duplicate definition. The restatement
convention (A02 owns the two `⟪D01:…⟫` objects D01 does not yet define) matches
`SolutionClass.lean`'s handling of the `Contracts.V1.Data` objects, and both
docstrings cite the exact `Spec.lean` line ranges.

## 3. U5 `patch` — the witness, and the "no `▸` cast" claim

**Confirmed: the witness is literally `u₁` / `u₂`, with no transport.**
`rcases le_total T₁ T₂` then `rw [max_eq_right h]` / `rw [max_eq_left h]` rewrites
the **goal's existential binder type** from `ClassicalSolutionR ν a f (max T₁ T₂)`
to `… T₂` / `… T₁`, after which `refine ⟨u₂, …⟩` / `refine ⟨u₁, …⟩` supplies the
solution itself. The self-agreement clause is therefore `fun _ _ _ => rfl` and the
self-gauge clause is `PressureGaugeEquivOn.refl _ _`, both genuinely reflexivity.

The rewrite is legitimate because the body of the existential mentions only `T₁`
and `T₂`, never `max T₁ T₂`, so no occurrence in the body is disturbed.

**Agreement with the other solution is exactly U2/U3**, restricted:

* branch `T₁ ≤ T₂` (witness `u₂`): clause 1 is
  `(velocity_unique_core hν u₁ u₂ t ⟨ht.1, lt_of_lt_of_le ht.2 (le_min le_rfl h)⟩ x).symm`,
  clause 3 is `PressureGaugeEquivOn.mono (Ico_subset_Ico le_rfl (le_min le_rfl h)) (pressure_gauge_core hν u₁ u₂)`.
* branch `T₂ ≤ T₁` (witness `u₁`): the mirror, with `hvel` used directly (no
  `.symm`) in clause 2 and `hpre.symm` in clause 4.

Orientation checked against the definitions:
`velocity_unique_core` (`Uniqueness.lean:81-84`) concludes on `Ico 0 (min T₁ T₂)`
with `u₁ = u₂`, and `pressure_gauge_core` (`Uniqueness.lean:133-135`) gives
`PressureGaugeEquivOn (Ico 0 (min T₁ T₂)) u₁.pressure u₂.pressure`. The side
conditions `T₁ ≤ min T₁ T₂` (resp. `T₂ ≤ min T₁ T₂`) are `le_min le_rfl h` /
`le_min h le_rfl` and are correct in each branch. The spec's clause ordering
(`u₁.pressure w.pressure` and `u₂.pressure w.pressure`) matches the direction of
`PressureGaugeEquivOn I p q := ∃ c, ∀ t ∈ I, ∀ x, q (t,x) = p (t,x) + c t`
(`SolutionClass.lean:109-110`) in both branches — I checked each of the four
clauses in each of the two branches individually.

The three new helper lemmas are correct on that unfolding: `refl` supplies
`c = 0`, `symm` supplies `c ↦ -c`, `mono` reuses the same `c`.

## 4. U9 `lifespan_le_of_unbounded` — the mathematics

The proof is by contradiction from `hcon : ENNReal.ofReal T < maximalLifespanR ν a f`.
I traced every step against the cited signatures; all four brief-flagged points
check out.

**(a) `Ico 0 T` vs `Icc 0 T` — correct, with margin to spare.**
`exists_horizon_gt_of_lt_lifespan` (`Order.lean:124-127`) requires `0 ≤ T`
(supplied as `hT.le`) and yields a **strict** `T < T'` together with
`Nonempty (ClassicalSolutionR ν a f T')`. `ClassicalSolutionR.exists_velocity_bound`
(`Bounds.lean:214-216`) is then applied with `b := T`, `hb0 := hT.le`,
`hbT := hTT' : T < T'`, and returns `∀ t ∈ Icc 0 T, ∀ x, ‖w.velocity (t,x)‖ ≤ B`.
Its own internal `hsub : Icc 0 b ⊆ Ico 0 T'` is exactly the inclusion in question
and needs the strict inequality, which it has. The bound is uniform in `x` as well
as `t`, so it is a genuine `L^∞` bound at each time.
The proof only ever *consumes* the bound on `Ioo 0 T ⊆ Ico 0 T ⊆ Icc 0 T`
(`hbound_slice` is stated on `Ico 0 T` and applied via `⟨ht.1, ht.2.le⟩`), so the
closed endpoint is spare capacity, not a load-bearing step. No off-by-one.

**(b) The filter manipulation is correct.**
`limsupLeft T φ = Filter.limsup φ (nhdsWithin T (Iio T))`. The proof shows
`Ioo 0 T ∈ 𝓝[<] T` as `Ioi 0 ∩ Iio T` via `rw [← Ioi_inter_Iio]` and
`inter_mem (mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hT)) self_mem_nhdsWithin`.
`Ioi_mem_nhds hT` genuinely needs the spec hypothesis `0 < T`, which is present —
the hypothesis is used, not decorative. `Filter.eventually_of_mem` then gives
`∀ᶠ t in 𝓝[<] T, speedENorm (u(t,·)) ≤ ENNReal.ofReal B`, and
`Filter.limsup_le_of_le` bounds the limsup (the `IsCoboundedUnder` autoparam
discharges by `isBoundedDefault` because `ℝ≥0∞` is an `OrderBot`). Closing:
`rw [hunbdd]` turns it into `⊤ ≤ ENNReal.ofReal B`, killed by `top_le_iff` plus
`ENNReal.ofReal_ne_top`. Correct, and the argument does not depend on `𝓝[<] T`
being `NeBot` (it is, `T` being a real number, but the step does not need it).

**(c) The brief's premise about the quantifier is not what the spec says — and
the module matches the spec, not the brief.** `Spec.lean:576-582` does **not**
quantify over `u : ClassicalSolutionR ν a f T`. It quantifies over a raw
`u : SpaceTimeField` and `p : SpaceTimeScalar` together with the *family*
hypothesis

```
(∀ S : ℝ, 0 < S → S < T → ∃ w : ClassicalSolutionR ν a f S, w.velocity = u ∧ w.pressure = p)
```

i.e. "`(u,p)` is a classical solution on every `[0,S)` with `S < T`". That is the
right formulation — `T` is the blow-up time, so there is in general **no**
solution on `[0,T)` in the class, and demanding one would make the field
unusable by R42. The module reproduces this verbatim (§2), and the hypothesis
about the left limsup is indeed about `u`'s velocity as `t ↑ T`, the endpoint of
its own family of horizons.

**The theorem does not assume `T < maximalLifespanR`.** That inequality appears
only as `hcon`, introduced by `by_contra` on the conclusion, and is discharged as
`False`. Both substantive hypotheses do real work: `hex` is used to build `hagree`,
and `hunbdd` is used at the last step. Nothing is silently assumed.

The identification step is sound: for `t ∈ Ico 0 T` the proof picks the
intermediate horizon `S = (t+T)/2`, so `t < S < T < T'`; `hex S` supplies
`wS : ClassicalSolutionR ν a f S` with `wS.velocity = u`, and
`velocity_unique_core hν w wS` applies at `t ∈ Ico 0 (min T' S)` because
`t < T' ` and `t < S`. Both solutions carry the same datum `(ν, a, f)`, as
`velocity_unique_core` requires. The two `linarith` side goals (`0 < (t+T)/2` from
`0 ≤ t` and `0 < T`; `(t+T)/2 < T` from `t < T`) are both valid.

**(d) The paper.** Confirmed the manuscript states the criterion in `L^∞`, and
that the formalized route is the manuscript's own two-step argument:

* `paper/sections/04-whole-space.tex:35` (Theorem 4.1 `thm:Rinsert`) displays
  `\limsup_{t\uparrow T}\norm{u_\eps(t)}_\infty=\infty` — the `L^∞` norm, matching
  `speedENorm z = eLpNorm z ⊤ volume` and `limsupLeft`.
* `paper/sections/04-whole-space.tex:53`: "An extension through `T` would be
  bounded in `C_tH^2` on a neighborhood of `T`, hence bounded in `L^\infty_x` by
  \eqref{eq:Rproduct}, contradicting the blowup of `U_\eps`. Thus its maximal
  lifespan is exactly `T`."
* `eq:Rproduct` (`paper/sections/appendix-a-local-theory.tex:9-14`) contains
  `\norm{v}_\infty\le C\norm{v}_{H^2}`.
* Proposition 2.1 itself (`02-preliminaries.tex:106-114`, `prop:local`
  = `lem:Rlocal`) states the continuation criterion in the integrated `H²` form
  `\int_0^S\norm{u(t)}_{H^2(D)}^2\dd t<\infty`; the `L^∞` blow-up statement is the
  one Theorem 4.1's proof actually uses, and it is what the spec formalizes.

The Lean proof follows the same two steps rather than a shortcut:
`exists_velocity_bound` (`Bounds.lean:217-232`) obtains the continuous `H²` datum
path from `u.sobolev 2`, bounds it on the compact `Icc 0 b`
(`IsCompact.exists_bound_of_continuousOn`), and converts to a pointwise velocity
bound through `A03.boundedRepresentativeConst * D01.jetSobolevConst 2` — i.e.
the `eq:Rproduct` embedding. That is the manuscript's `C_tH²` → `L^∞` chain,
pre-assembled.

## 5. Honesty of `ATTEMPTS_U5U9.md`

All three rejected approaches were spot-checked and all three claims hold.

* **The `▸` cast breaking `rfl`** (`ATTEMPTS_U5U9.md:90-95`). Reproduced in a
  scratch file outside the worktree (`/tmp/rev058/cast_check.lean`): with
  `hmax : T₂ = max T₁ T₂` and witness `hmax ▸ u₂`, the self-agreement clause
  fails exactly as claimed —
  `error: Type mismatch  rfl  has type ?m = ?m but is expected to have type (hmax ▸ u₂).velocity (x✝², x✝) = u₂.velocity (x✝², x✝)`.
  The claim is accurate and the chosen `rw`-the-binder route is the right fix.
* **`LocalizedBlowup.no_continuous_continuation` needing the stronger local
  form** (`ATTEMPTS_U5U9.md:101-104`). Read `Source/LocalizedBlowup.lean:10-13,
  36-39`: the hypothesis is `LocalSpeedUnboundedAt T K u`, which asserts that for
  every threshold and every `δ` there is a witness `(t,x)` with **`x ∈ K`** for a
  fixed compact `K`. The spec's hypothesis is a global essential-supremum limsup
  with no spatial localization whatever, so it cannot produce witnesses confined
  to a compact set. Strictly stronger, not applicable. Accurate; and it agrees
  with `research/A02/COMPARISON.md:96,172`, which recorded the same thing before
  the lane started.
* **The `H²`-continuity + `eq:Rproduct` manuscript sketch being what
  `exists_velocity_bound` already packages** (`ATTEMPTS_U5U9.md:96-100`).
  Confirmed by reading `Bounds.lean:217-232` — see §4(d). Accurate.

The "Commands run" section (`:106-112`) matches what I reproduced.

## 6. Findings

No blocking finding. Nothing below requires a change to this lane.

1. *(severity: none — observation; `Patch.lean:66-81`)*
   `PressureGaugeEquivOn.{refl,symm,mono}` are general facts about the relation
   defined in `SolutionClass.lean:109`, but they live in `Patch.lean`. They are
   correct and correctly scoped, and putting them where they were first needed is
   the established pattern in this tree. If a later A02 unit needs them, moving
   them next to the definition would be the tidier home. No action now.

2. *(severity: none — observation; U9 statement)*
   Because `\norm{v}_\infty\le C\norm{v}_{H^2}`, an `L^∞` blow-up hypothesis is
   **stronger** than an `H²` blow-up hypothesis, so the formalized
   `lifespan_le_of_unbounded` is the weaker of the two theorems one could state.
   This is deliberate and is the manuscript's own statement
   (`04-whole-space.tex:35`), documented at `Spec.lean:571-575` and
   `COMPARISON.md:96`. Recorded here only so that a downstream lane needing the
   `H²` form knows it is not covered by this unit.

3. *(severity: none — observation; build wiring)*
   `formalization/NSFormalization.lean` imports no `Section4` module, so
   `Patch.lean` is not in the default-target closure — the same is true of every
   pre-existing `Section4/A02/*` module, so this is the project convention and
   not a regression. CI still compiles it: `.github/workflows/contracts.yml`
   runs `experiments/build_changed_lean.py --base-ref`, which maps every changed
   `formalization/**/*.lean` path to a `lake build` module target, and
   `Patch.lean` is a changed path. (`research/A02/axioms_u5u9.lean` is outside
   the three prefixes that script recognises and so is not run in CI — again the
   convention for every prior lane's `axioms_*.lean` harness.)

## 7. Scope check

The lane adds only the three files listed at the top; it modifies and deletes
nothing. No registry, contract, plan, or task-card file needed updating, and
`make check`'s `check_work_queue.py` confirms ownership, contract registration
and task cards are consistent at this commit.
