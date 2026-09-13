# C01 unit U2 review (lane 045)

Reviewed: `formalization/NSFormalization/Section4/C01/ForceSlices.lean` (178 lines),
`research/C01/axioms_u2.lean` (45 lines) and `research/C01/ATTEMPTS_U2.md` at
commit `cb3defc` ("Rewire ForceSlices to the canonical D01 DatumToJets lemmas").
Read-only review; nothing in the lane was changed except this file.

Worktree: `.claude/worktrees/045-C01-unit-u2`. Lane diff vs `erenup/integration`:
three **new** files, no existing file touched.

## Verdict: **ACCEPT-WITH-NOTES**

The module builds clean, emits no diagnostics of its own, contains no `sorry`,
`admit`, `native_decide`, `axiom` or `set_option`/`maxHeartbeats` escape, and
`#print axioms` on the theorem is exactly the three standard logical axioms. The
`example` in `axioms_u2.lean` is the spec field `forceTimeRegularity`
token-for-token and is discharged by the proved theorem with no extra
hypotheses. The `slice` / `l2Sq` / `l2Norm` restatements are byte-identical to
`Spec.lean:167,172,177`. Continuity really is on `Ici 0` including `t = 0`.
The dependency rewire that caused the lane to be resumed is correct and complete:
`A02.Energy` is not in the module's import closure. `make check` passes.

Both findings are documentation-only, in `ATTEMPTS_U2.md`, and neither touches
the Lean. There is one informational note about CI coverage.

---

## Findings

### 1. LOW — `ATTEMPTS_U2.md`: the first half still documents the superseded pre-rewire proof

`research/C01/ATTEMPTS_U2.md` §"Route that worked" (lines 22-40), §"Cast
handling" (lines 50-57) and §"Small failures fixed along the way" item 3
(line 70) describe the **first** version of the proof, which used
`A02.sliceLp`, `A02.sliceLp_ae`, `A02.memLp_of_isSobolevDatum`,
`NavierStokesR3.Comparison.continuous_slice_of_continuousOn` and a
`subst hs` cast device. None of those appear in the committed file: the rewire
replaced them with `D01.jetOfDatum` / `jetOfDatum_ae` / `memLp_of_isSobolevDatum`
/ `contDiff_slice` and with carrying the whole proof at the nat-cast order
`((0 : ℕ) : ℝ)` so that no cast transport is needed at all.

Only the final §"Rewire to D01 (post-review, before merge)" (lines 84-137)
corrects this, and it does so by narrating the delta rather than by superseding
the earlier text. A reader who stops at §"Route that worked" comes away with a
description of a proof that does not exist and of a dependency on
`Section4/A02/Energy.lean` that the lane specifically removed.

*Fix*: add a one-line "**Superseded — see §Rewire to D01**" banner at the head of
each of the three stale sections, or rewrite them in terms of the D01 route.

### 2. LOW — `ATTEMPTS_U2.md` snag 2 misdescribes the failure mode (the fix itself is right)

`ATTEMPTS_U2.md:64-68` records:

> After `rw [lpNorm_two_eq_sqrt_l2Sq hmem]` the residual
> `√(l2Sq z) = √(Comparison.l2Sq z)` was not closed by `rw`'s auto-`rfl`
> (instances transparency does not unfold the two `def`s).

Reproduced: `rw` never produces that residual goal. It fails earlier, with
`Tactic 'rewrite' failed: Did not find an occurrence of the pattern`, in both
directions — the pattern `√(NavierStokesR3.Comparison.l2Sq z)` is not
syntactically present in `l2Norm z = (eLpNorm z 2 volume).toReal`
(probe `/tmp/probe_u2_b.lean`), and the pattern
`NavierStokesR3.Comparison.comparisonLpNorm 2 z` is not present in
`√(l2Sq z) = (eLpNorm z 2 volume).toReal` either (probe `/tmp/probe_u2_c.lean`).

The *substance* is correct — the spec's `l2Sq` and the vendor's
`NavierStokesR3.Comparison.l2Sq` (`ComparisonSetup.lean:31`, body
`∫ x : Space, ‖f x‖ ^ 2`) are defeq but not syntactically equal, so the bridge
has to be a `show` at default transparency — and the committed fix
(`ForceSlices.lean:117`, `show Real.sqrt (NavierStokesR3.Comparison.l2Sq z) = …`)
is exactly right. Only the sentence describing *how* the naive attempt failed is
wrong. *Fix*: reword to "`rw` cannot even find the pattern, because …".

### 3. INFO (not a lane defect) — the module is outside the `lake test` closure

No module in `verification/` imports `NSFormalization.Section4.C01.ForceSlices`;
the only importer in the repository is `research/C01/axioms_u2.lean`, which is
not part of any Lake library. `formalization/NSFormalization.lean` imports no
`Section4` module at all, so the default target does not reach it either.
Consequently `make check` and `lake test` do **not** compile this file; only an
explicit `lake build NSFormalization.Section4.C01.ForceSlices` does.

This is the project's existing convention for units not yet bound to a
registered contract — `Section4/A02/*` and `Section4/D01/DatumToJets.lean` are
likewise unreferenced from `verification/` — so it is not something this lane
introduced or should fix. It is recorded because it means a future refactor of
`D01/DatumToJets.lean` (for instance lane 040's dedupe landing) will not be
caught by the standard gates; the U2 module has to be built explicitly.

---

## What was checked, and how

### 1. Build and hygiene

```
cd WT && bash scripts/lean-install.sh            # exit 0 ("== OK"), incl. `lake test`
. WT/scripts/lean-env.sh ; export LEAN_NUM_THREADS=6
cd WT/verification
lake build NSFormalization.Section4.C01.ForceSlices
  -> Build completed successfully (9879 jobs).        exit 0
```

Messages attributable to the file: **zero**.
`grep -c "Section4/C01/ForceSlices.lean" <build log>` → `0`;
`grep -ci error <build log>` → `0`. (The build log does carry warnings, but every
one of them is from pre-existing `NSFormalization/Paper3/*`,
`NSFormalization/Source/*` or vendor modules, not from this lane.)

Independent full re-elaboration of the file, which surfaces *all* of its own
diagnostics rather than replaying a cached olean:

```
lake env lean ../formalization/NSFormalization/Section4/C01/ForceSlices.lean
  -> (no output)                                       exit 0
```

Conformance and axioms:

```
lake env lean ../research/C01/axioms_u2.lean
  -> 'NSFormalization.Section4.C01.forceTimeRegularity' depends on axioms:
     [propext, Classical.choice, Quot.sound]           exit 0
```

The `example` typechecks (exit 0 with no error), so the spec-typed statement is
discharged.

Escape hatches:

```
grep -nE "sorry|admit|native_decide|axiom |maxHeartbeats" \
  formalization/NSFormalization/Section4/C01/ForceSlices.lean \
  research/C01/axioms_u2.lean
  -> no match (exit 1)
grep -n "set_option" <same two files>
  -> no match
```

Repository gates:

```
cd WT && make check
  -> check_formalization_plan.py / check_contracts.py / test_contract_policy.py
     (13 tests, OK) / check_work_queue.py ("30 work items: ownership, contract
     registration and task cards consistent")            exit 0
```

### 2. Spec conformance

`research/C01/Spec.lean` field `forceTimeRegularity` is at `:326-329`, and the
three supporting `def`s are at `:167` (`slice`), `:172` (`l2Sq`), `:177`
(`l2Norm`) — the line numbers the module and `axioms_u2.lean` cite are exact.

The three restatements are **byte-identical** across all three files (checked
programmatically, not by eye):

| def | Spec.lean == ForceSlices.lean | Spec.lean == axioms_u2.lean |
|---|---|---|
| `slice`  | True | True |
| `l2Sq`   | True | True |
| `l2Norm` | True | True |

The field statement and the theorem statement agree token-for-token modulo
indentation:

```
-- Spec.lean:326-329
forceTimeRegularity :
  ∀ f : SpaceTimeField, MemForceR f →
    (∀ t : ℝ, 0 ≤ t → MemLp (slice f t) 2 volume) ∧
      ContinuousOn (fun s => l2Norm (slice f s)) (Ici (0 : ℝ))

-- ForceSlices.lean:156-159
theorem forceTimeRegularity :
    ∀ f : SpaceTimeField, MemForceR f →
      (∀ t : ℝ, 0 ≤ t → MemLp (slice f t) 2 volume) ∧
        ContinuousOn (fun s => l2Norm (slice f s)) (Ici (0 : ℝ)) := by
```

The `example` in `axioms_u2.lean:37-41` restates that type in the spec's own
vocabulary (`BlowupDensity.Contracts.V1.Data.SpaceTimeField` / `.MemForceR`,
and its own copies of `slice`/`l2Sq`/`l2Norm`) and is closed by the bare term
`NSFormalization.Section4.C01.forceTimeRegularity` — **no extra hypotheses, no
tactic massaging**. That it elaborates is the real check that the A02
restatement of `MemForceR` is definitionally the contract's: both are `def`s
whose bodies I compared line by line (`SolutionClass.lean:86-92` vs
`Contracts/V1/Data.lean:544-550`) and they are identical text.

**Continuity is on `Ici 0`, endpoint included.** `Contracts/V1/Data.lean:113` is
`abbrev futureTimes : Set ℝ := Ici (0 : ℝ)` — `Ici`, not `Ioi` — and
`MemForceR` (`Data.lean:548`) asks for `ContDiffOn ℝ ∞ G futureTimes`, so the
*datum path* is smooth up to and including `t = 0`. `A02/SolutionClass.lean:59`
restates `futureTimes` verbatim. The proof takes `hGcont := hGsmooth.continuousOn
: ContinuousOn G (Ici 0)` and composes, so the conclusion genuinely covers
`t = 0`; there is no `Ioi 0` weakening anywhere, and the conjunct proved is
literally the spec's `ContinuousOn … (Ici (0 : ℝ))`. The lane's claim on this
point is correct, and the task brief's anticipated `t = 0` gap does not arise.

### 3. Dependency hygiene (the reason the lane was resumed)

Import list of `ForceSlices.lean` (lines 1-3) is exactly:

```
import NSFormalization.Section4.A02.SolutionClass
import NSFormalization.Section4.D01.DatumToJets
import NavierStokes.R3.LpNormTools
```

I computed the **transitive** import closure of
`NSFormalization.Section4.C01.ForceSlices` over `formalization/`,
`vendor/NavierStokesAndEuler/`, `vendor/HeliCorgi/` and `verification/`
(1386 in-repo modules resolved, 270 unresolved names being Mathlib/Batteries).
The only `Section4` modules in it are:

```
NSFormalization.Section4.A02.SolutionClass
NSFormalization.Section4.A05.SmoothJets
NSFormalization.Section4.C01.ForceSlices
NSFormalization.Section4.D01.DatumToJets
NSFormalization.Section4.D01.SmoothDatum
```

`NSFormalization.Section4.A02.Energy` is **not** in the closure. (Filtering the
closure for any module whose name contains `A02` or `Energy` returns only
`A02.SolutionClass` plus unrelated `Euler.*` / `NavierStokes.*` / `Source.*`
energy modules pulled in through the vendor packages — never `A02.Energy`.)
So the module would still compile with `Section4/A02/Energy.lean` deleted, which
is what lane 040's dedupe does. The independent re-elaboration
`lake env lean ../formalization/.../ForceSlices.lean` succeeding is the runtime
confirmation of the same thing. `A02/Energy.lean` is still present on this branch
and still carries `sliceLp` (`:110`), `sliceLp_ae` (`:162`) and its own
`memLp_of_isSobolevDatum` (`:175`) — the module simply no longer reaches them.
The only textual occurrence of `A02/Energy.lean` in the closure is a docstring
line in `SolutionClass.lean:21`, as `ATTEMPTS_U2.md` claims.

Every cited D01 lemma exists at the cited line **on this branch**:

| citation | actual | signature check |
|---|---|---|
| `jetOfDatum :196` | `DatumToJets.lean:196` | `def jetOfDatum (m j : ℕ) (hj : j ≤ m) (A : RealVectorSobolev (m : ℝ))` ✔ |
| `jetOfDatum_ae :202` | `DatumToJets.lean:202` | `theorem jetOfDatum_ae {m j : ℕ} (hj : j ≤ m) {z} (hz : ContDiff ℝ ∞ z) {A} (hA : IsSobolevDatum (m : ℝ) z A)` ✔ |
| `memLp_of_isSobolevDatum :267` | `DatumToJets.lean:267` | `theorem memLp_of_isSobolevDatum {m : ℕ} {z} (hz : ContDiff ℝ ∞ z) {A} (hA : …) : MemLp z 2 volume` ✔ |
| `contDiff_slice :366` | `DatumToJets.lean:366` | `theorem contDiff_slice {T} {v} (hv : ContDiffOn ℝ ∞ v (Ico (0:ℝ) T ×ˢ univ)) {t} (ht : t ∈ Ico (0:ℝ) T)` ✔ |

The `contDiff_slice_future` adapter is sound: `futureDomain` is
`Ici 0 ×ˢ univ` (`vendor/…/NavierStokes/ProblemStatement.lean:45`), the `.mono`
lands `ContDiffOn ℝ ∞ f (Ico 0 (t+1) ×ˢ univ)`, and `⟨ht, by linarith⟩` supplies
`t ∈ Ico 0 (t+1)` — so the horizon trick covers every `t ≥ 0` including `t = 0`.

The cast story checks out too: `MemForceR`'s `m`-th witness has order `(m : ℝ)`
with `m : ℕ`, and the whole proof is carried at `((0 : ℕ) : ℝ)` with every D01
call at `m := 0`, so no `((0 : ℕ) : ℝ) = 0` transport is needed anywhere. This is
cleaner than the `subst` device the pre-rewire version used.

The proof also does **not** use `MemLp G 1` / `MemLp G 2` over
`positiveTimeMeasure` (`obtain ⟨G, hpath, hGsmooth, _, _⟩`), which is correct:
the field is the purely local slicewise statement, as its docstring insists.

### 4. Honesty spot-checks of `ATTEMPTS_U2.md`

**Snag 1 — `PiLp.continuous_apply` needs explicit implicits: CONFIRMED.**
Probe `/tmp/probe_u2_a.lean`, the bare term in the exact context of the file:

```lean
example (i : Fin 3) :
    Continuous (fun A : RealVectorSobolev ((0 : ℕ) : ℝ) => A i) :=
  PiLp.continuous_apply i
```
```
error: Type mismatch
  PiLp.continuous_apply ↑↑i
has type
  ∀ (β : ?m.10 → Type ?u.11) [inst : (i : ?m.10) → TopologicalSpace (β i)]
    (i_1 : ?m.10), Continuous fun f => f.ofLp i_1
but is expected to have type
  Continuous fun A => A.ofLp i
```

That is precisely the "leftover `∀ β …` in the inferred type" the log describes,
and the committed fix
(`PiLp.continuous_apply (p := 2) (β := fun _ : Fin 3 => RealSobolevHilbert ((0 : ℕ) : ℝ)) i`,
`ForceSlices.lean:102-104`) elaborates.

**Snag 2 — the `Comparison.l2Sq` `show` fix: fix CONFIRMED, description
slightly wrong.** See finding 2. Both naive forms fail, so the `show` really is
load-bearing; only the recorded error message is not what actually happens.

No claim in `ATTEMPTS_U2.md` was found to overstate what was proved. The log is
explicit and correct that interval integrability of `s ↦ ‖f(s)‖₂` and
`‖f(s)‖₂²` on `[0,t]` is *not* proved and is not part of the field, matching the
field docstring at `Spec.lean:306-312`.

---

## Summary of commands

| command (cwd) | result |
|---|---|
| `bash scripts/lean-install.sh` (WT) | exit 0, `== OK` (includes `lake test`) |
| `lake build NSFormalization.Section4.C01.ForceSlices` (WT/verification) | exit 0, `Build completed successfully (9879 jobs).`, 0 messages from the file |
| `lake env lean ../formalization/NSFormalization/Section4/C01/ForceSlices.lean` (WT/verification) | exit 0, no output |
| `lake env lean ../research/C01/axioms_u2.lean` (WT/verification) | exit 0, `depends on axioms: [propext, Classical.choice, Quot.sound]` |
| `grep -nE "sorry\|admit\|native_decide\|axiom \|maxHeartbeats"` on both files | no match |
| `make check` (WT) | exit 0 |
| transitive import closure of the module | 1386 in-repo modules; `Section4.A02.Energy` absent |
| `/tmp/probe_u2_a.lean` (snag 1) | fails as recorded |
| `/tmp/probe_u2_b.lean`, `/tmp/probe_u2_c.lean` (snag 2) | both fail; failure mode differs from the log |
