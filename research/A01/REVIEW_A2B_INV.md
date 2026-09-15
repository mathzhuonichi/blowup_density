# Review — lane 134-A01-a2b-invariance (A01 unit A2b closed)

Reviewer run 2026-09-13, worktree `.claude/worktrees/134-A01-a2b-invariance`,
branch `erenup/134-A01-a2b-invariance`, one commit `237e898` on merge-base `e8decb6`.
Diff = 5 files (1 new Lean module, 1 new ATTEMPTS, 1 new axioms probe, 2 split-table rows).
Probes in `/tmp/rev134/` (volatile; every error text quoted verbatim below).

## Verdict: **ACCEPT-WITH-NOTES**

The Lean is correct, the statement is byte-faithful to `forced_global_of_bound'` minus `hinv`
(machine-checked two ways), the recorded heartbeat failure reproduces verbatim, and the
negative check confirms the invariance is genuinely *proved*, not smuggled.  The notes are all
documentation-level (one naming inconsistency the lane itself introduced, one dangling file
citation, one now-redundant probe).

---

## 1. Compiles / axioms / hygiene — **PASS**

```
$ . scripts/lean-env.sh ; cd verification
$ LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.A01.ContinuationInvariant
Build completed successfully (3942 jobs).

$ lake env lean ../formalization/NSFormalization/Section4/A01/ContinuationInvariant.lean
exit=0   bytes=0            # silent: no warning, no `sorry` warning, no unused-variable noise

$ lake env lean ../research/A01/axioms_a2b_inv.lean          # exit=0
'NSFormalization.Section4.A01.restart_window_invariance' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.exists_uniform_restart_time_invariant' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.gluePath_invariant' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.forced_global_mild_of_bound_invariant' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.forced_global_of_bound_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound]
```
Both non-vacuity `example`s in the audit file elaborate (exit 0, no error lines).

```
$ make check   → exit=0  (contracts frozen, 13 policy tests OK, "30 work items: ownership,
                          contract registration and task cards consistent.")
$ make test    → exit=0  ([10123/10123] Replayed Tests.DatumLemmasV3 … "standard logical
                          axioms only")   # unchanged: the module is not yet in a contract closure
$ grep -rnE "sorry|admit|native_decide|axiom" <module> <axioms file>
  → single hit: the word "axiom" inside the audit file's docstring.  No `sorry`, no `admit`,
    no `native_decide`, no `axiom` declaration.
$ grep -n "set_option" formalization/.../ContinuationInvariant.lean
  60:set_option maxHeartbeats 600000 in            # the only one, single-declaration, commented
```

**F1 (info, confirms the record).  `400000` really fails.**  `/tmp/rev134/hb400.lean` = the
module with the single `600000` replaced by `400000`:
```
$ lake env lean /tmp/rev134/hb400.lean            # exit=1
/tmp/rev134/hb400.lean:139:8: error: (deterministic) timeout at `isDefEq`, maximum number of heartbeats (400000) has been reached
/tmp/rev134/hb400.lean:61:0: error: (deterministic) timeout at `whnf`, maximum number of heartbeats (400000) has been reached
/tmp/rev134/hb400.lean:156:8: error: (kernel) unknown constant 'NSFormalization.Section4.A01.restart_window_invariance'
```
Line 139 is `rw [hcov, heatKernel_translation]` inside the translated Duhamel integrand — the
`isDefEq` blow-up the lane-126 reviewer measured.  `600000` is justified, not heartbeat-chasing.

## 2. Statement fidelity — **PASS**

**(a) `forced_global_of_bound_unconditional` vs `Continuation.forced_global_of_bound'`.**
Two independent machine checks.

*Syntactic* (`/tmp/rev134/fidelity.lean`, `set_option pp.fullNames true`, both `#check @…`,
then whitespace-normalised and the `hinv` binder excised by script):
```
REMOVED hinv BLOCK: (∀ (u : C(↑(Set.Icc 0 S), ↥(EulerCylinderSobolevSpace.SobolevSpace 1 (q + 1)))),
  ‖u‖ ≤ R → (∀ (t : ↑(Set.Icc 0 S)), u t = …quadraticDuhamel…) →
  ∀ (θ : AddCircle 1) (t : ↑(Set.Icc 0 S)), (…sobolevTranslation 1 (q + 1) (0, θ)) (u t) = u t) →
EQUAL after removing hinv: True
```
Every other binder — `hq hν hS hR a ha F hF hu₀ hbound` — and all seven conclusion clauses are
character-for-character identical.

*Definitional* (`/tmp/rev134/defeq.lean`): with all of `'`'s binders in context,
`have h1 := forced_global_of_bound_unconditional …; have h2 := forced_global_of_bound' … hinv;
have : h1 = h2 → True := fun _ => trivial` elaborates.  This matters beyond the pp diff: the two
modules each install their **own** `local instance : Fact (0 < (1:ℝ))`, so `SobolevSpace 1 (q+1)`
carries different instance terms in the two statements; the `Eq` forces them to unify (Prop proof
irrelevance), ruling out an instance-level drift that pretty-printing hides.

**(b) The invariance clause is the `exists_local` one.**  `Source/ForcedCylinderInvariant.lean:43`
(`exists_local_forced_mild_invariant`, last clause) reads
`∀ (θ : AddCircle period) t, sobolevTranslation period (q + 1) (0, θ) (u t) = u t` with
`variable (period : ℝ) [Fact (0 < period)]` (`:10`).  At `period := 1` this is exactly the lane's
clause: quantified over **all** `θ : AddCircle 1`, i.e. the full auxiliary-angle circle group, not
a subgroup, not a fixed θ, not a "for some θ".  Same `sobolevTranslation 1 (q+1) (0, θ)` at the
same order `q+1`.

**(c) `hbound` is the vendor's hypothesis verbatim.**  `Euler/BoundedMildContinuation.lean:41-44`
has it at `period`/`C`/`u₀`; the lane's step 3 is its instantiation at
`period := 1`, `C := coefficients 1 hq (sobolevPath F hF q)`,
`u₀ := ordinarySobolev (q+1) a.toLp a.translation_contDiff` — identical to lane 126's
`forced_global_mild_of_bound`, which is a one-line application of the vendor theorem.  The
machine diff in (a) covers it: `hbound` is inside the identical part.  **Nothing was weakened or
strengthened in `hbound`.**

**(d) Non-vacuity.**  The audit file's two `example`s (zero data: `ha` divergence-free, `hu₀` at
every `R ≥ 0`) elaborate.  Additionally `/tmp/rev134/nonvac.lean` (exit 0) shows both premises are
satisfiable at an **arbitrary, possibly nonzero** datum `a : SmoothL2Field Space`:
`ordinarySobolev_angle (q+1) a.toLp a.translation_contDiff θ` proves the datum invariance the
induction uses **with no hypothesis on `a` at all** (`Source/OrdinaryCylinderDescent.lean:71`),
and `hu₀` holds by `le_rfl` at `R := ‖ordinarySobolev …‖`.  So nothing in the new module is
secretly zero-only.
*Limit of this evidence (unchanged from lane 126, not a new defect — see F5.)*

**(e) Negative check — the invariance is not obtainable from the unprimed route.**
`/tmp/rev134/negative.lean` states the unconditional conclusion and tries
`apply forced_global_of_bound' hq hν hS hR a ha F hF hu₀ hbound; assumption`:
```
/tmp/rev134/negative.lean:38:2: error: Tactic `assumption` failed
…
hbound : ∀ (T : ℝ) (hT : 0 ≤ T) (hTS : T ≤ S) (u : C(↑(Icc 0 T), ↥(SobolevSpace 1 (q + 1)))), … → ‖u‖ ≤ R
⊢ ∀ (u : C(↑(Icc 0 S), ↥(SobolevSpace 1 (q + 1)))), ‖u‖ ≤ R → (∀ (t : ↑(Icc 0 S)), u t = quadraticDuhamel …) →
    ∀ (θ : AddCircle 1) (t : ↑(Icc 0 S)), (sobolevTranslation 1 (q + 1) (0, θ)) (u t) = u t
```
The `hinv` goal survives and nothing in context closes it — the lane's claim "re-assembly, not
`apply`" is accurate, and indeed its step 4 re-runs `forced_mild_divergenceFree` /
`forced_ordinary_descent` on the *invariant* `u` from step 3.

**No hidden global uniqueness.**  `mild_solution_unique`
(`Euler/VolterraUniqueness.lean:22-31`) is used exactly once, inside
`restart_window_invariance`, at the **window** length `T` with
`hsmall : kernelMass T (parabolicKernelBound ν) * C.ballLipschitz R < 1` *derived* from
`T ≤ δ` and `exists_positive_time_budget` (module lines 89-93), never at `S`.  Cross-checked
the vendor side: `EulerUniformHeatLocal.exists_uniform_restart_time`
(`Euler/UniformHeatLocal.lean:40-45`) obtains its own `δ` from
`exists_positive_time_budget ν (C.ballBound (R+1)) (C.ballLipschitz (R+1)) 1 S` — so the lane's
ATTEMPTS claim that the vendor window already lives in the `(R+1)` contraction regime is **true
as recorded**; the `min δ₁ δ₂` is defensive, not load-bearing (either alone would do, but the
vendor witness is opaque from outside, so `min` is the right engineering call).

**Step 3 is a faithful fork.**  Line-by-line against
`Euler/BoundedMildContinuation.lean:49-83`: same `hind : ∀ n` scaffolding, same
`min ((n:ℝ)*δ) S ≤ a'` grid invariant, same `b := min δ (S-a')`, same `advance_grid`, same
`quadratic_mild_window_iff` base, same `glue_quadratic_mild` step, same
`exists_nat_ge (S/δ)` / `min_eq_right` / `subst` terminal, same final `simpa only [...]` for the
initial value.  The only additions are the fourth conjunct of the inductive existential and its
four discharges (base = `ordinarySobolev_angle`, restart = IH, step = 1b, glue = 2).

## 3. Consistency — **PASS with two doc notes**

* Imports: the module imports **only** `NSFormalization.Section4.A01.Continuation` (one line);
  everything else is reached through `open`.  No vendor definition is restated — `grep -nE
  "^\s*(def|structure|abbrev|instance|axiom) "` returns nothing but the `local instance : Fact`
  (needed because `Continuation.lean:89`'s is `local`).  `gluePath` / `glueFunction_left` /
  `glueFunction_right` / `advance_grid` / `glue_quadratic_mild` / `quadratic_mild_window_iff` /
  `mild_solution_unique` are all used from their vendor homes.
* `Contracts/`, `Bindings/`, `Tests/`, `contracts.json`, `work_items.json`, `TASKS.md`,
  `AGENT_RUNS.csv` untouched; `make check` and `make test` unchanged and green.

**F2 (low, MAINT).  `research/A01/probes/probe_restart_window_invariance.lean` is now fully
redundant.**  Machine-checked: the probe's theorem body and the module's lines 69-146 are
**byte-identical** after renaming the theorem
(`diff <(sed 's/probe_restart_window_invariance/restart_window_invariance/' probe) module_lines`
→ empty, 78 lines each).  "Promoted verbatim and credited" is exactly true.  Suggest the lead
either delete the probe in a later MAINT sweep or add one line to it saying it is superseded by
`Section4/A01/ContinuationInvariant.lean:69`.  (`probe_window_invariance.lean` and
`a2b_invariant_port.lean` remain useful as the non-restart / smaller-budget variants.)

**F3 (low, doc).  The `A2b-b → A2b-c` rename is only half-applied inside `A3_SPLIT.md`.**
The table rows are consistent (`A2b-a` = "reviewer §3 A2b-b" = this lane, `A2b-c` = cross-order),
and they agree with `A01_SPLIT.md:87` ("lane 134, row A2b-b" = invariance) and with
`REVIEW_A2B.md:529` ("★ Row A2b-b — invariance-carrying forced continuation") and
`ATTEMPTS_A2B.md:92` ("Remaining work — row A2b-b").  But two prose lines in the *same file* still
use the freed name in its old (cross-order) sense:
* `A3_SPLIT.md:168` — "**Cross-order agreement** (A2b-b): `A02.uniqueness` pins the two orders…"
* `A3_SPLIT.md:192` — "* **A2b-b** — an `A02.uniqueness` application."

so `A3_SPLIT.md` now says both "A2b-b = invariance (done)" and "A2b-b = cross-order (open)".
Fix = change those two occurrences to `A2b-c`.  (`REVIEW_A3.md:296`'s "Row A2b-b" is a frozen
historical review and should be left alone.)  Grep used:
`grep -rn "A2b-b\|A2b-c\|A2b-a" research/A01/*.md`.

## 4. Honesty of ATTEMPTS — **PASS with one dangling citation**

* "400000 fails" — reproduced verbatim, F1 above.
* "`δ = min` black-box design" — verified against both black boxes' actual sources
  (`UniformHeatLocal.lean:29-45`, module lines 171-180); the stated reason (both windows fire
  under `le_trans hTδ (min_le_left/right)`) is what the proof does, and the stated consistency
  argument about `C.ballBound (R+1)` is factually correct (see §2).
* "first-try compile, no failed Lean approaches" — plausible and consistent with the fact that
  the module is the reviewer's two checked probes plus a verbatim vendor fork; nothing in the
  diff suggests otherwise.
* "the `lake env lean` on `axioms_a2b_inv.lean` first failed with
  `object file … Euler/OrdinaryCauchyInterpolation.olean … does not exist`" — consistent; I had
  to build the same four `Euler.*` modules in this worktree before the audit file ran.

**F4 (low, doc).  ATTEMPTS cites a file that does not exist.**
`ATTEMPTS_A2B_INV.md` §"First-try compile" cites `research/A01/cont_inv_draft.lean`; the worktree
is clean (`git status --short` empty) and that path is absent.  This is the `LESSONS.md`
2026-09-14 rule about citing volatile probe paths.  Fix = reword to "a scratch draft, checked with
`lake env lean` and discarded" (no file should be added; the committed module supersedes it).

**F5 (info, inherited — not a defect of this lane).  The full theorem has still never been
instantiated.**  `hbound` is nobody's theorem yet, so no `example` anywhere produces
`forced_global_of_bound_unconditional`'s conclusion for concrete data; the non-vacuity evidence
covers `ha`, `hu₀` and the datum-invariance only.  Producing `hbound` even for zero data would
itself need the global uniqueness this lane deliberately avoids, so this is genuinely A3's job,
exactly as the lane says.  Recorded so the next reviewer does not re-derive it.

---

## 5. For the lead — what A3 can now consume

### 5.1 Rows whose blocker this lane removed

| row | before | now |
|---|---|---|
| **A3-L2** (choose `T₀`, define `horizon`) | "open (dissolved by F5)", input A2b-a′ | **ready, S.**  `forced_global_of_bound_unconditional` hands the *whole* prescribed `[0,S]` with all seven `exists_local` clauses from `hbound` alone, so `horizon := S` needs no choice over `exists_local`'s `∃ T` and no `hinv` side condition.  This is the row to schedule next if one wants a visible A3 deliverable without waiting on A04. |
| **A3-Tm** (order-`m` solution on the shared `T₀`) | "gap", input A2b-a′ | **structurally unblocked, still M.**  At each fixed `q` the unconditional theorem gives a solution on all of `[0,S]`; what is still missing is (i) `hbound` at each order and (ii) the cross-order handle (`A2b-c`), since `q` is fixed throughout. |
| **H1** (`horizon_lower_bound`) | lead = `forced_uniform_restart_time` | lead **upgraded** to `exists_uniform_restart_time_invariant` — same shape plus the invariance clause.  Still *not literally H1* (order-`q+1` cylinder `‖u₀‖ ≤ R`, not `‖a‖_{H¹}` + `‖f‖_{L¹H¹}`); that caveat is unchanged. |

Unchanged by this lane: **A2 / A3-M1 / A3-M2** (blocked on A04 `hpr`), **A3-L1·k** (blocked on
119's C1b-m-D + the new one-directional norm comparison), **A3-L1·f** (open S, independent),
**A2b-c** (open), **T1** (waits on A3).

### 5.2 The exact shape of `hbound` A3 must supply

```lean
hbound : ∀ (T : ℝ) (hT : 0 ≤ T) (hTS : T ≤ S) (u : C(Icc (0:ℝ) T, SobolevSpace 1 (q+1))),
  (∀ t, u t = quadraticDuhamel 1 ν hν hT hTS
      (coefficients 1 hq (sobolevPath F hF q))
      (ordinarySobolev (q+1) a.toLp a.translation_contDiff) u t) → ‖u‖ ≤ R
```
In D01-carrier terms:

* `a : SmoothL2Field Space` is the R³ smooth `L²` datum; the initial vector is its **cylinder
  lift at order `q+1`**, `ordinarySobolev (q+1) a.toLp a.translation_contDiff`.
* the force is `F : Icc 0 S → SmoothL2Field Space` with `hF : ∀ n, Continuous (·.jetLp n)`,
  lifted to the order-`q` path `sobolevPath F hF q`.
* `‖u‖` is the **`ContinuousMap` sup-norm over the closed `Icc 0 T`** of the cylinder norm
  `‖·‖_{SobolevSpace 1 (q+1)}`, i.e. `sup_{t ∈ [0,T]} ‖u t‖_{H^{q+1}-cylinder}`.
* `R` is chosen **before** `T` and `u` (and must also dominate the datum, via `hu₀`), and the
  quantification is over *every* Duhamel solution on *every* subwindow, not only the constructed
  one — the same quantifier-order point A02 `restart` makes.

Three shape mismatches the A3 lane should plan for (none is new, but they are now the only thing
between `hbound` and a closed A01 spine):

1. **Norm side.**  `Propagation.lean`'s Grönwall outputs are abstract in `y : ℕ → ℝ → ℝ`, but the
   intended instantiation (A04) is the R³-side `sobolevNormAt m (⇑(U t))`, whereas `hbound` needs
   the **cylinder** `‖u t‖_{SobolevSpace 1 (q+1)}`.  Row **A3-L1·k** supplies
   `sobolevNormAt 2 (⇑(U t)) ≤ c·‖u t‖` — the *converse* direction.  A comparison
   `‖u t‖ ≤ c'·(finitely many sobolevNormAt m (⇑(U t)))` is **not currently a row in
   `A3_SPLIT.md`** and should be added.
2. **Interval side.**  Grönwall delivers on the half-open `Ico 0 T₀` (`gronwall_bddAbove_Ico`,
   `higherOrder_bddAbove`); `hbound` needs the closed `Icc 0 T` for every `T ≤ S`, endpoint
   included.  Harmless if `T₀` is taken `> S`, but it has to be said somewhere.
3. **Mild ⟹ energy.**  `hbound` quantifies over an arbitrary *mild* (Duhamel) solution, while
   eq:Rhigh is an energy identity for a regular solution.  Supplying `hbound` therefore needs the
   mild→strong bridge (A02 / T1 territory), not just the Grönwall arithmetic.  Worth an explicit
   row rather than leaving it implicit inside "A2".

Good news for the uniformity requirement: `gronwall_bddAbove_Ico`'s bound
`(y 0 + Bbnd)·exp(Cgron·Kbnd)` is **explicit and solution-independent** once `Kbnd`, `Bbnd` are,
so the "`R` before `u`" quantifier order is reachable — it is `Kbnd` (A3-L1·k) that currently is
not uniform.

### 5.3 Does the H1 lead's `δ` compose with this lane's `δ`?  — **precisely: no, they are two
different witnesses; use the invariant one and drop the other.**

* `Continuation.forced_uniform_restart_time` (`Continuation.lean:249-263`) is literally
  `exists_uniform_restart_time 1 q ν hν S hS R hR (coefficients 1 hq (sobolevPath F hF q))`, i.e.
  it re-exports the **vendor witness δ₁**.
* `exists_uniform_restart_time_invariant` returns **`min δ₁' δ₂`**, where `δ₁'` is an
  independently obtained witness of the *same* vendor existential and `δ₂` comes from
  `restart_window_invariance (R := R+1)`.

Both existentials are opaque: **there is no lemma in the tree equating `forced_uniform_restart_time`'s
`δ` with `exists_uniform_restart_time_invariant`'s**, and none can be written, because both are
`∃`-witnesses.  Mathematically they are the *same* construction — both trace back to
`exists_positive_time_budget ν (C.ballBound (R+1)) (C.ballLipschitz (R+1)) 1 S` — but that is
invisible at the statement level.

Consequence for A3/H1: **consume `exists_uniform_restart_time_invariant` only**; do not obtain
both and try to relate them.  Its statement is `forced_uniform_restart_time`'s plus one extra
hypothesis (`∀ θ, sobolevTranslation 1 (q+1) (0,θ) u₀ = u₀`) and one extra conclusion clause.  The
extra hypothesis is **free on the H1 route**, since every datum there is a cylinder lift and
`OrdinaryCylinderDescent.ordinarySobolev_angle` proves its invariance unconditionally — verified
in `/tmp/rev134/nonvac.lean` for an arbitrary `a`.  So the invariant version is a strict upgrade
in practice, and `forced_uniform_restart_time` can be left as the historical lead.

---

## 6. Commands run (all from the lane worktree, after `. scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`)

| command | result |
|---|---|
| `cd verification && lake build NSFormalization.Section4.A01.ContinuationInvariant` | `Build completed successfully (3942 jobs).` |
| `lake build Euler.OrdinaryCauchyInterpolation Euler.OrdinaryH3Norms Euler.SmoothL2Series Euler.LpSmoothFieldAlgebra` | success (prerequisite of the audit file) |
| `lake env lean ../formalization/NSFormalization/Section4/A01/ContinuationInvariant.lean` | exit 0, 0 bytes |
| `lake env lean ../research/A01/axioms_a2b_inv.lean` | exit 0, 5× standard three axioms, both examples elaborate |
| `lake env lean /tmp/rev134/hb400.lean` (600000 → 400000) | exit 1, `isDefEq` timeout at `:139:8` (quoted §1) |
| `lake env lean /tmp/rev134/fidelity.lean` + python normalise/diff | `EQUAL after removing hinv: True` |
| `lake env lean /tmp/rev134/defeq.lean` | example 1 (`h1 = h2` type unification) elaborates |
| `lake env lean /tmp/rev134/negative.lean` | exit 1, `assumption` fails on the surviving `hinv` goal (quoted §2e) |
| `lake env lean /tmp/rev134/nonvac.lean` | exit 0 (arbitrary-datum invariance + `hu₀`) |
| `make check` | exit 0 |
| `make test` | exit 0, `[10123/10123]`, "standard logical axioms only" |
| `diff` probe vs module lines 69-146 | empty (byte-identical, 78 lines) |
| `grep -rn "A2b-b\|A2b-c\|A2b-a" research/A01/*.md` | F3 above |
| `git status --short` | empty |

## 7. Actions requested before merge (all optional, none blocking)

1. **F3** — change `A3_SPLIT.md:168` and `:192` "A2b-b" → "A2b-c" (the lane freed the name; two
   prose lines in the same file still use the old sense).
2. **F4** — reword the `research/A01/cont_inv_draft.lean` citation in `ATTEMPTS_A2B_INV.md`
   (file does not exist).
3. **F2** — MAINT: mark or delete `research/A01/probes/probe_restart_window_invariance.lean`
   as superseded (now byte-identical to the merged theorem).
