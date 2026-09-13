# REVIEW — lane 114-R42-lifespan-v2 (`R42.insertion_lifespan_v2`)

Reviewer: opus reviewer (lane 114). Worktree
`/data_8T/ping/blowup_density/.claude/worktrees/114-R42-lifespan-v2`, branch
`erenup/114-R42-lifespan-v2`, HEAD `8e82e9b`, merge-base with
`origin/erenup/integration` = `d3f7060`. Probes in `/tmp/rev114/`. No
state-changing git was run; nothing outside this file was written.

## Verdict: **ACCEPT**

All four gates are green, the three new fields are faithful to the manuscript
(two are the theorem's own displays, one is the proof-step identification of
04:53), the binding introduces no hypothesis beyond version one's, and the
`ATTEMPTS` record is honest (its single recorded failure reproduces verbatim).
Six findings follow; **none blocks the merge** — F4 and F5 are one-sentence
`scope` additions the lead may fold in at merge time or leave to the next R42
lane, F6/F7 are cosmetic, F1/F2/F3 are confirmations.

---

## 1. Compiles / policy

### 1.1 Commands and tail output

```
$ . scripts/lean-env.sh && cd verification && LEAN_NUM_THREADS=6 lake build Tests.InsertionLifespanV2
EXIT=0
ℹ [9975/9975] Replayed Tests.InsertionLifespanV2
info: Tests/InsertionLifespanV2.lean:32:0: Contract BlowupDensity.Tests.checkedInsertionLifespanV2: checked; standard logical axioms only
Build completed successfully (9975 jobs).
```

```
$ make check
EXIT=0
python3 experiments/test_contract_policy.py
.............
Ran 13 tests in 0.043s
OK
python3 experiments/check_work_queue.py
30 work items: ownership, contract registration and task cards consistent.
```
(`check_contracts.py` inside `make check` lists `Tests.InsertionLifespanV2` in
the closure; `base_compatibility_checked: false` there, since `make check`
passes no base ref — checked separately in 1.3.)

```
$ make test
EXIT=0
$ grep -c "checked; standard logical axioms only" /tmp/rev114/test.log
20
$ grep -iE "error:" /tmp/rev114/test.log
(no output)
ℹ [10070/10070] Replayed Tests.InsertionLifespanV2
info: Tests/InsertionLifespanV2.lean:32:0: Contract BlowupDensity.Tests.checkedInsertionLifespanV2: checked; standard logical axioms only
```
All 20 registered contracts check; `R42.insertion_lifespan_v2` is the 20th.

```
$ make test-mutations
EXIT=0
implementation_refactor: accepted
admitted_proof: rejected as required
extra_axiom: rejected as required
weakened_hypothesis: rejected as required
Mutation suite passed. This is an infrastructure check, not a PDE proof.
```

```
$ python3 experiments/check_contracts.py --base-ref origin/erenup/integration
EXIT=0
{'registered_contracts': 20, 'base_compatibility_checked': True,
 'scope': 'Architecture checks only; run lake test for Lean type and axiom checks.'}
```

```
$ cd verification && lake env lean ../research/R42/axioms_contract_v2.lean
'BlowupDensity.Bindings.InsertionLifespan.blowup_essSup' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.InsertionLifespan.insertionLifespanV2API' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.InsertionLifespan.insertionLifespanV2API_family' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### 1.2 Diff surface

`git diff origin/erenup/integration...HEAD --stat` (three-dot; the two-dot diff
is misleading because the lane branched before 110/`B02` merged):

```
 collaboration/TASKS.md                           |   2 +-
 collaboration/tasks/R42.md                       |   2 +-
 collaboration/work_items.json                    |   3 +-
 research/R42/ATTEMPTS_CONTRACT_V2.md             | 101 +++++++++++++
 research/R42/axioms_contract_v2.lean             |  19 +++
 verification/Bindings/InsertionLifespanV2.lean   |  95 ++++++++++++
 verification/Contracts/V2/InsertionLifespan.lean | 182 +++++++++++++++++++++++
 verification/Tests/InsertionLifespanV2.lean      |  92 ++++++++++++
 verification/contracts.json                      |  11 ++
 9 files changed, 504 insertions(+), 3 deletions(-)
```

* **No file under `Contracts/V1` is touched.** No existing `Tests/` module is
  touched (only the new `Tests/InsertionLifespanV2.lean` is added). No existing
  `Bindings/` module is touched — in particular `Bindings/InsertionLifespan.lean`
  is byte-unchanged, so `Tests.InsertionLifespan` keeps running against the
  frozen version-one witness.
* **`contracts.json` is purely additive**: the diff is the 11-line new entry plus
  the one `-` line of the `--- a/` header; no pre-existing `scope` string churns.
* `logs/AGENT_RUNS.csv` and `PLAN.md` are untouched by the lane — correct, those
  are the lead's at merge time.
* Ledger change is the standard claim+render shape: one id appended to R42's
  `contracts` list in `work_items.json`, `TASKS.md` and `tasks/R42.md`
  regenerated.

### 1.3 Token grep

```
$ grep -nE "sorry|admit|\baxiom\b|native_decide|set_option|maxHeartbeats" \
    verification/Contracts/V2/InsertionLifespan.lean \
    verification/Bindings/InsertionLifespanV2.lean \
    verification/Tests/InsertionLifespanV2.lean \
    research/R42/axioms_contract_v2.lean
(none in any of the four)
```

---

## 2. Statement fidelity — the three new fields

Manuscript, `paper/sections/04-whole-space.tex` (read only, never edited):

* `:32` "there are $g_\eps\in\mathcal F_{\R}$ and **a solution** $u_\eps$ such that"
* `:34` $T^\nu_{\max,\R}(a,g_\eps)=T$  (version one's `lifespan`)
* `:35` $\limsup_{t\uparrow T}\norm{u_\eps(t)}_\infty=\infty$
* `:53` (inside the proof) "Proposition~\ref{prop:local} identifies the solution
  with the unique maximal solution."

`research/section4/STATEMENTS.md`: `:346` `⟪D01:IsMaximalSolution⟫ ν a (gPert ε)
(uPert ε) (pPert ε)`; `:348-350` `⟪D01:limsupLeft⟫ T (fun t => ⟪D01:normLinfty⟫
(uPert ε t)) = ⊤` with the explicit rider "do not substitute the equivalent
`¬ BoundedNear` restatement". `:333` is version one's `referenceLifespan`. All
line citations in the contract docstring, the binding docstring and the
`contracts.json` scope were spot-checked and are **accurate**
(`Contracts/V1/MaximalPartial.lean:101,106` = the `limsupLeft`/`speedENorm`
`def`s; `Bindings/MaximalPartial.lean:57,61` = the two `rfl` bridges;
`Bindings/InsertionLifespan.lean:215-217,319,349` = `hblow`, `sol_fullHorizon`,
`isMaximalSolution_of_inserted`; `REVIEW_CONTRACT.md:386-387,443-452` = the three
gaps this lane closes).

### (a) `blowup_limsup` — **exactly the second display of `:35`**, in the stronger reading

```lean
blowup_limsup : ∀ ε ∈ Ioc (0 : ℝ) family.ε₀,
  Contracts.V1.MaximalPartial.limsupLeft family.T
      (fun t => Contracts.V1.MaximalPartial.speedENorm
        (fun x : Space => family.velocity ε (t, x))) = ⊤
```

Both operators are the **frozen** `Contracts/V1/MaximalPartial` ones:

```lean
def limsupLeft (T : ℝ) (φ : ℝ → ℝ≥0∞) : ℝ≥0∞ := Filter.limsup φ (nhdsWithin T (Iio T))
def speedENorm (z : SpatialField) : ℝ≥0∞ := eLpNorm z ⊤ (volume : Measure Space)
```

Probe `/tmp/rev114/fidelity.lean` (compiles clean, no output beyond the requested
`#print axioms`):

* `speedENorm z = essSup (fun x => ‖z x‖ₑ) volume` — proved by
  `rw [speedENorm, eLpNorm_exponent_top, eLpNormEssSup]`. It is a genuine
  **essential supremum**, i.e. literally $\norm{\cdot}_{L^\infty}$.
* `essSup f volume ≤ ⨆ x, f x` — proved. Hence `essSup = ⊤ ⟹ sup = ⊤`: the
  essSup rendering is the **stronger** half of the pair, never weaker. (For the
  continuous slices this record co-carries via `velocity_smooth` the two are
  equal, so it is *the* display; but the direction that matters for safety is the
  one proved above, and it holds unconditionally.)
* `limsupLeft T φ = Filter.limsup φ (𝓝[<] T)` by `rfl`, and `(𝓝[<] T).NeBot` by
  `infer_instance`. So this is the genuine left-hand `limsup` over the filter, **not**
  a limsup along some chosen sequence, and `= ⊤` cannot be satisfied vacuously by
  a trivial filter.

Classification: **exactly the manuscript display** (up to the slice notation
`fun x => family.velocity ε (t, x)`, forced because `InsertionFamilyAPI.velocity`
is spacetime-valued, matching `Data.ClassicalSolutionR.velocity`). The lane's
`ATTEMPTS` fidelity note and the `scope` fidelity note both say exactly this and
are correct. This closes gap 1 of `REVIEW_CONTRACT.md:443-446`: version one
registered the blow-up only in the pointwise `SpeedUnboundedAt` form, whose own
docstring (`Contracts/V1/InsertionFamily.lean:282-287`) concedes it is "in
isolation the **weaker** one".

### (b) `maximal` — the `:53` identification; correct predicate, with one caveat

`Contracts.V2.MaximalPartial.IsMaximalSolution ν a f u p` unfolds to

```lean
0 < maximalLifespanR ν a f ∧
  ∀ S : ℝ, 0 < S → ENNReal.ofReal S < maximalLifespanR ν a f →
    ∃ w : ClassicalSolutionR ν a f S, w.velocity = u ∧ w.pressure = p
```

i.e. *lifespan positive* + *`(u,p)` are literally the velocity/pressure of a
classical solution on `[0,S)` for every `S` below the maximal lifespan*. That is
`⟪D01:IsMaximalSolution⟫` at the mandated arity `ν a f u p`
(`STATEMENTS.md:1198`, `:346`), and it is the registered predicate of
`A02.maximal_partial_v2`. Combined with the inherited `lifespan`
(`maximalLifespanR ν a (force ε) = ENNReal.ofReal T`) the pair is identified as
*a* maximal solution whose $T^\nu_{\max,\R}$ is exactly `T` — probe §3 of
`/tmp/rev114/fidelity.lean` extracts the conjunction off an arbitrary record.

**Caveat (F4 below).** `IsMaximalSolution` does not itself contain the word
"unique". The manuscript's `:53` says "the **unique** maximal solution"; the
uniqueness half is A02's `maximal_unique`, a field of
`Contracts.V2.MaximalPartial.MaximalPartialV2API` (contract
`A02.maximal_partial_v2`), which this record does **not** carry as a field. A
consumer needs both contracts to reproduce the full sentence of `:53`. The scope
string does not say so.

Classification: **definitional rendering of the `:53` proof step**, exactly as
strong as the registered predicate, no stronger and no weaker. Note it is a
*proof-step* conclusion (line 53 sits inside `\begin{proof}`), not one of the
theorem's four displays — legitimate, and the docstring cites `:53` honestly.

### (c) `solution` — pins `velocity`/`pressure` to the family's own fields

```lean
solution : ∀ ε ∈ Ioc (0 : ℝ) family.ε₀,
  ∃ w : Data.ClassicalSolutionR ν family.a (family.force ε) family.T,
    w.velocity = family.velocity ε ∧ w.pressure = family.pressure ε
```

The two equations are what make this not a bare existence claim: the solution
whose existence is asserted **is** the family's `u_ε`, `p_ε`, not some other
solution of the same datum. `ClassicalSolutionR … family.T` is the horizon
`[0,T)` itself (`Contracts/V1/Data.lean:624-648`: `velocity_smooth`,
`pressure_smooth`, `divergence`, `sobolev`, `pressure_gradient` all on
`Ico 0 T`), so this is genuinely the **full-horizon** object, strictly more than
`IsMaximalSolution`'s family of per-`S` solutions for `S < T`.

Verified by probe that the two previously-unexported `ClassicalSolutionR` fields
really come back out for `u_ε`/`p_ε` on all of `[0,T)`:

```lean
example … : ∀ m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
    ContinuousOn G (Ico (0:ℝ) A.family.T) ∧
      ∀ t ∈ Ico (0:ℝ) A.family.T,
        IsSobolevDatum (m:ℝ) (fun x => A.family.velocity ε (t, x)) (G t) := by
  obtain ⟨w, hv, _⟩ := A.solution ε hε; simpa [hv] using w.sobolev
example … : ∀ t ∈ Ico (0:ℝ) A.family.T,
    MemLp (fun x => pressureGradient (A.family.pressure ε) t x) 2 volume := by
  obtain ⟨w, _, hp⟩ := A.solution ε hε; simpa [hp] using w.pressure_gradient
```
Both compile. This closes gap 3 of `REVIEW_CONTRACT.md:386-387,450-452`; the
scope's "NOT asserted: `sobolev` and `pressure_gradient` … still not stated as
fields (a consumer derives them by opening the `solution` field's
`ClassicalSolutionR`)" is exactly right.

Classification: **`:32`'s "there are `g_ε ∈ F_R` and a solution `u_ε`" as a
definitional rendering**, with the identity equations making it stronger than the
bare existential.

### (d) No new hypotheses

```
$ cd verification && lake env lean ../research/R42/axioms_contract_v2.lean
@insertionLifespanV2API : {ν : ℝ} → {P : BlowupDensity.Contracts.V1.PacketAPI ν} →
  (F : BlowupDensity.Contracts.V1.InsertionFamilyAPI ν P) →
    BlowupDensity.Contracts.V1.Data.MemForceR F.g →
      BlowupDensity.Contracts.V1.Data.RegularThrough ν F.a F.g (F.T + F.margin) →
        BlowupDensity.Contracts.V2.InsertionLifespan.InsertionLifespanV2API ν P
@insertionLifespanAPI  : {ν : ℝ} → {P : BlowupDensity.Contracts.V1.PacketAPI ν} →
  (F : BlowupDensity.Contracts.V1.InsertionFamilyAPI ν P) →
    BlowupDensity.Contracts.V1.Data.MemForceR F.g →
      BlowupDensity.Contracts.V1.Data.RegularThrough ν F.a F.g (F.T + F.margin) →
        BlowupDensity.Contracts.V1.InsertionLifespan.InsertionLifespanAPI ν P
```

Identical binder-for-binder except the return type. **Claim confirmed.** The
statement-level check is the same: `insertionLifespanV2Statement` takes exactly
`F`, `Data.MemForceR F.g`, `Data.RegularThrough ν F.a F.g (F.T + F.margin)`,
textually the same premises as `insertionLifespanStatement`
(`Contracts/V1/InsertionLifespan.lean:154-158`). And the version-2 statement
**implies** the version-1 statement, proved in the probe:

```lean
example : Contracts.V2.InsertionLifespan.insertionLifespanV2Statement →
    Contracts.V1.InsertionLifespan.insertionLifespanStatement := by
  intro h ν P F hg hreg
  obtain ⟨A, hA⟩ := h ν P F hg hreg
  exact ⟨A.toInsertionLifespanAPI, hA⟩
```

The anti-substitution guard is present on both layers:
`insertionLifespanV2API_family … : (insertionLifespanV2API F hg hreg).family = F := rfl`
in the binding, and the `rfl` in `checkedInsertionLifespanV2`'s
`⟨…, rfl⟩` pinning `A.family = F` in the test. `A.memForce`/`A.regular` are still
reachable off the version-2 record (probe §5), so R47's reuse path survives.

### (e) Non-vacuity — precisely what is conditional (F5)

There is **no inhabitant-level check at the contract level**: nothing in
`Contracts/`, `Bindings/` or `Tests/` exhibits an `InsertionFamilyAPI`
unconditionally, and neither the version-1 nor the version-2 scope says so. The
chain, as it actually stands on this branch:

| record | how it is obtained | conditional on |
|---|---|---|
| `PacketAPI ν` | `Bindings.packet ν hν` — **unconditional** for every `ν > 0`; registered as `I01.packet`, `Tests.checkedPacket : ∀ ν, 0 < ν → PacketAPI ν`, standard axioms | nothing |
| `CorrectionAPI ν P` | `Contracts.V2.correctionStatement` / V1 `correctionStatement` | a smooth divergence-free `(v,π)` solving `eq:NS` with force `g` on `(0,T+δ)` |
| `ScalingAPI ν P` | `scalingStatement : ∀ ν P (C : CorrectionAPI ν P) (th : ThresholdAPI), ∃ A, …` | a `CorrectionAPI` |
| `InsertionFamilyAPI ν P` | `insertionFamilyStatement : ∀ … (R : Data.ClassicalSolutionR ν a S.correction.g (T+δ)), R.velocity = … → R.pressure = … → ∃ A, …` | a reference `ClassicalSolutionR` through `T+δ` |
| `InsertionLifespanV2API ν P` | this lane | the above, plus `hg`, `hreg` |

So **this contract, like version one, is conditional on the manuscript's own
hypothesis** — "Let $(v,\pi,g)$ be the solution for $a\in\mathcal X_{\R}$ and
$g\in\mathcal F_{\R}$, regular through $T+\delta$" (`:32`). That is the right
conditionality and is not a defect. But note for the ledger: the version-1
review's sentence "both R42 records are conditional on an `InsertionFamilyAPI`
existing, which needs `I01.packet`'s record to be inhabited — still the open end"
is now **stale**: `PacketAPI` *is* inhabited (`Bindings/Packet.lean:104`). The
open end is now the reference `ClassicalSolutionR`, i.e. Theorem 4.2's own
hypothesis, whose supply is A01/A02's job.

---

## 3. Consistency

* **Import policy.** `Contracts/V2/InsertionLifespan.lean` imports exactly
  `Contracts.V1.InsertionLifespan` and `Contracts.V2.MaximalPartial` — both
  `Contracts.*`. `check_contracts.py` (inside `make check` and in the
  `--base-ref` run) accepts it; `hooks/post_lean.py` ran on each edit.
* **No restatements, so no bridge owed.** The version-2 contract file declares
  exactly one `structure` (`InsertionLifespanV2API`) and one `def`
  (`insertionLifespanV2Statement`), both new and version-2-owned. It copies no
  upstream or local definition: `limsupLeft`, `speedENorm`, `ClassicalSolutionR`,
  `maximalLifespanR`, `IsMaximalSolution`, `InsertionFamilyAPI`, `PacketAPI` all
  come in through the two imports. Correspondingly the binding adds no new `rfl`
  bridge and owes none — the two blow-up operators already bridge at
  `Bindings/MaximalPartial.lean:57,61` (`maximalPartial_limsupLeft_eq`,
  `maximalPartial_speedENorm_eq`, both `:= rfl`, verified in place), and the
  `ClassicalSolutionR`/`IsMaximalSolution` transports are the existing
  `uniqueness_toA02` / `maximalPartial_ofA02` / `maximalPartial_isMaximalSolution_iff`
  inside `Bindings.InsertionLifespan` and `Bindings.MaximalPartialV2`. This is
  the intended contrast with `Contracts/V2/MaximalPartial.lean`, which *did*
  restate two objects and therefore *did* owe transports.
* **Naming / namespace.** Contract namespace
  `BlowupDensity.Contracts.V2.InsertionLifespan` mirrors
  `BlowupDensity.Contracts.V2.MaximalPartial`; `extends` + `{ … with … }` +
  `toInsertionLifespanAPI` recovery mirror `MaximalPartialV2API` /
  `Bindings.maximalPartialV2` / `maximalPartial_of_v2` one-for-one. See F6 for
  the one divergence (binding namespace), which is deliberate and documented.
* **`scope` string.** Compared field-by-field with the `R42.insertion_lifespan`
  entry and with `REVIEW_CONTRACT.md:440-465` ("What R42 still lacks after this
  contract"). It names all three gaps that section raised and claims exactly
  them; the "NEW relative to `R42.insertion_lifespan`" and "NOT asserted"
  paragraphs are both accurate as verified above; the "Carried unchanged from
  version 1" and "Derived, not assumed" lists match version one's verbatim. No
  over-claim found. Two wording notes: F4 and F6.

---

## 4. Honesty of `research/R42/ATTEMPTS_CONTRACT_V2.md`

One failure is recorded — the unused-`ε` linter warning from a first draft that
wrote the three field bodies as `fun ε hε => …`. **Reproduced verbatim** with
`/tmp/rev114/unused_eps.lean` (a copy of the binding's record literal with named
`ε` binders):

```
$ cd verification && lake env lean /tmp/rev114/unused_eps.lean
/tmp/rev114/unused_eps.lean:17:20: warning: Variable name `ε` is not explicitly referenced.
Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _ε
Note: This linter can be disabled with `set_option linter.unusedVariables false`
… (identical at 18:19 and 19:25 — three warnings, one per field)
```
Same text, same count, same fix (`fun _ε hε`), matching the version-one
convention in `Bindings/InsertionLifespan.lean`.

No compile-level blocker is claimed anywhere in the lane's records ("No hard
compile failure was hit"), and the whole file builds from a warm cache, so
nothing else needed reproducing. Every row of the ATTEMPTS "Commands and
results" table was re-run independently in §1 and matches, including the
`git diff verification/contracts.json | grep -c '^-'` = 1 claim.

---

## 5. Findings

| # | Severity | Finding |
|---|---|---|
| F1 | none (confirmation) | All gates green: `lake build Tests.InsertionLifespanV2` prints "checked; standard logical axioms only"; `make check` / `make test` (20/20 contracts) / `make test-mutations` all exit 0; `check_contracts.py --base-ref origin/erenup/integration` → `registered_contracts: 20`, `base_compatibility_checked: True`. No frozen `Contracts/V1`, existing `Tests/` or existing `Bindings/` file touched; `contracts.json` purely additive. No `sorry`/`admit`/`axiom`/`native_decide`/`set_option`/`maxHeartbeats` in any new file. |
| F2 | none (confirmation) | `blowup_limsup` is the genuine second display of `:35`: `speedENorm` **is** the essential supremum (`= essSup ‖·‖ₑ volume`, proved), `limsupLeft` **is** `Filter.limsup φ (𝓝[<] T)` over a `NeBot` filter (proved), and `essSup ≤ sup` (proved) makes the essSup form the stronger, never-weaker reading. Not an along-a-sequence statement, not vacuous. |
| F3 | informational | `maximal` is **derivable** from `solution` + the inherited `lifespan` + A02's already-registered `restrict` — probe `/tmp/rev114/redundancy.lean` proves it in 9 lines and compiles clean. So the field is a convenience repackaging in the registered vocabulary, not new mathematical content and not new trust surface. Not a defect; recorded so a future reader does not mistake it for an independent assertion. |
| F4 | low (scope wording) | The manuscript's `:53` says "the **unique** maximal solution". `IsMaximalSolution` carries no uniqueness clause; uniqueness is `maximal_unique` in `Contracts.V2.MaximalPartial.MaximalPartialV2API` (contract `A02.maximal_partial_v2`), which this record does **not** carry as a field. Suggest one sentence in the `NOT asserted` list, e.g. "uniqueness of the maximal solution (the word *unique* of 04:53) is not a field here; it is `maximal_unique` of `A02.maximal_partial_v2`, which a consumer must hold alongside." `contracts.json` scope strings are not frozen by `check_contracts.py`, so this is a cheap edit at merge time — or a one-line entry in the next R42 lane's notes. |
| F5 | low (scope wording) | Neither the version-1 nor the version-2 scope records that the whole record is **conditional** on an `InsertionFamilyAPI` existing, which needs a reference `Data.ClassicalSolutionR ν a g (T+δ)` — Theorem 4.2's own hypothesis. Related: the version-1 review's "needs `I01.packet`'s record to be inhabited — still the open end" is now stale, since `Bindings.packet ν hν` inhabits `PacketAPI` unconditionally (`I01.packet`, `Tests.checkedPacket`, standard axioms). The open end has moved to the reference solution. Suggest one sentence in the scope, and a correction line in `research/R42/` or `logs/LESSONS.md` so the stale claim does not propagate to R41D/R46/R47. |
| F6 | cosmetic | The scope opens `"Version 2 of R42.insertion_lifespan (extends the version-1 InsertionLifespanAPI unchanged, extends InsertionLifespanAPI): …"` — the clause is duplicated. The `A02.maximal_partial_v2` convention reads `"… extending A02.maximal_partial version 1 unchanged (extends MaximalPartialAPI): …"`. Purely editorial; nothing enforces it. |
| F7 | cosmetic / no action | `Bindings/InsertionLifespanV2.lean` reopens the namespace `BlowupDensity.Bindings.InsertionLifespan` from a *second* module, so that namespace's declarations are now split across two files. `Bindings/MaximalPartialV2.lean` instead uses the flat `BlowupDensity.Bindings` with a `maximalPartial_` prefix. The choice here matches the version-one `Bindings/InsertionLifespan.lean` (which owns that namespace) and is explained in the file's docstring, so it is consistent with the closer precedent. No action. |

## 6. What this lane changes for downstream R42 consumers

After merge, `R41D`/`R46`/`R47` can, from contracts alone and with no hypothesis
beyond `hg`/`hreg`: open the inserted pair as a full-horizon
`Data.ClassicalSolutionR` (hence `sobolev` and `pressure_gradient` for `u_ε` on
`[0,T)`), name it as the maximal solution in `A02.maximal_partial_v2`'s
vocabulary, and cite the manuscript's displayed
$\limsup_{t\uparrow T}\norm{u_\eps(t)}_\infty=\infty$ — all three of the gaps
`REVIEW_CONTRACT.md:443-452` listed. What remains open for R42 is unchanged and
correctly disclaimed: A04's continuation criterion `eq:criterion`, and the
inhabitation of the reference solution (F5).

## 7. Commands run (full list)

```
git log/diff/show (read-only)
. scripts/lean-env.sh; cd verification
LEAN_NUM_THREADS=6 lake build Tests.InsertionLifespanV2          → exit 0, "checked; standard logical axioms only"
make check                                                       → exit 0, 13/13 policy tests, 30 work items consistent
make test                                                        → exit 0, 20/20 contracts checked, no "error:"
make test-mutations                                              → exit 0, "Mutation suite passed."
python3 experiments/check_contracts.py --base-ref origin/erenup/integration
                                                                 → exit 0, 20 contracts, base_compatibility_checked: True
lake env lean ../research/R42/axioms_contract_v2.lean             → 3 × [propext, Classical.choice, Quot.sound]; two identical signatures
lake env lean /tmp/rev114/fidelity.lean                           → clean (only the requested #print axioms line)
lake env lean /tmp/rev114/redundancy.lean                         → clean (maximal derived from solution+lifespan+restrict)
lake env lean /tmp/rev114/unused_eps.lean                         → 3 × unused-ε warning, ATTEMPTS reproduction
grep -nE "sorry|admit|axiom|native_decide|set_option|maxHeartbeats" <4 new files>  → none
```
