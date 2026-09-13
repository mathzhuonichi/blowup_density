# Review — lane 035, B01 units 1–3

**Verdict: ACCEPT-WITH-NOTES.**

Everything the brief asks to be true is true: both modules build clean, the conformance file
typechecks with only the three standard axioms, the five spec-field `example`s carry the spec
field types *token-for-token* and are discharged by `:=` with no extra hypotheses, the
`MemForceCompact` half of unit 1 is genuinely reused from `D01/ForceClass.lean`, and the three
spot-checked `ATTEMPTS.md` claims reproduce exactly (I re-ran the two failures). The findings
below are all documentation/hygiene; none of them is a mathematical or kernel-level defect, and
none blocks the merge.

---

## 1. Commands and results

All from the worktree `/data_8T/ping/blowup_density/.claude/worktrees/035-B01-units-1-3` (WT),
after `bash scripts/lean-install.sh`, `. scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`, no `-j`,
one lake at a time, every lake run from `WT/verification`.

| # | Command | Result |
|---|---|---|
| 1 | `cd WT && bash scripts/lean-install.sh` | ends `== OK`; `lake exe cache get` + `lake test` → `[9941/9941]`, every contract test reports `checked; standard logical axioms only` |
| 2 | `cd WT/verification && lake build NSFormalization.Section4.B01.Compact NSFormalization.Section4.B01.Completion` | `Build completed successfully (9879 jobs).`, **exit 0**. `grep -n "B01\|sorry\|declaration uses"` over the full log → **no match**. Every warning in the log comes from replayed pre-existing `Source/*` and `Paper3/*` modules (`unnecessarySimpa`, `unusedSimpArgs`, deprecations); **zero** warnings from `Section4/B01` |
| 3 | `lake env lean ../research/B01/axioms_u123.lean` | **exit 0**, no error, no warning, no `sorry`. All 8 `#print axioms` lines are exactly `[propext, Classical.choice, Quot.sound]` (`isSobolevPath_angularRealVectorSlice`, `aestronglyMeasurable_angularRealVectorSlice`, `bochnerDatumENorm_toLp_sub`, `approxCompact`, `completionRepresentative`, `completionSurjective`, `completionNorm`, `completionCongr`). All 8 `example`s typecheck |
| 4 | `grep -n 'sorry\|admit\|native_decide\|axiom\|maxHeartbeats' formalization/NSFormalization/Section4/B01/*.lean` | one hit only: `Compact.lean:30`, the string `axioms_u123.lean` inside the module docstring. **Nothing outside comments** |
| 5 | `cd WT && make check` | **exit 0** (`check_formalization_plan.py --check`, `check_contracts.py`, `test_contract_policy.py` 13 tests OK, `check_work_queue.py` "30 work items: ownership, contract registration and task cards consistent") |
| 6 | `lake env lean /tmp/t1_rw.lean` (ATTEMPTS §1 reproduction) | fails exactly as claimed, see finding 4 |
| 7 | `lake env lean /tmp/t2_haveI.lean` (ATTEMPTS §2 reproduction) | `linter.style.haveILetI` fires exactly as claimed, see finding 4 |

Scratch files for 6–7 were written to `/tmp`; nothing in WT was modified except this review file.

## 2. Spec conformance (unit 2 and unit 3) — clean

I extracted each `BochnerApproxAPI` field type from `research/B01/Spec.lean` and each `example`
type from `research/B01/axioms_u123.lean` mechanically (strip the field name / `example :`, strip
the `:=` tail, normalize indentation) and compared strings:

```
approxCompact            (Spec.lean:312, axioms_u123.lean:59)  identical = True
completionRepresentative (Spec.lean:320, axioms_u123.lean:65)  identical = True
completionSurjective     (Spec.lean:325, axioms_u123.lean:69)  identical = True
completionNorm           (Spec.lean:331, axioms_u123.lean:74)  identical = True
completionCongr          (Spec.lean:337, axioms_u123.lean:78)  identical = True
```

All five are discharged by a bare `:= NSFormalization.Section4.B01.<name>` — no `by`, no
coercion, no extra hypothesis, no weakening of a binder. `completionNorm` keeps the spec's
instance binder `[Fact (1 ≤ q)]` in instance position.

The conformance file is honest about *which* namespace the `example` types live in: it opens
`BlowupDensity.Contracts.V1.Data` and does **not** open `NSFormalization.Section4.B01`, referring
to the formalization theorems by fully-qualified name. So the `example` types really are the
contract's `CompletedDense` / `MemBochnerDatum` / `bochnerDatumENorm` / `forceClassCompact`, and
the kernel checks the defeq against the local restatements. This is the right shape for the check.

## 3. Unit 1 — matches `COMPARISON.md:145`

`COMPARISON.md:145` asks for three things; all three are accounted for:

* `IsSobolevPath s F (angularRealVectorSlice s f hf hc)` under `∀ z i, (F z).ofLp i = f i z` →
  `Compact.lean:89` `isSobolevPath_angularRealVectorSlice`, hypotheses identical to the table row.
* `AEStronglyMeasurable (angularRealVectorSlice s f hf hc) forceTimeMeasure` →
  `Compact.lean:100` `aestronglyMeasurable_angularRealVectorSlice`.
* The `MemForceCompact` half — **not reproved.** It is
  `NSFormalization.Section4.D01.memForceCompact_of_smooth_support`, which I opened at
  `formalization/NSFormalization/Section4/D01/ForceClass.lean:352-354`:
  `theorem memForceCompact_of_smooth_support {f : VelocityField} (hs : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (hp : ∀ z ∈ tsupport f, 0 < z.1) : MemForceCompact f := ⟨hs, hc, fun z hz => ⟨hp z hz, mem_univ _⟩⟩`
  — literally the term `COMPARISON.md:145` predicted. `axioms_u123.lean:51` states the
  obligation and discharges it by that lemma; `approxCompact` calls it at `Compact.lean:147`.

The source citations check out: `ARVB:54` `angularRealVectorSlice_pairing`, `ARVB:64`
`memLp_angularRealVectorSlice`, `ARVB:120`
`exists_angular_real_vector_positive_physical_approx` — all three at the stated lines of
`formalization/NSFormalization/Paper3/AngularRealVectorBochner.lean`.

## 4. Findings

### Finding 1 — `Contracts.V1.Data.bochnerSpace` does not exist (severity: **low**, documentation)

**Declaration:** `Compact.lean:79-81` (`bochnerSpace`), plus `Compact.lean:25-26` (module
docstring) and `research/B01/ATTEMPTS.md` "Failures" item 3.

**What is wrong.** `Compact.lean:79` says "`Contracts.V1.Data.bochnerSpace`/`research/B01/Spec.lean:158`, restated", and the module docstring says the six predicates are restated verbatim from
"`Contracts/V1/Data.lean:212,205,732,743,563,158`". There is **no** `bochnerSpace` anywhere in
`verification/Contracts/` —
`grep -rn "bochnerSpace" verification/Contracts/` returns nothing. `Data.lean:158` is a line in
the middle of the `IsSobolevDatum` docstring, not a declaration. The only upstream source is
`research/B01/Spec.lean:158`, and against *that* the local copy is byte-identical:

```
Spec.lean:158  abbrev bochnerSpace (q : ℝ≥0∞) (s : ℝ) := Lp (RealVectorSobolev s) q forceTimeMeasure
Compact.lean:81 abbrev bochnerSpace (q : ℝ≥0∞) (s : ℝ) := Lp (RealVectorSobolev s) q forceTimeMeasure
```

`ATTEMPTS.md` repeats the error by listing `bochnerSpace` among the definitions that are
"byte-for-byte the Data bodies".

**Fix.** In `Compact.lean:79` write "`research/B01/Spec.lean:158`, restated" (drop
`Contracts.V1.Data.bochnerSpace`); in `Compact.lean:25-26` drop `158` from the `Data.lean` line
list and add a separate sentence for `bochnerSpace`; correct the same sentence in `ATTEMPTS.md`.
Note that `research/B01/axioms_u123.lean:31` already gets this right ("`research/B01/Spec.lean:158`, restated"). No code change.

### Finding 2 — three restatements are not token-for-token (severity: **low**, fidelity)

**Declarations:** `Compact.lean:61-68` `CompletedDenseVia`, `Compact.lean:72-73`
`CompletedDense`, `Compact.lean:76` `forceClassCompact`.

**What is wrong.** A declaration-aware diff against `Contracts/V1/Data.lean` gives:

```
bochnerDatumENorm (Data:205)   identical = True
MemBochnerDatum   (Data:212)   identical = True
CompletedDenseVia (Data:732)   identical = False
  -     (path : SpaceTimeField → (ℝ → RealVectorSobolev s) → Prop)
  -     (S : Set SpaceTimeField) : Prop :=
  +     (path : VelocityField → (ℝ → RealVectorSobolev s) → Prop)
  +     (S : Set VelocityField) : Prop :=
CompletedDense    (Data:743)   identical = False
  - abbrev CompletedDense (q : ℝ≥0∞) (s : ℝ) (S : Set SpaceTimeField) : Prop :=
  + abbrev CompletedDense (q : ℝ≥0∞) (s : ℝ) (S : Set VelocityField) : Prop :=
forceClassCompact (Data:563)   identical = False
  - def forceClassCompact : Set SpaceTimeField := {f | MemForceCompact f}
  + def forceClassCompact : Set VelocityField := {f | MemForceCompact f}
```

The *only* difference is `SpaceTimeField` → `VelocityField`, four occurrences. Since
`Data.lean:104` is `abbrev SpaceTimeField := VelocityField`, these are defeq on the nose (and the
`example`s prove it in the kernel), and `formalization/` cannot import `Contracts.*`, so the
substitution was forced *as written*. But it is avoidable, and the tree already shows the
avoidance: `Section4/D01/HomogeneousWitness.lean:613-614` restates
`/-- `Data.lean:104` `SpaceTimeField`. -/ abbrev SpaceTimeField := VelocityField`
locally precisely so the downstream copies stay verbatim.

**Fix.** Add the one-line `abbrev SpaceTimeField := VelocityField` to `Compact.lean` §0 (with the
`Data.lean:104` citation) and use it in the three restatements; all three then become
token-for-token. Purely cosmetic — no proof changes, no type changes.

### Finding 3 — second local copy of `bochnerDatumENorm` (severity: **low**, duplication)

**Declaration:** `Compact.lean:57-58` `NSFormalization.Section4.B01.bochnerDatumENorm`.

**What is wrong.** `NSFormalization/Section4/D01/HomogeneousWitness.lean:619-621` (namespace
`NSFormalization.Section4.D01.Homogeneous`, opened at `:88`) already carries the identical
verbatim restatement of `Data.lean:205`. The tree now has two copies. The same is true of
`forceTimeMeasure`, but that duplication is pre-existing (`ForceClass.lean:147` and
`HomogeneousWitness.lean:617`) and not this lane's doing.

Two mitigating facts, which is why this is **low** and not a blocker: (a) `CLAUDE.md:31`'s
"only one local restatement" rule is written for the `structure` exception
(`ClassicalSolutionR`), not for plain `def`s; (b) reusing the D01 copy would force `Compact.lean`
to import the heavy `HomogeneousWitness.lean` and to `open NSFormalization.Section4.D01.Homogeneous`,
which is a worse trade. `MemBochnerDatum`, `CompletedDenseVia`, `CompletedDense`,
`forceClassCompact` and `bochnerSpace` have **no** prior copy anywhere in `formalization/`
(checked by `grep -rn --include='*.lean'` over the whole tree, B01 excluded), and `IsSobolevPath`,
`MemForceCompact`, `forceTimeMeasure`, `IsSobolevDatum` are correctly *imported* from D01 rather
than re-restated.

**Fix.** Either leave as is with a one-line note in `Compact.lean` §0 acknowledging the
`D01.Homogeneous` copy, or (when unit 10 lands) hoist the completion vocabulary into a single
`Section4/B01/Vocabulary.lean` (or into `D01/ForceClass.lean`) that both `B01` and
`D01.Homogeneous` import.

### Finding 4 — `ATTEMPTS.md` honesty spot-check: all three claims hold (severity: none)

I re-ran the two claimed build failures rather than taking them on trust.

1. **`rw [← hFf (t, x) i]` fails (ATTEMPTS §"Failures" item 1).** Confirmed, verbatim, including
   the beta-redex diagnosis. `lake env lean /tmp/t1_rw.lean` (the exact unit-1 proof with `rw`
   substituted for `simp only`) →
   ``error: Tactic `rewrite` failed: Did not find an occurrence of the pattern f i (t, x) in the target expression (fun x => ψ x * ↑(f i (t, x))) x = (fun x => ψ x * ↑(((fun x => F (t, x)) x).ofLp i)) x``, exit 1.
   The goal shape is exactly what `ATTEMPTS.md` describes.
2. **`haveI : Fact (1 ≤ q)` trips `linter.style.haveILetI` (item 2).** Confirmed.
   `lake env lean /tmp/t2_haveI.lean` →
   ``warning: Try this: haveI̵ / The goal is a proposition, so `have` is preferred over `haveI`.``
   `approxCompact`'s goal is a `Prop`, so the linter would have fired; the `have : Fact (1 ≤ q) := ⟨hq1⟩`
   at `Compact.lean:134` is the right fix, and local hypotheses of class type are found by
   instance resolution (the module compiles, which is the proof). The parenthetical
   "this linter is only a warning in `formalization/`" is also correct: `formalization/lakefile.toml`
   sets no `warningAsError` on the `NSFormalization` lib, unlike `verification`'s `Tests`.
3. **`exists_angular_real_vector_positive_physical_approx` at `Paper3/AngularRealVectorBochner.lean:120`.**
   Confirmed — the `theorem` keyword is on line 120. The neighbouring citations are right too:
   `angularRealVectorSlice_pairing` at `:54`, `memLp_angularRealVectorSlice` at `:64`,
   `cyclesToAngularRealVector` at `:15`, `cyclesToAngularRealVector_norm_le` at `:24`.

The only inaccuracy in `ATTEMPTS.md` is the `bochnerSpace` provenance claim folded into finding 1.

### Finding 5 — the two new modules are in no default build target (severity: **info**)

Nothing in `formalization/NSFormalization.lean`, `verification/Contracts/`, `verification/Bindings/`
or `verification/Tests/` imports `NSFormalization.Section4.B01.*`
(`grep -rn --include='*.lean' "Section4.B01"` outside `Section4/B01/` is empty), and the root
`NSFormalization.lean` lists no `Section4` module at all. So `make test` / `lake test` will not
re-check these two modules; only an explicit `lake build NSFormalization.Section4.B01.…` does.
There is also no `rfl` bridge in `verification/Bindings/` yet (the convention of
`Bindings/GradientL6.lean:23`), which `CLAUDE.md:30` asks of every restated definition.

This is **not** a defect of this lane: `COMPARISON.md:154` assigns the promotion to
`Contracts/V1/BochnerApprox.lean` plus the typed `Bindings` entry and the `#print axioms` test to
unit 10, and `make check`'s `check_work_queue.py` is green as things stand. Recording it so the
gap is visible until unit 10 closes it; until then `research/B01/axioms_u123.lean` is the only
regression net, and it must be re-run by hand.

## 5. Proof-level spot-check (no findings)

Read in full and found sound:

* `approxCompact` (`Compact.lean:132-157`). The `r = ⊤` branch of `∀ r : ℝ≥0∞, 0 < r` is handled
  (`lt_top_iff_ne_top.mpr hMne` off the finiteness half of `bochnerDatumENorm_toLp_sub`), which is
  the branch that is easy to forget; the `r ≠ ⊤` branch uses `ε := min 1 r.toReal`, positive by
  `ENNReal.toReal_pos hr.ne' hrtop`, and `ENNReal.toReal_lt_toReal hMne hrtop` with both
  side conditions discharged. `norm_sub_rev` reconciles the source theorem's `‖b - D‖` with the
  contract's `D - b`. No hypothesis of the spec field is strengthened.
* `bochnerDatumENorm_toLp_sub` (`Compact.lean:111-123`) is honest a.e.-class bookkeeping
  (`Lp.coeFn_sub` + two `coeFn_toLp`, then `eLpNorm_congr_ae`, `Lp.eLpNorm_ne_top`, `Lp.norm_def`).
* The four `completion*` theorems (`Completion.lean:31,39,46,53`) are the claimed one-liners over
  `Lp.memLp`, `MemLp.toLp`/`coeFn_toLp`, `Lp.enorm_def`, `eLpNorm_congr_ae`.

## 6. What would flip this to ACCEPT

Findings 1 and 2 are two comment edits and one added `abbrev` — no proof touched, no rebuild of
anything but the two B01 modules. Findings 3 and 5 are for the unit-10 lane to absorb.
