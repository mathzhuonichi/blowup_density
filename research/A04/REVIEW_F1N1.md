# Review — A04 units F1 and N1 (lane 039)

Reviewer: independent opus reviewer, worktree `.claude/worktrees/039-A04-units-f1-n1`
at `7b44645`.  Scope: `formalization/NSFormalization/Section4/A04/{Forcing,Continuity}.lean`,
`research/A04/axioms_f1n1.lean`, `research/A04/ATTEMPTS_F1N1.md`.

## Verdict

**ACCEPT-WITH-NOTES.**

The Lean is correct, `sorry`-free, warning-free and axiom-clean; every restated
`def` is token-for-token its original and `rfl`-equal to it; the N1 payoff
discharges the *exact* integrand of `ContinuationAPI.highContinuationIntegral`
under a strict **subset** of that field's hypotheses (no `HasSmoothSobolevPath`,
no `MemL1Hm`, no `0 < ν`, no `a ∈ initialClassR`, no `3 ≤ m`); F1a/F1b produce
the spec's `MemL1Hm f` and `BoundedIntoHOne (Icc 0 b) K f` in the spec's argument
order, and the conformance theorems are stated in `Contracts.V1.Data` vocabulary
and discharged by `exact` with no extra hypotheses.

The five findings below are all **low** severity: three are documentation
inaccuracies (wrong `Data.lean` line citations, an overstated `Nat.cast` claim, an
off-by-one conjunct index), one is a duplicated definition that should be
acknowledged, one is an optional export.  None affects soundness, and none blocks
the merge.  Fixing 1–4 is a docstring/one-line-tactic edit.

## Findings

### 1. `bochnerDatumENorm` is now a **third** in-repo copy, and the docstring does not say why — *low*

* Declaration: `NSFormalization.Section4.A04.bochnerDatumENorm`
  (`formalization/NSFormalization/Section4/A04/Forcing.lean:78`).
* The repository already carries two: the canonical
  `verification/Contracts/V1/Data.lean:205` and the verbatim restatement
  `formalization/NSFormalization/Section4/D01/HomogeneousWitness.lean:620`.  I
  verified all three are `rfl`-equal (scratch check §3 below).
* Forcing.lean §0 justifies restating only by "`NSFormalization` … cannot import
  `Contracts.*`", which is true but does not address the copy already inside the
  same package.  Reusing the D01 one would drag `HomogeneousWitness`'s closure
  (`WeakFourierUniqueness`, `CompactFourier`, `FourierConvention`, …) into a
  module whose whole point (per `ATTEMPTS_F1N1.md` §"Failures" item 4) is the
  smallest closure — so the copy is defensible, but that is the reason and it is
  not written down.
* Fix: add one sentence to the §0 docstring naming
  `Section4/D01/HomogeneousWitness.lean:620` and the build-hygiene reason for not
  importing it (the same sentence the module already writes for
  `sobolevENorm_eq` vs `A03.VectorTameProduct`).

### 2. Wrong `Data.lean` line citations for the three restated norms — *low*

* Declarations: `A04.bochnerDatumENorm`, `A04.forceSobolevENorm`,
  `A04.forceSobolevENormL1` (`Forcing.lean:76`, `:81`, `:89` docstrings).
* They cite `Data.lean:213`, `Data.lean:228`, `Data.lean:236`.  The actual
  definitions are at `Data.lean:205`, `:225`, `:231`.  Line `213` is the body of
  `MemBochnerDatum`; line `228` is inside `forceSobolevENorm`'s body; line `236`
  is the body of **`forceSobolevENormL2`** — i.e. the citation for the `L¹`
  abbreviation points at the `L²` one.
* Everything else checked out: `SolutionClass.lean:90/91/119` and
  `Data.lean:544/643` are exactly the clauses the docstrings claim, and
  `HomogeneousWitness.lean:619` already cites `Data.lean:205` correctly, so this
  is drift in the new file, not a moved target.
* Fix: `213 → 205`, `228 → 225`, `236 → 231`.

### 3. `Nat.cast_ofNat` **is** `rfl` at this pin; the claim and the tactic that rests on it are both wrong — *low* (honesty spot-check)

* Declaration: `A04.intervalIntegrable_highContinuationIntegrand`
  (`Continuity.lean:128-130`), and `ATTEMPTS_F1N1.md` §"Failures … " item 2.
* The attempts record says "`Nat.cast_one` / `Nat.cast_ofNat` are **not** `rfl`".
  Half true.  `((1 : ℕ) : ℝ) = (1 : ℝ)` is indeed not `rfl` (Lean reports
  `Type mismatch … ↑1 = 1`), so F1b's `simpa only [Nat.cast_one]` is genuinely
  required.  But `((2 : ℕ) : ℝ) = (2 : ℝ) := rfl` **compiles** at this toolchain
  (`instOfNat` for `n ≥ 2` unfolds to `Nat.cast`), and I checked the consequence
  directly: `continuousOn_sobolevNormAt_velocity w 2` typechecks against the
  `sobolevNormAt (2 : ℝ)` goal with no rewrite at all.
* So the two lines
  `have h := continuousOn_sobolevNormAt_velocity w 2` /
  `simp only [Nat.cast_ofNat] at h` are dead weight.
* Fix: replace the `have`/`simp only`/`exact` block for `hv2` with
  `(continuousOn_sobolevNormAt_velocity w 2).mono hsub`, and narrow the attempts
  claim to `Nat.cast_one`.

### 4. Off-by-one conjunct index in `ATTEMPTS_F1N1.md`'s clause table — *low* (honesty spot-check)

* Row `memL1Hm_of_memForceR` calls `MemLp G 1 forceTimeMeasure` "the … conjunct
  (4th)".  The same table numbers `IsSobolevPath` "(1st)" and
  `ContDiffOn ℝ ∞ G futureTimes` "(2nd)"; under that numbering `MemLp G 1` is the
  **3rd** (`SolutionClass.lean:89,90,91,92`).  "4th" counts the anonymous
  constructor slot including `G` itself, which the neighbouring rows do not.
* The rest of the table is accurate and I checked every row against the code:
  `memL1Hm_of_memForceR` destructures `⟨G, hpath, _hc, h1, _h2⟩` and uses only
  `hpath` (index-set membership), `h1.1` (`AEStronglyMeasurable`) and `h1.2.ne`
  (`eLpNorm ≠ ⊤`); `_h2`, the `L²_t` conjunct, is genuinely unused, as is the
  `ContDiffOn ℝ ∞ f futureDomain` half of `MemForceR`;
  `exists_boundedIntoHOne_of_memForceR` uses `⟨G, hpath, hc, _, _⟩`, i.e. the 1st
  and 2nd conjuncts only; `sobolevENorm_velocity_ne_top` uses `⟨G, _, hGd⟩`, i.e.
  the `IsSobolevDatum` conjunct only, discarding `ContinuousOn G`;
  `continuousOn_sobolevNormAt_velocity` uses both.  `HasSmoothSobolevPath` appears
  nowhere in either module.
* Fix: "(4th)" → "(3rd)".

### 5. The real-valued half of N1 is proved but not exported — *low, optional*

* `research/A04/COMPARISON.md:208` phrases N1 as "… `sobolevNormAt` is then the
  datum norm `‖G t‖`, and `t ↦ sobolevNormAt s u t` is continuous there".  Only
  the `ℝ≥0∞` form is exported (`Forcing.sobolevENorm_eq`); the real-valued
  identity `sobolevNormAt s u t = ‖G t‖` lives inside the `show`/`rw` of
  `continuousOn_sobolevNormAt_of_datumPath` (`Continuity.lean:86-90`) and a
  consumer must re-derive the two `toReal` lines.
* Fix (optional): export
  `theorem sobolevNormAt_eq (hA : IsSobolevDatum s (fun x => u (t,x)) A) : sobolevNormAt s u t = ‖A‖`
  and use it in the `congr` step.

## Checks performed

### 1. Builds, axioms, hygiene

Environment: `bash scripts/lean-install.sh` (`== OK`), `. scripts/lean-env.sh`,
`LEAN_NUM_THREADS=6`, no `-j`, all lake commands from `verification/`.

```
$ cd verification && lake build NSFormalization.Section4.A04.Forcing \
                                NSFormalization.Section4.A04.Continuity
Build completed successfully (9880 jobs).
EXIT=0
```
No `sorry` warning anywhere in the log; neither A04 module appears in it (Lake
re-emits cached warnings on replay, so absence = no warnings).  Confirmed by
fresh elaboration, which prints **nothing** for either file:

```
$ lake env lean ../formalization/NSFormalization/Section4/A04/Forcing.lean     -> (no output) EXIT=0
$ lake env lean ../formalization/NSFormalization/Section4/A04/Continuity.lean  -> (no output) EXIT=0
```

```
$ lake env lean ../research/A04/axioms_f1n1.lean
EXIT=0
```
All **10** `#print axioms` report exactly `[propext, Classical.choice, Quot.sound]`:
`memL1Hm_of_memForceR`, `exists_boundedIntoHOne_of_memForceR`,
`sobolevENorm_velocity_ne_top`, `sobolevENorm_force_ne_top`,
`continuousOn_sobolevNormAt_velocity`, `continuousOn_sobolevNormAt_force`,
`intervalIntegrable_highContinuationIntegrand`, `f1a_memL1Hm_of_memForceR`,
`f1b_exists_boundedIntoHOne_of_memForceR`,
`n1_intervalIntegrable_highContinuationIntegrand`.  No errors, no warnings.

```
$ grep -nE "sorry|admit|native_decide|axiom|maxHeartbeats" \
    formalization/NSFormalization/Section4/A04/{Forcing,Continuity}.lean \
    research/A04/axioms_f1n1.lean
```
14 hits, **all** in prose comments or in the `#print axioms` commands themselves;
nothing in a proof.  `grep -nE "set_option|attribute|@\[|unsafe|partial|opaque|instance "`
on the three files: no hits.

```
$ make check
EXIT=0   (check_formalization_plan --check; check_contracts; test_contract_policy 13 tests OK;
          check_work_queue: 30 work items consistent)
```

### 2. Restatement fidelity

Token-for-token diff against the originals — all six restated `def`s are
**verbatim**, with no `VelocityField`-for-`SpaceTimeField` substitution:
`Forcing.lean` uses the identifier `SpaceTimeField`, opened from
`Section4.A02.SolutionClass:53`, which is exactly `abbrev SpaceTimeField := VelocityField`.

| restated in `Forcing.lean` | original | verbatim? |
|---|---|---|
| `sobolevNormAt` (`:73`) | `research/A04/Spec.lean:183` | yes |
| `bochnerDatumENorm` (`:78`) | `Data.lean:205` | yes |
| `forceSobolevENorm` (`:84`) | `Data.lean:225` | yes |
| `forceSobolevENormL1` (`:91`) | `Data.lean:231` | yes |
| `MemL1Hm` (`:96`) | `Spec.lean:268` | yes |
| `BoundedIntoHOne` (`:102`) | `Spec.lean:286` | yes |

Imports: `Forcing.lean:1-2` is `import NSFormalization.Section4.A02.SolutionClass`
and `import NSFormalization.Section4.D01.ForceClass` only — `ClassicalSolutionR`,
`MemForceR`, `IsSobolevPath`, `forceTimeMeasure` are **imported from A02**, not
copied; `sobolevENorm`, `IsSobolevDatum`, `sobolevENorm_le_of_isSobolevDatum`,
`isSobolevDatum_unique` are imported from D01.  Nothing is re-declared that could
have been imported, except `bochnerDatumENorm` (finding 1) and `sobolevENorm_eq`
(a second copy of `A03/VectorTameProduct.lean:71`, explicitly and correctly
justified in `ATTEMPTS_F1N1.md` item 4 — A03 would pull in the tame-product
closure).

Scratch `example … := rfl` file (written to `/tmp`, typechecked, deleted).
**All 20 examples compiled, `EXIT=0`:**

```
-- §1 the A02/D01 coincidences the Forcing.lean docstring claims
@A02.MemForceR = @D01.MemForceR                        := rfl   ✓
@A02.IsSobolevPath = @D01.IsSobolevPath                := rfl   ✓
@A02.IsSobolevDatum = @D01.IsSobolevDatum              := rfl   ✓
A02.futureTimes = D01.futureTimes                      := rfl   ✓
A02.forceTimeMeasure = D01.forceTimeMeasure            := rfl   ✓
-- §2 each against the canonical Contracts.V1.Data original
Data.MemForceR = A02.MemForceR / = D01.MemForceR       := rfl   ✓
Data.IsSobolevPath = A02.IsSobolevPath                 := rfl   ✓
Data.IsSobolevDatum = A02. / = D01.                    := rfl   ✓
Data.futureTimes = A02.futureTimes                     := rfl   ✓
Data.forceTimeMeasure = A02.forceTimeMeasure           := rfl   ✓
Data.sobolevENorm = D01.sobolevENorm                   := rfl   ✓
-- §3 the A04 restated norms
Data.bochnerDatumENorm   = A04.bochnerDatumENorm       := rfl   ✓
Data.forceSobolevENorm   = A04.forceSobolevENorm       := rfl   ✓
Data.forceSobolevENormL1 = A04.forceSobolevENormL1     := rfl   ✓
D01.Homogeneous.bochnerDatumENorm = A04.bochnerDatumENorm := rfl ✓   (finding 1)
-- §4 the A04 restated draft defs against Spec.lean's text, re-typed by the reviewer
A04.sobolevNormAt / A04.MemL1Hm / A04.BoundedIntoHOne  := rfl   ✓
```

Third copy of `bochnerDatumENorm`: **confirmed** — `Data.lean:205`,
`D01/HomogeneousWitness.lean:620`, `A04/Forcing.lean:78`.  See finding 1.

### 3. Serves the spec

`research/A04/Spec.lean:494-510` `highContinuationIntegral` — the field's first
conjunct is

```
IntervalIntegrable
  (fun s : ℝ => Cgron m ν * sobolevNormAt 2 w.velocity s ^ 2 *
                  sobolevNormAt (m : ℝ) w.velocity s + sobolevNormAt (m : ℝ) f s)
  volume t₀ t
```

`A04.intervalIntegrable_highContinuationIntegrand` (`Continuity.lean:117-125`)
and its conformance twin `n1_intervalIntegrable_highContinuationIntegrand`
(`axioms_f1n1.lean:120-133`) reproduce that term **character for character**,
including the `((Cgron m ν * X ^ 2) * Y) + Z` association and the `2 : ℝ`
numeral.  Hypotheses actually taken: `MemForceR f`, `w : ClassicalSolutionR ν a f T`,
`Cgron`, `m`, `0 ≤ t₀`, `t₀ ≤ t`, `t < T`.  Hypotheses of the field **not** taken:
`0 < ν`, `a ∈ initialClassR`, `MemL1Hm f`, `HasSmoothSobolevPath T w.velocity`,
`3 ≤ m`.  A strict subset — so the conjunct is discharged under weaker
assumptions than the field offers, and in particular **`HasSmoothSobolevPath` is
not used**: continuity comes from the `ContinuousOn G (Ico 0 T)` conjunct of
`ClassicalSolutionR.sobolev` (`SolutionClass.lean:120`) and from
`ContDiffOn ℝ ∞ G futureTimes` of `MemForceR` (`:90`) via `.continuousOn.mono`.
`Cgron` is universally quantified rather than a structure field, so any
`ContinuationAPI` instance may use it.

F1 against the spec: `MemL1Hm (f : SpaceTimeField)` and
`BoundedIntoHOne (I : Set ℝ) (K : ℝ≥0∞) (f : SpaceTimeField)` — same argument
order in `Forcing.lean:96,102` and in the produced statements
`MemL1Hm f` / `BoundedIntoHOne (Icc 0 b) K f`.  `restartBeyond`
(`Spec.lean:581`) consumes `BoundedIntoHOne (Icc (0:ℝ) (S+1)) K f`, which is the
`b := S+1` instance of F1b; F1b delivers only *some* finite `K`, and both
`Spec.lean:281-284` and the `exists_boundedIntoHOne_of_memForceR` docstring say so
explicitly — the equality with the velocity's `K` is correctly **not** claimed.
This matches `COMPARISON.md:209` word for word ("for some finite `K` at every `b`").

Conformance file: stated in `Contracts.V1.Data` vocabulary
(`open BlowupDensity.Contracts.V1.Data`; the three `Draft` defs are re-typed from
`Spec.lean:183,268,286` and rest on `Data.sobolevENorm` /
`Data.forceSobolevENormL1`; `MemForceR` and `ClassicalSolutionR` are `Data`'s).
The structure bridge `toA02` (`axioms_f1n1.lean:56-68`) is field-by-field over all
ten fields of `Data.ClassicalSolutionR` (`velocity, pressure, horizon_pos,
velocity_smooth, pressure_smooth, initial, divergence, momentum, sobolev,
pressure_gradient`) with no coercion or side condition — it elaborates, so every
field type is defeq.  Every conformance theorem is `fun … => <library theorem> …`
with no extra hypothesis and no tactic.

### 4. Proof spot-audit (not requested, done anyway — all clean)

* `sobolevENorm_eq`: `le_antisymm` of `sobolevENorm_le_of_isSobolevDatum` and
  `le_iInf` + `isSobolevDatum_unique`.  Identical to `A03/VectorTameProduct.lean:71`.
* `memL1Hm_of_memForceR`: `iInf_le` at the witness `⟨G, hpath, h1.1⟩` then
  `ne_top_of_le_ne_top h1.2.ne`.  Sound.
* `exists_boundedIntoHOne_of_memForceR`: `K := ENNReal.ofReal C`.  Degenerate
  `b < 0` is harmless — `Icc 0 b = ∅` makes the conclusion vacuous; for `b ≥ 0`,
  `hC 0` forces `C ≥ 0`, so `ofReal C` does not collapse.
* `continuousOn_sobolevNormAt_of_datumPath`: `(hGc.norm).congr`, with the
  pointwise identity `(sobolevENorm s (u(t,·))).toReal = ‖G t‖` via
  `sobolevENorm_eq`, `← ofReal_norm`, `ENNReal.toReal_ofReal (norm_nonneg _)`.
  Sound; note it never needs finiteness as a hypothesis because the datum
  supplies it.
* `intervalIntegrable_highContinuationIntegrand`: `ContinuousOn.intervalIntegrable`
  after `Set.uIcc_of_le htt`, with `Icc t₀ t ⊆ Ico 0 T` from `0 ≤ t₀`, `t < T`.
  Sound.  (The `simp only [Nat.cast_ofNat]` step inside is redundant — finding 3.)

Module wiring matches the established lane convention (A02 lanes 032/033 did the
same): the new modules are reachable from `research/A04/axioms_f1n1.lean` and are
not added to `formalization/NSFormalization.lean`, which carries no `Section4`
imports at all.  CI (`.github/workflows/contracts.yml`) runs `make check` only.

## Commands, verbatim

```
cd WT && bash scripts/lean-install.sh                                   -> == OK
. WT/scripts/lean-env.sh ; export LEAN_NUM_THREADS=6
cd WT/verification && lake build NSFormalization.Section4.A04.Forcing \
                                 NSFormalization.Section4.A04.Continuity
                                                                        -> Build completed successfully (9880 jobs). EXIT=0
cd WT/verification && lake env lean ../formalization/NSFormalization/Section4/A04/Forcing.lean     -> no output, EXIT=0
cd WT/verification && lake env lean ../formalization/NSFormalization/Section4/A04/Continuity.lean  -> no output, EXIT=0
cd WT/verification && lake env lean ../research/A04/axioms_f1n1.lean    -> 10/10 [propext, Classical.choice, Quot.sound], EXIT=0
cd WT/verification && lake env lean /tmp/lane039_rfl_check.lean         -> EXIT=0 (20 rfl examples; scratch deleted)
cd WT/verification && lake env lean /tmp/lane039_natcast2.lean          -> EXIT=1  ((1:ℕ):ℝ) = (1:ℝ) is NOT rfl
cd WT/verification && lake env lean /tmp/lane039_natcast3.lean          -> EXIT=0  ((2:ℕ):ℝ) = (2:ℝ) IS rfl
cd WT/verification && lake env lean /tmp/lane039_probe.lean             -> probe 1 (no Nat.cast_ofNat rewrite needed) OK;
                                                                           probe 2 (order-1 cast) fails as expected
cd WT && grep -nE "sorry|admit|native_decide|axiom|maxHeartbeats" <3 files>  -> comments and #print axioms only
cd WT && make check                                                     -> EXIT=0
```
