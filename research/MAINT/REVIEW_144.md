# REVIEW — lane 144-MAINT-zero-solution (opus reviewer, 2026-09-14)

Branch `erenup/144-MAINT-zero-solution`, HEAD `d6635a8`, base `origin/erenup/integration` (`ed22b2f`).
Read-only review. Probes added by the reviewer live in `research/MAINT/probes/rev144_*.lean`.

**Verdict: ACCEPT-WITH-NOTES.** The mathematics is sound, every declaration is stated against the
tree's own definitions, all 11 declarations carry exactly the standard three axioms, the module
elaborates silently, `make check` is green, and the witness is genuinely usable downstream (it
crosses the registered `Bindings` bridge into the frozen contract structure). The notes are three
one-line cosmetics plus one layering observation; none blocks the merge.

---

## 1. What the lane claims

Land the zero classical solution **once** so later conformance/probe files stop rebuilding it:
`memForceR_zero`, `zero_mem_initialClassR`, `zeroSol`, `zeroSol_velocity/_pressure`,
`sobolevNormAt_zero`, `gradientSobolevNormAt_zero`, `hasSmoothSobolevPath_zero`, `path_zero`,
`jets_zero`, `const_not_jets` in `formalization/NSFormalization/Section4/A04/ZeroSolution.lean`,
plus a retarget of `research/A01/axioms_a3_m2.lean` onto the new module.

## 2. What is actually in Lean

### 2.1 Statements — every one against the tree's definitions, nothing restated

The module contains **no `def`/`structure` restatement at all**: it `open`s the tree's names and
states everything over them. Checked identifier by identifier:

| declaration | file:line | stated over | definition at |
|---|---|---|---|
| `memForceR_zero : MemForceR (0 : SpaceTimeField)` | `A04/ZeroSolution.lean:72` | `D01.MemForceR` | `Section4/D01/ForceClass.lean:158` |
| `zero_mem_initialClassR : (0 : SpatialField) ∈ initialClassR` | `:80` | `A02.initialClassR` = `{a \| MemHInfty a ∧ IsSolenoidal a}` | `Section4/A02/SolutionClass.lean:97` (`MemHInfty` `:88`, `IsSolenoidal` `:92`) |
| `zeroSol … : ClassicalSolutionR ν 0 0 T` | `:91` | `A02.ClassicalSolutionR` | `Section4/A02/SolutionClass.lean:114` |
| `zeroSol_velocity`, `zeroSol_pressure` | `:106`, `:109` | projections, `rfl`, `@[simp]` | — |
| `sobolevNormAt_zero (s t) = 0` | `:116` | `A04.sobolevNormAt` | `Section4/A04/Forcing.lean:74` |
| `gradientSobolevNormAt_zero (s t) = 0` | `:124` | `A04.gradientSobolevNormAt` | `Section4/A04/LaplacianDatum.lean:86` |
| `hasSmoothSobolevPath_zero T` | `:148` | `A04.HasSmoothSobolevPath` | `Section4/A04/DerivNorm.lean:87` |
| `path_zero ν T hν hT` | `:154` | the `zeroSol.velocity` specialisation | — |
| `jets_zero` | `:162` | `D01.SmoothSquareIntegrableJets` | `Section4/D01/DatumToJets.lean:118` |
| `const_not_jets (hc : c ≠ 0)` | `:174` | same | same |

`ClassicalSolutionR` here **is** the single A02 local restatement of `Contracts/V1/Data.lean:624`
— the `Restrict.lean` §0 lineage, moved verbatim into `Section4/A02/SolutionClass.lean` by lane 040
and documented as such in `Section4/A02/Restrict.lean:31-40`. It is **not** a new inductive type:
probe P4 (`research/MAINT/probes/rev144_positive.lean:29`) type-checks `zeroSol ν T hν hT` at
`NSFormalization.Section4.A02.ClassicalSolutionR ν 0 0 T`, and probe P7
(`research/MAINT/probes/rev144_contract_bridge.lean`) pushes it through the *registered* bridge
`BlowupDensity.Bindings.maximalPartial_ofA02` (`verification/Bindings/MaximalPartial.lean:74`)
into the frozen `BlowupDensity.Contracts.V1.Data.ClassicalSolutionR ν 0 0 T`. EXIT 0.

### 2.2 `zeroSol` — all ten fields, honestly discharged

`ClassicalSolutionR` (`SolutionClass.lean:114-138`) has ten fields; all ten are supplied.

* `velocity := 0`, `pressure := 0` (`:92-93`).
* `horizon_pos := hT` (`:94`) — `hT` is load-bearing.
* `velocity_smooth`, `pressure_smooth` := `contDiffOn_const` (`:95-96`) — `ContDiffOn ℝ ∞ 0` on
  `Ico 0 T ×ˢ univ`. Honest.
* `initial := fun _ => rfl` (`:97`) — target is `velocity (0,x) = a x` with `a = 0`, so `0 = 0`.
* `divergence` (`:98`) — `∀ t ∈ Ico 0 T, ∀ x, spatialDivergence 0 t x = 0`, discharged by unfolding
  `spatialDivergence`/`spatialDerivative` (`vendor/…/NavierStokes/ProblemStatement.lean:67`).
* `momentum` (`:99-102`) — the **genuine** eq:NS residual clause at interior times:
  `navierStokesResidual ν 0 0 t x = (0 : SpaceTimeField) (t,x)`, i.e. residual `= f = 0`.
  `navierStokesResidual` is the pinned upstream one, `vendor/…/NavierStokes/R3/ProblemStatement.lean:57`.
  Probe P5 (`rev144_positive.lean:34`) re-states the field's exact type and accepts `.momentum`, so
  no field is quietly weaker than the structure's. Honest.
* `sobolev := fun m => ⟨fun _ => 0, continuousOn_const, fun t _ => isSobolevDatum_zero _⟩` (`:103`)
  — **the continuous datum path is the constant-`0` path** `fun _ => (0 : RealVectorSobolev (m:ℝ))`
  with `continuousOn_const` on `Ico 0 T`, and the datum used is the **existing tree lemma**
  `isSobolevDatum_zero` at `Section4/A04/PressureDrop.lean:170` — **no fresh duplicate was
  created**, and there is no other `IsSobolevDatum`-of-zero lemma anywhere in
  `formalization/` (grep: only `PressureDrop.lean:170,205,206`). Probe P6
  (`rev144_positive.lean:41`) re-states the field's full type, including `ContinuousOn G (Ico 0 T)`,
  and accepts `.sobolev m`. Honest.
* `pressure_gradient` (`:104`) — `∀ t ∈ Ico 0 T, MemLp (fun x => pressureGradient 0 t x) 2 volume`;
  `pressureGradient` is upstream (`ProblemStatement.lean:71`), a sum of `fderiv`s of the constant
  `0`, hence `0 ∈ L²`. Honest.

`_hν : 0 < ν` is genuinely unused and correctly underscored: no field of `ClassicalSolutionR`
constrains the sign of `ν` (`ν • Δ0 = 0`), so the zero solution exists at any viscosity. The binder
is interface-matching, not a hidden constraint. The ATTEMPTS note says exactly this and is correct.

### 2.3 `const_not_jets` — the non-integrability is real

`const_not_jets` (`:174-187`) reduces `SmoothSquareIntegrableJets (fun _ => c)` at order `0` to
`MemLp (fun _ : Space => c) 2 volume` (via `eLpNorm_congr_norm_ae` + `norm_iteratedFDeriv_zero`),
then applies `memLp_const_iff`, whose two disjuncts are `c = 0` (killed by `hc`) and
`volume (univ : Set Space) < ⊤` (killed because `Space = EuclideanSpace ℝ (Fin 3)` has infinite
volume). That second killer is the genuine mathematical content and I verified it independently:
probe P1 (`rev144_positive.lean:18`) proves `volume (univ : Set Space) = ⊤`. So yes — this is real
non-integrability of a nonzero constant on `R³`, not a definitional accident.

### 2.4 `sobolevNormAt_zero` / `gradientSobolevNormAt_zero` are not vacuous

`sobolevNormAt_zero` goes through `A04.sobolevENorm_eq` (`Section4/A04/Forcing.lean:126`), whose
proof uses datum **uniqueness** (`D01.isSobolevDatum_unique`), so the infimum in `sobolevENorm`
really collapses to `‖0‖ₑ` — it is not the "junk `⊤`/junk `0`" case that `logs/LESSONS.md` warns
about. `gradientSobolevNormAt_zero` first proves `partialDeriv j 0 = 0` pointwise, then uses the
finiteness-guarded `gradientSobolevNormAt_sq_eq_sum` (`LaplacianDatum.lean:105`) with an explicit
`hfin` supplied from `hz` — the guard is discharged, not dodged.

Bare `sobolevENorm_eq` resolves unambiguously: two copies exist
(`A03/VectorTameProduct.lean:71`, `A04/Forcing.lean:126`) but the module is *inside* namespace
`…Section4.A04` and only `open`s A03 for `partialDeriv`, so the A04 copy wins by namespace
resolution. No repeat of the lane-109 ambiguity.

### 2.5 Non-vacuity downstream (the point of the lane)

`research/A01/axioms_a3_m2.lean` retargets cleanly: `§0`'s inline reconstruction
(`datum_zero`, `zeroSol`, `memForceR_zero`, `zero_mem_initialClassR`, `path_zero`,
`sobolevNormAt_zero` — 60 lines) is deleted and replaced by
`import NSFormalization.Section4.A04.ZeroSolution` + an `open`. The file still exercises the A3
m = 2 statements **non-vacuously**: `nonvac_highOrder_bddAbove_of_kbnd` and
`nonvac_highOrder_bddAbove_all_orders_of_kbnd` instantiate
`A01.highOrder_bddAbove_of_kbnd` / `…_all_orders_of_kbnd` at
`ν = 1`, `a = 0`, `f = 0`, `T = 1`, `m = 3`, `T₀ = 1`, `Kbnd = 0` on
`zeroSol 1 1 one_pos one_pos`, feeding the **whole** hypothesis package (`one_pos`,
`zero_mem_initialClassR`, `memForceR_zero`, `memL1Hm_of_memForceR memForceR_zero`, the solution,
`path_zero 1 1 one_pos one_pos`, `le_rfl : 3 ≤ 3`, `one_pos`, `le_rfl`, `kbnd_zero`). The audit-only
`kbnd_zero` (order-2 cap `= 0`) correctly stays local. All four `#print axioms` are standard.

### 2.6 Dedup: is anything already in the tree or a `simp` one-liner?

* **No prior tree copy.** `grep -rn 'sobolevNormAt_zero|sobolevENorm_zero|jets_zero'` over
  `formalization/` + `verification/` returns *only* the new module. `isSobolevDatum_zero` is the
  one pre-existing fact, and it is reused rather than duplicated.
* **None is a `simp` one-liner.** Probe `research/MAINT/probes/rev144_simp_dedup.lean` tries
  `by simp` on all six substantive statements from the imports alone; all six fail with
  `simp made no progress`. The module earns its place.
* **Files that can now import instead of rebuilding** (the lane deliberately retargeted only the
  first; the rest are listed in `ATTEMPTS_144.md` §"Other places" and I verified the inventory is
  accurate and complete):
  * `research/A01/axioms_a3_m2.lean` — **done this lane**.
  * `research/A01/probes/rev142_probe4_spatialfield.lean:37-77` — full rebuild
    (`datum_zero`, `zeroSol`, `memForceR_zero`, `zero_mem_initialClassR`, `path_zero`,
    `sobolevNormAt_zero`). Can import.
  * `research/D01/negative_simp_p2.lean:30-100` — `datum_zero`, `jets_zero`, `zeroSol`,
    `memForceR_zero`, `const_not_jets`. Can import.
  * `research/A01/axioms_a3_force.lean:35` — `memForceR_zero` only. Can import.
  * `research/A04/negative_simp_sl3{,_fail}.lean` — `datum_zero_of_weakenedNoHL` is a **different**
    object (datum under a weakened hypothesis). Correctly excluded.
  * Review `.md` appendices carrying the same inline code (records, not compiled):
    `research/D01/REVIEW_SL8_ASSEMBLY.md`, `REVIEW_SL8_PREP.md`, `REVIEW_CONTRACT_V3.md`,
    `research/A04/REVIEW_CONTRACT.md`, `REVIEW_CONTRACT_V2.md` carry a literal `def zeroSol`;
    `research/A04/REVIEW_ENERGY_HIGH.md`, `REVIEW_G2B.md`, `REVIEW_HPR.md`,
    `REVIEW_HIGH_CONTINUATION.md`, `research/D01/REVIEW_SIMP_P2.md`,
    `research/A01/REVIEW_A3_M2.md`, `A3_SPLIT.md` reference it in prose. Nothing to do.

### 2.7 Hygiene

* No `sorry` / `admit` / `axiom` / `native_decide` anywhere in the module (grep returns only the
  substring `axioms_a3_m2.lean` inside a docstring source list).
* **No `set_option` at all**, hence no `maxHeartbeats`. Nothing to check against the ≤ 400000 rule.
* **No `paper/…:NN` citation anywhere in the module** — so there is nothing to mis-cite, and the
  lane cannot propagate a stale line number (`logs/LESSONS.md`, the "行号引用会代代相传" entry).
  The docstrings instead cite `research/*.md` sources and `A04/PressureDrop:170`; I opened
  `PressureDrop.lean:170` and it is exactly `theorem isSobolevDatum_zero (s : ℝ) : …`. ✓
* The module elaborates with **zero warnings of its own** (`lake env lean` on the file: silent).

### 2.8 Placement (`A04/` vs `A02/` / `D01/`) — MAINT only, not blocking

`A04/` is **correct and forced**: `sobolevNormAt`, `gradientSobolevNormAt` and
`HasSmoothSobolevPath` are A04 definitions (`Forcing.lean:74`, `LaplacianDatum.lean:86`,
`DerivNorm.lean:87`), so no A02- or D01-level module could state
`sobolevNormAt_zero` / `gradientSobolevNormAt_zero` / `hasSmoothSobolevPath_zero`. The module
docstring's "lowest layer whose imports suffice" argument is right.

The refinement worth recording (finding 4 below): the *cheap half* of the lane — `zeroSol`,
`memForceR_zero`, `zero_mem_initialClassR`, `jets_zero`, `const_not_jets` — needs only A02 + D01,
and the only reason the whole module sits above `A04.PressureDrop` is the three-line
`isSobolevDatum_zero`. Measured import closure (transitive `NSFormalization.*` only):

| module | closure |
|---|---|
| `A04.ZeroSolution` | 109 |
| same, without the `A04.PressureDrop` import | 88 |

i.e. `PressureDrop` alone drags in **20 extra modules** — the whole Leray-multiplier / pressure
stack (`D01.LerayMultiplier`, `LeraySymbol`, `LerayDatum`, `LerayLowering`, `Longitudinal`,
`Transverse`, `OrderZero{Datum,Symbol,Curl,Algebra}`, `RealPairing`, `LaplacianPairing`,
`MomentumSlice`, `Pressure`, `PressureJets`, `DivergenceTime`, `HalfOrder`,
`A04.{MomentumDatum,TimeDerivative,PressureDrop}`) — for one three-line lemma. Consumers like
`research/D01/negative_simp_p2.lean` (a D01-level probe) pay all of it to retarget.

## 3. Gaps / findings

| # | sev | where | finding | exact fix |
|---|---|---|---|---|
| 1 | minor | `A04/ZeroSolution.lean:88` | `zeroSol`'s docstring says "Every field is discharged by `simp`" — false for 7 of the 10 fields (`velocity_smooth`/`pressure_smooth` = `contDiffOn_const`, `initial` = `rfl`, `horizon_pos` = `hT`, `sobolev` = an explicit triple; only `divergence`, `momentum`, `pressure_gradient` use `simp`). | replace "Every field is discharged by `simp`" with "The analytic fields are discharged by unfolding (`simp`); the rest are `contDiffOn_const` / `rfl` / the constant-`0` datum path". |
| 2 | minor | `A04/ZeroSolution.lean:55-61` | four opened names are never used in code: `memForceR_of_memForceCompact` (mentioned only in the `:41` docstring prose), `MemHInfty`, `IsSolenoidal`, `SpaceTimeScalar`, `RealVectorSobolev`. Harmless (Lean does not warn), but the LESSONS-109 ambiguity hazard grows with every superfluous `open`. | drop those five names from the three `open` lines. |
| 3 | minor | module docstring | no `paper/` anchor at all. The three objects assembled do have canonical anchors — `initialClassR` = `paper/sections/02-preliminaries.tex:12-13` (eq:Rinitial, `X_R = H^∞ ∩ L²_σ`), `MemForceR` = `:17-22` (eq:Rclasses), eq:NS = `paper/sections/01-introduction.tex:4`. I opened all three lines and they say what would be claimed. | add one line to the header: "Manuscript anchors: `X_R` = `02-preliminaries.tex:12-13` eq:Rinitial, `F_R` = `02-preliminaries.tex:17-22` eq:Rclasses, eq:NS = `01-introduction.tex:4`." |
| 4 | note (MAINT, do not block) | layering | `A04.PressureDrop` is imported purely for `isSobolevDatum_zero` and costs +20 modules of closure (§2.8). The clean follow-up is to move `isSobolevDatum_zero` down to `Section4/D01/SmoothDatum.lean` (where `IsSobolevDatum` is defined, `:306` area) and drop the `PressureDrop` import here — it would also let `research/D01/negative_simp_p2.lean` retarget without inheriting the Leray stack. | a separate MAINT lane; nothing to change in 144. |

Nothing found that affects correctness, fidelity, or axiom cleanliness.

## 4. Commands and results

All run in `/data_8T/ping/blowup_density/.claude/worktrees/144-MAINT-zero-solution`, after
`. scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`, lake from `verification/` only.

```
$ cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.A04.ZeroSolution
EXIT=0
Build completed successfully (9942 jobs).
# grep of the log for 'ZeroSolution' or any Section4 diagnostic: no hits.
# The only warnings are the known upstream HeliCorgi/Source/Paper3 linter warnings.

$ cd verification && LEAN_NUM_THREADS=6 lake env lean \
    ../formalization/NSFormalization/Section4/A04/ZeroSolution.lean
EXIT=0
(no output — fresh elaboration of the module is silent)

$ cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/MAINT/axioms_144.lean
EXIT=0
'NSFormalization.Section4.A04.memForceR_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A04.zero_mem_initialClassR' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A04.zeroSol' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A04.zeroSol_velocity' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A04.zeroSol_pressure' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A04.sobolevNormAt_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A04.gradientSobolevNormAt_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A04.hasSmoothSobolevPath_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A04.path_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A04.jets_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A04.const_not_jets' depends on axioms: [propext, Classical.choice, Quot.sound]
# all 11 = exactly [propext, Classical.choice, Quot.sound]

$ cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/A01/axioms_a3_m2.lean
EXIT=0
'NSFormalization.Section4.A01.highOrder_bddAbove_of_kbnd' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.highOrder_bddAbove_all_orders_of_kbnd' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Lane142.nonvac_highOrder_bddAbove_of_kbnd' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lane142.nonvac_highOrder_bddAbove_all_orders_of_kbnd' depends on axioms: [propext, Classical.choice, Quot.sound]
# no warnings; the two non-vacuity theorems still fire on the imported zeroSol

$ make check
EXIT=0
python3 experiments/check_formalization_plan.py --check   → 30 tasks, missing_copied_imports []
python3 experiments/check_contracts.py                    → 24 registered contracts, closures OK
python3 experiments/test_contract_policy.py               → Ran 13 tests … OK
python3 experiments/check_work_queue.py                   → 30 work items: ownership, contract
                                                             registration and task cards consistent.
```

### Negative (mutation) probes — `research/MAINT/probes/rev144_mutation.lean`

Each block replays the module's own proof with `0` replaced by a **nonzero constant field `c`**
(`hc : c ≠ 0` in context, `set_option autoImplicit false` so nothing is silently re-bound —
`logs/LESSONS.md`, the 077 entry). All three break, each at exactly the step where zero-ness is
load-bearing:

```
$ cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/MAINT/probes/rev144_mutation.lean
EXIT=1
../research/MAINT/probes/rev144_mutation.lean:27:4: error: unsolved goals
case inl
c : Space
hc : c ≠ 0
x : Space
m : Fin 0 → Space
i✝ : Fin 3
⊢ c.ofLp i✝ = 0
../research/MAINT/probes/rev144_mutation.lean:34:40: error: Application type mismatch: The argument
  isSobolevDatum_zero ↑m
has type
  IsSobolevDatum (↑m) (fun x => 0) 0
but is expected to have type
  NSFormalization.Section4.A02.IsSobolevDatum (↑m) (fun x => c) 0
in the application
  Exists.intro 0 (isSobolevDatum_zero ↑m)
../research/MAINT/probes/rev144_mutation.lean:41:55: error: Type mismatch
  isSobolevDatum_zero s
has type
  IsSobolevDatum s (fun x => 0) 0
but is expected to have type
  IsSobolevDatum s (fun x => c) 0
```

* **M1** (`jets_zero` at a nonzero constant): the `n = 0` branch reduces to `c i = 0` — i.e. the
  order-0 jet of a constant is that constant, and only `c = 0` makes it `L²`-trivial. This is the
  exact statement `const_not_jets` proves *false*, so the pair is consistent.
* **M2** (`zero_mem_initialClassR` at a nonzero constant): the `MemHInfty` datum witness no longer
  unifies — a nonzero constant has no order-`m` Sobolev datum.
* **M3** (`sobolevNormAt_zero` at a nonzero constant): same, at the `sobolevENorm_eq` step.

None of these is the forbidden "drop an argument and re-apply" check (`logs/LESSONS.md`, 113).

### Positive probes — `research/MAINT/probes/rev144_positive.lean`, `rev144_contract_bridge.lean`

```
$ cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/MAINT/probes/rev144_positive.lean
EXIT=0
$ cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/MAINT/probes/rev144_contract_bridge.lean
EXIT=0
```

P1 `volume (univ : Set Space) = ⊤` (the real content of `const_not_jets`);
P2 `@D01.MemForceR = @A02.MemForceR := rfl` (the docstring's defeq claim — **true**);
P3 the D01 witness is accepted where an `A02.MemForceR` is demanded;
P4 `zeroSol` inhabits `A02.ClassicalSolutionR`;
P5 the `momentum` field has the full eq:NS-residual type at interior times;
P6 the `sobolev` field carries `ContinuousOn G (Ico 0 T)` plus the datum clause at every time;
P7 `BlowupDensity.Bindings.maximalPartial_ofA02 (zeroSol …) : Contracts.V1.Data.ClassicalSolutionR ν 0 0 T`.

### Dedup probe — `research/MAINT/probes/rev144_simp_dedup.lean`

```
$ cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/MAINT/probes/rev144_simp_dedup.lean
EXIT=1  — 6 errors, all `simp made no progress` (lines 19, 20, 21, 23, 24, 25)
```

`MemForceR 0`, `0 ∈ initialClassR`, `sobolevNormAt s 0 t = 0`, `gradientSobolevNormAt s 0 t = 0`,
`HasSmoothSobolevPath T 0`, `SmoothSquareIntegrableJets 0` — none is reachable by `simp` from the
imports alone. The lane is not re-proving something the tree already hands out.

---

## Lead follow-up

Findings 1–3 are three one-line edits (docstring wording, five `open` names, one anchor line) and
can be batched into the next A04 simplifier lane rather than bounced back to the worker. Finding 4
is a separate MAINT lane (move `isSobolevDatum_zero` from `A04/PressureDrop.lean:170` down to
`D01/SmoothDatum.lean`, drop the `PressureDrop` import here, then retarget
`research/D01/negative_simp_p2.lean`, `research/A01/probes/rev142_probe4_spatialfield.lean`,
`research/A01/axioms_a3_force.lean`).
