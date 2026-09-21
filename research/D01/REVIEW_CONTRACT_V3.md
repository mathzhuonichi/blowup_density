# REVIEW — lane 120 (D01 / P2 contract V3 = `D01.datum_lemmas_v3`)

Reviewer run in the lane worktree `.claude/worktrees/120-D01-p2-contract-v3`
(branch `erenup/120-D01-p2-contract-v3`, one commit `b7eff94` on merge-base `8aab657`).
Under review: `verification/Contracts/V3/DatumLemmas.lean`, `verification/Bindings/DatumLemmasV3.lean`,
`verification/Tests/DatumLemmasV3.lean`, `verification/contracts.json` (+11 lines),
`research/D01/{ATTEMPTS_CONTRACT_V3.md,axioms_contract_v3.lean}`.
Probes: `/tmp/rev120/` — reproduced in the appendices so nothing is lost when `/tmp` is cleared
(`logs/LESSONS.md` 2026-09-14).

## Verdict: **ACCEPT-WITH-NOTES**

The three fields are the review-§6 / appendix-C statements verbatim, every vocabulary item resolves
to the canonical `Contracts.V1` declaration, the record is inhabited by a closed value with standard
axioms only, the hypothesis class is inhabited at contract level, A04's `hP` slot is discharged
directly, and all four gates are green at 22 contracts. Nothing is weakened, nothing frozen is
touched.

Notes: one **wrong manuscript citation repeated nine times, including inside the scope string that
is about to freeze** (finding 0 — `02-preliminaries.tex:76-81` is the Leray-projection paragraph and
`eq:projected`, not `eq:Rpressure`; the right range is `:89-94`); one **wrong recorded reason** for the one deliberate omission (finding 1 — the omission itself
is right, the justification in the frozen scope string is not, and a contract-vocabulary form of the
same content is provable today, in 20 lines, shown below); one **new fact the lead should book**
(finding 2 — this is the first registered contract whose audited closure reaches vendored HeliCorgi);
and four wording/consistency items. None is a reason to hold the merge.

---

## 1. Compiles / policy / hygiene — **PASS**

| command (worktree root, after `. scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`) | result |
|---|---|
| `cd verification && lake build Tests.DatumLemmasV3` | `Build completed successfully (10015 jobs).` |
| `make check` | exit 0 |
| `make test` | exit 0, **22** contracts |
| `make test-mutations` | exit 0 |
| `python3 experiments/check_contracts.py --base-ref origin/erenup/integration` | `"registered_contracts": 22`, `"base_compatibility_checked": true` |
| `cd verification && lake env lean ../research/D01/axioms_contract_v3.lean` | exit 0, 4 × standard axioms |

Build tail, verbatim:

```
ℹ [10015/10015] Replayed Tests.DatumLemmasV3
info: Tests/DatumLemmasV3.lean:31:0: Contract BlowupDensity.Tests.checkedDatumLemmasV3: checked; standard logical axioms only
Build completed successfully (10015 jobs).
```

`make check` tail:

```
python3 experiments/test_contract_policy.py
.............
Ran 13 tests in 0.040s
OK
python3 experiments/check_work_queue.py
30 work items: ownership, contract registration and task cards consistent.
```

`make test`: `grep -c 'standard logical axioms only'` = **22**, i.e. every previously registered
contract still passes and the new one is the 22nd. `make test-mutations` tail:

```
implementation_refactor: accepted
admitted_proof: rejected as required
extra_axiom: rejected as required
weakened_hypothesis: rejected as required
Mutation suite passed. This is an infrastructure check, not a PDE proof.
```

**`/V3/` path requirement** (`experiments/check_contracts.py:118`,
`assert f'/V{contract["version"]}/' in contract['specification']`): the entry has `"version": 3`
and `"specification": "verification/Contracts/V3/DatumLemmas.lean"` — satisfied. No lakefile change
was needed (the `Contracts` library globs), and the closure/registration asserts at
`check_contracts.py:109-140` all pass, including
`assert registered_tests == {m for m in modules if m.startswith('Tests.')}`.

**Diff scope.** `git diff 8aab657 --name-status`:

```
A	research/D01/ATTEMPTS_CONTRACT_V3.md
A	research/D01/axioms_contract_v3.lean
A	verification/Bindings/DatumLemmasV3.lean
A	verification/Contracts/V3/DatumLemmas.lean
A	verification/Tests/DatumLemmasV3.lean
M	verification/contracts.json
```

Five additions plus `contracts.json`; `git diff 8aab657 --numstat -- verification/contracts.json`
= `11  0` and `git diff … | grep '^-' | grep -v '^---'` is **empty** — purely additive. No
`Contracts/V1/*`, `Contracts/V2/*`, `Bindings/DatumLemmas*.lean` (V1/V2) or `Tests/DatumLemmas*.lean`
(V1/V2) file appears in the diff at all, so the frozen-V1/V2 rule is respected structurally, not just
by convention.

**Hygiene.** `grep -rnE 'sorry|admit|axiom|native_decide|set_option|maxHeartbeats'` over the three
Lean deliverables returns **zero** hits. The only hits in the whole diff are in the research probe
`research/D01/axioms_contract_v3.lean` (four `#print axioms` lines plus prose), which is the intended
use. No `set_option`, no heartbeat bump, no `@[simp]` attribute added.

## 2. Statement fidelity — **PASS**, with findings 1/3/4/5

### (a) The three fields are the recorded targets, character for character

`research/D01/REVIEW_SL8_ASSEMBLY.md` §6 "Exact field statements" / appendix C `Field1/2/3` versus
`Contracts/V3/DatumLemmas.lean:128-131`, `:137-140`, `:152-156`: identical modulo indentation. Field 1
is also `research/D01/P2_SPLIT.md`'s "Target" block verbatim
(`SmoothSquareIntegrableJets (fun x : Space => pressureGradient u.pressure t x)` for
`u : ClassicalSolutionR ν a f T`, `hf : MemForceR f`, `t ∈ Ioo (0:ℝ) T`).

Fully-qualified field types (`set_option pp.fullNames true`, `/tmp/rev120/fid.lean`, appendix A):

```
BlowupDensity.Contracts.V3.DatumLemmas.DatumLemmasV3API.solution_slice_pressureGradient_smoothJets : ∀
  (self : BlowupDensity.Contracts.V3.DatumLemmas.DatumLemmasV3API) (ν : ℝ)
  (a : BlowupDensity.Contracts.V1.Data.SpatialField) (f : BlowupDensity.Contracts.V1.Data.SpaceTimeField) (T : ℝ)
  (u : BlowupDensity.Contracts.V1.Data.ClassicalSolutionR ν a f T),
  BlowupDensity.Contracts.V1.Data.MemForceR f →
    ∀ t ∈ Set.Ioo 0 T,
      BlowupDensity.Contracts.V1.SmoothSquareIntegrableJets fun x =>
        BlowupDensity.Contracts.V1.pressureGradient u.pressure t x
```

(fields 2 and 3 likewise, appendix A). **Every vocabulary item is the canonical one**:
`Contracts.V1.Data.{SpatialField, SpaceTimeField, ClassicalSolutionR, MemForceR, IsSobolevDatum}`,
`Contracts.V1.{pressureGradient, temporalDerivative}` (Packet, `:115`/`:99`), and
`Contracts.V1.SmoothSquareIntegrableJets` (GradientL6 `:106`). The last one matters: there are **two**
byte-identical `SmoothSquareIntegrableJets` in the V1 tree — `Contracts.V1` (GradientL6) and
`Contracts.V1.BoundedRep` (BoundedRepresentative `:152`) — and the field resolves to the first, which
is the one `Bindings.DatumLemmas.datumLemmas_smoothSquareIntegrableJets_eq` pins. `RealVectorSobolev`
is `NSFormalization.Paper3`'s on both sides (a canonical module, not a restatement).

### (b) `SmoothSquareIntegrableJets` vs the manuscript's `H^∞` — **closed inside the record**

`paper/sections/02-preliminaries.tex:89-94` (the `eq:Rpressure` environment is `:90-92`):

> On $\R^3$ we require `∇p=(I-\PP)(f-\nabla\cdot(u\otimes u))=:G`.
> For smooth $H^\infty$ data, $G$ is smooth and its Fourier transform is parallel to $\xi$.

The manuscript's `H^∞` is `Contracts.V1.Data.MemHInfty` (`Data.lean:495`, `ContDiff ∞` + a datum at
every integer order). The jet class the V3 field uses is tied to it by an **already registered V1
field in the very same record**, `memHInfty_iff_smoothJets` (`Contracts/V1/DatumLemmas.lean:196`). So
the manuscript's conclusion for the gradient is derivable from field 1 with no implementation module
in sight (`/tmp/rev120/redundancy.lean`, appendix D):

```lean
theorem memHInfty_pressureGradient (A : Contracts.V3.DatumLemmas.DatumLemmasV3API) … :
    MemHInfty (fun x : Space => pressureGradient u.pressure t x) :=
  (A.memHInfty_iff_smoothJets _).mpr
    (A.solution_slice_pressureGradient_smoothJets ν a f T u hf t ht)
```
`'Rev120Red.memHInfty_pressureGradient' depends on axioms: [propext, Classical.choice, Quot.sound]`.

So field 1 is a **definitional rendering** of eq:Rpressure's regularity conclusion, not a weakening.

The same probe shows **field 3 is derivable from field 1 + `memHInfty_iff_smoothJets`** inside the
record (`field3_from_field1_and_v1`, standard axioms). Field 3 therefore carries no independent
content and cannot be inconsistent with field 1; it is a convenience shape, exactly as the field
docstring says. Registering it is still right — see (d).

`Ioo` vs the paper: the manuscript states eq:Rpressure as a requirement on the solution class with no
time range; `P2_SPLIT.md`'s recorded target, `ClassicalSolutionR.momentum` (imposed on `Ioo 0 T`) and
the C01 consumer are all `Ioo`. So `Ioo` is the **exact** recorded target, and the contract says so
(`:125-127`). `t = 0` is listed as not asserted. Good.

### (c) Non-vacuity at contract level — **PASS**, both directions

`/tmp/rev120/vacuity.lean` (appendix B) rebuilds the lane-117 reviewer's `zeroSol` **retargeted from
`A02.ClassicalSolutionR` to `Contracts.V1.Data.ClassicalSolutionR`** (all ten fields discharged,
`sobolev` and `pressure_gradient` included), plus `memForceR_zero : MemForceR (0 : SpaceTimeField)`,
and fires the contract fields on it:

```
'Rev120NV.field1_on_zeroSol' depends on axioms: [propext, Classical.choice, Quot.sound]
'Rev120NV.field3_on_zeroSol' depends on axioms: [propext, Classical.choice, Quot.sound]
'Rev120NV.const_not_jets' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`memForceR_zero` is not a loophole: `forceTimeMeasure = volume.restrict (Ioi 0)` is infinite, so
`memLp_const_iff` forces the datum path to be genuinely zero. `const_not_jets` is the other
direction — a nonzero constant field is `ContDiff ℝ ∞` but **not** in
`Contracts.V1.SmoothSquareIntegrableJets` — so the conclusion is not true of every smooth field.
The API itself is a closed value: `#check BlowupDensity.Tests.checkedDatumLemmasV3` gives
`: BlowupDensity.Contracts.V3.DatumLemmas.DatumLemmasV3API`, `#print axioms` standard.

### (d) A04's `hP` slot is discharged **directly** by field 3

`Section4/A04/MomentumDatum.lean:149` is
`hP : IsSobolevDatum (m : ℝ) (fun x => pressureGradient w.pressure t x) P`. `/tmp/rev120/a04_hp.lean`
(appendix C) supplies it from the contract alone — one `obtain`, no extra hypothesis about the
pressure, no `by`-block mathematics:

```lean
  obtain ⟨P, hP⟩ :=
    Tests.checkedDatumLemmasV3.solution_slice_pressureGradient_exists_datum ν a f T u hf t ht m
  exact ⟨P, hP,
    NSFormalization.Section4.A04.momentum_datum (Bindings.uniqueness_toA02 u) hf hm hGd hGc ht
      hL hN hP hF⟩
```
```
'Rev120.momentum_datum_from_contract' depends on axioms: [propext, Classical.choice, Quot.sound]
```
Note the direction works because the probe starts from a **contract** solution `u` and hands
`uniqueness_toA02 u` to A04; `(uniqueness_toA02 u).{pressure,velocity}` reduce by `rfl`, so `hP`
stated for `u.pressure` is accepted for `w.pressure`. Booking "A04 eq:Rhigh's `hP` input unblocked"
is now justified from the registry, not only from the implementation module.

### (e) The two `rfl` bridges in `Bindings` are exactly the ones needed

The fields are stated with `Contracts.V1.{pressureGradient,temporalDerivative}` (Packet) while the
`PressureJets.lean` theorems conclude with `NavierStokes.ProblemStatement.{…}` — so
`datumLemmasV3_pressureGradient_eq` and `datumLemmasV3_temporalDerivative_eq` are the two load-bearing
pins, and no other new bridge is required. The remaining restatements already have bridges imported
transitively through `Bindings.DatumLemmasV2 → Bindings.DatumLemmas`:
`datumLemmas_smoothSquareIntegrableJets_eq` (`:60`), `datumLemmas_memForceR_eq` (`:118`) and —
needed by field 3 and not mentioned in the lane's ATTEMPTS — `datumLemmas_isSobolevDatum_eq` (`:46`).
`ClassicalSolutionR` is the `CLAUDE.md` structure exception and goes through
`Bindings.uniqueness_toA02`, correctly. All `#print axioms` on the bridges are standard (appendix A).

### (f) The omitted order-`m` identity — see **finding 1**

## 3. Consistency — **PASS**, with findings 2/6/7

* **Import policy.** `Contracts/V3/DatumLemmas.lean` imports `Contracts.V2.DatumLemmas` and
  `Contracts.V1.Packet` only, both `Contracts.*`; `check_contracts.py`'s
  `contract_import_allowed` gate passes. The module contains **no** `def`/`abbrev`/`structure` other
  than `DatumLemmasV3API` itself, so there is nothing restated and nothing that can drift.
* **Conventions vs V2.** `open` set, `noncomputable section`, `extends`, docstring layout
  ("Why a new version" / "What changed, exactly" / "Out of scope" / "Self-containedness") and the
  `{ datumLemmasV2 with … }` binding shape all mirror `Contracts/V2/DatumLemmas.lean` and
  `Bindings/DatumLemmasV2.lean`. One deliberate divergence, for the better — finding 6.
* **The `Ioo` restriction** is stated in the module docstring, in field 1's docstring and in the
  registry scope. Consistent everywhere.
* **Scope string.** It supersedes the V1/V2 sentence explicitly and lists all four non-assertions the
  brief asks for: the identity (in both spellings), `t = 0`, the scalar `p`, and A01's
  `IsLerayComplement pressure_recovery`. Two wording imprecisions: findings 4 and 5.
* **Citations spot-checked and all correct**: `PressureJets.lean:93/128/141/150`,
  `Data.lean:160/544`, `Packet.lean:99/115`, `GradientL6.lean:106`, `Uniqueness.lean:79,83`,
  `Contracts/V1/DatumLemmas.lean:269` (`solution_slice_pressureGradient_contDiff`, on `Ico 0 T`).
* **`work_items.json` skipped** — correct, finding 7.

## 4. Honesty of `ATTEMPTS_CONTRACT_V3.md` — **PASS**

Both recorded negative examples reproduce. `/tmp/rev120/negA.lean` (opening
`BlowupDensity.Contracts.V1` **and** `NavierStokes.ProblemStatement`, i.e. review §6's *prose* open
set, then stating field 1):

```
/tmp/rev120/negA.lean:15:39: error: Ambiguous term
  Space
Possible interpretations:
  NavierStokes.ProblemStatement.Space : Type

  BlowupDensity.Contracts.V1.Space : Type
```
(identical to the ATTEMPTS text; the real output has a blank line between the two interpretations).
`/tmp/rev120/negB.lean`:

```
/tmp/rev120/negB.lean:5:62: error: Type mismatch
  rfl
has type
  ?m.3 = ?m.3
but is expected to have type
  BlowupDensity.Contracts.V1.Data.ClassicalSolutionR = NSFormalization.Section4.A02.ClassicalSolutionR
```
Verbatim, including the direction of the equation. The ATTEMPTS' command table is accurate: every
row was re-run and matches (§1 above), including the `10015 jobs` figure.

One omission, not a defect: the ATTEMPTS' "Bridges" section lists the `SmoothSquareIntegrableJets`
and `MemForceR` bridges as the pre-existing ones relied on, but field 3 also relies on
`datumLemmas_isSobolevDatum_eq` (`Bindings/DatumLemmas.lean:46`). It exists and is imported, so the
binding is sound; only the note is incomplete.

---

## 5. Findings

| # | severity | finding |
|---|---|---|
| 0 | **medium** | **The manuscript citation for P2 is wrong, and it is repeated nine times — including in `contracts.json`'s scope string.** Every occurrence reads `paper/sections/02-preliminaries.tex:76-81`. That range is the **Leray-projection paragraph and `eq:projected`** (`:76-81` = "The Leray projection `P` has Fourier symbol … The projected equation is" + `\begin{equation}\label{eq:projected}`). `eq:Rpressure` is at **`:89-94`**: `:89` "On `R^3` we require", `:90-92` the equation environment, `:93-94` "For smooth `H^∞` data, `G` is smooth …". `paper/sections/02-preliminaries.tex` has not been touched since `b01490b` (`git log -- paper/sections/02-preliminaries.tex`), so this is not drift — the range was wrong when written; it was inherited from `research/D01/REVIEW_SL8_ASSEMBLY.md` §2(b), which quotes the right text under the wrong number, and copied forward. Occurrences: `Contracts/V3/DatumLemmas.lean:6,24,101,116,133,142`, `Bindings/DatumLemmasV3.lean:10`, `Tests/DatumLemmasV3.lean:15`, `research/D01/ATTEMPTS_CONTRACT_V3.md`, and one in the `D01.datum_lemmas_v3` **scope string**. The Lean statements are unaffected — fidelity to the *text* is confirmed independently in §2(a)/(b) — but the citation is the audit trail from a frozen contract back to the manuscript, and this one lands on a different equation. **Cheapest fix, and worth doing before merge** (the scope string cannot be edited afterwards): `sed -i 's/02-preliminaries\.tex:76-81/02-preliminaries.tex:89-94/g'` over the four files plus the `contracts.json` entry, then re-run `make check && make test`. `research/D01/REVIEW_SL8_ASSEMBLY.md` should get the same correction so the next lane does not re-copy it. |
| 1 | **medium** | **The recorded reason for not registering the order-`m` identity is wrong, and a contract-vocabulary form of the same content is provable today.** `Contracts/V3/DatumLemmas.lean:55-65` and the registry scope both say the identity cannot be stated "because its statement names the momentum residual, an A01/MomentumSlice notion outside `Contracts/V1/Data` vocabulary". The residual is **not** the obstruction: `f (t, x)`, `advection` and `spatialLaplacian` are all `Contracts.V1.Packet` (`:107`, `:120`), so `h = f − (u·∇)u + νΔu` writes out in contract vocabulary directly. The real obstruction is the **operator** `(I−P)ₘ : RealVectorSobolev m → RealVectorSobolev m` (`D01.Leray.lerayComplement`), which has no `Contracts/V1` counterpart — `grep` over `Contracts/V1/*.lean` for `leray\|Leray\|Helmholtz` finds only `IsSolenoidal` and prose. The **decision stands** (do not register now), but the justification that gets frozen with the contract is misleading and would steer a V4 lane away from work that is in fact available. Concretely, the operator-free form of the identity — the Helmholtz split `datumᵐ h = datumᵐ ∂ₜu + datumᵐ ∇p` — is statable in pure contract vocabulary **and provable in ~20 lines with standard axioms** (`/tmp/rev120/v4note.lean`, appendix E, `'Rev120V4.splitIdentity' depends on axioms: [propext, Classical.choice, Quot.sound]`). Together with V1's already-registered datum uniqueness it pins `datumᵐ ∇p` from `Am` and `datumᵐ ∂ₜu`, which is the consumable half of eq:Rpressure at order `m`. **Recommend for a V4** (with the transversality clause `(I−P)ₘ datumᵐ ∂ₜu = 0` if a contract-level Leray operator is ever introduced); **not required now**. For this lane the minimum fix would be one sentence in the scope: the blocker is the operator, not the residual. |
| 2 | info (for the lead) | **V3 is the first registered contract whose audited closure reaches vendored HeliCorgi.** `check_contracts.py` closures: `D01.datum_lemmas` 1127 modules / **0** `Formal.*`; `_v2` 1134 / **0**; `A02.uniqueness` 1183 / **0**; `_v3` **1251 / 28** `Formal.*` (`R3Leray*`, `R3Stokes*`, `FlowMap*`, `PDEBridgeAdapter`, …), entering through `Section4/D01/LeraySymbol.lean` and `LerayMultiplier.lean`. No rule is broken — `Tests/DatumLemmasV3.lean` imports only `Contracts.V3.DatumLemmas`, `Bindings.DatumLemmasV3`, `TestSupport.Axioms`, so `warningAsError = true` is not tripped (the 52 vendor warnings are attributed to the `Formal` library), and `checkAxioms` reports standard axioms only, so there is no trust leak. **No `FormalPatched.*` module is pulled in** (checked). But `make test`'s audited surface now spans HeliCorgi, so a vendor bump or a toolchain change can break a *registered contract* rather than only a research module. Worth a line in `PLAN.md` / `NEXT_SESSION.md`. |
| 3 | low | **"Strengthens the V1 field" is true only on the interior.** `Contracts/V3/DatumLemmas.lean:122-124` says field 1 "strengthens the V1 field `solution_slice_pressureGradient_contDiff` (spatial `C^∞` only) to full `H^∞` regularity". V1's field is on `Ico 0 T` (`Contracts/V1/DatumLemmas.lean:271`), V3's on `Ioo 0 T`, so the conclusion is strengthened but the domain is narrowed — it is not a strengthening in the ordering sense. The next sentence discloses the `Ioo` restriction, so no reader is actually misled; "strengthens … on the interior" would be exact. |
| 4 | low | **The supersession sentence in the scope is over-broad by one word.** V1's sentence is "any Sobolev datum or jet class for **the pressure or its gradient**"; the V3 scope quotes it and answers "that datum and jet class are now asserted, on Ioo 0 T", which is true only for the **gradient**. The scalar-`p` half is correctly re-listed under "Not asserted" three clauses later, so the scope is self-correcting; the one sentence read alone is not. |
| 5 | info | **Only the registry scope sentence is superseded, not V1's docstring claim.** `Contracts/V1/DatumLemmas.lean:66-71` says `SmoothSquareIntegrableJets (∇p(t,·))` does not follow **from the class as specified** — that remains **true**, and provably so: lane 117's theorem adds `hf : MemForceR f`, which is not a field of `ClassicalSolutionR`, and `Section4/D01/Pressure.lean:62-66` records a counterexample without a force hypothesis (lane-117 review finding 1). `Contracts/V3/DatumLemmas.lean:29` ("So the V1 'no pressure datum' sentence is superseded") elides the distinction, though the preceding sentence does state the force hypothesis. Keep the distinction visible if a V4 docstring revisits this. |
| 6 | info (good) | **The V3 regression guard is stronger than V2's, deliberately.** V2 has `def datumLemmas_of_v2 : DatumLemmasAPI := datumLemmasV2.toDatumLemmasAPI` (type-level only); V3 has `theorem datumLemmasV3_toDatumLemmasV2API_eq : datumLemmasV3.toDatumLemmasV2API = Bindings.datumLemmasV2 := rfl`, which additionally pins the **witness**, not just the type. Verified `rfl` and standard axioms. Recommend V4 and any future versioned contract copy the V3 form. |
| 7 | info | **Skipping `work_items.json` is right, and matches precedent exactly.** `git log -S datum_lemmas -- collaboration/work_items.json` is **empty** — V1 and V2 were never listed either. D01 is `kind: "specification"` with `contracts: []`; `experiments/check_work_queue.py:21` asserts only `set(item['contracts']) <= registered` (empty is fine) and `:22-23` requires non-empty only for `proof`/`assembly` items. `experiments/tasks.py:20,34` render the card from `item['contracts']`, so with `[]` unchanged `tasks.py render` is provably a no-op and `collaboration/tasks/D01.md:29` stays "Registered component contracts: none yet." That line is now stale in spirit — D01 has three registered contracts — but the gap predates this lane. If the lead wants it fixed, do it as a one-off `MAINT` pass across D01 V1/V2/V3 at once, not inside this lane. |

---

## 6. Commands run (worktree root, after `. scripts/lean-env.sh`)

| command | result |
|---|---|
| `cd verification && LEAN_NUM_THREADS=6 lake build Tests.DatumLemmasV3` | `Build completed successfully (10015 jobs).`; `checked; standard logical axioms only` |
| `make check` | exit 0; `test_contract_policy` 13 OK; `check_work_queue` "30 work items … consistent" |
| `make test` | exit 0; 22 × "standard logical axioms only" |
| `make test-mutations` | exit 0; `implementation_refactor: accepted`, other three `rejected as required` |
| `python3 experiments/check_contracts.py --base-ref origin/erenup/integration` | exit 0; `registered_contracts: 22`; `base_compatibility_checked: true` |
| `cd verification && lake env lean ../research/D01/axioms_contract_v3.lean` | exit 0; 4 × `[propext, Classical.choice, Quot.sound]` |
| `cd verification && lake env lean /tmp/rev120/fid.lean` | exit 0; field types fully qualified; 5 × standard axioms |
| `cd verification && lake env lean /tmp/rev120/vacuity.lean` | exit 0; 3 × standard axioms |
| `cd verification && lake env lean /tmp/rev120/a04_hp.lean` | exit 0; standard axioms |
| `cd verification && lake env lean /tmp/rev120/redundancy.lean` | exit 0; 2 × standard axioms |
| `cd verification && lake env lean /tmp/rev120/v4note.lean` | exit 0; standard axioms |
| `cd verification && lake env lean /tmp/rev120/negA.lean` / `negB.lean` | the two recorded errors, verbatim |
| `git diff 8aab657 --name-status` / `--numstat -- verification/contracts.json` | 5 additions + `contracts.json` `11 0`; no deletions |
| `grep -rnE 'sorry\|admit\|axiom\|native_decide\|set_option\|maxHeartbeats'` on the 3 Lean deliverables | 0 hits |
| `git log -S datum_lemmas -- collaboration/work_items.json` | empty |
| `sed -n '76,81p;89,94p' paper/sections/02-preliminaries.tex` | `:76-81` = Leray projection + `eq:projected`; `:89-94` = `eq:Rpressure` + "For smooth `H^∞` data …" (finding 0) |
| `grep -rn '02-preliminaries.tex:76-81'` over the lane's files + `contracts.json` | 9 + 1 occurrences |

---

## Appendix A — `/tmp/rev120/fid.lean` (field types, closed value, bridges)

```lean
import Tests.DatumLemmasV3

set_option pp.fullNames true

open BlowupDensity

#check @Contracts.V3.DatumLemmas.DatumLemmasV3API.solution_slice_pressureGradient_smoothJets
#check @Contracts.V3.DatumLemmas.DatumLemmasV3API.solution_slice_temporalDerivative_smoothJets
#check @Contracts.V3.DatumLemmas.DatumLemmasV3API.solution_slice_pressureGradient_exists_datum
#check @Contracts.V3.DatumLemmas.DatumLemmasV3API.toDatumLemmasV2API
#check Tests.checkedDatumLemmasV3
#print axioms Tests.checkedDatumLemmasV3
#print axioms Bindings.datumLemmasV3
#print axioms Bindings.datumLemmasV3_toDatumLemmasV2API_eq
#print axioms Bindings.datumLemmasV3_pressureGradient_eq
#print axioms Bindings.datumLemmasV3_temporalDerivative_eq
```

Output (fields 2 and 3, and the axiom lines):

```
… solution_slice_temporalDerivative_smoothJets : ∀
  (self : …DatumLemmasV3API) (ν : ℝ)
  (a : BlowupDensity.Contracts.V1.Data.SpatialField) (f : BlowupDensity.Contracts.V1.Data.SpaceTimeField) (T : ℝ)
  (u : BlowupDensity.Contracts.V1.Data.ClassicalSolutionR ν a f T),
  BlowupDensity.Contracts.V1.Data.MemForceR f →
    ∀ t ∈ Set.Ioo 0 T,
      BlowupDensity.Contracts.V1.SmoothSquareIntegrableJets fun x =>
        BlowupDensity.Contracts.V1.temporalDerivative u.velocity t x
… solution_slice_pressureGradient_exists_datum : ∀
  (self : …DatumLemmasV3API) … ,
  BlowupDensity.Contracts.V1.Data.MemForceR f →
    ∀ t ∈ Set.Ioo 0 T,
      ∀ (m : ℕ),
        ∃ P,
          BlowupDensity.Contracts.V1.Data.IsSobolevDatum (↑m)
            (fun x => BlowupDensity.Contracts.V1.pressureGradient u.pressure t x) P
… toDatumLemmasV2API : …DatumLemmasV3API → BlowupDensity.Contracts.V2.DatumLemmas.DatumLemmasV2API
BlowupDensity.Tests.checkedDatumLemmasV3 : BlowupDensity.Contracts.V3.DatumLemmas.DatumLemmasV3API
'BlowupDensity.Tests.checkedDatumLemmasV3' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.datumLemmasV3' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.datumLemmasV3_toDatumLemmasV2API_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.datumLemmasV3_pressureGradient_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.datumLemmasV3_temporalDerivative_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Appendix B — `/tmp/rev120/vacuity.lean` (contract-level non-vacuity)

```lean
import Tests.DatumLemmasV3

open Set MeasureTheory
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1.Data
open NSFormalization.Paper3 (RealVectorSobolev)
open scoped ContDiff

namespace Rev120NV

theorem datum_zero (s : ℝ) : IsSobolevDatum s (fun _ : Space => (0 : Space)) 0 := by
  intro i ψ
  simp

/-- The zero solution with zero force on `[0,1)`, as a **contract** solution. -/
def zeroSol (ν : ℝ) : ClassicalSolutionR ν 0 0 1 where
  velocity := 0
  pressure := 0
  horizon_pos := zero_lt_one
  velocity_smooth := contDiffOn_const
  pressure_smooth := contDiffOn_const
  initial := fun _ => rfl
  divergence := by
    intro t _ x
    simp [spatialDivergence, spatialDerivative]
  momentum := by
    intro t _ x
    simp [NavierStokesR3.ProblemStatement.navierStokesResidual, temporalDerivative, advection,
      spatialDerivative, spatialLaplacian, pressureGradient]
  sobolev := fun m => ⟨fun _ => 0, continuousOn_const, fun t _ => datum_zero _⟩
  pressure_gradient := by
    intro t _
    simp [pressureGradient]

theorem memForceR_zero : MemForceR (0 : SpaceTimeField) := by
  refine ⟨contDiffOn_const, fun m => ⟨fun _ => 0, fun t _ => datum_zero _, contDiffOn_const, ?_, ?_⟩⟩
  · exact MemLp.zero
  · exact MemLp.zero

theorem field1_on_zeroSol (ν : ℝ) :
    BlowupDensity.Contracts.V1.SmoothSquareIntegrableJets
      (fun x : Space => BlowupDensity.Contracts.V1.pressureGradient (zeroSol ν).pressure (1/2) x) :=
  BlowupDensity.Tests.checkedDatumLemmasV3.solution_slice_pressureGradient_smoothJets
    ν 0 0 1 (zeroSol ν) memForceR_zero (1/2) (by constructor <;> norm_num)

theorem field3_on_zeroSol (ν : ℝ) (m : ℕ) :
    ∃ P : RealVectorSobolev (m : ℝ),
      IsSobolevDatum (m : ℝ)
        (fun x : Space => BlowupDensity.Contracts.V1.pressureGradient (zeroSol ν).pressure (1/2) x) P :=
  BlowupDensity.Tests.checkedDatumLemmasV3.solution_slice_pressureGradient_exists_datum
    ν 0 0 1 (zeroSol ν) memForceR_zero (1/2) (by constructor <;> norm_num) m

theorem const_not_jets {c : Space} (hc : c ≠ 0) :
    ContDiff ℝ ∞ (fun _ : Space => c) ∧
      ¬ BlowupDensity.Contracts.V1.SmoothSquareIntegrableJets (fun _ : Space => c) := by
  refine ⟨contDiff_const, ?_⟩
  rintro ⟨-, h⟩
  have h0 := h 0
  have hconst : MemLp (fun _ : Space => c) 2 volume := by
    refine ⟨aestronglyMeasurable_const, ?_⟩
    have h2 := h0.2
    rwa [eLpNorm_congr_norm_ae (f := iteratedFDeriv ℝ 0 (fun _ : Space => c))
      (g := fun _ : Space => c)
      (Filter.Eventually.of_forall (fun x => by simp [norm_iteratedFDeriv_zero]))] at h2
  rcases (memLp_const_iff (p := 2) two_ne_zero (by simp)).mp hconst with hz | hv
  · exact hc hz
  · simp at hv

#print axioms field1_on_zeroSol
#print axioms field3_on_zeroSol
#print axioms const_not_jets

end Rev120NV
```

## Appendix C — `/tmp/rev120/a04_hp.lean` (A04's `hP` from the contract)

```lean
import Bindings.DatumLemmasV3
import Tests.DatumLemmasV3
import NSFormalization.Section4.A04.MomentumDatum

open Set MeasureTheory
open BlowupDensity
open BlowupDensity.Contracts.V1
open BlowupDensity.Contracts.V1.Data
open NSFormalization.Paper3 (RealVectorSobolev)
open scoped ContDiff

namespace Rev120

theorem momentum_datum_from_contract
    {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    (u : ClassicalSolutionR ν a f T) (hf : MemForceR f)
    {m : ℕ} (hm : 2 ≤ m)
    {G : ℝ → RealVectorSobolev (m : ℝ)}
    (hGd : ∀ t ∈ Ico (0 : ℝ) T, IsSobolevDatum (m : ℝ) (fun x => u.velocity (t, x)) (G t))
    (hGc : ContDiffOn ℝ ∞ G (Ico (0 : ℝ) T))
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T)
    {L N F : RealVectorSobolev (m : ℝ)}
    (hL : IsSobolevDatum (m : ℝ) (fun x => NavierStokes.ProblemStatement.spatialLaplacian
      u.velocity t x) L)
    (hN : IsSobolevDatum (m : ℝ) (fun x => NavierStokes.ProblemStatement.advection
      u.velocity t x) N)
    (hF : IsSobolevDatum (m : ℝ) (fun x => f (t, x)) F) :
    ∃ P : RealVectorSobolev (m : ℝ),
      IsSobolevDatum (m : ℝ) (fun x => pressureGradient u.pressure t x) P ∧
      deriv G t = ν • L - N - P + F := by
  obtain ⟨P, hP⟩ :=
    Tests.checkedDatumLemmasV3.solution_slice_pressureGradient_exists_datum ν a f T u hf t ht m
  exact ⟨P, hP,
    NSFormalization.Section4.A04.momentum_datum (Bindings.uniqueness_toA02 u) hf hm hGd hGc ht
      hL hN hP hF⟩

#print axioms momentum_datum_from_contract

end Rev120
```

Negative example recorded on the way: writing `hGc : ContDiffOn ℝ ⊤ G …` instead of `ℝ ∞` (with
`open scoped ContDiff`) gives

```
error: Application type mismatch: The argument
  hGc
has type
  ContDiffOn ℝ ⊤ G (Ico 0 T)
but is expected to have type
  ContDiffOn ℝ (↑⊤) G (Ico 0 T)
```

## Appendix D — `/tmp/rev120/redundancy.lean` (field 3 ⊆ field 1; the manuscript's `H^∞`)

```lean
import Tests.DatumLemmasV3

open Set
open BlowupDensity
open BlowupDensity.Contracts.V1
open BlowupDensity.Contracts.V1.Data
open NSFormalization.Paper3 (RealVectorSobolev)

namespace Rev120Red

theorem field3_from_field1_and_v1
    (A : Contracts.V3.DatumLemmas.DatumLemmasV3API)
    (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) (T : ℝ)
    (u : ClassicalSolutionR ν a f T) (hf : MemForceR f) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) T)
    (m : ℕ) :
    ∃ P : RealVectorSobolev (m : ℝ),
      IsSobolevDatum (m : ℝ) (fun x : Space => pressureGradient u.pressure t x) P :=
  ((A.memHInfty_iff_smoothJets _).mpr
    (A.solution_slice_pressureGradient_smoothJets ν a f T u hf t ht)).2 m

theorem memHInfty_pressureGradient
    (A : Contracts.V3.DatumLemmas.DatumLemmasV3API)
    (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) (T : ℝ)
    (u : ClassicalSolutionR ν a f T) (hf : MemForceR f) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) T) :
    MemHInfty (fun x : Space => pressureGradient u.pressure t x) :=
  (A.memHInfty_iff_smoothJets _).mpr
    (A.solution_slice_pressureGradient_smoothJets ν a f T u hf t ht)

#print axioms field3_from_field1_and_v1
#print axioms memHInfty_pressureGradient

end Rev120Red
```

## Appendix E — `/tmp/rev120/v4note.lean` (finding 1: the identity **is** statable in contract vocabulary)

```lean
import Tests.DatumLemmasV3
import NSFormalization.Section4.A03.VectorTameProduct
import NSFormalization.Section4.D01.DatumToJets

open Set MeasureTheory
open BlowupDensity
open BlowupDensity.Contracts.V1
open BlowupDensity.Contracts.V1.Data
open NSFormalization.Paper3 (RealVectorSobolev)
open scoped ContDiff

namespace Rev120V4

/-- Contract-vocabulary statement.  Only `Contracts.V1.Data` / `Contracts.V1.Packet`
notions appear: `ClassicalSolutionR`, `MemForceR`, `IsSobolevDatum`, `advection`,
`spatialLaplacian`, `temporalDerivative`, `pressureGradient`, `RealVectorSobolev`. -/
def SplitIdentity : Prop :=
  ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) (T : ℝ)
    (u : ClassicalSolutionR ν a f T), MemForceR f → ∀ t : ℝ, t ∈ Ioo (0 : ℝ) T →
    ∀ m : ℕ, 2 ≤ m → ∀ Am D P : RealVectorSobolev (m : ℝ),
      IsSobolevDatum (m : ℝ) (fun x : Space => f (t, x) - advection u.velocity t x
          + ν • spatialLaplacian u.velocity t x) Am →
      IsSobolevDatum (m : ℝ) (fun x : Space => temporalDerivative u.velocity t x) D →
      IsSobolevDatum (m : ℝ) (fun x : Space => pressureGradient u.pressure t x) P →
      Am = D + P

theorem splitIdentity : SplitIdentity := by
  intro ν a f T u hf t ht m hm Am D P hAm hD hP
  have hsR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hcD : ContDiff ℝ ∞ (fun x : Space => temporalDerivative u.velocity t x) :=
    (Tests.checkedDatumLemmasV3.solution_slice_temporalDerivative_smoothJets ν a f T u hf t ht).1
  have hcP : ContDiff ℝ ∞ (fun x : Space => pressureGradient u.pressure t x) :=
    (Tests.checkedDatumLemmasV3.solution_slice_pressureGradient_smoothJets ν a f T u hf t ht).1
  have mD := NSFormalization.Section4.D01.memLp_of_isSobolevDatum hcD hD
  have mP := NSFormalization.Section4.D01.memLp_of_isSobolevDatum hcP hP
  have hsum := NSFormalization.Section4.A03.isSobolevDatum_add hsR
    (NSFormalization.Section4.A03.locIntField_of_memLp mD)
    (NSFormalization.Section4.A03.locIntField_of_memLp mP) hD hP
  have hpt : (fun x : Space =>
        temporalDerivative u.velocity t x + pressureGradient u.pressure t x)
      = fun x : Space => f (t, x) - advection u.velocity t x
          + ν • spatialLaplacian u.velocity t x := by
    funext x
    have hm0 := u.momentum t ht x
    simp only [NavierStokesR3.ProblemStatement.navierStokesResidual] at hm0
    show NavierStokes.ProblemStatement.temporalDerivative u.velocity t x
        + NavierStokes.ProblemStatement.pressureGradient u.pressure t x
      = f (t, x) - NavierStokes.ProblemStatement.advection u.velocity t x
        + ν • NavierStokes.ProblemStatement.spatialLaplacian u.velocity t x
    rw [← hm0]
    module
  rw [hpt] at hsum
  exact NSFormalization.Section4.D01.isSobolevDatum_unique hAm hsum

#print axioms splitIdentity

end Rev120V4
```

Output: `'Rev120V4.splitIdentity' depends on axioms: [propext, Classical.choice, Quot.sound]`.

Negative example on the way: `linear_combination (norm := module) hm0` **fails** here —
`ring`/`module` treat `Contracts.V1.temporalDerivative` and
`NavierStokes.ProblemStatement.temporalDerivative` as different atoms even though they are `rfl`-equal
(`error: ring failed, ring expressions not equal … ⊢ 1 = 0`). The fix is an explicit `show` into one
vocabulary before the algebra tactic — worth a line in `logs/LESSONS.md`.
