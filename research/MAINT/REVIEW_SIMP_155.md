# REVIEW — lane 155-SIMP-d01-c01-dedup (opus reviewer, 2026-09-14)

Branch `erenup/155-SIMP-d01-c01-dedup` @ `af21f47`, base `86bf360` (the branch predates the V3
`EnergyAbsorptionPartial` contract on integration, so all contract checks use `--base-ref 86bf360`).
Read-only review: no edits to lane files, no git state changes.  One new probe written
(`research/MAINT/probes/rev155_negative.lean`) and this file.

## Verdict: **ACCEPT-WITH-NOTES**

Two cosmetic notes (N1 doc-only in a module this lane did not touch, N2 bookkeeping).  **Nothing
blocking.**  The key property holds: *no theorem or definition that survives in the seven touched
modules changed its statement*, and every dependent compiles.

---

## 1. What the lane changed

A simplifier/tester pass over seven merged Section 4 modules — six mechanical items plus a tester
sweep, no new mathematics on the critical path:

1. **F3 hoist** — the a.e. Fourier transport `coord_smul_deriv_ae` existed twice: inline as `heq`
   inside `memLp_coord_smul_datum` (`D01/FiniteOrderConstructor`) and as a standalone copy in
   `D01/FiniteOrderNorm`.  One canonical copy now lives in `FiniteOrderConstructor.lean:159`;
   `memLp_coord_smul_datum` consumes it, `FiniteOrderNorm` gets it by import.
2. **F2 sharp constants** — six *additive* new lemmas in `FiniteOrderNorm`, headed by the Plancherel
   identity `eLpNorm_raiseIntegrand_sq_eq` and the `4^m` constructor.
3. **C01 rename** — `continuous_jetLp_sumField` → `sumField_jetLp_continuous`.
4. **A04 → D01 layering** — `isSobolevDatum_zero` sunk from `A04/PressureDrop` to `D01/SmoothDatum`;
   `A04/ZeroSolution` drops `import …A04.PressureDrop`.
5. **A01 retirement** — the three order-restricted `CarrierWords` theorems subsumed by lane 153's
   `L2Descent` full-order versions.
6. **Tester** — six conformance files and six negative probes updated.

---

## 2. What is in Lean now — the statement-invariance table

Method: for each of the seven modules, `git show 86bf360:<file>` vs HEAD, declaration headers
extracted mechanically (namespace-qualified name + binders + type, normalised whitespace, truncated
at the top-level `:=`) and compared.  **Result: `changed = 0` in all seven modules.**

| module | common decls | **changed** | removed | added |
|---|---|---|---|---|
| `D01/FiniteOrderConstructor.lean` | 7 | **0** | 0 | 1 |
| `D01/FiniteOrderNorm.lean` | 14 | **0** | 1 | 6 |
| `D01/SmoothDatum.lean` | 33 | **0** | 0 | 1 |
| `A04/PressureDrop.lean` | 9 | **0** | 1 | 0 |
| `A04/ZeroSolution.lean` | 11 | **0** | 0 | 0 |
| `C01/JetPaths.lean` | 17 | **0** | 1 | 1 |
| `A01/CarrierWords.lean` | 7 | **0** | 3 | 0 |

### Every removed / renamed / moved declaration, with its consumer proof

| decl | what happened | consumers outside `research/` at HEAD |
|---|---|---|
| `D01.coord_smul_deriv_ae` | **moved**, `FiniteOrderNorm.lean:150` → `FiniteOrderConstructor.lean:159`. **Fully-qualified name unchanged** (both files are `namespace …Section4.D01`), so no call site can notice. Byte-identical: `diff` of the old 55-line block against the new one is **empty**. | `FiniteOrderNorm.eLpNorm_coord_smul_eq` and `memLp_coord_smul_datum`, both compile. |
| `A04.isSobolevDatum_zero` → `D01.isSobolevDatum_zero` | **namespace changed.** Statement and proof byte-identical (`theorem isSobolevDatum_zero (s : ℝ) : IsSobolevDatum s (fun _ : Space => (0 : Space)) 0`, proof `intro i ψ; simp`), `SmoothDatum.lean:246`. | `grep -rn 'A04.isSobolevDatum_zero' formalization verification` → **0 hits** at HEAD *and* at base `86bf360` (no call site was ever qualified). Bare-name users are `PressureDrop.lean:206,207` (resolves through its existing non-selective `open NSFormalization.Section4.D01`, `:56`) and `ZeroSolution.lean:57,73,81,104,119,134,151` (added to its *selective* `open …D01 (…)` list). **No `verification/` reference at all.** |
| `C01.continuous_jetLp_sumField` → `C01.sumField_jetLp_continuous` | **renamed**, `JetPaths.lean:158`. Signature byte-identical. | At base the only term-level uses were inside `JetPaths.lean` itself (`:188`) and `research/C01/axioms_jet_paths.lean:30`; both updated. `C01/PressureJetPath.lean` uses **neither** name (verified). `Source/PhysicalBesselSobolev.lean:83` keeps its own `ℂ` version untouched — the rename removes the bare-name ambiguity hazard of LESSONS-109. |
| `A01.word_descent_ae`, `word_descent_ae_partial`, `hword_jet_of_descent` | **retired**, replaced by a `/-! ## Retired: … -/` docstring block at `CarrierWords.lean:234-245` naming the `L2Descent` successors. | `grep -rn` over `formalization/` + `verification/` at HEAD: the only survivors are **docstrings** (`CarrierWords.lean:39,41,42,43`, `L2Descent.lean:152,193`). `L2Descent.lean` never used them at term level — it is built on the *kept* helpers, all seven of which remain reachable (`wordField`, `wordField_field`, `descent_step_ae`, `word_eq_zero_of_mem_zero`, `eLpNorm_jet_component_le`, `locInt_component_lp/_smooth`; none orphaned). Worker's claim confirmed. |

### Consumed constants — byte-identical (item 2 of the brief)

`git diff -U0` hunk headers on `FiniteOrderNorm.lean` settle this mechanically:

```
@@ -33,4  +33,4  @@   docstring only
@@ -142,6 +142,6 @@   docstring only
@@ -149,57 +149,2 @@   the 55-line duplicate coord_smul_deriv_ae removed, 0 added
@@ -338,0 +284,115 @@  PURE INSERTION after norm_raise_le  (sharp identity block)
@@ -425,0 +486,63 @@  PURE INSERTION after norm_isSobolevDatum_le_two (sharp constructor block)
```

Not one line inside `HasWeakDerivsL2Bound`, `weakDerivsBound_mono`, `norm_raise_le`,
`exists_isSobolevDatum_norm_le` (`16^m`), `norm_isSobolevDatum_le_of_memLp_derivs` (`16^m`) or
`norm_isSobolevDatum_le_two` (`256`) was touched — **statements *and* proofs are byte-identical**.
Side-by-side extraction confirms it independently.  Their lane-147/148 consumers are intact:
`A01/OrderTwoCap.lean:135,138,152,174,178` and `C01/PressureJetPath.lean:173`.

### The new sharp lemmas are additive and honest

`eLpNorm_raiseIntegrand_sq_eq` (`FiniteOrderNorm.lean:296`) is an **identity**, not a bound, and the
`‖ξ‖² = ∑ⱼ ξⱼ²` step is used honestly:

* `hns` (`:313`): `‖ξ‖^2 = ∑ j, (ξ j)^2` by `EuclideanSpace.norm_eq` + `Real.sq_sqrt` + `sq_abs` — an
  equality, no inequality anywhere in the proof.
* `‖sobolevBesselWeight 1 ξ‖ = √(1+‖ξ‖²)` is `D01.norm_sobolevBesselWeight_one`
  (`FiniteOrderDatum.lean:81`), checked at the cited line.
* `hreal` (`:318`): `(√(1+‖ξ‖²)·‖Aᵢ‖)² = ‖Aᵢ‖² + ∑ⱼ(|ξⱼ|·‖Aᵢ‖)²` — exact.
* Closed with `lintegral_add_left'` + `lintegral_finsetSum'` (exact splittings), no `le` step.

`norm_raiseHilbert_sq_eq` / `norm_raise_sq_eq` propagate the identity componentwise; the sharp
constructor `exists_isSobolevDatum_norm_le_sharp` (`:496`) is the same induction as the `16^m` one
with `norm_raise_sq_eq` replacing the four-term Cauchy–Schwarz, giving `4^m` by `1 + 3` directions
(`:527-531`).  `4^m ≤ 16^m`, so the sharp results are strictly stronger and nothing downstream is
weakened.  All six new declarations print exactly the three standard axioms.

### Layering (item 3)

* `A04/ZeroSolution.lean` no longer imports `A04.PressureDrop`.
* **Import-closure claim independently measured** (transitive `NSFormalization.*` only, resolved from
  the `import` lines of the base tree via `git archive 86bf360` vs the HEAD tree):
  **base = 109, HEAD = 89.** The claimed 109 → 89 is exact.
* `PressureDrop.lean` still compiles with `isSobolevDatum_zero` coming from D01 **through its existing
  non-selective `open NSFormalization.Section4.D01` (`:56`)** — no alias, no explicit qualification.
  Correct choice: an `A04` alias would have been ambiguous for both A04 consumers, which `open` D01
  (LESSONS-109).
* **No ambiguity anywhere.** Four modules `open` both A04 and D01 (`A01/ForceCap`,
  `A01/GronwallInstance`, `A01/OrderTwoCap`, `A01/AprioriRows`); since `A04.isSobolevDatum_zero` no
  longer exists, the bare name has exactly one interpretation. All four build. Each of the six new
  D01 names and the renamed C01 name has exactly **1** declaration site tree-wide (`formalization/` +
  `vendor/`), so the rename and the additions introduce no new bare-name collision.

### Hygiene (item 5)

* `sorry` / `admit` / `native_decide` / `axiom`: **none** in the seven modules — the only grep hits
  are docstring prose ("No `sorry`, no `axiom`").
* No `set_option` added or removed anywhere in the diff.
* The retired theorems are **not silently deleted**: `CarrierWords.lean:234-245` is a retirement
  block naming `L2Descent.word_descent_ae_full` / `hword_jet_full`, the reason (miscitation hazard
  from two `hword_jet` suppliers with different order hypotheses), the subsumption probe, and the
  list of kept helpers.
* Lane touches **no** `Contracts/` file and **no** `contracts.json`
  (`git diff --name-only 86bf360...HEAD | grep -i contract` is empty).

---

## 3. Gaps / notes

**N1 (cosmetic, doc-only, non-blocking) — two dangling docstring references in a module this lane
did not touch.** `Section4/A01/L2Descent.lean:152` ("the descent-to-classical-jet a.e. identity of
`CarrierWords.word_descent_ae`") and `:193` ("…removing the `n + 3 ≤ q + 1` restriction of
`CarrierWords.hword_jet_of_descent`") now name theorems that no longer exist. They still read
correctly as history and `CarrierWords.lean:234` explains the retirement, so this is not a
correctness issue. *Fix (one line each):* append "(retired in lane 155)" at both sites, or requalify
as "the former `CarrierWords.word_descent_ae`". Can also be left for the next A01 lane.

**N2 (bookkeeping) — two numbers in the ATTEMPTS per-item table are loose.** Measured
`git diff --numstat`: item 1 `FiniteOrderConstructor` **+48/−36** ✓ exact; item 2 `FiniteOrderNorm`
**+184/−61** ✓ exact; item 4 `SmoothDatum` **+9/−0** ✓ exact; item 3 `JetPaths` is recorded as
"(+12/−?)" but is actually **+7/−5** (12 = total lines *touched*, not added); item 5 `CarrierWords`
is recorded as "−~100 net" but is **+26/−120 = −94 net**. Everything else in the table checks out.

**N3 (note, no action) — a non-vacuity example was dropped, but coverage is preserved elsewhere.**
`research/A01/axioms_carrier_words.lean` lost the concrete `u = 0, U = 0, Z = zeroField` instance
that exercised the retired assembly end-to-end. The successor is covered: `axioms_l2_descent.lean:14`
prints axioms for `hword_jet_full`, and `research/A01/probes/rev153_consumer.lean:27` fires it on a
concrete instance. Both re-run green here (EXIT=0, 0 errors), so no coverage regression — but worth
recording that `axioms_carrier_words` is now helpers-only.

No other gaps. The three points the brief flagged as the highest risk — the qualified-`A04` consumer,
the rename's consumers, and the `L2Descent` term-level use of the retired trio — are all **clean**.

---

## 4. Commands and results

All from the worktree with `. scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`, lake from `verification/`.
(Note: the module list must be word-split explicitly — zsh does not split unquoted `$VAR`, LESSONS
2026-09-14; a first attempt passed all 125 modules as one target and failed with `unknown target`.)

| command | result |
|---|---|
| `lake build` **entire Section 4 tree** (125 modules) | **`Build completed successfully (10510 jobs)`, exit 0.** Zero errors. Every warning in the log is pre-existing, from `vendor/HeliCorgi/Formal/*` or `NSFormalization/Source/*`; none from the seven touched modules. |
| `make test` | **exit 0**, **25/25 contracts** "checked; standard logical axioms only" (…`TameProduct`, `EnergyAbsorptionPartialV2` last). |
| `make test-mutations` | **exit 0** — `implementation_refactor: accepted`; `admitted_proof` / `extra_axiom` / `weakened_hypothesis` `rejected as required`; `Mutation suite passed`. |
| `make check` | **exit 0** — 13 policy tests OK, `30 work items: ownership, contract registration and task cards consistent.` |
| `check_contracts.py --base-ref 86bf360` | **exit 0**, `"base_compatibility_checked": true`. |
| `check_contracts.py --base-ref origin/erenup/integration` | `AssertionError: Removed stable specification: verification/Contracts/V3/EnergyAbsorptionPartial.lean` — **reproduced and confirmed as stale-base noise**: that file does not exist on this branch's base, and the lane touches no `Contracts/` file. Lead re-runs after rebase. |
| `experiments/build_changed_lean.py` | **exit 0**, `Build completed successfully (10226 jobs)` — the touched modules sit inside a CI-compiled closure. |
| import closure of `A04.ZeroSolution` (transitive `NSFormalization.*`), base vs HEAD | **109 → 89**, matching the claim exactly. |

**Conformance files** (`lake env lean`), every declaration printing exactly
`[propext, Classical.choice, Quot.sound]` — axiom lists parsed across line wraps:

| file | exit | decls | non-standard |
|---|---|---|---|
| `research/D01/axioms_finite_order_norm.lean` | 0 | 21 (incl. all 6 new F2 lemmas **and** the untouched `16^m`/`256` trio) | 0 |
| `research/D01/axioms_finite_order_close.lean` | 0 | 9 (incl. hoisted `coord_smul_deriv_ae`) | 0 |
| `research/C01/axioms_jet_paths.lean` | 0 | 18 (incl. renamed `sumField_jetLp_continuous`) | 0 |
| `research/MAINT/axioms_144.lean` | 0 | 11 | 0 |
| `research/A04/axioms_hpr.lean` | 0 | 10 (incl. `D01.isSobolevDatum_zero`, now qualified) | 0 |
| `research/A01/axioms_carrier_words.lean` | 0 | 8 | 0 |

**Negative probes** — each fails at the line the worker recorded, for the intended reason:

```
rev145_mutA_drop_sum.lean:312:23  error: unsolved goals
rev145_mutB_4pow.lean:410:37      error: unsolved goals
rev145_mutC_64.lean:426:41        error: unsolved goals
rev146_mutation.lean:33:91,40:73  error: unsolved goals
rev144_mutation.lean:27:4,34:40,41:55  unsolved goals / Application type mismatch / Type mismatch
rev153_mut1_slice.lean:56:57      error: Function expected at
```
Positive control `research/A01/probes/rev153_subsumes.lean` (the three retired statements re-proved
from the `L2Descent` full versions): **EXIT=0**, so the retirement loses no theorem.
`axioms_l2_descent.lean` and `rev153_consumer.lean`: **EXIT=0**, 0 errors.

**Reviewer's own negative check** (brief item 6) — new file
`research/MAINT/probes/rev155_negative.lean`, `set_option autoImplicit false` throughout so a deleted
hypothesis cannot be silently re-bound (LESSONS 077):

* *Part 1, the **moved** lemma.* CONTROL — the consumer term of
  `ZeroSolution.hasSmoothSobolevPath_zero` / `zeroSol.sobolev`,
  `⟨fun _ => 0, fun t _ => ok _, contDiffOn_const⟩`, elaborates against the real statement:
  **no error**. MUTANT 1 — the same term against a weakened `∃ A, IsSobolevDatum s 0 A` (datum merely
  *exists*, not `= 0`) **breaks as expected**:
  ```
  rev155_negative.lean:35:32: error: Type mismatch
    weakened ?m.18
  has type   ∃ A, IsSobolevDatum ?m.18 (fun x => 0) A
  but is expected to have type   IsSobolevDatum (↑m) (fun x => 0 (t, x)) ((fun x => 0) t)
  ```
* *Part 2, the **hoisted** lemma.* POSITIVE — `coord_smul_deriv_ae hA hC hw i j` typechecks at exactly
  the claimed `(2πi)·(ξⱼ•Aᵢ) =ᵐ frequencyUnit·(C j i)` type: **no error**, pinning that the hoist
  did not drift. MUTANT 2 — doubling the constant on the right **breaks as expected**:
  ```
  rev155_negative.lean:75:2: error: Type mismatch
    coord_smul_deriv_ae hA hC hw i j
  has type   … =ᵐ[volume] fun ξ => ↑frequencyUnit * ↑↑↑((C j).ofLp i) ξ
  but is expected to have type   … =ᵐ[volume] fun ξ => ↑(2 * frequencyUnit) * ↑↑↑((C j).ofLp i) ξ
  ```
  (Trap for the next reader: `mut` is a reserved token in this Lean — name the hypothesis something
  else, or the file fails with `unexpected token 'mut'` before any real check runs.)

`git status --short` in the worktree shows only the untracked
`research/MAINT/probes/rev155_negative.lean` — the reviewer changed no lane file and no git state.
