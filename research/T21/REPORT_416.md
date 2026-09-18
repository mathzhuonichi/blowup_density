# REPORT_416 — T21 reconciliation (Opus; transcribed by lead from the agent message, report-file guard)

Done. `REPORT_416.md` was not written (report-file guard); the full report follows as instructed by the brief.

---

# Lane 416-SPEC-t21-reconcile — T21 reconciliation report

## 1. What was decided (this is a specification lane — nothing was proved)

Two blind drafts of `cor:nondensity` (`paper/sections/03-torus.tex:506-520`) and `thm:main` (`:6-16`, proof `:522-525`) were reconciled into one binding decision document and one statement-only Lean file. **Base B for both structures**, with draft A's binder order on `fixedInitialDensity` and A's `mainStatement` shape. Both structures are **`Prop`-valued**.

The four findings the brief asked me to settle:

**(a) The canonical/registered `maximalLifespanT` seam — settled, and settled in the *opposite* direction from draft B.** B measured that `Contracts.V1.TorusLocalTheory.maximalLifespanT` is not `rfl`-equal to `NSFormalization.Section3.T10.maximalLifespanT` (the `ClassicalSolutionT` structure exception) and concluded "do not import T20, copy it". That conclusion is wrong: the two are *propositionally* equal by `BlowupDensity.Bindings.TorusLocalTheory.maximalLifespanT_eq` (`/data_8T/ping/blowup_density/.claude/worktrees/416-SPEC-t21-reconcile/verification/Bindings/TorusLocalTheory.lean:270`), proved through the fieldwise `toContract`/`ofContract` conversions, and the *hypotheses* (`forceClassT`, `forceSobolevENormT`/`criticalRho`) need no transport at all — they are `rfl` (`:57,67`). So the reconciled spec states `criticalGlobalRegularity` in **registered** vocabulary and *imports* the canonical T20 record. I checked the whole bridge in Lean and kept it in the file as `Spec.lean` §4:

```lean
example (K : NSFormalization.Section3.T20.CriticalRegularityTAPI)
    (ν : ℝ) (hν : 0 < ν) (g : SpaceTimeField) (hg : g ∈ forceClassT)
    (hsmall : forceSobolevENormT 1 (1 / 2) g < ENNReal.ofReal (K.c * ν)) :
    maximalLifespanT ν (fun _ : Space ↦ 0) g = ⊤ := by
  rw [BlowupDensity.Bindings.TorusLocalTheory.maximalLifespanT_eq]
  exact K.globalRegularity ν hν g hg hsmall
```

This removed ~230 lines of copied T20 record and the whole copied T12 block that both drafts carried.

**(b) `Prop` vs `Type` — `Prop`, for both.** Measured justification, not precedent-citing: T20 is `Type` because `prop:critical` genuinely *selects* `c, C₀, C₁, CH1, Ccriterion` before every `ν, g, T`. T21 selects nothing — `cor:nondensity`'s `c` is T20's and enters as a structure **index**, and `thm:main`'s only number is the literal `1/2`. And the `Type` "registry convention" is only a convention: `Contracts/V1/MainThresholds.lean`'s `MainThresholdsAPI` is `Type`-valued but has **no data field** (all four fields are `Prop`s). Recorded as owner question §3 (1), the same one T19 raised — one ruling should cover T19/T21/T24.

**(c) "a dense subset cannot miss a nonempty open set" (`:519`) — confirmed dropped**, both drafts agree. With `RelativelyDenseT` as the registered ε-form, that sentence *is* the definition instantiated at `g = 0`, `r = ofReal (c*ν)`; a field would be `id`. The spec carries an `example … := rfl` unfolding `RelativelyDenseT` so a reader can see why, and the step is recorded as proof unit N10 (6 lines, mirroring `R41.not_breakdownDenseR_zero_L1`).

**(d) The monotonicity — kept as fields, two of them, unconditional.** `sliceSobolevMonotone` (`:517-518`, the inequality the paper actually displays) and `forceSobolevMonotone` (`:519`, the time-integrated form that upgrades the ball). They are genuinely different statements — the second is an inequality between infima over *strongly measurable paths*. Draft A's extra `g ∈ forceClassT` hypothesis is dropped: its proof never uses it. Draft B's third field `reweightContraction` is dropped as a field (it is the `:517` *justification*, lives in the T10 data layer, and would drag a `NormedAddCommGroup (PeriodicSobolev s)` instance — the one that times out at default heartbeats — into the API); it is recorded as proof unit N1.

Other decisions worth flagging to you: `criticalBallT` is parameterized by `s` (A's ball is fixed at `1/2` and cannot express `:519`); `𝓑⁰` gets its own `breakdownSetTZero` def spelled `fun _ : Space ↦ 0`, *literally* T20's spelling, so the two compose with no rewrite; clause (ii) is a single biconditional (R41 convention); `fixedInitialDensity` uses T19's exact binder order so `d.fixedInitialDensity` discharges it with no shuffling (checked).

**Divergence from both drafts:** the three unconsumed T19 structures (`MixedRegionAPI`, `StrongClosureAPI`, `ProjectionAPI`) are **not** copied. Only `PeriodicDensityAPI` + `periodicDensityStatement` are, verbatim from `research/T19/Spec.lean:184-255` (byte-identity checked with `diff`). A copy nothing reads is drift surface, not policy compliance.

**One hygiene defect found in draft A, measured not asserted.** `DraftA.lean:818,938` declares `structure CriticalRegularityTAPI` inside `namespace NSFormalization.Section3.T20` — the exact fully-qualified name of the canonical module's record. A probe confirms: ``error: `NSFormalization.Section3.T20.CriticalRegularityTAPI` has already been declared``. `DraftA.lean` can therefore never coexist with the real T20 module. Draft B's `BlowupDensity.T20.Spec` namespace is correct.

## 2. What exists in Lean now

`/data_8T/ping/blowup_density/.claude/worktrees/416-SPEC-t21-reconcile/research/T21/Spec.lean` (644 lines, elaborates with 0 errors, no proof of any API field):

- `BlowupDensity.T21.breakdownSetTZero`, `criticalBallT` — the two sets named in the statements, plus three `rfl` drift checks.
- `structure NonDensityAPI (c : ℝ) : Prop` — 9 fields: `hc`, `criticalGlobalRegularity`, `zeroMemBall`, `ballRelativelyOpen`, `sliceSobolevMonotone`, `forceSobolevMonotone`, `criticalBallDisjoint`, `ballDisjoint`, `nonDensity`.
- `structure MainTheoremAPI : Prop` — 5 fields: `thresholdValue`, `zeroInitialClass`, `fixedInitialDensity`, `zeroInitialDensityIff`, `zeroInitialNonDensity`.
- `def nonDensityStatement`, `def mainStatement` — the paper-order aliases (both checked dischargeable from the fields in a scratch file).
- `def nonDensityOfCritical : ∀ K : NSFormalization.Section3.T20.CriticalRegularityTAPI, NonDensityAPI K.c`, `def mainOfDensityAndNonDensity`, `def mainOfInputs` — the assembly signatures, no inhabitant.
- `BlowupDensity.T19.PeriodicDensityAPI` + `periodicDensityStatement`, copied verbatim.
- Every field carries a `-- from DraftA:<line>` / `-- from DraftB:<line>` provenance comment plus a docstring with paper line, exact quantifier order, and a non-vacuity note.

`/data_8T/ping/blowup_density/.claude/worktrees/416-SPEC-t21-reconcile/research/T21/RECONCILIATION.md` (135 lines): §0 lead-review placeholder, §1 the clause-by-clause tables for `cor:nondensity`, `thm:main` and the assembly signatures (A vs B vs decision, every row with a paper line) plus a "False clauses / traps" section, §2 base/threading decision, §3 nine ambiguities and owner questions, §4 sixteen proof units N0–N15 each tagged with its supplier, §5 next steps.

Committed as `70ca6e0c` on `erenup/416-SPEC-t21-reconcile`. No push, merge, or rebase.

## 3. Gaps

- **No field is proved.** The three assembly signatures are arrow types with no inhabitant.
- **Structurally new torus lemmas needed:** N1 (order-lowering weight contraction over `IsPeriodicReweight`) and N3 (a coefficient-side `PeriodicSobolev t →L[ℝ] PeriodicSobolev s` of operator norm ≤ 1 — the torus analogue of `R41.lowerVectorL`, needed so `AEStronglyMeasurable` survives path transport). N4 (`0 ∈ forceClassT`) and N12 (`0 ∈ initialClassT`) are easy. N6 (triangle inequality for `forceSobolevENormT 1 s`) is needed **only** if you keep `ballRelativelyOpen` — see §3 (4) below.
- **Already available, no work:** N0 (the T20 bridge, checked), N5 (`torusForceSobolevENorm_zero`, `formalization/NSFormalization/Section3/T19/Bookkeeping.lean:238`), N11 (`thresholdValue`, `Bookkeeping.lean:55`), N13 (T19's field verbatim). N7–N10, N14, N15 are `ENNReal`/order plumbing with `Section4/R41/NonDensityL1.lean` as a line-by-line template.
- **The whole argument already exists on the torus** in `formalization/NSFormalization/Paper1/PeriodicCriticalRegularity.lean` (`critical_regular_ball:81`, `paper1_main_with_critical_interfaces:99`) and `Paper1/PeriodicMain.lean:59` — but in `TestForce`/`forceDistance`/`lifespan` vocabulary. The gap to this spec is a binding layer, not new mathematics.
- **Registration blocked:** `thm:main` cannot become a `Contracts/V1` file until T19's `PeriodicDensityAPI` and T20's `CriticalRegularityTAPI` register — a contract may import only `Contracts.*`, and the `maximalLifespanT_eq` step would have to move into `Bindings` at that point.
- **The copied T19 block will drift** if `research/T19/RECONCILIATION.md` is amended. A canonical `Section3/T19` module carrying the record (the analogue of what T20 already has) would remove the copy.

## 4. Open questions for you (full list in RECONCILIATION §3)

1. **`Prop` vs `Type`** — decided `Prop`; needs one owner ruling across T19/T21/T24.
2. **Registration order** T19 → T20 → T21, and where the `Bindings` bridge lives after registration.
3. **`zeroInitialNonDensity` kept although derivable** from `zeroInitialDensityIff.mp` (3 lines). `:523` argues for keeping; R41 keeps only the biconditional. Droppable.
4. **`ballRelativelyOpen` kept** although it is the only field the non-density argument does not use, and the only one costing a new structural lemma (N6). `:515` says "relative **open** ball" and `:519` invokes openness. Droppable, and N6 goes with it.
5. `reweightContraction` dropped as a field (kept as N1) — reversible if you want the `:517` mechanism in the API.

## 5. Commands run and results

| command | result |
|---|---|
| `cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T20.CriticalRegularity NSFormalization.Section3.T19.Bookkeeping Bindings.TorusLocalTheory` | `Build completed successfully (10605 jobs)` (not built in this worktree beforehand) |
| `cd verification && lake env lean /tmp/t21probe416.lean` (T20 import + `maximalLifespanT_eq` bridge) | first run: `error: Application type mismatch … Space → NavierStokes.ProblemStatement.Space` — missing `open NavierStokes.ProblemStatement`; after adding it: **0 errors**, both `example`s accepted |
| `cd verification && lake env lean /tmp/t21clash416.lean` | ``error: `NSFormalization.Section3.T20.CriticalRegularityTAPI` has already been declared`` — confirms draft A's namespace defect |
| `cd verification && lake env lean ../research/T21/Spec.lean` | **exit 0, 0 errors**, ~3 s |
| `cd verification && lake env lean /tmp/t21check416.lean` (`#print` of both structures and all five defs) | 9 + 5 fields, all quantifier orders as intended; `NonDensityAPI` has one parameter `c : ℝ` |
| `cd verification && lake env lean /tmp/t21alias416.lean` (alias/seam consistency) | `mainStatement := ⟨A.fixedInitialDensity, A.zeroInitialDensityIff⟩`, `nonDensityStatement := A.nonDensity`, and `d.fixedInitialDensity` against the T21 field — all typecheck (only unused-variable linter warnings from a scratch-only example) |
| `diff <(sed -n '184,255p' research/T19/Spec.lean) <copied block>` | identical — T19 copy is byte-for-byte |
| `grep -nE ': *True\|:= *0$\|→ *True' research/T21/Spec.lean` | **empty** (exit 1) |
| `grep -nE 'sorry\|admit\|\baxiom\b\|native_decide' research/T21/Spec.lean` | **empty** (exit 1) |
| `git commit` on `erenup/416-SPEC-t21-reconcile` | `70ca6e0c`; working tree clean; no push/merge/rebase |

### Failed approaches

1. **First probe without `open NavierStokes.ProblemStatement`** — `fun _ : Space ↦ 0` elaborated against a different `Space` than `SpatialField`'s domain. Both drafts open that namespace; the reconciled spec does too.
2. **Draft B's rejected approach, re-examined and reversed** — B rejected importing the canonical T20 module because `maximalLifespanT` is not `rfl`-equal across the seam. I re-measured: the failure is confined to the *conclusion*, the propositional bridge already exists in `Bindings`, and importing removes both the T20 and T12 copy blocks. The `rfl` failure alone was not a sufficient reason to copy.
3. **Copying all four T19 structures (what both drafts did)** — rejected: three of them are `:527-590` corollaries that `thm:main` never consumes, and an unread copy is drift surface. Only `PeriodicDensityAPI` is copied.
4. **Keeping draft A's `criticalRadius_pos` and split `zeroForce_mem_forceClass`/`zero_mem_criticalBall`** — rejected: the first is `ENNReal.ofReal_pos` applied to `hc`, and the second is literally the first conjunct of the third.
