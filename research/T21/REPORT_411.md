# REPORT 411 — lane `411-SPEC-t21-draft-b` (T21 double-blind draft B)

## 1. What was proved

Nothing was proved: this is a **specification** lane.  What was produced is the
blind draft B of the Lean *statements* of the two top-level results of
Section 3 of `paper/sections/03-torus.tex`:

* `cor:nondensity` (`:506-509`, proof `:510-520`) — non-density of `𝓑⁰_{ν,T}`
  in `𝓕` at and above the critical order, through the explicit open ball
  `{g ∈ 𝓕 : ‖g‖_{L¹_tH^s_x} < cν}` of the `prop:critical` constant;
* `thm:main` (`:6-16`, proof `:522-524`) — the Sobolev density threshold,
  clause (i) for every fixed `a ∈ 𝓧` and clause (ii) as a biconditional at the
  zero initial velocity.

The file contains no `sorry`, no `axiom`, no `native_decide`, and no
placeholder/`True` field.  The only `:= rfl` terms are seven deliberate
definitional drift checks.

## 2. What exists in Lean now

`/data_8T/ping/blowup_density/.claude/worktrees/411-SPEC-t21-draft-b/research/T21/DraftB.lean`
(1406 lines) elaborates with 0 errors.  Its own T21 declarations, in namespace
`BlowupDensity.T21.DraftB`:

* `def breakdownSetTZero (ν T : ℝ)` — `𝓑⁰_{ν,T} = 𝓑_{ν,0,T}`
  (`02-preliminaries.tex:41`); no torus zero-datum set is registered yet, and
  `Contracts/V1/Data.lean`'s own docstring says `𝓑⁰` is the torus symbol.
* `def criticalBallT (c ν s : ℝ)` — the ball of `03-torus.tex:513` and `:519`,
  relative to `forceClassT`, radius `ENNReal.ofReal (c * ν)`.
* `structure NonDensityAPI (c : ℝ) : Prop` — 10 fields, one paper clause each:
  `hc`, `criticalGlobalRegularity`, `zeroMemBall`, `ballRelativelyOpen`,
  `reweightContraction`, `sliceSobolevMonotone`, `forceSobolevMonotone`,
  `criticalBallDisjoint`, `ballDisjoint`, `nonDensity`.
* `structure MainTheoremAPI : Prop` — 5 fields: `thresholdValue`,
  `zeroInitialClass`, `fixedInitialDensity` (i), `zeroInitialDensityIff` (ii),
  `zeroInitialNonDensity`.
* `def nonDensityStatement`, `def mainStatement` — the two results in the
  paper's quantifier order.
* `def nonDensityOfCritical : ∀ K : CriticalRegularityTAPI, NonDensityAPI K.c`,
  `def mainOfDensityAndNonDensity`, `def mainOfInputs : PeriodicDensityAPI →
  CriticalRegularityTAPI → MainTheoremAPI` — the assembly signatures, no
  inhabitant constructed.

Vocabulary: registered contracts (`TorusData`, `TorusLocalTheory`, `Data`,
`MainThresholds`, `CompletedDensity`, `Packet`, `PacketImport`,
`MaximalPartial`, `Correction`, `GradientL6`) are imported and used by name.
Three delimited verbatim copy blocks carry the unregistered vocabulary:
`BlowupDensity.T15.Draft` + `BlowupDensity.T19` (the four T19 structures, from
`research/T19/Spec.lean:91-529`), `BlowupDensity.T12.Draft` (from
`research/T20/Spec.lean:611-699`) and `BlowupDensity.T20.Spec` (the
`CriticalRegularityTAPI`, from `research/T20/Spec.lean:894-1245`, textually the
canonical `NSFormalization.Section3.T20.CriticalRegularityTAPI`).  The single
edit to the copies is documented in the module docstring: the two
`open BlowupDensity.T1{0,1}.Draft` lines become
`open BlowupDensity.Contracts.V1.TorusLocalTheory`, so the copied text is
unchanged but resolves against the **registered** contract, as
`research/T19/Spec.lean` already does.

`/data_8T/ping/blowup_density/.claude/worktrees/411-SPEC-t21-draft-b/research/T21/COMPARISON_B.md`
(245 lines): the paper-clause → Lean-field table for both results with the
Section 4 `R41` counterpart (or "torus-only") per row, the design choices, seven
ambiguities for the reconciliation, the "needs a lemma" list, the exact spelling
of `L¹_tH^s` in `TorusLocalTheory`, and the implementation-candidate tables for
`Section4/R41/*` and `Paper1/*`.

## 3. Gap

* No proof of any field exists.  `nonDensityOfCritical`, `mainOfInputs` and
  `mainOfDensityAndNonDensity` are arrow types with no inhabitant.
* T19's `PeriodicDensityAPI` and T20's `CriticalRegularityTAPI` are both
  **unregistered**; `thm:main` cannot be registered as a `Contracts/V1` file
  until they are, because a registered contract may import only `Contracts.*`.
  Today the draft reaches them by verbatim copy.
* Eight lemmas the proof lane must supply are listed in `COMPARISON_B.md` §5.
  The two structural ones: a coefficient-side order-lowering **continuous
  linear map** `PeriodicSobolev t →L[ℝ] PeriodicSobolev s` (the torus analogue
  of `R41.lowerVectorL`), needed for `forceSobolevMonotone`; and the triangle
  inequality for `forceSobolevENormT 1 s`, needed for `ballRelativelyOpen`.
* `Paper1/PeriodicCriticalRegularity.lean` and `Paper1/PeriodicMain.lean`
  already contain the whole argument on the torus (`critical_regular_ball`,
  `paper1_main_with_critical_interfaces`, `forceDistance_order_mono`,
  `periodicVectorSobolevNorm_mono`) but in the weaker `TestForce` /
  `forceDistance` / `lifespan` vocabulary.  The gap to the draft is a binding
  layer, not new mathematics.
* Measured, not assumed: the registered and canonical spellings of
  `forceSobolevENormT` and `forceClassT` are definitionally equal, but
  `maximalLifespanT` is **not** (different `ClassicalSolutionT` inductives,
  the `CLAUDE.md` structure exception).  So `criticalRho` and the ball
  vocabulary transfer by `rfl`, while `globalRegularity` must go through
  `Bindings.TorusLocalTheory`.
* Two clauses are deliberately not fields, with reasons in `COMPARISON_B.md`:
  the "a dense subset cannot miss a nonempty open set" step (`:519`) would be
  `RelativelyDenseT` unfolded, i.e. a tautology; and the scope remark `:525`
  states what is *not* proved.
* Open owner question, inherited from T19: `MainTheoremAPI`/`NonDensityAPI` are
  `Prop`-valued (no data), which diverges from the `Type`-valued registry
  convention of `MainThresholdsAPI`/`CompletedDensityAPI`.

## 4. Commands run and results

Environment sourced with `. scripts/lean-env.sh` in every shell; `lake` run
from `verification/`.

| command | result |
|---|---|
| `lake env lean /tmp/t21probe.lean` (contract imports only) | 0 errors, 2.3 s — the registered contracts are prebuilt in this worktree |
| `lake build NSFormalization.Section3.T20.CriticalRegularity` | `Build completed successfully (10591 jobs)` |
| `lake env lean /tmp/t21drift.lean` | 2 of 3 `rfl` drift checks accepted; `maximalLifespanT` rejected with "Type mismatch … `rfl`" — recorded in `COMPARISON_B.md` §6 |
| `lake env lean ../research/T21/DraftB.lean` (copy blocks only, before the T21 section) | 0 errors |
| `lake env lean ../research/T21/DraftB.lean` (first full version) | 3 errors: `Unknown identifier BlowupDensity.Contracts.V1.GradientL6.{lift,gradientTensor,laplacian}` |
| `lake env lean ../research/T21/DraftB.lean` (after fixing the namespace to `BlowupDensity.Contracts.V1`) | **0 errors, exit 0** |
| `lake env lean /tmp/t21/check.lean` (`#print` of the four statement defs) | all four elaborate to the intended quantifier orders |
| `lake env lean /tmp/t21/check2.lean` (`#print` of both structures) | 10 + 5 fields, all as intended; `NonDensityAPI` has one parameter `c : ℝ` |
| `grep -nE ': *True\|:= *0$\|→ *True' research/T21/DraftB.lean` | **empty** |
| `grep -nE 'sorry\|admit\|\baxiom\b\|native_decide' research/T21/DraftB.lean` | **empty** |

### Failed approaches and why

1. **Importing `NSFormalization.Section3.T20.CriticalRegularity` into
   `DraftB.lean` and using `CriticalRegularityTAPI` by name instead of copying
   it.**  Rejected after measuring: the canonical structure speaks the
   canonical `maximalLifespanT`, which is *not* definitionally the registered
   one (probe above), so the draft would have mixed two lifespans in one file.
   It would also make the deliverable depend on a 10591-job build rather than
   on the prebuilt contracts.  Copying the reconciled text and re-basing its
   two `open` lines onto the registered contract gives the same content with a
   single vocabulary.
2. **Drift checks against `BlowupDensity.Contracts.V1.GradientL6.lift` etc.**
   Failed with "Unknown identifier": `Contracts/V1/GradientL6.lean` declares
   into namespace `BlowupDensity.Contracts.V1`, not `…V1.GradientL6`.  Fixed by
   using the real namespace; the three `rfl` checks then pass.
3. **A field rendering "a dense subset cannot miss a nonempty open set" as a
   general lemma over `RelativelyDenseT`.**  Written, then removed: it unfolds
   to the definition of `RelativelyDenseT` and would have been a tautology,
   which the brief forbids.
4. **Copying `BlowupDensity.T10.Draft` / `T11.Draft` alongside the T20 block**
   (the shape `research/T20/Spec.lean` itself uses).  Rejected: `CLAUDE.md`
   allows only one local restatement of `ClassicalSolutionT`, and T19's
   already-reconciled spec uses the registered `Contracts.V1.TorusLocalTheory`
   names, so a second restatement here would have put two incompatible
   `ClassicalSolutionT`s in one file.
