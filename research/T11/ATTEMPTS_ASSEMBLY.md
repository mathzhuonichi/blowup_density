# T11 / U17 (lane 340) — attempts, dead ends and the exact obstacles

Positive and negative record for the assembly + contract lane.  Companion to
`REPORT_340.md`.

## 1. The horizon/solution selection had to be redone, not reused

`Section3/T11/Restart.lean` already builds the first three
`PeriodicLocalTheoryAPI` fields (`periodicLocalHorizonOfInput`,
`periodicLocalSolutionOfInput`, `periodicLocalRegularityOfInput`,
`periodicLocalTheoryAPI_of_input`), but every one of them is parametrized by
`H : PeriodicQuantitativeLocalInput'` — the **`H¹`** input of amendment 1, which
is open (`H1_GAP.md` G1).  Lane 338 proves
`PeriodicQuantitativeLocalInputH3`, a *different* `Prop`, so
`periodicLocalTheoryAPI_of_input periodicQuantitativeLocalInputH3` does not
typecheck: the two predicates differ in the Sobolev order of the datum ball and
neither implies the other definitionally.

**What worked.**  Redo the `Classical.choice` selection in `Assembly.lean` from
lane 338's unconditional `exists_periodicLocalSolution_unconditional`.  It is
*shorter* than `Restart.lean`'s, because lane 339's
`ClassicalRegularity.regularity_of_solution` makes `regularity` automatic for an
arbitrary selected family: the `Σ δ, {w // PeriodicLocalRegularity …}` bundle of
`Restart.lean` (needed there to keep the witness attached to its regularity
proof across the dependent `rw`) collapses to `Σ δ, ClassicalSolutionT ν a f δ`.

**Negative note.**  A first attempt tried to keep the bundle shape; it works but
carries an extra `Subtype` projection through every use for no benefit.

## 2. Namespace collision inside `NSFormalization.Section3.T11`

`periodicLocalChoice` is already declared in `Restart.lean` in the same
namespace; the new selection had to be named `periodicLocalChoiceU`.  (Same
family as the `logs/LESSONS.md` 2026-09-17 entry about anonymous instances
colliding across modules of one namespace — here the name was explicit, so the
error was immediate and cheap.)

## 3. The structure exception cost more than `ClassicalSolutionT` itself

`toContract` / `ofContract` are plain field transport and both round trips are
`rfl`, as expected: every field type of the contract copy is definitionally
equal to the canonical one (including `sobolev`, whose `PeriodicSobolev`
carrier is bridged by `Bindings.TorusData.periodicSobolev_eq`, and
`pressure_gradient`, whose `MemLp … periodicTorusMeasure` needs the contract's
`local instance` torus measure to be defeq to `Paper1.periodicTorusMeasure`).

What is *not* free is everything that mentions the structure.  Seven
declarations could not get an `rfl` bridge and needed proved equalities:

| declaration | bridge |
|---|---|
| `maximalLifespanT` | `iSup_congr` + `iSup_congr_Prop` on `Nonempty (ClassicalSolutionT …)` |
| `RegularThroughT` | `propext` through the same `Nonempty` iff |
| `breakdownSetInT`, `breakdownSetT` | `ext` + `maximalLifespanT_eq` |
| `SolvesBelowT`, `IsMaximalPeriodicSolution`, `ExtendsBeyondT` | `propext`, rebuilding the existential witness through the conversions |
| `PeriodicLocalRegularity` | `propext` fieldwise: the record depends on the solution only through `velocity`/`pressure`, which the conversion preserves by `rfl` |

`iSup_congr_Prop` is the piece worth remembering: `⨆ _ : Nonempty A, x` cannot be
rewritten by `simp` from an `Iff` on the index proposition, and
`iSup_congr (fun S ↦ iSup_congr_Prop h (fun _ ↦ rfl))` closes it in one line.

## 4. Deprecations and small traps at `v4.34.0-rc2`

* `Set.mem_setOf_eq` is deprecated (`Set.mem_ofPred_eq`).  The `breakdownSetInT`
  bridge avoids both by destructuring the membership with `rintro ⟨hY, hle⟩`.
* The contract does **not** import `Contracts.V2.*`: the two literal
  cross-spelling checks of `research/T11/Spec.lean:513-522`
  (`convectionDivergenceT = V2.LocalTheory.convectionDivergence`,
  `timeShiftT = V2.Continuation.timeShift`) were moved into the binding, where
  importing V2 is unremarkable.  Keeping them in a V1 contract would make V1
  depend on V2.

## 5. `Tests/` importing HeliCorgi's `Formal.*` is **not** a problem

`Tests.TorusLocalTheory` transitively imports
`Formal.EndpointSafeTwoSpacePicard` (through
`Section3/T11/Assembly → MildClassical → Restart → LocalExistence →
LocalExistenceProbe`).  `CLAUDE.md` warns that the `Tests` library is
`warningAsError = true` and that the 52 vendored warnings would become errors.
They do not: Lake's `leanOptions` apply to the modules **of that library only**,
and imported `.olean`s are replayed, not re-elaborated.  `lake build
Tests.TorusLocalTheory` is green and the vendored warnings appear as warnings on
the `Formal` library's own replay lines.  The rule to keep is the narrower one:
a `Tests` module must not *use* a deprecated or warning-triggering declaration
itself.

## 6. What was deliberately not attempted

The `H¹` ball.  `H1_GAP.md` §2 shows the route is missing at the level of the
bilinear estimate (`H^r × H^r →L H^{r-1}` only for `r ≥ 3`), not at the level of
bookkeeping, so no amount of assembly work closes it.  Both manuscript
sentences are registered as named unproved predicates and
`periodicContinuationAPI_of_h1` machine-checks that they are the *only* residue:
the other three fields of `PeriodicContinuationAPI` are supplied
unconditionally.
