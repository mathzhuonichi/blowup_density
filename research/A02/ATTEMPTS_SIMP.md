# A02 simplifier + tester pass (lane 040, SIMP-A02)

Follow-up lane over the four merged A02 modules
`Section4/A02/{SolutionClass,Restrict,Order,Energy}.lean`, per the "After ACCEPT"
section of `.claude/skills/lane-review/SKILL.md`.  No new mathematics; every
public theorem's statement is byte-identical to the merged version (verified by a
signature diff against `HEAD`, see below).

Worktree `.claude/worktrees/040-SIMP-A02-dedupe`, base `erenup/integration`.

## Line counts (before → after)

| module | before | after | note |
|---|---|---|---|
| `SolutionClass.lean` | 135 | 149 | header expanded to document the canonical-copy decision |
| `Restrict.lean` | 404 | 291 | deleted the §0 duplicate; trimmed header; dropped dead opens |
| `Order.lean` | 163 | 163 | untouched (already imports `Restrict`, no duplicate, no warnings) |
| `Energy.lean` | 258 | 163 | deleted §1–2; rewired §3 to D01 |
| **total** | **960** | **766** | −194 |

## Simplified

* **Dedupe of the restatement (task 1).**  `Restrict.lean` §0 (the byte-identical
  copy of `SolutionClass.lean`'s solution-class objects that lane 032 had left
  inline) is deleted.  `Restrict.lean` now `import`s
  `NSFormalization.Section4.A02.SolutionClass` for `SpatialField`,
  `SpaceTimeField`, `SpaceTimeScalar`, `futureTimes`, `forceTimeMeasure`,
  `IsSobolevDatum`, `IsSobolevPath`, `MemHInfty`, `IsSolenoidal`, `initialClassR`,
  `MemForceR`, `PressureGaugeEquivOn`, `ClassicalSolutionR`, `maximalLifespanR`,
  `RegularThrough` (15 declarations).  `Order.lean` still `import`s `Restrict`,
  and `Energy.lean` still `import`s `SolutionClass`, so all downstream names
  resolve to the single copy in the `A02` namespace.  Confirmed: importing
  `Order` and `Energy` together no longer collides (before this lane it did — both
  trees defined `A02.futureTimes` etc., which only never clashed because nothing
  imported both).
* **Dedupe of Energy §1–2 against D01 (task 2).**  `Energy.lean` §1
  (`cyclesComponent`, `norm_cyclesComponent_le`, `componentLp`, `sliceLp`,
  `sliceConst`, `sliceConst_nonneg`, `norm_sliceLp_le`) and §2
  (`compactRep_of_isSobolevDatum`, `componentLp_ae`, `sliceLp_ae`,
  `memLp_of_isSobolevDatum`, `l2Sq_le_of_isSobolevDatum`) re-derived at order 0
  what `Section4/D01/DatumToJets.lean` proves at general integer order.  All
  deleted; the deliverable `uniformFiniteEnergy_of_sobolevDatumPath` now calls
  D01 directly (see the dedupe map).  These helpers were used **only** inside
  `Energy.lean` and audited by `research/A02/axioms_u1a.lean`; nothing else in
  `formalization/`, `verification/` or `research/` referenced them
  (`grep` confirmed).  The registered contract already binds the canonical form:
  `verification/Bindings/DatumLemmas.lean:191` sets
  `memLp_of_isSobolevDatum := … D01.memLp_of_isSobolevDatum`, so D01 is the
  authoritative source.
* **Cleanup (task 4).**  No `set_option`/`maxHeartbeats` existed in any module.
  Removed dead `open`s from `Restrict.lean` (`NSFormalization.Paper3`,
  `NSFormalization.Source.RealSobolev (FourierData)`, `open scoped SchwartzMap` —
  none referenced once §0 was gone; rebuild confirms).  Removed the now-unused
  direct imports `Source.FourierPhysicalJets` and `Paper3.AngularTameProduct` from
  `Energy.lean` (D01.DatumToJets provides them transitively).  Added the one
  missing docstring (`ClassicalSolutionR.nonempty_restrict`).  Per-file build of
  each module reports **zero** warnings on its own lines.  No linter-flagged dead
  `have`s existed (the zero-warning build implies it).

## Not simplified, and why

* **A02's copies of `IsSobolevDatum`/`IsSobolevPath`/`MemForceR`/`futureTimes`/
  `forceTimeMeasure` were NOT replaced by importing the D01 copies (task 3).**
  They are definitionally equal to D01's — verified:

  ```
  example : A02.IsSobolevDatum   = D01.IsSobolevDatum   := rfl   -- SmoothDatum:237
  example : A02.IsSobolevPath    = D01.IsSobolevPath    := rfl   -- ForceClass:152
  example : A02.MemForceR        = D01.MemForceR        := rfl   -- ForceClass:158
  example : A02.futureTimes      = D01.futureTimes      := rfl   -- ForceClass:143
  example : A02.forceTimeMeasure = D01.forceTimeMeasure := rfl   -- ForceClass:147
  ```

  (run in a scratch file importing `A02.Energy` + `D01.{ForceClass,DatumToJets}`;
  all five `rfl`s typecheck.)  But the "preferred, if D01's are token-identical to
  `Contracts/V1/Data.lean`" branch of the task does **not** apply: D01's copies
  unfold `SpatialField`/`SpaceTimeField` to `Space → Space`/`VelocityField`,
  whereas A02's keep the abbreviations, matching `Contracts/V1/Data.lean` token for
  token.  The token-for-token agreement with the contract is exactly what the
  `Bindings` `rfl` bridges rely on, so A02's copies are the canonical ones for the
  A02 chain.  A permanent `rfl` bridge lemma was **not** added in
  `SolutionClass.lean` either: it would force `SolutionClass` (hence the otherwise
  lightweight `Restrict` and `Order`, which import only `Paper3` and
  `NavierStokes.R3.ProblemStatement`) to import `D01.SmoothDatum`/`D01.ForceClass`
  and their ~35-module analytic closure — a build-hygiene regression — while the
  defeq is already usable by `exact` from any module that imports both.  The
  decision and the five equalities are recorded in `SolutionClass.lean`'s header.
  `MemHInfty`, `IsSolenoidal`, `initialClassR`, `PressureGaugeEquivOn`,
  `maximalLifespanR`, `RegularThrough`, `SpatialField`, `SpaceTimeField`,
  `SpaceTimeScalar` have no counterpart in `D01.{SmoothDatum,ForceClass,DatumToJets}`
  at all.
* **`Energy.lean` keeps only `ContDiff ℝ ∞` slices, matching D01's stronger
  hypothesis.**  The deleted A02 helpers needed only `Continuous` of the slice;
  D01's `memLp_of_isSobolevDatum`/`eLpNorm_le_of_isSobolevDatum` need
  `ContDiff ℝ ∞`.  This is a genuinely stronger hypothesis, but the deliverables
  supply it: `ClassicalSolutionR.velocity_smooth` gives it through
  `D01.contDiff_slice`, and the `Continuous`-only generality was used nowhere, so
  no A02-local order-0 lemma was kept for it.
* **`Order.lean` was left untouched.**  It already imports `Restrict` (for
  `ClassicalSolutionR.restrict`/`nonempty_restrict`), carries no duplicate, has all
  docstrings, and builds with zero warnings.

## Dedupe map (old A02 name → canonical name)

Restatement (task 1): the 15 §0 objects `Restrict.lean` used to declare are now
the single copies in `NSFormalization.Section4.A02.SolutionClass` (same
namespace, same names) — `A02.Restrict.<name>` → `A02.SolutionClass.<name>` for
`SpatialField, SpaceTimeField, SpaceTimeScalar, futureTimes, forceTimeMeasure,
IsSobolevDatum, IsSobolevPath, MemHInfty, IsSolenoidal, initialClassR, MemForceR,
PressureGaugeEquivOn, ClassicalSolutionR, maximalLifespanR, RegularThrough`.

Energy dedupe against D01 (task 2):

| deleted `A02.*` (Energy §1–2) | canonical `D01.*` (DatumToJets) |
|---|---|
| `cyclesComponent` | `cyclesComponentOfAngular` (`:140`) |
| `norm_cyclesComponent_le` | `norm_cyclesComponentOfAngular_le` (`:153`) |
| `compactRep_of_isSobolevDatum` | `compactRep_cyclesComponentOfAngular` (`:161`) |
| `componentLp` / `sliceLp` / `componentLp_ae` / `sliceLp_ae` | `jetOfDatum` / `jetOfDatum_ae` (`:196,202`) at `j = 0` |
| `sliceConst` / `norm_sliceLp_le` | `jetDatumConst 0 0` / `norm_jetOfDatum_le` (`:218,224`) |
| `memLp_of_isSobolevDatum` | `memLp_of_isSobolevDatum` (`:267`) |
| `l2Sq_le_of_isSobolevDatum` | `eLpNorm_le_of_isSobolevDatum` (`:276`) + `LpNormTools.lpNorm_two_sq_eq_l2Sq` |
| (slice continuity) | `contDiff_slice` (`:366`) |

The three A02 deliverable theorems `uniformFiniteEnergy_of_sobolevDatumPath`,
`uniformFiniteEnergy_of_sobolev`, `ClassicalSolutionR.uniformFiniteEnergy` keep
their exact statements.  The `((0 : ℕ) : ℝ)`-vs-`(0 : ℝ)` cast (which is **not**
`rfl` — verified) is handled inside `uniformFiniteEnergy_of_sobolevDatumPath` by
`have hs0 : s = ((0 : ℕ) : ℝ) := by rw [hs, Nat.cast_zero]; subst hs0`, after which
D01's lemmas apply at `m = 0` with no transport (the A02↔D01 `IsSobolevDatum`
defeq moves the datum across on `exact`).

`research/A02/axioms_u1a.lean` was updated (allowed edit): the three `#print
axioms` lines for the deleted helpers were removed; the three deliverable
theorems remain audited and print `propext, Classical.choice, Quot.sound`.

## Negative-check results (task 6; edits NOT committed — done in scratch files)

* **`ClassicalSolutionR.uniformFiniteEnergy`, hypothesis `hbT : b < T` removed.**
  Dropping the `hbT` argument from the proof term
  `uniformFiniteEnergy_of_sobolev u.velocity_smooth u.sobolev hb0 hbT` gives:
  ```
  error: Type mismatch
    uniformFiniteEnergy_of_sobolev u.velocity_smooth u.sobolev hb0
  has type   b < T → UniformFiniteEnergy (Icc 0 b) u.velocity
  but is expected to have type   UniformFiniteEnergy (Icc 0 b) u.velocity
  ```
  → `b < T` is load-bearing (the uniform energy bound needs the compact `Icc 0 b`
  strictly inside the open slab `Ico 0 T`).
* **`exists_pressure_normalization`, the normalization field-use removed.**
  Replacing the witness `w.normalizePressure x₀` by the un-normalized `w`
  (`⟨w, rfl, fun _ => rfl⟩`) gives:
  ```
  error: Type mismatch  rfl  has type  ?m = ?m
  but is expected to have type
    w.pressure x✝ = w.pressure x✝ - w.pressure (x✝.1, x₀)
  ```
  → the basepoint subtraction of `ClassicalSolutionR.normalizePressure` is
  load-bearing; the identity witness cannot satisfy the pressure conjunct.

## CI reachability (task 7)

`python3 experiments/build_changed_lean.py --base-ref origin/main` prints all four
modules in its "Changed Lean modules" list:
`NSFormalization.Section4.A02.{Energy, Order, Restrict, SolutionClass}`.  So CI's
changed-module step rebuilds them.  (The script's trailing `FileNotFoundError:
'lake'` is only because `lake` was not on `PATH` in the bare `python3`
subprocess; module detection — the reachability question — completed and listed
the four.)

No A02 module is imported by any `verification/{Bindings,Tests,Contracts}` module
yet, so the four are **not** in a registered-contract Tests closure — CI runs them
only through the `build_changed_lean.py` step above.  That satisfies the tester
requirement ("a registered contract's test, *or* listed by
`build_changed_lean.py`"); they should be folded into the Tests closure when the
A02 contract is registered.

## Commands run (all `lake` from `WT/verification`, one at a time)

| command | result |
|---|---|
| `bash scripts/lean-install.sh` | `== OK`; `lake test` all contracts "checked; standard logical axioms only" |
| `lake build …A02.Energy` (after rewire) | `✔ Built …A02.SolutionClass`, `✔ Built …A02.Energy`; no A02 own-line warning |
| `lake build …A02.{Restrict,Order}` | `✔ Built` both; no A02 own-line warning |
| `lake env lean …/A02/{SolutionClass,Restrict,Order,Energy}.lean` | each: no own-line warning/error |
| `lake env lean ../research/A02/axioms_u1a.lean` | 3 deliverables, all `[propext, Classical.choice, Quot.sound]` |
| `lake env lean ../research/A02/AxiomsU4U6.lean` | no errors (all 9 `example`s typecheck); all 25 `#print axioms` standard |
| signature diff vs `HEAD` (python) | all three Energy signatures + all Restrict §1–3 statements byte-identical |
| negative checks A, B (scratch) | both fail with the expected type mismatch |
