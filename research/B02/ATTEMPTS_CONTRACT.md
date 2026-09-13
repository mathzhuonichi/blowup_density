# B02 contract registration (lane 099) — transcription notes

Registers the 16 proved fields of `research/B02/Spec.lean`'s `HomogeneousApproxAPI`
as the versioned partial contract `B02.homogeneous_partial`
(`verification/Contracts/V1/HomogeneousPartial.lean` +
`Bindings/HomogeneousPartial.lean` + `Tests/HomogeneousPartial.lean`), modelled
field-for-field on `B01.bochner_partial` (lane 071) and
`C01.energy_absorption_partial` (lane 091).

## Field → discharging theorem (all in `NSFormalization.Section4.B02`)

| # | contract field | Spec:line | theorem (module) |
|---|---|---|---|
| 1 | `chi_smooth` | 280 | `chi_smooth` (Remaining) |
| 2 | `chi_one` | 282 | `chi_one` (Remaining) |
| 3 | `chi_vanishes` | 285 | `chi_vanishes` (Remaining) |
| 4 | `chi_range` | 287 | `chi_range` (Remaining) |
| 5 | `annularRestriction` | 302 | `annularRestriction` (Annular) |
| 6 | `annularSmoothing` | 314 | `annularSmoothing` (Annular) |
| 7 | `annularSchwartz` | 362 | `annularSchwartz` (AnnularReal) |
| 8 | `lowFrequencyIntegrable` | 370 | `lowFrequencyIntegrable` (LowFrequency) |
| 9 | `lowFrequencyIntegral` | 378 | `lowFrequencyIntegral` (LowFrequency) |
| 10 | `fourierSupBound` | 397 | `fourierSupBound` (LowFrequency) |
| 11 | `lowHighSplit` | 421 | `lowHighSplit` (LowHigh) |
| 12 | `lebesgueHomogeneousDatum` | 454 | `lebesgueHomogeneousDatum` (LebesgueDatum) |
| 13 | `homogeneousDatumSub` | 490 | `isHomogeneousSliceDatum_sub_of_integrable` (LebesgueDatum) |
| 14 | `cutoffLebesgue` | 513 | `cutoffLebesgue` (Cutoff) |
| 15 | `spatialApproxHomogeneous` | 539 | `spatialApproxHomogeneous` (AnnularReal) |
| 16 | `temporalApprox` | 563 | `temporalApprox` (Remaining, `= Section4.B01.temporalApprox`) |

Plus the single data field `χ := NavierStokesR3.ComparisonCutoffs.baseCutoff` (the
same vendor cutoff `B01.bochner_partial` binds, `Bindings/BochnerPartial.lean:66`).

## Reuse decisions (not restated in the contract)

* From `Contracts/V1/Data`: `SpatialField`, `IsHomogeneousSliceDatum`,
  `IsHomogeneousPath`, `homogeneousFourierENorm`, `MemBochnerDatum`,
  `bochnerDatumENorm`, `MemForceCompact`, `forceClassCompact`, `forceTimeMeasure`.
* From `Contracts/V1/BochnerPartial`: `separatedPath`, used by `temporalApprox`
  (the datum path shared verbatim with `B01`; the task card and `Spec.lean`'s
  "Relation to B01" both direct reuse over a second copy). The contract therefore
  imports `Contracts.V1.BochnerPartial` in addition to `Contracts.V1.Data`; both
  are `Contracts.*` imports, so `check_contracts.py`'s import policy is satisfied.
* Upstream vocabulary reached by `open` (available transitively through
  `Data`, and each module is on `CONTRACT_CANONICAL_MODULES`): `Space`
  (`NavierStokes.ProblemStatement`), `RealVectorSobolev` (`NSFormalization.Paper3`),
  `angularFourier` (`NSFormalization.Source`), `FourierData`
  (`NSFormalization.Source.RealSobolev`). Same pattern as `BochnerPartial`'s
  `open NavierStokes.ProblemStatement (Space)` etc.

## Restated in the contract (nine spec-local defs), each rfl-bridged in the binding

`frequencyAnnulus`, `closedFrequencyAnnulus`, `IsAnnularDatum`,
`IsAnnularRestriction`, `IsAnnularSupported`, `scaledCutoff`, `schwartzVector`,
`lowHighConstant`, `SplitRange` — copied token-for-token from `Spec.lean:155-237`,
each paired with `homogeneousPartial_<name>_eq : <contract> = NSFormalization.Section4.B02.<name> := rfl`.
The Annular predicates rfl-bridge even though they call the contract-local
`frequencyAnnulus`/`closedFrequencyAnnulus`, because those are defeq to the B02
module's identically-bodied defs, so `rfl` unfolds through them.

## Mismatches / observations between Spec, modules, and the contract

1. `schwartzVector` return type. `Spec.lean:206` writes `: SpatialField`; the
   module `Cutoff.lean:57` writes `: Space → Space`. `SpatialField = Space → Space`
   (`Data.lean:99`), so they are defeq and the rfl bridge holds. The contract keeps
   `SpatialField` (the Spec spelling).
2. Hypothesis shape. `lowHighSplit` and `lebesgueHomogeneousDatum` take the two
   raw hypotheses `hs : -3/2 < s`, `hs0 : s ≤ 0`, while the contract field (like
   the spec) takes the packed `SplitRange s`. The binding supplies `hs.1`/`hs.2`,
   exactly as the conformance files `axioms_u7.lean:42`, `axioms_u6.lean:34` do.
   `lebesgueHomogeneousDatum` has `s` implicit, so its binder is `_s` (the theorem
   infers `s` from `k`); `lowHighSplit` has `s` explicit and passes it.
3. `homogeneousDatumSub` is registered ONLY as `isHomogeneousSliceDatum_sub_of_integrable`
   (implicit `{s} {z w} {Z W}`, four explicit hypotheses). Its hypothesis-free
   ancestor is FALSE (`REVIEW_U6.md` §4); the ⚠ counterexample note is copied into
   the contract field docstring verbatim, per the reviewer's first hard requirement.
4. `temporalApprox` (`= B01.temporalApprox`) concludes in `B01.separatedPath`, and
   the contract field uses `BochnerPartial.separatedPath`; these are defeq
   (`bochnerPartial_separatedPath_eq : … = B01.separatedPath := rfl`, already in the
   B01 binding), so direct assignment typechecks with no re-bridge needed here.

## Excluded fields (the reviewer's second hard requirement: named in the module docstring)

Three obligations of `HomogeneousApproxAPI` are deliberately absent (the `M` rows of
`REMAINING_SPLIT.md`, none proved on this branch), and are listed with their reasons
in the contract module docstring's "Out of scope" section:
`separatedAssembly` (:582, no smul/sum additivity combinator for
`IsHomogeneousSliceDatum`), `annularPathApprox` (:337, not a manuscript step, feeds
nothing, needs measurable-in-t selection + path DCT), `approxCompactHomogeneous`
(:607, depends on `separatedAssembly`; `B01`'s `approxCompact` is monolithic with no
homogeneous source theorem to reuse). Also absent, assigned to `B01`:
`forceClassCompact ⊆ forceClassR` and the completion identification.

## Failed / adjusted approaches

* Only adjustment during the build: the initial `lebesgueHomogeneousDatum := fun s hs k hk1 hk2 => …`
  raised the `unusedVariables` linter ("Variable name `s` is not explicitly
  referenced", because the theorem's `s` is implicit and inferred). Renamed the
  binder to `_s`; clean build afterwards. No other approach was tried and failed —
  the contract, binding and test compiled on first attempt.
* No eta-wrapping was needed for `spatialApproxHomogeneous`, `cutoffLebesgue`,
  `annularRestriction/Smoothing/Schwartz` or `temporalApprox` despite `SplitRange`,
  `scaledCutoff`/`schwartzVector` and `separatedPath` being restated/reused: the
  defeq to the modules' objects is transparent, so direct field assignment worked.

## Commands (from the worktree, `. scripts/lean-env.sh; export LEAN_NUM_THREADS=6`)

* `cd verification && lake build Tests.HomogeneousPartial` → `Build completed
  successfully (9898 jobs).`; `Tests/HomogeneousPartial.lean:15:0: Contract
  BlowupDensity.Tests.checkedHomogeneousPartial: checked; standard logical axioms only`.
* `make check` → passed (13/13 policy tests, 30 work items consistent).
* `make test` → every registered contract "checked; standard logical axioms only".
* `make test-mutations` → `extra_axiom: rejected as required`,
  `weakened_hypothesis: rejected as required`, `Mutation suite passed.`
* `python3 experiments/check_contracts.py --base-ref origin/erenup/integration` →
  `registered_contracts: 18`, `base_compatibility_checked: true`.
* `bash scripts/gates.sh Tests.HomogeneousPartial` → `== gates OK`.

## Post-review revisions (lane 099, review verdict ACCEPT-WITH-NOTES, `REVIEW_CONTRACT.md`)

The reviewer accepted all 16 fields as token-identical; two prose-only fixes were
requested before the `Contracts/V1` freeze (no Lean statement changed):

* **F2** (`lebesgueHomogeneousDatum` docstring + `contracts.json` scope): the prose
  said "smooth compactly supported field", but the Lean hypothesis is
  `MemLp k 1 ∧ MemLp k 2` (`L¹ ∩ L²`) with `SplitRange s`. Restored the Spec's
  clarifier ("hypothesis `L¹ ∩ L²` rather than compact support, for the reason
  recorded in `lowHighSplit` — the field applied at `04-whole-space.tex:249`,
  `(1−χ_R)h_n`, is Schwartz with unbounded support") to the field docstring, and
  changed "a smooth compact field" to "an `L¹ ∩ L²` field" in the scope. The
  statement was already correct and token-identical to the Spec; only the isolated
  reader could be misled.
* **F1** (`homogeneousDatumSub` docstring + `contracts.json` scope): recorded that in
  its integrability-carrying form this field is the **same proposition** as the
  already-registered `D01.datum_lemmas` field `isHomogeneousSliceDatum_sub`
  (`Contracts/V1/DatumLemmas.lean:458` — same four hypotheses, conclusion and binder
  order; `Section4/B02/isHomogeneousSliceDatum_sub_of_integrable` is a one-line
  re-export of the same `Section4/D01/HomogeneousWitness.lean` lemma). It is kept in
  `B02` because `Spec.lean:490` and `REVIEW_REMAINING.md` §5's first hard requirement
  list it as a `B02` obligation, so a `B02` consumer need not also depend on
  `D01.datum_lemmas` — not as a new result.

Re-run after the edits (worktree, `. scripts/lean-env.sh; export LEAN_NUM_THREADS=6`):

* `cd verification && lake build Tests.HomogeneousPartial` → `Build completed
  successfully (9898 jobs).`; `checked; standard logical axioms only`.
* `make check` → passed; `make test` → all 18 contracts `checked; standard logical
  axioms only`.
* `python3 experiments/check_contracts.py --base-ref origin/erenup/integration` →
  `registered_contracts: 18`, `base_compatibility_checked: true`.
