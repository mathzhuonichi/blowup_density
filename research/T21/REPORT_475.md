# Lane 475 report — T21 unit A assembly and registration

## 1. What was registered, with exact statements

`T03.non_density` V1 registers the nine-field `NonDensityAPI (c : ℝ)` and the
paper statement `cor:nondensity` (`03-torus.tex:506-520`):

```lean
def nonDensityStatement : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ s : ℝ, 1 / 2 ≤ s → ∀ T : ℝ, 0 < T →
    ¬ RelativelyDenseT 1 s forceClassT (breakdownSetTZero ν T)
```

It also registers the exact critical-input arrow
`∀ K : CriticalRegularityTAPI, NonDensityAPI K.c`.  The closed record is at
the explicit canonical value `c = criticalSmallnessH1`; the
witness-independent result is only `∃ c, Nonempty (NonDensityAPI c)`.

`T03.main` V1 registers the five-field `MainTheoremAPI` and `thm:main`
(`03-torus.tex:6-16`, proof `:522-524`):

```lean
def mainStatement : Prop :=
  (∀ a : SpatialField, a ∈ initialClassT →
      ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
        ∀ s : ℝ, s < 1 / 2 →
          RelativelyDenseT 1 s forceClassT (breakdownSetT ν a T)) ∧
    (∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T → ∀ s : ℝ,
      RelativelyDenseT 1 s forceClassT (breakdownSetTZero ν T) ↔ s < 1 / 2)
```

The two assembly arrows are
`∀ c, PeriodicDensityAPI → NonDensityAPI c → MainTheoremAPI` and
`PeriodicDensityAPI → CriticalRegularityTAPI → MainTheoremAPI`.  Thus the
registered gate is exactly T19 density plus T20 critical regularity through
T21 non-density.

## 2. Files and Lean contents

- `formalization/NSFormalization/Section3/T21/MainAssembly.lean` closes all
  three arrows, both records, the existential record witness, and both
  unconditional paper statements.  `Main.lean` now imports the lane-472
  `Zero.lean` theorem instead of redeclaring `zeroInitialClass`.
- `verification/Contracts/V1/TorusNonDensity.lean` and `TorusMain.lean` contain
  the verbatim reconciled record/statement shapes over registered vocabulary.
  Their `Bindings/` modules supply the canonical proofs and the approved
  breakdown-set/lifespan transport.  Their `Tests/` modules expose
  `checkedTorusNonDensity` and `checkedTorusMain`.
- `research/T21/probes/assembly_closes.lean` reads the two advertised fields
  at concrete data.  `research/T21/axioms_a.lean` audits every new layer, and
  `ATTEMPTS_A.md` records the parallel-lane dedupe and adapter.
- `verification/contracts.json` adds exactly `T03.non_density` and `T03.main`;
  the T21 work item and generated task cards list both registrations.

## 3. Gaps and exclusions

There is no proof, binding, registration, non-vacuity, or axiom gap in unit A.
The contract deliberately asserts only the torus `q = 1` threshold.  It does
not add a `q = 2` branch, a regular-reference rider, a converse for nonzero
initial data, or a proposition claiming the unclassified behavior mentioned
at `03-torus.tex:525`.

The only naming accommodation is forced by the landed lane-474 helper:
`mainOfDensityAndNonDensity_holds` already names the field-level theorem, so
the canonical arrow wrapper is
`mainOfDensityAndNonDensity_arrow_holds`.  Its proof is exactly the
lead-requested adapter.  The registered arrow theorem has the unsuffixed
requested name.

## 4. Commands and results

- The pre-edit closure build of `NSFormalization.Section3.T21.Main` and all
  lane-472 modules passed (10,733 jobs).
- `LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T21.MainAssembly
  Contracts.V1.TorusNonDensity Contracts.V1.TorusMain
  Bindings.TorusNonDensity Bindings.TorusMain Tests.TorusNonDensity
  Tests.TorusMain` passed (10,780 jobs).
- `lake env lean` on `research/T21/probes/assembly_closes.lean` passed.
  `lake env lean` on `research/T21/axioms_a.lean` passed; every printed line is
  exactly `[propext, Classical.choice, Quot.sound]`.
- `make check` passed with 54 registered contracts and a consistent work
  queue.  `make test` passed; both new `checked...` declarations reported
  standard logical axioms only.  `make test-mutations` passed all four
  mutations.
- `python3 experiments/check_contracts.py --base-ref
  origin/erenup/integration-section3` passed with `registered_contracts: 54`
  (base: 52) and `base_compatibility_checked: true`.
- `python3 experiments/tasks.py render`, the forbidden-token scan, and
  `git diff --check` passed.
