# T11 U10/U11 restart attempts (lane 321)

## Successful route

1. `Section3/T10/ForcePaths.lean` is present.  Its
   `forceSobolevENormT_ne_top` supplies the finite order-wise family
   `M m := forceSobolevENormT 1 (m : ℝ) f`.
2. The Section 4 proof
   `A04.forceSobolevENormL1_timeShift_le` was transported to the canonical
   periodic datum carrier.  For every admissible path `G`, the translated path
   `Gshift t := G (t + t₀)` still represents `timeShiftT t₀ f`; translation of
   the restricted half-line measure gives the `L¹` inequality.
3. Applying the one named input to this family gives `restart` with `δ`
   chosen before `t₀` and `a'`.
4. At `S=t₀=0`, the datum bound is its own finite H¹ norm and
   `timeShiftT 0 f = f`.  The selected solution and its regularity proof are
   kept in one dependent pair before being transported to the public horizon;
   this avoids separating dependent witnesses during equality transport.

## Exact failed elaborations

The first direct zero-shift conversion tried to construct the target
existential before rewriting its dependent solution type:

```text
Restart.lean:110:45: error: Application type mismatch: The argument
  w
has type
  ClassicalSolutionT ν a (timeShiftT 0 f) δ
but is expected to have type
  ClassicalSolutionT ν a f δ
in the application
  Exists.intro w
```

It was fixed by first packaging the shifted existential and then rewriting the
whole package with `timeShiftT_zero`.

The first horizon definition used proposition-valued `if` without activating
classical decidability inside the definition:

```text
Restart.lean:117:2: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  Decidable (0 < ν ∧ a ∈ initialClassT ∧ f ∈ forceClassT)
```

It was fixed with a local `classical` tactic block, not a new instance.

Rewriting only the horizon under a regularity predicate failed because the
solution type depends on that horizon:

```text
Restart.lean:148:6: error: Tactic `rewrite` failed: motive is not type correct:
  fun _a => PeriodicLocalRegularity ν a f _a
    (periodicLocalSolutionOfInput H ν hν a ha f hf)
```

The final implementation selects a subtype containing both the solution and
its regularity proof and transports that bundle once.

## Sole named input

There is no new or residual named input in this lane.  The only assumed input
is exactly the already defined U9 target:

```lean
def PeriodicQuantitativeLocalInput' : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ K : ℝ≥0∞, K ≠ ⊤ → ∀ M : ℕ → ℝ≥0∞, (∀ m, M m ≠ ⊤) → ∃ δ : ℝ, 0 < δ ∧
    ∀ a : SpatialField, a ∈ initialClassT → periodicSobolevENorm 1 a ≤ K →
      ∀ g : SpaceTimeField, ContDiff ℝ ∞ g → IsPeriodicOn univ g →
        (∀ m : ℕ, forceSobolevENormT 1 (m : ℝ) g ≤ M m) →
          ∃ w : ClassicalSolutionT ν a g δ, PeriodicLocalRegularity ν a g δ w
```

U9d/U9e remains responsible for discharging it.  The existing
`nonzero_forced_witness'` proves that its conclusion-side requirements are
simultaneously satisfiable by nonzero datum, force, and solution witnesses.
