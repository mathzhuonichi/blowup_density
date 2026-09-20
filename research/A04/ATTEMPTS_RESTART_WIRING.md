# Lane 213 — restart wiring audit and proved components

## Unconditional components

`Section4/A04/RestartWiring.lean` proves:

1. `map_forceTimeMeasure_shift_le`: positive translation pushes the half-line
   measure to a measure bounded by the original half-line measure.
2. `restart_force`: the entire `MemForceR` predicate survives positive time
   translation, including smoothness and both L¹ and L² datum paths at every order.
3. `local_restart`: at each presingular time, A01 constructs a classical solution
   with datum `u(t₀,·)` and force `timeShift t₀ f`, on its selected local horizon.
4. `localCarrier_hasSmoothSobolevPath`: lane 209's regularity for the selected
   carrier supplies exactly A04's `HasSmoothSobolevPath` predicate.
5. `uniform_local_restart_H7`: for fixed ν>0, f, t₀≥0, and finite H⁷ bound K,
   there is δ>0 on which every admissible datum in that ball has a classical
   solution with force `timeShift t₀ f`. This uses the A01 lower bound and
   `ClassicalSolutionR.restrict`, without adding any analytic hypothesis.

The last result explicitly fixes t₀ **before** choosing δ. It is a local
existence component, not a weakened replacement for `Restart` or `restartBeyond`.
The A02 slice qualification is also unconditional in `MaximalWiring.lean`.

## Why the requested unconditional continuation chain is not supplied

The task's descriptions of the existing interfaces differ from the actual code.
These are separate obligations, not one missing force-shift or datum lemma.

| Interface | Actual hypotheses / quantifiers | What a direct application lacks |
| --- | --- | --- |
| `A04.Restart` (`Continuation.lean`) | A `def : Prop`, not a structure; `∀ ν>0, ∀ K≠⊤, ∃ δ>0, ∀ a f u p t₀, …`; only H¹ datum and shifted L¹H¹ force bounds | A01 only supplies an H⁷ ball bound for each fixed force; `Restart` contains no H² integral cap |
| `A01.horizon_lower_bound_H7_fixedForce` | `∀ ν>0, ∀ f, MemForceR f → ∀ K≠⊤, ∃ δ>0, ∀ a, …` | δ depends on f; substituting `timeShift t₀ f` also makes it depend on t₀ |
| `A01.highOrder_bddAbove_all_orders_Ico_full` | A particular classical `w` on T, `HasSmoothSobolevPath T w.velocity`, continuous cylinder paths on `Icc 0 T`, slice agreement including T, and `‖u‖≤R`; orders m≥3 | `SolvesBelow` and a finite H² integral do not directly supply these witnesses at T, the path regularity for arbitrary shorter solutions, or low-order lowering |
| `A02.patch` | Two solutions with the same initial datum and force, both starting at zero; horizon `max T₁ T₂` | It is not a concatenation theorem for different initial times and shifted forces |

Consequently an H⁷ bound derived for one solution cannot furnish the δ selected
before all a/f/S/u/p in the unchanged H¹ `restartBeyond` statement. Even a proof
of H⁷ continuation for each fixed solution would not instantiate that statement.
This is an interface mismatch, not a claim that the manuscript's H¹ theorem is false.

The exact existing named inputs remain `A04.Restart` and `A04.HigherOrderBound`.
The former needs the H¹-uniform restart analysis (or an independent proof of its
lifespan conclusion); the latter needs the integral-cap Grönwall assembly for
arbitrary `SolvesBelow` families. Lane 179's theorem is not that assembly.
`A01.ManuscriptHorizonLowerBoundH1` is an unproved definition, not a theorem.
Simply assuming it would still leave the shifted concatenation argument.

No conjunction/structure is introduced to conceal these distinct gaps under
one named input. No `restartBeyond'`, `extendsBeyond'`, or
`lifespanInfiniteOfLocallyFinite'` is advertised as unconditional. The original
conditional theorems and their conclusions are unchanged. Goal 2 is **partial**;
the one-missing-fact fallback cannot yet close the audited dependency chain.

## Search and proof attempts

Read the requested spec/comparison/review material and searched all Section4
D01/A03/A04/A01/C01 modules, plus A02, for restart, shifted forcing and smooth
Sobolev-path suppliers. `GronwallEndpoint` is under A01, not A04. The actual
`ForceShift` module proves only `forceSobolevENormL1_timeShift_le`, so the full
force-class closure is new here. The existing `patch` proof chooses the longer
of two zero-origin solutions; it cannot be applied directly to the restarted data.

For the new force proof, pushforward domination avoids separate integral
calculations for the two exponents. `MemLp.mono_measure` followed by
`MemLp.comp_of_map` handles both. The measure-preimage equality requires
`MeasurableSet.nullMeasurableSet`. Explicitly typing the shift's measurability
avoids a rewrite mismatch between `id t + t₀` and `t + t₀`.

## Validation and satisfiability

All five declarations print exactly `[propext, Classical.choice, Quot.sound]`.
`axioms_restart_wiring.lean` checks the translated zero force and constructs a
local solution from an actual `A04.zeroSol` slice. The force closure proof is
universal over arbitrary admissible f and nonnegative shifts; it does not rely
on zero-force stationarity. No endpoint value of a general `SolvesBelow` family
or unattained closed-horizon regularity is postulated. No existing file is changed.
Full gate results are recorded in `../A02/REPORT_213.md`.
