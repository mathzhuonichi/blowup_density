ACCEPT-WITH-NOTES

## 1. What the lane claims

The worker claims three transport conclusions: momentum at the unchanged
viscosity on `Ioo 0 place.T`, divergence on `Ico 0 place.T`, and zero initial
velocity, all for every `ε ∈ Ioc 0 place.ε₀`
(`research/T15/REPORT_446.md:5-40`). It also claims that the proof uses one
fixed local lattice translate, that pressure normalization does not change the
gradient, and that `eps_time` supplies initial vanishing
(`research/T15/REPORT_446.md:42-50`).

These are the right U8 obligations. The paper chooses `K_*`, `x₀`, and a small
positive `ε` with `2ε² < T`, sets `t_ε = T-ε²`, and uses amplitudes
`ε⁻¹, ε⁻², ε⁻³` (`paper/sections/03-torus.tex:101-120`). Proposition 3.3 says
the periodized fields solve momentum at viscosity `ν` and start from zero
(`paper/sections/03-torus.tex:122-123`); its proof explicitly says every
momentum term receives the common `ε⁻³` factor, incompressibility is preserved,
and viscosity is not rescaled (`paper/sections/03-torus.tex:140-143`).

The canonical target record has exactly the matching fields: initial at time
zero, divergence on `Ico 0 T`, and momentum on `Ioo 0 T`
(`formalization/NSFormalization/Section3/T10/PeriodicData.lean:278-285`). The
eventual T15 assembly pins the record velocity and pressure to precisely these
periodized fields (`formalization/NSFormalization/Section3/T15/Scaling.lean:289-305`).

## 2. What is in Lean

The three statements printed in the worker report agree with the declarations
in the module:

1. `periodized_initial` has exactly the reported scale interval and zero value
   (`formalization/NSFormalization/Section3/T15/Equation.lean:34-41`).
2. `periodized_divergence` has the raw extension-divergence premise and the
   exact `Ico 0 place.T` conclusion
   (`formalization/NSFormalization/Section3/T15/Equation.lean:267-279`).
3. `periodized_momentum` keeps the same `ν`, uses normalized pressure, and has
   the exact `Ioo 0 place.T` conclusion
   (`formalization/NSFormalization/Section3/T15/Equation.lean:281-314`).

Statement fidelity is good. The scale definitions use `T-ε²`, source scaling
`ε⁻²`, and amplitudes `ε⁻¹, ε⁻², ε⁻³`
(`formalization/NSFormalization/Section3/T15/Bridges.lean:56-76`), exactly as in
the paper. The hypotheses are raw `scalingStatement` clauses: force vanishing,
the extended residual identity, and extended divergence occur at
`formalization/NSFormalization/Section3/T15/Scaling.lean:484-491`; support and
compactness occur at `:466-469`. The theorem does not add smoothness, positivity
of `ν`, a totalized-norm premise, or an opaque named input. Although
`CompactPositiveTimeSupport f` itself implies nonpositive-time vanishing, both
it and `hfzero` are genuine raw packet clauses, and both named inputs are used:
the former in the force single-copy step and the latter in scaled momentum
(`formalization/NSFormalization/Section3/T15/Equation.lean:66-75,312-314`).

The proof mechanism is also substantive. Closed strict-cube support is upgraded
to neighbourhood equality at cube representatives
(`formalization/NSFormalization/Section3/T15/Equation.lean:86-135`), local
Fréchet congruence covers temporal derivative, advection, Laplacian, and pressure
gradient (`formalization/NSFormalization/Section3/T15/Equation.lean:137-158`),
and floor reduction gives a fixed translate at arbitrary spatial points
(`formalization/NSFormalization/Section3/T15/Equation.lean:166-201`). The
translation identities then connect to the unchanged-viscosity parabolic
identity (`formalization/NSFormalization/Section3/T15/Equation.lean:203-227`;
`formalization/NSFormalization/Source/ParabolicScaling.lean:101-119`). Pressure
normalization is exactly subtraction of a time-dependent spatial constant
(`formalization/NSFormalization/Section3/T10/PeriodicData.lean:249-261`), and
its gradient invariance is proved directly
(`formalization/NSFormalization/Section3/T15/Equation.lean:43-47`).

There is no interval vacuity: `PlacementData` requires `0 < T`, `0 < ε₀`, and
`2ε² < T` for every admitted scale
(`formalization/NSFormalization/Section3/T15/Scaling.lean:108-115,165-183`). The
probe constructs `T=1`, a positive threshold, and all placement fields
(`research/T15/probes/equation_closes.lean:17-81`), applies all three theorems
(`research/T15/probes/equation_closes.lean:83-103`), and proves both the source
packet and an admitted periodized velocity are nonzero at interior times
(`research/T15/probes/equation_closes.lean:105-142`). Thus the lane is not
accepted through an empty interval or a zero-only example.

The reviewer mutation widens momentum from `Ioo 0 T` to `Ico 0 T`
(`research/T15/probes/rev446_widen_momentum.lean:10-28`). Reusing the lane proof
then fails specifically because the stronger statement includes `t=0`; this is
a substantive interval mutation, not a dropped argument.

Hygiene is otherwise clean. The lane adds one new formalization module and does
not modify an existing Lean module; the other changes are research/log records.
The axiom audit names all 18 declarations
(`research/T15/axioms_u8.lean:3-20`). Searches over all three changed Lean files
found no `sorry`, `admit`, declaration `axiom`, `native_decide`, or
`maxHeartbeats` setting. The lane-439 closed-cube observation quoted in the
report (`research/T15/REPORT_446.md:69-72`) agrees with line 62 of that branch's
report as inspected with `git show`.

## 3. Gaps and findings

There is no mathematical, statement, build, axiom, non-vacuity, or missing-lemma
gap for U8. The worker accurately limits the result to three fields rather than
claiming a complete `ClassicalSolutionT` assembly
(`research/T15/REPORT_446.md:74-85`). The report declares no theorem to be “not
in the tree.” As a defensive whole-tree check, `grep -rnE` for the four scaling
wrapper names found only the differently named Section 4 residual lemmas; the
canonical wrappers are in `verification/Bindings/Scaling.lean:58-103`, while
the formalization module legitimately uses the importable source identities at
`formalization/NSFormalization/Source/ParabolicScaling.lean:41-45,101-119`.

One record-only hygiene finding remains:

1. **Low — diff whitespace.** `git diff --check` reports trailing whitespace at
   `research/T15/ATTEMPTS_U8.md:366` and `research/T15/ATTEMPTS_U8.md:368`.
   Exact fixes: delete the two trailing spaces from line 366, and delete the
   four trailing spaces from line 368. These are blank lines inside a quoted
   diagnostic and do not affect any Lean result.

## 4. Commands and results

All Lean commands were run after `. scripts/lean-env.sh`, from `verification/`,
with `LEAN_NUM_THREADS=6`. The lane-review bootstrap reported Lean
`v4.34.0-rc2`, ran the registered `lake test` closure, and ended exactly with:

```text
== OK
```

`LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T15.Equation` exited 0.
It replayed warnings from pre-existing upstream modules, none from
`Equation.lean`, and ended exactly with:

```text
Build completed successfully (10004 jobs).
```

`LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section3/T15/Equation.lean`:

```text
exit 0
<no output>
```

`LEAN_NUM_THREADS=6 lake env lean ../research/T15/probes/equation_closes.lean`:

```text
exit 0
<no output>
```

`LEAN_NUM_THREADS=6 lake env lean ../research/T15/axioms_u8.lean` exited 0 with:

```text
'NSFormalization.Section3.T15.periodized_velocity_early' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T15.periodized_initial' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T15.pressureGradient_normalizePressureT' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T15.scaled_source_time_lt_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T15.scaled_momentum' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T15.scaled_divergence' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T15.periodize_eventuallyEq_of_closed_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T15.residual_eq_of_eventuallyEq' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T15.divergence_eq_of_eventuallyEq' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T15.floor_representative_mem_cube' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T15.periodize_sub_lattice' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T15.periodize_eventuallyEq_translate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T15.residual_translate' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T15.divergence_translate' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T15.periodized_velocity_local_translate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T15.periodized_pressure_local_translate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T15.periodized_divergence' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T15.periodized_momentum' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`. scripts/lean-env.sh && make check` exited 0. Its exact terminal checks were:

```text
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.046s

OK
python3 experiments/check_work_queue.py
45 work items: ownership, contract registration and task cards consistent.
```

The conditional verification gates were not applicable: this lane changes no
path under `verification/`, so `scripts/gates.sh` and
`check_contracts.py --base-ref origin/erenup/integration-section3` were not run.
The ordinary `make check` did run `experiments/check_contracts.py` and passed.

The negative command
`LEAN_NUM_THREADS=6 lake env lean ../research/T15/probes/rev446_widen_momentum.lean`
exited 1 as expected:

```text
../research/T15/probes/rev446_widen_momentum.lean:28:2: error: Type mismatch
  periodized_momentum hK hu hp hf hfzero heq place
has type
  ∀ ε ∈ Ioc 0 place.ε₀,
    ∀ t ∈ Ioo 0 place.T,
      ∀ (x : Space),
        NavierStokesR3.ProblemStatement.navierStokesResidual ν (periodizedScaledVelocity u place.x₀ place.T ε)
            (normalizedScaledPressure p place.x₀ place.T ε) t x =
          periodizedScaledForce f place.x₀ place.T ε (t, x)
but is expected to have type
  ∀ ε ∈ Ioc 0 place.ε₀,
    ∀ t ∈ Ico 0 place.T,
      ∀ (x : Space),
        NavierStokesR3.ProblemStatement.navierStokesResidual ν (periodizedScaledVelocity u place.x₀ place.T ε)
            (normalizedScaledPressure p place.x₀ place.T ε) t x =
          periodizedScaledForce f place.x₀ place.T ε (t, x)
```

`git diff --name-only origin/erenup/integration-section3...HEAD` returned:

```text
formalization/NSFormalization/Section3/T15/Equation.lean
logs/LESSONS.md
research/T15/ATTEMPTS_U8.md
research/T15/REPORT_446.md
research/T15/T15_SPLIT.md
research/T15/axioms_u8.lean
research/T15/probes/equation_closes.lean
```

`git diff --check origin/erenup/integration-section3...HEAD` returned the only
review note below (the final two lines render spaces as `␠` so this review file
itself remains whitespace-clean):

```text
research/T15/ATTEMPTS_U8.md:366: trailing whitespace.
+␠␠
research/T15/ATTEMPTS_U8.md:368: trailing whitespace.
+␠␠␠␠
```
