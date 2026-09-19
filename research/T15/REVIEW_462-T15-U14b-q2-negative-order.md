ACCEPT

## 1. What the lane claims

The worker claims the sharp `q = 2` convergence theorem and the combined
canonical field, with only the raw `ContDiff`, compact-positive-time-support,
and `PlacementData` hypotheses (`research/T15/REPORT_462.md:5-37`). It also
claims 17 proved declarations, a literal field-conformance probe, and a
nonzero packet instance (`research/T15/REPORT_462.md:41-50`).

The claim is faithful to the lane brief and to the canonical field. The
canonical declaration quantifies `q`, the proof that `q = 1 ∨ q = 2`, then
`s < criticalOrder q.toReal`, and uses the right-neighborhood filter at zero
(`formalization/NSFormalization/Section3/T15/Scaling.lean:447-452`). The
delivered combined theorem has exactly that order and exactly the same force
family (`formalization/NSFormalization/Section3/T15/ConvergenceTwo.lean:486-497`).
The specialized theorem has precisely `q = 2` and
`s < criticalOrder ((2 : ℝ≥0∞).toReal)`
(`formalization/NSFormalization/Section3/T15/ConvergenceTwo.lean:435-442`).
The literal `exact forceConvergence hf hc place` check compiles
(`research/T15/probes/convergence_two_closes.lean:19-28`).

The mathematics agrees with the cited source and tree lemmas:

- The paper gives the force mixed scaling
  `α(p,q) = -3 + 3/p + 2/q` and the spatial/time change-of-variables argument
  (`paper/sections/03-torus.tex:129-132`,
  `paper/sections/03-torus.tex:148-158`). The tree realizes that identity in
  `packetMixedScaling`
  (`formalization/NSFormalization/Section3/T15/Mixed.lean:355-379`).
- The canonical Bessel weight really is `1 + 4π² Σᵢ kᵢ²`, and datum existence
  is not hidden: an empty datum infimum would be `⊤`
  (`formalization/NSFormalization/Section3/T10/PeriodicData.lean:66-69`,
  `formalization/NSFormalization/Section3/T10/PeriodicData.lean:104-120`).
- The coefficient estimate used by the new negative-order bound is the stated
  torus `L¹` estimate
  (`formalization/NSFormalization/Section3/T10/FourierCalculus.lean:33-41`).
  Sharp lattice summability is proved for every `r < -3/2`
  (`formalization/NSFormalization/Section3/T15/ConvergenceTwo.lean:24-94`),
  and the resulting datum bound is proved at
  `formalization/NSFormalization/Section3/T15/ConvergenceTwo.lean:137-172`.
- Single-copy periodization is an actual equality of torus lifts
  (`formalization/NSFormalization/Section3/T15/Mixed.lean:288-312`), while
  order-zero Parseval is an equality with the physical `L²` norm
  (`formalization/NSFormalization/Section3/T15/ParsevalZero.lean:28-54`).
  These are used in the packet endpoint bounds at
  `formalization/NSFormalization/Section3/T15/ConvergenceTwo.lean:294-369`.
- Fourier-data interpolation and time Hölder are genuine inequalities, not
  repackaged goals
  (`formalization/NSFormalization/Section3/T15/ConvergenceTwo.lean:201-292`).
  The final branch chooses `r = (3*s - 3/2)/2`, proves
  `3*s < r < -3/2`, and obtains the positive exponent
  `1 - 3*θ/2`
  (`formalization/NSFormalization/Section3/T15/ConvergenceTwo.lean:449-483`).

No hypothesis is silently strengthened or vacuous. In particular, the main
statement has no `⊤.toReal`, no empty interval, and no extra named analytic
input. The only local interval is `Ioc 0 place.ε₀`, made eventual at `𝓝[>] 0`
using `place.eps_pos`
(`formalization/NSFormalization/Section3/T15/ConvergenceTwo.lean:429-432`,
`formalization/NSFormalization/Section3/T15/ConvergenceTwo.lean:480-483`).
The supplied placement has `ε₀ = 1/2` with an explicit positivity proof
(`research/T15/probes/convergence_two_closes.lean:134-156`).

## 2. What is in Lean

There are exactly 17 public theorem declarations in the new module, matching
the 17 entries in the axiom file
(`research/T15/axioms_u14b.lean:5-21`). The two claimed main theorem statements
exist verbatim at
`formalization/NSFormalization/Section3/T15/ConvergenceTwo.lean:435-497`.
All named hypotheses are used in the endpoint construction or the final
branch, and direct elaboration emits no unused-binder or other warning from
this module.

The result is non-vacuous in two independent senses. Smooth periodic datum
paths are constructed and used to collapse the infimum norms
(`formalization/NSFormalization/Section3/T15/ConvergenceTwo.lean:273-281`,
`formalization/NSFormalization/Section3/T15/ConvergenceTwo.lean:302-321`,
`formalization/NSFormalization/Section3/T15/ConvergenceTwo.lean:338-358`). Also,
the delivered probe proves `force (1/2, 0) ≠ 0` before applying the complete
two-exponent theorem
(`research/T15/probes/convergence_two_closes.lean:158-173`); that probe
typechecks with no output.

Hygiene passes. A search of
`formalization/NSFormalization/Section3/T15/ConvergenceTwo.lean` finds no
`sorry`, `admit`, `axiom`, `native_decide`, or `set_option maxHeartbeats`.
The lane commit itself adds `ConvergenceTwo.lean` and does not modify any
pre-existing Lean module. Its exact name-status output is:

```text
A	formalization/NSFormalization/Section3/T15/ConvergenceTwo.lean
A	research/T15/ATTEMPTS_U14b.md
A	research/T15/REPORT_462.md
M	research/T15/T15_SPLIT.md
A	research/T15/axioms_u14b.lean
A	research/T15/probes/convergence_two_closes.lean
```

The requested three-dot command reports two merge bases and therefore also
lists the inherited lane-458 files. Its exact output is:

```text
warning: origin/erenup/integration-section3...HEAD: multiple merge bases, using af49f7bdc7de44e26c6a6d68af63d5eb08f135be
formalization/NSFormalization/Section3/T15/Convergence.lean
formalization/NSFormalization/Section3/T15/ConvergenceTwo.lean
research/T15/ATTEMPTS_U14.md
research/T15/ATTEMPTS_U14b.md
research/T15/REPORT_458.md
research/T15/REPORT_462.md
research/T15/T15_SPLIT.md
research/T15/axioms_u14.lean
research/T15/axioms_u14b.lean
research/T15/probes/convergence_closes.lean
research/T15/probes/convergence_two_closes.lean
```

The direct lane-commit diff above resolves that merge-base ambiguity and
confirms the worker's “no existing Lean module changed” claim. No path under
`verification/` occurs in either the lane-commit diff or the three-dot diff.

## 3. Gaps and negative check

No mathematical gap remains. The worker explicitly reports no residual strip
(`research/T15/REPORT_462.md:52-69`), and the attempted-development record
ends with the complete range `s < -1/2`
(`research/T15/ATTEMPTS_U14b.md:278-284`). Consequently there is no “not in
the tree” gap claim requiring a Section4-wide missing-lemma grep.

The reviewer mutation is
`research/T15/probes/rev462_widen_threshold.lean:18-25`. It substantively
widens the main `q = 2` conclusion from `s < -1/2` to `s < 0`, without dropping
an argument. Applying the delivered proof then fails exactly as expected:

```text
../research/T15/probes/rev462_widen_threshold.lean:25:2: error: Type mismatch
  forceConvergence_two hf hc place
has type
  ∀ s < criticalOrder (ENNReal.toReal 2),
    Tendsto (fun ε => forceSobolevENormT 2 s (periodizedScaledForce f place.x₀ place.T ε)) (𝓝[>] 0) (𝓝 0)
but is expected to have type
  ∀ s < 0, Tendsto (fun ε => forceSobolevENormT 2 s (periodizedScaledForce f place.x₀ place.T ε)) (𝓝[>] 0) (𝓝 0)
```

Exit code: `1`. This confirms that the sharp negative threshold is load-bearing.

## 4. Commands and results

All Lean commands were run after `. scripts/lean-env.sh`, from `verification/`,
with `LEAN_NUM_THREADS=6`.

```text
$ lake build NSFormalization.Section3.T15.Convergence
Build completed successfully (10024 jobs).
EXIT_CODE=0
```

The command also replayed pre-existing warnings in imported Source, Paper1,
Paper3, and vendor modules; it emitted no warning from `Convergence.lean`.

```text
$ lake build NSFormalization.Section3.T15.ConvergenceTwo
✔ [10040/10040] Built NSFormalization.Section3.T15.ConvergenceTwo (4.1s)
Build completed successfully (10040 jobs).
EXIT_CODE=0
```

This command likewise replayed only pre-existing imported-module warnings; it
emitted no warning from `ConvergenceTwo.lean`.

```text
$ lake env lean ../formalization/NSFormalization/Section3/T15/ConvergenceTwo.lean
EXIT_CODE=0
```

Output before the exit status: exactly empty.

```text
$ lake env lean ../research/T15/probes/convergence_two_closes.lean
EXIT_CODE=0
```

Output before the exit status: exactly empty.

```text
$ lake env lean ../research/T15/axioms_u14b.lean
'NSFormalization.Section3.T15.summable_coordinate_rpow' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T15.coordinate_weight_le_periodic' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T15.summable_periodicWeight_rpow' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T15.negative_fourier_energy_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T15.tsum_energy_interpolation' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T15.norm_datum_le_L1' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T15.summable_vector_energy' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T15.datum_norm_sq_eq_energy' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T15.norm_datum_interpolation' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T15.eLpNorm_two_interpolation' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T15.forceNorm_interpolation' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T15.packet_forceNorm_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T15.packet_negative_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T15.packet_interpolated_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T15.forceConvergence_two_low' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T15.forceConvergence_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T15.forceConvergence' depends on axioms: [propext, Classical.choice, Quot.sound]
EXIT_CODE=0
```

The unfiltered `make check` command exited `0`; its stdout contained 1,256,402
bytes of architecture/closure JSON. I reran the same gate through `tail -n 14`
to record its exact final output compactly:

```text
      "Tests.Correction3"
    ]
  },
  "base_compatibility_checked": false,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.045s

OK
python3 experiments/check_work_queue.py
45 work items: ownership, contract registration and task cards consistent.
EXIT_CODE=0
```

`scripts/gates.sh` and
`check_contracts.py --base-ref origin/erenup/integration-section3` are
conditional on changes under `verification/`; no such file was touched, so
those two conditional gates were not applicable.

No fixes are required.
