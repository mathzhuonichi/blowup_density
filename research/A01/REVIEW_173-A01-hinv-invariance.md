ACCEPT

## 1. What the lane claims

The reworked report claims route β: `HasAprioriBoundInv`, the one-way conversion
`HasAprioriBound.toInv`, the core helper `forced_global_mild_core_of_boundInv`, and
the full exports `forced_global_of_boundInv` and
`localTheory_on_prescribed_horizon_of_boundInv` (`research/A01/REPORT_173.md:3-86`).
It says the two full exports have the same seven-clause conclusions as their
unrestricted-bound consumers, while the only consumer-hypothesis change is the
restricted invariant bound (`research/A01/REPORT_173.md:95-104`). It leaves route α
and the actual uniform estimate open (`research/A01/REPORT_173.md:107-134`).

These are the right claims for the brief. P9a expressly permits restricting the
bound quantifier if the consumer loop is re-closed
(`collaboration/HANDOFF.md:112-115`). The paper states local existence, uniqueness,
and continuation at `paper/sections/02-preliminaries.tex:105-118`, and gives the mild
equation and uniqueness argument at
`paper/sections/appendix-a-local-theory.tex:109-125`. Angle invariance is a
cylinder-carrier implementation condition, not an extra assertion about the paper's
physical solution.

Every declaration printed in the report exists with the reported statement:

- `HasAprioriBoundInv`: report `research/A01/REPORT_173.md:8-20`, Lean
  `formalization/NSFormalization/Section4/A01/AprioriInvariance.lean:26-37`.
- `HasAprioriBound.toInv`: report `research/A01/REPORT_173.md:24-30`, Lean
  `formalization/NSFormalization/Section4/A01/AprioriInvariance.lean:39-46`.
- `forced_global_mild_core_of_boundInv`: report
  `research/A01/REPORT_173.md:32-46`, Lean
  `formalization/NSFormalization/Section4/A01/AprioriInvariance.lean:48-62`.
- `forced_global_of_boundInv`: report `research/A01/REPORT_173.md:48-66`, Lean
  `formalization/NSFormalization/Section4/A01/AprioriInvariance.lean:108-131`.
- `localTheory_on_prescribed_horizon_of_boundInv`: report
  `research/A01/REPORT_173.md:68-86`, Lean
  `formalization/NSFormalization/Section4/A01/AprioriInvariance.lean:133-151`.

## 2. What is in Lean

### Predicate and hypotheses

`HasAprioriBoundInv` has the same fixed `R`, quantified `T`, `hT`, `hTS`, path `u`,
and Duhamel equation as `HasAprioriBound`; its sole addition is the angle-invariance
premise on that same `u` (`formalization/NSFormalization/Section4/A01/Horizon.lean:97-114`;
`formalization/NSFormalization/Section4/A01/AprioriInvariance.lean:26-37`). The exact
expansion is checked by `Iff.rfl` in
`research/A01/probes/rev173_fidelity.lean:15-28`. The conversion theorem discards
only that new premise when applying the old bound
(`formalization/NSFormalization/Section4/A01/AprioriInvariance.lean:39-46`).

For the local-theory pair, direct `#check` output becomes identical after the single
substitution `HasAprioriBoundInv` to `HasAprioriBound`. Every other binder remains:
`hq`, positive viscosity and horizon, nonnegative `R`, datum, divergence-free datum,
force regularity, and the initial norm bound. `forced_global_of_bound_unconditional`
writes the old predicate inline
(`formalization/NSFormalization/Section4/A01/ContinuationInvariant.lean:280-289`);
that body is exactly `HasAprioriBound`, so replacing it by `HasAprioriBoundInv` is
again the only logical hypothesis change.

There is no vacuity device. The consumers retain `hν : 0 < ν` and `hS : 0 < S`,
bound windows retain `hT : 0 ≤ T`, and no `ENNReal.toReal` or empty-interval
shortcut appears. The restricted bound is invoked with proved invariance at the
restart endpoint and terminal horizon
(`formalization/NSFormalization/Section4/A01/AprioriInvariance.lean:86-92,97-106`).
The datum-divergence hypothesis is consumed by divergence propagation and the proved
invariance by ordinary descent
(`formalization/NSFormalization/Section4/A01/AprioriInvariance.lean:127-131`).

### Exact seven-clause exports

The conclusion of `forced_global_of_boundInv` at
`formalization/NSFormalization/Section4/A01/AprioriInvariance.lean:116-126` is
token-identical to that of `forced_global_of_bound_unconditional` at
`formalization/NSFormalization/Section4/A01/ContinuationInvariant.lean:290-300`.
The conclusion of `localTheory_on_prescribed_horizon_of_boundInv` at
`formalization/NSFormalization/Section4/A01/AprioriInvariance.lean:140-150` is
token-identical to `localTheory_on_prescribed_horizon` at
`formalization/NSFormalization/Section4/A01/Horizon.lean:143-153`. The direct
`#check` comparison produced:

```text
exit_code=0
forced_conclusion_suffix_equal=true
local_conclusion_suffix_equal=true
local_full_type_equal_after_bound_predicate_substitution=true
```

Both conclusions contain all seven clauses after the `u,U` witnesses: norm bound,
cylinder initial value, ordinary initial value, ordinary-lift descent, divergence
freedom, forced Duhamel equation, and angle invariance. The consumer probe closes
with the full export (`research/A01/probes/fix173_consumer_match.lean:15-34`), and
the fidelity probe checks the local export
(`research/A01/probes/rev173_fidelity.lean:30-49`).

The four-clause theorem is named and documented as a core helper
(`formalization/NSFormalization/Section4/A01/AprioriInvariance.lean:48-50`). It is
likewise called a core helper/induction in `research/A01/ATTEMPTS_HINV.md:10-18`,
`research/A01/REPORT_173.md:95-100`, and `research/A01/A3_SPLIT.md:281-286`; no
record exports it as the main consumer.

### Invariance and non-vacuity

The consumer does not assume invariance separately. Initial invariance comes from
`ordinarySobolev_angle` (`formalization/NSFormalization/Section4/A01/AprioriInvariance.lean:63-67`;
the lemma is at `formalization/NSFormalization/Source/OrdinaryCylinderDescent.lean:69-77`).
The restart proof constructs the translated mild path, applies source/heat covariance,
and uses contraction uniqueness
(`formalization/NSFormalization/Section4/A01/ContinuationInvariant.lean:69-146`).
Invariant restarts and gluing are supplied at
`formalization/NSFormalization/Section4/A01/ContinuationInvariant.lean:150-202`.
Thus `HasAprioriBoundInv` receives proved invariance, not a circular assumption.

The filed concrete example has `q = 6`, `ν = 1`, `S = 1`, zero datum/force, and
calls `forced_global_of_boundInv`; its target explicitly contains `u`, `U`, and all
seven clauses (`research/A01/axioms_hinv.lean:23-59`). Its uniform-bound premise is
honestly exposed. Separately, a reviewer stdin probe using
`OrdinaryForcedLocal.exists_local` produced an actual invariant Duhamel solution on
some `0 < T ≤ 1`, so the restricted quantified solution class is not empty.

### Hygiene and citations

The lane-added Lean files contain no `sorry`, `admit`, `axiom`, or `native_decide`,
and add no `maxHeartbeats`. The imported base declaration
`restart_window_invariance` has a pre-existing, commented, per-declaration `600000`
setting (`formalization/NSFormalization/Section4/A01/ContinuationInvariant.lean:60-69`);
commit `5b4d9ad` did not add or modify it. Against `origin/erenup/integration`, the
only formalization path is the new `AprioriInvariance.lean`; no existing Lean module
was modified. The `A3_SPLIT.md` edit is the requested row-(iv) note.

The route-α citations are accurate: source covariance is at
`formalization/NSFormalization/Source/ForcedCylinderInvariant.lean:18-26`, heat
covariance at `formalization/NSFormalization/Source/ForcedCylinderTranslation.lean:48-71`,
and cylinder uniqueness has the small-kernel premise at
`vendor/NavierStokesAndEuler/Euler/VolterraUniqueness.lean:20-31`. The generic
unrestricted theorem and different `R3HsVelocity 3` specialization are at
`formalization/FormalPatched/EndpointSafeTwoSpaceUniqueness.lean:117-121,228-237`.
`Propagation.lean` is indeed scalar Grönwall, not invariance
(`formalization/NSFormalization/Section4/A01/Propagation.lean:1-23,62-81`).

## 3. Gaps

There is no remaining lane-173 defect for route β.

The estimate `HasAprioriBoundInv hq hν a F hF R` remains a supply-side obligation
(`research/A01/REPORT_173.md:107-112`). Route α, the stronger claim that every
unrestricted Duhamel solution is invariant, was not proved
(`research/A01/REPORT_173.md:114-119`). A required whole-tree `grep -rn` over
`formalization/NSFormalization/Section4` found no `duhamel_angle_invariant`; every
`HasAprioriBoundInv` hit is its definition, conversion, or consumer in the new module.
The broader search found the local cylinder uniqueness/covariance machinery at
`formalization/NSFormalization/Section4/A01/ContinuationInvariant.lean:117-145` and
the different-contract unrestricted theorem cited above. The worker does not hide a
drop-in α lemma and explicitly avoids claiming that unrestricted uniqueness is absent
from the tree (`research/A01/REPORT_173.md:114-119`;
`research/A01/ATTEMPTS_HINV.md:46-82`).

No fixes are required.

## 4. Commands and results

Every shell sourced `. scripts/lean-env.sh`; Lake ran only from `verification/`, with
`LEAN_NUM_THREADS=6`, one command at a time.

```text
$ LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.A01.AprioriInvariance
Build completed successfully (3944 jobs).

$ LEAN_NUM_THREADS=6 lake build --quiet NSFormalization.Section4.A01.AprioriInvariance
<no output>

$ LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section4/A01/AprioriInvariance.lean
<no output>
```

The axiom/full-export conformance file exited 0 with exactly:

```text
$ LEAN_NUM_THREADS=6 lake env lean ../research/A01/axioms_hinv.lean
'NSFormalization.Section4.A01.HasAprioriBoundInv' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.HasAprioriBound.toInv' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.forced_global_mild_core_of_boundInv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A01.forced_global_of_boundInv' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.localTheory_on_prescribed_horizon_of_boundInv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

Consumer/type-fidelity probes both exited 0:

```text
$ LEAN_NUM_THREADS=6 lake env lean ../research/A01/probes/fix173_consumer_match.lean
<no output>
$ LEAN_NUM_THREADS=6 lake env lean ../research/A01/probes/rev173_fidelity.lean
<no output>
```

The direct four-`#check` comparison exited 0 and printed this comparison result:

```text
exit_code=0
forced_conclusion_suffix_equal=true
local_conclusion_suffix_equal=true
local_full_type_equal_after_bound_predicate_substitution=true
```

The independent positive-time invariant-solution stdin instance exited 0:

```text
$ LEAN_NUM_THREADS=6 lake env lean --stdin
<no output>
```

Substantive mutation of the main full export, changing `‖u‖ ≤ R` to
`‖u‖ ≤ R - 1`, exited 1 for the expected mismatch; no argument was dropped:

```text
<stdin>:34:2: error: Type mismatch
  forced_global_of_boundInv hq hν hS hR a ha F hF hu₀ hbound
has type
  ∃ u U,
    ‖u‖ ≤ R ∧
      u ⟨0, ⋯⟩ = ordinarySobolev (q + 1) a.toLp ⋯ ∧
        U ⟨0, ⋯⟩ = a.toLp ∧
          (∀ (t : ↑(Icc 0 S)), ordinaryLift (U t) = value 1 (u t)) ∧
            (∀ (t : ↑(Icc 0 S)), value 1 (u t) ∈ divergenceFreeSpace 1 1 0) ∧
              (∀ (t : ↑(Icc 0 S)),
                  u t = quadraticDuhamel 1 ν hν ⋯ ⋯
                    (coefficients 1 hq (sobolevPath F hF q))
                    (ordinarySobolev (q + 1) a.toLp ⋯) u t) ∧
                ∀ (θ : AddCircle 1) (t : ↑(Icc 0 S)),
                  (sobolevTranslation 1 (q + 1) (0, θ)) (u t) = u t
but is expected to have type
  ∃ u U,
    ‖u‖ ≤ R - 1 ∧
      u ⟨0, ⋯⟩ = ordinarySobolev (q + 1) a.toLp ⋯ ∧
        U ⟨0, ⋯⟩ = a.toLp ∧
          (∀ (t : ↑(Icc 0 S)), ordinaryLift (U t) = value 1 (u t)) ∧
            (∀ (t : ↑(Icc 0 S)), value 1 (u t) ∈ divergenceFreeSpace 1 1 0) ∧
              (∀ (t : ↑(Icc 0 S)),
                  u t = quadraticDuhamel 1 ν hν ⋯ ⋯
                    (coefficients 1 hq (sobolevPath F hF q))
                    (ordinarySobolev (q + 1) a.toLp ⋯) u t) ∧
                ∀ (θ : AddCircle 1) (t : ↑(Icc 0 S)),
                  (sobolevTranslation 1 (q + 1) (0, θ)) (u t) = u t
```

`make check` from the worktree root exited 0. Its stdout contains the large
architecture JSON; exact head and terminal excerpts are:

```text
python3 experiments/check_formalization_plan.py --check
{
  "task_count": 30,
  "source_counts": {
    "formalization": 478,
    "vendor/NavierStokesAndEuler": 2486,
    "vendor/HeliCorgi": 129
  },
  "source_manifest_entries": 2975,
  "missing_copied_imports": [],
  "citation_interfaces_reachable": [],
  "tokens_in_copied_umbrella_closure": [
    {
      "module": "NSFormalization.Paper1.BoundaryCorollary",
      "path": "formalization/NSFormalization/Paper1/BoundaryCorollary.lean",
      "line": 90,
      "token": "sorry"
    }
  ],
  "tracked_cache_free": true,
  "source_hashes_match": false
}
⋯
  "base_compatibility_checked": false,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.046s

OK
python3 experiments/check_work_queue.py
30 work items: ownership, contract registration and task cards consistent.
```

The displayed copied-source `sorry` is the known out-of-scope
`formalization/NSFormalization/Paper1/BoundaryCorollary.lean:90`; it is neither in
this lane's diff nor the imported module closure.

Hygiene commands:

```text
$ rg -n '\b(sorry|admit|axiom|native_decide)\b|set_option\s+maxHeartbeats' \
    formalization/NSFormalization/Section4/A01/AprioriInvariance.lean \
    research/A01/axioms_hinv.lean research/A01/probes/fix173_consumer_match.lean
<no output>
$ git diff --check origin/erenup/integration...HEAD
<no output>
$ git diff --name-only origin/erenup/integration...HEAD
formalization/NSFormalization/Section4/A01/AprioriInvariance.lean
research/A01/A3_SPLIT.md
research/A01/ATTEMPTS_HINV.md
research/A01/REPORT_173.md
research/A01/axioms_hinv.lean
research/A01/probes/fix173_consumer_match.lean
$ git diff --name-only origin/erenup/integration...HEAD -- verification
<no output>
```

Since `verification/` is untouched, `scripts/gates.sh` and
`check_contracts.py --base-ref origin/erenup/integration` are not applicable under
the conditional gate rule. No git mutation command was run.
