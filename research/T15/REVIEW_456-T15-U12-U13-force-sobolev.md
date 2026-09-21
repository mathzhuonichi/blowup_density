ACCEPT

## 1. What the lane claims

The worker claims complete U12/U13 coverage for every `0 ≤ s ≤ 1`: an
explicit positive constant family, an honest `L¹_t H^s(T³)` datum path, and the
paper's packet estimate.  The statements printed in the worker report at
`research/T15/REPORT_456.md:9-45` agree with the declarations in Lean:

- `packetEndpoint`, `packetComponentConst`, and `sobolevConst` are defined at
  `formalization/NSFormalization/Section3/T15/SobolevBound.lean:19-30`.
  The module-level constant has the unavoidable packet argument
  `sobolevConst (f : VelocityField) : ℝ → ℝ`; after `f` is fixed this is
  literally the `ScalingAPI.sobolevConst : ℝ → ℝ` field at
  `formalization/NSFormalization/Section3/T15/Scaling.lean:396-410`.
- `sobolevConst_pos` is exactly the reported
  `∀ s, 0 ≤ s → s ≤ 1 → 0 < sobolevConst f s` at
  `formalization/NSFormalization/Section3/T15/SobolevBound.lean:37-42`.
- `forceSobolev_memLp` has exactly the reported raw-field hypotheses and
  quantifier order at
  `formalization/NSFormalization/Section3/T15/SobolevBound.lean:44-55`.
- `packetSobolevBound` has exactly the reported raw-field hypotheses, interval,
  scale interval, force, constant, and exponents at
  `formalization/NSFormalization/Section3/T15/SobolevBound.lean:197-240`.
  These match the canonical fields at
  `formalization/NSFormalization/Section3/T15/Scaling.lean:412-437`.

This is the requested mathematics.  The paper defines the scaled force with
amplitude `ε⁻³` at `paper/sections/03-torus.tex:101-120`, states
`‖F_ε‖_{L¹_tH^s(T³)} ≤ C_s(ε^(1/2)+ε^(1/2-s))` for `0 ≤ s ≤ 1` at
`paper/sections/03-torus.tex:133-137`, and explains the two rates and endpoints
at `paper/sections/03-torus.tex:150-158`.  The Lean theorem uses the same
periodized scaled force and the same two powers.

No silent vacuity was found.  `PlacementData.eps_pos` makes `(0,ε₀]` nonempty
(`formalization/NSFormalization/Section3/T15/Scaling.lean:165-177`).  Although
the explicit constant uses `ENNReal.toReal`, the quantitative proof first
proves both endpoint norms `< ⊤` at
`formalization/NSFormalization/Section3/T15/SobolevBound.lean:114-119,170-183`;
it therefore does not exploit `⊤.toReal = 0`.  The named hypotheses are
honest: `hf` constructs smooth scaled/translated slices
(`SobolevBound.lean:61-66,136`), while `hc` supplies compact support and support
placement (`SobolevBound.lean:68-86,137`).  The lower-order hypotheses in the
public U12 fields are the canonical `[0,1]` domain; the path construction is in
fact stronger and only needs `s ≤ 1`.

## 2. What is in Lean

The new module contains exactly 16 declarations (four definitions and twelve
theorems).  U12 is an honest path, not merely a finite extended-norm assertion:
`MemForceSobolevT` explicitly contains an `IsPeriodicSobolevPath` and `MemLp`
witness at `formalization/NSFormalization/Section3/T15/Scaling.lean:86-90`.
`forceSobolev_memLp` obtains that witness from `T15.force_mem` and
`T17.force_coefficient_path_real` at
`formalization/NSFormalization/Section3/T15/SobolevBound.lean:52-55`; the
underlying real-order construction states continuity, compact support, strong
measurability, the path relation, and `MemLp` at
`formalization/NSFormalization/Section3/T17/Sobolev.lean:127-136`.

U13 follows the reported route B correctly:

- the copy is recentered and shown supported in the origin-centered cube at
  `formalization/NSFormalization/Section3/T15/SobolevBound.lean:57-86`;
- `chartRadius < 1/2` follows from the actual chart-ball hypothesis at
  `SobolevBound.lean:88-91`, using the coordinate separation lemma at
  `formalization/NSFormalization/Section3/T13/KernelComparison.lean:87-105`;
- the periodization/translation identity and Fourier-norm translation are at
  `SobolevBound.lean:93-112`;
- the cited interpolation theorem really bounds the periodic `H^s` time norm
  by the `H⁰`/`H¹` endpoint product, including the `2π` factor, at
  `formalization/NSFormalization/Paper1/PeriodicForceEndpointScaling.lean:23-35`;
- the cited packet endpoints really have rates `ε^(1/2)` and `ε^(-1/2)` at
  `formalization/NSFormalization/Paper1/PeriodicPacketEndpointRates.lean:20-29,47-56`;
- the algebra gives `ε^(1/2-s)` componentwise at
  `SobolevBound.lean:149-195`, and finite-component assembly plus the harmless
  positive `1` weakens this to the paper's two-term RHS at
  `SobolevBound.lean:213-240`.

The conformance probe checks the delivered theorems and the reverse record
projections by `exact` at
`research/T15/probes/sobolev_bound_closes.lean:174-214`.  Its concrete
placement has `ε₀=1/2>0`, an interior chart ball, compact positive-time
support, and an admissible `ε=1/2` at
`research/T15/probes/sobolev_bound_closes.lean:120-171,216-237`; it also proves
the raw force is nonzero at `(1/2,0)` at lines 217-231.  This is a substantive
non-vacuity instance, not an empty interval or zero packet.

## 3. Gaps and hygiene

No mathematical, statement, or build gap remains.

The worker's only "not located" statement is narrowly about a ready-made
`ENNReal` adapter from `dotHomogeneousENorm`/`homogeneousFourierENorm` to the
cycles-frequency `fourierSobolev` norm; it is not a claim that the Fourier
convention change itself is absent (`research/T15/ATTEMPTS_U12_U13.md:101-116`).
The required whole-tree check was:

```text
$ grep -rn --include='*.lean' -E 'dotHomogeneousENorm.*fourierSobolev|homogeneousFourierENorm.*fourierSobolev|fourierSobolev.*dotHomogeneousENorm|fourierSobolev.*homogeneousFourierENorm' formalization/NSFormalization/Section4
<no output>
```

Related ingredients do exist and were not misreported: the actual convention
comparison is in `formalization/NSFormalization/Source/FourierConvention.lean:106-143`,
and the Section 4 angular path is bounded by the cycles vector norm at
`formalization/NSFormalization/Section4/I03/Angular.lean:114-142`.  Since route
B closes the deliverable, the absence of that exact convenience adapter is no
residual.

The forbidden-token/heartbeat scan of the delivered module, conformance probe,
axiom audit, and reviewer probe returned no matches for
`sorry|admit|axiom|native_decide|maxHeartbeats`.  There is therefore no
heartbeat override to audit.  All 16 declarations print exactly
`[propext, Classical.choice, Quot.sound]`.

The lane commit itself adds one new Lean module and no existing Lean module:
`git show --name-status HEAD` reports `A` for `SobolevBound.lean`, the two new
research Lean files, and record-only edits.  The explicitly requested
three-dot comparison has two merge bases and therefore also lists inherited
lane-450 files:

```text
$ git diff --name-only origin/erenup/integration-section3...HEAD
warning: origin/erenup/integration-section3...HEAD: multiple merge bases, using 898e1c35c6554cfb636e4d755c26b85e86d0ff3a
formalization/NSFormalization/Section3/T15/SobolevBound.lean
formalization/NSFormalization/Section3/T15/SobolevPath.lean
logs/LESSONS.md
research/T15/ATTEMPTS_U12_U13.md
research/T15/ATTEMPTS_U9.md
research/T15/REPORT_450.md
research/T15/REPORT_456.md
research/T15/T15_SPLIT.md
research/T15/axioms_u12_u13.lean
research/T15/axioms_u9.lean
research/T15/probes/sobolev_bound_closes.lean
research/T15/probes/sobolev_path_closes.lean
```

`git diff --name-status HEAD^ HEAD` isolates lane 456 and confirms that the
only formalization entry is the new `SobolevBound.lean`.  Neither comparison
contains a `verification/` path, so the conditional `scripts/gates.sh` and
`check_contracts.py --base-ref origin/erenup/integration-section3` gates were
not triggered.

The reviewer mutation is
`research/T15/probes/rev456_exponent_sign_mutation.lean:10-22`.  It retains
every premise and argument but flips the main exponent from `1/2-s` to
`1/2+s`.  Lean rejects the changed proof with the expected statement mismatch:

```text
../research/T15/probes/rev456_exponent_sign_mutation.lean:22:2: error: Type mismatch
  packetSobolevBound hf hc place
has type
  ∀ (s : ℝ),
    0 ≤ s →
      s ≤ 1 →
        ∀ ε ∈ Ioc 0 place.ε₀,
          forceSobolevENormT 1 s (periodizedScaledForce f place.x₀ place.T ε) ≤
            ENNReal.ofReal (sobolevConst f s * (ε ^ (1 / 2) + ε ^ (1 / 2 - s)))
but is expected to have type
  ∀ (s : ℝ),
    0 ≤ s →
      s ≤ 1 →
        ∀ ε ∈ Ioc 0 place.ε₀,
          forceSobolevENormT 1 s (periodizedScaledForce f place.x₀ place.T ε) ≤
            ENNReal.ofReal (sobolevConst f s * (ε ^ (1 / 2) + ε ^ (1 / 2 + s)))
```

Exit status was `1`, as required.

## 4. Commands and results

All Lake commands were run from `verification/` after sourcing
`../scripts/lean-env.sh`, with `LEAN_NUM_THREADS=6`.

```text
$ lake build NSFormalization.Section3.T15.SobolevBound
Build completed successfully (10018 jobs).
```

The raw build also replayed warnings from existing upstream modules; it emitted
no warning or error from `SobolevBound.lean` itself.  A `pipefail` rerun with
`tail -n 1` produced the exact compact transcript above and exited `0`.

```text
$ lake env lean ../formalization/NSFormalization/Section3/T15/SobolevBound.lean
<no output; exit 0>

$ lake env lean ../research/T15/probes/sobolev_bound_closes.lean
<no output; exit 0>
```

```text
$ lake env lean ../research/T15/axioms_u12_u13.lean
'NSFormalization.Section3.T15.packetEndpoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T15.packetComponentConst' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T15.sobolevConst' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T15.packetComponentConst_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T15.sobolevConst_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T15.forceSobolev_memLp' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T15.chartForce' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T15.chartForce_smooth' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T15.chartForce_compact' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T15.chartForce_supportedInCube' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T15.chartRadius_lt_half' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T15.periodize_chartForce' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T15.chartForce_fourierNorm' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T15.packetEndpoint_lt_top' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T15.packet_component_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T15.packetSobolevBound' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The raw `make check` run exited `0`.  Its middle output is the generated
dependency-closure JSON (over 1 MB); the exact final transcript from a second
`set -o pipefail; make check 2>&1 | tail -n 14` run was:

```text
      "Tests.ConservativeForcing"
    ]
  },
  "base_compatibility_checked": false,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.051s

OK
python3 experiments/check_work_queue.py
45 work items: ownership, contract registration and task cards consistent.
```

That compact rerun also exited `0`.  The module, conformance probe, axiom
audit, policy checks, queue check, hygiene scans, tree search, and substantive
negative mutation therefore all have the required results.
