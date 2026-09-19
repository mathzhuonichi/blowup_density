ACCEPT

## 1. What the lane claims

`research/T15/REPORT_450.md:5-39` claims two requested field theorems and two
smooth-periodization helpers in namespace `NSFormalization.Section3.T15`.
The report's displayed signatures at `REPORT_450.md:11-31` agree exactly with
the declarations at
`formalization/NSFormalization/Section3/T15/SobolevPath.lean:57-88` and
`:91-116`: same raw smoothness/support hypotheses, same admissible-scale
interval, same quantifier order, same integer Sobolev order, same half-open
solution slab, and the same explicit periodized velocity and normalized
pressure.

The target fields themselves are
`formalization/NSFormalization/Section3/T10/PeriodicData.lean:287-293`.
After substituting
`velocity := periodizedScaledVelocity u place.x₀ place.T ε` and
`pressure := normalizedScaledPressure p place.x₀ place.T ε`, the two
lane theorems are those field types, not approximations or stronger premises.
The definitions of the substituted fields are fixed at
`formalization/NSFormalization/Section3/T15/Bridges.lean:64-72,81-102`.

Paper fidelity is correct.  I opened `paper/sections/03-torus.tex:101-123`:
it fixes one compact placement, the scale conditions, the zero-past rescaling,
single-copy periodization, and spatially constant pressure normalization.
The classical-solution regularity being filled is described at
`paper/sections/02-preliminaries.tex:28-36,75-115`.  The canonical placement
record faithfully carries `T>0`, `ε₀>0`, compact support geometry, and the one
fixed scale interval at
`formalization/NSFormalization/Section3/T15/Scaling.lean:102-190`.

The cited proof route is also the actual route.  Smooth periodic slices have
data at every real order by
`formalization/NSFormalization/Section3/T11/CriterionBridge.lean:27-54`, and a
selected integer-order datum path is continuous on the same `Ico` slab by
`formalization/NSFormalization/Section3/T11/Maximal.lean:151-173`.  The lane
uses these at `SobolevPath.lean:70-88`.  This matches the established inserted
solution pattern at
`formalization/NSFormalization/Section3/T18/Lifespan.lean:111-144`.
For pressure, the cited continuous-vector Haar `MemLp` result is exactly
`formalization/NSFormalization/Section3/T10/ForcePaths.lean:18-23`, used at
`SobolevPath.lean:109-116`.

## 2. What is in Lean

There are exactly four declarations, as claimed:

- `contDiffOn_periodize_of_slice_support`
  (`SobolevPath.lean:16-38`) replaces a field by zero outside `t<T`, obtains a
  uniform spatial support bound, applies the vendor's locally finite
  periodization theorem, and transfers equality back only on the open slab.
- `periodizedVelocity_contDiffOn` (`SobolevPath.lean:41-54`) supplies that
  helper with the dilated zero-past velocity and the placement support lemma.
- `periodized_sobolev` (`SobolevPath.lean:57-88`) constructs data for every
  `m : ℕ` and proves `ContinuousOn` on exactly `Ico 0 place.T`.
- `periodized_pressure_gradient` (`SobolevPath.lean:91-116`) proves slice
  smoothness after subtracting the spatially constant pressure mean, then
  obtains Haar-`L²` membership of its gradient.

No premise is silently unused or vacuous.  The velocity theorem consumes
`hext`, `hK`, `hu`, and the placement fields at `SobolevPath.lean:49-54,70-88`;
the pressure theorem consumes its corresponding premises at `:101-116`.
`PlacementData.time_pos` and `.eps_pos` make both quantified intervals
inhabited (`Scaling.lean:108-115,165-173`), and `IsPeriodicDatum` contains
periodicity, genuine Haar integrability, and exact Fourier coefficients
(`PeriodicData.lean:104-114`).  There is no `⊤.toReal = 0` or totalized-norm
escape in either statement.

The worker's concrete probe builds `T=1`, `ε₀=1/2` placement data at
`research/T15/probes/sobolev_path_closes.lean:148-171`, instantiates both
field theorems at `ε=1/2` at `:196-212`, and proves the source velocity and
pressure genuinely nonzero at `:214-229`.  The reviewer non-vacuity probe
`research/T15/probes/rev450_nonvacuity.lean:15-28` additionally extracts an
actual datum at the inhabited time `t=0`, for every order and an admissible
scale; it compiles with zero output.

Hygiene passes.  Relative to
`origin/erenup/integration-section3...HEAD`, the only Lean implementation file
is the newly added `SobolevPath.lean`; the only modified pre-existing file is
the permitted research status record `research/T15/T15_SPLIT.md`.  There is no
`sorry`, `admit`, axiom declaration, `native_decide`, or `maxHeartbeats`
override in the module, positive probe, or axiom audit.  `git diff --check` is
clean.  The declarations' comments make no incorrect paper/tree citation.
No file under `verification/` changed, so the brief's conditional
`scripts/gates.sh` and base-aware `check_contracts.py` gates do not apply.
A merge-tree check against the current integration tip also completed without
a conflict.

## 3. Gaps

No mathematical, statement, build, citation, or hygiene gap remains.  The
worker report declares no "not in the tree" gap, so there is no missing-lemma
claim requiring a Section4-wide grep.

The required substantive negative test is
`research/T15/probes/rev450_widened_horizon.lean:19-30`.  It keeps every
hypothesis and argument but widens the main Sobolev conclusion from `[0,T)` to
`[0,T+1)`.  This matters mathematically: the input extension is assumed smooth
only for source time `<1`, corresponding to physical time `<T`.  Lean exits 1
with the expected interval mismatch:

```text
../research/T15/probes/rev450_widened_horizon.lean:30:2: error: Type mismatch
  periodized_sobolev hext hK hu place
has type
  ∀ ε ∈ Ioc 0 place.ε₀,
    ∀ (m : ℕ),
      ∃ G,
        ContinuousOn G (Ico 0 place.T) ∧
          ∀ t ∈ Ico 0 place.T,
            IsPeriodicDatum (↑m) (fun x => periodizedScaledVelocity u place.x₀ place.T ε (t, x)) (G t)
but is expected to have type
  ∀ ε ∈ Ioc 0 place.ε₀,
    ∀ (m : ℕ),
      ∃ G,
        ContinuousOn G (Ico 0 (place.T + 1)) ∧
          ∀ t ∈ Ico 0 (place.T + 1),
            IsPeriodicDatum (↑m) (fun x => periodizedScaledVelocity u place.x₀ place.T ε (t, x)) (G t)
```

This is a statement mutation, not an argument-deletion test.

## 4. Commands and results

All Lean commands used the sourced repository environment, ran from
`verification/`, set `LEAN_NUM_THREADS=6`, and were invoked one at a time.

`lake build NSFormalization.Section3.T15.SobolevPath` exited 0.  The full raw
transcript had 223 lines / 13,504 bytes and SHA-256
`99ee3b9cce0239f1d40aaf939a2948b2b06cece0515bcdfd82d2cddf065edcbd`.
It contains only replayed diagnostics from pre-existing dependencies; no line
names `SobolevPath.lean`.  Its exact final line is:

```text
Build completed successfully (10009 jobs).
```

Direct module and positive-probe checks both exited 0 with exactly zero output:

```text
$ lake env lean ../formalization/NSFormalization/Section3/T15/SobolevPath.lean
$ lake env lean ../research/T15/probes/sobolev_path_closes.lean
```

The axiom audit exited 0 with this exact output:

```text
'NSFormalization.Section3.T15.contDiffOn_periodize_of_slice_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T15.periodizedVelocity_contDiffOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T15.periodized_sobolev' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T15.periodized_pressure_gradient' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`lake env lean ../research/T15/probes/rev450_nonvacuity.lean` exited 0 with
exactly zero output.  The widened-horizon command exited 1 with the exact
diagnostic pasted in part 3.

`make check` exited 0.  Its repository-wide architecture JSON is large; the
captured raw transcript had 52,503 lines / 2,170,111 bytes and SHA-256
`e7f857a411d4777dd5de234d63e3c736530705fe4b89a87bca751bab0d3cbb31`.
Its exact final output was:

```text
  "base_compatibility_checked": false,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.046s

OK
python3 experiments/check_work_queue.py
45 work items: ownership, contract registration and task cards consistent.
```

The exact hygiene/diff output was:

```text
NO FORBIDDEN DECLARATION TOKENS
NO maxHeartbeats OVERRIDES
NO verification/ CHANGES
A formalization/NSFormalization/Section3/T15/SobolevPath.lean
A research/T15/ATTEMPTS_U9.md
A research/T15/REPORT_450.md
M research/T15/T15_SPLIT.md
A research/T15/axioms_u9.lean
A research/T15/probes/sobolev_path_closes.lean
git diff --check: CLEAN
```

The conditional verification gates were not run because the displayed diff
contains no `verification/` path.
