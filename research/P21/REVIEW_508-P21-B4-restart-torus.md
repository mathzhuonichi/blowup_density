ACCEPT-WITH-NOTES

Exact one-line fixes required before merge:

1. In `formalization/NSFormalization/Section3/T11/H1Restart.lean:244`, replace
   `convert hd using 1 <;> ring` by `convert hd using 1 ; ring`; this removes the
   lane-local linter warning and makes direct module checking silent as required.
2. Remove the final blank line at `research/P21/axioms_b4t.lean:187`, so that
   `git diff --check origin/erenup/core...HEAD` no longer fails on this lane file.

## 1. What the lane claims

The worker claims one exact fixed-force periodic H¹ restart theorem, 22 supporting
theorems, no remaining B4-T³ mathematical gap, and a B5 handoff rather than a
contract or article-status change (`research/P21/REPORT_508.md:3`,
`research/P21/REPORT_508.md:8`, `research/P21/REPORT_508.md:25`,
`research/P21/REPORT_508.md:68`, `research/P21/REPORT_508.md:96`). Those claims are
mathematically and formally accurate.

The underlying revised proposition states maximal smooth existence and extension
from finite squared H² dissipation (`paper/revised/sections/02-preliminaries.tex:147`,
`paper/revised/sections/02-preliminaries.tex:149`,
`paper/revised/sections/02-preliminaries.tex:152`,
`paper/revised/sections/02-preliminaries.tex:154`). Its proof explicitly describes a
uniform positive restart time for the fixed force on `[0,S+1]`
(`paper/revised/sections/02-preliminaries.tex:178`,
`paper/revised/sections/02-preliminaries.tex:180`,
`paper/revised/sections/02-preliminaries.tex:181`). The paper does not separately
display the stronger H¹-ball API theorem, and the worker says so honestly
(`research/P21/REPORT_508.md:42`). The lane brief nevertheless asks for that retained
research target. Its exact contract-vocabulary statement is
`research/P21/Targets.lean:38` through `research/P21/Targets.lean:47`.

The new theorem is literally the requested local T10/T11 statement:
`formalization/NSFormalization/Section3/T11/H1Restart.lean:576` through
`formalization/NSFormalization/Section3/T11/H1Restart.lean:582`. In particular,
`K ≠ ⊤` precedes one `δ > 0`; that `δ` precedes both `t₀` and `a'`; the
datum ball is `periodicSobolevENorm 1`; `f ∈ forceClassT`; and
`PeriodicLocalRegularity` uses the same `δ`, datum, shifted force, and returned
solution. The distinct contract solution structure is transported in the consumer
probe without strengthening the theorem (`research/P21/probes/b4t_closes.lean:38`,
`research/P21/probes/b4t_closes.lean:47`,
`research/P21/probes/b4t_closes.lean:52`).

## 2. What is in Lean

### Statements and fidelity

There are exactly 23 exported theorems. Their actual signatures support every
grouped claim in the worker report:

- carrier/Parseval bridges are at
  `formalization/NSFormalization/Section3/T11/H1Restart.lean:27`, `:34`, `:49`,
  and `:76`;
- the three B0 energy equalities are at the same file's `:115`, `:125`, and
  `:133`;
- the bridge-free B2 theorem and time adapters are at `:142`, `:165`, `:172`,
  and `:180`;
- the smooth-force identities and differential inequality are at `:189`, `:209`,
  and `:247`;
- compact integral conversion and uniform running/endpoint estimates are at
  `:285`, `:307`, and `:372`;
- the H³ energy bound, shift-compatible extension, smooth-force maximal
  construction, strict lifespan lower bound, and final restart are at `:412`,
  `:445`, `:489`, `:520`, `:542`, and `:576`.

The ordinary energy retains the zero Fourier mode: `hasSum_lTwoSqT` sums over all
periodic frequencies (`H1Restart.lean:34`-`:46`). The H¹ identity is exactly
`L² + gradientSqT` (`H1Restart.lean:49`-`:73`); the H² identity is exactly
`L² + 2 gradientSqT + laplacianSqT` (`H1Restart.lean:76`-`:112`). Combining
these with B0's exact Bessel identities (`Section3/T11/H1Bridges.lean:69`-`:91`)
proves all three requested equalities, including
`periodicHessianEnergy = laplacianSqT` (`H1Restart.lean:133`-`:139`). This is the
periodic Parseval identity with the mean retained, not a mean-zero shortcut.

The inherited B2 theorem has exactly three spatial bridge premises
(`formalization/NSFormalization/Section3/T11/EnstrophyInequality.lean:723`-`:740`).
`enstrophy_differential_on_IccT'` discharges all three from smooth periodic slices
and leaves no bridge premise (`H1Restart.lean:142`-`:162`).

### Hypothesis honesty and force shifts

`forceClassT` is definitionally the set of `MemForceT` forces, with smoothness,
spatial periodicity, and compact positive-time support
(`formalization/NSFormalization/Section3/T10/PeriodicData.lean:239`-`:245`). The
lane does not falsely assert that a positive time shift remains in this class.
Instead:

- B0 supplies a finite fixed-force slice cap and shift-compatible
  smoothness/periodicity (`Section3/T11/H1Bridges.lean:105`-`:135`,
  `Section3/T11/H1Bridges.lean:158`-`:168`);
- the lane rebuilds the differentiated identity and enstrophy inequality with only
  concrete `ContDiff` and periodicity hypotheses (`H1Restart.lean:189`-`:244`,
  `H1Restart.lean:247`-`:282`);
- `periodicHThree_bound_smoothT` assumes an actual `SolvesBelowT` solution and a
  finite actual H² lintegral, not a placeholder proposition
  (`H1Restart.lean:445`-`:486`);
- `shifted_horizon_extensionT` obtains the proved H³ quantitative local input and
  passes the two nonnegative shifts through the finite L¹ force bounds before
  using the existing gluing theorem (`H1Restart.lean:489`-`:517`). The supplier is
  a proved theorem, `periodicQuantitativeLocalInputH3`
  (`formalization/NSFormalization/Section3/T11/ExistenceInputH3.lean:335`-`:341`),
  and the gluing conclusion is a genuine classical solution
  (`formalization/NSFormalization/Section3/T11/RestartBeyond.lean:231`-`:238`).
- `exists_maximal_smoothT` first constructs a local classical solution via Picard
  and then invokes maximal gluing from positive lifespan (`H1Restart.lean:520`-`:539`;
  `formalization/NSFormalization/Section3/T11/MildClassical.lean:1322`-`:1345`).

There is no circular use of `h1RestartT`, no named `Prop` input, and no assumed H¹
target in this chain. `h1RestartT` is used only as the final exported conclusion.

The finite-cap hypothesis is load-bearing rather than hidden behind
`⊤.toReal = 0`: `hK` is passed into the ODE construction
(`H1Restart.lean:318`-`:320`) and into `ENNReal.toReal_mono` for the initial
energy (`H1Restart.lean:336`-`:340`). Force-cap finiteness is explicitly used at
`H1Restart.lean:185`. The restart interval is nonempty because `S ≥ 0`, and the
returned interval is genuine because `δ > 0` (`H1Restart.lean:578`-`:582`).

### Uniformity, endpoint, and regularity

The ODE constants are selected before shift and datum: the barrier is invoked with
`K.toReal²` and `(forceL2CapT f S).toReal²`, then `D := min d 1`, before the
proof introduces `t₀` and `a` (`H1Restart.lean:318`-`:328`). The shifted force
cap is used only on the common interval `D ≤ 1` (`H1Restart.lean:346`-`:353`).

Endpoint passage uses B3's nonnegative lintegral theorem
(`formalization/NSFormalization/Section4/A04/EnstrophyBarrier.lean:124`-`:141`)
at `H1Restart.lean:398`-`:407`, then restricts from `Ico` to the exact `Ioo`
carrier at `H1Restart.lean:409`. This matches the definition of
`squaredHTwoIntegralT` (`formalization/NSFormalization/Section3/T11/LocalTheory.lean:58`-`:61`).

The regularity conclusion is not selected-family-only. For every classical
solution and every smooth force, `periodicLocalRegularity_of_classical'` fills
all three fields `sobolev_smooth`, `pressure_poisson`, and `projected`
(`formalization/NSFormalization/Section3/T11/ClassicalRegularity.lean:1139`-`:1145`).
The final theorem applies exactly this arbitrary-solution result to the shifted
force (`H1Restart.lean:587`-`:590`).

### Non-vacuity, axioms, and ownership

The existing non-vacuity example uses viscosity `1`, zero force, restart time
`1/2`, and the explicit nonzero constant datum `coordinateVector 0`; it proves
the returned initial velocity is nonzero (`research/P21/probes/b4t_closes.lean:10`-`:34`).

All 23 exports are listed and individually subjected both to `#print axioms` and
an exact cardinality/membership check for `[propext, Classical.choice, Quot.sound]`
(`research/P21/axioms_b4t.lean:4`-`:10`, repeated through
`research/P21/axioms_b4t.lean:180`-`:186`). The axiom gate passes.

The new proof module is registered as a proof entrypoint
(`formalization/blueprint/entrypoints.json:73`). The lane-owned range
`5e5914a4^..HEAD` contains no B0/B2/B3 module, contract, binding, registry, paper,
or blueprint-status edit. It contains only the new B4 module, its research files,
the authorized entrypoint edit, and generated audit/graph refreshes. Thus lane 508
did not modify the separately reviewed modules from lanes 503/505/506.

## 3. Gaps and findings

There is no B4-T³ mathematical gap. The remaining B5 work is accurately isolated:
the existing `restartBeyond` declaration begins at
`formalization/NSFormalization/Section3/T11/RestartBeyond.lean:408` and consumes
its named input only at the single call `restart H` at `:424`. The exact H¹ endpoint
target and supplier substitution are recorded at `research/P21/P6_SPLIT.md:213`-`:250`.
No contract, binding, registry, paper, or blueprint status is changed by this lane.

For the required whole-Section4 missing-lemma audit, the worker declares no B4
gap. I nevertheless searched the entire
`formalization/NSFormalization/Section4` tree for
`h1UniformEndpointT|h1RestartT|PeriodicQuantitativeLocalInputH1Sup|restartBeyond.*H1|HOne.*restart`;
the exact result was exit 1 with zero output. A companion Section3 search finds
only the new `h1RestartT`. Hence no unsearched "not in the tree" claim was accepted.

The required substantive reviewer mutation is
`research/P21/probes/rev508_mutation.lean:10`-`:48`. It changes the Sobolev-order
constant from `1` to `0`, widening the admissible datum ball from H¹ to L², while
trying the unchanged proof. This is not an argument-dropping mutation. Before
wrapping the expected error in `#guard_msgs`, Lean failed with:

```text
../research/P21/probes/rev508_mutation.lean:19:2: error: Type mismatch
  h1RestartT
has type
  ∀ (ν : ℝ),
    0 < ν →
      ∀ f ∈ forceClassT,
        ∀ (S : ℝ),
          0 ≤ S →
            ∀ (K : ℝ≥0∞),
              K ≠ ∞ →
                ∃ δ,
                  0 < δ ∧
                    ∀ t₀ ∈ Icc 0 S,
                      ∀ a' ∈ initialClassT,
                        periodicSobolevENorm 1 a' ≤ K → ∃ w, PeriodicLocalRegularity ν a' (timeShiftT t₀ f) δ w
but is expected to have type
  ∀ (ν : ℝ),
    0 < ν →
      ∀ f ∈ forceClassT,
        ∀ (S : ℝ),
          0 ≤ S →
            ∀ (K : ℝ≥0∞),
              K ≠ ∞ →
                ∃ δ,
                  0 < δ ∧
                    ∀ t₀ ∈ Icc 0 S,
                      ∀ a' ∈ initialClassT,
                        periodicSobolevENorm 0 a' ≤ K → ∃ w, PeriodicLocalRegularity ν a' (timeShiftT t₀ f) δ w
EXIT=1
```

The checked probe records the same exact message at `rev508_mutation.lean:12`-`:39`
and compiles with zero output.

Two non-mathematical findings prevent an unqualified ACCEPT:

1. The direct module gate is not zero-output. It reports one lane-local warning
   at `H1Restart.lean:244`; the exact one-line fix is stated at the top.
2. The worker report says `git diff --check` passed
   (`research/P21/REPORT_508.md:130`), but the required base comparison exits 2
   because `axioms_b4t.lean:187` is a new blank line at EOF. Remove that line.

The literal `origin/erenup/core...HEAD` comparison currently warns of two merge
bases (`6471f930...` and `4c5d9015...`) and reports 65 files from parallel/inherited
lanes, so it is not an ownership-safe lane delta. The explicit lane-owned commit
range above is the relevant confirmation that lane 508 did not touch B0/B2/B3.

No `sorry`, `admit`, axiom declaration, or `native_decide` occurs in the new module
or probes. There is no `maxHeartbeats` override. Citations opened above resolve to
the stated source text and declarations.

## 4. Commands and results

All Lean commands used `. scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`, and Lake only
from `verification/`. Long outputs below quote only exact leading/trailing excerpts,
within the 40+40-line raw-output limit.

### Module build and direct check

`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T11.H1Restart`
exited 0. Exact first/last excerpts (493 output lines):

```text
⚠ [8778/9254] Replayed NSFormalization.Source.FiniteHilbertBochner
warning: NSFormalization/Source/FiniteHilbertBochner.lean:24:19: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
...
⚠ [10674/10674] Replayed NSFormalization.Section3.T11.H1Restart
warning: NSFormalization/Section3/T11/H1Restart.lean:244:21: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
Build completed successfully (10674 jobs).
```

`cd verification && LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section3/T11/H1Restart.lean`
exited 0 but produced exactly:

```text
../formalization/NSFormalization/Section3/T11/H1Restart.lean:244:21: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
```

### Axioms and probes

`cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/P21/axioms_b4t.lean`
exited 0. The 64-line output contains all 23 exact checks; exact first/last excerpts:

```text
'NSFormalization.Section3.T11.periodicGradient_bridgeT' depends on axioms: [propext, Classical.choice, Quot.sound]
Contract NSFormalization.Section3.T11.periodicGradient_bridgeT: checked; standard logical axioms only
'NSFormalization.Section3.T11.hasSum_lTwoSqT' depends on axioms: [propext, Classical.choice, Quot.sound]
Contract NSFormalization.Section3.T11.hasSum_lTwoSqT: checked; standard logical axioms only
'NSFormalization.Section3.T11.periodicHOne_bridgeT' depends on axioms: [propext, Classical.choice, Quot.sound]
Contract NSFormalization.Section3.T11.periodicHOne_bridgeT: checked; standard logical axioms only
...
'NSFormalization.Section3.T11.exists_maximal_smoothT' depends on axioms: [propext, Classical.choice, Quot.sound]
Contract NSFormalization.Section3.T11.exists_maximal_smoothT: checked; standard logical axioms only
'NSFormalization.Section3.T11.uniform_periodicHOne_lifespanT' depends on axioms: [propext, Classical.choice, Quot.sound]
Contract NSFormalization.Section3.T11.uniform_periodicHOne_lifespanT: checked; standard logical axioms only
'NSFormalization.Section3.T11.h1RestartT' depends on axioms: [propext, Classical.choice, Quot.sound]
Contract NSFormalization.Section3.T11.h1RestartT: checked; standard logical axioms only
```

Both probe commands exited 0 with exactly zero output:

```text
cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/P21/probes/b4t_closes.lean
cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/P21/probes/rev508_mutation.lean
```

`cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/P21/Targets.lean`
also exited 0 with exactly zero output.

### Owner checks

`python3 experiments/check_formalization_plan.py --check` exited 0:

```text
Blueprint: 41 proof nodes, 27 article/guide mappings; 2271 source modules; local imports and package paths resolve.
Static packaging checks only; no Lean build or mathematical certification.
```

`python3 experiments/check_contracts.py --summary` exited 0:

```text
{
  "registered_contracts": 34,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
```

`make check` exited 0 with exactly:

```text
python3 experiments/check_formalization_plan.py --check
Blueprint: 41 proof nodes, 27 article/guide mappings; 2271 source modules; local imports and package paths resolve.
Static packaging checks only; no Lean build or mathematical certification.
python3 experiments/check_contracts.py --summary
{
  "registered_contracts": 34,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
python3 experiments/test_contract_policy.py
...........
----------------------------------------------------------------------
Ran 11 tests in 0.003s

OK
```

`LEAN_NUM_THREADS=6 make test` exited 0. Exact first/last excerpts (547 lines):

```text
lake -d verification test
⚠ [8778/9140] Replayed NSFormalization.Source.FiniteHilbertBochner
warning: NSFormalization/Source/FiniteHilbertBochner.lean:24:19: try 'simp' instead of 'simpa'
...
ℹ [11025/11027] Replayed Tests.PeriodicInsertion
info: Tests/PeriodicInsertion.lean:15:0: Contract BlowupDensity.Tests.checkedPeriodicInsertion: checked; standard logical axioms only
ℹ [11026/11027] Replayed Tests.TorusNonDensity
info: Tests/TorusNonDensity.lean:24:0: Contract BlowupDensity.Tests.checkedTorusNonDensity: checked; standard logical axioms only
ℹ [11027/11027] Replayed Tests.TorusMain
info: Tests/TorusMain.lean:21:0: Contract BlowupDensity.Tests.checkedTorusMain: checked; standard logical axioms only
```

`LEAN_NUM_THREADS=6 make test-mutations` exited 0. Exact first/last excerpts
(552 lines):

```text
python3 experiments/test_contract_mutations.py
⚠ [8778/9359] Replayed NSFormalization.Source.FiniteHilbertBochner
warning: NSFormalization/Source/FiniteHilbertBochner.lean:24:19: try 'simp' instead of 'simpa'
...
implementation_refactor: accepted
admitted_proof: rejected as required
extra_axiom: rejected as required
weakened_hypothesis: rejected as required
Mutation suite passed. This is an infrastructure check, not a PDE proof.
```

The article audit command
`python3 experiments/audit_article_axioms.py --build --output-dir tmp/rev508-article-audit --workers 2`
exited 0; its final exact line was:

```text
72 declarations; 27 article entries; 0 forbidden-axiom results
```

`make paper` exited 0; its exact final checks were:

```text
Source inventory: 18 works; missing full text: none. Chapter-only coverage is explicitly marked.
26 numbered article statements and their guide mappings checked.
27 article results mapped, including the numbered remark; proof declaration kinds and source line numbers verified.
86 article labels resolved.
16 bibliography entries resolved; 34 registry declarations found; guide code paths verified.
Both PDF build logs are clean. Scope: structural checks, not a new proof certification.
make[1]: Leaving directory '/data_8T/ping/blowup_density/.claude/worktrees/508-P21-B4-restart-torus/paper'
```

### Hygiene and branch ownership

Forbidden-token and heartbeat searches both produced zero lines. The lane-owned
diff command `git diff --name-status 5e5914a4^..HEAD` exited 0 with exactly:

```text
A	formalization/NSFormalization/Section3/T11/H1Restart.lean
M	formalization/blueprint/AXIOM_AUDIT.json
M	formalization/blueprint/DEPENDENCY_GRAPH.md
M	formalization/blueprint/entrypoints.json
A	research/P21/ATTEMPTS_B4T.md
M	research/P21/P6_SPLIT.md
A	research/P21/REPORT_508.md
A	research/P21/axioms_b4t.lean
A	research/P21/probes/b4t_closes.lean
```

The required base diff check currently produces exactly:

```text
warning: origin/erenup/core...HEAD: multiple merge bases, using 6471f930d0d9b919dc7e2e43e06949e8101404d5
research/P21/axioms_b4t.lean:187: new blank line at EOF.
```

and exits 2. This is the second exact one-line fix above.

---
**Lead ruling (2026-09-21 06:45Z):** merged with both hygiene notes applied in the review commit (`H1Restart.lean:244` `<;>` → `;` — the `unnecessarySeqFocus` linter fires only when `convert` leaves a single goal, so the edit is semantically neutral; trailing blank line in `axioms_b4t.lean` removed). The final full rebuild (lane 512) re-verifies the module.
