ACCEPT-WITH-NOTES

Fix the four lane-local `unnecessarySeqFocus` warnings so the required direct
Lean check has zero output: at
`formalization/NSFormalization/Section4/A04/EnstrophyInequality.lean:143`
replace the line by `(convert hh using 1; norm_num)`; at lines 249, 256, and
465 replace the respective line by `(convert h using 1; ring)`. These are
one-line proof-script cleanups; no statement or mathematical change is needed.

## 1. What the lane claims

The worker claims 16 named lemmas, culminating in the pointwise and
closed-interval inequalities with

`Y = (sobolevENorm 1 u).toReal^2`,
`Z = (sobolevENorm 2 u).toReal^2`, `c = 1`, and

`Cnu = (2*kappa*C0^(3/2))^4/(kappa*nu/2)^3/kappa^3 + (1+nu) + (1+2*kappa/nu)`,

where `kappa = (2*pi)^(-2)` and `C0 = A05.gradientL6Const`
(`research/P21/REPORT_504.md:9-34`). It explicitly says that its only B0 norm
inputs are the H1 identity, H2 upper bridge, and physical-gradient carrier
bridge (`research/P21/REPORT_504.md:58-74`); the lead specifically approved
these hypotheses.

The cited article text is accurate. Proposition 2.1 states existence of a
unique maximal smooth velocity and extension under finite squared-H2 integral
at `paper/revised/sections/02-preliminaries.tex:147-156`. The new module quotes
those lines while explicitly saying that B1 serves the separate H1 restart
obligation, not a displayed clause of that proposition
(`formalization/NSFormalization/Section4/A04/EnstrophyInequality.lean:3-16`).
The actual Route B target is recorded as
`Y' + c*nu*Z ≤ Cnu*(1+Y)^3 + Cnu*||f||_2^2`, with lower-order terms retained,
at `research/P21/ASSESSMENT.md:165-174`; B1 is exactly the general, no-smallness
unit at `research/P21/ASSESSMENT.md:176-183`.

## 2. What is in Lean

All 16 names in the report exist, and
`research/P21/probes/b1_closes.lean:4-19` checks each one. Their statements agree
with the report:

- The unweighted identity at
  `formalization/NSFormalization/Section4/A04/EnstrophyInequality.lean:28-39`
  adds the ordinary identity
  `C01.energyIdentity_l2Sq` (`formalization/NSFormalization/Section4/C01/EnergySpec.lean:48-63`)
  to the raw gradient identity
  `C01.enstrophyIdentity_gradientSq`
  (`formalization/NSFormalization/Section4/C01/EnstrophyIdentityRaw.lean:161-191`).
  Thus the signs and all four low-order/dissipative/force contributions are as
  claimed. The weighted form is at
  `formalization/NSFormalization/Section4/A04/EnstrophyInequality.lean:258-272`.

- The 6-3-2 Holder inequality is at
  `formalization/NSFormalization/Section4/A04/EnstrophyInequality.lean:42-117`,
  the L3 interpolation at lines 120-143, and the support-free velocity L6
  estimate at lines 145-170. The other L6 input is the already proved
  `A05.eLpNorm_gradTensor_six_le`, with its explicit universal constant, at
  `formalization/NSFormalization/Section4/A05/GradientL6.lean:48-66`.
  Their assembly at
  `formalization/NSFormalization/Section4/A04/EnstrophyInequality.lean:172-198`
  has exactly `C0^(3/2) G^(3/2) L^(3/2)`. The registered H1/H2 version and its
  two displayed bridge hypotheses are at lines 449-465.

- Quartic Young, the 3/4-power absorption, and two-factor force absorption are
  at `formalization/NSFormalization/Section4/A04/EnstrophyInequality.lean:200-256`.
  The scalar assembly at lines 287-341 keeps `U`, uses
  `Y = U + kappa*G` and
  `Z ≤ U + 2*kappa*G + kappa^2*L`, and yields the displayed cubic and force
  coefficients. There is no critical-smallness hypothesis.

- `enstrophy_differential_of_norm_bridges` has only the general positive
  viscosity/weight assumptions and the three named norm inputs
  (`formalization/NSFormalization/Section4/A04/EnstrophyInequality.lean:347-364`).
  The fixed-convention theorem gives `c = 1` and exactly the reported `Cnu` at
  lines 416-447. The interval wrapper at lines 469-491 applies it at every
  member of `Icc r s` under `0 < r` and `s < T`. Although the wrapper also
  permits an empty `Icc`, it is not made true only that way: the pointwise
  theorem is independent of that wrapper, and the successful review probe
  instantiates the wrapper for the zero solution on the nonempty interval
  `[1,2]` inside `(0,3)`
  (`research/P21/probes/rev504_nonvacuity.lean:52-73`). The same probe proves
  the three zero norm bridges directly at lines 10-50, so no `top.toReal = 0`
  collapse is used.

- The classical carrier and force predicate are the canonical local restatement
  in `formalization/NSFormalization/Section4/A02/SolutionClass.lean:99-138`,
  matching the contract definitions at
  `verification/Contracts/V1/Data.lean:544-550` and lines 624-648. Omitting an
  explicit `a in initialClassR` assumption is a genuine strengthening once
  `w : ClassicalSolutionR nu a f T` is supplied; no named nonlinear or
  differential hypothesis is hidden.

All 16 declarations print exactly `[propext, Classical.choice, Quot.sound]`
(`research/P21/axioms_b1.lean:4-35`). The new module is registered at
`formalization/blueprint/entrypoints.json:40`. The fresh audit has the same
source hash and contents as the tracked audit.

Hygiene is otherwise clean. There is no `sorry`, `admit`, `axiom`,
`native_decide`, or `maxHeartbeats` in the new proof/probe/axiom files. Against
`origin/erenup/core`, the only proof module is the newly added
`EnstrophyInequality.lean`; no pre-existing Lean module was edited. The other
tracked changes are the required entrypoint/audit records and P21 research
records.

## 3. Gaps and negative checks

The B0 hypotheses are approved interfaces, not review gaps. They occur exactly
as reported at
`formalization/NSFormalization/Section4/A04/EnstrophyInequality.lean:351-359`
and, in the fixed theorem, at lines 419-427.

The report honestly leaves B3-B5 rather than claiming that every related tool
is absent (`research/P21/REPORT_504.md:82-86`). A whole-tree `grep -rn` found:

- generic linear Gronwall at
  `formalization/NSFormalization/Section4/A04/Gronwall.lean:166-214`;
- endpoint/maximality plumbing at
  `formalization/NSFormalization/Section4/A04/Continuation.lean:41-81` and
  `formalization/NSFormalization/Section4/A04/Continuation.lean:195-208`;
- an H7 fixed-force restart at
  `formalization/NSFormalization/Section4/A04/RestartWiring.lean:70-84`;
- maximal-endpoint H2 bounds that still assume critical smallness at
  `formalization/NSFormalization/Section4/R43/MaximalEndpoint.lean:15-53` and
  `formalization/NSFormalization/Section4/R44/Endpoint.lean:234-267`.

The exact general `(1+Y)^3` search hits only the new B1 module
(`formalization/NSFormalization/Section4/A04/EnstrophyInequality.lean:297,325-326`).
Thus the missing work is the nonlinear ODE barrier/integrated-dissipation
assembly and its use in the already available endpoint/restart plumbing; the
report does not incorrectly label the reusable plumbing as absent.

The substantive mutation is
`research/P21/probes/rev504_mutation.lean:8-28`: only the main RHS power is
weakened from 3 to 2. It fails for the expected reason, displaying the proved
cubic type versus the requested quadratic type:

```text
../research/P21/probes/rev504_mutation.lean:28:2: error: Type mismatch
  enstrophy_differential w hf hnu hOne ht hTwo hGradient
has type
  have kappa := 1 / (2 * Real.pi) ^ 2;
  have Cnu := (2 * kappa * A05.gradientL6Const ^ (3 / 2)) ^ 4 / (kappa * nu / 2) ^ 3 / kappa ^ 3 + (1 + nu) + (1 + 2 * kappa / nu);
  deriv (fun s => (D01.sobolevENorm 1 (slice w.velocity s)).toReal ^ 2) t +
      nu * (D01.sobolevENorm 2 (slice w.velocity t)).toReal ^ 2 ≤
    Cnu * (1 + (D01.sobolevENorm 1 (slice w.velocity t)).toReal ^ 2) ^ 3 + Cnu * l2Sq (slice f t)
but is expected to have type
  let kappa := 1 / (2 * Real.pi) ^ 2;
  let Cnu :=
    (2 * kappa * A05.gradientL6Const ^ (3 / 2)) ^ 4 / (kappa * nu / 2) ^ 3 / kappa ^ 3 + (1 + nu) +
      (1 + 2 * kappa / nu);
  deriv (fun q => (D01.sobolevENorm 1 (slice w.velocity q)).toReal ^ 2) t +
      nu * (D01.sobolevENorm 2 (slice w.velocity t)).toReal ^ 2 ≤
    Cnu * (1 + (D01.sobolevENorm 1 (slice w.velocity t)).toReal ^ 2) ^ 2 + Cnu * l2Sq (slice f t)
```

1. **NOTE, build hygiene:** the zero-output gate is not clean: direct Lean emits
   four lane-local linter warnings at source lines 143, 249, 256, and 465. The
   exact one-line fixes are stated immediately below the verdict. This is
   non-mathematical and does not justify rejection.

## 4. Commands and results

All Lean/Lake commands used `. scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`, and
Lake only from `verification/`.

1. `lake build NSFormalization.Section4.A04.EnstrophyInequality` — exit 0.
   The output is long because Lake replayed upstream warnings; first and last
   relevant lines (middle omitted) were:

```text
warning: NSFormalization/Source/FiniteHilbertBochner.lean:24:19: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
warning: NSFormalization/Source/FiniteHilbertBochner.lean:23:37: This simp argument is unused:
  PiLp.single_apply

Hint: Omit it from the simp argument list.
  [apply] simp [h]
[... middle omitted ...]
warning: NSFormalization/Section4/A04/EnstrophyInequality.lean:465:20: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
Build completed successfully (10325 jobs).
```

2. `lake env lean ../formalization/NSFormalization/Section4/A04/EnstrophyInequality.lean`
   — exit 0, but not the required zero output:

```text
../formalization/NSFormalization/Section4/A04/EnstrophyInequality.lean:143:21: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
../formalization/NSFormalization/Section4/A04/EnstrophyInequality.lean:249:20: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
../formalization/NSFormalization/Section4/A04/EnstrophyInequality.lean:256:20: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
../formalization/NSFormalization/Section4/A04/EnstrophyInequality.lean:465:20: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
```

3. `lake env lean ../research/P21/probes/b1_closes.lean` — exit 0; it printed
   the 16 exact signatures checked at `research/P21/probes/b1_closes.lean:4-19`.
   `lake env lean ../research/P21/probes/rev504_nonvacuity.lean` — exit 0 and
   zero output. The deliberately failing `rev504_mutation.lean` output is quoted
   in part 3.

4. `lake env lean ../research/P21/axioms_b1.lean` — exit 0. First and last
   portions (all intervening declarations had the same exact three-axiom set):

```text
'NSFormalization.Section4.A04.inhomogeneousEnergyIdentity' depends on axioms: [propext, Classical.choice, Quot.sound]
Contract NSFormalization.Section4.A04.inhomogeneousEnergyIdentity: checked; standard logical axioms only
'NSFormalization.Section4.A04.lintegral_convection_holder_632' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
Contract NSFormalization.Section4.A04.lintegral_convection_holder_632: checked; standard logical axioms only
'NSFormalization.Section4.A04.eLpNorm_three_interpolation' depends on axioms: [propext, Classical.choice, Quot.sound]
Contract NSFormalization.Section4.A04.eLpNorm_three_interpolation: checked; standard logical axioms only
[... middle omitted ...]
'NSFormalization.Section4.A04.enstrophy_differential' depends on axioms: [propext, Classical.choice, Quot.sound]
Contract NSFormalization.Section4.A04.enstrophy_differential: checked; standard logical axioms only
'NSFormalization.Section4.A04.convection_sobolev' depends on axioms: [propext, Classical.choice, Quot.sound]
Contract NSFormalization.Section4.A04.convection_sobolev: checked; standard logical axioms only
'NSFormalization.Section4.A04.enstrophy_differential_on_Icc' depends on axioms: [propext, Classical.choice, Quot.sound]
Contract NSFormalization.Section4.A04.enstrophy_differential_on_Icc: checked; standard logical axioms only
```

5. `make check` — exit 0, exact output:

```text
python3 experiments/check_formalization_plan.py --check
Blueprint: 41 proof nodes, 27 article/guide mappings; 2240 source modules; local imports and package paths resolve.
Static packaging checks only; no Lean build or mathematical certification.
python3 experiments/check_contracts.py --summary
{
  "registered_contracts": 29,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
python3 experiments/test_contract_policy.py
...........
----------------------------------------------------------------------
Ran 11 tests in 0.004s

OK
```

6. Fresh article audit:
   `python3 experiments/audit_article_axioms.py --build --output-dir tmp/article-audit-review504 --workers 2`
   — exit 0, exact output:

```text
Bindings.CompletedDensity: 8 declarations checked
NSFormalization.Section3.T21.MainAssembly: 33 declarations checked
NavierStokes.ComparatorR3Theorem: 2 declarations checked
Bindings.BoundaryInsertionV2: 4 declarations checked
NSFormalization.Source.PacketBreakdown: 1 declarations checked
Bindings.LocalTheoryV2: 1 declarations checked
Bindings.TorusLocalTheory: 1 declarations checked
Bindings.AffineVariation: 1 declarations checked
NSFormalization.Section3.T24.MultipleAssembly: 1 declarations checked
NSFormalization.Section3.T24.ConservativeAssembly: 1 declarations checked
NSFormalization.Section4.R43.Universal: 1 declarations checked
Bindings.ForceClasses: 1 declarations checked
Bindings.GridObservations: 1 declarations checked
56 declarations; 27 article entries; 0 forbidden-axiom results
```

`cmp -s formalization/blueprint/AXIOM_AUDIT.json tmp/article-audit-review504/report.json`
returned exit 0.

7. Although `verification/` was not touched, both optional gates were rerun.
   `make test` exited 0. First/last excerpt:

```text
lake -d verification test
warning: NSFormalization/Source/FiniteHilbertBochner.lean:24:19: try 'simp' instead of 'simpa'
[... upstream replay warnings omitted ...]
info: Tests.PeriodicInsertion.lean:15:0: Contract BlowupDensity.Tests.checkedPeriodicInsertion: checked; standard logical axioms only
info: Tests.TorusNonDensity.lean:24:0: Contract BlowupDensity.Tests.checkedTorusNonDensity: checked; standard logical axioms only
info: Tests.TorusMain.lean:21:0: Contract BlowupDensity.Tests.checkedTorusMain: checked; standard logical axioms only
```

`make test-mutations` exited 0; its final exact output was:

```text
implementation_refactor: accepted
admitted_proof: rejected as required
extra_axiom: rejected as required
weakened_hypothesis: rejected as required
Mutation suite passed. This is an infrastructure check, not a PDE proof.
```

8. `make paper` — exit 0; final exact output:

```text
python3 ../experiments/check_reader_documents.py
Source inventory: 18 works; missing full text: none. Chapter-only coverage is explicitly marked.
26 numbered article statements and their guide mappings checked.
27 article results mapped, including the numbered remark; proof declaration kinds and source line numbers verified.
86 article labels resolved.
16 bibliography entries resolved; 29 registry declarations found; guide code paths verified.
Both PDF build logs are clean. Scope: structural checks, not a new proof certification.
make[1]: Leaving directory '/data_8T/ping/blowup_density/.claude/worktrees/504-P21-B1-enstrophy-r3/paper'
```

9. Hygiene and branch scope:

```text
$ grep -nE '\b(sorry|admit|axiom|native_decide)\b|set_option[[:space:]]+maxHeartbeats' <new Lean files>
[no output]
$ git diff --name-status origin/erenup/core...HEAD
A formalization/NSFormalization/Section4/A04/EnstrophyInequality.lean
M formalization/blueprint/AXIOM_AUDIT.json
M formalization/blueprint/entrypoints.json
A research/P21/ATTEMPTS_B1.md
A research/P21/P6_SPLIT.md
A research/P21/REPORT_504.md
A research/P21/axioms_b1.lean
A research/P21/probes/b1_closes.lean
$ git diff --check origin/erenup/core...HEAD
[no output]
```

Required fixes: exactly the four one-line semicolon rewrites listed immediately
below the verdict; then rerun the direct Lean command and confirm zero output.

---
**Lead ruling (2026-09-21 05:05Z):** merged as-is. The four notes are `unnecessarySeqFocus` linter style warnings (`<;>` → `;`) at lines 143/249/256/465 with no mathematical or axiom content; lane 507 (B4) already builds on this module, so the cosmetic edits are deferred to the B5 registration lane (510) checklist, to be applied in one pass together with the other Route B modules.
