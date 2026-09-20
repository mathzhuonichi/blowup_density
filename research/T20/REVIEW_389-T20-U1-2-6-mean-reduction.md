ACCEPT

## 1. What the lane claims

The worker report claims that `reductionRegular`, `meanBound`, and
`meanFreeEquation` were proved with the canonical field statements, without a
named `Prop` input or a T12 critical embedding, and that U3/U4/U5 remain out of
scope (`research/T20/REPORT_389.md:1-18`, `:20-43`).  The stated routes are the
T11 mean formula/zero-mean API, the zero Fourier mode estimate and infimum for
the mean bound, and T11 `mean_derivative` plus transport-slice algebra for the
mean-free equation (`research/T20/REPORT_389.md:5-18`).

The mathematical source agrees: the paper defines `m`, `v`, and `h` at
`paper/sections/03-torus.tex:395-401`, gives `m' = \overline g` and the bound
at `paper/sections/03-torus.tex:402-406`, and gives the untranslated equation
with the retained `(m\cdot\nabla)v` term at
`paper/sections/03-torus.tex:407-410`.  The later regularity quantities cited
by the split are the `y,z,b` definitions at
`paper/sections/03-torus.tex:413-418` and the `H^1`/Laplacian/force finiteness
discussion at `paper/sections/03-torus.tex:467-488`.

## 2. What is in Lean

The three declarations are exact copies of the canonical fields, not aliases:

- `reductionRegular` has the same binders, `Ico` domain, local `v/h` lets, and
  all eleven conjuncts as `CriticalRegularityTAPI.reductionRegular`
  (`formalization/NSFormalization/Section3/T20/MeanReduction.lean:15-29` vs
  `formalization/NSFormalization/Section3/T20/CriticalRegularity.lean:209-223`).
  Its proof uses the T11 mean formula and transformed zero-mean field
  (`formalization/NSFormalization/Section3/T20/MeanReduction.lean:47-84`), then
  the smooth-periodic and finite-norm bridges
  (`formalization/NSFormalization/Section3/T20/MeanReduction.lean:85-115`).
  The cited bridges are genuine tree lemmas:
  `periodicHomogeneousENorm_lt_top` is at
  `formalization/NSFormalization/Section3/T13/TorusIdentity.lean:1089-1096`,
  while smooth torus-lift and gradient `MemLp` results are at
  `formalization/NSFormalization/Section3/T10/ForcePaths.lean:18-23` and
  `:199-204`.

- `meanBound` is byte-for-byte the canonical two-conjunct statement
  (`formalization/NSFormalization/Section3/T20/MeanReduction.lean:117-120`;
  canonical `formalization/NSFormalization/Section3/T20/CriticalRegularity.lean:225-228`).
  The proof explicitly proves the zero Fourier coefficient estimate
  (`formalization/NSFormalization/Section3/T20/MeanReduction.lean:124-138`),
  the interval integral bound (`formalization/NSFormalization/Section3/T20/MeanReduction.lean:140-156`),
  and the admissible-path infimum bound
  (`formalization/NSFormalization/Section3/T20/MeanReduction.lean:157-174`).
  No extra positivity, finiteness, or solution hypothesis is introduced.

- `meanFreeEquation` has exactly the canonical interior interval, quantifier
  order, signs, pressure term, and retained constant transport
  (`formalization/NSFormalization/Section3/T20/MeanReduction.lean:175-185`;
  canonical `formalization/NSFormalization/Section3/T20/CriticalRegularity.lean:236-246`).
  The proof derives the data-defined mean derivative from T11
  `mean_derivative` (`formalization/NSFormalization/Section3/T20/MeanReduction.lean:194-203`),
  uses the transport slice identities
  (`formalization/NSFormalization/Section3/T20/MeanReduction.lean:204-246`),
  and subtracts `forceMeanT` from the original momentum equation
  (`formalization/NSFormalization/Section3/T20/MeanReduction.lean:247-262`).
  T11's source declarations match the claimed inputs at
  `formalization/NSFormalization/Section3/T11/Assembly.lean:404-417` and the
  concrete proofs at
  `formalization/NSFormalization/Section3/T11/MeanIdentity.lean:137-171`.

The exact target-shape probe closes all three by `exact` (`research/T20/probes/mean_reduction_closes.lean:23-57`).  It also gives a nonzero constant mode `coordinateVector 0`, proves it nonzero, and supplies an inhabited zero force class and periodic datum (`research/T20/probes/mean_reduction_closes.lean:61-74`).  Thus the report does not rely only on syntactic zero fields.  `ClassicalSolutionT` itself carries `0 < T` (`research/T20/Spec.lean:94-103`), so the interior hypotheses are not made vacuous by an unconstrained horizon.  All theorem binders are used in the proofs; there is no `⊤.toReal = 0` or other junk conclusion.

## 3. Gaps and hygiene

The report's U3/U4/U5 gap statement is consistent with the split: those fields
are separately specified at `research/T20/T20_SPLIT.md:83-101`, and the status
entry explicitly leaves them open at `research/T20/T20_SPLIT.md:262-276`.  A whole-Section4 search found
no `bIntegral`, `constantTransportSkew`, or
`constantTransportCommutesLambda` declaration.  `velocityCriticalL3` does
exist in the separate whole-space A05 tree
(`formalization/NSFormalization/Section4/A05/CriticalL3.lean:390-397`), so the
report's remaining dependency is correctly understood as the unproved T12
torus field, not as a claim that no repository lemma of that name exists.
`gradientLambdaCriticalL3` has no Section4 declaration; `gradientLSix` appears
only in explanatory text (`formalization/NSFormalization/Section4/A05/HessianLaplacian.lean:14`).

`git diff --name-only origin/erenup/integration-section3...HEAD` shows only the
new `MeanReduction.lean`, the research/probe/report files, and the permitted
`T20_SPLIT.md` status edit; no existing Lean module and no `verification/` file
was modified.  The module has no `set_option maxHeartbeats`, no anonymous
instances, and no forbidden declaration.  A targeted scan of the module and
exact-target probe for `sorry|admit|axiom|native_decide` returned no matches
(exit 1 means empty result); the `#print axioms` audit file's literal command
is not an axiom declaration.

## 4. Commands and results

All Lean commands were run after `. scripts/lean-env.sh`, from `verification/`,
with `LEAN_NUM_THREADS=6`:

```text
LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T20.MeanReduction
Build completed successfully (10597 jobs).

LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section3/T20/MeanReduction.lean
(no output; exit 0)

LEAN_NUM_THREADS=6 lake env lean ../research/T20/probes/mean_reduction_closes.lean
(no output; exit 0)

LEAN_NUM_THREADS=6 lake env lean ../research/T20/axioms_u1_2_6.lean
'NSFormalization.Section3.T20.reductionRegular' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T20.meanBound' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T20.meanFreeEquation' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The build also replayed pre-existing dependency linter warnings; none came
from `MeanReduction.lean` itself.

`LEAN_NUM_THREADS=6 make check` exited 0.  Its exact head reported
`missing_copied_imports: []`, `citation_interfaces_reachable: []`,
`tracked_cache_free: true`, `source_hashes_match: false`, and the repository's
pre-existing copied-source admission count of 11; its tail reported the 13
contract-policy tests `OK` and
`45 work items: ownership, contract registration and task cards consistent.`
The admission token named by that architecture scan is the pre-existing
`NSFormalization.Paper1.BoundaryCorollary` copied-source entry at
`formalization/NSFormalization/Paper1/BoundaryCorollary.lean:90`, not this
lane's module.

The full wrapper also passed:

```text
BASE_REF=origin/erenup/integration-section3 scripts/gates.sh NSFormalization.Section3.T20.MeanReduction
script_exit=0
extra_axiom: rejected as required
weakened_hypothesis: rejected as required
Mutation suite passed. This is an infrastructure check, not a PDE proof.
"base_compatibility_checked": true,
== gates OK
```

The direct `python3 experiments/check_contracts.py --base-ref
origin/erenup/integration-section3` exited 0 and ended with
`"base_compatibility_checked": true`.

The reviewer-only substantive negative probe flips the sign of the constant
transport term (`research/T20/probes/rev389_negative.lean:14-27`).  It fails at
the `exact meanFreeEquation` line with the expected Lean type mismatch: the
theorem supplies `+ constantTransportT ...`, while the mutated goal expects
`- constantTransportT ...`; the command printed
`../research/T20/probes/rev389_negative.lean:27:2: error: Type mismatch`.
This is a real statement mutation, not argument deletion.

Verdict: ACCEPT
Fixes: none.
