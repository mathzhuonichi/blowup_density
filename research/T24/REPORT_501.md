# Lane 501 — P5.5 assembly and both-branch registration

## 1. Statements

`multipleRegionsOmegaAPI` constructs all thirty fields of the bounded-domain
record from `RegionsOmegaData`. Its four P5b fields consume only the concrete
P5a components, support, placements, positive scales, time bounds, packet and
geometry. The two velocity sums are definitionally equal; no deduplication or
unit-lane source change was needed. `multipleRegionsOmegaStatement_holds`
introduces the raw packet clauses and prescribed Ω, T, N and balls, builds the
data, and supplies the constructed record. There is no solution/API premise.

`T04.multiple_regions_v2` registers the conjunction of the retained V1 torus
statement and the packet-indexed bounded box-or-regular-level domain statement.
The domain record and statement match `SpecOmega.lean` token-for-token after
substitution of registered vocabulary: `DomainPlacementData P.toPacketAPI`,
packet-indexed `Scaling3` fields, `Data.spatialGradient`, and the registered
boundary domain/solution classes. Norm definitions have whole-function `rfl`
guards; both thirty-field conversions have `rfl` round trips. Energy remains
≤ the original M² times the scale sum; dissipation remains = the original D²
times that sum. No-slip and separate blow-up in each ball are explicit.

The concrete probe constructs both canonical and registered inhabitants for
the unit box, one radius-1/4 ball at (1/2,1/2,1/2), ν=T=1 and the registered
packet. It reads off `region_blowup 0` and `no_slip` without assuming an API.

## 2. Files and commits

- `formalization/NSFormalization/Section3/T24/MultipleOmegaAssembly.lean`:
  constructor and raw existence theorem.
- `verification/Contracts/V2/MultipleRegions.lean`,
  `verification/Bindings/MultipleRegionsV2.lean`,
  `verification/Tests/MultipleRegionsV2.lean`: specification, raw projection
  bundle/conversions/proofs, checked conjunction and branch projections.
- `verification/contracts.json`: new V2 entry; V1 retained (30 total).
- `research/T24/probes/multiple_omega_nonvacuity.lean`, `axioms_p5c.lean`,
  `ATTEMPTS_P5C.md`: concrete witnesses, twelve-declaration audit, diagnostics.
- Blueprint graph, entrypoints, RESULT_MAP, CLOSURE_AUDIT, AXIOM_AUDIT and
  regenerated DEPENDENCY_GRAPH: M316_B Closed, dependencies M316/B314,
  Proposition 3.16 Closed; inventory 22 Closed / 5 Partial.
- Root/blueprint/verification READMEs, guide, reader-check expected coverage,
  and both rebuilt PDFs: consistent coverage and 30-interface count.

Closed-step commits: `324833a1` (assembly/probe), `187a430e` (V2 registration),
`ef7600ee` (blueprint/audit/documents). This report and the split status form
the final reporting commit.

## 3. Gaps and resolved diagnostics

No P5 mathematical, assembly, registration or validation gap remains. Scope is
the registered bounded box-or-regular-level domain class and the V1 torus
geometry. No unit-lane proof module was changed and no extra hypothesis added.

Resolved diagnostics:

- Probe: `Unknown identifier ...T13.fundamentalCube_compact.isBounded.subset`;
  use the proved `T18.isCompact_fundamentalCube`. `OfNat (Fin data.N) 0`
  required an explicit `Fin 1` witness at the canonical projection.
- Graph: `Current test roots differ from retained tests`; add the V2 test root.
  `Source changed: rerun the article axiom audit`; rerun the full real audit.
- First `make paper`: `check_reader_documents.py:61: AssertionError` because
  the expected Partial set still contained `prop:multiple`. Update that set
  and explicitly check Closed plus the V2 proof name; rerun passes.

The graph schema indexes `completion_from` on every node. Its old edges were
removed, retaining the required empty list, consistent with other Closed nodes.
The lane brief's pre-existing untracked copy was left untouched.

## 4. Commands and results

Source `. scripts/lean-env.sh`, use `LEAN_NUM_THREADS=6`, and run direct Lake
commands from `verification/`. Full logs are in ignored `tmp/lane501/`.

- `lake build NSFormalization.Section3.T24.MultipleOmegaAssembly`: PASS.
- `lake build Tests.MultipleRegionsV2`: PASS; standard logical axioms only.
- `lake env lean ../research/T24/probes/multiple_omega_nonvacuity.lean`: PASS,
  zero output, including canonical and registered blow-up/no-slip projections.
- `lake env lean ../research/T24/axioms_p5c.lean`: PASS; all twelve declarations
  print exactly `[propext, Classical.choice, Quot.sound]`.
- Token comparison against SpecOmega under the listed registered substitutions:
  PASS for all thirty fields and the domain existence statement.
- `python3 experiments/audit_article_axioms.py --build --output-dir
  tmp/article-audit-501 --workers 2`: PASS, 58 declarations / 27 article entries /
  zero forbidden-axiom results, empty prohibited-source-token list. Reviewed
  `report.json` copied to the tracked AXIOM_AUDIT.
- `python3 experiments/check_formalization_plan.py`: PASS after audit refresh;
  regenerated DEPENDENCY_GRAPH, 41 proof nodes, 27 mappings.
- `make check`: PASS, 30 contracts and 11 policy tests.
- `make test`: PASS, all current Lean acceptance interfaces.
- `make test-mutations`: PASS; refactor accepted, admitted proof, extra axiom
  and weakened hypothesis rejected.
- `make paper`: PASS; 26 numbered statements plus the numbered remark, all
  proof locations verified, both PDF logs clean.
- `git diff --check`: PASS; no prohibited proof tokens in new Lean modules.
