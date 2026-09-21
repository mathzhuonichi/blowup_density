# Lane 493 — P2 / C35_FULL

Status: **Closed**. Lemma 3.5 is exported for the article reference and geometry,
with all 45 correction fields and every displayed estimate retained.

## 1. Statements

`NSFormalization.Section3.T17.correctionStatementArticle_holds` proves the new
`correctionStatementArticle`. Its inputs are positive viscosity, a classical
periodic solution on the horizon `place.T + δ`, positive margin, admissible
initial datum/force, the building-block placement, the Lemma 3.4 ball
(`0 < r`, `r < 1/2`, inclusion in the placement chart), and raw packet support.
Positive target time and compact enlarged carrier come from placement.
It returns a cutoff with `LocalPotentialAPI` and the full `CorrectionAPI`,
plus identification with the original velocity on `Ico 0 (place.T + δ)`.
No smoothness, divergence or global-periodicity premise is added.

The raw support clause is not a field of raw `PlacementData`.
`BlowupDensity.Bindings.Correction3.correctionArticle_of_packet` derives it
from registered `PacketAPI.velocity_support`, so packet consumers do not
supply that premise separately.

G5 is respected: the correction API's global `reference_periodic` field
prevents asserting the API for the unconstrained original velocity outside
its lifespan. The potential record also fixes its radial formula at all
times, so its zero-extension convention is retained. `article_potential_formula`
identifies the radial formula on the classical slab. `article_window_identification`
uses `eps_time` to put the full closed cutoff window inside that slab.
`article_force_identification` uses `correction_support` to prove **global**
equality of the force computed with the extension and the article velocity.
Correction/force profiles are likewise identified globally, including their
zero parts outside the fixed cylinder.

Named article exports cover force smoothness, periodicity, open support,
spatial volume and time length, both derivative inequalities, `eq:wE`,
`eq:Hmixed`, and `eq:HHs` (the revised article's Sobolev label). They retain
all exponents, constants, the range `0 ≤ s ≤ 1`, both Sobolev terms, and
mixed/Sobolev integrability guards. The profile smoothness, support, uniform
bounds and scaling identities are also exported for `reference.velocity`.
All constants remain selected before the scale.

`T02.correction_v2` is registered alongside V1. Its statement uses the
registered classical-solution, placement, cutoff and correction records;
the binding applies their existing fieldwise conversions.

## 2. Files

New proof: `formalization/NSFormalization/Section3/T17/ArticleScope.lean`
(26 proved theorems).

New interface: `verification/Contracts/V2/Correction3.lean`,
`verification/Bindings/Correction3V2.lean`, `verification/Tests/Correction3V2.lean`.

Research: `probes/article_scope.lean`, `axioms_493.lean`, `ATTEMPTS_493.md`,
this report, and the P2 status in `SPEC_ISSUES.md`.

Updated contract registry and count; blueprint graph, entrypoints, result map,
closure audit, source axiom audit and generated dependency graph; README counts;
guide proof locations and both rebuilt PDFs. The reader checker now expects
five Partial entries and explicitly requires the article correction theorem.
Existing Lean proof modules were not edited.

`C35_FULL` is Closed with `depends_on: ["C35_T"]` and no remaining completion
links. Coverage is **22 Closed / 5 Partial**; the registry has **30 interfaces**.

## 3. Gaps and encountered errors

No remaining mathematical or verification gap for P2. The false unamended
G4/G5 statements remain untouched and are not used as premises.

Resolved development errors are recorded in ATTEMPTS. In particular:
- `Unknown identifier A.potential.eps_time`: fixed section-variable inclusion.
- `Ambiguous term VelocityField`: removed competing implementation namespace
  from the registered contract.
- `Current test roots differ from retained tests`: registered the new test root.
- `Source changed: rerun the article axiom audit`: regenerated and reviewed audit.
- Initial `make paper`: `AssertionError` at reader checker line 61 because the
  expected Partial set still included `lem:correction`; updated the expected
  coverage and added an explicit Closed/theorem assertion. Final run passes.

## 4. Commands and results

All Lean commands used `scripts/lean-env.sh`, the verification package, and
`LEAN_NUM_THREADS=6`.

| Command | Result |
|---|---|
| `lake build NSFormalization.Section3.T17.ArticleScope` | Pass |
| `lake build Tests.Correction3V2` | Pass; main contract and packet specialization checked |
| `lake env lean ../research/T17/probes/article_scope.lean` | Pass |
| `lake env lean ../research/T17/axioms_493.lean` | All 26 theorems print exactly `[propext, Classical.choice, Quot.sound]` |
| `python3 experiments/audit_article_axioms.py --build --output-dir tmp/article-audit --workers 2` | Pass: 65 declarations, 27 article entries, zero forbidden-axiom results; reviewed report copied to AXIOM_AUDIT.json |
| `python3 experiments/check_formalization_plan.py` | Pass after audit refresh; graph regenerated |
| `make check` | Pass: 30 contracts and 11 policy tests |
| `make test` | Pass |
| `make test-mutations` | Pass: refactor accepted; admission, extra axiom and weakened hypothesis rejected |
| `make paper` | Pass: both PDF logs clean; 27 guide mappings and 30 registry declarations checked |
| `git diff --check` | Pass |

Detailed local command logs are under `tmp/lane493/`; full audit artifacts are
under `tmp/article-audit/`. No push, merge or rebase was performed.
