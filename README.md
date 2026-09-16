# Density of forces producing Navier--Stokes blowup

This is one shared repository for the entire project: both contributors can
work on the manuscript, all formalization code, references, research notes,
tests and project infrastructure. The default integration branch is `main`;
use task branches and pull requests for changes. Section 3 (the torus) is the current formalization priority, on
`erenup/integration-section3`. Start with the [live plan](PLAN.md),
[current state](NEXT_SESSION.md), and [work packages](collaboration/HANDOFF.md).

For two-person development, start with [CONTRIBUTING.md](CONTRIBUTING.md),
the [owned work queue](collaboration/TASKS.md), and the
[versioned Lean acceptance interfaces](verification/README.md).
Use `make check`, `make test`, and `make test-mutations` before a proof PR.
Section 4 has 37 registered contracts and is preserved on the frozen branch
`erenup/integration`, with PR #259 to `main` pending owner review. Its working
documents and remaining owner decisions are in the [Section 4 archive](archive/section4/README.md).

The active Section 3 DAG and stages are in [SECTION3_PLAN.md](collaboration/SECTION3_PLAN.md).
The completed Section 4 work (the former Paper 3) remains available below.
The [proof task tree](formalization/blueprint/README.md) reuses the existing
OpenAI and HeliCorgi whole-space libraries and isolates the remaining
manuscript adapters. The [source-only package](formalization/README.md)
contains the copied local proofs and two upstream source snapshots, without
compilation caches. No new Lean code was written during this reorganization.
Neither the merged article nor its legacy umbrella has full formal certification.

This workspace contains a consolidated English article based on the current
Paper 1 and Paper 3 manuscripts. The five main sections are Introduction,
Definitions and preliminary results, The torus, The whole space, and Conclusion.
Two concise appendices cite the classical local theory and Sobolev embeddings
and give the normalization, continuation, and homogeneous-space details
needed for their application.

- [Read the merged PDF](output/pdf/blowup_density.pdf).
- [Edit the main LaTeX source](paper/blowup_density.tex); the section files are in
  [paper/sections/](paper/sections/).
- [Review the theorem correspondence](logs/THEOREM_CORRESPONDENCE.md).
- [Read the revision record](logs/REVISION_20260912.md).
- [Inspect source provenance and citations](reference/README.md).

The 34 numbered results in the two source manuscripts correspond to 28 distinct
numbered results after sharing repeated material. The force classes, initial-data
quantifiers, density thresholds, continuation criterion, and distinction between
breakdown by T and insertion with blowup exactly at T are retained. This is a
mathematical and editorial consolidation; it is not a new formal certification.

## Original manuscripts

Unmodified server sources copied from
`zchi-server:/home/user/zchi/math-authoring-kit/research/ns/ns paper/` are in
[paper/originals/server/](paper/originals/server/). The more recent local copies
from `/Users/chizhuoni/Documents/GitHub/NS/ns paper/` are preserved in
[paper/originals/local/](paper/originals/local/) and provide the editorial baseline.
Their only differences are citation comments and a clarification that the
classical local-theory references supply background. Their mathematics agrees.
The [SHA-256 manifest](logs/SOURCE_MANIFEST.json) identifies all four copied files.

## Build and verification

Run from this workspace:

```sh
make -C paper
python3 experiments/check_manuscript.py
python3 experiments/check_formalization_plan.py
```

The build requires LaTeX with `latexmk` and `pdflatex`. The script checks the five
main sections, source-result coverage, mathematical expressions in theorem
statements, labels, citations, and LaTeX warnings. It writes
[MANUSCRIPT_CHECK.json](logs/MANUSCRIPT_CHECK.json). Proof review and the
shared statement formulations and restored source notation requiring contextual comparison are documented
separately in the theorem correspondence. Generated build and rendering files
are ignored; the readable PDF is retained.
