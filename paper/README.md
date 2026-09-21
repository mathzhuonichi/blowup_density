# Article and Lean guide

The only current article source is
[revised/blowup_density_revised.tex](revised/blowup_density_revised.tex), with
four sections in `revised/sections/` and its bibliography in
[revised/references.tex](revised/references.tex).
[formalization_guide.tex](formalization_guide.tex) maps the 26 numbered
statements and one numbered remark to Lean source locations and explains the
coverage limits. The two original manuscripts are retained as PDFs only in
[originals/local/](originals/local/).

Run `make paper` from the repository root, or `make readers` here. The outputs
are [the article](../output/pdf/blowup_density_revised.pdf) and
[the guide](../output/pdf/formalization_guide.pdf). The article is built first
because the guide reads its theorem numbers from the generated AUX file.
`make clean` removes intermediates while preserving the PDFs.

The reader-document checker verifies reference targets, bibliography metadata,
the retained corpus hashes, complete result-to-code coverage, declaration names
and source line numbers, registered test declarations, and clean LaTeX logs.
It no longer requires the retired merged manuscript or historical source
snapshots. These are structural checks, not a proof that the mathematics is
unchanged or a fresh Lean build.

Terminology conventions are in [reference/TERMINOLOGY.md](../reference/TERMINOLOGY.md);
the reviewed replacement map remains in [terminology.json](terminology.json).
The full reference corpus is retained under [reference/](../reference/).

Every result row carries an explicit coverage label. Closed means complete formalization; Partial means partial formalization.
Downstream results can be Closed when they use only proved upstream cases. The guide records the boundary-IBP closure and distinguishes
unproved H1 restart predicates from the proved H7/H3 continuation route.
