# Article and Lean guide

The only current article source is
[revised/blowup_density_revised.tex](revised/blowup_density_revised.tex), with
four sections in `revised/sections/` and its bibliography in
[revised/references.tex](revised/references.tex).
[formalization_guide.tex](formalization_guide.tex) maps the 26 numbered
statements and one numbered remark to Lean source locations and explains the
scope qualifications. The two original manuscripts are retained as PDFs only in
[originals/local/](originals/local/).

The checked-in outputs, [the article](blowup_density_revised.pdf) and
[the guide](formalization_guide.pdf), live beside their sources in this directory.
PDF production is kept outside the repository's Lean build interface.

To rebuild both PDFs with a TeX installation and `latexmk`, run from the
repository root, in this order:

```sh
latexmk -cd -pdf -interaction=nonstopmode -halt-on-error -outdir=.. paper/revised/blowup_density_revised.tex
latexmk -cd -pdf -interaction=nonstopmode -halt-on-error paper/formalization_guide.tex
```

The article build supplies the auxiliary labels used by the guide. The guide's
article links resolve to the neighboring PDF. LaTeX auxiliary files are ignored.

The reader-document checker verifies reference targets, bibliography metadata,
the retained corpus hashes, complete result-to-code coverage, declaration names,
source line numbers and registered test declarations. It no longer requires the
retired merged manuscript, historical source snapshots or LaTeX build logs.
These are structural checks, not a proof that the mathematics is unchanged or a
fresh Lean build.

Terminology conventions are in [reference/TERMINOLOGY.md](../reference/TERMINOLOGY.md);
the reviewed replacement map remains in [terminology.json](terminology.json).
The full reference corpus is retained under [reference/](../reference/).

Every result row is Closed. The guide records the boundary-IBP closure and the
proved H1-uniform restart and endpoint continuation routes on both domains.
