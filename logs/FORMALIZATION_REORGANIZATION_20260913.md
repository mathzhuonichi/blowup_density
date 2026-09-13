# Section 4 formalization reorganization

Date: 13 September 2026. The active target is the merged article's Section 4,
formerly Paper 3. Repository records are in English; the original Lean sources
and their source quotations were preserved verbatim.

## Delivered layout

- `paper/blowup_density.tex` and `output/pdf/blowup_density.pdf`: renamed main
  manuscript and rebuilt PDF. Build configuration, checker and workspace links
  use the new basename. Section text and mathematical statements were unchanged.
- `paper/originals/local/`: verified current original Paper 1 and Paper 3 TeX,
  plus their copied matching local PDFs.
- `formalization/`: 340 original Lean files, unchanged, with relative Lake
  dependency paths relocated to `../vendor/NavierStokesAndEuler`.
- `vendor/NavierStokesAndEuler/`: 2,486 original Lean files and package metadata.
- `vendor/HeliCorgi/`: 128 Formal Lean modules plus the original Lean Lakefile,
  pinned at `de518485776d1d8de60f0c51151121df71e3ab6d`.
- `formalization/blueprint/`: 30-node task graph, exact contracts, original-to-
  merged result map, external reuse audit and implementation handoff.

No Lean proof or import was edited. Compiler caches, package caches, Git history,
legacy build logs, numerical output and installed compilers were not copied.
HeliCorgi's Lean 4.32.1 project remains separate from the OpenAI/local Lean
4.34.0-rc2 project; interoperability is a future checked adaptation task.

## Mathematical planning outcome

Reuse the concrete whole-space libraries and the existing insertion family.
The main remaining obligations are forced classical/all-order solution and
maximal-lifespan adapters, squared-H2 continuation, critical energy estimates,
and final topology/class assemblies. Periodic domain transfers are deferred.
The local namespace `Paper1` contains reusable Euclidean results; directory
names are not domain evidence.

HeliCorgi's operator/pressure/uniqueness/restart stack reduces foundational
work. Its current capstone is unforced, locally defined and spatially
distributional. Those exact scope differences remain visible in the plan.
OpenAI's forced finite-order cylinder construction complements that stack;
it also needs the manuscript's classical common-interval bridge.

## Checks performed

- Rebuilt the renamed manuscript with `make -C paper`.
- Ran `python3 experiments/check_manuscript.py`: 34 source occurrences,
  28 merged numbered results, 106 labels, 14 bibliography entries, no LaTeX
  warnings. This checks document integrity, not mathematical proof validity.
- Compared `pdftotext -layout` output before and after renaming: identical.
- Read the merged whole-space statements and both analytic appendices; visually
  inspected the rendered page containing the Section 4 main theorem.
- Read selected local and upstream theorem declarations, the OpenAI paper's
  first theorem, and Tao's published Theorem 5.4 and smooth-data explanation.
- Ran `python3 experiments/check_formalization_plan.py`: source hashes,
  relative paths, source import closure, cache exclusion, evidence paths,
  DAG acyclicity and complete result mapping passed.
- Checked all links in the new plan and entry-point documentation.

The legacy umbrella reaches one admitted boundary theorem. Six schematic
citation axioms and four upstream comparator challenge admissions are also
present outside that umbrella closure. The static report gives exact file and
line locators. No new Lean build or transitive kernel axiom audit was run;
no full-paper certification or clean legacy umbrella certification is claimed.

## Publication scope

The user authorized a new private GitHub repository named `blowup_density`.
The upload contains the existing consolidated manuscript/reference workspace
and the source-only formalization plan. No automatic Lean CI is introduced.
The proof task tree is represented by versioned Markdown/JSON, not by a batch
of GitHub issues. Future tasks should start from `formalization/blueprint/README.md`.

The initial staged-tree whitespace check reports pre-existing whitespace in
verbatim upstream Lean, archived source HTML and prior review Markdown. Those
files were preserved rather than reformatted. The new plan, checker and current
entry-point documents pass the focused whitespace check. The staged tree was
also checked for copied caches, oversized files and common credential patterns;
none was found.
