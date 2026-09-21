# Lane 499 — P21 / P6 assessment report

Status: **assessment complete; P6 remains Partial.** Deliverable: `research/P21/ASSESSMENT.md`. No Lean changes, probes, admissions, new theorem inputs, registry edits or coverage changes.

## 1. What was assessed

Compared the revised Proposition 2.1, Tao 2013's actual Section 5 proof, the guide, proof graph and closure audit with A01/A04 and T11 local theory. Wrote exact proposed Lean statement expressions for fixed-force H¹-uniform local restart and endpoint continuation on both domains, explicitly marked unproved and not type-checked. Distinguished existential duration from the old selected high-order horizon, fixed-force from cross-force bounds, and smooth admissible data from arbitrary rough H¹ data.

The revised proposition does not explicitly state H¹-uniform restart. Its proof bounds every high norm before restarting. H¹ is subcritical in 3D, not the scaling-critical Ḣ¹ᐟ² endpoint.

## 2. What is in the tree

A01 constructs smooth solutions on one H⁷-selected interval, using the ordinary cylinder; A04 supplies compact-time fixed-force restart and the squared-H² continuation conclusion. T11 constructs H³/H² mild solutions, propagates smoothness, and supplies H³ restart plus the full integral continuation conclusion. HeliCorgi endpoint-safe Picard acts on continuous paths in an abstract Banach space and requires a concrete bilinear/smoothing contract; its name does not assert an H¹ or critical Sobolev endpoint instance. T11's fractional half-step contract starts at r≥3.

Downstream article quotations and current bindings/closure evidence show that the stronger H¹-ball duration is not consumed by the Closed results. The report preserves the registered force-class qualification rather than claiming arbitrary locally smooth forcing is literally exported.

## 3. What is missing

For Tao's route: mixed-space linear estimates, a concrete low-order bilinear estimate, quantitative forced contraction, and same-interval low-to-high persistence/assembly. Estimated XL programme, 27–45 focused days for both domains, with stated contingency.

For the narrower smooth-data fixed-force target, a potentially shorter route uses a general enstrophy/ODE bound and the already proved integral continuation theorem; estimated 12–21 days, conditional on bridge reuse. This was assessed mathematically, not proved or benchmarked. Recommended decision is (iii), leave Partial; if commissioned later, test this energy route before building a full rough-data mild theory. H² uniformity would not close the named H¹ obligation.

Requested historical files `research/A01/RECONCILIATION.md` and `research/A01/SPEC_ISSUES.md` are absent. Used surviving V2 decision, review and report records, with current declarations taking precedence. No Lean error is claimed because no Lean probe/build was run.

## 4. Commands run and results

- `pwd`, `git status --short`, `rg --files`: confirmed worktree and located contracts, blueprint, source and research records. Existing untracked lane/common briefs were left untouched.
- `head`, `sed -n`, `rg -n`, and Python source inventories: read common instructions and project verification context; inspected article/guide/graph/audit, registered local/continuation APIs and bindings, A01 source inventory and relevant bodies, A04 restart/high-continuation modules, requested T11 modules, kept HeliCorgi roots and historical records. Broad searches were followed by targeted reads where output was truncated.
- Searches for `H¹`, `H1`, `ball`, `uniform`, concrete two-space types, and downstream article labels: established scope distinctions and located the cited consumers. Missing requested A01 historical paths returned `No such file or directory`; a subsequent filename search located the substitute records.
- `pdftotext -layout reference/Tao_2013_Localisation_Compactness_Published.pdf /tmp/p21-tao.txt`: succeeded. Read equations (13), (22), (24)–(25), (45)–(46) and proofs of Theorems 5.1/5.4; printed page locators recorded in the assessment. Temporary extraction/index files are outside the tracked deliverables.
- `git diff --check`: passed for the documentation changes.
- Committed the initial assessment skeleton, then the completed assessment/report. No push, merge or rebase.

No `lake`, `make`, axiom audit, PDF rendering, or contract tests were run: this lane changes only research Markdown and makes no kernel-verification claim. The common brief's Lean closure/registration procedure does not apply to the user's explicitly assessment-only scope.
