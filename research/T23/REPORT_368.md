# REPORT_368 — T23 Draft A

## 1. 证了哪个定理

这是 `cor:boundary`（`paper/sections/03-torus.tex:632-667`）的 statement-only
Draft A。`BoundaryInsertionAPI` records the bounded box/smooth-domain
hypotheses, a compatible smooth no-slip reference through `T+δ`, the interior
support and fixed boundary collar, the three insertion displays, the bounded
classical-solution/lifespan/blow-up clauses, domain energy estimates, the
`s<1/2` force convergence, all-real-order domain/zero-extension comparison, and
no-slip uniqueness.  `boundaryInsertionStatement` preserves the paper's
quantifier order and concludes with `Nonempty` of the API.

## 2. Lean 里现在有什么

`research/T23/DraftA.lean` is 2,498 lines.  It imports the registered packet
and packet-import contracts, and contains the T18 vocabulary
(`PeriodicInsertionAPI` and its used T13--T17 blocks) copied verbatim with a
provenance header, the T22 bounded-domain vocabulary copied verbatim, and the
new T23 definitions `IsRegularLevelDomain`, `IsBoxDomain`,
`SmoothOnClosedDomainSlab`, `DomainForceClass`, quotient-domain force norms,
bounded energy/lifespan predicates, and `BoundaryInsertionAPI`.

`research/T23/COMPARISON_A.md` is the clause-by-clause paper/Lean table.  It
also records torus-only versus Section 4 fields, choices and ambiguities, the
T11/T12/T18/T20 lemma-consumption list, and implementation candidates.  The
candidate `Paper1/BoundaryCorollary.lean` was inspected only; it was not
imported because its `exists_interior_noSlip_insertion` proof has the known
`sorry` at line 90.

## 3. 缺口是什么

No bounded-domain local/continuation implementation is registered.  The
remaining proof work is the bounded no-slip difference-energy uniqueness,
construction of the interior insertion from T18's packet/correction data,
the T22 quotient/zero-extension comparison applied uniformly to the fixed
interior support, and the bridge from the periodic/whole-space continuation
packages to `IsBoundedClassicalSolution`.  The paper's mixed `L^q_tL^p_x`
periodization clauses are intentionally marked torus-only rather than asserted
by the bounded corollary.  `T20` is not a direct dependency; only a future
critical-route continuation lemma could consume it.

## 4. 跑了什么命令、什么结果

* `cd verification && lake env lean ../research/T23/DraftA.lean` — **0 errors**.
* `grep -nE ': *True|:= *0$|→ *True' research/T23/DraftA.lean` — empty output.
* `grep -nE '^(def|structure|theorem) '` over the four named `Paper1`
  boundary candidates — declarations recorded in `COMPARISON_A.md`; the
  `sorry`-bearing candidate was not imported.
* `wc -l research/T23/DraftA.lean research/T23/COMPARISON_A.md` — `2498` and
  `137` lines respectively.
