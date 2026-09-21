# Post-Revision Semantic Review

**Date:** 12 September 2026  
**Scope:** the six authorized clarifications in paper/blowup_density.tex,
paper/sections/03-torus.tex, paper/sections/04-whole-space.tex, and
paper/sections/05-conclusion.tex  
**Comparison basis:** tmp/semantic-revision/before/paper/ and
tmp/semantic-revision/source.diff, including the subsequent punctuation-only
change after \(t_\varepsilon=T-\varepsilon^2\)

## Verdict

The six revisions preserve the mathematical objects, quantifier order,
topologies, and conclusions of the governing statements and proofs. I found no
semantic objection. In particular, the revision does not create a rough
force/trajectory product-density claim, does not extend \(U\) or \(P\) beyond
their singular source time, does not make the force family in Proposition
prop:affine affine or fixed, and does not broaden the grid observation theorem
beyond its whole-space pre-blowup scope.

## Per-change checks

### 1. Completed force spaces and energy approximation

- **Current locator:** paper/blowup_density.tex, lines 48--53.
- **Governing statements:** paper/sections/04-whole-space.tex, lines 218--229,
  Proposition prop:Renergy; paper/sections/03-torus.tex, lines 540--561,
  Corollary cor:closure; and paper/sections/04-whole-space.tex, lines 31--42,
  Theorem thm:Rinsert.
- **Check:** the abstract now assigns density to smooth compact **forces**
  producing breakdown by \(T\), for fixed
  \(a\in\mathcal X_{\mathbb R}\), \(q\in\{1,2\}\), and every
  \(s<2/q-3/2\), on the full positive-time Bochner spaces. It separately
  states strong approximation of regular reference velocities in energy and
  dissipation. This is exactly the separation made by Proposition prop:Renergy
  and the trajectory estimates. It neither assigns a trajectory to an
  arbitrary rough force nor asserts density in an undefined completed product
  space.
- **Result:** semantically exact; no strengthening or weakening.

### 2. Prescribed time and grid-observation scope

- **Current locators:** paper/blowup_density.tex, lines 36--37 and 54--56;
  paper/sections/04-whole-space.tex, lines 297--329, Theorem thm:Rgrid and its
  interpretation; paper/sections/05-conclusion.tex, lines 18--22.
- **Governing statement/proof:** Theorem thm:Rgrid gives equality of both
  velocity and force cell averages on \(\mathbb R^3\), on every cell of each
  grid in a fixed finite family, for every \(0\le t<T\). Its construction may
  depend on that prescribed family.
- **Check:** changing “before a prescribed time” to “by a prescribed time
  \(T>0\)” matches the breakdown sets \(T_{\max}\le T\) and binds the \(T\)
  used later in the abstract. The revised grid claims now specify the
  whole-space domain, the exact half-open time interval, and a prescribed
  finite family. The interpretive paragraph correctly identifies the
  numerical inputs as initial-velocity cell averages plus force cell averages
  for \(0\le t<T\); it does not claim equality of force averages after \(T\).
- **Result:** semantically exact; the revision removes the former scope
  ambiguity without changing Theorem thm:Rgrid.

### 3. Scaling center

- **Current locator:** paper/sections/03-torus.tex, lines 101--107.
- **Governing construction:** Lemma lem:localization and equation eq:scaling,
  with the requirement \(x_0+\varepsilon K_*\subset B\).
- **Check:** choosing \(x_0\in B\) makes the subsequent containment valid for
  all sufficiently small \(\varepsilon\), since \(K_*\) is compact and \(B\)
  is open. The choice introduces no new restriction: the insertion theorem
  already permits an arbitrary nonempty coordinate ball and the center was
  always free to be selected inside it.
- **Result:** semantically exact; an implicit choice is now bound explicitly.

### 4. Negative-time extension of the source force

- **Current locator:** paper/sections/03-torus.tex, lines 108--120, equation
  eq:scaling.
- **Governing domains:** Theorem thm:packet declares
  \(F\in C_c^\infty(\mathbb R^3\times(0,\infty))\) and \(U,P\) only before
  source time one; Lemma lem:packetenergy supplies the negative-time zero
  extensions of \(U,P\).
- **Check:** the new sentence extends only \(F\) to nonpositive source times.
  This is smooth because its temporal support is compactly contained in
  \((0,\infty)\). It then separately invokes the already proved
  negative-time extensions of \(U,P\). The next sentence still restricts
  \(U_\varepsilon,P_\varepsilon\) to target times \(t<T\), whose source-time
  arguments are strictly below one. Thus neither \(U\) nor \(P\) has been
  extended through or beyond its singular time. The force remains defined at
  all positive target times using its original positive-source-time domain.
- **Result:** semantically exact; it only makes the previously implicit
  evaluation domain well defined.

### 5. Positive continuation margin in the no-slip corollary

- **Current locator:** paper/sections/03-torus.tex, lines 632--652, Corollary
  cor:boundary; proof at lines 653--664.
- **Governing construction:** the cutoffs use the reference on a neighborhood
  of time \(T\), with sufficiently small scale chosen so that
  \(2\varepsilon^2<\delta\).
- **Check:** “for some \(\delta>0\)” now binds the parameter already used in
  \([0,T+\delta]\). It records exactly the positive future margin required by
  the proof. The compatible smooth no-slip reference remains an explicit
  assumption, and the force remains smooth on every finite closed slab with
  compact temporal support in \((0,\infty)\). No arbitrary-data
  bounded-domain existence statement has been introduced.
- **Result:** semantically exact; no new mathematical conclusion or material
  hypothesis beyond the intended meaning of “through \(T\).”

### 6. Domain and object of the affine variation

- **Current locator:** paper/sections/05-conclusion.tex, lines 23--26.
- **Governing statement:** paper/sections/03-torus.tex, lines 668--690,
  Proposition prop:affine and equation eq:affine.
- **Check:** the conclusion now attributes the affine family to the
  whole-space compact solution and calls it an affine family of
  **velocities**. It explicitly says that the corresponding forces change.
  This matches \(U+b\), whose image is affine in \(b\), and
  \[
  F+\lambda L_Ub+\lambda^2(b\cdot\nabla)b,
  \]
  whose force dependence is generally quadratic in \(\lambda\) and does not
  preserve a fixed force. The periodic/bounded-domain attribution is retained
  only for the finite collection of prescribed singular regions from
  Proposition prop:multiple.
- **Result:** semantically exact; no fixed-force or affine-force claim is
  present.

## Diff boundary

Across the four changed LaTeX files, the actual current diff against the
frozen before/ copies contains only these clarifications and the stated
punctuation change from a comma to a period after
\(t_\varepsilon=T-\varepsilon^2\). Corollary cor:boundary is the one numbered
statement body deliberately revised: it now explicitly binds \(\delta>0\) and
states the reference interval as \([0,T+\delta]\), preserving its intended
mathematical scope. The other 27 numbered statement bodies are unchanged up
to whitespace. No displayed estimate, force or velocity definition, support
condition, norm, exponent, or proof step was redirected or altered.

## Final disposition

All six clarifications pass targeted semantic review. No manuscript edit is
recommended from this review.
