# Smooth cutoff constructions and PDE gluing

Survey date: 12 September 2026.

Publication update: the manuscript now cites the published Euler article,
DOI [10.1017/fmp.2025.10012](https://doi.org/10.1017/fmp.2025.10012).
Its publisher PDF is saved separately as
`Enciso_PenafielTomas_PeraltaSalas_2025_Published.pdf`.
Theorem 1.5 (p. 5), Lemma 2.11 (p. 17), Lemmas 11.1–11.2 (pp. 70–71),
and Section 11.3 (pp. 75–77) have now been checked in that version.
The preprint-based survey and follow-up below are retained as the record
of the earlier comparison; the previous publisher-access limitation has
been resolved by retrieving the PDF.

## Scope and comparison with Papers 1 and 3

The request is for articles that construct PDE solutions using the idea behind
the smooth Urysohn lemma, without restriction to Navier–Stokes equations.
The current manuscript's insertion construction was read in
`paper/sections/01-introduction.tex` and `paper/sections/03-torus.tex`, together
with the source provenance in the topic README. The comparison concerns the
construction mechanism, not an independent certification of the manuscript.

The relevant mechanism is to choose a smooth function equal to one near an
inner region and zero outside a larger region, preserve differential
constraints, and construct a solution with prescribed local behavior.
In the manuscript, the correction is

\[
w_\varepsilon=-\nabla\times(\eta_\varepsilon\theta_\varepsilon A),
\qquad u_\varepsilon=v+w_\varepsilon+U_\varepsilon.
\]

The corrected background vanishes near the active support of the inserted
solution. The remaining smooth residual is included in a modified force.
This last feature distinguishes the manuscript from constructions that must
remove the residual while keeping the equation's right-hand side fixed.

## Selected primary sources

### 1. Erwann Delay: underdetermined elliptic equations

*Smooth compactly supported solutions of some underdetermined elliptic PDE,
with gluing applications*, Communications in Partial Differential Equations
37 (2012), 1689–1716.

- [Full text, arXiv:1003.0535v4](https://arxiv.org/pdf/1003.0535v4).
- Saved as `Delay_2012_Underdetermined_Elliptic_Gluing.pdf`.
- Read: Theorem 1.5 and Corollary 1.6, PDF p. 4; Section 6, pp. 10–11.

For an appropriate linear underdetermined elliptic operator, two kernel
elements are joined as `chi V + (1-chi) W + U`, with the correction supported
in the closure of the transition region. The adjoint hypotheses API and KRC
and the flux compatibility condition are essential. Remark 6.4 explicitly
allows gluing to zero when the flux vanishes. Section 9.1 treats divergence-free
fields. This is the closest abstract precedent for making a solution vanish
locally while retaining its differential constraint.

### 2. Erwann Delay: prescribed scalar curvature

*Localized gluing of Riemannian metrics in interpolating their scalar
curvature*, Differential Geometry and its Applications 29 (2011), 433–439.

- [Full text, arXiv:1003.5146v1](https://arxiv.org/pdf/1003.5146v1).
- Saved as `Delay_2011_Scalar_Curvature_Gluing.pdf`.
- Read: Theorem 1.1, PDF p. 2, and Section 2.2.

For sufficiently close metrics and trivial kernel of the adjoint linearized
scalar-curvature operator on the transition region, the construction gives

\[
\widetilde g=\chi g+(1-\chi)\bar g+h,
\qquad R(\widetilde g)=\chi R(g)+(1-\chi)R(\bar g).
\]

The correction is supported in the closure of that region. Thus two metrics
with the same constant scalar curvature can be joined without changing that
curvature. This is a concrete nonlinear geometric PDE counterpart, with
additional analytic correction beyond the cutoff.

### 3. Enciso, Peñafiel-Tomás, and Peralta-Salas: Euler extension

*An extension theorem for weak solutions of the 3d incompressible Euler
equations and applications to singular flows*, Forum of Mathematics, Pi
13 (2025), e21.

- [Published article](https://www.cambridge.org/core/journals/forum-of-mathematics-pi/article/an-extension-theorem-for-weak-solutions-of-the-3d-incompressible-euler-equations-and-applications-to-singular-flows/45F600F532ABCFDA3A76A1075E4319CC).
- [Read preprint, arXiv:2404.08115v2](https://arxiv.org/html/2404.08115v2).
- Saved as `Enciso_PenafielTomas_PeraltaSalas_2025_Euler_Extension.pdf`;
  the saved PDF is the April 2024 preprint, not the typeset 2025 article.
- Read: Lemma 2.11 and its cutoff/potential construction; Theorem 1.5;
  the initial preparation in Section 11.3. Locators refer to preprint v2.

Lemma 2.11 glues smooth Euler subsolutions subject to flux compatibility,
using a cutoff and a potential correction to preserve divergence. Theorem
1.5 constructs a weak solution equal to a prescribed smooth solution outside
a chosen region, but singular inside it. Convex integration removes the
Reynolds stress. Initial data are uniformly close, not required to be
identical. This is a particularly close analogy to local singular insertion,
but is not a classical forced blowup theorem.

### 4. Carlotto and Schoen: Einstein constraint localization

*Localizing solutions of the Einstein constraint equations*, Inventiones
Mathematicae 205 (2016), 559–615.

- [Full text, arXiv:1407.4766v2](https://arxiv.org/pdf/1407.4766v2).
- Saved as `Carlotto_Schoen_Einstein_Localization.pdf`.
- Read: Theorem 2.3, PDF p. 6; regularity discussion and Section 3.1,
  pp. 7–8; statement and gluing application in Section 6.

Under the stated asymptotic flatness and decay hypotheses, with the cone
vertex sufficiently far out, new vacuum constraint data equal the original
data in an inner conical region and flat data outside a larger cone. An
angular cutoff first makes an approximate solution; a localized deformation
then solves the constraints. This realizes exact spatial separation for a
nonlinear PDE system. The immediate theorem constructs constrained initial
data; it does not assert arbitrary compact spacetime pasting of Einstein
evolutions.

### 5. del Pino, Musso, and Wei: critical nonlinear heat equation

*Infinite time blow-up for the 3-dimensional energy critical heat equation*,
Analysis & PDE 13 (2020), 215–274.

- [Full text, arXiv:1705.01672v4](https://arxiv.org/pdf/1705.01672v4).
- [Publisher record](https://msp.org/apde/2020/13-1/apde-v13-n1-p07-s.pdf).
- Saved as `delPino_Musso_Wei_Heat_Gluing.pdf`.
- Read: main construction statement; equation (1.9); equations
  (2.38)–(2.40), PDF p. 10; final inner–outer argument in Section 8, p. 31.

For `u_t = Delta u + u^5` on three-dimensional Euclidean space, equation
(2.38) joins inner and outer profiles with a smooth cutoff at scale
`r_0 sqrt(t)`. The authors compute the resulting PDE residual and solve
coupled inner and outer correction problems. The result is a solution
unbounded as time tends to infinity. Unlike the manuscript, the residual
is removed without adding an external force, and the final solution need
not agree exactly with the original profiles on open regions.

## Interpretation and coverage limits

These are substantive construction analogies, not a list of occurrences of
the word Urysohn. The checked arguments use smooth cutoff functions; this
survey does not claim that their authors explicitly invoke Urysohn's lemma.
Useful search terms are `localized gluing`, `compactly supported correction`,
`gluing to zero`, `extension of local solutions`, and `inner-outer gluing`.
Search results about Urysohn integral equations concern a different subject.

The best starting point for the abstract mechanism is Delay (2012); the most
direct nonlinear non-fluid formula is Delay (2011); the closest singular
insertion comparison is Enciso–Peñafiel-Tomás–Peralta-Salas. The heat paper
shows how the same cutoff idea enters an evolutionary PDE construction
when a genuine correction problem must be solved.

The source statements and indicated construction passages were inspected;
the full proofs were not independently rederived. No conclusion about the
novelty or validity of Papers 1 and 3 follows from this survey alone.
All five saved PDFs were checked for a PDF header and successfully processed
with `pdftotext`. Preprint versions are identified above; theorem numbering
may differ in published versions.

## Follow-up: how directly does the Euler construction anticipate this manuscript?

The follow-up comparison examined preprint v2, Sections 11.1–11.3, against
the current manuscript's exact insertion and force-density arguments.
The publisher's full HTML could not be fetched in this follow-up because
it exceeded the retrieval size limit. The detailed comparison therefore
uses the explicitly identified preprint, not an asserted version-by-version
audit of the published article.

The overlap is stronger than a shared use of cutoff functions. In Section
11.3 the Euler authors first replace the local background by a spatially
constant field. Lemma 11.1 supplies a localized singular building block,
including scaling and small relative energy. Lemma 11.2 joins blocks whose
departures from that background have disjoint closed supports. Thus local
background preparation, singular building blocks, shrinking, and exact
patching already belong to their construction. Their building blocks and
background correction are obtained using weak-solution machinery.

The present manuscript changes the available input and the target conclusion.
It assumes the cited compact classical forced NS blowup construction, removes
the smooth background near its support by an explicit vector-potential cutoff,
and places the remaining smooth defect in a new external force. Linearity of
the viscous term and vanishing nonlinear cross terms give an exact identity.
This is a comparatively direct adaptation of a known localization paradigm,
once the much stronger classical building block is supplied.

It is not a direct consequence of the Euler theorem. Formally reusing an
unforced Euler solution as a forced NS solution requires `f = -nu Delta v`.
The Euler theorem's weak regularity does not ensure that this is a smooth
force, or that the velocity is classical before its singular time. Conversely,
allowing a variable force makes the residual correction substantially simpler
than eliminating Reynolds stress in an unforced equation.

The contribution requiring separate evaluation is the quantitative force-space
statement: fixed smooth initial velocity, unchanged earlier history near a
regular reference, smooth force through the terminal time, and force-density
thresholds. The homogeneous scaling factor is
`epsilon^(2/q - 3/2 - s)` when the profile's homogeneous norm is finite;
the smooth background force correction gains one power of epsilon.
The endpoint non-density claims require separate regularity estimates.
The converse in the current manuscript is stated for zero initial velocity.
These distinctions prevent identifying the theorems, but they do not by
themselves establish originality or substantial methodological novelty.

A defensible provisional description is: quantitative force-density
consequences of the compact forced NS blowup theorem, obtained through a
localized insertion construction with close precedents in Euler gluing.
Neither the existence of a distinct statement nor the need to write its
estimates establishes that those estimates are new. Determining that would
require a focused comparison with existing forced NS density results and
the consequences already drawn in the source of the building block.
No manuscript novelty claims were changed in this follow-up.
