# Sources for the introductory notation

Checked on 12 September 2026 against the current introduction and the
homogeneous realizations in Section 2 and Appendix B. This is a source and
convention audit. The initial search did not change the manuscript. At the
user's subsequent request, all three sources were added as background
references, retaining every pre-existing mathematical expression in the
introduction. Three footnotes explain the convention differences documented
below. The bibliography gives the published Taylor and Tao book metadata
and links to the inspected author files; Hunter is cited as lecture notes.

## Recommended primary reference: Taylor

Michael E. Taylor, *Partial Differential Equations I: Basic Theory*, second
edition, Applied Mathematical Sciences 115, Springer, 2011.
[Publisher record and DOI](https://doi.org/10.1007/978-1-4419-7055-8).

The publisher confirms the edition and chapter titles. The actual definitions
were read in the author's publicly available chapter files, linked from his
[PDE course](https://mtaylor.web.unc.edu/notes/pde-course/). Page and equation
locators below refer to those standalone files, not to unverified pagination
in the bound second edition.

| Manuscript convention | Checked passage | Match |
|---|---|---|
| Unitary Fourier transform on R^3 | Chapter 3, Section 3, equation (3.1), standalone p. 25 | Exact after setting n=3: prefactor `(2 pi)^(-n/2)` and exponent `-i x dot xi` |
| Schwartz space | Chapter 3, equation (3.3), p. 25 | Same rapidly decreasing smooth functions |
| Tempered distributions | Chapter 3, Section 4, equations (4.1)–(4.2), p. 32 | Same continuous dual of the Schwartz space |
| Distributional Fourier transform | Chapter 3, equations (4.16)–(4.19), p. 34 | Same extension by duality |
| H^s(R^3), all real s | Chapter 4, Section 1, equations (1.3)–(1.4), pp. 1–2 | Exact set definition: tempered distributions with weighted Fourier transform in L2 |
| H^s norm | Chapter 4, equations (1.5)–(1.7), p. 2; Chapter 3, Proposition 3.2, p. 27 | Exact norm by Plancherel, not merely an equivalent norm |
| Bessel multiplier | Chapter 4, equation (1.5) | Taylor's `Lambda^s` equals the manuscript's `J^s`, not its homogeneous `Lambda^s` |
| Periodic H^s | Chapter 4, Section 3, equations (3.8)–(3.10), p. 14; Chapter 3, Section 1, p. 3 | Same Sobolev scale after coordinate conversion; the displayed weights are not identical |

Taylor writes angular torus coordinates with period `2 pi`, Fourier exponent
`-i k dot theta`, and normalized measure `(2 pi)^(-n) d theta`. Under
`theta = 2 pi x`, the Fourier coefficients coincide with the manuscript's
unit-torus coefficients. The Sobolev weights `(1+|k|^2)^s` and
`(1+4 pi^2 |k|^2)^s` define equivalent norms for each fixed real s; the latter
is the manuscript's spectral convention for the unit-torus Laplacian.
Do not claim literal equality of those two periodic norms.

Saved files:

- `Taylor_PDE_I_Chapter3_Author.pdf`, from
  <https://mtaylor.web.unc.edu/wp-content/uploads/sites/16915/2018/04/fourier.pdf>.
- `Taylor_PDE_I_Chapter4_Author.pdf`, from
  <https://mtaylor.web.unc.edu/wp-content/uploads/sites/16915/2018/04/chap4.pdf>.

## Bochner spaces: Hunter

John K. Hunter, *Notes on Partial Differential Equations*, Appendix 6.A,
*Vector-valued functions*, publicly available from the author's UC Davis
[lecture-note page](https://www.math.ucdavis.edu/~hunter/pdes/pdes.html).
The downloaded chapter is `Hunter_Vector_Valued_Functions.pdf`, from
<https://www.math.ucdavis.edu/~hunter/pdes/ch6A.pdf>.

Definition 6.14 (printed p. 196; PDF p. 2) specifies strong measurability.
Definition 6.27 (printed p. 199; PDF p. 5) gives exactly the manuscript's
integral norm for finite time exponent and essential-supremum norm at infinity.
The following page makes equality almost everywhere explicit. The source
uses a finite interval `(0,T)` and a real Banach space X; the manuscript uses
a general interval I, including `(0,infinity)`. Extending the same definition
to such intervals changes neither the norm formula nor strong measurability.
Using "Banach space" rather than "normed space" in the manuscript would match
the source's setting for the complete Sobolev realizations actually used.

## Homogeneous norm formula: Tao, with an explicit convention conversion

Terence Tao, *Nonlinear dispersive equations: local and global analysis*,
author-hosted draft, Appendix A, printed pp. 329–331 (PDF pp. 211–213).
Read and saved as `Tao_Nonlinear_Dispersive_Equations_Author_Draft.pdf`, from
<https://www.math.ucla.edu/~tao/preprints/chapter.pdf>.
This draft's pagination must not be attributed to the published book without
checking the corresponding edition.

Tao uses the unnormalized Fourier transform `F_T u = integral exp(-ix.xi) u`.
His Appendix A includes the compensating factor `(2 pi)^(-d/2)` in both
Sobolev norms. Since `F_T u = (2 pi)^(d/2) F_ours u`, his displayed norm formulas
become exactly the manuscript's inhomogeneous and homogeneous Fourier norms.
His symbols `|nabla|` and `<nabla>` correspond to the manuscript's `Lambda`
and `J`, respectively.

This verifies the homogeneous norm formula on common elements where it is
finite. It does not justify identifying every possible completion or
distributional realization at every real s. In particular, the manuscript
must retain its explicit low-frequency conventions. Its realized dot-H^{-1}
space, the subcritical positive-order completions, and derivative-level use
of dot-H^{3/2} should not be replaced by an unrestricted statement that all
homogeneous spaces follow one definition in a textbook. For s<=-3/2 in
dimension three, a generic Schwartz function need not have finite homogeneous
norm; the manuscript correctly avoids that assertion in its force scaling.

## Suggested citation placement

1. At the start of the spatial definitions, cite Taylor, Chapter 3,
   Sections 3–4 and Chapter 4, Section 1, specifically for Euclidean spaces
   and the unitary Fourier convention. Keep the manuscript's explicit formulas.
2. Cite Hunter, Appendix 6.A, Definitions 6.14 and 6.27, at the Bochner-space
   paragraph. Specify the source's interval and Banach-space assumptions when
   describing the match in a research record.
3. If adding a homogeneous-space background citation, use Tao's norm formulas
   with the normalization conversion above, while retaining the internal
   references to Section 2 and Appendix B for realizations.

The symbols `L^q_t H^s_x`, `L^q_t L^p_x`, the abbreviation `||.||_p`, and `E_T`
are explicitly defined manuscript notation. Their validity does not require
finding a source using identical typography or the name `E_T`.

## Excluded shortcuts and verification limits

Hunter's separate Fourier appendix uses a different Fourier normalization,
so it was not selected as the primary exact-convention reference for H^s.
Danchin's 2020 course was located, but direct full-text access failed because
of a host certificate problem. The Bahouri–Chemin–Danchin publisher page
provided metadata only. Neither was treated as a verified replacement for
the actual homogeneous realization used here. The source PDFs listed above
were successfully downloaded and processed with `pdftotext`; the displayed
source definitions were inspected. This is not a full audit of the textbooks.

## Follow-up: direct sources for Appendices A and B

The current appendices were read in full for this source audit. Their results
are classical estimates or consequences of classical local theory. The
classification below distinguishes a directly stated source result from a
short deduction under the manuscript's conventions. No appendix was deleted.

### Forced local theory in Appendix A

Terence Tao, *Localisation and compactness properties of the Navier–Stokes
global regularity problem*, Analysis & PDE 6 (2013), 25–107,
DOI [10.2140/apde.2013.6.25](https://doi.org/10.2140/apde.2013.6.25).
The publisher PDF was downloaded and read as
`Tao_2013_Localisation_Compactness_Published.pdf`, from
<https://msp.org/apde/2013/6-1/apde-v6-n1-p02-p.pdf>.

Theorem 5.1 (pp. 48–49) gives forced periodic H1 local existence, uniqueness,
higher spatial regularity, and smoothness. Corollary 5.2 (p. 50) gives the
maximal-development alternative. Theorem 5.4 (pp. 52–53) gives the whole-space
counterpart. Its proof explicitly states that its smoothness argument only
requires initial data in every H^k and force in C_t^j H_x^k for all j,k,
which matches the manuscript's stronger smooth-data assumptions.
The periodic theorem initially uses zero means; Section 3, equations (36)–(38),
explains their removal by a velocity/force transformation. Viscosity is
normalized to one in the source and can be restored by rescaling time and
amplitudes. These are explicit adaptations, not new local existence results.

The exact L2-in-time H2 continuation condition is a short consequence rather
than the verbatim statement of these theorems. For a smooth solution set
Y=||u||_{H1}. The H1 energy estimate and
`||u tensor u||_{H1} <= C ||u||_{H2} ||u||_{H1}` give, after Young's inequality
and regularized division,

`Y' <= C_nu ||u||_{H2}^2 Y + ||f||_{H1}`.

If the manuscript's continuation integral is finite and f is smooth through
the proposed terminal time S, Gronwall gives a uniform H1 bound. The cited
local theory can then be restarted at times approaching S with a common
positive duration. Its higher-order regularity statement makes the extension
smooth in the manuscript's class. This argument works on both domains after
the indicated mean and viscosity reductions. Keeping this brief bridge would
avoid presenting a stronger-looking citation than the source actually states.

### Multiplication and embeddings

- Appendix A's tame product bound follows from Tao's *Nonlinear dispersive
  equations*, Appendix A, Lemma A.8, equation (A.17), together with (A.13),
  H2 embedded in L-infinity in dimension three. The inspected author draft
  places these at printed pp. 338 and 336. Localization in periodic charts
  gives the corresponding torus estimate. Its short direct Fourier proof
  in the manuscript is also sufficient and can be retained for convenience.
- Appendix B's whole-space inequality is exactly the homogeneous Sobolev
  embedding (A.11) in the same source: take d=3, p=2, s=a and
  q=6/(3-2a). Both a=1/2 and a=1 satisfy 0<a<3/2, giving q=3 and q=6.
  The Fourier normalization conversion already recorded above applies.
- For the periodic statement, Michael E. Taylor's *Partial Differential
  Equations III*, Chapter 13, Section 6, Proposition 6.4, equation (6.13),
  supplies the inhomogeneous embedding; the preceding text explicitly
  explains passage to compact manifolds. The author's chapter was downloaded
  as `Taylor_PDE_III_Chapter13_Author.pdf`, from
  <https://mtaylor.web.unc.edu/wp-content/uploads/sites/16915/2018/04/chap13.pdf>.
  The inspected statement and surrounding discussion are on standalone
  pp. 24–25. Take p=2, n=3 and s=1/2 or 1. On the unit torus, removal of
  the zero Fourier mode gives `||v||_{H^a} <= C_a ||v||_{dot H^a}` by the
  explicit spectral-gap inequality already in Appendix B. This yields the
  homogeneous periodic conclusion with its essential zero-mean assumption.
- The derivative estimates in Appendix B follow by applying the a=1/2
  inequality to each derivative and to Lambda v, and the a=1 inequality to
  each derivative, followed by Plancherel. They are consequences, not an
  additional endpoint embedding at a=3/2.

### Role of the OpenAI source

The downloaded OpenAI manuscript was searched and its relevant Section 10
passages were read. Lemma 10.5 is a uniqueness comparison for its compact
reference solution and a smooth bounded-energy competitor. The proof of
Theorem 1.1 in Section 10.4 excludes extension of the constructed solution
using its velocity growth and a standard Sobolev embedding. These passages
do not supply the full forced local theory for arbitrary smooth data in
Appendix A, or the pair of fractional homogeneous embeddings in Appendix B.
Its own Appendices A and B concern the specialized construction and profile
continuation, not the general analytic preliminaries of this manuscript.

Accordingly, classical sources are the appropriate attribution for both
appendices. OpenAI remains the source of the compact blowup input. A shorter
presentation could retain the statements and citations plus the mean,
viscosity, continuation, and homogeneous-realization bridges, without
reproducing the entire classical analytic development.

### Implemented reduction after independent review

The user requested an independent review before editing the appendices.
The reviewer inspected both the source applicability and the complete
replacement drafts; the findings are recorded in
`../logs/APPENDIX_REDUCTION_INDEPENDENT_REVIEW_20260912.md`.
The reviewed reduction has now been applied. Appendix A cites Tao's published
2013 local theory and retains the short multiplication proof, viscosity and
mean transformations, recovery of the pressure gradient from the projected
force, common-interval smoothness, uniqueness, and high-order continuation
estimate. In particular, no scalar-pressure L2 claim is imported for a
general force. Appendix B cites the classical embeddings and retains the
homogeneous realization, spectral gap, and derivative arguments. The
manuscript's definitions and numbered statements are preserved. The
introduction and preliminary roadmap now describe these classical inputs
accurately rather than claiming a full construction of the local theory or
a direct proof of the Sobolev embedding theorem.
