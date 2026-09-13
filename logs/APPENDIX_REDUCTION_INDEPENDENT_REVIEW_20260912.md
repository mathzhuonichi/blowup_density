# Independent review of the proposed appendix reduction

Date: 12 September 2026.

Scope: independent source-applicability and logical audit of the proposed
replacement of long proofs in Appendices A and B by classical citations and
short convention bridges. The current appendix statements, Proposition 2.1
(`prop:local`), and the downloaded primary sources were inspected. This is
an independent agent review, not formal proof certification. No manuscript
file was edited by this reviewer.

The exact proposed files `tmp/appendix-revision/draft-a.tex` and
`tmp/appendix-revision/draft-b.tex` were subsequently read in full. They
retain the required bridges below and are approved at the stated audit
level. No mathematical gap or unsupported scalar-pressure integrability
claim was found in these drafts. A useful optional clarification is that
the common-interval bounds in every Sobolev order and the projected
equation first give `W^(1,infinity)_t H^k_x`, hence continuity into `H^k`;
the now continuous right-hand side gives `C^1_t H^k_x`, and repeated
differentiation yields every `C^j_t H^k_x` order, with one-sided derivatives
at the initial time. This elaborates the cited regularity argument rather
than adding a new hypothesis.

## Conclusion

The reduction is mathematically appropriate if the bridges below remain.
The general local theory and embeddings should be attributed to classical
sources, independently of the OpenAI blowup construction. Neither a citation
alone nor an unqualified assertion that all source conventions coincide
would be sufficient. Keeping the existing Fourier product proof and
high-order continuation argument is a sound economical choice.

## Appendix A: verified source coverage and retained arguments

1. Tao, *Localisation and compactness properties of the Navier--Stokes global
   regularity problem*, Analysis & PDE 6 (2013), 25--107, Theorem 5.1(ii)--(iv),
   printed pp. 48--49, supplies periodic existence, uniqueness, a common
   interval with all higher `X^k` bounds, and smoothness. Corollary 5.2,
   printed p. 50, supplies periodic maximal development. Theorem 5.4(ii)--(iv),
   printed pp. 52--53, supplies the whole-space counterpart. Corollary 5.2
   should not be described as a whole-space theorem; the same maximal
   construction there follows by patching Theorem 5.4.
2. The source defines `H^1` data with force in `L^infinity_t H^1_x`, although
   the quantitative lifespan estimate uses its `L^1_t H^1_x` norm. The
   manuscript's forces, smooth into every `H^m` on compact intervals, satisfy
   both requirements. Local theory may be restarted on translated intervals;
   the force's compact-interval `H^1` bound gives uniform control of its local
   integral. No global time integrability is needed for this step.
3. Theorem 5.4(iv) is stated for Schwartz data. Crucially, its proof on p. 53
   explicitly permits initial data in every `H^k` and force in `C^j_t H^k_x`
   for every `j,k`. Cite this proof-level extension and explain it, rather
   than describing the theorem statement itself as covering arbitrary
   `H^infinity` data. The higher-order estimates all hold on the same interval;
   one must not intersect unrelated existence intervals for different orders.
4. For the whole-space velocity, applying the source to the projected force
   `P f` is particularly clean. This force retains all stated Sobolev and time
   regularity, and the velocity equation is unchanged. Recover the pressure
   for the original force by the manuscript's gradient formula. Do not import
   an `L^2` scalar-pressure claim for a general unprojected force: the inverse
   derivative in its gradient component can have a low-frequency obstruction.
   The manuscript correctly requires an `L^2` pressure gradient and permits
   the scalar pressure to lie outside `L^2`.
5. For nonzero periodic means retain the explicit transformation
   `m(t) = mean(a) + integral_0^t mean(f)`, `X'(t)=m(t)`, `X(0)=0`,
   `v(t,x)=u(t,x+X(t))-m(t)`. Its force is
   `f(t,x+X(t))-m'(t)` and has zero mean; pressure is translated and remains
   periodic. This agrees with the source's Section 3, equations (36)--(38),
   printed p. 44. At a restart, reinitialize the same transformation from
   the new initial time. Translation preserves spatial Sobolev norms.
6. Restore viscosity by `tau=nu*t`, `v(tau,x)=nu^(-1)u(tau/nu,x)`,
   `p_new=nu^(-2)p(tau/nu,x)`, and `f_new=nu^(-2)f(tau/nu,x)`.
   This preserves the required regularity for each fixed positive viscosity.
7. The retained Fourier product estimate is valid on both domains. Pairing
   the smooth projected equation in `H^m`, using that estimate and Young's
   inequality, yields
   `Y_m' <= C_(m,nu) ||u||_(H^2)^2 Y_m + ||f||_(H^m)` for `m>=3`.
   Regularized norm division handles zeros. Finite `integral ||u||_(H^2)^2`
   therefore bounds every `H^m` up to the proposed terminal time. A bounded
   `H^3` norm in particular bounds the `H^1` norm required by Tao's lifespan
   estimate; the force bound is uniform on a slightly larger compact time
   interval. Restarting sufficiently close to the terminal time produces an
   extension beyond it, and uniqueness identifies the solutions on overlaps.
   Thus the exact manuscript continuation criterion is a proved consequence,
   not a verbatim source theorem. The existing short difference-energy
   uniqueness argument is valid and may remain.

## Appendix B: verified source coverage and retained arguments

- Tao, *Nonlinear dispersive equations: local and global analysis*, Appendix A,
  equation (A.11), gives the Euclidean homogeneous Sobolev estimate. Take
  `d=3`, `p=2`, `s=a` and `q=6/(3-2a)` for `a=1/2,1`; these values satisfy all
  hypotheses. The inspected author draft places this on printed p. 335.
  Equation (A.13) on p. 336 and Lemma A.8, (A.17), on p. 338 also support
  the Euclidean multiplication background. Draft pagination must not be
  represented as independently checked pagination of the published book.
- Retain the Fourier-normalization conversion already documented in the
  introduction. The Euclidean homogeneous realization should remain explicit:
  completing functions whose Fourier transforms are smooth and supported in
  compact annuli identifies an element with `Fourier(v)=|xi|^(-a)G`, `G in L2`.
  The test-function estimate is finite because `2a<3`, yields convergence in
  tempered distributions, and identifies the same limit supplied by the
  `L^q` embedding. This excludes polynomial ambiguity in the chosen realization.
- Taylor, *Partial Differential Equations III*, Chapter 13, Section 6,
  Proposition 6.4, equation (6.13), gives the inhomogeneous embedding, with
  the paragraph immediately preceding Proposition 6.3 explaining transfer
  to compact manifolds. Inspected standalone chapter pp. 24--25. Use that
  compact-manifold consequence for the torus and retain the explicit
  mean-zero spectral-gap inequality converting the manuscript's `H^a` norm
  to its homogeneous norm. No claim of identical periodic norm conventions
  is needed. Fourier truncation then handles distributions with finite norm.
- Keep the derivative argument: apply `a=1/2` to each partial derivative and
  to `Lambda v`, and apply `a=1` to each partial derivative, followed by
  Plancherel. This does not assert the false endpoint embedding
  `dot H^(3/2) -> L^infinity`. Retain the derivative-realization qualification
  for general distributions and the clear inclusion of the smooth
  `H^infinity` fields actually used in the paper.

## Editorial consistency after the reduction

Update the introduction's claim of a "direct proof" of the embeddings and
the preliminary paragraph saying Appendix A "constructs one common H^3
existence interval" if the contraction construction is removed. Appendix B's
title and opening assertion that no Sobolev embedding theorem is assumed
must also change. Preserve the statements and their labels; the deleted
maximal-function and potential-estimate labels currently have no external
uses in the active manuscript. The unchanged original manuscripts should
remain untouched.
