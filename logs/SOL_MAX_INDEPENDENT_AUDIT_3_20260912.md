# Sol Max Independent Mathematical Audit 3

**Date:** 12 September 2026  
**Manuscript:** *Density of Forces Producing Navier--Stokes Blowup*  
**Reviewer:** independent reviewer 3  
**Source snapshot:** the files and hashes frozen in logs/SOL_MAX_AUDIT_SOURCE_MANIFEST_20260912.json

## Independence and scope

I read README.md, paper/blowup_density.tex, all seven files in paper/sections/, and
paper/references.tex. I did not read earlier audit reports, verdicts,
theorem-correspondence judgments, or the reports of the other two reviewers. I
used the source manifest only to identify the frozen snapshot. I checked all 28
numbered mathematical results in the merged manuscript, including their proofs,
dependencies, quantifiers, endpoints, pressure conventions, scalar/vector and
tensor uses, relative topologies, and completion arguments.

The OpenAI blowup theorem is treated as the explicitly imported input requested
for this audit. I checked its exact statement and source status, but I did not
attempt to recertify its 166-page construction. I independently checked the
manuscript's deductions from that input. I also checked the load-bearing
local-theory and Sobolev citations in the saved primary sources, and checked
the contextual citations to the extent recorded in the source-verification
table and limitations below.

## Overall verdict

**Conditional on OpenAI Theorem 1.1 as an imported input, I found no critical
or major mathematical error, no unresolved proof gap in either density
threshold, and no circular dependency in the current manuscript.** The torus
and whole-space if-and-only-if statements have the quantifier scope actually
proved: density below the threshold for every fixed admissible initial
velocity, and the converse only from zero initial velocity. The distinction
between breakdown by \(T\) and insertion with unbounded speed exactly at \(T\)
is also maintained in the theorem statements and proofs.

I found two headline-level scope/terminology problems and three minor
definitional or attribution ambiguities. None changes a numbered theorem once
that theorem is read with its stated hypotheses. They should nevertheless be
corrected because the abstract and conclusion are what many readers will rely
on.

Severity labels below are: **S0 critical**, **S1 major**, **S2 moderate**,
**S3 minor**, and **S4 note**.

## Findings requiring revision

### 1. “Completed energy-force spaces” is undefined and can be read as a stronger product-density result

- **Status:** ambiguity / unsupported headline terminology
- **Severity:** S2 moderate
- **Location:** paper/blowup_density.tex, lines 49--50 (abstract); compare
  paper/sections/04-whole-space.tex, lines 218--272, Proposition
  prop:Renergy, and paper/sections/03-torus.tex, lines 535--557, Corollary
  cor:closure.
- **Current claim:** the abstract says that the construction gives “density in
  completed energy-force spaces.”
- **Reasoning:** no space with that name is defined. Proposition prop:Renergy
  proves density of smooth compact singular forces in the completed **force**
  spaces \(L^q_tH^s_x\) and \(L^2_t\dot H^{-1}_x\). Separately, the
  insertion theorem gives \(E_T\)-closure of singular trajectories around a
  **smooth regular reference trajectory**, with simultaneous convergence of
  the corresponding force differences. The proof does not define or prove
  density in a completed product space containing arbitrary rough forces
  together with associated energy trajectories. An arbitrary element of a
  completed force space need not have a classical reference trajectory to
  which the \(E_T\) assertion can be attached.
- **Impact:** the abstract can be understood as claiming a rough
  force/trajectory product-density theorem stronger than Proposition
  prop:Renergy. The numbered propositions themselves are not affected.
- **Minimal fix:** replace the phrase by, for example, “density of smooth
  compact singular forces in the completed force spaces, together with strong
  \(E_T\) trajectory closure around smooth regular references.”

### 2. The headline cell-average claim omits both its whole-space and pre-blowup scope

- **Status:** confirmed statement/proof scope mismatch
- **Severity:** S2 moderate for the abstract; S3 minor for the conclusion
- **Location:** paper/blowup_density.tex, lines 49--51 (abstract), and
  paper/sections/05-conclusion.tex, lines 18--22; compare
  paper/sections/04-whole-space.tex, lines 297--320, Theorem thm:Rgrid and
  equation eq:gridforce.
- **Current claim:** the abstract states equality of velocity and force cell
  averages “on any prescribed finite family of Cartesian grids,” without a
  domain or time qualifier. The conclusion identifies the whole-space domain
  but again omits the time qualifier.
- **Reasoning:** Theorem thm:Rgrid proves

  \[
  A_hu_\varepsilon(t)=A_hv(t),\qquad
  A_hg_\varepsilon(t)=A_hg(t),\qquad 0\le t<T,
  \]

  on \(\mathbb R^3\). Its proof integrates the difference momentum equation
  and uses the compactly supported velocity and pressure differences. That
  argument is available only before \(T\), when the inserted velocity exists.
  Both forces are defined after \(T\), but the theorem neither states nor
  proves equality of their cell averages there. The rescaled source force may
  retain prescribed smooth values corresponding to source times greater than
  or equal to one, so post-\(T\) equality does not follow from the current
  construction.
- **Impact:** a reader can reasonably interpret the abstract as an all-time
  force-observation claim, or as a claim on both domains. The theorem is a
  whole-space indistinguishability statement for observations up to the
  singular time.
- **Minimal fix:** in the abstract write “on \(\mathbb R^3\), for every
  \(0\le t<T\), on any prescribed finite family of Cartesian grids”; add the
  same time qualifier in the conclusion and in the interpretive sentence at
  paper/sections/04-whole-space.tex, line 323.

### 3. The rescaled force is evaluated at negative source time before its zero extension is explicitly defined

- **Status:** ambiguity with a canonical repair; not a proof gap
- **Severity:** S3 minor
- **Location:** paper/sections/03-torus.tex, lines 101--115, equation
  eq:scaling, and lines 135--143, Proposition prop:scaling; compare
  paper/sections/01-introduction.tex, lines 61--63, and
  paper/sections/02-preliminaries.tex, lines 127--153, Lemma
  lem:packetenergy.
- **Current definition:** \(F_\varepsilon(x,t)=\varepsilon^{-3}
  F((x-x_0)/\varepsilon,(t-t_\varepsilon)/\varepsilon^2)\) is declared for all
  positive \(t\). For \(0<t<t_\varepsilon\), its second argument is negative,
  while Theorem thm:packet initially declares \(F\) only on
  \((0,\infty)\). The text explicitly mentions zero extensions of \(U\) and
  \(P\), but not of \(F\), and the proof later speaks of the force as vanishing
  at negative times.
- **Reasoning:** because
  \(F\in C_c^\infty(\mathbb R^3\times(0,\infty))\), its support has positive
  distance from time zero, so extension by zero to \(t\le0\) is canonical and
  smooth. With that extension, every scaling identity is valid. The current
  formula leaves that harmless step implicit.
- **Impact:** no estimate or theorem fails, but the displayed definition is
  formally outside the stated domain of \(F\) for early target times.
- **Minimal fix:** immediately before eq:scaling, state: “Extend \(U,P,F\) by
  zero to negative times; the extension of \(F\) is smooth because its support
  is compact in \((0,\infty)\).”

### 4. The conclusion grammatically associates the affine family with the periodic/bounded-domain constructions

- **Status:** attribution ambiguity
- **Severity:** S3 minor
- **Location:** paper/sections/05-conclusion.tex, lines 22--24; compare
  paper/sections/03-torus.tex, lines 660--687, Proposition prop:affine, and
  lines 689--713, Proposition prop:multiple.
- **Current claim:** “The additional periodic and bounded-domain constructions
  give prescribed finite collections of singular regions and
  infinite-dimensional families of singular velocities.”
- **Reasoning:** Proposition prop:multiple is the periodic/bounded-domain
  finite-region result. Proposition prop:affine is stated for the whole-space
  packet \(U\) and a cylinder
  \(B_0\times(\tau_0,\tau_1)\subset\mathbb R^3\times(0,1)\). Its proof does
  not explicitly port that affine family to the torus or a bounded domain,
  although such a port is likely routine.
- **Impact:** no theorem is wrong, but the conclusion blurs which domain has
  actually been stated for the affine result.
- **Minimal fix:** split the sentence: “The periodic and bounded-domain
  construction gives finite prescribed collections of singular regions. The
  whole-space packet also admits the infinite-dimensional variations of
  Proposition prop:affine.”

### 5. The localization paragraph should choose the scaling center inside the fixed ball

- **Status:** quantifier/selection ambiguity with an immediate repair
- **Severity:** S3 minor
- **Location:** paper/sections/03-torus.tex, lines 22--30 and 101--105, Lemma
  lem:localization and the setup for equation eq:scaling.
- **Current setup:** \(B\) is fixed, then the text says only to choose \(x_0\)
  “in a torus coordinate ball” and subsequently requires
  \(x_0+\varepsilon K_*\subset B\).
- **Reasoning:** as \(\varepsilon\downarrow0\),
  \(x_0+\varepsilon K_*\) contracts to \(x_0\), so the displayed inclusion for
  all sufficiently small \(\varepsilon\) requires the intended choice
  \(x_0\in B\), preferably with positive distance from its boundary. The later
  insertion theorem clearly permits choosing such a point in the prescribed
  nonempty ball; the proof silently makes that choice.
- **Impact:** none on the construction, but the local setup does not literally
  justify its next “for sufficiently small” requirement for an arbitrary
  point in some coordinate ball.
- **Minimal fix:** replace the sentence by “Fix \(x_0\in B\)” (or choose a
  smaller ball compactly contained in \(B\) and \(x_0\) in that smaller ball).

## Significant concerns examined and rejected

### R1. Exact statement and status of the imported OpenAI theorem

- **Status:** rejected concern
- **Severity:** none within the expressly conditional scope of this audit
- **Location:** paper/sections/01-introduction.tex, lines 11--34, Theorem
  thm:packet; paper/references.tex, lines 42--51.
- **Reasoning:** the saved official PDF
  reference/OpenAI_Finite_Time_Blowup_for_Navier_Stokes.pdf, Theorem 1.1 on
  page 1, states for every \(\nu>0\): a force in
  \(C_c^\infty(\mathbb R^3\times(0,\infty);\mathbb R^3)\); smooth \(u,p\) on
  \([0,1)\); zero initial velocity; a common compact spatial support for
  \(u,p\); uniformly bounded \(L^2\) velocity; unbounded \(L^\infty\) limsup
  at time one; and the stated no-global-bounded-energy consequence. The
  manuscript retains all these hypotheses and conclusions and does not change
  the viscosity.

  The cited item is accurately labeled “Manuscript, 166 pp.” The frozen
  citation points to official repository revision
  8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538. The copied
  R3ActualCandidate.lean, lines 5--10 and 18--21, expressly says that its
  extracted compact candidate does not itself claim the comparator
  nonexistence conclusion. The manuscript uses that Lean citation only for the
  compact witness/properties and expressly disclaims formal certification of
  this article. The current official repository describes its broader
  formalization review status as “self-assessed”; that current metadata does
  not enlarge what the pinned citation proves.
- **Impact:** the article is conditional on a very recent external theorem,
  but it states that dependence rather than concealing it.
- **Minimal fix:** none required. “Taking Theorem 1.1 as an external input”
  would make the logical status even more conspicuous.

### R2. Energy and dissipation of the compact packet

- **Status:** rejected concern
- **Severity:** none
- **Location:** paper/sections/02-preliminaries.tex, lines 122--153, Lemma
  lem:packetenergy and equation eq:packetenergy.
- **Reasoning:** compact spatial support justifies the exact energy identity.
  Regularizing division gives
  \(\|U(t)\|_2\le N(t)=\int_0^t\|F(s)\|_2\,ds\). Substitution yields
  \[
  \|U(t)\|_2^2+2\nu\int_0^t\|\nabla U\|_2^2\le N(t)^2,
  \]
  because \(2\int_0^tN(s)N'(s)\,ds=N(t)^2\). This proves finite
  dissipation. Since the source force vanishes near zero, the same estimate
  forces \(U=0\) there; then \(\nabla P=0\), and compact pressure support
  forces \(P=0\).
- **Impact:** the \(E_T\) convergence rests on a valid derived property, not
  on an unquoted part of the imported theorem.
- **Minimal fix:** none.

### R3. Parabolic exponents and low-frequency Sobolev estimates

- **Status:** rejected concern
- **Severity:** none
- **Location:** paper/sections/03-torus.tex, lines 101--156, Proposition
  prop:scaling; paper/sections/04-whole-space.tex, lines 55--79, equations
  eq:RpositiveScale and eq:RnegativeScale; lines 264--270 for the homogeneous
  \(\dot H^{-1}\) calculation.
- **Reasoning:** velocity, pressure, and force amplitudes scale as
  \(\varepsilon^{-1},\varepsilon^{-2},\varepsilon^{-3}\), respectively, at
  fixed viscosity. A force therefore gains
  \(\varepsilon^{-3+3/p+2/q}\) in \(L^q_tL^p_x\) and
  \(\varepsilon^{2/q-3/2-s}\) in a homogeneous
  \(L^q_t\dot H^s_x\) norm. These exponents give the stated \(1/2\) and
  \(-1/2\) thresholds. For \(-3/2<s<0\), compact smooth profiles have finite
  homogeneous norm because \(r^{2s}r^2\,dr\) is integrable at zero. For
  \(s\le-3/2\), the proof correctly switches to an inhomogeneous norm of a
  larger index instead of asserting a false generic homogeneous estimate. At
  \(s=-1\), an amplitude \(\varepsilon^{-a}\) has spatial
  \(\dot H^{-1}\) factor \(\varepsilon^{5/2-a}\), and the \(L^2_t\) factor is
  \(\varepsilon\), giving \(\varepsilon^{1/2}\) for the packet force and
  \(\varepsilon^{3/2}\) for the correction.
- **Impact:** the threshold exponents and completed homogeneous-space
  convergence are consistent.
- **Minimal fix:** none.

### R4. Sign of the local vector potential and nonlinear cross terms

- **Status:** rejected concern
- **Severity:** none
- **Location:** paper/sections/03-torus.tex, lines 171--211, Lemma
  lem:potential and equations eq:potential--eq:bgzero; lines 282--341,
  Theorem thm:insertion.
- **Reasoning:** for
  \(A(y)=\int_0^1r\,v(x_0+ry)\times y\,dr\), direct differentiation gives
  \[
  \nabla_y\times\bigl(r\,v(x_0+ry)\times y\bigr)
   =\frac{d}{dr}\bigl(r^2v(x_0+ry)\bigr),
  \]
  so \(\nabla\times A=v\), with the sign used in the manuscript. On the
  active packet support, both cutoffs equal one and
  \(w_\varepsilon=-v\) on an open neighborhood. Hence
  \(b_\varepsilon=v+w_\varepsilon\) and its spatial derivatives vanish
  there. Outside the support, the smooth compact packet and its derivatives
  vanish. Both cross-advection terms therefore vanish pointwise, including at
  the support boundary. The residual \(H_\varepsilon\) has the correct
  vector-valued expansion; no missing scalar pressure correction is needed
  because the smooth residual is allowed to enter the force.
- **Impact:** the insertion equation is exact, rather than an approximate
  gluing identity.
- **Minimal fix:** none.

### R5. Exact terminal time and maximal-solution identification

- **Status:** rejected concern
- **Severity:** none
- **Location:** paper/sections/03-torus.tex, lines 327--340, Theorem
  thm:insertion; paper/sections/04-whole-space.tex, lines 44--53, Theorem
  thm:Rinsert.
- **Reasoning:** the constructed solution exists smoothly on every compact
  subinterval of \([0,T)\), so its maximal lifespan is at least \(T\). Local
  uniqueness identifies it with the maximal solution for its data. On the
  packet support the corrected background is exactly zero, so the global
  \(L^\infty\) norm dominates the packet norm and has unbounded limsup as
  \(t\uparrow T\). Any smooth extension through \(T\) in the manuscript's
  class would be bounded in \(H^2\) on a compact interval around \(T\), hence
  bounded in \(L^\infty\), a contradiction. Thus the lifespan is exactly
  \(T\), not merely at most \(T\).
- **Impact:** the two-case density proof correctly changes the conclusion to
  “by \(T\)” only when it leaves an already earlier-breaking reference
  unchanged.
- **Minimal fix:** none.

### R6. Periodic critical estimate, including nonzero spatial mean

- **Status:** rejected concern
- **Severity:** none
- **Location:** paper/sections/03-torus.tex, lines 365--499, Proposition
  prop:critical and equations eq:criticalenergy, eq:ybound, and eq:H1energy.
- **Reasoning:** writing \(u=v+m\) gives \(m'=\bar g\) and adds the
  skew-adjoint transport \(m(t)\cdot\nabla v\), which vanishes in both energy
  identities. The mean satisfies
  \(|m(t)|\le\|g\|_{L^1_tH^{1/2}_x}\). Testing with \(\Lambda v\) yields
  \[
  \tfrac12(y^2)'+(\nu-Cy)z^2\le b\,y,
  \]
  because the homogeneous mean-zero \(H^{1/2}\) norm controls \(L^3\). The
  continuity argument keeps \(y=\|v\|_{\dot H^{1/2}}\) below the absorption
  threshold. The subsequent \(H^1\) estimate may have a large but finite
  \(\int\|h\|_2^2\): smallness is needed only for the nonlinear coefficient.
  It supplies \(L^2_tH^2_x\) on every finite putative lifespan, while the mean
  contributes only \(S\rho^2\). The continuation criterion then gives global
  regularity.
- **Impact:** the open regular ball at \(s=1/2\) is valid even though the force
  need not be mean zero.
- **Minimal fix:** none.

### R7. Whole-space endpoint estimates at \(L^1_tH^{1/2}_x\) and \(L^2_tH^{-1/2}_x\)

- **Status:** rejected concern
- **Severity:** none
- **Location:** paper/sections/04-whole-space.tex, lines 81--174,
  Propositions prop:Rcritical1 and prop:Rcritical2.
- **Reasoning:** the homogeneous \(L^1_t\dot H^{1/2}_x\) estimate controls the
  scale-critical \(y=\|u\|_{\dot H^{1/2}}\); the ordinary energy estimate
  separately controls low frequencies and makes continuation inhomogeneous.
  For the square-integrable force, testing with \(Ju\) is the correct
  \(H^{1/2}\) energy identity:
  \[
  \|u\|_{H^{3/2}}^2=Y^2+Z^2,\qquad
  Y=\|u\|_{H^{1/2}},\quad Z=\|\nabla u\|_{H^{1/2}}.
  \]
  The dual force term is bounded by
  \(B(Y^2+Z^2)^{1/2}\), with \(B=\|f\|_{H^{-1/2}}\). The three \(L^3\)
  factors in the convection term are controlled by \(Y\), \(Z\), and
  \((Y^2+Z^2)^{1/2}\). Absorption and Gronwall give a sufficient radius of
  the stated form \(c\nu^{3/2}e^{-C\nu S}\), after adjustment of universal
  constants. Large higher force norms affect the finite continuation bound
  but need not be small.
- **Impact:** the non-density argument at and above \(s=-1/2\) is supported;
  the radius correctly depends on \(T\).
- **Minimal fix:** none.

### R8. Local theory, pressure, viscosity, and continuation are not circular

- **Status:** rejected concern
- **Severity:** none
- **Location:** paper/sections/02-preliminaries.tex, lines 75--120,
  Proposition prop:local; paper/sections/appendix-a-local-theory.tex, lines
  1--157.
- **Reasoning:** Tao's published 2013 Theorems 5.1(ii)--(iv) and
  5.4(ii)--(iv) give the forced \(H^1\) local existence, uniqueness, and
  smoothness framework used here. The source uses viscosity one and a periodic
  mean-zero normalization. The manuscript's changes
  \[
  \tau=\nu t,\quad \widetilde u=\nu^{-1}u,\quad
  \widetilde p=\nu^{-2}p,\quad \widetilde f=\nu^{-2}f
  \]
  correctly restore arbitrary fixed viscosity, and its time-dependent
  Galilean translation correctly removes and restores the periodic means.
  Applying the local theory to \(\mathbb P f\) is legitimate. On
  \(\mathbb R^3\), the manuscript recovers
  \(\nabla p=(I-\mathbb P)(f-\nabla\cdot(u\otimes u))\), and the radial
  integral of the curl-free smooth vector field gives a scalar potential
  without asserting \(p\in L^2\).

  The additional criterion
  \(\int_0^S\|u\|_{H^2}^2<\infty\) is proved in the manuscript, not
  attributed verbatim to Tao. The tame product estimate yields a Gronwall
  coefficient \(C\|u\|_{H^2}^2\), after which the source \(H^1\) local
  interval can be restarted uniformly. The Sobolev lemma is sourced
  independently in Appendix B, so the density theorem is not used to prove
  its own local theory.
- **Impact:** pressure gradients, means, and viscosity match the equations
  used later.
- **Minimal fix:** none.

### R9. Homogeneous realizations and density in the completions

- **Status:** rejected concern
- **Severity:** none
- **Location:** paper/sections/02-preliminaries.tex, lines 50--73, equation
  eq:homogeneous-realization; paper/sections/04-whole-space.tex, lines
  218--272, Proposition prop:Renergy.
- **Reasoning:** the chosen \(\dot H^{-1}\) realization is a separable Hilbert
  space: \(h\mapsto |\xi|^{-1}\widehat h\) is isometric onto \(L^2\), and
  \(G\mapsto\mathcal F^{-1}(|\xi|G)\) is tempered. The proof of compact-smooth
  density first uses annular Fourier approximation and then a physical
  cutoff. For the cutoff tail \(k\),
  \[
  \|k\|_{\dot H^{-1}}^2\le C\|k\|_1^2+\|k\|_2^2
  \]
  is valid in dimension three because
  \(\int_{|\xi|<1}|\xi|^{-2}\,d\xi<\infty\). Time simple functions can be
  approximated by compact smooth time bumps because \(q=1,2<\infty\). The
  final two-stage approximation proves density of the smooth singular subset
  in the full Bochner completion; it does not define breakdown for rough
  target forces, and the manuscript explicitly says so.
- **Impact:** the completion theorem is stronger than a relative-density
  statement but is supported by a complete density argument.
- **Minimal fix:** none, apart from Finding 1's abstract terminology.

### R10. The bounded-domain insertion does not need a global arbitrary-data existence theorem

- **Status:** rejected concern
- **Severity:** none
- **Location:** paper/sections/03-torus.tex, lines 595--657, Corollary
  cor:boundary.
- **Reasoning:** the reference solution is assumed. All modifications are
  compactly supported in a fixed interior ball, so the equation is verified
  locally and the no-slip trace is unchanged. The quotient \(H^s(\Omega)\)
  norm and fixed interior cutoff give a scale-independent comparison with
  zero extension for every real \(s\). To rule out a smooth continuation of
  the constructed branch, one needs only classical uniqueness on common
  intervals, supplied by the displayed difference-energy calculation with
  vanishing boundary terms; any putative extension would then agree before
  \(T\) and contradict the packet's unbounded speed. A theorem asserting
  existence for arbitrary bounded-domain data is not used.
- **Impact:** the corollary is conditional on the explicitly assumed
  compatible smooth reference, as it should be.
- **Minimal fix:** none. One extra sentence spelling out the extension
  contradiction would make the last inference more self-contained.

### R11. Affine variations, multiple regions, and conservative forces

- **Status:** rejected concern
- **Severity:** none
- **Location:** paper/sections/03-torus.tex, lines 659--734, Propositions
  prop:affine, prop:multiple, and prop:conservative.
- **Reasoning:** for compactly supported divergence-free \(b\) away from
  times zero and one, the force in eq:affine is exactly the residual of
  \(U+b\), and every new term is supported where \(b\) is supported; hence
  the singular endpoint is unchanged. Countably many disjoint spatial
  supports give an infinite-dimensional vector space of admissible \(b\)'s,
  and its translate gives the stated affine family of velocities. For
  finitely many inserted packets, pairwise disjoint supports annihilate all
  cross-advection terms, and orthogonality gives the finite
  energy/dissipation sums. Finally, a force \(-\nabla\phi\) does no work
  against a divergence-free periodic or no-slip velocity; the zero-data
  energy identity therefore forces \(u=0\). The periodic-potential qualifier
  correctly excludes constant forces represented only by nonperiodic affine
  potentials.
- **Impact:** these variants introduce no hidden interaction or pressure
  terms.
- **Minimal fix:** none, apart from the domain attribution in Finding 4.

### R12. Contextual citations do not carry hidden proof obligations

- **Status:** rejected concern
- **Severity:** none
- **Location:** paper/sections/01-introduction.tex, lines 44--59 and
  208--221; paper/sections/04-whole-space.tex, lines 182--216 and 276--286;
  paper/references.tex, lines 2--84.
- **Reasoning:** the published Enciso--Peñafiel-Tomás--Peralta-Salas article
  states the weak Euler localization/singular-set result described in the
  introduction; Section 11.3 explicitly first replaces the local background
  by a spatially constant field. Hofmanová--Zhu--Zhu Theorem 1.4 states
  density of deterministic forces giving nonunique Leray--Hopf solutions in
  \(L^1(0,1;L^2)\) from rest and existence of such a force for each
  divergence-free \(L^2\) datum. Fefferman equations (4)--(5) match the
  manuscript's Schwartz initial class and rapid-decay force seminorms. Tao's
  2018 Theorem 45 is an unforced, mean-zero, periodic small critical-data
  result, and the manuscript describes it only as precedent.
  Guermond--Minev--Shen and Berselli--Spirito are used only to distinguish
  energy spaces from stronger numerical or forcing hypotheses. None of these
  citations is substituted for a step in the insertion or endpoint proofs.
- **Impact:** no citation changes the regularity class or logical force of a
  numbered theorem.
- **Minimal fix:** none.

## Quantifier, topology, and dependency audit

| Claim | Quantifiers/topology actually proved | Audit result |
|---|---|---|
| Torus \(L^1_tH^s_x\) density | For each fixed \(a\in\mathcal X_{\mathbb T^3}\), density for \(s<1/2\); iff only for \(a=0\) | Correctly stated in Theorem thm:main and qualified afterward |
| Whole-space \(L^q_tH^s_x\), \(q=1,2\) | For each fixed \(a\in\mathcal X_{\mathbb R}\), density below \(s_q=2/q-3/2\); iff only for \(a=0\) | Correctly stated in Theorem thm:Rmain |
| Relative topology | Smooth classes carry the subspace topology from the displayed norm; no test-function topology is claimed | Correct and used consistently |
| Breakdown time | Exact \(T\) only around a reference regular beyond \(T\); arbitrary-force density concerns \(T_{\max}\le T\) | Correctly separated |
| Initial-data projection | \(\forall a\,\exists f\), not \(\exists f\,\forall a\) | Correctly stated and proved fiberwise |
| Completed inhomogeneous force spaces | Smooth compact singular forces are dense in the full \(L^q_tH^s_x\) completion below threshold | Correct; rough targets are not assigned classical solutions |
| Completed homogeneous force space | \(L^2_t\dot H^{-1}_x\) uses the explicitly fixed no-polynomial realization | Correct |
| Trajectory closure | \(E_T\)-closure is around smooth regular references and imposes no endpoint value | Correct; abstract terminology should be narrowed |
| Cell observations | A finite family of complete whole-space grids, coordinatewise on every cell, for \(0\le t<T\) | Correct theorem; headline qualifiers are missing |

The logical dependency chain is acyclic:

1. imported OpenAI packet;
2. independent classical local theory, multiplication, and Sobolev embeddings;
3. packet energy/dissipation and zero extension;
4. localization, parabolic scaling, and local vector-potential cutoff;
5. exact insertion and subcritical density;
6. independent critical regularity balls;
7. the two if-and-only-if classifications;
8. completion, grid, bounded-domain, and variation corollaries.

The non-density arguments do not use the blowup packet, and the local theory
does not use either density theorem.

## Full manuscript coverage matrix

| File and current line range | Material checked | Result |
|---|---|---|
| README.md, 1--49 | manuscript scope, source claims, build claims | No mathematical overclaim beyond the abstract issues identified above |
| paper/blowup_density.tex, 1--71 | macros, theorem environments, abstract, assembly, AI declaration | Builds cleanly; Findings 1--2 concern abstract scope |
| paper/sections/01-introduction.tex, 1--232 | equation, imported theorem, spaces, topology, roadmap, literature comparisons | Imported statement and conventions match sources |
| paper/sections/02-preliminaries.tex, 1--153 | data classes, lifespan, homogeneous realization, projection/pressure, local proposition, packet energy | Correct under the stated classes |
| paper/sections/03-torus.tex, 1--157 | threshold statement, fractional localization, scaling | Correct; Findings 3 and 5 are setup clarifications |
| paper/sections/03-torus.tex, 158--364 | vector potential, correction bounds, exact insertion, density | Exact equation and exponents verified |
| paper/sections/03-torus.tex, 365--520 | critical regularity, non-density, theorem completion | Mean and endpoint estimates verified |
| paper/sections/03-torus.tex, 522--734 | mixed norms, closures, bounded domain, affine/multiple/conservative variants | Mathematically supported; Finding 4 concerns attribution |
| paper/sections/04-whole-space.tex, 1--180 | two thresholds, negative Sobolev estimates, endpoint regularity, main proof | Both thresholds and low-frequency arguments verified |
| paper/sections/04-whole-space.tex, 182--275 | compact/rapid classes, energy-force pairings, completed spaces | Completion proof verified; Finding 1 concerns its summary |
| paper/sections/04-whole-space.tex, 276--323 | grid definitions and identical observations | Valid on its stated pre-\(T\), whole-space scope |
| paper/sections/05-conclusion.tex, 1--40 | scope, sharpness, limitations | Findings 2 and 4 require wording changes |
| paper/sections/appendix-a-local-theory.tex, 1--157 | multiplication, local theory reductions, uniqueness, continuation | Source applicability and deductions verified |
| paper/sections/appendix-b-embeddings.tex, 1--111 | homogeneous realizations, spectral gap, derivative embeddings | Correct for \(a=1/2,1\); no endpoint-\(L^\infty\) claim |
| paper/references.tex, 1--84 | all 14 entries, locators, roles, source type | No load-bearing citation mismatch found |

## Source verification record

| Source | Passage checked | Application result |
|---|---|---|
| OpenAI, *Finite Time Blowup for Navier--Stokes* | official saved PDF, Theorem 1.1, p. 1; official repository metadata | Exact imported statement matches; external proof not recertified |
| Tao, *Localisation and compactness properties...* (2013) | Theorem 5.1(ii)--(iv), Corollary 5.2, Theorem 5.4(ii)--(iv), equations (36)--(38) | Supports forced \(H^1\) local theory after explicit reductions |
| Tao, *Nonlinear Dispersive Equations* | Appendix A, (A.11), (A.13), Lemma A.8 | Supports Euclidean embeddings/product background |
| Taylor, *PDE III* | Chapter 13 compact-manifold discussion and Proposition 6.4/(6.13) | Supports torus embeddings; manuscript supplies spectral gap |
| Taylor, *PDE I* | Chapter 3 (3.1), (3.3), Section 4; Chapter 4 (1.3)--(1.7) | Fourier and Sobolev conventions match stated caveats |
| Hunter, *Notes on PDE* | Appendix 6.A, Definitions 6.14 and 6.27 | Strong measurability and Bochner norms match |
| Enciso--Peñafiel-Tomás--Peralta-Salas (2025) | Theorem 1.5, Lemma 2.11, Section 11.3 | Methodological comparison is accurate |
| Hofmanová--Zhu--Zhu, arXiv:2309.03668v2 | Theorem 1.4 and Sections 4--5 | Deterministic density/general-data summary is accurate |
| Fefferman, Clay problem statement | equations (4)--(5) | Rapid-decay comparison is accurate |
| Tao, 254A Notes 1 | Theorem 45 | Correctly cited as unforced periodic precedent |
| Guermond--Minev--Shen | Section 2 and Theorem 3.2 | Contextual numerical distinction is accurately limited |
| Berselli--Spirito; Fujita--Kato | contextual roles | No proof depends on an unavailable passage |

Primary online status checks used the official OpenAI repository and its pinned
revision rather than third-party commentary:

- <https://github.com/openai/NavierStokesAndEuler>
- <https://github.com/openai/NavierStokesAndEuler/tree/8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538>
- <https://cdn.openai.com/pdf/32d9f210-8b73-45e0-91bc-82a30aef8a9a/navier-stokes.pdf>

## Mechanical validation

I copied the frozen paper/ tree to a temporary directory and ran its make
target with TeX Live 2025. The document compiled in 30 pages after the normal
reruns, with no unresolved references, undefined citations, duplicate labels,
overfull/underfull boxes, or other LaTeX warnings in the final log. I then ran
a copied experiments/check_manuscript.py against that temporary build. It
reported five main sections, 34 source results consolidated into 28 merged
results, 106 labels, 14 bibliography entries, and no warnings. These are
structural checks, not evidence of mathematical correctness; the mathematical
conclusions above come from the independent line-by-line audit.

## Limitations

1. The OpenAI theorem's 166-page proof was deliberately not rederived, in
   accordance with the audit instructions. Every conclusion here is
   conditional on that imported theorem.
2. The current official Lean repository presents broader current claims than
   the frozen pinned witness, but I did not build or certify that repository.
   I used the pinned local Lean excerpts only to check that the manuscript does
   not overstate what its specific citation records.
3. The saved Fujita--Kato item is publisher metadata rather than full text, and
   a complete local Berselli--Spirito PDF was unavailable. Both are contextual
   citations; all analytic claims needed in proofs are proved in the
   manuscript or supported by the fully inspected Tao and Taylor sources.
4. This is an independent human-readable proof audit, not a formal
   verification of the merged article. Absence of a detected error should not
   be represented as formal certification.

## Recommended disposition

The manuscript's numbered density, non-density, insertion, completion, and
observation results are ready to proceed **conditional on the imported OpenAI
theorem**. Before circulation, revise the five items above, especially the two
abstract-level scope statements. Those edits require no change to a proof or
numbered theorem.
