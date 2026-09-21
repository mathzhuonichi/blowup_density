# Independent mathematical audit 1

**Manuscript:** *Density of Forces Producing Navier--Stokes Blowup*  
**Audit date:** 12 September 2026  
**Reviewer:** independent reviewer 1  
**Source basis:** the frozen source set recorded in
`/Users/chizhuoni/Documents/ChatGPT/NS 2/logs/SOL_MAX_AUDIT_SOURCE_MANIFEST_20260912.json`.
The SHA-256 hashes of every audited TeX file and the compiled PDF matched that
manifest at the end of this review. I did not read any prior audit verdict or
any other current reviewer's report.

## Verdict

I found **no confirmed mathematical error and no load-bearing proof gap** in
the main argument. The compact blowup theorem is an external input, as the
manuscript says; its exact stated hypotheses and conclusion match Theorem 1.1
of the saved primary PDF. Conditional on that input, the localization,
parabolic rescaling, divergence-free cutoff, cancellation, force estimates,
density arguments, and critical non-density estimates form a coherent proof
of the two main threshold theorems.

I found three low-severity ambiguities. None changes a theorem after the
intended reading is made explicit:

1. the scaled-force formula evaluates the source force at negative rescaled
   times without explicitly declaring its zero extension;
2. expository statements about grid averages omit the theorem's
   pre-blowup time range; and
3. the abstract says "before" a prescribed time although the defined result
   is breakdown *by* that time and the insertion may be singular exactly at
   the endpoint.

The successful LaTeX build and manuscript checker were used only as structural
checks. They are not evidence for the mathematical verdict.

## Findings

### A1. The negative-time extension of the source force should be declared

- **Status:** ambiguity
- **Severity:** low
- **Locations:**
  - `/Users/chizhuoni/Documents/ChatGPT/NS 2/paper/sections/02-preliminaries.tex`,
    lines 127--153, Lemma `lem:packetenergy`;
  - `/Users/chizhuoni/Documents/ChatGPT/NS 2/paper/sections/03-torus.tex`,
    lines 101--115, equation `eq:scaling`;
  - the same file, lines 135--143, proof of Proposition `prop:scaling`.
- **Evidence and reasoning:** The external force is introduced as
  \(F\in C_c^\infty(\mathbb R^3\times(0,\infty))\). For
  \(0<t<t_\varepsilon=T-\varepsilon^2\), the displayed formula
  \[
    F_\varepsilon(x,t)=\varepsilon^{-3}
    F\!\left((x-x_0)/\varepsilon,(t-t_\varepsilon)/\varepsilon^2\right)
  \]
  has a negative second argument. Lemma `lem:packetenergy` explicitly says
  that \(U\) and \(P\) are extended by zero to negative time, but it does not
  say this for \(F\). The proof later speaks of the force as vanishing at
  negative times, which reveals the intended convention.
- **Why this is not a proof gap:** Compact support in the open set
  \((0,\infty)\) implies that \(F\) vanishes on \(0<t<\tau\) for some
  \(\tau>0\). Its extension by zero to \(t\leq0\) is therefore \(C^\infty\),
  and all scaling identities then hold exactly as written.
- **Impact:** Without the convention, the formula is formally undefined on a
  portion of its asserted positive-time domain. There is no change to the
  construction or any estimate after the canonical extension is stated.
- **Minimal repair:** After fixing \((U,P,F)\), add: "Extend \(U,P,F\) by zero
  to negative times; these extensions are smooth." The existing proof already
  proves the assertion for \(U,P\), and compact temporal support proves it for
  \(F\).

### A2. Grid-average claims in the abstract and discussion lose the precise time qualifier

- **Status:** ambiguity
- **Severity:** low
- **Locations:**
  - `/Users/chizhuoni/Documents/ChatGPT/NS 2/paper/blowup_density.tex`, lines 49--51;
  - `/Users/chizhuoni/Documents/ChatGPT/NS 2/paper/sections/04-whole-space.tex`,
    lines 297--304, Theorem `thm:Rgrid`, and lines 305--323, its proof and
    following interpretation;
  - `/Users/chizhuoni/Documents/ChatGPT/NS 2/paper/sections/05-conclusion.tex`,
    lines 18--22.
- **Evidence and reasoning:** The exact theorem states
  \(A_hu_\varepsilon(t)=A_hv(t)\) and
  \(A_hg_\varepsilon(t)=A_hg(t)\) only for \(0\leq t<T\). The proof subtracts
  the two momentum equations for the two classical velocities, so the proof
  as presented is also a pre-blowup proof. The abstract says simply
  "equality of velocity and force cell averages," the conclusion says that
  the construction "preserves all velocity and force cell averages," and
  the sentence after the theorem says that a procedure receives identical
  force-average data. Because both forces are defined on all of
  \((0,\infty)\), those unqualified formulations can be read as equality of
  the complete force inputs, including after \(T\). That stronger statement
  is neither stated in the theorem nor proved there.
- **Impact:** The theorem and every density conclusion remain correct. The
  issue concerns the advertised scope of the observation statement.
- **Minimal repair:** Add "at every time before \(T\)" to the abstract,
  conclusion, and the interpretive sentence after Theorem `thm:Rgrid`.

### A3. "Before a prescribed time" is inconsistent with the manuscript's endpoint convention

- **Status:** ambiguity
- **Severity:** low
- **Locations:**
  - `/Users/chizhuoni/Documents/ChatGPT/NS 2/paper/blowup_density.tex`, lines 35--38;
  - `/Users/chizhuoni/Documents/ChatGPT/NS 2/paper/sections/02-preliminaries.tex`,
    lines 38--48, equations `eq:singularforces` and `eq:Rsingularforces`;
  - `/Users/chizhuoni/Documents/ChatGPT/NS 2/paper/sections/03-torus.tex`,
    lines 282--334, Theorem `thm:insertion`.
- **Evidence and reasoning:** The abstract describes forces for which
  regularity is lost "before" a prescribed time. The defined singular sets
  use \(T_{\max}\leq T\), and the principal insertion theorem constructs
  \(T_{\max}=T\). Thus the manuscript's mathematical convention is "by
  \(T\)," with equality included.
- **Impact:** This is confined to the abstract; all formal statements and the
  detailed discussion use the correct quantifier.
- **Minimal repair:** Replace "before a prescribed time" by "by a prescribed
  time."

## Rejected concerns and supporting calculations

The items in this section are recorded because they are the most vulnerable
steps in the manuscript. Each concern was tested independently and rejected on
the stated evidence.

### R1. Applicability of the external compact-blowup input

- **Status:** rejected concern
- **Severity if it had failed:** critical
- **Locations:**
  - `/Users/chizhuoni/Documents/ChatGPT/NS 2/paper/sections/01-introduction.tex`,
    lines 11--34, Theorem `thm:packet`;
  - `/Users/chizhuoni/Documents/ChatGPT/NS 2/reference/OpenAI_Finite_Time_Blowup_for_Navier_Stokes.pdf`,
    Theorem 1.1, page 1.
- **Check:** The saved primary source states, for every \(\nu>0\), a force in
  \(C_c^\infty(\mathbb R^3\times(0,\infty);\mathbb R^3)\), smooth velocity
  and pressure on \([0,1)\), zero initial velocity, a common fixed compact
  spatial support for velocity and pressure, uniform \(L^2\) control, and
  unbounded \(L^\infty\) speed as \(t\uparrow1\). It also states the same
  bounded-energy global-competitor consequence reproduced in the manuscript.
  These are exactly the properties used downstream. The manuscript does not
  silently require a stronger initial datum or a different viscosity.
- **Dependency label:** This 166-page construction remains an **external
  assumed theorem**. This audit checked its statement and its application; it
  did not reprove the construction.

### R2. Energy, dissipation, and initial vanishing of the packet

- **Status:** rejected concern
- **Severity if it had failed:** high
- **Location:**
  `/Users/chizhuoni/Documents/ChatGPT/NS 2/paper/sections/02-preliminaries.tex`,
  lines 122--153, Lemma `lem:packetenergy`.
- **Check:** On every \([0,b]\), \(b<1\), compact spatial support justifies
  \[
    \frac12\frac{d}{dt}\|U\|_2^2+\nu\|\nabla U\|_2^2=(F,U).
  \]
  With \(N(t)=\int_0^t\|F(s)\|_2\,ds\), regularized division gives
  \(\|U(t)\|_2\leq N(t)\), and reinsertion gives
  \[
    \|U(t)\|_2^2+2\nu\int_0^t\|\nabla U\|_2^2
       \leq 2\int_0^tN'(s)N(s)\,ds=N(t)^2.
  \]
  Since \(F\) vanishes on an initial interval, this forces \(U=0\) there.
  The equation then gives \(\nabla P=0\); a spatially constant function with
  compact support on \(\mathbb R^3\) is zero. Hence the negative-time zero
  extensions of \(U,P\) are genuinely smooth. No endpoint energy value at
  \(t=1\) is assumed.

### R3. Parabolic exponents and the two force thresholds

- **Status:** rejected concern
- **Severity if it had failed:** critical
- **Locations:**
  - `/Users/chizhuoni/Documents/ChatGPT/NS 2/paper/sections/03-torus.tex`,
    lines 101--156, Proposition `prop:scaling`;
  - `/Users/chizhuoni/Documents/ChatGPT/NS 2/paper/sections/03-torus.tex`,
    lines 213--280, Lemma `lem:correction`;
  - `/Users/chizhuoni/Documents/ChatGPT/NS 2/paper/sections/04-whole-space.tex`,
    lines 55--79, equations `eq:RpositiveScale` and `eq:RnegativeScale`.
- **Independent calculation:** For
  \(F_\varepsilon=\varepsilon^{-3}F(x/\varepsilon,t/\varepsilon^2)\),
  the spatial homogeneous \(H^s\) factor is
  \(\varepsilon^{-3+3/2-s}=\varepsilon^{-3/2-s}\), and the temporal
  \(L^q\) factor is \(\varepsilon^{2/q}\). Thus
  \[
    \|F_\varepsilon\|_{L_t^q\dot H_x^s}
      =\varepsilon^{\,2/q-3/2-s}\|F\|_{L_t^q\dot H_x^s}.
  \]
  The background defect has amplitude \(\varepsilon^{-2}\), so its exponent
  is larger by one. For the velocity,
  \(\varepsilon^{-1}\varepsilon^{3/2}=\varepsilon^{1/2}\) in
  \(L_x^2\), and
  \(\varepsilon^{-2}\varepsilon^{3/2}\varepsilon
  =\varepsilon^{1/2}\) in \(L_{t,x}^2\) for the gradient. These reproduce
  every exponent in the manuscript and give \(s<1/2\) for \(q=1\) and
  \(s<-1/2\) for \(q=2\).
- **Low-frequency boundary:** For \(-3/2<s<0\), a compact smooth profile has
  finite \(\dot H^s\) because its Fourier transform is bounded at zero and
  \(\int_0^1r^{2s+2}\,dr<\infty\). At \(s\leq-3/2\), the proof correctly
  avoids a false homogeneous claim and uses \(H^r\hookrightarrow H^s\) for
  a fixed \(-3/2<r<-1/2\). This also covers the limiting index
  \(s=-3/2\).

### R4. Local vector potential, exact cancellation, and smooth force through blowup

- **Status:** rejected concern
- **Severity if it had failed:** critical
- **Locations:**
  - `/Users/chizhuoni/Documents/ChatGPT/NS 2/paper/sections/03-torus.tex`,
    lines 158--211, Lemma `lem:potential`;
  - the same file, lines 213--341, Lemma `lem:correction` and Theorem
    `thm:insertion`;
  - `/Users/chizhuoni/Documents/ChatGPT/NS 2/paper/sections/04-whole-space.tex`,
    lines 31--53, Theorem `thm:Rinsert`.
- **Vector-potential check:** With \(y=x-x_0\),
  \[
    A=\int_0^1r\,v(x_0+ry,t)\times y\,dr
  \]
  satisfies
  \[
    \nabla_y\times[r\,v(x_0+ry,t)\times y]
      =\frac{d}{dr}[r^2v(x_0+ry,t)],
  \]
  because \(\nabla\cdot v=0\). Integration gives \(\nabla\times A=v\)
  with the sign used in the manuscript.
- **Cancellation check:** On the active packet interval,
  \(\eta_\varepsilon=1\) and \(\theta_\varepsilon=1\) on a neighborhood of
  the fixed packet support, hence
  \(b_\varepsilon:=v+w_\varepsilon=0\) on that neighborhood. Therefore both
  \((b_\varepsilon\cdot\nabla)U_\varepsilon\) and
  \((U_\varepsilon\cdot\nabla)b_\varepsilon\) vanish there. Outside the
  support, \(U_\varepsilon\) and all of its spatial derivatives vanish by
  global smoothness. The cancellation is pointwise, including the support
  boundary; it is not merely an integral cancellation.
- **Smoothness check:** In rescaled variables, \(w_\varepsilon=O(1)\),
  \(\partial_tw_\varepsilon,\Delta w_\varepsilon=O(\varepsilon^{-2})\),
  and the advective correction terms are no worse. The time cutoff is
  supported inside the interval on which the reference is smooth and is flat
  near its endpoints. Consequently \(H_\varepsilon\) is smooth through
  \(t=T\) and is globally zero outside a compact time interval. The packet
  force is globally smooth independently of the velocity's failure to extend.
- **Terminal-time check:** On the packet support,
  \(u_\varepsilon=U_\varepsilon\), so the \(L^\infty\) limsup diverges. A
  classical extension through \(T\) would be bounded in \(H^2\), hence in
  \(L^\infty\), on a compact time neighborhood. Local uniqueness identifies
  such an extension with the constructed solution before \(T\), giving a
  contradiction. Thus the asserted maximal lifespan is exactly \(T\).

### R5. Density quantifiers and preservation of the fixed initial velocity

- **Status:** rejected concern
- **Severity if it had failed:** high
- **Locations:**
  - `/Users/chizhuoni/Documents/ChatGPT/NS 2/paper/sections/03-torus.tex`,
    lines 343--363, Proposition `prop:density`;
  - the same file, lines 559--585, Proposition `prop:projection` and its
    qualification;
  - `/Users/chizhuoni/Documents/ChatGPT/NS 2/paper/sections/04-whole-space.tex`,
    lines 176--180, proof of Theorem `thm:Rmain`.
- **Check:** For each fixed \(a\), reference force \(g\), and radius, the two
  cases \(T_{\max}(a,g)\leq T\) and \(T_{\max}(a,g)>T\) are exhaustive. The
  first uses \(g\) itself. In the second, the solution exists on a slightly
  longer interval and the insertion changes neither \(a\) nor the earlier
  history. Thus the quantifier is exactly
  \(\forall a\,\forall g\,\forall\rho>0\,\exists f\), with \(f\) allowed to
  depend on \(a,g,\rho\). The manuscript explicitly rejects the stronger
  \(\exists f\,\forall a\) reading and distinguishes breakdown by \(T\) from
  exact singularity at \(T\).

### R6. Endpoint non-density on the torus

- **Status:** rejected concern
- **Severity if it had failed:** critical
- **Location:**
  `/Users/chizhuoni/Documents/ChatGPT/NS 2/paper/sections/03-torus.tex`,
  lines 365--519, Proposition `prop:critical`, Corollary `cor:nondensity`, and
  the proof of Theorem `thm:main`.
- **Check:** Removing the mean gives \(u=v+m\), \(m'=\bar g\), and
  \(|m(t)|\leq\rho\). The constant transport \(m\cdot\nabla\) is skew-adjoint
  for all Fourier multipliers used. With
  \(y=\|\Lambda^{1/2}v\|_2\),
  \(z=\|\Lambda^{3/2}v\|_2\), and
  \(b=\|h\|_{\dot H^{1/2}}\), the independently checked estimates are
  \[
    |((v\cdot\nabla)v,\Lambda v)|\leq C yz^2,
    \qquad |(h,\Lambda v)|\leq by.
  \]
  The continuity argument therefore keeps \(y<c\nu\). Testing next with
  \(-\Delta v\) gives
  \[
    (\|\nabla v\|_2^2)'+\nu\|\Delta v\|_2^2
       \leq C\nu^{-1}\|h\|_2^2.
  \]
  Although the \(L_t^2L_x^2\) norm of \(h\) need not be small, it is finite
  for each smooth time-compact force. Poincare's inequality for \(v\), plus
  the bounded mean, gives the \(L_t^2H_x^2\) continuation criterion. Hence a
  nonempty \(L_t^1H_x^{1/2}\) ball around zero is globally regular. Norm
  monotonicity supplies the obstruction for every \(s\geq1/2\).

### R7. The two whole-space endpoint estimates and low frequencies

- **Status:** rejected concern
- **Severity if it had failed:** critical
- **Locations:**
  - `/Users/chizhuoni/Documents/ChatGPT/NS 2/paper/sections/04-whole-space.tex`,
    lines 81--133, Proposition `prop:Rcritical1`;
  - the same file, lines 135--174, Proposition `prop:Rcritical2`.
- **\(L_t^1\dot H_x^{1/2}\) check:** The homogeneous estimate is the same
  critical inequality as on the torus. Smallness of
  \(\|a\|_{\dot H^{1/2}}+\|f\|_{L_t^1\dot H^{1/2}}\) keeps
  \(\|u\|_{\dot H^{1/2}}\) below the absorption threshold. The subsequent
  \(H^1\) estimate controls high frequencies. The ordinary \(L^2\) energy
  estimate separately controls low frequencies, yielding
  \[
    \int_0^S\|u\|_{H^2}^2
      \leq C S K(S)^2+C\nu^{-1}\|\nabla a\|_2^2
       +C\nu^{-2}\int_0^S\|f\|_2^2<\infty.
  \]
- **\(L_t^2H_x^{-1/2}\) check:** Testing with
  \(Ju\), \(J=(I-\Delta)^{1/2}\), is the correct inhomogeneous test. With
  \(Y=\|u\|_{H^{1/2}}\), \(Z=\|\nabla u\|_{H^{1/2}}\), one has exactly
  \(\|u\|_{H^{3/2}}^2=Y^2+Z^2\). Sobolev embedding gives
  \[
    |((u\cdot\nabla)u,Ju)|\leq C YZ(Y^2+Z^2)^{1/2}
       \leq C Y(Y^2+Z^2),
  \]
  and duality gives
  \(|(f,Ju)|\leq B(Y^2+Z^2)^{1/2}\),
  \(B=\|f\|_{H^{-1/2}}\). While \(Y\leq\theta\nu\), absorption and
  Gronwall yield the stated radius of order
  \(\nu^{3/2}e^{-C\nu S}\). The ordinary energy estimate again supplies the
  low-frequency part needed for continuation. Thus the endpoint regular
  neighborhood used for \(q=2\) is valid and is correctly allowed to depend
  on \(S=T\).

### R8. Completed force spaces and the homogeneous \(\dot H^{-1}\) claim

- **Status:** rejected concern
- **Severity if it had failed:** medium
- **Location:**
  `/Users/chizhuoni/Documents/ChatGPT/NS 2/paper/sections/04-whole-space.tex`,
  lines 201--272, Proposition `prop:Renergy`.
- **Check:** The manuscript fixes a concrete Fourier realization of
  \(\dot H^{-1}\), so there is no quotient-by-polynomials ambiguity. Smooth
  compact spatial functions are dense: annular Fourier approximation first
  gives Schwartz functions, and physical cutoff convergence follows from
  \[
    \|k\|_{\dot H^{-1}}^2
      \leq C\|k\|_1^2+\|k\|_2^2,
  \]
  since \(\int_{|\xi|<1}|\xi|^{-2}\,d\xi<\infty\) in dimension three. Simple
  functions and time mollification then give joint spacetime compactness.
  For the insertion, an amplitude-\(\varepsilon^{-a}\) profile has spatial
  \(\dot H^{-1}\) factor \(\varepsilon^{5/2-a}\); the temporal \(L^2\) factor
  is \(\varepsilon\). Hence the packet and correction are respectively
  \(O(\varepsilon^{1/2})\) and \(O(\varepsilon^{3/2})\), as claimed. The
  two-stage approximation of a rough Bochner-space target is logically
  valid because breakdown is asserted only for the final smooth compact
  approximants.

### R9. Bounded-domain insertion and boundary behavior

- **Status:** rejected concern
- **Severity if it had failed:** medium
- **Location:**
  `/Users/chizhuoni/Documents/ChatGPT/NS 2/paper/sections/03-torus.tex`,
  lines 595--657, Corollary `cor:boundary`.
- **Check:** All changes are supported in a fixed interior ball, so the new
  velocity equals the reference in a boundary collar and preserves the
  no-slip condition. For a smooth distribution supported in a fixed
  \(K\Subset\Omega\), choosing a fixed
  \(\chi\in C_c^\infty(\Omega)\) equal to one near \(K\) gives
  \(E_0z=\chi Z\) for every whole-space extension \(Z\). Peetre's inequality
  and Fourier convolution make multiplication by \(\chi\) bounded on
  \(H^s(\mathbb R^3)\) for every real \(s\), with a scale-independent
  constant. This validates the negative-order as well as positive-order
  domain estimates. Classical no-slip uniqueness follows from the standard
  difference-energy identity; the perturbation's unbounded speed excludes a
  smooth continuation through \(T\).

### R10. Finite-grid velocity and force averages

- **Status:** rejected concern
- **Severity if it had failed:** high for Theorem `thm:Rgrid`
- **Location:**
  `/Users/chizhuoni/Documents/ChatGPT/NS 2/paper/sections/04-whole-space.tex`,
  lines 276--321, Theorem `thm:Rgrid`.
- **Geometric check:** A finite union of complete uniform-grid face sets is a
  closed, measure-zero, locally finite union of planes. Its complement
  contains a point with a ball lying in one cell of every grid. Finiteness of
  the grid family is essential and is stated.
- **Velocity-average check:** For a compactly supported divergence-free
  perturbation \(\delta u\) in a cell \(C\),
  \[
     \delta u_j=\nabla\cdot(x_j\delta u),\qquad
     \int_C\delta u_j=0.
  \]
- **Force-average check:** Subtraction of the two momentum equations and the
  divergence theorem gives exactly
  \[
    \int_C\delta g
      =\frac d{dt}\int_C\delta u
       +\int_{\partial C}
        (u_\varepsilon\otimes u_\varepsilon-v\otimes v
          +\delta p I-\nu\nabla\delta u)n\,dS.
  \]
  The first term is zero. The velocity, pressure, and their relevant
  differences vanish near the cell boundary, so the flux is zero. A
  spatially constant pressure gauge contributes
  \(c(t)\int_{\partial C}n\,dS=0\). Thus all stated pre-blowup cell averages
  agree, including every cell of every prescribed grid.

### R11. Classical local theory and Sobolev inputs

- **Status:** rejected concern
- **Severity if it had failed:** critical
- **Locations:**
  - `/Users/chizhuoni/Documents/ChatGPT/NS 2/paper/sections/appendix-a-local-theory.tex`,
    lines 1--157;
  - `/Users/chizhuoni/Documents/ChatGPT/NS 2/paper/sections/appendix-b-embeddings.tex`,
    lines 1--111;
  - `/Users/chizhuoni/Documents/ChatGPT/NS 2/reference/Tao_2013_Localisation_Compactness_Published.pdf`,
    Theorems 5.1 and 5.4 and Corollary 5.2, printed pages 48--53;
  - `/Users/chizhuoni/Documents/ChatGPT/NS 2/reference/Tao_Nonlinear_Dispersive_Equations_Author_Draft.pdf`,
    Appendix A, equation (A.11) and Lemma A.8;
  - `/Users/chizhuoni/Documents/ChatGPT/NS 2/reference/Taylor_PDE_III_Chapter13_Author.pdf`,
    Section 6, Proposition 6.4 and the compact-manifold discussion preceding it.
- **Source check:** Tao's Theorems 5.1(ii)--(iv) and 5.4(ii)--(iv) give the
  cited \(H^1\) local existence, uniqueness, persistence of higher Sobolev
  regularity on the same interval, and smoothness. The proof of Theorem 5.4
  explicitly notes that \(u_0\in H^k\) and
  \(f\in C_t^jH_x^k\) for all \(j,k\) suffice; Schwartz data are not required.
  The manuscript's force classes are bounded into \(H^1\) and integrable into
  every \(H^m\) on each compact time interval, so the hypotheses match after
  applying the Leray projection. The viscosity-one reduction and periodic
  mean-removal formulas were checked directly and have the correct factors
  and signs.
- **Continuation check:** The tame product estimate gives
  \[
    (\|u\|_{H^m})'
       \leq C_{m,\nu}\|u\|_{H^2}^2\|u\|_{H^m}
          +\|f\|_{H^m}.
  \]
  Thus finite \(\int_0^S\|u\|_{H^2}^2\) bounds every higher norm by
  Gronwall. A uniform \(H^1\) bound and a force bounded in \(H^1\) give a
  common positive restart interval from times tending to \(S\), proving the
  stated criterion without a hidden Poincare assumption on \(\mathbb R^3\).
- **Embedding check:** The Euclidean homogeneous embeddings used in the
  critical estimates lie in the valid range \(0<a<3/2\), specifically
  \(\dot H^{1/2}\hookrightarrow L^3\) and
  \(\dot H^1\hookrightarrow L^6\). The manuscript constructs the relevant
  distributional realization and proves the periodic version from the
  inhomogeneous compact-manifold embedding plus the nonzero-mode spectral
  gap. The derived estimates for \(\nabla v\) and \(\Lambda v\) have the
  correct derivative counts.

### R12. Remaining numbered constructions

- **Status:** rejected concern
- **Severity if any had failed:** low to medium, depending on the claim
- **Location:**
  `/Users/chizhuoni/Documents/ChatGPT/NS 2/paper/sections/03-torus.tex`,
  lines 522--734.
- **Check:**
  - The mixed-norm condition \(3/p+2/q>3\) is exactly
    \(\alpha(p,q)>0\); the correction exponent is larger by one.
  - The trajectory closure uses precisely the norm controlled by the packet
    energy and dissipation, and it makes no endpoint-continuation claim.
  - The data-pair projection has quantifier order
    \(\forall a\,\exists f\), which the text states explicitly.
  - The affine variation is affine in the velocity \(U+b\); the force is
    correctly allowed to depend quadratically on \(b\). Because \(b\) is
    supported away from time one, every cross term is smooth and compactly
    supported.
  - Finitely many inserted packets have disjoint spatial supports, so every
    cross-advection term vanishes. The separate limsup in each ball does not
    require a common blowup sequence.
  - For a globally defined conservative force from rest, integration against
    the velocity kills the force term and gives zero energy; the conclusion
    \(u\equiv0\) is valid on both stated domains.

## Coverage matrix

| Audited source | Mathematical content checked | Outcome |
|---|---|---|
| `/Users/chizhuoni/Documents/ChatGPT/NS 2/README.md`, lines 1--49 | claimed manuscript organization, theorem-count and verification scope statements | Organization and stated distinction between structural checking and proof review are consistent; no mathematical dependency imported from the README. |
| `/Users/chizhuoni/Documents/ChatGPT/NS 2/paper/blowup_density.tex`, lines 1--71 | abstract, main advertised thresholds, source inputs, global organization | Threshold summary is accurate; ambiguities A2 and A3 affect only wording. |
| `/Users/chizhuoni/Documents/ChatGPT/NS 2/paper/sections/01-introduction.tex`, lines 1--232 | equation, external theorem, spaces/norms, topology, scaling preview, quantifier summary, contextual citations | External theorem statement matched; norm conventions and preview exponents checked. |
| `/Users/chizhuoni/Documents/ChatGPT/NS 2/paper/sections/02-preliminaries.tex`, lines 1--153 | data classes, maximal lifespan, pressure recovery, local theory, packet energy/dissipation | Valid; A1 concerns only an omitted explicit convention for \(F\). |
| `/Users/chizhuoni/Documents/ChatGPT/NS 2/paper/sections/03-torus.tex`, lines 1--157 | torus threshold theorem, fractional localization, packet scaling | Valid. Difference-integral constants and scale uniformity checked. |
| Same file, lines 158--363 | vector potential, cutoff defect, exact insertion, fixed-data density | Valid. Pointwise cancellation and exact terminal lifespan checked. |
| Same file, lines 365--520 | critical \(H^{1/2}\) estimate, continuation, endpoint non-density | Valid. Mean and low-mode treatment checked. |
| Same file, lines 522--734 | mixed norms, trajectory closure, data projection, bounded domains, affine and multiple insertions, conservative forcing | Valid within the stated scope. |
| `/Users/chizhuoni/Documents/ChatGPT/NS 2/paper/sections/04-whole-space.tex`, lines 1--180 | two whole-space thresholds, insertion, negative norms, both critical estimates | Valid. Critical and limiting indices checked separately. |
| Same file, lines 182--275 | compact/rapid-decay subclasses, completed spaces, \(\dot H^{-1}\), strong closure | Valid. Density of compact smooth spacetime functions and homogeneous scaling checked. |
| Same file, lines 276--323 | finite family of complete Cartesian grids, velocity and force cell averages | Pre-blowup theorem valid; A2 concerns unqualified expository summaries. |
| `/Users/chizhuoni/Documents/ChatGPT/NS 2/paper/sections/05-conclusion.tex`, lines 1--40 | scope, quantifiers, endpoint and observation limitations | Mathematically faithful except the time-range ambiguity A2. |
| `/Users/chizhuoni/Documents/ChatGPT/NS 2/paper/sections/appendix-a-local-theory.tex`, lines 1--157 | products, local existence, viscosity and mean reductions, uniqueness, continuation | Valid and supported by the cited primary theorem statements. |
| `/Users/chizhuoni/Documents/ChatGPT/NS 2/paper/sections/appendix-b-embeddings.tex`, lines 1--111 | Euclidean and torus critical embeddings and homogeneous realizations | Valid; endpoint exponents and spectral-gap conversion checked. |
| `/Users/chizhuoni/Documents/ChatGPT/NS 2/paper/references.tex`, lines 1--84 | all fourteen bibliography entries and their roles | Load-bearing locators checked against saved primary texts; contextual claims sampled as described below. |

## Primary-source verification

| Source | Exact use checked | Result |
|---|---|---|
| `/Users/chizhuoni/Documents/ChatGPT/NS 2/reference/OpenAI_Finite_Time_Blowup_for_Navier_Stokes.pdf`, Theorem 1.1, page 1 | compact smooth force, compact velocity/pressure, zero datum, bounded energy, unbounded speed, each \(\nu>0\) | Exact match. External theorem accepted as an input, not reproved. |
| Same PDF, Lemma 10.3 and proof of Theorem 1.1, printed pages 120--124 | force extension through \(t=1\), compact time support, energy and viscosity conventions | Consistent with the properties used by the manuscript. |
| `/Users/chizhuoni/Documents/ChatGPT/NS 2/reference/Tao_2013_Localisation_Compactness_Published.pdf`, Theorems 5.1, 5.4 and Corollary 5.2, printed pages 48--53 | periodic and whole-space forced \(H^1\) local theory, uniqueness, regularity, maximal development | Applicable after the explicit projection, mean, and viscosity reductions. |
| `/Users/chizhuoni/Documents/ChatGPT/NS 2/reference/Tao_Nonlinear_Dispersive_Equations_Author_Draft.pdf`, Appendix A | homogeneous Sobolev embedding and product estimates | Exponents and uses match. |
| `/Users/chizhuoni/Documents/ChatGPT/NS 2/reference/Taylor_PDE_III_Chapter13_Author.pdf`, Section 6 | inhomogeneous Sobolev embedding and compact-manifold localization | Supports the periodic embedding together with the manuscript's explicit spectral-gap step. |
| `/Users/chizhuoni/Documents/ChatGPT/NS 2/reference/Enciso_PenafielTomas_PeraltaSalas_2025_Published.pdf`, Theorem 1.5, Lemma 2.11, and Section 11.3 | local modification and making the background spatially constant before singular insertion | The cited comparison is accurate and contextual. |
| `/Users/chizhuoni/Documents/ChatGPT/NS 2/reference/HZZ_2024_Navier_Stokes.pdf`, Theorem 1.4, Corollary 4.6 and Theorem 5.1 | deterministic \(L_t^1L_x^2\) density of nonunique Leray--Hopf solutions from rest and existence for each \(L^2_\sigma\) datum | The contextual summary is accurate. |
| `/Users/chizhuoni/Documents/ChatGPT/NS 2/reference/R3ActualCandidate.lean`, lines 18--21, and `/Users/chizhuoni/Documents/ChatGPT/NS 2/reference/R3CompactCandidate.lean`, lines 23--37 | selected compact candidate and recorded support/zero-data properties | The declarations match the limited citation; no Lean build or certification of this article was inferred. |

## Unresolved limits

1. The external 166-page compact-blowup construction was not reproved. All
   positive density statements are conditional on that explicitly cited
   theorem.
2. This was an independent mathematical audit, not a formal proof-assistant
   verification.
3. The bounded-domain corollary assumes existence of a compatible smooth
   reference. It does not prove general bounded-domain local theory.
4. Non-density for nonzero initial velocity at or above the critical orders is
   not claimed and remains outside the classification.
5. Mixed norms outside \(3/p+2/q>3\), infinitely many grids, and grid
   refinement for a fixed perturbation are not classified.
6. I verified the load-bearing source statements and the specific contextual
   comparisons used in the introduction. I did not audit every bibliographic
   item as an independent theorem, because the remaining citations do not
   carry the proof.
7. `make -C paper` and `python3 experiments/check_manuscript.py` completed
   without warnings. Those checks establish build and structural consistency
   only.

## Minimal revision list

1. Explicitly extend \(F\), as well as \(U,P\), by zero to negative times.
2. Qualify every summary of the grid result with \(0\leq t<T\).
3. Change the abstract's "before a prescribed time" to "by a prescribed
   time."

No mathematical theorem needs to be weakened or withdrawn on the evidence of
this audit.
