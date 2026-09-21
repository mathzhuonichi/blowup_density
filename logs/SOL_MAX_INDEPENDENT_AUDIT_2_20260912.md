# Independent mathematical audit 2

**Manuscript:** *Density of Forces Producing Navier--Stokes Blowup*  
**Audit date:** 12 September 2026  
**Reviewer role:** second independent reviewer  
**Frozen scope:** paper/blowup_density.tex, paper/references.tex, and all seven files in paper/sections/

## Verdict

I found **no confirmed mathematical error and no unresolved proof gap in the load-bearing argument**, conditional on the explicitly imported compact forced-blowup theorem stated as Theorem 1.1 (label **thm:packet**).

I independently reconstructed the fixed-viscosity scaling, periodic localization, local divergence-free cutoff, exact cancellation of cross-advection terms, correction-force estimates, forced local theory, continuation criterion, periodic mean treatment, both whole-space low-frequency arguments, all three critical estimates, completed Bochner-space density, and endpoint non-density logic. These steps are mathematically coherent as written.

I found two low-severity presentation ambiguities. Neither changes a theorem:

1. The whole-space insertion hypothesis redundantly nests the defined phrase “regular through” inside an existential time margin.
2. The abstract and conclusion do not repeat the grid theorem’s explicit restriction to times before blowup.

This is not a formal certification. The 166-page OpenAI construction is an explicitly imported input; I checked its exact statement and its use here, not its internal construction. I did not consult earlier reviewer verdicts or audit reports. I used the frozen-source manifest only to identify and later verify the reviewed files.

## Finding register

| ID | Status | Severity | Precise location | Reasoning, impact, and minimal repair |
|---|---|---:|---|---|
| A1 | ambiguity | low | paper/sections/02-preliminaries.tex, lines 35--36; paper/sections/04-whole-space.tex, Theorem 4.2 (**thm:Rinsert**), lines 31--33 and 176--179 | “Regular through $S$” means smooth extension past $S$. Because Theorem 4.2 asks for a solution “regular through $T+\delta$ for some $\delta>0$,” shrinking the existential margin makes this equivalent to being regular through $T$; it is not a stronger mathematical assumption. The construction only needs smoothness on a fixed neighborhood of $T$. Repair: use the simpler hypothesis “regular through $T$,” or match Theorem 3.6 and say “smooth on $[0,T+\delta]$ for some $\delta>0$.” |
| A2 | ambiguity | low | paper/blowup_density.tex, lines 49--51; paper/sections/04-whole-space.tex, Theorem 4.7 (**thm:Rgrid**), lines 297--304 and 323; paper/sections/05-conclusion.tex, lines 18--22 | The precise theorem asserts equality of velocity and force cell averages only for $0\le t<T$. This is the proved and natural range: the inserted classical velocity is not defined after $T$, while its force is. The abstract and conclusion omit this qualifier and could be read as claiming force-average equality on the whole positive time axis. The imported theorem does not imply that post-$T$ claim. Repair: add “for $0\le t<T$” or “before blowup” to the two summaries. |

There are no findings with status **confirmed error** or **proof gap**.

## Load-bearing checks

### 1. Imported packet and the derived energy facts

**Status:** rejected concern.  
**Severity:** none.  
**Locations:** paper/sections/01-introduction.tex, Theorem 1.1 (**thm:packet**), lines 15--34; paper/sections/02-preliminaries.tex, Lemma 2.2 (**lem:packetenergy**), lines 122--153.

The saved primary manuscript reference/OpenAI_Finite_Time_Blowup_for_Navier_Stokes.pdf, Theorem 1.1 on p. 1, states exactly the properties reproduced here: for every $\nu>0$, a force in $C_c^\infty(\mathbb R^3\times(0,\infty))$, uniformly compact spatial support for velocity and pressure on $0\le t<1$, zero initial velocity, bounded kinetic energy, and unbounded speed as $t\uparrow1$.

The manuscript correctly derives the two extra facts it needs. Compact support justifies

$$
\frac12\frac{d}{dt}\|U\|_2^2+\nu\|\nabla U\|_2^2
=\langle F,U\rangle .
$$

With $N(t)=\int_0^t\|F(s)\|_2\,ds$, regularized norm division gives $\|U(t)\|_2\le N(t)$ and then

$$
\|U(t)\|_2^2+2\nu\int_0^t\|\nabla U(s)\|_2^2\,ds\le N(t)^2 .
$$

Since $F$ is spacetime compact, this gives finite integrated dissipation up to time one. Compact support in the open time interval also implies $F=0$ near $t=0$; the energy inequality forces $U=0$ there. The equation then gives $\nabla P=0$, and compact spatial support forces $P=0$. Hence the smooth zero extensions used later are justified.

### 2. Scaling and negative-frequency regimes

**Status:** rejected concern.  
**Severity:** none.  
**Locations:** paper/sections/03-torus.tex, **eq:scaling** through **eq:packetHs**, compiled equations (17)--(20), lines 101--156; paper/sections/04-whole-space.tex, **eq:RpositiveScale** and **eq:RnegativeScale**, compiled equations (46)--(47), lines 55--79.

For amplitude $\varepsilon^{-a}$, spatial scale $\varepsilon$, and time scale $\varepsilon^2$,

$$
\|\varepsilon^{-a}h(\,\cdot/\varepsilon,\cdot/\varepsilon^2)\|_
 {L_t^q\dot H_x^s}
=\varepsilon^{\,2/q+3/2-a-s}\|h\|_{L_t^q\dot H_x^s}.
$$

Thus the packet force, with $a=3$, has exponent

$$
\beta(q,s)=\frac2q-\frac32-s,
$$

and the correction, with effective amplitude $a=2$, gains one power of $\varepsilon$. The mixed Lebesgue exponent is

$$
\alpha(p,q)=-3+\frac3p+\frac2q .
$$

Every Navier--Stokes term acquires the common factor $\varepsilon^{-3}$, so the viscosity stays fixed. The velocity energy and dissipation norms both acquire $\varepsilon^{1/2}$.

For $-3/2<s<0$, compact smooth profiles have finite homogeneous norm because their Fourier transform is bounded at zero and $\int_{|\xi|<1}|\xi|^{2s}\,d\xi<\infty$. For $q=2$ and $s\le-3/2$, the manuscript correctly avoids a false homogeneous assertion: it chooses $r\in(-3/2,-1/2)$ with $r>s$ and uses $\|z\|_{H^s}\le\|z\|_{H^r}$. For $q=1$ and all $s<0$, $L^2\hookrightarrow H^s$ suffices. The endpoint exponents are therefore exactly $1/2$ for $q=1$ and $-1/2$ for $q=2$.

The periodic localization lemma, Lemma 3.2 (**lem:localization**), also checks out. The Euclidean and periodic difference integrals use the same $c_s$, with the periodic $2\pi$ frequency retained. Nonzero lattice translates are uniformly bounded because the fixed containing ball has positive distance from the fundamental-cube boundary. The resulting constant is independent of the shrinking support.

### 3. Vector potential, correction, and exact insertion

**Status:** rejected concern.  
**Severity:** none.  
**Locations:** paper/sections/03-torus.tex, Lemmas 3.4--3.5 (**lem:potential**, **lem:correction**) and Theorem 3.6 (**thm:insertion**), lines 158--341; paper/sections/04-whole-space.tex, Theorem 4.2 (**thm:Rinsert**), lines 31--53.

For $y=x-x_0$,

$$
A(x,t)=\int_0^1r\,v(x_0+ry,t)\times y\,dr
$$

has the correct sign. Incompressibility gives

$$
\nabla_y\times\bigl(r\,v(x_0+ry,t)\times y\bigr)
=2r\,v(x_0+ry,t)+r^2(y\cdot\nabla_x)v(x_0+ry,t)
=\frac d{dr}\bigl(r^2v(x_0+ry,t)\bigr),
$$

so $\nabla\times A=v$. Where both cutoffs equal one, $w_\varepsilon=-v$ on an open neighborhood of the complete packet support.

In rescaled variables, $A=\varepsilon\mathcal A_\varepsilon$ and $w_\varepsilon=O(1)$. Hence $\partial_tw_\varepsilon$ and $\Delta w_\varepsilon$ are $O(\varepsilon^{-2})$; the advection corrections are smaller or of the same order. Spatial support has volume $O(\varepsilon^3)$ and temporal support length $O(\varepsilon^2)$, giving the stated energy, mixed-norm, and Sobolev bounds.

Writing $b_\varepsilon=v+w_\varepsilon$, expansion leaves only

$$
(b_\varepsilon\cdot\nabla)U_\varepsilon
+(U_\varepsilon\cdot\nabla)b_\varepsilon .
$$

Both terms vanish. On a neighborhood of $\operatorname{supp}U_\varepsilon$, $b_\varepsilon$ and all its derivatives vanish. Off that support, $U_\varepsilon$ and its derivatives vanish; smoothness covers the support boundary. The new force is smooth through $T$ because it consists of the imported globally smooth packet force and a correction depending only on the smooth reference and cutoffs.

Local uniqueness identifies the constructed velocity with the maximal solution. Any extension through $T$ would be locally bounded in $H^2$, hence in $L^\infty$, contradicting the packet’s unbounded speed. Thus exact terminal time $T$ is established around every regular reference.

### 4. Forced local theory, pressure, viscosity, and common interval

**Status:** rejected concern.  
**Severity:** none.  
**Locations:** paper/sections/02-preliminaries.tex, Proposition 2.1 (**prop:local**), lines 75--120; paper/sections/appendix-a-local-theory.tex, lines 60--126.

The relevant primary-source statements in reference/Tao_2013_Localisation_Compactness_Published.pdf are:

- Theorem 5.1(ii)--(iv), pp. 48--50: periodic $H^1$ local existence, uniqueness, and smooth-data regularity under the mean-zero normalization.
- Corollary 5.2, p. 50: maximal periodic development.
- Theorem 5.4(ii)--(iv), pp. 52--53: the whole-space analogue.
- Section 3, equations (36)--(38), p. 44: the time-dependent Galilean mean transformation.

On each compact interval, the manuscript’s forces are bounded in $H^1$ and integrable in every $H^m$, so they meet the source hypotheses. Tao’s higher-order estimates hold on the same $H^1$-controlled interval. The parenthetical after the proof of Theorem 5.4(iv) explicitly allows $u_0\in H^k$ and $f\in C_t^jH_x^k$ for all $j,k$, rather than Schwartz data; this matches the manuscript’s whole-space class.

The viscosity normalization is correct. Setting

$$
\tau=\nu t,\qquad
\widetilde u(\tau,x)=\nu^{-1}u(\tau/\nu,x),\qquad
\widetilde p(\tau,x)=\nu^{-2}p(\tau/\nu,x),\qquad
\widetilde f(\tau,x)=\nu^{-2}f(\tau/\nu,x)
$$

divides every term by $\nu^2$ and produces viscosity one.

For the periodic mean, define

$$
m(t)=\int_{\mathbb T^3}a+\int_0^t\int_{\mathbb T^3}f,
\qquad X'(t)=m(t).
$$

Then

$$
v(t,x)=u(t,x+X(t))-m(t),\qquad
h(t,x)=f(t,x+X(t))-m'(t)
$$

is Tao’s symmetry (36) with auxiliary velocity $-m$. The reduced initial velocity and force have zero mean, and the time-translation transport cancels the subtracted advecting velocity.

Applying the source theory to $\mathbb P f$ is legitimate. The manuscript’s pressure formulas restore $(I-\mathbb P)f$. On $\mathbb R^3$, the field

$$
G=(I-\mathbb P)\bigl(f-\nabla\cdot(u\otimes u)\bigr)
$$

is smooth, curl-free, and in $L^2$; the radial formula differentiates to $G$. No scalar $L^2$ pressure claim is made.

The common smooth interval follows at the $H^1$ level. Since all higher spatial orders are available on that same interval, the projected equation gives the stated time regularity. This avoids the failure of endpoint time smoothness that can occur for merely pointwise-smooth $H^1$ data lacking all Sobolev derivatives.

### 5. Continuation criterion

**Status:** rejected concern.  
**Severity:** none.  
**Location:** paper/sections/appendix-a-local-theory.tex, **eq:Rhigh** and **eq:highcontinuation**, compiled equations (59)--(60), lines 127--156.

The displayed $L_t^2H_x^2$ condition is not attributed as a verbatim source theorem; the manuscript proves the bridge. For each integer $m\ge3$,

$$
\frac12\frac d{dt}\|u\|_{H^m}^2+\nu\|\nabla u\|_{H^m}^2
\le C_m\|u\|_{H^2}\|u\|_{H^m}\|\nabla u\|_{H^m}
+\|f\|_{H^m}\|u\|_{H^m}.
$$

Young’s inequality and regularized norm division give

$$
\bigl(\|u\|_{H^m}\bigr)'
\le C_{m,\nu}\|u\|_{H^2}^2\|u\|_{H^m}+\|f\|_{H^m}.
$$

Finite $\int_0^S\|u\|_{H^2}^2\,dt$ therefore bounds every $H^m$ norm up to $S$. The bounded $H^1$ restart data and a force bounded in $H^1$ on $[0,S+1]$ give a common positive local duration at times $t_0\uparrow S$. Taking $t_0$ close enough to $S$ yields an interval extending beyond $S$, and uniqueness identifies it with the original solution. No endpoint limit or whole-space Poincaré inequality is missing.

### 6. Periodic critical estimate and mean

**Status:** rejected concern.  
**Severity:** none.  
**Location:** paper/sections/03-torus.tex, Proposition 3.8 (**prop:critical**), lines 365--499; critical energy **eq:criticalenergy**, compiled equation (36); $H^1$ estimate **eq:H1energy**, compiled equation (39).

Write $u=v+m$, where $m$ is the spatial mean. Then $m'=\bar g$, $h=g-\bar g$, and

$$
\partial_tv+(v\cdot\nabla)v+(m\cdot\nabla)v-\nu\Delta v+\nabla p=h.
$$

The constant transport $m\cdot\nabla$ is skew-adjoint and commutes with the Fourier multipliers. With

$$
y=\|\Lambda^{1/2}v\|_2,\qquad
z=\|\Lambda^{3/2}v\|_2,\qquad
b=\|h\|_{\dot H^{1/2}},
$$

testing against $\Lambda v$ gives

$$
\frac12(y^2)'+(\nu-C_0y)z^2\le by.
$$

This follows from $\|v\|_3\lesssim y$ and
$\|\nabla v\|_3+\|\Lambda v\|_3\lesssim z$. Removing the zero mode cannot increase the inhomogeneous force norm, so $\int b\le\|g\|_{L_t^1H_x^{1/2}}$. The strict first-time bootstrap from $y(0)=0$ yields $y\le\rho<c\nu$ throughout the lifespan.

The stronger estimate needed for continuation is

$$
\left|\langle(v\cdot\nabla)v,\Delta v\rangle\right|
\le\|v\|_3\|\nabla v\|_6\|\Delta v\|_2
\lesssim y\|\Delta v\|_2^2.
$$

After absorption,

$$
(\|\nabla v\|_2^2)'+\nu\|\Delta v\|_2^2
\lesssim\nu^{-1}\|h\|_2^2.
$$

The right-hand side is finite because the topology is relative to the smooth time-compact force class; its finiteness is not inferred from smallness of the $L_t^1H_x^{1/2}$ norm. For any finite putative maximal time $S$, the mean contributes only $S\rho^2$, and the mean-zero spectral gap controls $\|v\|_{H^2}$ by $\|\Delta v\|_2$. Proposition 2.1 then continues the solution.

### 7. Whole-space critical estimates and low frequencies

**Status:** rejected concern.  
**Severity:** none.  
**Locations:** paper/sections/04-whole-space.tex, Proposition 4.3 (**prop:Rcritical1**), lines 81--133; Proposition 4.4 (**prop:Rcritical2**), lines 135--174.

For the $L_t^1\dot H_x^{1/2}$ estimate, the homogeneous critical energy inequality controls $y=\|u\|_{\dot H^{1/2}}$. The manuscript handles the missing low frequencies separately:

$$
\|u(t)\|_2\le\|a\|_2+\int_0^t\|f(s)\|_2\,ds=:K(t).
$$

Together with the absorbed $H^1$ estimate and

$$
\|u\|_{H^2}^2\lesssim\|u\|_2^2+\|\Delta u\|_2^2,
$$

this gives finite $L_t^2H_x^2$ norm on every finite interval, even when the homogeneous critical norm is small but the finite $L^2$ norm is large.

For the square-integrable critical force, set

$$
Y=\|u\|_{H^{1/2}},\qquad
Z=\|\nabla u\|_{H^{1/2}},\qquad
B=\|f\|_{H^{-1/2}}.
$$

The exact Fourier identity is

$$
\|u\|_{H^{3/2}}^2=Y^2+Z^2.
$$

The nonlinear factors satisfy

$$
\|u\|_3\lesssim Y,\qquad
\|\nabla u\|_3\lesssim Z,\qquad
\|Ju\|_3\lesssim(Y^2+Z^2)^{1/2}.
$$

For the last bound,

$$
\|Ju\|_{\dot H^{1/2}}^2
=\int|\xi|(1+|\xi|^2)|\widehat u|^2\,d\xi
\le\int(1+|\xi|^2)^{3/2}|\widehat u|^2\,d\xi .
$$

The force pairing is

$$
|\langle f,Ju\rangle|
\le\|f\|_{H^{-1/2}}\|Ju\|_{H^{1/2}}
=B(Y^2+Z^2)^{1/2}.
$$

Consequently, while $Y\le\theta\nu$,

$$
(Y^2)'+\nu Z^2\le C_2\nu Y^2+C_3\nu^{-1}B^2.
$$

Gronwall yields

$$
Y(t)^2\le C\nu^{-1}e^{C\nu S}
\|f\|_{L_t^2H_x^{-1/2}}^2.
$$

A radius of the stated form $c\nu^{3/2}e^{-C\nu S}$ is therefore safely small after renaming constants. The first-time bootstrap is strict. Once $Y$ is small, the $H^1$ absorption applies. Membership in $\mathcal F_{\mathbb R}$ independently supplies finite $L_t^1L_x^2$ and $L_t^2L_x^2$ norms, completing the low-frequency continuation argument.

### 8. Homogeneous realizations and Appendix B

**Status:** rejected concern.  
**Severity:** none.  
**Locations:** paper/sections/02-preliminaries.tex, **eq:homogeneous-realization**, compiled equation (11), lines 50--73; paper/sections/appendix-b-embeddings.tex, Lemma B.1 (**lem:critical-embeddings**), lines 11--110.

For $a\in\{1/2,1\}$, with both orders below $3/2$, the completion of Fourier data supported away from zero in $\|\Lambda^av\|_2$ has the realization

$$
\widehat v=|\xi|^{-a}G,\qquad G\in L^2.
$$

The distributional pairing is finite at zero precisely because $2a<3$. The homogeneous Sobolev embedding selects a unique $L^{6/(3-2a)}$ representative. This construction includes all smooth $H^\infty$ fields used in the paper.

The derivative-level uses of $\dot H^{3/2}$ do not assert the false endpoint embedding into $L^\infty$. They apply the valid $a=1/2$ embedding to $\partial_jv$ and $\Lambda v$, and the $a=1$ embedding to $\partial_jv$.

The torus argument correctly starts with Taylor’s inhomogeneous compact-manifold embedding and then uses the explicit spectral gap on mean-zero distributions. The mean-zero condition is essential and is stated.

The separate realization

$$
\dot H^{-1}
=\{h:\widehat h=F\text{ is measurable and }|\xi|^{-1}F\in L^2\}
$$

is a Hilbert space rather than a seminormed polynomial quotient: the map $h\mapsto|\xi|^{-1}\widehat h$ is an isometric bijection onto $L^2$, and its inverse maps $G$ to $\mathcal F^{-1}(|\xi|G)$. Requiring a measurable Fourier representative excludes distributions supported only at zero.

### 9. Bochner completions, non-density endpoints, and grids

**Status:** rejected concern, except for ambiguity A2 in the summary prose.  
**Severity:** none for the theorems.  
**Locations:** paper/sections/01-introduction.tex, lines 118--150; paper/sections/04-whole-space.tex, Proposition 4.6 (**prop:Renergy**), lines 218--272; paper/sections/03-torus.tex, Theorem 3.1 (**thm:main**), Proposition 3.8 (**prop:critical**), and Corollary 3.9 (**cor:nondensity**); paper/sections/04-whole-space.tex, Theorem 4.1 (**thm:Rmain**); paper/sections/04-whole-space.tex, Theorem 4.7 (**thm:Rgrid**), lines 276--321.

Every inhomogeneous $H^s$ and the specified $\dot H^{-1}$ are separable Hilbert spaces, so the simple-function Bochner approximation is available. The proof supplies all remaining details: frequency truncation and mollification produce Schwartz approximants; physical cutoffs converge in a sufficiently strong integer Sobolev norm; the $\dot H^{-1}$ cutoff is controlled by

$$
\|k\|_{\dot H^{-1}}^2\lesssim\|k\|_1^2+\|k\|_2^2;
$$

and measurable time sets are approximated by compactly supported smooth time functions. The proposition only claims complete-space density for finite $q=1,2$, exactly the range covered.

At the critical indices, the manuscript does not rely on scaling. The regularity propositions give a nonempty relative open ball about zero disjoint from the singular-force set. For stronger orders, monotonicity of the inhomogeneous Fourier weights embeds a small strong-norm ball into the critical regular ball. This proves non-density at and above the threshold. The converse is consistently restricted to zero initial velocity, while positive density is fiberwise for every fixed admissible initial velocity.

The earlier-breakdown quantifier is also correct: a force whose reference solution already breaks down by $T$ is left unchanged, so general density concerns breakdown by $T$. Exact singularity at $T$ is asserted only around references regular through $T$. The extended-data statement preserves the order $\forall a\,\exists f$.

For Theorem 4.7, a point outside the faces of finitely many locally finite Cartesian grids has a ball lying inside one cell of every grid. For compactly supported divergence-free $\delta u$,

$$
\delta u_j=\nabla\cdot(x_j\delta u),
$$

so its integral over each containing cell is zero. Integrating the difference equation over that cell leaves the time derivative of zero plus a boundary flux. All differences vanish near the boundary, and a constant pressure gauge contributes a multiple of $\int_{\partial C}n\,dS=0$. Thus both velocity and force averages agree for every $0\le t<T$.

## Primary-source hypothesis audit

| Source | Checked locator | Role and result |
|---|---|---|
| OpenAI, *Finite Time Blowup for Navier--Stokes* | Theorem 1.1, p. 1; relevant Section 10 completion passages | Exact match to **thm:packet**. The construction remains an imported input. |
| Tao, *Localisation and compactness properties of the Navier--Stokes global regularity problem* (2013) | Section 3, (36)--(38); Theorem 5.1(ii)--(iv); Corollary 5.2; Theorem 5.4(ii)--(iv) and its concluding parenthetical | Hypotheses match after the manuscript’s explicit projection, pressure recovery, viscosity scaling, and mean transformation. The continuation criterion is correctly proved as a consequence rather than quoted verbatim. |
| Tao, *Nonlinear Dispersive Equations*, Appendix A | Equation (A.11); Lemma A.8, equation (A.17) | Applicable to $(p,s,q)=(2,1/2,3)$ and $(2,1,6)$. For $p=2$, the homogeneous norm is the Fourier-multiplier norm used here after the stated normalization conversion. |
| Taylor, *PDE III*, Chapter 13, Section 6 | Discussion preceding Proposition 6.4 and equation (6.13) | Proposition 6.4 is stated on $\mathbb R^n$; the preceding discussion transfers the result to compact manifolds. The manuscript cites both and supplies the zero-mean spectral-gap step. |
| Enciso--Peñafiel-Tomás--Peralta-Salas (2025) | Theorem 1.5; Lemma 2.11; Section 11.3 | The methodological comparison to weak Euler localization and singular insertion is accurate and is not used as a proof dependency. The manuscript correctly distinguishes exterior agreement, convex integration, and Reynolds-stress removal from the present forced classical construction. |
| Hofmanová--Zhu--Zhu (2024) | Theorem 1.4; Corollary 4.6; Theorem 5.1 | The stated deterministic density from rest and the general-data quantifier match the source. Contextual only. |
| Clay problem statement; Guermond--Minev--Shen | Clay equations (4)--(5); GMS Section 2 and Theorem 3.2 | The rapid-decay convention and warning that numerical error estimates require more than energy membership match the cited passages. Contextual only. |

## Coverage matrix

| Component | Material checked | Outcome |
|---|---|---|
| paper/blowup_density.tex | Abstract, scope claims, thresholds, included-file structure | Substantively accurate; see A2. |
| paper/sections/01-introduction.tex | Equation, imported theorem, Fourier/Sobolev/Bochner conventions, roadmap, literature comparisons | No mathematical mismatch found. |
| paper/sections/02-preliminaries.tex | Data classes, lifespans, homogeneous realization, projection, pressure, local theory, packet energy | No error found. |
| paper/sections/03-torus.tex, lines 1--341 | Localization, scaling, potential, correction, exact insertion | Reconstructed; estimates and cancellation are correct. |
| paper/sections/03-torus.tex, lines 343--520 | Density, mean treatment, critical energy, endpoint non-density | Reconstructed; no gap found. |
| paper/sections/03-torus.tex, lines 522--734 | Mixed norms, trajectory closure, data-pair projection, bounded-domain insertion, variations, multiple regions, conservative forces | Quantifiers and calculations are sound. |
| paper/sections/04-whole-space.tex, lines 1--180 | Insertion, negative Sobolev estimates, both critical estimates, threshold theorem | Reconstructed; no gap found; see A1. |
| paper/sections/04-whole-space.tex, lines 182--275 | Compact/rapid classes, duality, complete force spaces, homogeneous density | Density and low-frequency arguments are complete. |
| paper/sections/04-whole-space.tex, lines 276--323 | Theorem 4.7 (**thm:Rgrid**) | The pre-$T$ theorem is correct; see A2 for summary wording. |
| paper/sections/05-conclusion.tex | Summary and limitations | Substantively accurate; see A2. |
| paper/sections/appendix-a-local-theory.tex | Product estimates, Tao 2013 hypotheses, reductions, uniqueness, continuation | Valid source application and deduction. |
| paper/sections/appendix-b-embeddings.tex | Euclidean/periodic embeddings, realizations, spectral gap, derivative estimates | Valid; no false endpoint embedding. |
| paper/references.tex | Every bibliography entry and all load-bearing citation locators | No citation-dependent mathematical error found. |

## Limitations

- This is an independent human-readable audit, not a formal proof or full certification.
- The OpenAI compact-blowup construction was treated as the explicitly imported theorem. Its full construction was not reproved.
- I read the complete saved passages needed for load-bearing citations and sampled contextual citations at their stated locators. I did not conduct a new field-wide novelty search.
- I did not use successful compilation or a format-check command as evidence of mathematical validity.
- The critical regularity results concern the stated relative smooth-force classes. Auxiliary finite norms used for continuation come from class membership; the proofs do not claim analogous results for arbitrary rough forces possessing only the displayed small norm.
