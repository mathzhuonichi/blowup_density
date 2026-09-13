# Three independent Sol Max reviews: synthesis and adjudication

Date: 12 September 2026.

## Outcome

Three separately dispatched reviewers, each using `gpt-5.6-sol` with reasoning
effort `max`, independently read the current manuscript and reconstructed its
proofs. Each found no confirmed error invalidating a numbered theorem and no
unresolved gap in the main proof dependencies, **taking the explicitly cited
OpenAI Theorem 1.1 as an external input**. The primary agent independently
checked the main calculations and reviewed every reported finding before
preparing this synthesis.

The actionable findings concern omitted conventions, parameter selection, and
the precision of summary prose. Six clarifications are recommended below;
two additional wording changes are optional. None presently requires weakening
a numbered theorem. These are not six counterexamples or six proof gaps.
The reviewers' agreement is not formal verification, and this review did not
reprove the external 166-page blowup construction.

The manuscript and its PDF were kept unchanged during this audit. Proposed
repairs are recorded here for a subsequent focused revision.

## Review protocol and records

All three reviewers were instructed to read the abstract, five main sections,
both appendices, and bibliography. They were prohibited from consulting prior
review verdicts or each other's reports before finalizing their own findings.
Each reviewed the entire paper; their additional emphases were:

| Reviewer | Additional emphasis | Independent record |
|---|---|---|
| 1 | Local insertion, scaling, support and time extension, density quantifiers, boundary and grid constructions | [Audit 1](SOL_MAX_INDEPENDENT_AUDIT_1_20260912.md) |
| 2 | Forced local theory, continuation, critical estimates, low frequencies, homogeneous and Bochner spaces, source applicability | [Audit 2](SOL_MAX_INDEPENDENT_AUDIT_2_20260912.md) |
| 3 | Notation, domains, time endpoints, parameter scope, abstract/conclusion claims, dependency circularity | [Audit 3](SOL_MAX_INDEPENDENT_AUDIT_3_20260912.md) |

[The source manifest](SOL_MAX_AUDIT_SOURCE_MANIFEST_20260912.json) records SHA-256
hashes for the nine active TeX files and the 30-page PDF. Every final comparison
matched. The review reports contain detailed coverage and source-verification
matrices. A short follow-up with reviewer 3 addressed the bounded-domain
parameter declaration after its independent report had been finalized.

The primary agent corrected inaccurate compiled locators in reviewer 2's draft
by requesting a check against `output/pdf/blowup_density.aux`; the finalized report uses
the correct result numbers and global equation numbers. The substantive
judgments below are reasoned adjudications, not a count of reviewer votes.

## Recommended clarifications

### C1. Explicitly extend the source force to nonpositive time

**Classification:** missing explicit domain convention; minor.  
**Reported by:** reviewers 1 and 3; independently confirmed by the primary agent.  
**Locations:** `paper/sections/03-torus.tex:101–115`, equation (17),
`eq:scaling`; `paper/sections/02-preliminaries.tex:127–153`, Lemma 2.2.

For $0<t<t_\varepsilon$, the formula for $F_\varepsilon$ evaluates $F$ at
$(t-t_\varepsilon)/\varepsilon^2<0$. Its declared domain is positive source
time. Lemma 2.2 explicitly extends $U,P$, but not $F$, by zero. The later
scaling proof already uses the intended zero extension of $F$.

There is a canonical valid repair: compact support strictly inside positive
time gives an interval near zero on which $F=0$, so its zero extension is
smooth. No estimate changes.

Suggested text immediately before equation (17):

> We also extend $F$ by zero to nonpositive times; this extension is smooth
> because its temporal support is compact in $(0,\infty)$. Together with the
> zero extensions of $U,P$ from Lemma 2.2, this makes the following formulas
> well defined at every target time for which they are used.

### C2. Choose the scaling center in the fixed localization ball

**Classification:** incomplete selection instruction; minor.  
**Reported by:** reviewer 3; independently confirmed.  
**Location:** `paper/sections/03-torus.tex:101–104`.

The text chooses $x_0$ in an unspecified coordinate ball, then requires
$x_0+\varepsilon K_*\subset B$ for sufficiently small $\varepsilon$. That
inclusion is guaranteed by choosing $x_0$ inside the fixed ball $B$; an
arbitrary point in another coordinate ball does not suffice. Since the center
is freely chosen, this is a setup clarification, not an existence obstruction.

Replace the center-selection sentence by:

> Fix $x_0\in B$.

For $R_*:=\sup_{y\in K_*}|y|<\infty$, choosing
$\varepsilon R_*<\operatorname{dist}(x_0,\partial B)$ then justifies the
inclusion explicitly.

### C3. Keep the domain and pre-blowup time range in every grid summary

**Classification:** summary-scope ambiguity; highest editorial priority in
this review, not a false numbered theorem.  
**Reported by:** all three reviewers.  
**Locations:** `paper/blowup_density.tex:49–51`;
`paper/sections/05-conclusion.tex:18–22`;
`paper/sections/04-whole-space.tex:323`. Compare Theorem 4.7,
`thm:Rgrid`, at `paper/sections/04-whole-space.tex:297–320`.

The theorem asserts equality on $\mathbb R^3$ for $0\le t<T$. The abstract
does not repeat either qualification, and the conclusion and interpretive
sentence do not repeat the time range. Because the forces are defined after
$T$, a reader could mistake this for equality of the complete all-time force
observations. The velocity is only constructed before $T$.

The missing all-time statement cannot be deduced from the declared packet
hypotheses. To see this, take a smooth time bump $\chi$ supported in $(1,2)$,
a compact smooth spatial function $\psi$ with nonzero integral, and a nonzero
constant vector $e$. Replacing the imported force by

$$
F^\sharp(x,\sigma)=F(x,\sigma)+\chi(\sigma)\psi(x)e
$$

changes none of the packet equations or hypotheses before source time one.
It can, however, change the rescaled force average after target time $T$.
Thus post-$T$ equality is not guaranteed by the input used in this paper.
This argument challenges only an overbroad reading of the summaries, not
Theorem 4.7 itself.

Suggested summary:

> On $\mathbb R^3$, the velocity and force cell averages agree for every
> $0\le t<T$ on any prescribed finite family of Cartesian grids.

Restrict the subsequent deterministic-procedure interpretation to observations
on this same interval.

### C4. Name the completed force spaces rather than an undefined combined phrase

**Classification:** terminology ambiguity; minor.  
**Reported by:** reviewer 3; accepted with a narrower interpretation.  
**Location:** `paper/blowup_density.tex:49–50`; compare Proposition 4.6,
`prop:Renergy`, at `paper/sections/04-whole-space.tex:218–272`.

The phrase "completed energy-force spaces" can naturally mean force spaces
appropriate to energy estimates. It is therefore not itself an explicit claim
of density in an arbitrary force/trajectory product space. Nevertheless, no
space with that combined name is defined, and the phrase is avoidably unclear.

The actual results are distinct: density of smooth compact singular forces in
the specified completed force spaces; and strong $E_T$ trajectory closure
around smooth regular references, with simultaneous convergence of force
differences. They do not assign a classical trajectory to every rough force
in a completion.

Suggested text:

> The construction also gives strong trajectory approximation in energy and
> dissipation, and density of smooth compact singular forces in the stated
> completed force spaces.

### C5. Attribute the two further constructions to their stated domains

**Classification:** imprecise summary attribution; minor.  
**Reported by:** reviewer 3.  
**Location:** `paper/sections/05-conclusion.tex:22–24`; compare Propositions
3.15 and 3.16 at `paper/sections/03-torus.tex:660–713`.

Proposition 3.16 states the multiple-region construction on the torus and
bounded domains. Proposition 3.15 formulates the affine velocity family for
the whole-space packet. The conclusion grammatically attributes both results
to the periodic and bounded-domain constructions.

Compactly supported affine variations can themselves be scaled and placed
inside the other domains by the same local argument, so this is not evidence
that such families cannot exist there. The concise repair is to summarize the
results in the domains in which they were actually stated:

> The periodic and bounded-domain construction gives finite prescribed
> collections of singular regions. The whole-space packet also admits the
> infinite-dimensional variations of Proposition 3.15.

### C6. Bind the positive time margin in the bounded-domain corollary

**Classification:** standalone parameter-scope omission; minor.  
**Raised by:** the primary agent; assessed in a targeted follow-up by reviewer 3.  
**Location:** Corollary 3.14, `paper/sections/03-torus.tex:627–644`.

The statement uses $T+\delta$ without locally saying that $\delta>0$.
Earlier insertion statements explicitly quantify this positive margin. The
bounded-domain proof reuses their choice $2\varepsilon^2<\delta$ to keep
the correction inside the given reference interval. State the intended
margin in this corollary as well; no new argument is needed under that
intended hypothesis.

Suggested opening:

> Suppose that, for some $\delta>0$, $(v,\pi,g)$ is a smooth no-slip
> solution on $\overline\Omega\times[0,T+\delta]$ ...

## Optional wording changes and rejected overinterpretations

### O1. "Before" versus "by" the prescribed time

Reviewer 1 recommends changing "before a prescribed time" in
`paper/blowup_density.tex:35–38` to "by a prescribed time", consistently with the
defined set $\{T_{\max}\le T\}$. This is sensible terminology alignment.
It is not a counterexample to the abstract's qualitative density claim:
strictly-before-$T$ density also follows by applying the theorem at any
$T'<T$, while the regular critical ball excludes breakdown at every time
at or before $T$. The specific insertion displayed in the paper is at $T$,
so "by" remains the clearest wording.

### O2. Nested use of "regular through"

Reviewer 2 identifies the wording "regular through $T+\delta$ for some
$\delta>0$" in Theorem 4.2. Given the definition, this is equivalent to
"regular through $T$" after shrinking the existential margin. It does not
strengthen the actual hypothesis or invalidate the two-case density proof.
Using the latter wording, or "smooth on $[0,T+\delta]$ for some
$\delta>0$", is an optional simplification.

### No missing general bounded-domain local-existence theorem

An early concern was that Corollary 3.14 needed an additional bounded-domain
local theory to justify the exact singular time. That concern was rejected
independently by the reviewers and by the primary agent. The reference is
assumed and the new branch is explicit on $[0,T)$. Any smooth continuation
through $T$ would agree on every common compact interval by the no-slip
difference-energy argument. It would be bounded on a closed spacetime slab,
contradicting the constructed unbounded speed. One may spell out this
contradiction, but no arbitrary-data existence theorem is needed here.

## Mathematical checks retained in the reports

The independent reports give detailed calculations; the central checks are:

| Dependency | Verified content and scope |
|---|---|
| External packet | Exact statement of OpenAI Theorem 1.1, including compact force, compact velocity/pressure, zero data, fixed positive viscosity, bounded energy and unbounded speed; its internal construction is imported |
| Energy and initial vanishing | $\|U(t)\|_2^2+2\nu\int_0^t\|\nabla U\|_2^2\le(\int_0^t\|F\|_2)^2$; this supplies finite dissipation and initial zero intervals |
| Local vector potential | Differentiating $r\,v(x_0+ry)\times y$ gives the $r$ derivative of $r^2v(x_0+ry)$, with the correct curl sign |
| Exact insertion | Both cross-advection terms vanish pointwise because the modified reference vanishes on a neighborhood of the packet support |
| Scaling | Force exponent $2/q-3/2-s$; correction has one extra power of $\varepsilon$; both packet energy/dissipation norms scale by $\varepsilon^{1/2}$ |
| Classical local theory | Tao 2013 Theorems 5.1/5.4 apply on a common $H^1$-controlled interval after mean/viscosity reduction and projection of the force |
| Whole-space pressure | Recover the original force's gradient part; no unsupported scalar-pressure $L^2$ condition is imposed |
| Continuation | The high-order estimate has integrable coefficient $C_{m,\nu}\|u\|_{H^2}^2$; bounded $H^1$ data and locally bounded force give a uniform restart interval |
| Critical $L^1$ estimates | Small critical velocity norm absorbs convection; the torus mean and whole-space low frequencies are handled separately |
| Critical $L^2H^{-1/2}$ estimate | With $Y=\|u\|_{H^{1/2}}$ and $Z=\|\nabla u\|_{H^{1/2}}$, $\|u\|_{H^{3/2}}^2=Y^2+Z^2$ gives the sufficient radius $c\nu^{3/2}e^{-C\nu S}$ |
| Negative orders | Homogeneous scaling for generic compact profiles is used only above $-3/2$; lower inhomogeneous orders follow by norm monotonicity |
| Completions | The specified $\dot H^{-1}$ realization is Hilbert, compact smooth spatial approximation is valid, and the finite-$q$ Bochner approximation gives joint spacetime compactness |
| Quantifiers | Fiberwise density for every fixed initial velocity; converse only at zero initial velocity; exact $T$ near regular references and breakdown by $T$ for general references |
| Grid averages | Finite grid family, compact divergence-free perturbation, zero cell velocity integral, and zero difference-momentum boundary flux for $t<T$ |

The primary agent also reopened the current [official OpenAI PDF](https://cdn.openai.com/pdf/32d9f210-8b73-45e0-91bc-82a30aef8a9a/navier-stokes.pdf)
and checked its first-page statement against the local copy. The published
Tao theorem statements and their proof-level smoothness extension were read
in the saved publisher PDF. The [current HZZ version record](https://arxiv.org/abs/2309.03668)
still identifies version 2 of 10 September 2024; its deterministic comparison
was checked in the saved full text. These source checks do not certify the
external constructions.

## Validation and remaining limits

The existing manuscript checker passed with five main sections, 34 source
results represented by 28 retained numbered results, 106 labels, 14 references,
and no LaTeX warnings. Reviewers also reported successful compilation, including
an isolated temporary build by reviewer 3. These checks establish document
integrity; the mathematical assessment comes from the proof reconstructions.

No source or PDF hash changed during this review. The primary agent added the
source manifest and this synthesis, the reviewers wrote their reports, and
the log index was updated. No manuscript revision, commit, publication, or
Lean certification was performed.

The principal remaining limitation is the imported compact-blowup theorem:
this audit verifies the article's use of that theorem, not its 166-page proof.
Agreement among three runs of the same model can leave shared blind spots.
Accordingly, the correct disposition is **no detected invalidating error in
the reviewed proof, with the explicit clarifications above**, not a guarantee
that the article is error-free.

## Subsequent implementation

The user subsequently authorized applying C1-C6 and checking that the revised
language preserved the intended mathematical objects. Those changes are now
implemented; see [the revision record](REVISION_20260912.md) and
[the targeted post-edit semantic review](POST_REVISION_SEMANTIC_REVIEW_20260912.md).
The independent reports and frozen manifest above continue to identify the
pre-edit version. This implementation note does not retroactively change their
review scope.
