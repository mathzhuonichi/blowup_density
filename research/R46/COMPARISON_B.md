# Proposition 4.6 — independent draft B

## Paper clause → Lean field

| Paper | Lean field | Meaning |
| --- | --- | --- |
| `04-whole-space.tex:219`, first assertion | `REnergyAPI.sobolevDensity` | For every fixed admissible datum and positive ν,T, compact smooth forces with maximal lifespan ≤ T are dense in the full L^q H^s completion, q∈{1,2}, s<2/q−3/2. |
| `04-whole-space.tex:219`, second assertion | `REnergyAPI.homogeneousDensity` | The same set is dense in the full L² dot H⁻¹ completion, using the homogeneous realization. |
| `04-whole-space.tex:221-227` | `REnergyAPI.strongTrajectoryClosure` | After every admissible reference and prescribed ball, choose one insertion family; both the E_T distance and the sum of three force distances tend to zero. |
| `04-whole-space.tex:228` | Compact difference from `A.forceDifference_compact`; homogeneous summand in `strongTrajectoryClosure` | Only g_ε−g is measured in dot H⁻¹; no homogeneous-space membership assumption on g. |

The two limits deliberately share one field and one existential family. Splitting them into independently existential fields would lose simultaneity.

## Completion and realization

Both density fields use the registered `Data.CompletedDenseVia`, **not** `RelativelyDense` or `BreakdownDenseR`. Its quantifier expansion is:

`∀ b : ℝ → RealVectorSobolev s, MemBochnerDatum q s b → ∀ radius > 0, ∃ f ∈ breakdownSetIn forceClassCompact ν a T, ∃ D, path f D ∧ AEStronglyMeasurable D forceTimeMeasure ∧ bochnerDatumENorm q s (D-b) < radius`.

Thus b is any finite strongly measurable Bochner datum, not a physical smooth force or an arbitrary distribution outside the space. The target and radius precede the approximating force. The registered `BochnerPartial.bochnerSpace` is `Lp (RealVectorSobolev s) q forceTimeMeasure`; its `completion*` clauses describe the quotient-by-a.e.-equality interpretation of this path model.

* Nonhomogeneous: `path = IsSobolevPath s`, with weighted Fourier datum G and Fourier transform ⟨ξ⟩⁻ˢG (`04-whole-space.tex:231-235`).
* Homogeneous: q=2, s=−1, `path = IsHomogeneousPath (-1)`, with Fourier transform |ξ|G (`02-preliminaries.tex:58-72`; `04-whole-space.tex:241`). The same Hilbert datum carrier does **not** identify the two physical realizations.

`RealVectorSobolev` carries real vector data with the Euclidean component norm. `forceTimeMeasure` is Lebesgue measure restricted to (0,∞). Radius and norms are ENNReal-valued; no `toReal` conversion of norms is used. The only `toReal` is for the exponent q, explicitly restricted to 1 or 2.

## Strong trajectory closure and quantifiers

The order is `∀ a∈X_R, ∀ν>0, ∀T>0, ∀g∈F_R, ∀δ>0`, reference regularity and classical reference R, then `∀x₀, ∀r>0`, then `∃P, ∃A`. Packet and insertion records are witnesses, never extra assumptions on the caller. A is identified with the prescribed datum, horizon, background force, velocity, pressure and ball. It supplies the registered Theorem 4.2 clauses, including its energy rate and subcritical force convergence, on the same ε-family.

The registered insertion record does not itself carry full `ClassicalSolutionR` membership, `MemForceR` of the inserted forces or exact maximal lifespan. These conclusions are explicitly conjoined for every `0<ε≤A.ε₀`. This prevents interpreting “trajectory” as an arbitrary field or forgetting that the approximating solutions break down at T.

Both limits use `nhdsWithin 0 (Ioi 0)`. The first is the registered `energyENorm T` of the velocity difference, i.e. the sum of L∞(0,T;L²) and L²(0,T;gradient L²) norms. The second is literally a sum of three norms on the force difference over **all** (0,∞). `forceSobolevENorm 1 0` represents L¹_t L²_x via H⁰=L², matching the proof's q=1,s=0 specialization (`:271`). It is not a weak or pointwise closure, and does not impose a value at the singular time T.

No new notion is needed: all predicates, norms, solution types and family records are registered vocabulary. Consequently there are no local copied definitions requiring a “needs registration” flag or an rfl bridge. No unregistered `HomogeneousScalingAPI` or `InsertionLifespanAPI` is used.

## Ambiguities and review points

1. Theorem 4.2 says “regular through T+δ”. The draft spells this literally as `RegularThrough ν a g (T+δ)` and names R on `[0,T+δ)`. The family may use a smaller positive internal margin. Shrinking the existential regularity margin also permits the common formulation with only a solution on `[0,T+δ)`; this equivalence is not proved here.
2. Carrying `InsertionFamilyAPI` preserves the paper's reference to Theorem 4.2 but exposes its packet/correction implementation witnesses. A later public contract could hide those witnesses behind a conclusion-only predicate. This draft does not weaken the imported theorem by merely assuming an insertion family already exists, or strengthen “may arrange” to convergence for every possible family.
3. `IsSobolevPath` and `IsHomogeneousPath` realize every nonnegative time, whereas Bochner equivalence is a.e. on positive times. This is inherited registered vocabulary; only the smooth compact approximant must have such a path. Targets remain arbitrary completed-space elements.
4. No density statement for arbitrary rough-force classical solutions is asserted. No extra corollary from `:274`, quantitative homogeneous scaling estimate from the proof, or grid assertion is added as a proposition field.
5. `HomogeneousPartial` explicitly omits the full homogeneous Bochner assembly, and `Scaling` omits the registered homogeneous scaled estimates. Their absence concerns future proofs, not the statement. Elaboration does not establish an inhabitant of `REnergyAPI`.

## Independence

Only the requested manuscript/registered sources and the R46 blueprint entry were used. No competing draft, `research/section4/STATEMENTS.md`, existing R46/R41 research, or collaboration brief was opened. References to those paths inside permitted contract docstrings were not followed. The referenced Theorem 4.2 statement (`04-whole-space.tex:31-43`) was consulted to fix “every reference”.
