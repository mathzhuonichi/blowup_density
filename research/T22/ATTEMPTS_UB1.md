# T22 U-B1 attempts — restriction bridge

Lane 383, 2026-09-18.

## Result

Both requested declarations close without additional hypotheses:

```lean
theorem restrictDatum_eq_restrictField {Ω s z A}
    (hA : IsSobolevDatum s (zeroExtension Ω z) A) :
    restrictDatum Ω s A = restrictField Ω z

theorem domainSobolevENorm_le_sobolevENorm :
    domainSobolevENorm Ω s (restrictField Ω z) ≤
      sobolevENorm s (zeroExtension Ω z)
```

The first proof applies `hA` to a bundled `DomainTest`, then uses
`setIntegral_eq_integral_of_forall_compl_eq_zero`.  If `x ∉ Ω` and the test
were nonzero at `x`, then `x` would lie in its function support, hence in its
topological support, contradicting `tsupport ψ ⊆ Ω`.  The remaining pointwise
identity is the two branches of `Ω.indicator z`.

The norm proof is only order theory: `le_iInf` fixes an arbitrary whole-space
datum of the zero extension, the restriction theorem makes it an admissible
member of the domain infimum, and `iInf_le_of_le` compares the two copies of
its extended norm.

## Rejected first route

The first integral attempt tried to rewrite the zero-extension integrand by
`integral_indicator`.  Lean reported:

```text
Tactic `apply` failed: could not unify the conclusion of
`setIntegral_eq_integral_of_forall_compl_eq_zero` ...
with the goal
  ∫ x in Ω, ψ x * z x i = ∫ x, ψ x * zeroExtension Ω z x i
```

More importantly, `integral_indicator` requires `MeasurableSet Ω`, which the
reconciled statement deliberately does not assume.  The successful proof
does not need it: it first replaces the domain integral by the full integral
using pointwise vanishing of the test outside `Ω`, and only then compares the
two integrands pointwise.

## Axiom audit

Every canonical T22 declaration and both U-B1 theorems print exactly
`[propext, Classical.choice, Quot.sound]`; see `axioms_ub1.lean`.
