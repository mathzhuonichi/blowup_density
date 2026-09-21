# B3 attempts

Scope: abstract real functions; no spatial norm bridges or B0 modules imported.
P6 remains Partial. Initial implementation uses the one-sided FTC inequality,
which needs an integrable upper bound, not an integrable derivative.
Barrier route: differentiate -(1+Y)^(-2), folding F into C(1+F).
Only authorized existing-file edits: entrypoints.json, P6_SPLIT.md, and the
required refreshed AXIOM_AUDIT.json. New internal unit needs no article contract.

## Closed steps

1. `enstrophy_integrated_of_bound`: one-sided FTC applied to the upper bound
   C(1+M)^3+CF-cZ. Only Z needs compact integrability. Committed separately.
2. `enstrophy_reciprocal_barrier`: differentiation of -(1+Y)^(-2), using
   CF≤CF(1+Y)^3, gives a constant derivative upper bound 2C(1+F).
   The interior-only FTC avoids assuming a derivative at the initial endpoint.
3. `enstrophy_uniform_barrier`: d=1/(4C(1+F)(1+K)^2), M=2(1+K)-1.
   Reciprocal comparison yields (1+Y)^2≤2(1+K)^2, hence the stated height.
   The existential choices precede all intervals/functions. Negative S is
   harmless (empty closed interval); integrated API explicitly assumes S≥0.
4. `enstrophy_endpoint_lintegral`: exhaust Ico a b by Ico a q for rational q<b,
   a countable directed union. No measurability needed for this lemma.
5. `enstrophy_endpoint_integral`: converts locally integrable real integrals
   to nonnegative integrals, obtains a finite endpoint lintegral, proves endpoint
   integrability, then converts back. Measurability alone plus totalized real
   integral bounds would be insufficient; local integrability is explicit.
6. Combined uniform barrier/dissipation API and probes: constant Y, zero Z;
   actual cubic solution Y(t)=(sqrt(1-2t))⁻¹-1, C=c=1, K=F=0; endpoint Z=0.

## Resolved elaboration issues

- `HasDerivAt.one_div` is not the API in this pin: used `.inv` with the
  derivative Pow/Inv imports, then reciprocal algebra.
- `convert` exposed equalities between real module instances; `convert!`
  and explicit denominator nonvanishing closed the derivative identity.
- `integrableOn_Icc_iff_integrableOn_Ico.mpr` was parsed as an unknown constant;
  parenthesizing the theorem applies its default finite-endpoint argument.
- The integral subtraction rewrite needed an explicit lambda `change`.

No remaining Lean errors; no new assumptions about spatial norm carriers.
No article-level Closed markers, contracts or registry entries changed: this
is an internal unit of the still-Partial H¹ restart obligation.
