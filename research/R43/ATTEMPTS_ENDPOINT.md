# Lane 223 — endpoint attempts

## Successful route

The starting tree already contains `R43/MaximalEndpoint.lean`. Its
`maximal_h2TimeIntegral` applies `C01.h2TimeIntegral_Ioc` at every shorter
horizon using a fixed terminal-S budget and then uses
`C01.lintegral_Ioo_le_of_Ioc` (countable directed union). Thus G5 needed no
new convergence theorem. The budget is
`32*S*energyBudget a f S^2 + 32*ν⁻¹*gradientSq a +
32*(ν⁻¹)^2*∫₀ˢ l2Sq(f(t))`; at zero datum the middle term vanishes and
`energyBudget` becomes `forcePrimitive`. All terms are real and finite;
force-square integrability is proved upstream from `MemForceR`.

The explicit radius is
`min (1/(8*trilinearConst)) (1/(4*(A05.gradientL6Const*A05.criticalL3Const)))`.
Its positivity, strict bootstrap threshold, and absorption inequality are
proved separately. Lane 221 bounds the forcing primitive, the bootstrap
bounds each classical slice, and A05's homogeneous datum norm identity bridges
the L³ embedding to the real critical norm. The maximal family is accessed
only at horizons strictly beyond the time under consideration.

`maximal_squaredHTwoIntegral_of_small_force` supplies exactly the last premise
of `A04.lifespanInfiniteOfLocallyFinite_of_memForceR'`. `exists_maximal'`
supplies the family and positive lifespan. Homogeneous smallness is proved
first. G2 gives the final inhomogeneous statement without a changed threshold.
The conformance file also proves the statement in `Contracts.V1.Data`
vocabulary, using the existing lifespan bridge for the two solution structures.

## Baseline dependency mismatch and resolution

The brief names `A04/RestartFixedForce.lean` and `A04/ShiftedExtension.lean`,
but neither was in this checkout. Searches across Section4 D01/A03/A04/A01/C01
found only the older conditional continuation API. Both requested files exist
in local branch `erenup/217-A04-shifted-extension` at
`d6f9cfd605041cb015a2119d351b6d77578c6b18`. They were copied with `git show`,
unchanged, as new files, and committed separately. No existing Lean module,
branch merge, rebase, push, or other worktree was changed. The two imports build
successfully. This supplies the requested unconditional theorem rather than
introducing a fallback continuation hypothesis.

## Failed elaboration attempts and fixes

- Rewriting A05's embedding with R43's D01 norm identity failed:
  `Did not find an occurrence ... D01.dotHomogeneousENorm`.
  A05 has a separately named datum-infimum definition. Use
  `A05.u1_dotHomogeneousENorm_eq` on the same homogeneous datum; no numerical
  or analytic comparison is needed.
- `field_simp` in the absorption arithmetic left
  `C₁*Cemb/(C₁*Cemb) = 1`. Finish with `div_self hp.ne'`, where `hp` is the
  strictly positive product; merely adding the product to `field_simp` did not
  close this normalization goal.
- The zero-force example's `zero_le _` resolved to an implicit-argument lemma;
  use `bot_le`. Its norm simplification needs the definition
  `D01.Homogeneous.bochnerDatumENorm` explicitly unfolded.

## Scope and validation

No fallback hypothesis remains. The optional general-initial-datum bootstrap
and `RCritical1API.universal` are not claimed. Existing Lean modules were not
edited. The two requested research status documents were updated.

All 12 authored module declarations and the Data conformance theorem print
exactly `[propext, Classical.choice, Quot.sound]`. The zero-force example
constructs a zero datum path, proves the actual smallness premise, and applies
the endpoint theorem. No heartbeat override is needed in `Endpoint.lean`.
Full commands and outcomes are in `REPORT_223.md`.
