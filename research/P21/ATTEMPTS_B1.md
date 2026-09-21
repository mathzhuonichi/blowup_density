# B1 attempts — lane 504

Scope: general whole-space enstrophy inequality, no critical smallness. B0 norm
bridges remain explicit hypotheses; no B0 modules are created. P6 stays Partial.

Read COMMON_PHASE5, ASSESSMENT, REPORT_499, project verification documentation,
A02.Restrict and the C01 energy/enstrophy identities. The raw identity controls
physical gradient energy, not the inhomogeneous registered Fourier norm.

1. Added physical L² and gradient identities, retaining both dissipation and
   both force terms. Closure build of C01.EnstrophyIdentityRaw passed.

Existing-file edits: entrypoints.json registers the new module as required.
2. Closed Hölder with exponents 6,3,2 by adapting the existing C01 proof.
   First compile exposed namespace shadowing of `SpatialField`; fixed with
   explicit `Space → Space`. No analytic assumption was added.
3. Closed L³ interpolation for any measurable normed-valued field via weighted
   Hölder with weights 3/4,1/4 on |g|²,|g|⁶. The first rpow rewrite incorrectly
   requested nonzero norms; `rpow_add_of_nonneg` handles zero and infinity.
4. Closed velocity L⁶ ≤ C gradient L² with C = A05.gradientL6Const,
   using the underlying support-free Sobolev estimate and a three-column
   operator/Frobenius comparison. Combined with interpolation and Hölder:
   ofReal |advectionWork z| ≤ (ofReal C)^(3/2) G^(3/2) L^(3/2).
   This is unconditional for SmoothL2 z; G and L are physical extended norms.
5. Closed real convection estimate with only two explicit physical-to-norm
   bounds, and scaled Young: C Y^(3/4) Z^(3/4) ≤ ε Z + C⁴ ε⁻³ Y³.
   The elementary quartic proof splits b ≤ a/ε and its complement; no
   library availability claim or unproved Young input is used.
