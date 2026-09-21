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
6. Closed scalar weighted cubic assembly. For Y=U+κG and
   Z≤U+2κG+κ²L (0<κ≤1), the coefficient of Z is ν. The cubic coefficient
   is (2κC)⁴/(κν/2)³/κ³ + 1+ν and the force coefficient is 1+2κ/ν.
   The L² term U is explicitly retained and bounded by Y. No Poincaré
   inequality, critical smallness, or endpoint-integrability claim is used.
7. Closed classical assembly and compact-interval wrapper, plus the convection
   estimate explicitly in `D01.sobolevENorm` vocabulary. B0 hypotheses in the
   final differential theorem are precisely:
   - H¹² = l2Sq + κ gradientSq throughout (0,T), κ=(2π)⁻²;
   - H²² ≤ l2Sq + 2κ gradientSq + κ² laplacianSq at the time;
   - eLpNorm gradTensor 2 ≤ ofReal sqrt(gradientSq) at the time.
   The Laplacian norm bridge and both force estimates are discharged locally
   from existing C01/I02 lemmas. No assumption of a differentiated norm,
   convection estimate, Young inequality, or differential inequality remains.
   `hOne` transfers HasDerivAt using equality in a neighborhood, not equality
   at one time. Finite ENorms already follow from classical Sobolev paths.

Transient compilation errors fixed: the first `convert` exposed two real
instance equalities (closed by rfl); an overly general numeral rewrite touched
PiLp's exponent (replaced by an explicit equality for 3); a derivative-value
placeholder was not inferred (the exact raw derivative value is now written).
No failed proof is shipped and no analytic residual is inferred from these
elaboration errors. The B0 bridge proofs are deliberately outside lane scope.
