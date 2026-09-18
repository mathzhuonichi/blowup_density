# T20 draft A comparison — `prop:critical`

This is the independent draft-A comparison for
`paper/sections/03-torus.tex:370-505`. It does not use another T20 lane or a
T20 reconciliation brief.

## Paper clause → Lean field

| Paper | Draft-A declaration / field | R43 / C01 / A04 counterpart |
|---|---|---|
| `:383-387`, “there is `c>0`”, with `c` independent of `ν,g` | `CriticalRegularityTAPI.c`, `hc`; `c_lt_C₀` and `c_lt_C₁` record the proof's choices at `:457,:477` | `R43.CriticalRegularityAPI.c`, `hc`; R43 hides its proof constants. C01 stores positive analytic constants as data before PDE quantifiers. |
| `:385-390`, `eq:smallcritical` and `T_max^ν(0,g)=∞` | `globalRegularity` | Exact torus counterpart of `R43.CriticalRegularityAPI.inhomogeneousAtZero`; continuation route corresponds to `A04.ContinuationV2API.lifespanInfiniteOfLocallyFinite`. |
| `:395-403`, `m=mean(u)`, `m'=mean(g)`, `m(0)=0` | `meanPathT` uses T11's data-defined `galileanMeanT 0 g`; not duplicated as a T20 API field | No R43/C01/A04 field. Owner is T11 `PeriodicMeanReductionAPI.mean_formula` / `mean_derivative`. A lemma must specialize these to the untranslated reduction. |
| `:404-406`, `eq:meanbound` | `meanBound` | No direct R43/C01/A04 analogue: all Section 4 fields are whole-space and have no spatial zero mode. |
| `:407-410`, `eq:meanfree` | `meanFreeVelocity`, `meanFreeForce`, `constantTransportTerm`; field `meanFreeEquation` | No direct Section 4 analogue. Its pointwise-residual shape is closest to the local-solution equation underlying C01. |
| `:411`, constant transport commutes with multipliers and is skew-adjoint | No T20 contract field: these are proof lemmas for the two energy identities | No direct counterpart. C01's energy identities similarly consume cancellation lemmas without registering each cancellation as an API field. |
| `:414-418`, definitions of `y,z,b` | `criticalY`, `criticalZ`, `criticalBRate` | R43's proof describes the same `y,z,b`, but `CriticalRegularityAPI` exposes only its conclusions. |
| `:438-440`, `eq:criticalenergy` | `criticalEnergy`, with a witnessed derivative of `y²` and explicit finite homogeneous memberships | R43 proof's hidden critical estimate. C01 explicitly excludes the critical half-order estimate; its `enstrophyIdentity` / `enstrophyDifferentialBound` provide the house style for witnessed derivatives. |
| `:442-444`, `eq:bintegral` | `criticalBIntegral`, field `bIntegral` | R43 uses the analogous homogeneous-to-inhomogeneous force comparison internally. C01's `forcePrimitive` has the same bookkeeping role but is an ordinary-energy real integral. |
| `:454-456`, `eq:ybound` | `criticalBPartial`, field `yBound` | R43 internal bootstrap; no registered R43 field. The scalar proof shape is implemented by `Paper1.CriticalEnergyCertificate.norm_le_radius`. |
| `:460-464`, integrated critical dissipation | Not a field: it is an immediate integrated consequence of `criticalEnergy`, `yBound`, and the smallness margin, and was not among the brief's named standalone fields | No registered R43 field; closest C01 analogue is `enstrophyIntegralBound`. |
| `:482-484`, `eq:H1energy` | `gradientLTwoSq`, `laplacianLTwoSq`, field `hOneEnergy` | Torus counterpart of `C01.EnergyAbsorptionAPI.enstrophyDifferentialBound`; `CH1` mirrors `CRH1`. |
| `:486-500`, integrate `eq:H1energy`, compare `H²` with `Δ`, split `u=m+v` | No duplicate T20 field; these are lemmas used to build T11's squared-`H²` criterion | Counterparts: `C01.enstrophyIntegralBound`, `h2TimeIntegralZeroDatum`; T12 `hTwo_le_laplacian`; A04's `squaredHTwoIntegral` premise. |
| `:500-503`, continuation contradiction | Folded into `globalRegularity` | `A04.ContinuationV2API.extendsBeyond` and `lifespanInfiniteOfLocallyFinite`. |

## Choices made in draft A

- `CriticalRegularityTAPI : Type`, not `Prop`. The universal reals `c`, `C₀`,
  `C₁`, and `CH1` are mathematical data. This follows the Type-valued style of
  R43 and T12 and fixes all constants before `ν`, `g`, the solution, and time.
- The theorem uses the literal datum `fun _ : Space => 0`, matching the paper
  and R43's zero-datum clause. Its membership in `initialClassT` is a basic
  lemma, not a redundant hypothesis that changes the proposition's quantifier
  order.
- The solution estimates quantify a common `(u,p)` through T11's
  `SolvesBelowT` on each compact presingular horizon. This is the exact
  continuation-facing representation and avoids assigning meaningful values
  to a maximal field after its lifespan.
- The mean removal is untranslated: `v(t,x)=u(t,x)-m(t)` and
  `h(t,x)=g(t,x)-meanT(g(t))`. T11's Galilean object is used only for the
  data-defined mean path; no spatial shift appears in `meanFreeVelocity`.
- `eq:meanfree` is written as the ordinary viscosity-`ν` residual of `v`, plus
  `constantTransportTerm`, equal to `h`. Since the residual already contains
  `(v·∇)v`, this is literally the paper's equation.
- `criticalY`, `criticalZ`, and `criticalBRate` remain `ℝ≥0∞`-valued and hence
  fail safe at `⊤`. `criticalEnergy` bundles concrete
  `MemPeriodicHomogeneous` facts before converting these quantities to reals.
  The derivative is existentially witnessed with `HasDerivAt`; it cannot be
  satisfied by supplying an arbitrary number.
- Nonnegative time integrals in `meanBound`, `criticalBIntegral`, and
  `criticalBPartial` are `lintegral`s. This preserves divergence as `⊤`.
- The H¹ display uses real Haar integrals because `HasDerivAt` requires a real
  target. The same field first supplies smoothness and the relevant `MemLp`
  facts, preventing Mathlib's totalized Bochner integral from hiding a
  nonintegrable slice.
- Only the six named proof displays are T20 fields. Mean differentiation,
  multiplier commutation/skew-adjointness, the integrated dissipation display,
  and the continuation packaging remain lemmas or their owning T11/T12 API
  clauses. This avoids duplicating sibling contracts.

## Ambiguities for reconciliation

1. The brief calls the continuation bound `eq:criterion`, while the supplied
   paper excerpt has an unlabelled display at `:496-500`; T11's actual public
   criterion is `squaredHTwoIntegralT S u ≠ ⊤`. Draft A keeps it out of the T20
   record because the requested exact field list ends at `eq:H1energy` plus the
   main theorem.
2. The paper writes ordinary integrals of nonnegative norms. Draft A uses
   `lintegral` for `eq:meanbound` and `eq:bintegral`. An implementation must
   prove equality with the real interval integrals once integrability is known.
3. The paper's symbols `C₀`, `C₁`, and the `C` after Young's inequality are
   not numerically fixed. Draft A records three positive data fields and the two
   explicit restrictions on `c`. A reconciliation could instead define `C₀`
   and `C₁` from a chosen T12 API witness, but that would couple this theorem's
   public type to the whole T12 structure.
4. `eq:criticalenergy` is pointwise notation for the derivative of a squared
   norm. Draft A uses an existential derivative witness. An alternative is the
   C01 two-field pattern (identity plus a conditional differential bound), but
   that would add a field not named by the T20 brief.
5. The paper's critical dissipation display at `:460-464` is standalone
   typography but absent from the brief's explicit field list. Draft A treats
   it as a derived lemma; reconciliation should confirm that scope choice.

## Needs a lemma

1. `zero_mem_initialClassT`: the rest datum belongs to T10's concrete smooth,
   periodic, solenoidal class.
2. Specialize T11 `PeriodicMeanReductionAPI.mean_formula` and
   `mean_derivative` at the zero datum, identifying the solution mean with
   `meanPathT` without applying the Galilean spatial translation.
3. Mean-zero decomposition for every solution/force slice, including Haar
   integrability, and preservation of smoothness, periodicity, divergence, and
   pressure gauge under subtraction of the spatial constant.
4. The pointwise residual identity for `u-m`: time differentiation of the
   data-defined mean, invariance of spatial derivatives under subtraction of a
   constant, and decomposition of advection into `(v·∇)v+(m·∇)v`.
5. `constantTransportTerm` is skew-adjoint in physical `L²(T³)` and commutes
   with every periodic Fourier multiplier used at orders `1/2` and `1`.
6. The force-mean bound
   `∫₀ᵗ|meanT(g)| ≤ ‖g‖_{L¹H^{1/2}}`, including normalized-Haar Cauchy–Schwarz
   and the order-`1/2` spectral comparison.
7. Removing the zero mode is contractive on the inhomogeneous datum path and
   yields `criticalBIntegral g ≤ criticalForceRadius g` with strong
   measurability of the centered path.
8. Classical T10 solution slices and centered force slices furnish
   `MemPeriodicHomogeneous` at orders `1/2` and `3/2`; this bridges integer
   smooth Sobolev data to the fractional homogeneous data used by T12.
9. Assemble `C₀` from T12 `velocityCriticalL3` and
   `gradientLambdaCriticalL3`, including existence/uniqueness of the physical
   Lambda representative, pressure cancellation, and the exact critical
   energy derivative identity.
10. Instantiate the scalar continuity bootstrap, including continuity of
    `criticalY` and the forcing primitive and the `ζ↓0` regularization, to prove
    `yBound` from `criticalEnergy`, `bIntegral`, and `c_lt_C₀`.
11. Assemble `C₁` from T12 `velocityCriticalL3` and `gradientLSix`; prove
    pressure and constant-transport cancellation in the `-Δv` test and apply
    Young's inequality with the stated coefficients to obtain `hOneEnergy`.
12. Integrate `hOneEnergy`; prove `∫₀∞‖h‖₂²<∞` from `MemForceT`; apply T12
    `hTwo_le_laplacian`; and prove the orthogonal zero/mean-mode identity for
    `u=m+v` used at `:496-500`.
13. Feed the resulting `squaredHTwoIntegralT` finiteness into T11
    `PeriodicContinuationAPI.lifespanInfiniteOfLocallyFinite`, using
    `PeriodicLocalTheoryAPI.exists_maximal`, to derive `globalRegularity`.

## Existing `Paper1/` implementation candidates

| File / declaration | Candidate use | Limitation |
|---|---|---|
| `PeriodicCriticalRegularity.lean:63`, `CriticalRegularityCertificate` | Existing positive radius plus global-lifespan theorem shape; `exists_critical_regularity_constant` and `critical_regular_ball` already package its consequence | Uses the older `TestForce` / `forceDistance` / `PeriodicLifespan.lifespan` vocabulary and exposes no PDE bridge. It needs a T10/T11 binding, not direct import into the contract. |
| `CriticalEnergyCertificate.lean:16`, `CriticalEnergyCertificate`; `:44`, `norm_le_radius` | Exact real-variable certificate for `criticalEnergy → yBound` | Abstract scalar functions only. T20 must construct the certificate from the periodic PDE and prove all continuity/derivative hypotheses. |
| `CriticalEnergyCoercivity.lean:15`, `dissipation_coercive` | Half-viscosity coercivity once `y≤ρ` | Depends on a completed scalar certificate. |
| `CriticalEnergyDerivative.lean:8,21`, `absorbed_energy_inequality_on_interval`, `energy_derivative_le` | Absorbed form and derivative estimate used by the bootstrap | No torus norms or force path. |
| `CriticalEnergyForcing.lean:10`, `forcing_work_le_radius` and `CriticalEnergySignatures.lean:8-25` | Scalar sign and forcing bookkeeping | No PDE/content bridge. |
| `PeriodicMeanZeroEstimate.lean:18,50,94` | Spectral-gap arithmetic after removal of the zero Fourier coefficient | Finite-mode sums only; does not prove the complete `lp`/physical-field T12 statement. `one_le_periodicAngularMagnitude` at `:71` is reusable arithmetic. |
