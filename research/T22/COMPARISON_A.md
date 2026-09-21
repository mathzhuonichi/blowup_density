# T22 draft A comparison

Scope: `paper/sections/03-torus.tex:600-630`, the T22 contract sentence in
`collaboration/tasks/T22.md`, and the representation choice in
`collaboration/SECTION3_PLAN.md` §1. This document compares the paper with
[`DraftA.lean`](DraftA.lean); it does not inspect either independent T22 draft.

## Paper clause to Lean declaration

| Paper clause | Draft A declaration | Quantifiers / fidelity note |
|---|---|---|
| `H^s(Omega)` consists of restrictions of whole-space `H^s` distributions (`03-torus.tex:601-603`) | `SobolevExtension` | A representative carries D01's real-vector angular datum and must agree with the domain field almost everywhere on `Omega`. `HasIntegrableSchwartzPairings` closes the documented totalized-integral loophole in `Data.IsSobolevDatum`. |
| Quotient formula `eq:restriction-norm` (`03-torus.tex:603-605`) | `restrictionSobolevENorm`, field `restriction_norm` | `forall s Omega z`, the value is the `iInf` of the registered whole-space `sobolevENorm s E.field` over bundled valid extensions. The displayed field deliberately exposes the infimum instead of leaving the convention hidden behind a name. |
| The convention includes negative orders (`03-torus.tex:606`) | real parameter `s : ℝ` in `SobolevExtension`, `restrictionSobolevENorm`, `restriction_norm`, `cutoff_multiplier`, and `zero_extension` | There is no nonnegative-order hypothesis. |
| At order zero this is the usual `L^2(Omega)` norm (`03-torus.tex:606-607`) | `domainL2ENorm`, field `restriction_zero` | Uses the vector `eLpNorm` of the zero extension, with measurability explicit. This preserves the paper's square-root-of-summed-squares vector convention. |
| `Omega` is a bounded domain and `K compactly contained in Omega` (`03-torus.tex:600,608`, domain alternatives at `:633`) | `IsBoundedOpenDomain`, `CompactlyContained` | The norm layer needs only bounded openness, not a smooth-boundary or box witness. `CompactlyContained K Omega` is `IsCompact K ∧ K ⊆ Omega`; openness then supplies positive boundary separation in `R^3`. |
| `z` is smooth and supported in `K` (`03-torus.tex:608-609,613`) | `IsSmoothSupportedIn` | Smoothness and topological support are imposed on the actual zero extension, exactly the object whose whole-space norm occurs in the display. |
| `E_0 z` is extension by zero (`03-torus.tex:610-615`) | `zeroExtension` | The input uses the repository's ambient `SpatialField`; values outside `Omega` are ignored. |
| Fix `chi in C_c^infty(Omega)` equal to one near `K` (`03-torus.tex:615-616`) | data field `χ`; fields `chi_smooth`, `chi_compactSupport`, `chi_support`, `chi_one_near` | `χ Omega K` is selected before `s`, matching the proof's one fixed spatial cutoff. The open neighborhood on which it is one is explicit and is contained in `Omega`. |
| For every extension `Z`, `chi Z = E_0 z` (`03-torus.tex:616-617`) | `cutoff_extension_identity` | Equality is almost everywhere on `R^3`, which is the correct equality for the Sobolev/Lebesgue representatives. |
| Multiplication by fixed `chi` is bounded on `H^s(R^3)` for every real `s` (`03-torus.tex:617-624`) | data field `C`, `C_pos`, field `cutoff_multiplier` | Quantifier order is `Omega, K, s`, geometry hypotheses, then `Z, A`. The bound produces an output D01 datum `B` and states `norm B <= ofReal (C Omega K s) * norm A`. This is the registered angular real-vector datum architecture, not a second Fourier model. |
| Two-sided `eq:zero-extension` (`03-torus.tex:610-614`) | `zero_extension` | One conjunction transcribes the displayed chain, for every real `s`: domain quotient norm `<=` whole-space zero-extension norm `<= C` times the domain norm. |
| The constant is independent of a smaller support and shrinking `epsilon` (`03-torus.tex:626-627`) | quantifier order of `C` and `zero_extension` | `C Omega K s` has no field, support, time, or scale argument and is selected before `z`. Thus the same value applies pointwise to every member of an epsilon-family whose zero-extension support stays in the fixed `K`. No redundant epsilon-specialized field is added. |
| The same comparison holds in time norms for fixed `K` (`03-torus.tex:627-629`) | derived consequence, not a separate API field | The T22 task contract names the two spatial displays and their scale-independent multiplier constant. A faithful Bochner lift needs a registered quotient `H^s(Omega)` carrier and measurable extension-path lemma; recording only a scalar pointwise-infimum integral would recreate the lower-integral gap avoided by D01. This is listed below as a required lemma for the T23 consumer. |
| No bounded zero-extension operator on arbitrary `H^s(Omega)` is asserted (`03-torus.tex:629-630`) | enforced by the hypotheses of `zero_extension` | The upper bound requires one fixed compact interior `K` and `IsSmoothSupportedIn`; there is no unrestricted operator field. |

## Choices in draft A

1. The whole-space side is reused verbatim from
   `verification/Contracts/V1/Data.lean`: `SpatialField`,
   `RealVectorSobolev`, `IsSobolevDatum`, and `sobolevENorm`. In particular,
   the Fourier normalization is angular, reality is built into the datum, and
   vector norms use the Euclidean `PiLp 2` product.
2. Domain fields stay on the ambient physical carrier and are quotiented by
   almost-everywhere agreement on `Omega`. This makes restriction compatible
   with the repository's force and velocity types while respecting the
   equivalence-class semantics of `H^s` and `L^2`.
3. A quotient representative is bundled with a datum and integrable Schwartz
   pairings. Without the latter condition, the totalized integral caveat in
   `Data.IsSobolevDatum` becomes reachable inside the infimum and can
   spuriously drive a nonzero quotient norm to zero.
4. `IsSmoothSupportedIn` is phrased on `zeroExtension Omega z`. For the paper's
   interior-supported smooth fields this is equivalent to intrinsic smoothness
   on the domain plus support in `K`, and it states exactly the regularity used
   by the whole-space multiplier.
5. `C` is real and positive; the `ℝ≥0∞` inequalities use
   `ENNReal.ofReal (C Omega K s)`. No `.toReal` occurs.
6. Boundedness is included for statement fidelity, although the cutoff and
   multiplier argument only needs `Omega` open and `K` compactly contained.

## Ambiguities for reconciliation

- **Domain carrier.** The paper says restrictions of distributions, while the
  repository's registered D01 interface represents distributions through
  physical fields and Schwartz pairings. Draft A uses the latter. An accepted
  contract could instead define a quotient of vector tempered distributions,
  but that would require a new restriction relation and a bridge back to T23's
  physical force fields.
- **Pointwise versus a.e. restriction.** Draft A chooses a.e. agreement. The
  smooth fields used by the corollary have canonical pointwise representatives,
  so either choice gives the same application, but a.e. is the faithful normed
  space convention.
- **Meaning of compact support.** Draft A uses `tsupport (E_0 z) ⊆ K`. If the
  accepted T10/T23 vocabulary tracks support by `Function.support`, a bridge is
  needed; topological support is the manuscript's standard smooth-field reading.
- **Domain assumptions.** Draft A asks for a bounded open set but does not
  encode “box or bounded smooth domain.” Those boundary regularity alternatives
  belong to T23's PDE/no-slip layer and are irrelevant to this multiplier
  statement.
- **Time-norm lift.** Lines 627-629 are a mathematical consequence of the
  pointwise estimate, but the existing registered data layer has no
  bounded-domain Bochner quotient carrier. Reconciliation should decide whether
  T22 registers that carrier now or leaves the lift as the first lemma in T23.
- **Cutoff range.** The proof only asks for a compactly supported smooth cutoff
  equal to one near `K`; it does not state `0 <= chi <= 1`. Draft A therefore
  does not strengthen the target with a range condition.

## Needs a lemma

1. Existence of `chi Omega K` with `chi_smooth`, `chi_compactSupport`,
   `chi_support`, and `chi_one_near` for a compact inclusion in a bounded open
   subset of `R^3`.
2. The real-order cutoff multiplier theorem on D01's angular
   `RealVectorSobolev s` datum, including preservation of conjugate-reflection
   reality and of integrable Schwartz pairings.
3. The paper's weight-ratio estimate and the weighted `L^1 * L^2 -> L^2`
   Young bound needed by item 2, with angular Fourier normalization checked.
4. The a.e. identity `chi Z = E_0 z` from support separation, `chi = 1` near
   `K`, and `Z = z` a.e. on `Omega`.
5. The quotient calculation at order zero:
   `restrictionSobolevENorm 0 Omega z = domainL2ENorm Omega z`.
6. Infimum bookkeeping: apply the datum multiplier to every bundled extension,
   use the cutoff identity and datum uniqueness/a.e. congruence, then take the
   infimum to prove `zero_extension`.
7. A Bochner quotient-space construction or measurable-selection theorem that
   lifts `zero_extension` to all `L^q_t H^s_x` norms without a lower-integral
   gap; T23 then gets the fixed-`K`, epsilon-uniform force comparison.
8. Registration bridges (`rfl` where possible) from the spec-local physical
   aliases to the accepted T10 layer and from this norm to the T23 force norm.

## Section 4 counterparts and reuse

- **D01 / `Contracts.V1.Data`.** Reused verbatim: `Space`, `SpatialField`,
  `RealVectorSobolev`, `IsSobolevDatum`, `sobolevENorm`, `eLpNorm`, and the
  `ℝ≥0∞` totalization discipline. This is the substantive reusable R3 side.
  Only the domain quotient, zero extension, and spatial cutoff package are new.
- **B02 / `Contracts.V1.HomogeneousPartial`.** `annularRestriction` and
  `annularSmoothing` are statement templates for the quantifier order “real
  order, datum, explicit error/support data, output datum.” Their theorems are
  not directly reusable: they cut off and smooth in frequency for homogeneous
  data, whereas T22 multiplies by a fixed spatial cutoff in the inhomogeneous
  `H^s` datum. B02's fixed-cutoff packaging (`χ` plus separate smooth/support
  fields) is mirrored by `χ` and the four `chi_*` fields here.
- **`BoundaryAnalyticBridge`.** Its explicit bounded-flow witness unpacking and
  support-to-no-slip theorem can be reused verbatim by T23. It proves no
  Sobolev restriction or zero-extension estimate, so it discharges no T22
  field.
- **`BoundaryReferenceRestriction`.** Its horizon restriction of a bounded
  reference is likewise reusable verbatim by T23 and orthogonal to the present
  norm layer.
- **Existing `BoundaryCorollary.domainSobolevNorm/domainForceNorm`.** These are
  not reused: they are scalar, use the older `SobolevHilbert/sobolevRealization`
  model rather than D01's registered angular real-vector datum, assemble vector
  components by a sum of scalar norms, and do not provide `eq:zero-extension`.
  A bridge or replacement is needed before T23 can consume the accepted T22
  contract.
