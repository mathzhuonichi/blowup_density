# T22 reconciled comparison

Scope: `paper/sections/03-torus.tex:600-631`, especially
`eq:restriction-norm` at lines 603-605 and `eq:zero-extension` at lines
610-614.  The binding rulings are `research/T22/RECONCILIATION.md` §§2-3.
Draft A is lane 275 (`research/T22/DraftA.lean`); Draft B is lane 276
(`research/T22/DraftB.lean`).  Their original comparisons and reports are kept
verbatim beside this file.

## Vocabulary and import decision

`Spec.lean` imports `Contracts.V1.Data` and directly reuses its registered
whole-space vocabulary: `SpatialField`, `RealVectorSobolev`,
`angularRealization`, `FourierData`, `IsSobolevDatum`, and `sobolevENorm`.
It does not import `research/T10/Spec.lean` (a standalone research file) and it
does not copy any definition from it.  This is not a departure from T10: the
binding decision in the reconciliation §3 is that T22 is an `R^3`/domain layer
with no torus object.  T10 and T22 share the registered physical carrier
through `Contracts.V1.Data`; periodic data enter only in later consumers.

## Paper clause → Lean declaration, A/B provenance, and ruling

| Paper clause | Reconciled declaration | Draft A | Draft B | Binding ruling applied |
|---|---|---|---|---|
| `H^s(Omega)` consists of restrictions of whole-space distributions (`03-torus.tex:601-603`) | `DomainTest`, `DomainFunctional`, `restrictDatum` | Bundled a physical extension field, an `IsSobolevDatum`, and explicit integrable Schwartz pairings in `SobolevExtension` | Restricted a `RealVectorSobolev s` distribution to compactly supported Schwartz tests in `Omega` | Keep B. Negative-order elements must not be restricted to function-valued extensions. The ambient functional type is total; finite-norm elements are in the image of `restrictDatum`. |
| Quotient formula `eq:restriction-norm` (`03-torus.tex:603-605`) | `domainSobolevENorm` | `restrictionSobolevENorm` was an infimum over `SobolevExtension`; API repeated the unfolding as `restriction_norm` | Definition is the infimum of `‖A‖ₑ` over data whose distributional restriction equals `z` | Keep B's definition and omit a tautological API field. An empty extension family has norm `top`. |
| The convention includes negative orders (`03-torus.tex:606`) | Every datum/norm/multiplier binder uses `s : ℝ` | Yes | Yes | Agreement; retain unrestricted real order throughout. |
| At order zero the quotient norm is usual `L²(Omega)` (`03-torus.tex:606-607`) | `BoundedDomainNormAPI.orderZero` | `restriction_zero`, stated through the `L²` norm of the zero extension and explicit measurability | Equality with `eLpNorm z 2 (volume.restrict Ω)` under `IsOpen Ω` and `ContDiffOn ℝ ∞ z Ω` | Keep B. It matches the physical representative used by the target application and does not add a redundant `domainL2ENorm` definition. |
| The paper's section concerns a bounded domain (`03-torus.tex:600,633`) | Geometry hypothesis `IsOpen Ω` | `IsBoundedOpenDomain Ω := IsOpen Ω ∧ Bornology.IsBounded Ω` | Any open `Ω` | Keep B's weaker hypothesis. The local cutoff argument only uses openness plus compact inclusion; boundedness may be added by a proof lane only if genuinely required. |
| `K compactly contained in Omega` (`03-torus.tex:608`) | `IsCompact K → K ⊆ Ω` after `IsOpen Ω` | Named `CompactlyContained K Ω`, with the same compactness/inclusion plus bounded openness of `Ω` | Separate standard predicates | Keep B's unbundled geometry. In finite-dimensional Euclidean space these hypotheses give the needed positive separation from the complement. |
| Smooth fields supported in `K` (`03-torus.tex:608-609,613`) | `ContDiffOn ℝ ∞ z Ω` and `tsupport (zeroExtension Ω z) ⊆ K` | `IsSmoothSupportedIn` required global smoothness of the zero extension | Used exactly the reconciled hypotheses | Keep B. The proof must derive global smooth compact support of the zero extension from interior support; it is not strengthened into the statement. |
| `E₀z` is extension by zero (`03-torus.tex:610-615`) | `zeroExtension Ω z := Ω.indicator z` | An explicit `if x ∈ Ω then z x else 0` | `Set.indicator` | Keep B's name and spelling. Both ignore the input's values outside `Ω`. |
| Physical restriction of a smooth field | `restrictField` | Agreement of physical fields almost everywhere on `volume.restrict Ω` | Integration against each compact interior test | Keep B's distributional restriction. For `ContDiffOn` fields the compact-test integrals are genuine, so the registered integral totalization caveat is unreachable. |
| Multiplication of a distribution by a cutoff (`03-torus.tex:616-618`) | `IsCutoffDatum` | Pointwise `cutoffProduct` on a physical extension | Transpose multiplication on Schwartz tests | Keep B. It applies to every distributional datum and is therefore valid at negative order. No conjugation is inserted in the complex-linear distribution convention. |
| Choose `chi ∈ C_c^∞(Omega)` equal to one near `K` (`03-torus.tex:615-616`) | Proof dependency, not an API datum field | The cutoff `χ Ω K`, its support/smoothness/one-near facts, and `C Ω K s` were fields | Cutoff is locally chosen when deriving comparison from the generic multiplier field | Keep B's three-field API. Cutoff construction and the identity `chi Z = E₀z` become proof lemmas, exactly as reconciliation §2 says. |
| Fixed-cutoff multiplier bound for every real order (`03-torus.tex:617-624`) | `BoundedDomainNormAPI.cutoffMultiplier` | Quantified physical field plus datum and integrability; constant stored as `C Ω K s` | `∀ s χ`, smooth compact support, then `∃ C > 0`, before `∀ A`, producing `B` with `IsCutoffDatum` and a norm bound | Keep B. This is more reusable and has the correct dependence: `C` depends on `s,χ`, never on `A`. |
| First inequality in `eq:zero-extension` (`03-torus.tex:610-615,625`) | First conjunct of `zeroExtensionComparison` | First conjunct of `zero_extension` | First conjunct of `zeroExtensionComparison` | Agreement. The proof exhibits `E₀z` as one admissible whole-space extension in the quotient infimum. |
| Second inequality in `eq:zero-extension` (`03-torus.tex:610-624`) | Second conjunct of `zeroExtensionComparison` | Used stored cutoff and multiplier fields | One existential constant and the generic multiplier | Keep B. The proof chooses an interior cutoff, proves `χA = E₀z` for every extension datum `A`, applies `cutoffMultiplier`, and takes the infimum. |
| Constant independent of smaller support and shrinking `epsilon` (`03-torus.tex:626-627`) | `∃ C > 0` occurs before `∀ z` | `C Ω K s` was structurally outside `z` | Same order through the existential | Keep B. Since `C` has no field, scale, or time argument, one value applies to every family supported in the fixed `K`. |
| Pointwise comparison gives mixed-time comparisons when `K` is fixed (`03-torus.tex:627-629`) | Derived result, no fourth field | Listed as a later Bochner lemma | Also listed as a later Bochner lemma | Both drafts agree; the three-field ruling leaves this to T23. A correct lift must handle strong measurability and the quotient carrier, not integrate a pointwise infimum blindly. |
| No general bounded zero-extension operator (`03-torus.tex:629-630`) | Enforced by the smooth fixed-interior-support hypotheses | Enforced | Enforced | Agreement. The API makes no assertion about arbitrary `H^s(Ω)` elements or supports approaching the boundary. |
| Vector/tensor norms are Euclidean component sums (`03-torus.tex:630-631`) | Vector case inherited from `RealVectorSobolev` / `WithLp 2` | Reused the registered vector carrier | Reused the registered vector carrier | The reconciled T22 field is the vector case consumed by T23. A generic tensor product extension is not silently claimed. |

## Quantifier and non-vacuity audit

The three API fields contain no proposition parameter and no instance of the
record is asserted.

- `orderZero` equates two independently defined `ℝ≥0∞` quantities. It is not
  definitional because `domainSobolevENorm` is a distributional extension
  infimum.
- `cutoffMultiplier` chooses a finite positive constant before the datum and
  produces an actual output datum with an exact distributional graph and norm
  estimate.
- `zeroExtensionComparison` chooses one finite positive constant before the
  physical field. Its conclusion contains both inequalities from the displayed
  chain, while its hypotheses admit nonzero compactly supported bump fields
  whenever the chosen `K` has interior.

## Proof dependencies

This section refines the proof plan in `RECONCILIATION.md` §4.  It separates
registered facts already available, analytic work genuinely owed by T22, and
periodic T10 facts that are deliberately not dependencies of this proof.

### 1. Registered whole-space datum facts

The proof should stay in the `Contracts.V1.Data` normalization and use these
exact public facts where applicable:

1. `DatumLemmasAPI.isSobolevDatum_unique` identifies two
   `IsSobolevDatum s z` witnesses.  Its implementation rests on
   `NSFormalization.Paper3.angularRealization_injective`.
2. `DatumLemmasAPI.smoothJets_exists_datum` supplies a datum at every real
   order once the zero extension has been placed in
   `SmoothSquareIntegrableJets`.  For a globally smooth compactly supported
   zero extension, the jet hypotheses follow from compact support.
3. `NSFormalization.Section4.A01.IsSobolevDatum.congr_field` is the existing
   local a.e.-congruence lemma.  It is not yet a registered public T22
   dependency, so the proof lane must either register the needed spelling or
   prove the short integral-congruence result in its allowed module.
4. `NSFormalization.Section4.D01.exists_isSobolevDatum_zero_of_memLp` and its
   explicit `orderZeroDatum` give the order-zero existence direction.  The
   module explicitly records that the norm identity
   `‖orderZeroDatum hz‖ₑ = eLpNorm z 2 volume` is still missing; T22 cannot treat
   existence alone as the `orderZero` field.

### 2. `orderZero`

Beyond the datum constructor, the proof needs the exact vector Plancherel
isometry at order zero and the restriction/extension quotient calculation:

1. identify the norm of an order-zero angular datum with the ordinary
   Euclidean vector `L²(R³)` norm, including the `WithLp 2` component sum;
2. show restriction from `L²(R³)` to `L²(Ω)` is contractive;
3. show zero extension is an isometry from `L²(Ω)` into `L²(R³)` for the
   restricted measure; and
4. translate equality of compact-test restrictions into the a.e. equality
   needed by the `L²` argument.

These are the precise missing ingredients behind the reconciliation's phrase
“datum characterization at `s = 0`.”

### 3. `cutoffMultiplier`

For arbitrary real `s`, the direct proof needs:

1. the paper's weight ratio
   `(1+|xi|²)^(s/2)/(1+|eta|²)^(s/2)
   ≤ C_s (1+|xi-eta|²)^(|s|/2)`;
2. the Fourier product/convolution identity in the repository's angular
   normalization;
3. rapid decay of the Fourier transform of a smooth compact cutoff, giving the
   required weighted `L¹` kernel;
4. Young's `L¹ * L² → L²` estimate.  Existing implementation candidates are
   `NSFormalization.Source.YoungConvolution.eLpNorm_convolution_one_two` and
   `memLp_convolution_one_two`; and
5. preservation of conjugate-reflection reality for a real cutoff, so the
   output lies in `RealVectorSobolev s`, plus identification of its realization
   with `IsCutoffDatum`.

`Contracts/V1/HomogeneousPartial.lean` fields `annularRestriction`,
`annularSmoothing`, and `annularSchwartz` provide useful density and Schwartz
infrastructure, but they are frequency-annulus approximation statements and
do **not** themselves prove the spatial cutoff multiplier.  Likewise
`TameProductAPI.tameProductVector` is only an integer-order product estimate
under stronger membership assumptions.  It can support an alternative
integer-order-plus-interpolation route only after a real-order interpolation
theorem is supplied.  The proof lane may choose either route, as the
reconciliation permits.

### 4. `zeroExtensionComparison`

The assembly needs the following lemmas in addition to the multiplier:

1. construct `χ ∈ C_c^∞(Ω)` equal to one on a neighborhood of compact
   `K ⊆ Ω`;
2. derive `ContDiff ℝ ∞ (zeroExtension Ω z)` and compact support from
   `ContDiffOn ℝ ∞ z Ω` and
   `tsupport (zeroExtension Ω z) ⊆ K`;
3. show the zero-extension datum restricts to `restrictField Ω z`, which gives
   the left inequality by the defining infimum;
4. for every extension datum `A`, prove the distributional cutoff identity
   `χA = E₀z`, use `cutoffMultiplier` to produce `B`, and identify `B` as an
   `IsSobolevDatum s (zeroExtension Ω z)` witness; and
5. perform the `ENNReal` infimum bookkeeping with the fixed finite positive
   multiplier constant to obtain the upper inequality.

For `03-torus.tex:627-629`, T23 additionally needs strong measurability of the
relevant datum paths and the standard monotonicity of Bochner `eLpNorm`; that is
a downstream consequence, not a fourth T22 field.

### 5. Exact relationship to T10's “Needs a lemma” ledger

No field of `TorusDataAPI` and no periodic lemma from
`research/T10/COMPARISON.md` is needed to prove this T22 record.  The exact T10
lemma dependency set is therefore empty.  The potentially confusing entries
are:

| T10 “Needs a lemma” item | Why it is not a T22 proof dependency |
|---|---|
| 1 (`torusLift` / `periodicFourierCoeff` bridge) | T22 never lifts to `T³` and uses only angular whole-space distributions. |
| 2 (periodic Parseval and gradient identity) | `orderZero` needs the **whole-space/domain** Plancherel and restriction theorem above, not `TorusDataAPI.parseval_forward` or `parseval_backward`. |
| 3 (periodic weight facts, datum uniqueness/existence) | T22 uses `Data.IsSobolevDatum` and `DatumLemmasAPI.isSobolevDatum_unique`; the lattice weight `periodicFrequencyWeight` does not occur. |
| 4 (periodic Fourier reality) | Reality is already part of `RealVectorSobolev s`; T22 needs preservation under a real spatial cutoff in the continuous-frequency carrier. |
| 11 (periodic force paths) | The T22 API is spatial. The mixed-time lift for T23 is a separate Bochner argument on the domain/whole-space data. |
| 12 (periodic physical/coefficient energy identity) | Neither side of `zeroExtensionComparison` is the torus energy norm. |

Thus T10 is a DAG/vocabulary predecessor, not an analytic lemma provider for
T22.  This distinction prevents the torus Parseval theorem from being used in
place of the missing `R³` order-zero norm identity.

## Open questions for the owner

1. The selected carrier `DomainFunctional Ω` is a total function space and
   does not bundle linearity or continuity. Finite-norm elements are forced to
   equal `restrictDatum` of a genuine Sobolev datum, so the target fields are
   sound. Should registration keep this lightweight carrier, or replace it in
   a later V2 with a true compact-test distribution dual?
2. The reconciliation deliberately drops `Bornology.IsBounded Ω`; all local
   estimates remain valid for arbitrary open `Ω`. Should the registered V1
   contract retain this stronger generality even though the consuming
   corollary assumes a bounded box or smooth domain?
3. Lines 627-629 assert the mixed-time comparison as a consequence, but the
   three-field ruling leaves it out. Should T23 register the strong-measurable
   Bochner lift as its own lemma, or should a later T22 V2 expose it for reuse?
4. The paper's final sentence also mentions tensor norms. T23 consumes only
   vector-valued force differences, which is what `RealVectorSobolev` encodes.
   Does the owner want a later finite-Euclidean-product generalization rather
   than expanding V1 now?
5. The order-zero norm identity is explicitly absent from the current D01
   implementation's `OrderZeroDatum.lean`. Should its vector Plancherel theorem
   be promoted as a reusable D01/T22 component before attempting the quotient
   calculation, or proved privately in the T22 implementation lane?
