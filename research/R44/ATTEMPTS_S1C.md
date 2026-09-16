# R44 S1c proof-engineering record

## Final route

The completed module follows the datum-level route in the lane brief.

1. `halfHomogeneousDatum` applies the bounded Bessel-to-Riesz multiplier
   componentwise and is contractive.  Its realization proof cancels the
   homogeneous half weight against that multiplier.
2. `inhomogeneousCriticalL3` feeds this genuine homogeneous datum into A05's
   scalar/vector critical embedding, giving the needed inhomogeneous estimate.
3. `halfDatumPhysicalComponent` lowers a cycles-convention half-order datum to
   order zero and takes the inverse Fourier transform.  Reality follows from
   `D01.fourier_conjugation`,
   `D01.realSymmetry_sobolevOrderLowering`, and the datum's
   `realSubspace` membership.  `FourierPhysicalJets.vectorLpReassembly_ae` then
   assembles its real parts, while `physicalLp_distribution` identifies the
   resulting field with the original angular datum.
4. `inhomogeneous_half_order_parseval` lowers the physical order-zero data to
   the dual orders, transfers the Bessel weights with
   `real_inner_lowering_transfer`, and finishes with R43's
   `angular_real_parseval` and `component_real_pairing`.  Thus the exact
   physical pairing is derived for arbitrary square-integrable fields.
5. `advectionJHolder` is the same three-factor `L³` Hölder step used in R43.
   The velocity, three derivative columns, and physical `Ju` field are each
   bounded by `criticalL3Const`; summing the columns costs a factor three.
6. `weight_identity` replaces the `H^(3/2)` norm by
   `sqrt (Y²+Z²)`, and elementary square-root arithmetic gives the requested
   final form.

No fallback hypothesis was introduced.  The final theorem is conditional only
on `AdvectionJDatum`, whose only fields are standard `H^∞` regularity and the
negative-half-order advection datum.  The physical `Ju` realization and exact
Parseval identity are derived, and the structure contains no estimate.

## Physical half-order datum reassembly

- **Failed (committed draft): expose the inverse Fourier transform after
  applying Fourier injectivity.**  In `halfDatumPhysicalComponent_real`, the
  route
  `apply (Lp.fourierTransformₗᵢ Space ℂ).injective; change ...` left the
  target as the Fourier transform of the bundled `compLpL` implementing
  `conjugation`.  The requested pointwise `realSymmetry (𝓕 (𝓕⁻¹ L)) =
  𝓕 (𝓕⁻¹ L)` expression was not definitionally equal to that
  target.  The correction is to unfold/expose `physicalLp` before applying
  injectivity.  A first correction exposed `physicalLp` before injectivity but
  retained `simp only [conjugation]` afterward; that eagerly unfolded the
  bundled `compLpL` and caused the same mismatch.  The successful shape should
  leave `conjugation` folded so `D01.fourier_conjugation` rewrites it directly.
  Rewriting immediately after injectivity still did not match because the goal
  displayed the concrete `Lp.fourierTransformₗᵢ`; following the established
  `A05/RieszShift.lean` pattern, an outer-only `change
  FourierTransform.fourier ... = ...` is required before that rewrite.

- **Failed (committed draft): obtain vanishing imaginary part by `simpa`.**
  Pointwise conjugation invariance gives `z.im = -z.im`; simplification alone
  does not turn this into `z.im = 0`.  This route needs the explicit linear
  arithmetic step `linarith`.  An intermediate attempt to normalize the
  already-simplified equality with `simp only [map_neg, Complex.neg_im]` also
  failed with `simp made no progress`; no normalization is needed before
  `linarith`.  Calling `linarith` directly was also premature because the right
  side was still printed as `(starRingEnd ℂ z).im`; the established RieszShift
  proof first applies `simp only [Complex.conj_im] at him`.  That exposes
  `z.im = -z.im`, but the goal still contains `((z.re : ℂ)).im`; as in the
  same upstream proof, `simp only [Complex.ofReal_im]` must simplify the goal
  before `linarith`.

## Conformance witnesses

The following failures occurred while the draft structure still carried
explicit physical-realization/Parseval fields.  The successful general
Parseval theorem later made those fields redundant, and the final API removes
them entirely.

- **Failed: discharge the zero `jVelocity` datum by `simpa`.**  The structure
  field retained the literal function `0`, while `isSobolevDatum_zero` exposes
  `fun _ => 0`; simplification did not reconcile those dependent arguments.
  An explicit `change` to the lambda spelling is required.

- **Failed: close the zero pairing with the general zero-field simp set.**
  `Jmul 0` remained folded, leaving `⟪0, Jmul 0⟫ = 0`.  The zero witness
  must explicitly simplify with `[Jmul]`.  Even after unfolding, the generic
  simp set leaves the PiLp real inner product `⟪0,0⟫`; the final step is the
  explicit Hilbert lemma `inner_zero_left`.  A typed `change` attempted before
  unfolding the structure projection still failed definitionally, so the
  projection `Jmul zeroJWeightDatum.velocityThreeHalf` is first rewritten to
  typed zero.  Rewriting `inner_zero_left` at the whole vector level then hit
  the phantom-order mismatch (`-1/2` versus `1/2`) during tactic instance
  checking.  Expanding the finite-product inner product componentwise with
  `PiLp.inner_apply` after that rewrite met the same tactic pre-check.  The
  correct repair is instead to `change` both zero arguments to the *same*
  phantom order `-1/2` before any rewriting; the carrier itself is independent
  of the order parameter.

## Conformance and non-vacuity

- `research/R44/axioms_s1c.lean` prints every declaration in
  `TrilinearJ.lean`; all report exactly
  `[propext, Classical.choice, Quot.sound]`.
- The full `JWeightDatum`/`AdvectionJDatum` package is explicitly inhabited at
  zero and the final theorem is applied to it.
- Lane 218's nonzero compact-smooth bump is reconstructed verbatim.  It is
  proved nonzero and inhabits both `JWeightDatum` and the full
  `AdvectionJDatum`.  Its canonical physical `Ju` representative is proved
  `L²`; its negative-half advection datum is constructed from smooth jets; and
  the new general Parseval theorem supplies the exact pairing identity used by
  the final estimate.  The estimate is applied to this nonzero instance.

## Strengthening probe: automatic inhomogeneous Parseval

- **Failed first carrier spelling:** a general `(-1/2,+1/2)` Parseval proof
  initially rewrote `realSobolev_inner_eq_ambient` and `PiLp.inner_apply`
  directly on inner products whose two operands display different phantom
  Sobolev orders.  Although `realSubspace s` ignores `s` definitionally (which
  is why the original pairing elaborates), the tactic instance checker rejects
  reconstruction of those heterogeneous-looking applications.  The proof
  must state the component identities directly on the common ambient
  `FourierData` carrier, and explicitly `change` the vector inner product into
  the resulting finite sum.  The first revision changed only the order-shift
  identity; the final substitution still failed until the order-zero physical
  identity was likewise stated on ambient `FourierData`.

- **Successful route:** construct canonical order-zero data of both physical
  fields, lower them to `-1/2` and `0`, use datum uniqueness, transfer the two
  half weights to order zero, and apply R43's scalar real Plancherel plus
  `component_real_pairing`.  This became the exported theorem
  `inhomogeneous_half_order_parseval` and closes the nonzero satisfiability
  audit without an assumed equality.
