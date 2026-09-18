# T19 U1--U6 attempts and result (lane 388)

## Scope and canonical vocabulary

The implementation is
`formalization/NSFormalization/Section3/T19/Bookkeeping.lean`.  It imports only
canonical `formalization/` modules.  The T19-local definitions needed by the
Spec are restated there: `criticalOrder`, `IsPeriodicLebesgueSlicePath`,
`mixedLebesgueENormT`, and `spaceTimeL2L2ENormT`.  The mixed exponent is the
existing canonical `NSFormalization.Section3.T15.alphaT`; the force, Sobolev,
and energy objects come from T10.  Contract equalities and the conversion of a
contract `ClassicalSolutionT` are confined to the probe.

## Successful routes

- U1 unfolds `criticalOrder`; `norm_num` proves the value at `q = 1`.
- U2 rewrites with `T15.alphaT_formula`; both strict inequalities follow by
  linear arithmetic.  U3 unfolds `alphaT` and normalizes the two concrete
  `ℝ≥0∞` inputs.
- U4 bounds the squared time profile almost everywhere by its essential
  supremum, applies monotonicity of `lintegral`, evaluates the measure of
  `Ioo 0 T`, and takes the nonnegative `1/2` power.  The last normalization
  uses `Real.sqrt_eq_rpow` and the `ENNReal.ofReal` power identity.
- U5 rewrites the physical energy norm as the canonical coefficient energy.
  The continuous order-zero and order-one Sobolev datum paths are bounded on
  compact `[0,T]`.  For the gradient term, deleting the zero Fourier
  coefficient decreases the inhomogeneous Sobolev norm; this is proved
  componentwise using `lp.norm_compl_sum_single`, then assembled with the
  `PiLp` L2 norm formula.  The homogeneous mean-zero norm is consequently
  bounded by the compact order-one datum bound, making both energy summands
  finite.
- U6 selects the constant-zero Sobolev datum path and constant-zero mixed
  Lebesgue slice path in the defining infima, then reduces their `eLpNorm`s to
  zero.

## Probe and drift resolution

`research/T19/probes/bookkeeping_closes.lean` copies the Spec's unregistered
mixed carriers and local `L²_tL²_x` norm, checks all registered-to-canonical
equalities by `rfl`, and closes the exact U1--U5 field statements plus both U6
helpers with `exact`.  It includes the concrete U2 instance `(p,q)=(2,1)` and
the two U3 numeric instances.  U5 converts the contract solution using
`BlowupDensity.Bindings.TorusLocalTheory.ofContract`; its velocity field is
definitionally unchanged.

## Rejected or unnecessary routes

- No registered contract module was imported into the canonical module;
  duplicated contract statements would violate the repository's dependency
  direction.
- U4 did not require a separate packaged `lintegral_le_essSup_mul` lemma; the
  pointwise essential-sup bound and `lintegral_mono_ae` give the required
  estimate directly.
- For U5, bounding only the physical velocity and derivative pointwise would
  leave a sizeable torus norm bridge.  The solution's continuous Sobolev datum
  paths provide the compact bounds in exactly the coefficient norms used by
  `energyENormT`.

## Residual

There is no residual statement or named input for U1--U6.  All seven public
theorems audit to exactly `[propext, Classical.choice, Quot.sound]`.
