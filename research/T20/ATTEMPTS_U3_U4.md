# T20 U3 (`bIntegral`) and U4 (`constantTransportSkew`) — attempts log (lane 390)

Both fields proved verbatim over the canonical `Section3/T20/CriticalRegularity.lean`.
Every declaration prints `[propext, Classical.choice, Quot.sound]`.

## U4 `constantTransportSkew` (`Section3/T20/ConstantTransport.lean`)

Route that worked (first try after infrastructure survey):
- `periodicPairing a b = cubeIntegral (fun x ↦ ⟪a x, b x⟫_ℝ)` — the integrands are
  definitionally equal (`torusLift` evaluates at a point), so
  `NSFormalization.Paper1.integral_torusLift` closes it via `unfold; exact`.
- `constantTransportSpatialT m v x = fderiv ℝ v x m` is `rfl`; expanding `m` by
  `NavierStokes.PeriodicUniqueness.sum_coordinates` and CLM linearity gives
  `= ∑ j, m j • spatialPartial j v x`.
- Core IBP reused verbatim: `NavierStokes.PeriodicUniqueness.cubeIntegral_inner_partial`
  (per-direction vector integration by parts on the cube, from Mathlib's divergence
  theorem). Pulling the finite coordinate sum and constants `m j` through
  `cubeIntegral` uses `cubeIntegral_sum` / `cubeIntegral_const_mul`.

Negative note (only obstacle): `rw [cubeIntegral_sum Finset.univ _ (...)]` with the
summand function left as `_` fails — the higher-order `rw` pattern picks up a stray
metavariable (`(fun x => ?m i) * fun x => ⟪…⟫`). Fix: elaborate `cubeIntegral_sum`
into a `have` with the summand `fun i x => m i * ⟪…⟫` given explicitly, then `rw` the
resulting equation.

The two `Integrable` premises are genuinely unused: the cube-integral identity holds
unconditionally, so they only guard the Bochner integral in the manuscript field.

## U3 `bIntegral` (`Section3/T20/BIntegral.lean`)

Key structural observation: `meanFreeForce g (t,·)` is exactly
`meanZeroPartT (fun x ↦ g (t,x))` (`forceMeanT g t = meanT (g(t,·))` by `rfl`), so its
nonzero Fourier coefficients agree with those of `g(t,·)` and its `k=0` mode is
removed. The proof mirrors `T12.SpectralGap.homogeneous_le_sobolev`, but relates the
homogeneous norm of the *mean-free* slice to an inhomogeneous datum of the *original*
force slice:
- `criticalRho g = ⨅ G-path, ∫⁻ ‖G t‖ₑ` (`forceSobolevENormT` with `q = 1`,
  `eLpNorm_one_eq_lintegral_enorm`); `criticalBIntegral (meanFreeForce g) =
  ∫⁻ periodicHomogeneousENorm (1/2) (h(t,·))`. `le_iInf` + `lintegral_mono_ae` reduce
  to a slicewise bound at each `t > 0` (a.e. under `forceTimeMeasure = volume.restrict (Ioi 0)`).
- Slice bound `bIntegral_slice`: the bounded even reweighting
  `T12.reweightDatum bWeight 1 …` sends the inhomogeneous datum `G t` of `g(t,·)` to a
  homogeneous datum of `h(t,·)`. The datum equation is discharged by
  `T10.DatumBasics.periodicFourierCoeff_sub`/`periodicFourierCoeff_const`
  (`k=0` handled by `homogeneousDatumWeight (1/2) 0 = 0`, `k≠0` by weight cancellation
  with `div_mul_cancel₀`); `reweightDatum_norm_le` gives `‖h-datum‖ₑ ≤ ‖G t‖ₑ`.

Negative notes / dead ends:
1. `iInf_le _ ⟨⟨reweightDatum …⟩, hB⟩` with the function left as `_` **times out at
   `whnf`** (>400000 heartbeats): inferring the metavariable `?f` from the goal forces
   Lean to whnf the whole `reweightDatum` term (which carries a `Memℓp.mono'` proof).
   Fix: give `iInf_le` the index function explicitly
   (`iInf_le (fun A' : {A' // IsPeriodicHomogeneousDatum …} => ‖A'.1‖ₑ) ⟨…⟩`), then the
   ascribed `have` type is checked by one unfold + projection. The `IsPeriodicHomogeneousDatum`
   reconstruction (`hB`) is itself under 200000 heartbeats; the module bump to 400000 is
   a margin, not a need.
2. `rw [hdat.1 x j]` (periodicity of the slice) fails because the datum's
   `IsPeriodicSpatial` is stated on `fun x ↦ g(t,x)` and the goal is already
   beta-reduced (`g (t, x + e_j)`); `exact congrArg (· - forceMeanT g t) (hdat.1 x j)`
   closes it by defeq instead.
3. Reusing `T12.SpectralGap`'s private `homogeneousRatio*`/`reweightDatum_enorm_le`
   lemmas is impossible (they are `private`); the four elementary facts (`bWeight`
   nonneg / `|·|≤1` / evenness, enorm-of-norm bound) are re-derived here from the
   public `homogeneousDatumWeight_le_periodicFrequencyWeight_rpow` and
   `reweightDatum_norm_le`.

No `sorry`/`axiom`/`native_decide`; no named `Prop` inputs; no goal repackaging.
