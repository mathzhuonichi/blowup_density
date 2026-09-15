# Planned contract closure for the A01/C01 batch

This is a plan only.  Lane 176 does not add a contract, binding, test, or registry entry.
The closure audit on the rebased baseline finds `D01.homogeneous_norm` already registered and
`C01.energy_absorption_v4` extending V3 and consuming `C01.EnergyBounds` through its inherited
ordinary-energy fields.  The A01 modules listed below and the legacy C01
`Enstrophy`/`EnstrophyIdentityRaw` route remain outside every registered closure.

## A01 V2 bundle

Create a new `A01` version (without changing `A01.regularity_partial` V1) whose fields are the
proved constructor/wiring declarations below.  The contract should use the A02/Data vocabulary and
make every implementation input explicit; `ν`, initial data, and force membership are not to be
silently inferred.

* Datum-path ladder: `continuous_cylinder_word` takes `u : C(Icc 0 S, SobolevSpace 1 q)`,
  `hn : n ≤ q`, and `w : Fin n → Fin 4`; `weakDerivsBound_word_top` takes `u`, angular
  invariance `hu`, `m,n`, `hn : n ≤ q`, `hnm : n+m ≤ q`, `w`, `Z`, and
  `ordinaryLift Z = word …`; `weakDerivsBound_cylinder_top` takes `u`, `hu`, `U`,
  `ordinaryLift U = value 1 u`, `m`, and `hm : m ≤ q+1`; `datum_sub_norm_sq_le` takes
  `hm : m ≤ q+1`, two invariant slices `u,v`, their invariances `hu,hv`, carriers `U,V`,
  lift equalities `hU,hV`, data `A,B`, and `hA,hB : IsSobolevDatum`; and
  `exists_continuous_datumPath` takes continuous paths `u,U`, pointwise invariance `hu`, lift
  equation `hU`, `m`, and `hm : m ≤ q+1`, returning a continuous datum path.
* Divergence row c6 (`ConstructorDivergenceSlice`): `divergence_ae_of_cylinder` takes `u,U`,
  invariance `hu`, lift equality
  `hU`, `hdiv : value 1 u ∈ divergenceFreeSpace 1 1 0`, a smooth representative `Z`, and
  `hZ : Z.field =ᵐ ⇑U`; `divergence_of_cylinder_pointwise_of_contDiff` additionally takes
  continuous paths `u,U`, pointwise `hdiv`, `Z`, `hZ`, a `velocity`, `hslice` a.e. carrier
  equality, and `hslice_contDiff : ∀ t∈Ico 0 T, ContDiff ℝ ∞ (fun x => velocity (t,x))`.
* Pressure row c9/momentum: register the definitions `momentumResidualOfVelocity`,
  `pressureGradientOfVelocity`, and `pressureOfVelocity` by verbatim restatement, then the
  proved fields `pressureOfVelocity_basepoint`, `pressureGradientOfVelocity_memLp` (named
  `hres` and `htime`), `pressureGradient_pressureOfVelocity` (`hsmooth`, `hsym`),
  `pressureGradient_pressureOfVelocity_lerayComplement` (`hsmooth`, `hsym`, `hres`, `htime`,
  `hprojected`), its order-`m` version (also `m`, `Am`, `hAm`), `pressure_gradient_memLp_slice`
  and `pressure_gradient_memLp` (the corresponding slice-wise `hsmooth`, `hsym`, `hres`,
  `htime` families), `pressureOfVelocity_slice_smooth` (`hsmooth`),
  `pressure_smooth_of_velocity_smooth` (`hjoint`), and `momentum_of_projected` (`hvelocity`,
  `hdiv`, `hgradient_smooth`, `hgradient_symm`).  Keep `pressureOfVelocity_zero` as the
  non-vacuity/control theorem, not as a replacement for the pressure fields.
* Slice wiring: register `velocitySliceSmoothL2_field` as the compatibility theorem for
  `C01.velocityField`; register `sobolevENorm_slice_ne_top_order` with arbitrary named
  `m : ℕ`, retaining the `q+1` corollary; and register
  `sobolevSpace_norm_le_sobolevNormAt_of_solution` with explicit `hST`, `hu`, `hU`, and
  `hslice`, plus `isSobolevDatum_ordinary_of_hslice` with `hST`, `hslice`, `m`, and `t`, and
  `apriori_rows_of_hslice` with `hST`, `hq : 4 ≤ q`, `hu`, `hU`, and `hslice`.
  The retired `velocitySliceSmoothL2` alias is not a field.

The existing `OrderTwoCap`, `AprioriRows`, `CarrierWords`, and `L2Descent` modules should be in
the same A01 V2 closure, but their already-proved helpers are registered only where a V2 field
actually consumes them.  In particular, do not re-register retired order-restricted descent
theorems; use `L2Descent.word_descent_ae_top`, `word_descent_ae_full`, and `hword_jet_full`.

## C01 V4 status and future deduplication

The owner's `Contracts/V4/EnergyAbsorption.lean` is now registered as
`C01.energy_absorption_v4`; lane 177 was cancelled.  V4 extends the unchanged V3 interface and
adds exactly six public fields: `enstrophyIdentity`, `enstrophyDifferentialBound`,
`enstrophyIntegralBound`, `sobolevTwoFourier`, `h2TimeIntegral`, and
`h2TimeIntegralZeroDatum`.  Its binding uses the owner's `C01.EnstrophyIdentity`,
`C01.EnstrophyBounds`, `C01.SobolevTwo`, and `C01.H2TimeIntegral` chain.  The E5/E6/E7 helpers and
strict-interior finiteness results are implementation lemmas rather than contract fields.

Our renamed `C01.EnstrophyIdentityRaw` and its dependency `C01.Enstrophy` are not needed by the
registered V4 closure.  They provide an alternative raw-carrier proof of the identity, while
`h2TimeIntegral_strict`, `squaredHTwoIntegral_strict`, and
`h2TimeIntegral_of_absorption` are subsumed for contract purposes by the owner's quantitative
terminal-horizon result.  Keep both modules unchanged in this lane.  A future SIMP row should
audit their remaining research-only probes and then deduplicate or retire this legacy proof route;
that cleanup is explicitly not part of lane 176.
