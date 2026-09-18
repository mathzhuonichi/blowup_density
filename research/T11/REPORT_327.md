# REPORT 327 — T11 U9d2b: Duhamel time differentiation and the momentum equation

Lane `327-T11-U9d2b-momentum`, branch `erenup/327-T11-U9d2b-momentum`
(based on the integration branch with lane 326 merged).
Unconditional modulo the data hypotheses listed below; **no new `def … : Prop`**,
no named peeling input, no `sorry`/`admit`/`axiom`/`native_decide`, no
`set_option maxHeartbeats`.

## 1. 证了哪个定理 / What is proved

**(i) The Duhamel formula is differentiated in time, coefficient by
coefficient.**  For a forced mild solution `hu : TorusForcedMildOn C A P T u`
with a continuous projected force path, at every interior time `t ∈ Ioo 0 T`,
every component `i` and every lattice frequency `k`:

```
d/dt û(t)(i,k) = −ν·4π²|k|²·û(t)(i,k) + (P̂F)(t)(i,k) − (P̂Q(u,u))(t)(i,k)
```

both in the **weighted** `H³` coefficients (`mild_coeff_hasDerivAt`) and in the
**unweighted physical** coefficients (`mild_physicalCoeff_hasDerivAt`).  This is
the residual that lane 313/318/320/326 all recorded as open.

**(ii) The physical velocity has a genuine time derivative.**
`torusPhysicalVelocity u` is differentiable in `t` at every point of
`Ioo 0 T × ℝ³`, its derivative is the Fourier series `mildTimeDerivative C P u t`
of the derivative coefficients, and that field is `C^∞` and unit-periodic in `x`
with exactly the expected Fourier data.  Continuity up to `t = 0` is lane 318's
`torusForcedMildOn_physical_continuous`.  **The joint `C^∞` field is not proved
— see §3.**

**(iii) The momentum equation.**  For *any* pressure `p` whose gradient carries
the Leray-complement Fourier data `(I − P)(F − Q)` of the physical source, the
recovered velocity and `p` satisfy the exact `ClassicalSolutionT.momentum` field
statement, and the exact `PeriodicLocalRegularity.projected` field statement, at
every interior time.  Lane 326's constructed `mildPressure g u` instantiates
both.

**Two general tools proved on the way**, both recorded as absent from the tree by
lane 326: the **periodic convolution theorem** and the **weight
submultiplicativity + convolution decay estimate**.

## 2. Lean 里现在有什么 / What is in Lean

New module `formalization/NSFormalization/Section3/T11/MildMomentum.lean`
(74 named declarations, 2 explicitly named local instances), namespace
`NSFormalization.Section3.T11`.

### The differentiation core

| name | statement (one line) |
|---|---|
| `torusCoeffCLM s i k` | coefficient evaluation as a continuous `ℝ`-linear functional on `PeriodicSobolev s` |
| `torusHeatSymbol_eq_exp` | `torusHeatSymbol ν r k = exp(−(ν|2πk|²) r)` for **all real** `r` |
| `torusHeatSymbol_hasDerivAt` | `d/dr σ(r,k) = −ν|2πk|² σ(r,k)` |
| `torusForcedPicard_real` | `rfl` unfolding of the Picard value at a real nonnegative time |
| `mild_coeff_duhamel` | scalar Duhamel identity for `(u t).1 i k`, with the endpoint-safe smoother replaced a.e. by `√W(k) σ(t−s,k)` |
| `heat_duhamel_hasDerivAt` | the forced scalar ODE: `d/dt ∫₀ᵗ σ(t−s,k)χ(s) ds = −ν|2πk|² ∫₀ᵗ σ(t−s,k)χ(s) ds + χ(t)` |
| **`mild_coeff_hasDerivAt`** | **(i), weighted form** |
| **`mild_physicalCoeff_hasDerivAt`** | **(i), physical form** |

### Decay machinery (locally uniform in time)

| name | statement |
|---|---|
| `persistence_weight_pow_le` | `W(k)^{N+2}‖v̂(t)(i,k)‖ ≤ ‖u_{2N+4}(t)‖` on `Ico 0 T` |
| `persistence_uniform_decay` | on every `Icc a b ⊆ Ico 0 T`: `∃ M, ∀ t ∈ Icc a b, W(k)^N‖v̂(t)(i,k)‖ ≤ M (W(k)²)⁻¹` |
| `periodicFrequencyWeight_shift_le` | `W(k) ≤ 2 W(l) W(k−l)` |
| `periodicFrequencyWeight_pow_shift_le`, `inv_pow_weight_shift_le` | the `n`-th power form and its inverse |
| `norm_periodicDerivativeSymbol_le` | `‖2πi k_j‖ ≤ W(k)` |
| `convolution_norm_bound` | summability **and** `∑'_l ‖c(l)d(k−l)‖ ≤ 2ⁿM²(∑W⁻²)·(W(k)ⁿ)⁻¹` from `‖c‖,‖d‖ ≤ M (W^{n+2})⁻¹` |
| `norm_torusConvectionCoeff_le`, `norm_torusPhysicalCoeff_bilinear_le` | the same for the (projected) convection symbol |
| `persistence_nonlinear_decay`, `persistence_force_decay`, `mildDerivCoeff_decay` | locally uniform rapid decay of `Q̂`, of `P̂F̂`, and of the whole derivative coefficient |

### The periodic convolution theorem and the convection identity

| name | statement |
|---|---|
| **`periodicFourierCoeff_mul`** | `(f·g)^(k) = ∑'_l ĝ(l) f̂(k−l)` for continuous periodic `f`, `g` with `∑‖ĝ‖ < ∞` |
| `eq_torusScalarSeries_of_summable` | a continuous periodic function with summable data is its own Fourier series |
| `convectionDivergenceT_component` | `(∇·(v⊗v))_i = ∑_j ∂_j(v_j v_i)` |
| `periodicFourierCoeff_convectionDivergenceT` | its Fourier data as `∑_j 2πi k_j ∑'_l v̂_j(l) v̂_i(k−l)` |
| `torusConvectionCoeff`, `torusPhysicalCoeff_convectionDatum`, `torusPhysicalCoeff_bilinear` | the contract's `bilinear` is `lerayAt k` of exactly that convolution |
| **`convectionDivergenceT_coeff`** | `(∇·(u⊗u))^_i(t,k) = torusConvectionCoeff (u t) (u t) i k`, i.e. the physical tensor divergence **is** the contract's nonlinearity |

### The Leray symbol on bare coefficient vectors

`lerayAt k w i`, `periodicLeray_eq_lerayAt` (`rfl`), `lerayAt_const_mul`,
`lerayAt_sub`, `norm_lerayAt_le` (`≤ 2∑_j‖w_j‖`), `torusPhysicalCoeff_leray`.

### The physical time derivative and the momentum equation

| name | statement |
|---|---|
| `mildDerivCoeff`, `mildDerivCoeff_neg`, `mildDerivCoeff_summable` | the derivative coefficient family, its conjugate symmetry and all-order summability |
| `mildTimeDerivative` | its Fourier inversion, a genuine `SpatialField` |
| `mildTimeDerivative_contDiff/_periodic/_coeff` | `C^∞`, unit periods, and Fourier data `= mildDerivCoeff` |
| **`torusPhysicalVelocity_hasDerivAt`** | `HasDerivAt (fun r ↦ v(r,x)) (mildTimeDerivative C P u t x) t` on `Ioo a b` |
| `temporalDerivative_torusPhysicalVelocity'` | the same in the problem statement's `temporalDerivative` spelling, on all of `Ioo 0 T` |
| `spatialLaplacian_component`, `periodicFourierCoeff_spatialLaplacian` | `(Δv)_i` and its Fourier symbol `−4π²|k|²` |
| `mildSourceCoeff_eq`, `mildDerivCoeff_eq_source` | `d/dt v̂ = −ν|2πk|² v̂ + lerayAt k Ŝ`, with `Ŝ = F̂ − Q̂` the physical source |
| **`momentum_of_pressure`** | `navierStokesResidual ν (torusPhysicalVelocity u) p t x = g (t,x)` on `Ioo 0 T` |
| **`projected_of_pressure`** | the `PeriodicLocalRegularity.projected` field, verbatim |
| `mildPressure_gradient_source_coeff` | lane 326's pressure has exactly the required gradient data (all `k`, including `k = 0`) |
| **`momentum_of_mildPressure`**, **`projected_of_mildPressure`** | the two fields for lane 326's constructed pressure |

`momentum_of_pressure` is conditional only on data hypotheses:
`TorusForcedMildOn C A P T u`, `ContinuousOn P (Icc 0 T)`,
`PersistenceInput T u`, `PersistenceInput T F`,
`∀ t ≥ 0, IsPeriodicLerayDatum (F t) (P t)`, `ContDiff ℝ ∞ g`,
`IsPeriodicOn univ g`, `IsPeriodicSobolevPath 3 g F`, smoothness/periodicity of
the pressure slices, the gradient-datum identity, and divergence-freeness (lane
320's `persistence_mild_physical_divergence`).  `PersistenceInput T F` is the
*same* predicate as for `u`, applied to the force datum path — not a new name.

### Non-vacuity

`mildMomentum_nonzero_instance`: an explicit contract `C`, the nonzero forced
family `u t = (1+t)•e₀` driven by the constant force `e₀`, the `TorusForcedMildOn`
witness, the `PersistenceInput`, the derivative formula at every interior time
and every `(i,k)`, and `u 0 ≠ 0`.  Plus an `example` applying
`periodicFourierCoeff_mul` to a genuine nonzero smooth periodic pair.

## 3. 缺口是什么 / What is not proved (exact residual statements)

1. **`ClassicalSolutionT.velocity_smooth`**

   ```lean
   ContDiffOn ℝ ∞ (torusPhysicalVelocity u) (Ico (0 : ℝ) T ×ˢ (univ : Set Space))
   ```

   The **first** time derivative is delivered; iterating it requires the mild
   equation at Sobolev orders `5, 7, …`, or equivalently differentiability of
   `t ↦ u t` in `PeriodicSobolev 3` (false unless `u(t) ∈ H⁵`).
   `TorusForcedMildOn` is an `H³ × H²` statement and `PersistenceInput` gives only
   continuity of the higher-order realizations, no equation for them.  See
   `ATTEMPTS_MILD_MOMENTUM.md` §3.1 for the precise reason and the two routes out
   (a higher-order forced mild construction, or parabolic smoothing in weighted
   time norms).

2. **`ClassicalSolutionT.pressure_smooth`** (lane 326's residual) is unchanged for
   the same reason; §3.2 of the ATTEMPTS file records that the three ingredients
   lane 326 listed as missing for the weaker joint-*continuity* statement are now
   all available in this module.

3. Out of scope and untouched: `sobolev`, `initial`, `divergence` (lane 320),
   the pressure fields (lane 326), and the general U9d existential target in
   `EXISTENCE_ROUTE.md`.

No target statement was weakened; no `def … : Prop` packaging a goal or a field
was introduced; the single input `PersistenceInput T u` named in the brief is
used exactly as given (and reused, unchanged, for the force path).

## 4. 跑了什么命令、什么结果 / Commands and results

```
cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T11.MildMomentum
  → ✔ [9987/9987] Built … Build completed successfully. 0 errors, 0 warnings in the new module.

cd verification && lake env lean ../formalization/NSFormalization/Section3/T11/MildMomentum.lean
  → no output (clean)

cd verification && lake env lean ../research/T11/probes/mild_momentum_closes.lean
  → no output (clean); every delivered target closes at its verbatim statement

cd verification && lake env lean ../research/T11/axioms_mild_momentum.lean
  → no output; all 74 `#guard_msgs` pass:
    every declaration depends on exactly [propext, Classical.choice, Quot.sound]

make check   (from the worktree root)
  → architecture checks OK; contract-policy tests OK; work items consistent

grep -n "sorry\|admit\|native_decide\|^axiom" on the new module → no matches
```
