# REPORT 326 — T11 U9d2a: the pressure of the mild solution

Lane `326-T11-U9d2a-pressure`, branch `erenup/326-T11-U9d2a-pressure`.
Partial but unconditional-modulo-`PersistenceInput` delivery. No new named
input; no `sorry`/`admit`/`axiom`/`native_decide`.

## 1. 证了哪个定理 / What is proved

**The pressure is constructed, not assumed.** For a smooth unit-periodic
physical force `g` and a coefficient path `u` satisfying lane 320's
`PersistenceInput T u`:

* the **coefficient pressure** is the Leray complement of the physical source
  `S(t) = g(t,·) − ∇·(u⊗u)(t,·)`: at `k ≠ 0`,
  `p̂(t)(k) = (k · Ŝ(t,k)) / (2πi |k|²)`, and `p̂(t)(0) = 0` (the gauge);
* the **physical pressure** is its scalar Fourier inversion
  `p(t,x) = Re ∑' k p̂(t)(k) e^{2πi k·x}`;
* the defining identity is proved **against T10's Leray symbol**: for every
  Sobolev order `s` and every datum `B` of the source,
  `2πi k_i p̂(k) = Ŝ_i(k) − W(k)^{−s/2} · periodicLeray s B i k`;
* the **Poisson equation** `Δp = ∇·f − ∇·(∇·(u⊗u))` holds pointwise on
  `Ico 0 T × ℝ³`, in the exact `PeriodicLocalRegularity.pressure_poisson` shape;
* the **gauge**, **periodicity**, **spatial smoothness** and the
  **`pressure_gradient` `MemLp`** fields hold;
* the construction is **nonzero** on a concrete instance.

## 2. Lean 里现在有什么 / What is in Lean

New module `formalization/NSFormalization/Section3/T11/MildPressure.lean`
(80 named declarations, 2 explicitly named local instances). Namespace
`NSFormalization.Section3.T11`.

### The construction

| name | statement (one line) |
|---|---|
| `torusScalarSeries c x` | `∑' k, c k * periodicCharacter k x` — the scalar inversion used by the pressure |
| `sourceComponentCoeff S j k` | `periodicFourierCoeff (fun x ↦ ((S x j : ℝ) : ℂ)) k` |
| `lerayPotentialCoeff S k` | `if k = 0 then 0 else (∑ j, k_j Ŝ_j(k)) / ((2πi)·(∑ j k_j²))` |
| `lerayPotential S x` | `(torusScalarSeries (lerayPotentialCoeff S) x).re` |
| `mildPressureSource g u z` | `g z − convectionDivergenceT (torusPhysicalVelocity u) z.1 z.2` |
| `mildPressureCoeff g u t k` | `lerayPotentialCoeff (fun x ↦ mildPressureSource g u (t,x)) k` |
| `mildPressure g u` | `fun z ↦ lerayPotential (fun x ↦ mildPressureSource g u (z.1,x)) z.2` |

### The Leray-complement identities (item (i)/(iii) of the brief)

* `periodicDerivativeSymbol_mul_lerayPotentialCoeff` —
  `2πi k_i p̂(k) = (k_i/|k|²) (k · Ŝ(k))` for `k ≠ 0`.
* `lerayPotentialCoeff_leray_complement` —
  `periodicDerivativeSymbol i k * lerayPotentialCoeff S k =
   torusPhysicalCoeff s B i k − (W(k)^{−s/2}) * periodicLeray s B i k`
  for every `hB : IsPeriodicDatum s S B` and `k ≠ 0`. This is literally
  `(I − P) Ŝ` in the T10 symbol.
* `mildPressure_gradient_coeff` —
  `periodicFourierCoeff ((∂_i p(t,·)) : ℂ) k = periodicDerivativeSymbol i k * mildPressureCoeff g u t k`.
* `mildPressure_gradient_leray_complement` — the same in `(I − P)`-form: `∇p` has
  datum `(I − P)(F − Q)`.
* `mildPressureSourceCoeff_eq_force_sub_convection` —
  `Ŝ_j(t,k) = torusPhysicalCoeff 3 (F t) j k − periodicFourierCoeff ((∇·(u⊗u))_j(t,·)) k`,
  i.e. the source really is `F − Q` in physical Fourier data.

### The `ClassicalSolutionT` / `PeriodicLocalRegularity` pressure fields

| field | theorem | status |
|---|---|---|
| `pressure_periodic` | `mildPressure_periodic` (on `univ`) | proved |
| `pressure_gauge` | `mildPressure_gauge` | proved |
| `pressure_gradient` | `mildPressure_gradient_memLp` | proved |
| `pressure_smooth` | `mildPressure_spatial_contDiff` | **spatial slices only** |
| `PeriodicLocalRegularity.pressure_poisson` | `mildPressure_poisson` | proved |

Bundled as `MildPressureFields g u T`, built by
`mildPressure_fields (hg : ContDiff ℝ ∞ g) (hgp : IsPeriodicOn univ g) (hu : PersistenceInput T u)`.
`MildPressureFields` is a **conclusion**, not a hypothesis: it is produced from
the three inputs above and consumed by the assembly lane.

### Reusable general machinery (stated for arbitrary smooth periodic data)

`summable_weight_pow_mul_coeff` (all-order weighted absolute summability of the
Fourier coefficients of a smooth periodic function), `torusScalarSeries_coeff`
(scalar inversion recovers the coefficients), `torusScalarSeries_contDiff`,
`periodic_eq_of_coeff_eq` (two smooth periodic scalars with equal Fourier data
are equal), `periodicFourierCoeff_divergence`, `lerayPotentialCoeff_laplace_symbol`
(`−4π²|k|² p̂(k) = 2πi k·Ŝ(k)`), `spatialDivergence_eq_sum`,
`pressureGradient_component`, `convectionDivergenceT_spatial_contDiff/_periodic`.

### Non-vacuity

`mildPressure_nonzero_instance`: with the one-mode smooth periodic force
`testPressureSource testFrequency` and the genuine persistent path
`u t = (1+t) • torusConstantDatum 3 e₀` (`persistence_affine_constant`), all
fields of `MildPressureFields` hold **and** the constructed pressure slice at
`t = 0` is not the zero function (`lerayPotential_test_ne_zero`, via a nonzero
Fourier coefficient at the mode `e₀`).

## 3. 缺口是什么 / What is not proved (exact residual statements)

1. **`ClassicalSolutionT.pressure_smooth` in its joint slab shape**

   ```lean
   ContDiffOn ℝ ∞ (mildPressure g u) (Ico (0 : ℝ) T ×ˢ (univ : Set Space))
   ```

   Not derivable from the permitted input. `PersistenceInput T u` supplies only
   `ContinuousOn u_m (Ico 0 T)`; nothing constrains any time derivative of
   `t ↦ u t`, hence none of `t ↦ p̂(t)(k)`. Closing it needs the Duhamel
   differentiation of `TorusForcedMildOn` (open since lane 313/320) or a further
   named input, which this lane was forbidden to introduce.

2. **Joint continuity** `ContinuousOn (mildPressure g u) (Ico 0 T ×ˢ univ)` is
   reachable in principle but needs (a) the periodic convolution theorem
   `periodicFourierCoeff (f·g) k = ∑' l, f̂(l) ĝ(k−l)`, which is **not** in the
   tree, (b) locally uniform-in-`t` weighted bounds on the convection
   coefficients, (c) joint continuity of the first spatial derivatives of
   `torusPhysicalVelocity u` (lane 318 gives only the field). See
   `ATTEMPTS_MILD_PRESSURE.md` §3.2.

3. Out of scope and untouched: `momentum` / `projected`, `velocity_smooth`, and
   the final classical assembly. The general U9d existential target in
   `EXISTENCE_ROUTE.md` is unchanged.

No target statement was weakened, and no `def … : Prop` packaging a goal or a
field was introduced.

## 4. 跑了什么命令、什么结果 / Commands and results

```
cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T11.MildPressure
  → Build completed successfully (9986 jobs). 0 errors, 0 warnings in the new module.

cd verification && lake env lean ../formalization/NSFormalization/Section3/T11/MildPressure.lean
  → no output (clean)

cd verification && lake env lean ../research/T11/probes/mild_pressure_closes.lean
  → no output (clean); every delivered field closes at the verbatim statement

cd verification && lake env lean ../research/T11/axioms_mild_pressure.lean
  → no output; all 80 `#guard_msgs` pass.
    78 declarations: [propext, Classical.choice, Quot.sound];
    `testFrequency`, `testFrequency_ne_neg`: [propext] (a strict subset).

make check   → architecture checks OK; 13 contract-policy tests OK;
               45 work items consistent.
make test    → all registered contracts replay: "standard logical axioms only".

grep -n "sorry\|admit\|native_decide\|^axiom" on the new module → no matches.
```
