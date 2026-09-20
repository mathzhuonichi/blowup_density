# Lane 170-C01-e6-e7-enstrophy-identity report

## 1. Theorems proved

All declarations are in namespace `NSFormalization.Section4.C01`, in
`formalization/NSFormalization/Section4/C01/EnstrophyIdentity.lean`.

- `laplacianField_divergence_zero (U) (hdiv) (x)`:
  ```lean
  divergence (laplacianField U).field x = 0
  ```
  for `hdiv : ∀ x, divergence U.field x = 0`.
- `laplacian_pressure_pairing_zero (w) (hf) (ht : t ∈ Ioo 0 T)`:
  ```lean
  ⟪(laplacianField (velocitySliceField w (Ioo_subset_Ico_self ht))).toLp,
    (pressureGradientField w hf ht).toLp⟫_ℝ = 0
  ```
- `inner_enstrophy_identity_deriv (L N P F Gt)`:
  ```lean
  d = -2 * ⟪L, Gt⟫ →
  Gt = ν • L - N - P + F →
  ⟪L, P⟫ = 0 →
  d = 2 * ⟪N, L⟫ - 2 * ν * ‖L‖ ^ 2 - 2 * ⟪F, L⟫
  ```
  on every real inner-product space.
- `enstrophyDerivative_value_classical (w) (hf) (ht : t ∈ Ioo 0 T)`: the exact
  carrier-B value identity
  ```lean
  -2 * ⟪Δu.toLp, (∂ₜu).toLp⟫ =
    2 * ∫ x, ⟪((u·∇)u).field x, Δu.field x⟫_ℝ -
    2 * ν * ∫ x, ‖Δu.field x‖ ^ 2 -
    2 * ∫ x, ⟪f.field x, Δu.field x⟫_ℝ
  ```
  where every displayed field is exactly the corresponding
  `velocitySliceField`/`temporalSliceField`/`forceSliceField`,
  `advectionField`, or `laplacianField` expression in the source signature.
- `enstrophyIdentity_classical (w) (hf) (ht : t ∈ Ioo 0 T)`: the requested raw-integral
  E6 identity
  ```lean
  HasDerivAt
    (fun s : ℝ => ∫ x, ∑ i : Fin 3,
      ‖fderiv ℝ (fun y : Space => w.velocity (s, y)) x (axis i)‖ ^ 2)
    (2 * ∫ x, ⟪((u·∇)u).field x, Δu.field x⟫_ℝ -
      2 * ν * ∫ x, ‖Δu.field x‖ ^ 2 -
      2 * ∫ x, ⟪f.field x, Δu.field x⟫_ℝ) t
  ```
  with the abbreviated fields expanded exactly as in `enstrophyDerivative_value_classical`.
- `enstrophyIdentity_gradientSq (w) (hf) (ht : t ∈ Ioo 0 T)`: the local
  spec-vocabulary form
  ```lean
  HasDerivAt (fun s => gradientSq (slice w.velocity s))
    (2 * advectionWork (slice w.velocity t) -
      2 * ν * laplacianSq (slice w.velocity t) -
      2 * pairing (slice f t) (A05.lap (slice w.velocity t))) t
  ```
- `h2TimeIntegral_strict (w) (_hS : 0 < S) (hST : S < T)`:
  ```lean
  (∫⁻ t in Ioo (0 : ℝ) S,
    sobolevENorm 2 (slice w.velocity t) ^ (2 : ℝ)) ≠ ⊤
  ```
- `squaredHTwoIntegral_strict (w) (hS : 0 < S) (hST : S < T)`, the exact A04
  natural-power spelling:
  ```lean
  (∫⁻ t in Ioo (0 : ℝ) S,
    sobolevENorm 2 (slice w.velocity t) ^ (2 : ℕ)) ≠ ⊤
  ```
- `h2TimeIntegral_of_absorption (_hν) (_ha) (_hf) (w) (hS) (hST) (_habs)` has the
  same rpow conclusion as `h2TimeIntegral_strict`, under the exact instantiated C01 V1 gate
  ```lean
  ∀ t ∈ Ico (0 : ℝ) S,
    ENNReal.ofReal A05.gradientL6Const * criticalL3 (slice w.velocity t) ≤
      ENNReal.ofReal (ν / 4)
  ```
  together with `0 < ν`, `a ∈ initialClassR`, `MemForceR f`, `0 < S`, and `S < T`.

## 2. What is in Lean now

E6 and the E7 algebraic row are complete.  The existing E5 derivative is paired with lane
143's `momentum_split_toLp`; pressure is removed using the existing gradient cancellation
after proving `Δu` divergence free.  Both the raw-integral identity and the local
`gradientSq`/`advectionWork`/`laplacianSq`/`pairing` statement are available at every interior
time.

For the H² input, Lean now proves genuine lower-integral finiteness on every strict compact
subinterval `0 < S < T`, without needing absorption.  The proof uses the continuous
order-two datum path already present in `ClassicalSolutionR.sobolev`.  Both C01's real-power
and A04's natural-power spellings are present; the latter reuses lane 159's exponent pin.

`research/C01/axioms_e6e7.lean` audits all nine declarations.  Every declaration prints
exactly `[propext, Classical.choice, Quot.sound]`.  Its non-vacuity examples instantiate the
pressure theorem, both identity forms, and the absorption-shaped H² theorem on
`A04.zeroSol 1 2` using `A04.memForceR_zero`.

`ENERGY_SPLIT.md` marks E6, E7, and `enstrophyIdentity` DONE and the quantitative
`h2TimeIntegral` row PARTIAL.  `ATTEMPTS_E6E7.md` records the successful routes, failed
normalizations, exact endpoint residual, and the C01 V4 plan.  V4 should extend V3; no
contract was registered in this lane.

## 3. Gaps

The quantitative `research/C01/Spec.lean:h2TimeIntegral` and
`h2TimeIntegralZeroDatum` fields are not proved.  The current theorem requires `S < T`; the
spec permits `S ≤ T` and asserts an explicit `ENNReal.ofReal (Cassembly * ...)` upper bound.
The retained endpoint probe gives:

```text
Application type mismatch: The argument
  hST
has type
  S ≤ T
but is expected to have type
  S < T
in the application
  h2TimeIntegral_strict w hS hST
```

After the required `grep -rn` search of all
`Section4/{D01,A03,A04,A05,A01,C01}`, the two needed analytic inputs remain absent; the
probe reports exactly:

```text
Unknown identifier `sobolevTwoFourier`
Unknown identifier `enstrophyIntegralBound`
```

The exact residual is therefore: prove the integrated absorbed estimate
`enstrophyIntegralBound`, then the carrier-crossing order-two inequality
`sobolevTwoFourier`; assemble them with the registered `l2Bound` and `forceTimeRegularity`.
No missing scalar Grönwall lemma blocks the strict-interior finiteness result.

## 4. Commands and results

```text
$ cd verification && LEAN_NUM_THREADS=6 lake build \
    NSFormalization.Section4.C01.EnstrophyIdentity
Build completed successfully (10324 jobs).
exit 0
```

Lake replayed only pre-existing warnings from imported modules; the new module emits no
warning.  Direct checking is byte-empty:

```text
$ cd verification && lake env lean \
    ../formalization/NSFormalization/Section4/C01/EnstrophyIdentity.lean
<no output>
exit 0
```

```text
$ cd verification && lake env lean ../research/C01/axioms_e6e7.lean
<nine declarations, each [propext, Classical.choice, Quot.sound]>
exit 0
```

```text
$ make check
...
Ran 13 tests in 0.042s
OK
30 work items: ownership, contract registration and task cards consistent.
exit 0
```
