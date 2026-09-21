# Lane 305 — Fourier calculus

## Theorems and exact statements

Namespace: `NSFormalization.Section3.T10`. `spatialPartial` is
`NavierStokes.PeriodicIntegration.spatialPartial`. The Laplacian identification
uses T11 `scalarSpatialLaplacianT` on a time-independent real scalar field.
Repeated derivatives cover every natural order in one coordinate, and mixed
second partials are also exported. Rapid decay follows from the established
integer energy at order `2*N`, rather than iterating the Laplacian: this avoids
additional regularity machinery and yields the same requested bound.

```lean
theorem periodicFourierCoeff_fderiv {f : Space → ℂ} (hf : IsPeriodicSpatial f)
    (hs : ContDiff ℝ 1 f) (j : Fin 3) (k : PeriodicFrequency) :
    periodicFourierCoeff (fun x ↦ fderiv ℝ f x (coordinateVector j)) k =
      periodicDerivativeSymbol j k * periodicFourierCoeff f k
```

```lean
theorem periodicFourierCoeff_secondPartial {f : Space → ℂ} (hf : IsPeriodicSpatial f)
    (hs : ContDiff ℝ 2 f) (i j : Fin 3) (k : PeriodicFrequency) :
    periodicFourierCoeff (spatialPartial j (spatialPartial i f)) k =
      periodicDerivativeSymbol j k * periodicDerivativeSymbol i k * periodicFourierCoeff f k
```

```lean
theorem norm_periodicFourierCoeff_le (f : Space → ℂ) (k : PeriodicFrequency) :
    ‖periodicFourierCoeff f k‖ ≤ ∫ y, ‖torusLift f y‖ ∂periodicTorusMeasure
```

```lean
theorem summable_periodicFourierCoeff_of_h2 {f : Space → ℂ}
    (hf : IsPeriodicSpatial f) (hs : ContDiff ℝ 2 f) :
    Summable (periodicFourierCoeff f)
```

```lean
theorem summable_periodicFourierCoeff_of_smooth {f : Space → ℂ}
    (hf : IsPeriodicSpatial f) (hs : ContDiff ℝ ∞ f) :
    Summable (periodicFourierCoeff f)
```

```lean
theorem periodic_eq_tsum_mFourier {f : Space → ℂ} (hf : IsPeriodicSpatial f)
    (hs : Continuous f) (hc : Summable (periodicFourierCoeff f)) (x : Space) :
    f x = ∑' k, periodicFourierCoeff f k *
      Complex.exp ((2 * Real.pi * Complex.I : ℂ) * ∑ i, (k i : ℂ) * (x i : ℂ))
```

```lean
theorem norm_le_tsum_norm_periodicFourierCoeff {f : Space → ℂ}
    (hf : IsPeriodicSpatial f) (hs : Continuous f)
    (hc : Summable (periodicFourierCoeff f)) (x : Space) :
    ‖f x‖ ≤ ∑' k, ‖periodicFourierCoeff f k‖
```

```lean
theorem periodicFrequencyWeight_eq_paper1 (k : PeriodicFrequency) :
    periodicFrequencyWeight k = NSFormalization.Paper1.periodicFrequencyWeight k
```

```lean
theorem summable_weighted_periodicFourierCoeff {f : Space → ℂ}
    (hf : IsPeriodicSpatial f) (hs : ContDiff ℝ ∞ f) (s : ℝ) :
    Summable (fun k ↦ periodicFrequencyWeight k ^ s * ‖periodicFourierCoeff f k‖ ^ 2)
```

```lean
theorem periodicFourierCoeff_rapid_decay {f : Space → ℂ}
    (hf : IsPeriodicSpatial f) (hs : ContDiff ℝ ∞ f) (N : ℕ) :
    ∃ C : ℝ, ∀ k, periodicFrequencyWeight k ^ N * ‖periodicFourierCoeff f k‖ ≤ C
```

```lean
theorem summable_inverse_periodicFrequencyWeight :
    Summable (fun k : PeriodicFrequency ↦ (periodicFrequencyWeight k ^ 2)⁻¹)
```

```lean
theorem tsum_norm_periodicFourierCoeff_le {f : Space → ℂ}
    (hE : Summable (fun k ↦ periodicFrequencyWeight k ^ 2 * ‖periodicFourierCoeff f k‖ ^ 2)) :
    (∑' k, ‖periodicFourierCoeff f k‖) ≤
      Real.sqrt (∑' k, (periodicFrequencyWeight k ^ 2)⁻¹) *
      Real.sqrt (∑' k, periodicFrequencyWeight k ^ 2 * ‖periodicFourierCoeff f k‖ ^ 2)
```

```lean
theorem periodicFourierCoeff_iteratedFDeriv {f : Space → ℂ}
    (hf : IsPeriodicSpatial f) (hs : ContDiff ℝ ∞ f) (j : Fin 3) (m : ℕ)
    (k : PeriodicFrequency) :
    periodicFourierCoeff ((spatialPartial j)^[m] f) k =
      periodicDerivativeSymbol j k ^ m * periodicFourierCoeff f k
```

```lean
theorem norm_periodicFourierCoeff_iterated_le {f : Space → ℂ}
    (hf : IsPeriodicSpatial f) (hs : ContDiff ℝ ∞ f) (j : Fin 3) (m : ℕ)
    (k : PeriodicFrequency) :
    ‖periodicDerivativeSymbol j k ^ m * periodicFourierCoeff f k‖ ≤
      ∫ y, ‖torusLift ((spatialPartial j)^[m] f) y‖ ∂periodicTorusMeasure
```

```lean
theorem periodic_component_eq_tsum {v : NSFormalization.Section4.A02.SpatialField}
    (hp : IsPeriodicSpatial v) (hs : Continuous v)
    (hc : ∀ i, Summable (periodicFourierCoeff (fun x ↦ (v x i : ℂ))))
    (i : Fin 3) (x : Space) :
    (v x i : ℂ) = ∑' k, periodicFourierCoeff (fun y ↦ (v y i : ℂ)) k *
      Complex.exp ((2 * Real.pi * Complex.I : ℂ) * ∑ j, (k j : ℂ) * (x j : ℂ))
```

```lean
theorem periodicFourierCoeff_laplacian {f : Space → ℂ}
    (hp : IsPeriodicSpatial f) (hs : ContDiff ℝ 2 f) (k : PeriodicFrequency) :
    periodicFourierCoeff (fun x ↦ ∑ j : Fin 3, spatialPartial j (spatialPartial j f) x) k =
      (-(4 * Real.pi ^ 2 * ∑ j : Fin 3, (k j : ℝ) ^ 2) : ℂ) *
        periodicFourierCoeff f k
```

```lean
theorem scalarSpatialLaplacianT_eq (f : Space → ℝ) (t : ℝ) (x : Space) :
    NSFormalization.Section3.T11.scalarSpatialLaplacianT (fun z ↦ f z.2) t x =
      ∑ j : Fin 3, spatialPartial j (spatialPartial j f) x
```

```lean
theorem summable_periodicFourierCoeff_component_of_smooth
    {v : NSFormalization.Section4.A02.SpatialField} (hp : IsPeriodicSpatial v)
    (hs : ContDiff ℝ ∞ v) (i : Fin 3) :
    Summable (periodicFourierCoeff (fun x ↦ (v x i : ℂ)))
```

```lean
theorem spatialPartial_complexify {f : Space → ℝ} (hs : ContDiff ℝ 1 f)
    (j : Fin 3) :
    spatialPartial j (fun x ↦ (f x : ℂ)) = fun x ↦ ((spatialPartial j f x : ℝ) : ℂ)
```

```lean
theorem periodicFourierCoeff_scalarSpatialLaplacianT {f : Space → ℝ}
    (hp : IsPeriodicSpatial f) (hs : ContDiff ℝ 2 f) (t : ℝ)
    (k : PeriodicFrequency) :
    periodicFourierCoeff (fun x ↦
      (NSFormalization.Section3.T11.scalarSpatialLaplacianT (fun z ↦ f z.2) t x : ℂ)) k =
      (-(4 * Real.pi ^ 2 * ∑ j : Fin 3, (k j : ℝ) ^ 2) : ℂ) *
        periodicFourierCoeff (fun x ↦ (f x : ℂ)) k
```

```lean
theorem norm_periodicFourierCoeff_coordinate_decay {f : Space → ℂ}
    (hf : IsPeriodicSpatial f) (hs : ContDiff ℝ ∞ f) (j : Fin 3) (m : ℕ)
    (k : PeriodicFrequency) :
    ‖(2 * Real.pi * (k j : ℝ)) ^ m‖ * ‖periodicFourierCoeff f k‖ ≤
      ∫ y, ‖torusLift ((spatialPartial j)^[m] f) y‖ ∂periodicTorusMeasure
```

```lean
theorem norm_component_le_tsum_norm_periodicFourierCoeff
    {v : NSFormalization.Section4.A02.SpatialField} (hp : IsPeriodicSpatial v)
    (hs : ContDiff ℝ ∞ v) (i : Fin 3) (x : Space) :
    ‖v x i‖ ≤ ∑' k, ‖periodicFourierCoeff (fun y ↦ (v y i : ℂ)) k‖
```

```lean
theorem periodicFourierCoeff_gradient_sq {f : Space → ℂ}
    (hp : IsPeriodicSpatial f) (hs : ContDiff ℝ 1 f) (k : PeriodicFrequency) :
    (∑ j : Fin 3, ‖periodicFourierCoeff (spatialPartial j f) k‖ ^ 2) =
      (4 * Real.pi ^ 2 * ∑ j : Fin 3, (k j : ℝ) ^ 2) * ‖periodicFourierCoeff f k‖ ^ 2
```

## Files

- `formalization/NSFormalization/Section3/T10/FourierCalculus.lean`
- `research/T10/axioms_fourier_calculus.lean`
- `research/T10/probes/fourier_calculus_examples.lean`
- `research/T10/ATTEMPTS_FOURIER_CALCULUS.md`
- `research/T10/REPORT_305.md`

All are new files. No instances or heartbeat overrides were introduced.

## Scope and gaps

The scalar requested conclusions are proved. Decay uses all-order Parseval
energy rather than a separate theorem for powers of the Laplacian.
The iterated theorem covers repeated coordinate derivatives, not an arbitrary
list of distinct coordinates; mixed second derivatives are explicit.
Vector exports are componentwise summability, inversion, and the component
sup bound. A packaged vector H² datum constructor, vector Laplacian norm
identity, Lambda representative, and T12 embeddings are not asserted here.
The frequencywise full-gradient identity is proved; its physical integrated
counterpart is available through Paper1's existing H¹ energy theorem, not
re-exported as a vector integrated identity in this module.
No unresolved Lean errors remain. Resolved errors are in ATTEMPTS.

## Commands and results

Every Lean invocation sourced `scripts/lean-env.sh`, ran from `verification/`,
and used `LEAN_NUM_THREADS=6`.

- `lake build NSFormalization.Section3.T10.FourierCalculus`: PASS, 0 errors.
- `lake env lean ../formalization/NSFormalization/Section3/T10/FourierCalculus.lean`: PASS.
- `lake env lean ../research/T10/probes/fourier_calculus_examples.lean`: PASS.
- `lake env lean ../research/T10/axioms_fourier_calculus.lean`: PASS; every named
  declaration prints exactly `[propext, Classical.choice, Quot.sound]`.
- Root `make check`: PASS.
- Root `make test`: PASS.
- Root `make test-mutations`: PASS; all three negative mutations rejected.

No push, merge, rebase, or edits to existing tracked files.
