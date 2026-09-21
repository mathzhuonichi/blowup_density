# Lane 163 — C01 row E5 attempts and result

## Result

Row E5 is closed in `Section4/C01/Enstrophy.lean`, with no placeholders and the standard
three transitive axioms.  The proof follows the planned carrier-B route:

1. `wordEnergy_one` and `wordInner_sum_one` identify the new order-one layer using
   `(Fin 1 → Fin 3) ≃ Fin 3` (`Equiv.funUnique`).
2. `enstrophyDerivative_hasDerivAt` repeats E4's translated window construction, applies
   `wordEnergy_hasDerivWithinAt` at `s = 1` and `s = 0`, and subtracts.
3. `directional_pairing_sum_eq_neg_laplacian` sums `field_directional_inner` with
   `A.directionalField (axis i)` as its first field and identifies the sum of second
   derivatives with `laplacianField A`.
4. `enstrophyDerivative_classical_unconditional` chooses `c=t/2`,
   `S=(t+T)/2`, undoes the translation, and replaces the clamped carrier expression by the
   global raw integral near `t` through `gradientSq_eq_sum`.

## Attempts and pitfalls

### Order-one finite sum

A direct simplification did not reindex the functions `Fin 1 → Fin 3`.  The residual was:

```text
A : SmoothL2Field Space
⊢ ∑ n ∈ Finset.range 2, ∑ w, ‖(wordField A w).toLp‖ ^ 2 =
    ‖A.toLp‖ ^ 2 + ∑ i, ‖(A.directionalField (axis i)).toLp‖ ^ 2
```

The successful bridge is `Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin 3))`; its term
equality is `rfl` because a one-letter `wordField` is definitionally the corresponding
`directionalField`.

### Subtracting the two derivative identities

Using `convert hdiff using 1` exposed an instance-diamond equality before reaching the
function equality:

```text
⊢ Real.instAddCommGroup = Real.normedAddCommGroup.toAddCommGroup
```

The stable route is to `change` the theorem goal to the local paths `A` and `B`, normalize
the scalar derivative by a separate `ring` equality, and replace
`(E₀ + E₁) - E₀` by `E₁` through `HasDerivAt.congr_of_eventuallyEq` pointwise.

### Clamp-free raw-integral bridge

A direct `rw [← gradientSq_eq_sum ...]` failed to find the integral because the target had
the manuscript `Space` spelling while the bridge elaborated the vendor `Space` spelling:

```text
Tactic `rewrite` failed: Did not find an occurrence of the pattern
  ∫ x, ∑ i, ‖fderiv ℝ (velocityField ...).field x (axis i)‖ ^ 2
```

An explicitly typed local equality, proved by
`simpa only [velocityField_field] using (gradientSq_eq_sum ...).symm`, avoids unfolding or
instance search across that alias boundary.

## Scope after this lane

E5 itself has no residual.  Rows E6 (pressure cancellation), E7 (the arithmetic assembly),
and the full `enstrophyIdentity` remain separate rows and were not claimed here.
