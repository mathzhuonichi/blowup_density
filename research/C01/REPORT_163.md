# Lane 163-C01-e5-enstrophy report

## 1. Theorems proved

All declarations are in namespace `NSFormalization.Section4.C01` in
`formalization/NSFormalization/Section4/C01/Enstrophy.lean`.

- `wordEnergy_one (A : SmoothL2Field Space)`:
  `wordEnergy 1 A = wordEnergy 0 A + ∑ i : Fin 3, ‖(A.directionalField (axis i)).toLp‖ ^ 2`.
- `wordInner_sum_one (X Y : SmoothL2Field Space)`:
  `∑ n ∈ range (1+1), ∑ w : Fin n → Fin 3, ⟪(wordField X w).toLp,
  (wordField Y w).toLp⟫` equals
  `⟪X.toLp,Y.toLp⟫ + ∑ i : Fin 3,
  ⟪(X.directionalField (axis i)).toLp,(Y.directionalField (axis i)).toLp⟫`.
- `enstrophyDerivative_hasDerivAt (w) (hf) (hc : 0<c) (hcS : c≤S)
  (hST : S<T) (hr : r∈Ioo 0 (S-c))`: the exact shifted-window statement at
  `Enstrophy.lean:73-91`, namely
  `HasDerivAt (ρ ↦ ∑ᵢ ‖∂ᵢ velocityField(projIcc(ρ)+c)‖²)
  (2∑ᵢ⟪∂ᵢ velocitySliceField(r+c), ∂ᵢ temporalSliceField(r+c)⟫) r`.
  Both fields and all norms/pairings are the carrier-B `.directionalField`/`.toLp`
  expressions displayed in the source statement.
- `directional_pairing_sum_eq_neg_laplacian (A B : SmoothL2Field Space)`:
  `∑ᵢ ⟪(A.directionalField (axis i)).toLp,
  (B.directionalField (axis i)).toLp⟫ = -⟪(laplacianField A).toLp,B.toLp⟫`.
- `enstrophyDerivative_eq_neg_laplacian (w) (hf) (ht : t∈Ioo 0 T)`:
  `2∑ᵢ⟪∂ᵢ velocitySliceField(t),∂ᵢ temporalSliceField(t)⟫ =
  -2⟪ laplacianField(velocitySliceField(t)),temporalSliceField(t)⟫`.
- `enstrophyDerivative_classical_unconditional (w) (hf) (ht : t∈Ioo 0 T)`:
  ```lean
  HasDerivAt
    (fun s : ℝ => ∫ x, ∑ i : Fin 3,
      ‖fderiv ℝ (fun y : Space => w.velocity (s, y)) x (axis i)‖ ^ 2)
    (-2 * inner ℝ
      (laplacianField (velocitySliceField w (Ioo_subset_Ico_self ht))).toLp
      (temporalSliceField w hf ht).toLp)
    t
  ```

## 2. What is in Lean now

E5 is complete.  The order-one vendor derivative identity is subtracted from its
order-zero part on the same translated window.  The common energy/pairing terms cancel,
leaving exactly the three first-derivative terms.  Summed ordinary integration by parts
then changes these to the negative Laplacian pairing.  The final theorem chooses
`c=t/2`, `S=(t+T)/2`, undoes the shift, and uses `gradientSq_eq_sum` locally to state the
left side as a global, clamp-free raw integral.

`research/C01/axioms_e5.lean` audits every declaration and contains non-vacuous
instantiations on `A04.zeroSol` with `A04.memForceR_zero`.  `ENERGY_SPLIT.md` marks E5 DONE.

## 3. Gaps

There is no residual in E5.  E6 (the pressure/Laplacian cancellation), E7 (the arithmetic
core), and their assembly into the specification's full `enstrophyIdentity` are separate
rows and remain open; this lane does not claim them.

The target build exits successfully.  Lake replays pre-existing warnings from imported
modules, so its terminal output is not byte-empty; the new `Enstrophy` module itself emits
no warning.  Direct `lake env lean` on the module is byte-empty.

## 4. Commands and results

```text
$ cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.C01.Enstrophy
...
Build completed successfully (10303 jobs).
exit 0
```

The omitted lines are replayed linter warnings in existing imported modules.

```text
$ cd verification && lake env lean ../formalization/NSFormalization/Section4/C01/Enstrophy.lean
<no output>
exit 0
```

```text
$ cd verification && lake env lean ../research/C01/axioms_e5.lean
'NSFormalization.Section4.C01.wordEnergy_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.C01.wordInner_sum_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.C01.enstrophyDerivative_hasDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.C01.directional_pairing_sum_eq_neg_laplacian' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.C01.enstrophyDerivative_eq_neg_laplacian' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.C01.enstrophyDerivative_classical_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0
```

```text
$ make check
...
Ran 13 tests in 0.043s

OK
python3 experiments/check_work_queue.py
30 work items: ownership, contract registration and task cards consistent.
exit 0
```
