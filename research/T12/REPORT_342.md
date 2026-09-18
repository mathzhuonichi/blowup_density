# Lane 342 report — T12 scalar tame product (`eq:Rproduct`, torus half)

## 1. What is proved

The `tameProduct` field of `research/T12/probes/api_on_canonical.lean`, verbatim
and unconditionally, with an explicit constant family and its positivity:

```lean
def tameProductConst (m : ℕ) : ℝ :=
  (4 : ℝ) ^ ((m : ℝ) / 2) * Real.sqrt torusInverseWeightSum

theorem tameProductConst_pos (m : ℕ) : 0 < tameProductConst m

theorem tameProduct :
    ∀ m : ℕ, 2 ≤ m → ∀ a b : Space → ℝ,
      MemPeriodicHmScalar m a → MemPeriodicHmScalar m b →
        periodicScalarSobolevENorm (m : ℝ) (fun x ↦ a x * b x) ≤
          ENNReal.ofReal (tameProductConst m) *
            (periodicScalarSobolevENorm 2 a * periodicScalarSobolevENorm (m : ℝ) b +
              periodicScalarSobolevENorm 2 b * periodicScalarSobolevENorm (m : ℝ) a)
```

`torusInverseWeightSum = ∑ₖ (1+4π²|k|²)^{-2}` is lane 336's lattice tail
constant (`Section3/T11/PairingBound.lean`), positive and finite there.  The
factor `4^{m/2}` is what lane 336's `torusWeightPeetre` supplies at exponent
`m/2` (the brief's `2^{m/2}` is not available from that lemma).

Existence of the product's order-`m` datum is part of the claim and is
**constructed**, not assumed: `periodicScalarSobolevENorm` is an infimum over
representing data, so the left-hand side is `⊤` unless a datum exists; the
`ℓ²` bound below *is* the membership proof of the weighted convolution
sequence, and periodicity plus Haar integrability of `torusLift (ab)` are
supplied from the factors (`MemLp.integrable_mul`).

Named intermediate results, all exported and all unconditional:

```lean
theorem torusYoungConvolution {Y γ : PeriodicFrequency → ℝ}
    (hY0 : ∀ k, 0 ≤ Y k) (hγ0 : ∀ k, 0 ≤ γ k)
    (hY : Summable fun k ↦ Y k ^ 2) (hγ : Summable γ) :
    (∀ k, Summable fun l ↦ Y l * γ (k - l)) ∧
      Summable (fun k ↦ (∑' l, Y l * γ (k - l)) ^ 2) ∧
        Real.sqrt (∑' k, (∑' l, Y l * γ (k - l)) ^ 2) ≤
          Real.sqrt (∑' k, Y k ^ 2) * (∑' k, γ k)

theorem periodicScalarSobolevENorm_eq {s : ℝ} {z : Space → ℝ} {A : PeriodicScalarData}
    (hA : IsPeriodicScalarDatum s z A) : periodicScalarSobolevENorm s z = ‖A‖ₑ

theorem exists_scalarDatum {s : ℝ} {z : Space → ℝ}
    (h : periodicScalarSobolevENorm s z ≠ ⊤) :
    ∃ A : PeriodicScalarData, IsPeriodicScalarDatum s z A

theorem scalarAbsCoeff_summable {z : Space → ℝ} {A : PeriodicScalarData}
    (hA : IsPeriodicScalarDatum 2 z A) :
    Summable (scalarAbsCoeff z) ∧
      (∑' k, scalarAbsCoeff z k) ≤ Real.sqrt torusInverseWeightSum * ‖A‖

theorem torusLift_ae_eq_series {f : Space → ℂ}
    (hf : MemLp (torusLift f) 2 periodicTorusMeasure)
    (hc : Summable fun k ↦ ‖periodicFourierCoeff f k‖) :
    torusLift f =ᵐ[periodicTorusMeasure]
      fun q ↦ ∑' k, periodicFourierCoeff f k * UnitAddTorus.mFourier k q

theorem periodicFourierCoeff_mul_of_series {f g : Space → ℂ}
    (hcf : Summable fun k ↦ ‖periodicFourierCoeff f k‖)
    (hfae : torusLift f =ᵐ[periodicTorusMeasure]
      fun q ↦ ∑' l, periodicFourierCoeff f l * UnitAddTorus.mFourier l q)
    (hg : Integrable (torusLift g) periodicTorusMeasure) (k : PeriodicFrequency) :
    periodicFourierCoeff (fun x ↦ f x * g x) k =
      ∑' l, periodicFourierCoeff f l * periodicFourierCoeff g (k - l)

theorem memPeriodicHmScalar_ofCoeff {m : ℕ} {c : PeriodicFrequency → ℂ}
    (hneg : ∀ k, c (-k) = star (c k)) (habs : Summable fun k ↦ ‖c k‖)
    (hcont : Continuous (torusScalarSeries c))
    (hw : Summable fun k ↦ (periodicFrequencyWeight k ^ ((m : ℝ) / 2) * ‖c k‖) ^ 2) :
    MemPeriodicHmScalar m (scalarOfCoeff c)
```

**Answer to the brief's open question.**  The convolution theorem is extended
from smooth to `H^m` scalars through the **`L²` representation**, not by
density: `torusLift_ae_eq_series` identifies the `L²` Fourier series of
`MemLp.toLp (torusLift a)` with the uniformly convergent series in `C(T³, ℂ)`
by uniqueness of sums in `L²`, and `periodicFourierCoeff_mul_of_series` is the
`MildPressure` argument with smoothness of the first factor replaced by that
a.e. identity plus absolute summability, and smoothness of the second replaced
by integrability of its lift.

## 2. Files

| file | content |
|---|---|
| `formalization/NSFormalization/Section3/T12/TameProduct.lean` | new module, 798 lines, namespace `NSFormalization.Section3.T12`; §1 weight/`ℓ²` helpers, §2 Young `ℓ² ∗ ℓ¹ ⊆ ℓ²`, §3 scalar data layer, §4 a.e. Fourier inversion, §5 the convolution theorem beyond smooth data, §6 `tameProductConst`/`tameProduct`, §7 non-vacuity constructor |
| `research/T12/probes/tame_product_closes.lean` | both API fields closed by `example … := tameProduct` / `tameProductConst_pos`, verbatim, plus the two-mode non-vacuity witness |
| `research/T12/axioms_tame_product.lean` | `#print axioms` for all 28 exported declarations |
| `research/T12/ATTEMPTS_TAME_PRODUCT.md` | routes taken and rejected, seven resolved elaboration errors with exact text |
| `research/T12/COMPARISON.md` | one appended status line |

Imports used: `Section3/T12/MeanZeroCalculus` (the T12 vocabulary),
`Section3/T10/Parseval` (`fourier_repr_toLp`, `memLp_torusLift_component`),
`Section3/T11/PairingBound` (`torusInverseWeight_summable`,
`torusInverseWeightSum`, `torusWeightPeetre`), `Section3/T11/MildPressure`
(`torusScalarSeries*`, `torusMFourier_norm`).  No existing module was edited.

Non-vacuity is genuine, not the zero field: the probe builds the two-mode
coefficient family supported exactly on `{e₀, -e₀}` with both values `1`
(physically `a(x) = 2 cos 2π x₁`), proves `MemPeriodicHmScalar m` for it at
**every** `m`, checks both Fourier modes equal `1`, checks the field is not
identically zero, and instantiates `tameProduct` at it.

## 3. Gaps

- **Nothing residual in the delivered statement.**  `tameProduct` is
  unconditional; there is no named `Prop` input, no `sorry`, no axiom.
- The constant `4^{m/2} (∑ₖ W(k)^{-2})^{1/2}` is not claimed to be sharp.  It
  is what the additive Peetre split plus one Cauchy--Schwarz give; a sharper
  constant would need a dyadic-shell argument (`appendix-a-local-theory.tex:44-47`).
- The **vector/tensor** corollary of `eq:Rproduct`
  (`appendix-a-local-theory.tex:50`, and the A03-style
  `tameProductVector` / `scalarSobolevENorm_component_le` /
  `sobolevENorm_le_sum_components` bridges listed as item (11) of
  `research/T12/COMPARISON.md` §"Proof dependencies") is **not** in scope of
  this lane and is not proved.  The scalar and vector carriers remain unrelated
  until that component pair lands.
- `periodicFourierCoeff_mul_of_series` is stated for one-sided hypotheses
  (summability + a.e. series on the *first* factor, integrability on the
  *second*).  A symmetric version was not needed and is not proved.
- The reconciliation's item (2), "`L¹`-Fourier uniqueness on the unit-volume
  torus", is **not** proved: the route here only needs the `L²` case, which
  Mathlib supplies.  Consumers that genuinely need the `L¹` statement still
  have to prove it.

## 4. Commands and results

```
cd <worktree> && LEAN_SEED_DIR=/data_8T/ping/blowup_density bash scripts/lean-install.sh
  → == OK (packages symlinked, lake test green)

cd verification && LEAN_NUM_THREADS=6 lake build \
  NSFormalization.Section3.T11.PairingBound \
  NSFormalization.Section3.T11.ClassicalRegularity \
  NSFormalization.Section3.T12.MeanZeroCalculus \
  NSFormalization.Section3.T10.Parseval
  → Build completed successfully (10000 jobs)

cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T12.TameProduct
  → ✔ Built NSFormalization.Section3.T12.TameProduct (5.9s); 0 errors, 0 warnings

cd verification && LEAN_NUM_THREADS=6 lake env lean \
  ../formalization/NSFormalization/Section3/T12/TameProduct.lean
  → rc=0, no output

cd verification && LEAN_NUM_THREADS=6 lake env lean \
  ../research/T12/probes/tame_product_closes.lean
  → rc=0, no output (both API fields close, two-mode witness accepted)

cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/T12/axioms_tame_product.lean
  → all 28 declarations: [propext, Classical.choice, Quot.sound]

make check   (worktree root)
  → contract/architecture checks OK; 13 policy tests OK;
    "45 work items: ownership, contract registration and task cards consistent."
```
