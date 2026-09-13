import NSFormalization.Section4.A02.SolutionClass
import NSFormalization.Section4.D01.DatumToJets
import NSFormalization.Section4.A03.BoundedRepresentative
import NSFormalization.Section4.A05.SmoothJets

/-!
# A02 unit U1b — the sup-bound half of the uniqueness hypotheses

`research/A02/COMPARISON.md` §3 splits A02's implication **I1** into the energy
half (**U1a**, `Section4/A02/Energy.lean`) and the sup-bound half (**U1b**, this
module).  U1b supplies the two hypotheses of
`NSFormalization.Source.BoundedViscosityUniqueness.classical_uniqueness_on_Icc`
(`Source/BoundedViscosityUniqueness.lean:23`) that a `ClassicalSolutionR` does
*not* carry as a field, on every closed subinterval `Icc 0 b` with `0 ≤ b < T`:

```
∃ B, 0 ≤ B ∧ ∀ t ∈ Icc 0 b, ∀ x, ‖u.velocity (t,x)‖ ≤ B                 (velocity)
∃ G, 0 ≤ G ∧ ∀ t ∈ Icc 0 b, ∀ x, ‖spatialDerivative u.velocity t x‖ ≤ G (gradient)
```

with `spatialDerivative = NavierStokes.ProblemStatement.spatialDerivative`
(`vendor/…/NavierStokes/ProblemStatement.lean:59`).

## The four sub-steps (COMPARISON.md U1b(i)–(iv))

* **(i) `H² ↪ L^∞` pointwise on the jet class.**  `A03.enorm_le_jetENorm`
  (`Section4/A03/BoundedRepresentative.lean:165`), the everywhere-pointwise bound
  `‖z x‖ₑ ≤ C · jetENorm 2 z` on `A03.SmoothL2UpTo 2`.  The velocity slice is in
  that class by `D01.smoothSquareIntegrableJets_slice`
  (`Section4/D01/DatumToJets.lean:396`), which starts exactly at
  `ClassicalSolutionR.velocity_smooth` + `ClassicalSolutionR.sobolev`; the jet
  `H²` norm is bounded by the manuscript datum norm through
  `D01.jetSobolevENorm_le_sobolevENorm` (`DatumToJets.lean:343`).

* **(ii) the order shift for `∇u`.**  The datum-side shift
  `‖∂ᵢu‖_{H²} ≤ ‖u‖_{H³}` is *open* in the datum carrier
  (`Section4/D01/SmoothDatum.lean:388` records `exists_isSobolevDatum_fderiv` as a
  non-quantitative existence only).  This module proves instead the **jet-side**
  order shift `jetENorm_dirDeriv_le : jetENorm 2 (∂ᵢw) ≤ jetENorm 3 w`, by the
  pointwise identity `‖iteratedFDeriv j (∂ᵢw)‖ ≤ ‖iteratedFDeriv (j+1) w‖`
  (`ContinuousLinearMap.norm_iteratedFDeriv_comp_left` with `‖·‖ ≤ 1` on the
  coordinate-evaluation map, and `norm_iteratedFDeriv_fderiv`), reindexed over
  `j ≤ 2`.  This is the same calculus as `A05.SmoothL2.clm`
  (`Section4/A05/SmoothJets.lean`), made quantitative.

* **(iii) physical `spatialDerivative` = derivative of the slice.**
  `spatialDerivative u.velocity t x = fderiv ℝ (fun y => u.velocity (t,y)) x` by
  `rfl`, and `A05.opNorm_le_sum` (`A05/SmoothJets.lean`) bounds the operator norm
  by the sum of the three coordinate images `∂ᵢ(slice) x`, each an ordinary
  vector field to which (i)+(ii) apply through the derivative-closure
  `D01.smoothSquareIntegrableJets_dirDeriv` (`DatumToJets.lean:479`).

* **(iv) uniformity in `t ∈ Icc 0 b`.**  The `ContinuousOn G (Ico 0 T)` clause of
  `ClassicalSolutionR.sobolev` at orders `2` and `3` gives, on the compact
  `Icc 0 b ⊆ Ico 0 T`, one bound for `‖G t‖`; that turns the family of per-slice
  bounds into a single constant.  Same device as
  `A02.uniformFiniteEnergy_of_sobolevDatumPath` (`Energy.lean`), which used
  order `0`.
-/

noncomputable section

namespace NSFormalization.Section4.A02

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Paper3 (RealVectorSobolev)
open NSFormalization.Section4
open scoped ContDiff ENNReal

/-! ## 1. The jet-side order shift `jetENorm 2 (∂ᵢw) ≤ jetENorm 3 w` (sub-step ii) -/

/-- The order-`j` jet of the coordinate derivative `∂ᵢw` is pointwise no larger
than the order-`(j+1)` jet of `w`: coordinate evaluation is a norm-`≤ 1` linear
map, and `norm_iteratedFDeriv_fderiv` shifts `fderiv` into an order.  This is the
pointwise engine of the order shift and mirrors `A05.SmoothL2.clm`. -/
theorem norm_iteratedFDeriv_dirDeriv_le
    (i : Fin 3) {w : Space → Space} (hw : ContDiff ℝ ∞ w) (j : ℕ) (x : Space) :
    ‖iteratedFDeriv ℝ j (A05.dirDeriv i w) x‖ ≤ ‖iteratedFDeriv ℝ (j + 1) w x‖ := by
  have hcd : ContDiff ℝ ∞ (fderiv ℝ w) := hw.fderiv_right (m := ∞) (by simp)
  have hL : ‖ContinuousLinearMap.apply ℝ Space (coordinateVector i)‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun f => ?_)
    rw [ContinuousLinearMap.apply_apply, one_mul]
    exact (f.le_opNorm (coordinateVector i)).trans (by simp [coordinateVector])
  have hb := (ContinuousLinearMap.apply ℝ Space (coordinateVector i)).norm_iteratedFDeriv_comp_left
    (hcd.contDiffAt (x := x)) (n := j) (by exact_mod_cast le_top)
  rw [A05.dirDeriv_eq_clm]
  refine hb.trans ?_
  rw [norm_iteratedFDeriv_fderiv]
  exact mul_le_of_le_one_left (norm_nonneg _) hL

/-- The `L²` norm of the order-`j` jet of `∂ᵢw` is ≤ that of the order-`(j+1)`
jet of `w`. -/
theorem eLpNorm_iteratedFDeriv_dirDeriv_le
    (i : Fin 3) {w : Space → Space} (hw : ContDiff ℝ ∞ w) (j : ℕ) :
    eLpNorm (iteratedFDeriv ℝ j (A05.dirDeriv i w)) 2 volume
      ≤ eLpNorm (iteratedFDeriv ℝ (j + 1) w) 2 volume := by
  refine eLpNorm_mono_enorm (fun x => ?_)
  rw [← ofReal_norm, ← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (norm_iteratedFDeriv_dirDeriv_le i hw j x)

/-- **The jet-side order shift (sub-step ii).**  `jetENorm 2 (∂ᵢw) ≤ jetENorm 3 w`:
each of the three summands of the left side is dominated by the corresponding
order-shifted summand of the right, and the missing order-`0` summand on the
right is nonnegative. -/
theorem jetENorm_dirDeriv_le (i : Fin 3) {w : Space → Space} (hw : ContDiff ℝ ∞ w) :
    A03.jetENorm 2 (A05.dirDeriv i w) ≤ A03.jetENorm 3 w := by
  have key : (∑ j ∈ Finset.range 3, eLpNorm (iteratedFDeriv ℝ j (A05.dirDeriv i w)) 2 volume)
      ≤ ∑ j ∈ Finset.range 4, eLpNorm (iteratedFDeriv ℝ j w) 2 volume := by
    calc (∑ j ∈ Finset.range 3, eLpNorm (iteratedFDeriv ℝ j (A05.dirDeriv i w)) 2 volume)
        ≤ ∑ j ∈ Finset.range 3, eLpNorm (iteratedFDeriv ℝ (j + 1) w) 2 volume :=
          Finset.sum_le_sum (fun j _ => eLpNorm_iteratedFDeriv_dirDeriv_le i hw j)
      _ ≤ (∑ j ∈ Finset.range 3, eLpNorm (iteratedFDeriv ℝ (j + 1) w) 2 volume)
            + eLpNorm (iteratedFDeriv ℝ 0 w) 2 volume := le_self_add
      _ = ∑ j ∈ Finset.range 4, eLpNorm (iteratedFDeriv ℝ j w) 2 volume :=
          (Finset.sum_range_succ' (fun j => eLpNorm (iteratedFDeriv ℝ j w) 2 volume) 3).symm
  exact key

/-! ## 2. Per-slice pointwise bounds -/

/-- **Velocity, per slice (sub-steps i, iv-datum).**  A smooth field with all jets
`L²` and an order-`2` angular datum `A` is bounded everywhere by
`C · jetSobolevConst 2 · ‖A‖`. -/
theorem norm_le_of_datum {w : Space → Space} (hw : D01.SmoothSquareIntegrableJets w)
    {A : RealVectorSobolev ((2 : ℕ) : ℝ)} (hA : IsSobolevDatum ((2 : ℕ) : ℝ) w A) (x : Space) :
    ‖w x‖ ≤ A03.boundedRepresentativeConst * D01.jetSobolevConst 2 * ‖A‖ := by
  have hup : A03.SmoothL2UpTo 2 w := D01.smoothJetsUpTo_of_allOrders 2 hw
  have h1 : ‖w x‖ₑ ≤ ENNReal.ofReal A03.boundedRepresentativeConst * A03.jetENorm 2 w :=
    A03.enorm_le_jetENorm hup x
  have h2 : A03.jetENorm 2 w
      ≤ ENNReal.ofReal (D01.jetSobolevConst 2) * D01.sobolevENorm ((2 : ℕ) : ℝ) w :=
    D01.jetSobolevENorm_le_sobolevENorm 2 hw.1
  have h3 : D01.sobolevENorm ((2 : ℕ) : ℝ) w ≤ ‖A‖ₑ := D01.sobolevENorm_le_of_isSobolevDatum hA
  have hchain : ‖w x‖ₑ
      ≤ ENNReal.ofReal (A03.boundedRepresentativeConst * D01.jetSobolevConst 2 * ‖A‖) := by
    calc ‖w x‖ₑ ≤ ENNReal.ofReal A03.boundedRepresentativeConst * A03.jetENorm 2 w := h1
      _ ≤ ENNReal.ofReal A03.boundedRepresentativeConst *
            (ENNReal.ofReal (D01.jetSobolevConst 2) * D01.sobolevENorm ((2 : ℕ) : ℝ) w) :=
          by gcongr
      _ ≤ ENNReal.ofReal A03.boundedRepresentativeConst *
            (ENNReal.ofReal (D01.jetSobolevConst 2) * ‖A‖ₑ) :=
          by gcongr
      _ = ENNReal.ofReal (A03.boundedRepresentativeConst * D01.jetSobolevConst 2 * ‖A‖) := by
          rw [← ofReal_norm A, ← ENNReal.ofReal_mul (D01.jetSobolevConst_pos 2).le,
            ← ENNReal.ofReal_mul A03.boundedRepresentativeConst_pos.le]
          congr 1
          ring
  rw [← ofReal_norm (w x)] at hchain
  exact (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg (mul_nonneg A03.boundedRepresentativeConst_pos.le
      (D01.jetSobolevConst_pos 2).le) (norm_nonneg _))).mp hchain

/-- **Gradient, per slice (sub-steps i, ii, iii, iv-datum).**  The operator norm
of `fderiv ℝ w x` is bounded by `3 · (C · jetSobolevConst 3 · ‖A‖)` for an
order-`3` angular datum `A` of `w`: split into the three coordinate derivatives
(`opNorm_le_sum`), each of which is again a smooth all-jet-`L²` field
(`smoothSquareIntegrableJets_dirDeriv`) whose `L^∞` bound uses the order shift. -/
theorem norm_fderiv_le_of_datum {w : Space → Space} (hw : D01.SmoothSquareIntegrableJets w)
    {A : RealVectorSobolev ((3 : ℕ) : ℝ)} (hA : IsSobolevDatum ((3 : ℕ) : ℝ) w A) (x : Space) :
    ‖fderiv ℝ w x‖ ≤ 3 * (A03.boundedRepresentativeConst * D01.jetSobolevConst 3 * ‖A‖) := by
  have hterm : ∀ i : Fin 3, ‖fderiv ℝ w x (coordinateVector i)‖
      ≤ A03.boundedRepresentativeConst * D01.jetSobolevConst 3 * ‖A‖ := by
    intro i
    have hdi : D01.SmoothSquareIntegrableJets (A05.dirDeriv i w) :=
      D01.smoothSquareIntegrableJets_dirDeriv hw i
    have hup : A03.SmoothL2UpTo 2 (A05.dirDeriv i w) := D01.smoothJetsUpTo_of_allOrders 2 hdi
    have h1 : ‖A05.dirDeriv i w x‖ₑ
        ≤ ENNReal.ofReal A03.boundedRepresentativeConst * A03.jetENorm 2 (A05.dirDeriv i w) :=
      A03.enorm_le_jetENorm hup x
    have hshift : A03.jetENorm 2 (A05.dirDeriv i w) ≤ A03.jetENorm 3 w :=
      jetENorm_dirDeriv_le i hw.1
    have h2 : A03.jetENorm 3 w
        ≤ ENNReal.ofReal (D01.jetSobolevConst 3) * D01.sobolevENorm ((3 : ℕ) : ℝ) w :=
      D01.jetSobolevENorm_le_sobolevENorm 3 hw.1
    have h3 : D01.sobolevENorm ((3 : ℕ) : ℝ) w ≤ ‖A‖ₑ := D01.sobolevENorm_le_of_isSobolevDatum hA
    have hchain : ‖A05.dirDeriv i w x‖ₑ
        ≤ ENNReal.ofReal (A03.boundedRepresentativeConst * D01.jetSobolevConst 3 * ‖A‖) := by
      calc ‖A05.dirDeriv i w x‖ₑ
          ≤ ENNReal.ofReal A03.boundedRepresentativeConst * A03.jetENorm 2 (A05.dirDeriv i w) := h1
        _ ≤ ENNReal.ofReal A03.boundedRepresentativeConst * A03.jetENorm 3 w :=
            by gcongr
        _ ≤ ENNReal.ofReal A03.boundedRepresentativeConst *
              (ENNReal.ofReal (D01.jetSobolevConst 3) * D01.sobolevENorm ((3 : ℕ) : ℝ) w) :=
            by gcongr
        _ ≤ ENNReal.ofReal A03.boundedRepresentativeConst *
              (ENNReal.ofReal (D01.jetSobolevConst 3) * ‖A‖ₑ) :=
            by gcongr
        _ = ENNReal.ofReal (A03.boundedRepresentativeConst * D01.jetSobolevConst 3 * ‖A‖) := by
            rw [← ofReal_norm A, ← ENNReal.ofReal_mul (D01.jetSobolevConst_pos 3).le,
              ← ENNReal.ofReal_mul A03.boundedRepresentativeConst_pos.le]
            congr 1
            ring
    have hreal : ‖A05.dirDeriv i w x‖
        ≤ A03.boundedRepresentativeConst * D01.jetSobolevConst 3 * ‖A‖ := by
      rw [← ofReal_norm (A05.dirDeriv i w x)] at hchain
      exact (ENNReal.ofReal_le_ofReal_iff
        (mul_nonneg (mul_nonneg A03.boundedRepresentativeConst_pos.le
          (D01.jetSobolevConst_pos 3).le) (norm_nonneg _))).mp hchain
    exact hreal
  calc ‖fderiv ℝ w x‖ ≤ ∑ i : Fin 3, ‖fderiv ℝ w x (coordinateVector i)‖ := A05.opNorm_le_sum _
    _ ≤ ∑ _i : Fin 3, A03.boundedRepresentativeConst * D01.jetSobolevConst 3 * ‖A‖ :=
        Finset.sum_le_sum (fun i _ => hterm i)
    _ = 3 * (A03.boundedRepresentativeConst * D01.jetSobolevConst 3 * ‖A‖) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        norm_num

/-! ## 3. The two U1b theorems on the solution class -/

/-- **A02 unit U1b, velocity bound.**  The velocity of a classical whole-space
solution on `[0,T)` is uniformly bounded on `R³` over every compact time
interval `Icc 0 b` with `0 ≤ b < T`.  This is the `hB0`/`hB` pair of
`Source.BoundedViscosityUniqueness.classical_uniqueness_on_Icc`
(`Source/BoundedViscosityUniqueness.lean:31`). -/
theorem ClassicalSolutionR.exists_velocity_bound {ν T : ℝ} {a : SpatialField}
    {f : SpaceTimeField} (u : ClassicalSolutionR ν a f T) {b : ℝ} (hb0 : 0 ≤ b) (hbT : b < T) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Icc (0 : ℝ) b, ∀ x, ‖u.velocity (t, x)‖ ≤ B := by
  obtain ⟨G, hGc, hGd⟩ := u.sobolev 2
  have hsub : Icc (0 : ℝ) b ⊆ Ico (0 : ℝ) T := fun t ht => ⟨ht.1, lt_of_le_of_lt ht.2 hbT⟩
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := b)).exists_bound_of_continuousOn
    (hGc.mono hsub)
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 0 ⟨le_rfl, hb0⟩)
  have hcpos : 0 ≤ A03.boundedRepresentativeConst * D01.jetSobolevConst 2 :=
    mul_nonneg A03.boundedRepresentativeConst_pos.le (D01.jetSobolevConst_pos 2).le
  refine ⟨A03.boundedRepresentativeConst * D01.jetSobolevConst 2 * C, mul_nonneg hcpos hC0, ?_⟩
  intro t ht x
  have hslice : D01.SmoothSquareIntegrableJets (fun y : Space => u.velocity (t, y)) :=
    D01.smoothSquareIntegrableJets_slice u.velocity_smooth
      (fun m => (u.sobolev m).imp fun _ h => h.2) (hsub ht)
  have hdat : IsSobolevDatum ((2 : ℕ) : ℝ) (fun y : Space => u.velocity (t, y)) (G t) :=
    hGd t (hsub ht)
  refine (norm_le_of_datum hslice hdat x).trans ?_
  exact mul_le_mul_of_nonneg_left (hC t ht) hcpos

/-- **A02 unit U1b, gradient bound.**  The spatial derivative of the velocity of a
classical whole-space solution on `[0,T)` is uniformly bounded in operator norm
on `R³` over every compact `Icc 0 b` with `0 ≤ b < T`.  This is the `hG0`/`hG`
pair of `Source.BoundedViscosityUniqueness.classical_uniqueness_on_Icc`
(`Source/BoundedViscosityUniqueness.lean:32`); `spatialDerivative` is
`NavierStokes.ProblemStatement.spatialDerivative`. -/
theorem ClassicalSolutionR.exists_gradient_bound {ν T : ℝ} {a : SpatialField}
    {f : SpaceTimeField} (u : ClassicalSolutionR ν a f T) {b : ℝ} (hb0 : 0 ≤ b) (hbT : b < T) :
    ∃ Gb : ℝ, 0 ≤ Gb ∧ ∀ t ∈ Icc (0 : ℝ) b, ∀ x, ‖spatialDerivative u.velocity t x‖ ≤ Gb := by
  obtain ⟨G, hGc, hGd⟩ := u.sobolev 3
  have hsub : Icc (0 : ℝ) b ⊆ Ico (0 : ℝ) T := fun t ht => ⟨ht.1, lt_of_le_of_lt ht.2 hbT⟩
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := b)).exists_bound_of_continuousOn
    (hGc.mono hsub)
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 0 ⟨le_rfl, hb0⟩)
  have hcpos : 0 ≤ A03.boundedRepresentativeConst * D01.jetSobolevConst 3 :=
    mul_nonneg A03.boundedRepresentativeConst_pos.le (D01.jetSobolevConst_pos 3).le
  refine ⟨3 * (A03.boundedRepresentativeConst * D01.jetSobolevConst 3 * C),
    mul_nonneg (by norm_num) (mul_nonneg hcpos hC0), ?_⟩
  intro t ht x
  have hslice : D01.SmoothSquareIntegrableJets (fun y : Space => u.velocity (t, y)) :=
    D01.smoothSquareIntegrableJets_slice u.velocity_smooth
      (fun m => (u.sobolev m).imp fun _ h => h.2) (hsub ht)
  have hdat : IsSobolevDatum ((3 : ℕ) : ℝ) (fun y : Space => u.velocity (t, y)) (G t) :=
    hGd t (hsub ht)
  refine (norm_fderiv_le_of_datum hslice hdat x).trans ?_
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hC t ht) hcpos) (by norm_num)

end NSFormalization.Section4.A02
