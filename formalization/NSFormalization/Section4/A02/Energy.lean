import NSFormalization.Section4.A02.SolutionClass
import NSFormalization.Section4.D01.DatumToJets
import NavierStokes.R3.ComparisonFiniteEnergy
import NavierStokes.R3.LpNormTools

/-!
# A02 unit U1a — uniform finite energy from the order-zero Sobolev datum path

`research/A02/COMPARISON.md` §3 splits A02's implication **I1** into the energy
half (**U1a**, this module) and the sup-bound half (**U1b**).  The energy half is
the first of the three hypotheses of
`NSFormalization.Source.BoundedViscosityUniqueness.classical_uniqueness_on_Icc`
(`formalization/NSFormalization/Source/BoundedViscosityUniqueness.lean:23`) that
`Contracts.V1.Data.ClassicalSolutionR` (`verification/Contracts/V1/Data.lean:624`)
does not carry as a field:

```
UniformFiniteEnergy (Icc 0 b) u.velocity   for every 0 ≤ b < T.
```

## What the proof uses

Exactly two fields of `ClassicalSolutionR`, in the form in which `Data.lean`
states them:

* `velocity_smooth : ContDiffOn ℝ ∞ velocity (Ico 0 T ×ˢ univ)` — gives, at each
  `t ∈ Ico 0 T`, a *smooth* spatial slice through `D01.contDiff_slice`
  (`Section4/D01/DatumToJets.lean:366`).  Smoothness is what excludes the
  totalized-integral degeneracy of `IsSobolevDatum` (`Data.lean:147-154`).
* `sobolev` at `m = 0`: a datum path `G : ℝ → RealVectorSobolev 0` with
  **`ContinuousOn G (Ico 0 T)`** and `IsSobolevDatum 0 (velocity (t,·)) (G t)`
  for every `t ∈ Ico 0 T`.  The `ContinuousOn` clause is the one that carries the
  argument: on the compact `Icc 0 b ⊆ Ico 0 T` it gives a single bound for
  `‖G t‖`, and that bound is what turns a family of finite energies into *one*
  finite bound.  Continuity at the single order `m = 0` suffices; no higher order
  and no embedding is needed, which is why U1a is an **M** and U1b an **L**.

No other field is touched: the equation, the divergence constraint, the pressure
and the initial condition play no role.

## Route — reused from D01

The order-0 datum ⟹ `L²`-slice step is `Section4/D01/DatumToJets.lean`'s at
general integer order; lane 040 removed the byte-identical order-0 re-derivation
that lane 033 had here and calls D01 directly:

* `D01.contDiff_slice` (`:366`): the slice of a field smooth on the closed-at-zero
  slab is smooth on all of `R³`;
* `D01.memLp_of_isSobolevDatum` (`:267`): a smooth field with an order-`m` angular
  datum is in `L²`;
* `D01.eLpNorm_le_of_isSobolevDatum` (`:276`): its `L²` norm is bounded by the
  datum norm, with the fixed constant `D01.jetDatumConst 0 m`.

`D01`'s lemmas take `ContDiff ℝ ∞` of the slice where an order-0 argument needs
only `Continuous`; that is a genuinely stronger hypothesis, but
`velocity_smooth` supplies it through `D01.contDiff_slice`, so no A02-local
order-0 copy is kept.  `D01`'s predicate is `D01.IsSobolevDatum`, definitionally
equal to the `A02.IsSobolevDatum` of `SolutionClass.lean` (verified `rfl`, see
`research/A02/ATTEMPTS_SIMP.md`), so `exact` moves a datum across.

`NavierStokesR3.LpNormTools.lpNorm_two_sq_eq_l2Sq` turns the resulting `L²` norm
into `∫ ‖u (t,x)‖ ^ 2`, and `NavierStokesR3.Comparison.squareIntegrableAtTime_iff_memLp`
into `SquareIntegrableAtTime`.  The constant is not claimed to be sharp, since
`UniformFiniteEnergy` existentially quantifies the bound.
-/

noncomputable section

namespace NSFormalization.Section4.A02

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NavierStokesR3.ProblemStatement (SquareIntegrableAtTime kineticEnergy UniformFiniteEnergy)
open NSFormalization.Paper3
open NSFormalization.Section4.D01
  (contDiff_slice memLp_of_isSobolevDatum eLpNorm_le_of_isSobolevDatum jetDatumConst
    jetDatumConst_pos)
open scoped ContDiff ENNReal

/-! ## 1. Unit U1a -/

/-- **A02 unit U1a, datum-path form.**  A field smooth on the half-open slab whose
order-zero angular Sobolev datum path is continuous on `Ico 0 T` has uniformly
finite energy on every compact `Icc 0 b` with `b < T`.

The order parameter is carried as `s` with `hs : s = 0` so that the `m = 0`
instance of `ClassicalSolutionR.sobolev`, whose order is the cast `((0 : ℕ) : ℝ)`,
applies without a transport. -/
theorem uniformFiniteEnergy_of_sobolevDatumPath {T b s : ℝ} {u : VelocityField}
    (hs : s = 0)
    (hu : ContDiffOn ℝ ∞ u (Ico (0 : ℝ) T ×ˢ (univ : Set Space)))
    {G : ℝ → RealVectorSobolev s}
    (hG : ContinuousOn G (Ico (0 : ℝ) T))
    (hdat : ∀ t ∈ Ico (0 : ℝ) T, IsSobolevDatum s (fun x => u (t, x)) (G t))
    (hb0 : 0 ≤ b) (hbT : b < T) :
    UniformFiniteEnergy (Icc (0 : ℝ) b) u := by
  -- rewrite the real order `s = 0` as the nat-cast order `↑(0 : ℕ)` that D01 wants
  have hs0 : s = ((0 : ℕ) : ℝ) := by rw [hs, Nat.cast_zero]
  subst hs0
  have hsub : Icc (0 : ℝ) b ⊆ Ico (0 : ℝ) T := fun t ht => ⟨ht.1, lt_of_le_of_lt ht.2 hbT⟩
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := b)).exists_bound_of_continuousOn
    (hG.mono hsub)
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 0 ⟨le_rfl, hb0⟩)
  have hK0 : (0 : ℝ) ≤ jetDatumConst 0 0 := (jetDatumConst_pos 0 0).le
  refine ⟨(1 / 2 : ℝ) * (jetDatumConst 0 0 * C) ^ 2,
    mul_nonneg (by norm_num) (pow_nonneg (mul_nonneg hK0 hC0) 2), ?_⟩
  intro t ht
  have hcd : ContDiff ℝ ∞ fun x : Space => u (t, x) := contDiff_slice hu (hsub ht)
  have hdt := hdat t (hsub ht)
  have hmem := memLp_of_isSobolevDatum (m := 0) hcd hdt
  refine ⟨(NavierStokesR3.Comparison.squareIntegrableAtTime_iff_memLp
    hcd.continuous.aestronglyMeasurable).2 hmem, ?_⟩
  -- the L² norm of the slice is bounded by the datum norm (D01), uniformly in `t`
  have hcomp : NavierStokesR3.Comparison.comparisonLpNorm 2 (fun x : Space => u (t, x))
      ≤ jetDatumConst 0 0 * ‖G t‖ := by
    have hbd : eLpNorm (fun x : Space => u (t, x)) 2 volume
        ≤ ENNReal.ofReal (jetDatumConst 0 0 * ‖G t‖) := by
      rw [ENNReal.ofReal_mul hK0, ofReal_norm (G t)]
      exact eLpNorm_le_of_isSobolevDatum (m := 0) hcd hdt
    calc NavierStokesR3.Comparison.comparisonLpNorm 2 (fun x : Space => u (t, x))
          = (eLpNorm (fun x : Space => u (t, x)) 2 volume).toReal := rfl
      _ ≤ (ENNReal.ofReal (jetDatumConst 0 0 * ‖G t‖)).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hbd
      _ = jetDatumConst 0 0 * ‖G t‖ := ENNReal.toReal_ofReal (mul_nonneg hK0 (norm_nonneg _))
  have hl2 : NavierStokesR3.Comparison.l2Sq (fun x : Space => u (t, x))
      ≤ (jetDatumConst 0 0 * C) ^ 2 := by
    rw [← NavierStokesR3.LpNormTools.lpNorm_two_sq_eq_l2Sq hmem]
    refine (pow_le_pow_left₀ (NavierStokesR3.LpNormTools.lpNorm_nonneg 2 _) hcomp 2).trans ?_
    exact pow_le_pow_left₀ (mul_nonneg hK0 (norm_nonneg _))
      (mul_le_mul_of_nonneg_left (hC t ht) hK0) 2
  dsimp only [kineticEnergy, NavierStokesR3.Comparison.l2Sq] at hl2 ⊢
  linarith

/-- **A02 unit U1a.**  The two hypotheses are verbatim `ClassicalSolutionR`'s
`velocity_smooth` (`verification/Contracts/V1/Data.lean:632`) and `sobolev`
(`:643-645`); the conclusion is the `UniformFiniteEnergy` hypothesis of
`Source.BoundedViscosityUniqueness.classical_uniqueness_on_Icc`
(`Source/BoundedViscosityUniqueness.lean:29`) on every closed subinterval of the
lifespan. -/
theorem uniformFiniteEnergy_of_sobolev {T b : ℝ} {u : VelocityField}
    (hu : ContDiffOn ℝ ∞ u (Ico (0 : ℝ) T ×ˢ (univ : Set Space)))
    (hsob : ∀ m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
      ContinuousOn G (Ico (0 : ℝ) T) ∧
        ∀ t ∈ Ico (0 : ℝ) T, IsSobolevDatum (m : ℝ) (fun x => u (t, x)) (G t))
    (hb0 : 0 ≤ b) (hbT : b < T) :
    UniformFiniteEnergy (Icc (0 : ℝ) b) u := by
  obtain ⟨G, hGc, hGd⟩ := hsob 0
  exact uniformFiniteEnergy_of_sobolevDatumPath (s := ((0 : ℕ) : ℝ)) Nat.cast_zero hu hGc hGd
    hb0 hbT

/-- **A02 unit U1a, on the solution class.**  A classical whole-space solution on
`[0,T)` has uniformly finite energy on every `Icc 0 b` with `0 ≤ b < T`.  This is
the first of the three hypotheses of
`Source.BoundedViscosityUniqueness.classical_uniqueness_on_Icc`
(`Source/BoundedViscosityUniqueness.lean:29`) that `ClassicalSolutionR` does not
carry as a field; the other two are unit **U1b**. -/
theorem ClassicalSolutionR.uniformFiniteEnergy {ν T : ℝ} {a : SpatialField}
    {f : SpaceTimeField} (u : ClassicalSolutionR ν a f T) {b : ℝ}
    (hb0 : 0 ≤ b) (hbT : b < T) :
    UniformFiniteEnergy (Icc (0 : ℝ) b) u.velocity :=
  uniformFiniteEnergy_of_sobolev u.velocity_smooth u.sobolev hb0 hbT

end NSFormalization.Section4.A02
