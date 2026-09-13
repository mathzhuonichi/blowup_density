import NSFormalization.Section4.A02.SolutionClass
import NSFormalization.Source.FourierPhysicalJets
import NSFormalization.Paper3.AngularTameProduct
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

* `velocity_smooth : ContDiffOn ℝ ∞ velocity (Ico 0 T ×ˢ univ)` — used *only*
  for continuity of the spatial slice at each `t ∈ Ico 0 T`, which is what makes
  the slice locally integrable, hence identifiable with an `L²` class off a null
  set.  Without it the datum predicate is vacuous on a slice that pairs
  integrably with no Schwartz test (the totalization caveat of
  `Data.lean:147-154`).
* `sobolev` at `m = 0`: a datum path `G : ℝ → RealVectorSobolev 0` with
  **`ContinuousOn G (Ico 0 T)`** and `IsSobolevDatum 0 (velocity (t,·)) (G t)`
  for every `t ∈ Ico 0 T`.  The `ContinuousOn` clause is the one that carries the
  argument: on the compact `Icc 0 b ⊆ Ico 0 T` it gives a single bound for
  `‖G t‖`, and that bound is what turns a family of finite energies into *one*
  finite bound.  Continuity at the single order `m = 0` suffices; no higher
  order and no embedding is needed, which is why U1a is an **M** and U1b an
  **L**.

No other field is touched: the equation, the divergence constraint, the pressure
and the initial condition play no role, so the work is done by
`uniformFiniteEnergy_of_sobolev`, which takes those two fields as hypotheses.
`ClassicalSolutionR.uniformFiniteEnergy` is the target statement itself, against
the shared restatement of the D01 solution class in
`NSFormalization/Section4/A02/SolutionClass.lean` (byte-identical to §0 of lane
032's `Section4/A02/Restrict.lean`; the `NSFormalization` package is a dependency
of the `Contracts` library and cannot import `Contracts.V1.Data`).

## Route

`IsSobolevDatum` is stated in the manuscript's *angular* normalization through
`Paper3.angularRealization`.  At order `0`:

1. `Paper3.angularRealization_eq_cycles` moves the datum to the cycles
   convention, `Paper3.cyclesToAngular` being a `≃L` with `‖·‖`-bound
   `frequencyUnit ^ |s|`, which is `1` at `s = 0`;
2. `Source.FourierPhysicalJets.physicalLp` is the `L²` class of a cycles datum
   and `physicalLp_ae` identifies it — through Mathlib's
   `ae_eq_of_integral_contDiff_smul_eq` — with any *continuous* field having the
   same Schwartz pairing.  This is the "order-0 datum ⟹ `L²`-slice realization"
   step of the unit table;
3. `Source.FourierPhysicalJets.vectorLpReassembly` puts the three components back
   into `Lp Space 2 volume`;
4. `NavierStokesR3.LpNormTools.lpNorm_two_sq_eq_l2Sq` turns the resulting `L²`
   norm into `∫ ‖u (t,x)‖ ^ 2`, and
   `NavierStokesR3.Comparison.squareIntegrableAtTime_iff_memLp` into
   `SquareIntegrableAtTime`.

The constant is the product of two operator norms; nothing below needs it to be
sharp, since `UniformFiniteEnergy` existentially quantifies the bound.
-/

noncomputable section

namespace NSFormalization.Section4.A02

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NavierStokesR3.ProblemStatement (SquareIntegrableAtTime kineticEnergy UniformFiniteEnergy)
open NSFormalization.Paper3
open NSFormalization.Source NSFormalization.Source.RealSobolev
open NSFormalization.Source.FourierPhysicalJets
open scoped ContDiff ENNReal SchwartzMap

/-! ## 1. The physical `L²` slice of an order-zero angular datum -/

/-- One component of an order-zero angular real-vector datum, read in the cycles
convention of `Paper3.sobolevRealization`. -/
def cyclesComponent (A : RealVectorSobolev (0 : ℝ)) (i : Fin 3) : SobolevHilbert (0 : ℝ) :=
  (cyclesToAngular 0).symm ((A i : FourierData))

/-- At order zero the angular-to-cycles transport is norm nonincreasing, because
`frequencyUnit ^ |0| = 1`; the Euclidean `PiLp 2` carrier then dominates each
component. -/
theorem norm_cyclesComponent_le (A : RealVectorSobolev (0 : ℝ)) (i : Fin 3) :
    ‖cyclesComponent A i‖ ≤ ‖A‖ := by
  refine (cyclesToAngular_symm_norm_le 0 ((A i : FourierData))).trans ?_
  rw [abs_zero, Real.rpow_zero, one_mul]
  exact PiLp.norm_apply_le A i

/-- The physical `L²` class of one component of an order-zero datum. -/
def componentLp (A : RealVectorSobolev (0 : ℝ)) (i : Fin 3) :
    Lp ℂ 2 (volume : Measure Space) :=
  physicalLp 0 le_rfl (cyclesComponent A i)

/-- The physical `L²` class of the whole three-vector slice of an order-zero
datum. -/
def sliceLp (A : RealVectorSobolev (0 : ℝ)) : Lp Space 2 (volume : Measure Space) :=
  vectorLpReassembly (componentLp A)

/-- The constant of `norm_sliceLp_le`: the two operator norms involved.  It is
not claimed to be sharp. -/
def sliceConst : ℝ :=
  ‖(vectorLpReassembly : (Fin 3 → Lp ℂ 2 (volume : Measure Space)) →L[ℝ]
      Lp Space 2 (volume : Measure Space))‖ * ‖physicalLp (0 : ℝ) le_rfl‖

theorem sliceConst_nonneg : 0 ≤ sliceConst :=
  mul_nonneg (norm_nonneg _) (norm_nonneg _)

theorem norm_sliceLp_le (A : RealVectorSobolev (0 : ℝ)) : ‖sliceLp A‖ ≤ sliceConst * ‖A‖ := by
  have hA : 0 ≤ ‖A‖ := norm_nonneg A
  have hcomp : ‖componentLp A‖ ≤ ‖physicalLp (0 : ℝ) le_rfl‖ * ‖A‖ := by
    refine (pi_norm_le_iff_of_nonneg (mul_nonneg (norm_nonneg _) hA)).2 ?_
    intro i
    exact ((physicalLp (0 : ℝ) le_rfl).le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (norm_cyclesComponent_le A i) (norm_nonneg _))
  calc ‖sliceLp A‖ ≤ ‖(vectorLpReassembly : (Fin 3 → Lp ℂ 2 (volume : Measure Space)) →L[ℝ]
        Lp Space 2 (volume : Measure Space))‖ * ‖componentLp A‖ :=
        vectorLpReassembly.le_opNorm _
    _ ≤ ‖(vectorLpReassembly : (Fin 3 → Lp ℂ 2 (volume : Measure Space)) →L[ℝ]
        Lp Space 2 (volume : Measure Space))‖ * (‖physicalLp (0 : ℝ) le_rfl‖ * ‖A‖) :=
        mul_le_mul_of_nonneg_left hcomp (norm_nonneg _)
    _ = sliceConst * ‖A‖ := by rw [sliceConst, mul_assoc]

/-! ## 2. The datum pairing identifies the physical slice -/

/-- An order-zero angular datum pairs with every compactly supported Schwartz test
exactly as the physical component does — the cycles-convention form of
`IsSobolevDatum`. -/
theorem compactRep_of_isSobolevDatum {z : Space → Space} {A : RealVectorSobolev (0 : ℝ)}
    (h : IsSobolevDatum 0 z A) (i : Fin 3) :
    CompactRep 0 (cyclesComponent A i) (fun x => ((z x i : ℝ) : ℂ)) := by
  intro ψ _
  have hz := h i ψ
  rw [angularRealization_eq_cycles] at hz
  simpa only [cyclesComponent, smul_eq_mul] using hz

/-- **The order-zero datum ⟹ `L²`-slice realization, componentwise.**  Continuity
of the physical field is what excludes the totalized-integral degeneracy of
`IsSobolevDatum`. -/
theorem componentLp_ae {z : Space → Space} {A : RealVectorSobolev (0 : ℝ)}
    (hz : Continuous z) (h : IsSobolevDatum 0 z A) (i : Fin 3) :
    (componentLp A i : Space → ℂ) =ᵐ[volume] fun x => ((z x i : ℝ) : ℂ) :=
  physicalLp_ae le_rfl ((complexComponent i).continuous.comp hz)
    (compactRep_of_isSobolevDatum h i)

/-- **The order-zero datum ⟹ `L²`-slice realization.**  A continuous field with an
order-zero angular datum agrees a.e. with an explicit element of
`Lp Space 2 volume`. -/
theorem sliceLp_ae {z : Space → Space} {A : RealVectorSobolev (0 : ℝ)}
    (hz : Continuous z) (h : IsSobolevDatum 0 z A) :
    (sliceLp A : Space → Space) =ᵐ[volume] z := by
  have h2 : ∀ᵐ x ∂(volume : Measure Space), ∀ i : Fin 3,
      (componentLp A i : Space → ℂ) x = ((z x i : ℝ) : ℂ) :=
    ae_all_iff.mpr (fun i => componentLp_ae hz h i)
  show (vectorLpReassembly (componentLp A) : Space → Space) =ᵐ[volume] z
  filter_upwards [vectorLpReassembly_ae (componentLp A), h2] with x hx hix
  rw [hx]
  ext i
  change ((componentLp A i : Space → ℂ) x).re = z x i
  rw [hix i, Complex.ofReal_re]

theorem memLp_of_isSobolevDatum {z : Space → Space} {A : RealVectorSobolev (0 : ℝ)}
    (hz : Continuous z) (h : IsSobolevDatum 0 z A) : MemLp z 2 (volume : Measure Space) :=
  (memLp_congr_ae (sliceLp_ae hz h)).mp (Lp.memLp _)

/-- The energy density integrates to at most the squared datum norm, up to the
fixed constant `sliceConst`. -/
theorem l2Sq_le_of_isSobolevDatum {z : Space → Space} {A : RealVectorSobolev (0 : ℝ)}
    (hz : Continuous z) (h : IsSobolevDatum 0 z A) :
    NavierStokesR3.Comparison.l2Sq z ≤ (sliceConst * ‖A‖) ^ 2 := by
  have hmem := memLp_of_isSobolevDatum hz h
  have hnorm : NavierStokesR3.Comparison.comparisonLpNorm 2 z = ‖sliceLp A‖ :=
    (congrArg ENNReal.toReal (eLpNorm_congr_ae (sliceLp_ae hz h))).symm
  rw [← NavierStokesR3.LpNormTools.lpNorm_two_sq_eq_l2Sq hmem, hnorm]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_sliceLp_le A) 2

/-! ## 3. Unit U1a -/

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
  subst hs
  have hsub : Icc (0 : ℝ) b ⊆ Ico (0 : ℝ) T := fun t ht => ⟨ht.1, lt_of_le_of_lt ht.2 hbT⟩
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := b)).exists_bound_of_continuousOn
    (hG.mono hsub)
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 0 ⟨le_rfl, hb0⟩)
  refine ⟨(1 / 2 : ℝ) * (sliceConst * C) ^ 2,
    mul_nonneg (by norm_num) (pow_nonneg (mul_nonneg sliceConst_nonneg hC0) 2), ?_⟩
  intro t ht
  have hslice : Continuous fun x : Space => u (t, x) :=
    NavierStokesR3.Comparison.continuous_slice_of_continuousOn hu.continuousOn (hsub ht)
  have hdt := hdat t (hsub ht)
  have hmem := memLp_of_isSobolevDatum hslice hdt
  refine ⟨(NavierStokesR3.Comparison.squareIntegrableAtTime_iff_memLp
    hslice.aestronglyMeasurable).2 hmem, ?_⟩
  have hle := l2Sq_le_of_isSobolevDatum hslice hdt
  have hmono : (sliceConst * ‖G t‖) ^ 2 ≤ (sliceConst * C) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg sliceConst_nonneg (norm_nonneg _))
      (mul_le_mul_of_nonneg_left (hC t ht) sliceConst_nonneg) 2
  have hfin := hle.trans hmono
  dsimp only [kineticEnergy, NavierStokesR3.Comparison.l2Sq] at hfin ⊢
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
