import NSFormalization.Section4.A01.L2Descent
import NSFormalization.Section4.A02.SolutionClass
import Euler.ClassicalDivergence
import Euler.MeanCylinderSolenoidal

/-!
# A01 constructor row c6: divergence-free velocity slices

This module isolates the divergence field of the mild-to-classical constructor in the two layers
required by `research/A01/A01_SPLIT.md` row c6.

* `divergence_ae_of_cylinder` starts from one time slice of the cylinder pair.  It explicitly
  descends the three first spatial words with `word_descent_ae_top`, identifies them a.e. with the
  three classical coordinate derivatives using `word_descent_ae_full`, and sums their diagonal
  components.  The source constraint enters through
  `EulerClassicalDivergence.divergenceFree_classical_divergence_zero`.
* `divergence_of_cylinder_pointwise_of_contDiff` is the c3 handoff.  A candidate velocity slice
  which is `ContDiff ℝ ∞` and agrees a.e. with the same ordinary `L²` carrier equals the smooth
  representative everywhere.  Continuity upgrades the a.e.-zero derivative sum to the pointwise
  `ClassicalSolutionR.divergence` field shape.

## The source notion of divergence-free

`EulerLiftedGradientSpace.divergenceFreeSpace` is the orthogonal complement of the closed lifted
gradient space (`Euler/EulerProof.lean:1340`), not definitionally a coordinate-word sum.  Its weak
test identity is `weak_divergence_test_integral`; the vendor packages the analytic weak-to-classical
conversion as `EulerClassicalDivergence.divergenceFree_classical_divergence_zero`.  Thus no Fourier
normalization or `2π` factor occurs on this cylinder route.  The HeliCorgi theorem
`MNS2.r3DecodedFrequency_incompressible_ae_decoder` is the analogous decoder theorem for its
separate `R3L2SolenoidalSubmodule`; it is not the carrier produced by `Horizon.lean`.

No placeholder declaration or pointwise divergence assumption is used.  The c3 spatial smoothness
remains an explicit named hypothesis of the pointwise theorem.
-/

noncomputable section

namespace NSFormalization.Section4.A01

open Set MeasureTheory
open NSFormalization.Section4.A02 (SpaceTimeField)
open NavierStokes.ProblemStatement (Space coordinateVector spatialDivergence spatialDerivative)
open EulerMeanOrdinaryLift EulerCylinderSobolevSpace EulerLiftedGradientSpace
  EulerCylinderSobolev EulerPressureSpatialRegularity EulerLpTranslation EulerMetricTransport
open scoped ContDiff

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-! ## 1. Cylinder divergence at one time, on the a.e. carrier -/

/-- **A01 constructor row c6, a.e. layer.**

Let `u` be one cylinder Sobolev slice, `U` its ordinary `L²` descent, and `Z` a smooth
all-order-`L²` representative of `U`.  If the cylinder value is in the vendor's genuine
divergence-free subspace, then the classical coordinate divergence of `Z.field` vanishes almost
everywhere:

`(∀ᵐ x) ∑ i, (fderiv ℝ Z.field x (coordinateVector i)) i = 0`.

The proof descends the three words `∂ᵢu` to `Zi i`, identifies `Zi i` a.e. with
`fderiv ℝ Z.field · eᵢ`, and sums the diagonal components.  The weak lifted constraint is
converted to classical divergence zero by the vendor's
`divergenceFree_classical_divergence_zero`; the conclusion is deliberately retained in a.e. form
because identifying a merely a.e.-specified candidate velocity with `Z.field` is the separate c3
handoff below. -/
theorem divergence_ae_of_cylinder {q : ℕ}
    (u : SobolevSpace 1 (q + 1))
    (U : EulerMeanSolenoidal.L2)
    (hu : ∀ θ : AddCircle (1 : ℝ), sobolevTranslation 1 (q + 1) (0, θ) u = u)
    (hU : ordinaryLift U = value 1 u)
    (hdiv : value 1 u ∈ divergenceFreeSpace 1 1 0)
    (Z : SmoothL2Field Space)
    (hZ : Z.field =ᵐ[volume] ⇑U) :
    ∀ᵐ x ∂(volume : Measure Space),
      ∑ i : Fin 3, (fderiv ℝ Z.field x (coordinateVector i)) i = 0 := by
  -- There is one cylinder word for each of the three spatial coordinate derivatives.
  let n : ℕ := 1
  have hn : n ≤ q + 1 := by omega
  choose Zi hZi using fun i : Fin 3 =>
    word_descent_ae_top u hu n hn (fun _ : Fin 1 => i)
  have hZi_ae : ∀ i : Fin 3, (⇑(Zi i)) =ᵐ[volume]
      (wordField Z (fun _ : Fin 1 => i)).field := by
    intro i
    exact word_descent_ae_full u hu U hU Z hZ.symm n hn
      (fun _ : Fin 1 => i) (Zi i) (hZi i)

  -- Lift `Z` to the cylinder.  It is a smooth representative of `value 1 u`.
  have hrep0 := ordinaryLift_ae U
  rw [hU] at hrep0
  have hZlift : (fun p : LiftDomain 1 => U p.1) =ᵐ[liftMeasure 1]
      fun p : LiftDomain 1 => Z.field p.1 :=
    ordinaryProjection_measurePreserving.quasiMeasurePreserving.ae hZ.symm
  have hrep : ((value 1 u : LiftDomain 1 → Space)) =ᵐ[liftMeasure 1]
      fun p : LiftDomain 1 => Z.field p.1 := hrep0.trans hZlift
  have hlocal : ∀ p : LiftDomain 1,
      ContDiff ℝ ∞ (localFieldLift 1 (fun z : LiftDomain 1 => Z.field z.1) p) := by
    intro p
    exact Z.smooth.comp (contDiff_const.add contDiff_fst)
  have hlifted_zero :=
    EulerClassicalDivergence.divergenceFree_classical_divergence_zero
      1 1 (0 : Space) (value 1 u) hdiv (fun p : LiftDomain 1 => Z.field p.1) hrep hlocal
  have hclassical : ∀ x : Space,
      ∑ i : Fin 3, (fderiv ℝ Z.field x (coordinateVector i)) i = 0 := by
    intro x
    have hx := hlifted_zero (x, 0)
    simpa [EulerMeanCylinderSolenoidal.fieldDerivative_spatial 1 Z.field Z.smooth,
      coordinateDirection, coordinateVector] using hx

  -- Match each descended word to its classical derivative, then sum the three diagonal entries.
  have hcomponents : ∀ i : Fin 3, ∀ᵐ x ∂(volume : Measure Space),
      Zi i x i = (fderiv ℝ Z.field x (coordinateVector i)) i := by
    intro i
    filter_upwards [hZi_ae i] with x hx
    rw [hx, wordField_field]
    simp only [iteratedFDeriv_one_apply]
  have hwords_zero : ∀ᵐ x ∂(volume : Measure Space), ∑ i : Fin 3, Zi i x i = 0 := by
    filter_upwards [ae_all_iff.mpr hcomponents] with x hx
    calc
      ∑ i : Fin 3, Zi i x i
          = ∑ i : Fin 3, (fderiv ℝ Z.field x (coordinateVector i)) i := by
              apply Finset.sum_congr rfl
              intro i _
              exact hx i
      _ = 0 := hclassical x
  filter_upwards [ae_all_iff.mpr hcomponents, hwords_zero] with x hx hzero
  calc
    ∑ i : Fin 3, (fderiv ℝ Z.field x (coordinateVector i)) i
        = ∑ i : Fin 3, Zi i x i := by
            apply Finset.sum_congr rfl
            intro i _
            exact (hx i).symm
    _ = 0 := hzero

/-! ## 2. The c3 continuity handoff: a.e. to pointwise -/

/-- **A01 constructor row c6, pointwise c3 handoff.**

For a cylinder path `(u,U)` on `[0,T]`, suppose `Z t` is a smooth `L²` representative of every
ordinary slice and a candidate spacetime velocity has the same a.e. slices.  If each candidate
slice on `[0,T)` is `ContDiff ℝ ∞` (the spatial consequence of constructor row c3), then its
divergence vanishes in exactly the field shape required by `ClassicalSolutionR.divergence`:

`Every t in Ico 0 T, every x, spatialDivergence velocity t x = 0`.

Continuity is used twice: first to upgrade the a.e.-zero divergence of `Z t`, and then to identify
the candidate slice with `Z t` everywhere from their common a.e. `U t` representative. -/
theorem divergence_of_cylinder_pointwise_of_contDiff {q : ℕ} {T : ℝ}
    (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q + 1)))
    (U : C(Icc (0 : ℝ) T, EulerMeanSolenoidal.L2))
    (hu : ∀ (t : Icc (0 : ℝ) T) (θ : AddCircle (1 : ℝ)),
      sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t)
    (hU : ∀ t, ordinaryLift (U t) = value 1 (u t))
    (hdiv : ∀ t, value 1 (u t) ∈ divergenceFreeSpace 1 1 0)
    (Z : Icc (0 : ℝ) T → SmoothL2Field Space)
    (hZ : ∀ t, (Z t).field =ᵐ[volume] ⇑(U t))
    (velocity : SpaceTimeField)
    (hslice : ∀ t : Icc (0 : ℝ) T,
      (fun x : Space => velocity (↑t, x)) =ᵐ[volume] ⇑(U t))
    (hslice_contDiff : ∀ t ∈ Ico (0 : ℝ) T,
      ContDiff ℝ ∞ (fun x : Space => velocity (t, x))) :
    ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Space, spatialDivergence velocity t x = 0 := by
  intro t ht x
  let τ : Icc (0 : ℝ) T := ⟨t, ht.1, ht.2.le⟩
  have hdiv_ae := divergence_ae_of_cylinder
    (u τ) (U τ) (hu τ) (hU τ) (hdiv τ) (Z τ) (hZ τ)
  have hdiv_cont : Continuous (fun y : Space =>
      ∑ i : Fin 3, (fderiv ℝ (Z τ).field y (coordinateVector i)) i) := by
    apply continuous_finsetSum
    intro i _
    exact (EuclideanSpace.proj i).continuous.comp
      (((Z τ).smooth.continuous_fderiv (by simp)).clm_apply continuous_const)
  have hdiv_fun : (fun y : Space =>
      ∑ i : Fin 3, (fderiv ℝ (Z τ).field y (coordinateVector i)) i) = 0 := by
    apply (hdiv_cont.ae_eq_iff_eq volume
      (continuous_const : Continuous (0 : Space → ℝ))).mp
    exact hdiv_ae
  have hsliceZ_ae : (fun y : Space => velocity (t, y)) =ᵐ[volume] (Z τ).field :=
    (hslice τ).trans (hZ τ).symm
  have hsliceZ : (fun y : Space => velocity (t, y)) = (Z τ).field :=
    ((hslice_contDiff t ht).continuous.ae_eq_iff_eq volume (Z τ).smooth.continuous).mp
      hsliceZ_ae
  simp only [spatialDivergence, spatialDerivative, hsliceZ]
  exact congrFun hdiv_fun x

end NSFormalization.Section4.A01
