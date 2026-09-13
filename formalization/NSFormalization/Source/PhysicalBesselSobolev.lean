import NSFormalization.Source.PhysicalSobolevDistribution
import Euler.OrdinaryFieldAlgebra

/-! Explicit even-order Sobolev data from physical smooth L² jets. -/
noncomputable section
namespace NSFormalization.Source.PhysicalBesselSobolev
open MeasureTheory FourierTransform EulerLpTranslation NavierStokes.ProblemStatement
open SmoothL2Field EulerOrdinarySobolev NSFormalization.Paper3
open PhysicalSobolevDistribution
open scoped SchwartzMap LineDeriv ENNReal ContDiff
open Laplacian

private def basis : OrthonormalBasis (Fin 3) ℝ Space := EuclideanSpace.basisFun (Fin 3) ℝ

/-- Physical scalar Laplacian, using the existing finite-sum field algebra. -/
def laplacianField (A : SmoothL2Field ℂ) : SmoothL2Field ℂ :=
  sumField Finset.univ (fun i => (A.directionalField (basis i)).directionalField (basis i))

 theorem physicalDistribution_addField (A C : SmoothL2Field ℂ) :
    physicalDistribution (addField A C) = physicalDistribution A + physicalDistribution C := by
  change Lp.toTemperedDistributionCLM ℂ volume 2 _ = _
  rw [toLp_addField, map_add]
  rfl

 theorem physicalDistribution_sumField {ι : Type*} (I : Finset ι)
    (A : ι → SmoothL2Field ℂ) :
    physicalDistribution (sumField I A) = ∑ i ∈ I, physicalDistribution (A i) := by
  change Lp.toTemperedDistributionCLM ℂ volume 2 _ = _
  rw [toLp_sumField, map_sum]
  rfl

 theorem physicalDistribution_laplacianField (A : SmoothL2Field ℂ) :
    physicalDistribution (laplacianField A) = Δ (physicalDistribution A) := by
  rw [laplacianField, physicalDistribution_sumField, TemperedDistribution.laplacian_eq_sum basis]
  simp only [physicalDistribution_directionalField]

/-- Multiplication by a real constant through the existing real-linear field map. -/
def scaleField (c : ℝ) (A : SmoothL2Field ℂ) : SmoothL2Field ℂ :=
  mapField (c • ContinuousLinearMap.id ℝ ℂ) A

 theorem physicalDistribution_scaleField (c : ℝ) (A : SmoothL2Field ℂ) :
    physicalDistribution (scaleField c A) = c • physicalDistribution A := by
  ext φ
  rw [physicalDistribution_apply]
  change (∫ x, φ x • (c • A.field x)) = c • physicalDistribution A φ
  rw [physicalDistribution_apply, ← integral_smul]
  congr 1
  funext x
  exact smul_comm _ _ _

/-- The cycles-frequency Bessel operator of order two. -/
def besselField (A : SmoothL2Field ℂ) : SmoothL2Field ℂ :=
  addField A (scaleField (-((2 * Real.pi) ^ 2)⁻¹) (laplacianField A))

 theorem physicalDistribution_besselField_raw (A : SmoothL2Field ℂ) :
    physicalDistribution (besselField A) = physicalDistribution A +
      (-((2 * Real.pi) ^ 2)⁻¹) • Δ (physicalDistribution A) := by
  rw [besselField, physicalDistribution_addField, physicalDistribution_scaleField,
    physicalDistribution_laplacianField]

 theorem besselPotential_two_eq (u : 𝓢'(Space, ℂ)) :
    TemperedDistribution.besselPotential Space ℂ 2 u =
      u + (-((2 * Real.pi) ^ 2)⁻¹) • Δ u := by
  have hw : (fun x : Space => (((1 + ‖x‖ ^ 2) ^ ((2 : ℝ) / 2) : ℝ) : ℂ)) =
      (fun _ => (1 : ℂ)) + (fun x => ((‖x‖ ^ 2 : ℝ) : ℂ)) := by
    funext x
    simp
  rw [TemperedDistribution.besselPotential, hw,
    TemperedDistribution.fourierMultiplierCLM_apply,
    TemperedDistribution.smulLeftCLM_add (by fun_prop) (by fun_prop)]
  simp only [add_apply, TemperedDistribution.smulLeftCLM_const, one_smul]
  rw [TemperedDistribution.laplacian_eq_fourierMultiplierCLM]
  have hc : (-((2 * Real.pi) ^ 2)⁻¹) * (-((2 * Real.pi) ^ 2)) = 1 := by
    field_simp
  rw [smul_smul, hc, one_smul, fourierInv_add, fourierInv_fourier_eq]
  rfl

 theorem physicalDistribution_besselField (A : SmoothL2Field ℂ) :
    physicalDistribution (besselField A) =
      TemperedDistribution.besselPotential Space ℂ 2 (physicalDistribution A) := by
  rw [physicalDistribution_besselField_raw, besselPotential_two_eq]

 theorem continuous_jetLp_sumField {K ι : Type*} [TopologicalSpace K]
    (I : Finset ι) (A : ι → K → SmoothL2Field ℂ)
    (hA : ∀ i n, Continuous (fun t => (A i t).jetLp n)) (n : ℕ) :
    Continuous (fun t => (sumField I (fun i => A i t)).jetLp n) := by
  classical
  induction I using Finset.induction_on generalizing n with
  | empty =>
    have he (t : K) : sumField ∅ (fun i => A i t) = (zeroField : SmoothL2Field ℂ) := by
      apply field_ext
      funext x
      simp [sumField_field, zeroField]
    simp_rw [he]
    exact continuous_const
  | @insert i I hi ih =>
    have he (t : K) : sumField (insert i I) (fun j => A j t) =
        addField (A i t) (sumField I (fun j => A j t)) := by
      apply field_ext
      funext x
      simp [sumField_field, addField_field, Finset.sum_insert hi]
    simp_rw [he]
    exact continuous_jetLp_addField _ _ (hA i) ih n

 theorem continuous_jetLp_laplacianField {K : Type*} [TopologicalSpace K]
    (A : K → SmoothL2Field ℂ) (hA : ∀ n, Continuous (fun t => (A t).jetLp n))
    (n : ℕ) : Continuous (fun t => (laplacianField (A t)).jetLp n) := by
  apply continuous_jetLp_sumField
  intro i n
  exact continuous_jetLp_directionalField _
    (continuous_jetLp_directionalField A hA (basis i)) (basis i) n

 theorem continuous_jetLp_besselField {K : Type*} [TopologicalSpace K]
    (A : K → SmoothL2Field ℂ) (hA : ∀ n, Continuous (fun t => (A t).jetLp n))
    (n : ℕ) : Continuous (fun t => (besselField (A t)).jetLp n) :=
  continuous_jetLp_addField _ _ hA
    (continuous_jetLp_mapField _ _ (continuous_jetLp_laplacianField A hA)) n

/-- Iterated physical order-two Bessel operator. -/
def iteratedBesselField : ℕ → SmoothL2Field ℂ → SmoothL2Field ℂ
  | 0, A => A
  | k + 1, A => besselField (iteratedBesselField k A)

 theorem physicalDistribution_iteratedBesselField (k : ℕ) (A : SmoothL2Field ℂ) :
    physicalDistribution (iteratedBesselField k A) =
      TemperedDistribution.besselPotential Space ℂ (2 * (k : ℝ)) (physicalDistribution A) := by
  induction k with
  | zero => simp [iteratedBesselField]
  | succ k ih =>
    rw [iteratedBesselField, physicalDistribution_besselField, ih,
      TemperedDistribution.besselPotential_besselPotential_apply]
    congr 1
    push_cast
    ring

 theorem continuous_jetLp_iteratedBesselField {K : Type*} [TopologicalSpace K]
    (A : K → SmoothL2Field ℂ) (hA : ∀ n, Continuous (fun t => (A t).jetLp n))
    (k n : ℕ) : Continuous (fun t => (iteratedBesselField k (A t)).jetLp n) := by
  induction k generalizing n with
  | zero => exact hA n
  | succ k ih => exact continuous_jetLp_besselField _ ih n

/-- Explicit weighted Fourier datum for every even nonnegative order. -/
def evenSobolevDatum (k : ℕ) (A : SmoothL2Field ℂ) : SobolevHilbert (2 * (k : ℝ)) :=
  𝓕 (iteratedBesselField k A).toLp

 theorem evenSobolevDatum_realization (k : ℕ) (A : SmoothL2Field ℂ) :
    sobolevRealization (2 * (k : ℝ)) (evenSobolevDatum k A) = physicalDistribution A := by
  have hf : ((evenSobolevDatum k A : Lp ℂ 2 volume) : 𝓢'(Space, ℂ)) =
      weightedFourierDistribution (2 * (k : ℝ)) (physicalDistribution A) := by
    rw [evenSobolevDatum, ← Lp.fourier_toTemperedDistribution_eq]
    change 𝓕 (physicalDistribution (iteratedBesselField k A)) = _
    rw [physicalDistribution_iteratedBesselField,
      TemperedDistribution.fourier_besselPotential_eq_smulLeftCLM_fourier_apply]
    rfl
  rw [sobolevRealization_apply, hf, reconstruction_weightedFourier]

@[simp] theorem norm_evenSobolevDatum (k : ℕ) (A : SmoothL2Field ℂ) :
    ‖evenSobolevDatum k A‖ = ‖(iteratedBesselField k A).toLp‖ := Lp.norm_fourier_eq _

 theorem continuous_evenSobolevDatum {K : Type*} [TopologicalSpace K]
    (A : K → SmoothL2Field ℂ) (hA : ∀ n, Continuous (fun t => (A t).jetLp n)) (k : ℕ) :
    Continuous (fun t => evenSobolevDatum k (A t)) :=
  continuous_physicalH0Datum _ (continuous_jetLp_iteratedBesselField A hA k 0)

@[simp] theorem evenSobolevDatum_zero (A : SmoothL2Field ℂ) :
    evenSobolevDatum 0 A = physicalH0Datum A := rfl

 theorem continuous_norm_evenSobolevDatum {K : Type*} [TopologicalSpace K]
    (A : K → SmoothL2Field ℂ) (hA : ∀ n, Continuous (fun t => (A t).jetLp n)) (k : ℕ) :
    Continuous (fun t => ‖evenSobolevDatum k (A t)‖) :=
  (continuous_evenSobolevDatum A hA k).norm

end NSFormalization.Source.PhysicalBesselSobolev
