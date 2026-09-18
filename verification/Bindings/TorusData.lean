import Contracts.V1.TorusData
import NSFormalization.Section3.T10.DatumBasics
import NSFormalization.Section3.T10.Leray
import NSFormalization.Paper1.FourierReconstructionAdapter

/-!
# Binding for the periodic data contract

Every contract-side definition is checked against the canonical T10 data
layer by `rfl`.  The pointwise bridge form is used for polymorphic definitions
whose implicit type or instance arguments make an unannotated bare function
equality underconstrained.

`DatumBasics`, `Parseval`, and `PhysicalBridge` cannot currently coexist in
one Lean environment: their anonymous local torus-measure instances receive
the same generated global declaration names.  This binding therefore imports
the compatible `DatumBasics` and `Leray` pair, uses their five API theorems
directly, and repeats the already-kernel-checked Parseval and physical-bridge
arguments under binding-local names for the other five fields.  This avoids
changing any frozen canonical module; the exact import error is recorded in
`research/T10/ATTEMPTS_CONTRACT.md`.
-/

noncomputable section

namespace BlowupDensity.Bindings

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NavierStokes.PeriodicIntegration (Coords toSpace UnitPeriods)
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.TorusData
open scoped ENNReal BigOperators ComplexConjugate

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-! ## 1. Definitional drift guards -/

theorem periodicFrequency_eq :
    PeriodicFrequency = NSFormalization.Section3.T10.PeriodicFrequency := rfl

theorem periodicTorus_eq :
    PeriodicTorus = NSFormalization.Section3.T10.PeriodicTorus := rfl

theorem periodicTorusMeasure_eq :
    periodicTorusMeasure = NSFormalization.Section3.T10.periodicTorusMeasure := rfl

/-- Pointwise because the implicit result type `E` makes the bare polymorphic
function equality underconstrained. -/
theorem isPeriodicSpatial_eq {E : Type*} [Add E] (z : Space → E) :
    IsPeriodicSpatial z = NSFormalization.Section3.T10.IsPeriodicSpatial z := rfl

/-- Pointwise because both the implicit result type and the set argument must
be fixed before the two polymorphic predicates can be compared. -/
theorem isPeriodicOn_eq {E : Type*} (I : Set ℝ) (z : SpaceTime → E) :
    IsPeriodicOn I z = NSFormalization.Section3.T10.IsPeriodicOn I z := rfl

/-- Pointwise because a bare equality leaves the implicit codomain `E`
unconstrained. -/
theorem torusLift_eq {E : Type*} (f : Space → E) (z : PeriodicTorus) :
    torusLift f z = NSFormalization.Section3.T10.torusLift f z := rfl

theorem periodicFourierCoeff_eq (f : Space → ℂ) (k : PeriodicFrequency) :
    periodicFourierCoeff f k =
      NSFormalization.Section3.T10.periodicFourierCoeff f k := rfl

theorem periodicFrequencyWeight_eq (k : PeriodicFrequency) :
    periodicFrequencyWeight k =
      NSFormalization.Section3.T10.periodicFrequencyWeight k := rfl

theorem periodicScalarData_eq :
    PeriodicScalarData = NSFormalization.Section3.T10.PeriodicScalarData := rfl

theorem periodicVectorData_eq :
    PeriodicVectorData = NSFormalization.Section3.T10.PeriodicVectorData := rfl

theorem realPeriodicSubmodule_eq :
    realPeriodicSubmodule = NSFormalization.Section3.T10.realPeriodicSubmodule := rfl

/-- The phantom-order carrier is bridged through its defining real submodule. -/
theorem periodicSobolev_eq (s : ℝ) :
    PeriodicSobolev s = NSFormalization.Section3.T10.PeriodicSobolev s := by
  exact realPeriodicSubmodule_eq

theorem periodicSobolevDataNorm_eq (s : ℝ) (A : PeriodicSobolev s) :
    periodicSobolevDataNorm s A =
      NSFormalization.Section3.T10.periodicSobolevDataNorm s A := rfl

theorem isPeriodicDatum_eq (s : ℝ) (z : SpatialField) (A : PeriodicSobolev s) :
    IsPeriodicDatum s z A = NSFormalization.Section3.T10.IsPeriodicDatum s z A := rfl

theorem periodicSobolevENorm_eq (s : ℝ) (z : SpatialField) :
    periodicSobolevENorm s z =
      NSFormalization.Section3.T10.periodicSobolevENorm s z := rfl

theorem meanT_eq (z : SpatialField) :
    meanT z = NSFormalization.Section3.T10.meanT z := rfl

theorem constantPartT_eq (z : SpatialField) :
    constantPartT z = NSFormalization.Section3.T10.constantPartT z := rfl

theorem meanZeroPartT_eq (z : SpatialField) :
    meanZeroPartT z = NSFormalization.Section3.T10.meanZeroPartT z := rfl

theorem meanDecompositionT_eq (z : SpatialField) :
    meanDecompositionT z = NSFormalization.Section3.T10.meanDecompositionT z := rfl

theorem meanZeroPeriodicSobolev_eq (s : ℝ) :
    meanZeroPeriodicSobolev s =
      NSFormalization.Section3.T10.meanZeroPeriodicSobolev s := rfl

theorem isMeanZeroT_eq (z : SpatialField) :
    IsMeanZeroT z = NSFormalization.Section3.T10.IsMeanZeroT z := rfl

theorem periodicAngularFrequencySq_eq (k : PeriodicFrequency) :
    periodicAngularFrequencySq k =
      NSFormalization.Section3.T10.periodicAngularFrequencySq k := rfl

theorem homogeneousDatumWeight_eq (s : ℝ) (k : PeriodicFrequency) :
    homogeneousDatumWeight s k =
      NSFormalization.Section3.T10.homogeneousDatumWeight s k := rfl

theorem isPeriodicHomogeneousDatum_eq (s : ℝ) (z : SpatialField)
    (A : PeriodicSobolev s) :
    IsPeriodicHomogeneousDatum s z A =
      NSFormalization.Section3.T10.IsPeriodicHomogeneousDatum s z A := rfl

theorem periodicHomogeneousENorm_eq (s : ℝ) (z : SpatialField) :
    periodicHomogeneousENorm s z =
      NSFormalization.Section3.T10.periodicHomogeneousENorm s z := rfl

theorem periodicDerivativeSymbol_eq (j : Fin 3) (k : PeriodicFrequency) :
    periodicDerivativeSymbol j k =
      NSFormalization.Section3.T10.periodicDerivativeSymbol j k := rfl

theorem isSolenoidalPeriodicDatum_eq {s : ℝ} (A : PeriodicSobolev s) :
    IsSolenoidalPeriodicDatum A =
      NSFormalization.Section3.T10.IsSolenoidalPeriodicDatum (s := s) A := rfl

theorem periodicLeray_eq (s : ℝ) (A : PeriodicSobolev s)
    (i : Fin 3) (k : PeriodicFrequency) :
    periodicLeray s A i k = NSFormalization.Section3.T10.periodicLeray s A i k := rfl

theorem isPeriodicLerayDatum_eq {s : ℝ} (A B : PeriodicSobolev s) :
    IsPeriodicLerayDatum A B =
      NSFormalization.Section3.T10.IsPeriodicLerayDatum (s := s) A B := rfl

theorem isPeriodicReweight_eq (s t : ℝ) (A : PeriodicSobolev s)
    (B : PeriodicSobolev t) :
    IsPeriodicReweight s t A B =
      NSFormalization.Section3.T10.IsPeriodicReweight s t A B := rfl

/-! ## 2. Composition-safe copies of the proved physical and Parseval bridges -/

/-- The contract lift evaluates to a periodic field at every quotient image.
This is the binding-local copy of `T10.torusLift_apply_of_periodic`. -/
private theorem torusData_torusLift_apply_of_periodic {E : Type*} [Add E]
    {z : Space → E} (hz : IsPeriodicSpatial z) (x : Space) :
    torusLift z (fun i ↦ (x i : UnitAddCircle)) = z x := by
  exact NSFormalization.Paper1.torusLift_coe_of_unitPeriods
    (show UnitPeriods z from hz) x

/-- Pullback along the quotient map is unit-periodic.  This is the
binding-local copy of `T10.isPeriodicSpatial_torusLift_comp`. -/
private theorem torusData_isPeriodicSpatial_torusLift_comp {E : Type*} [Add E]
    (Z : PeriodicTorus → E) :
    IsPeriodicSpatial (fun x : Space ↦ Z (fun i ↦ (x i : UnitAddCircle))) := by
  intro x i
  apply congrArg Z
  funext j
  by_cases hji : j = i
  · subst j
    simp [coordinateVector]
  · simp [coordinateVector, hji]

/-- Composition-safe copy of the canonical lift injectivity theorem. -/
private theorem torusData_torusLift_injective :
    ∀ z w : SpatialField, IsPeriodicSpatial z → IsPeriodicSpatial w →
      torusLift z = torusLift w → z = w := by
  intro z w hz hw hzw
  funext x
  rw [← torusData_torusLift_apply_of_periodic hz x,
    ← torusData_torusLift_apply_of_periodic hw x, hzw]

/-- Composition-safe copy of the canonical lift surjectivity theorem. -/
private theorem torusData_torusLift_surjective :
    ∀ Z : PeriodicTorus → Space,
      ∃ z : SpatialField, IsPeriodicSpatial z ∧ torusLift z = Z := by
  intro Z
  let z : SpatialField := fun x ↦ Z (fun i ↦ (x i : UnitAddCircle))
  refine ⟨z, torusData_isPeriodicSpatial_torusLift_comp Z, ?_⟩
  funext q
  change Z (fun i ↦
    (((UnitAddTorus.measurableEquivPiIoc (0 : Coords) q).val i : ℝ) :
      UnitAddCircle)) = Z q
  exact congrArg Z
    ((UnitAddTorus.measurableEquivPiIoc (0 : Coords)).symm_apply_apply q)

/-- A constant physical field has its own normalized torus mean. -/
private theorem torusData_meanT_const (c : Space) :
    meanT (fun _ : Space ↦ c) = c := by
  simp [meanT, torusLift]

/-- Composition-safe copy of the canonical normalized-mean decomposition. -/
private theorem torusData_mean_decomposition :
    ∀ z : SpatialField, IsPeriodicSpatial z →
      Integrable (torusLift z) periodicTorusMeasure →
        (∀ x : Space, constantPartT z x + meanZeroPartT z x = z x) ∧
          IsMeanZeroT (meanZeroPartT z) := by
  intro z _hz hz_int
  constructor
  · intro x
    simp [constantPartT, meanZeroPartT]
  · change meanT (meanZeroPartT z) = 0
    change (∫ y : PeriodicTorus, torusLift z y - meanT z
      ∂periodicTorusMeasure) = 0
    rw [integral_sub hz_int (integrable_const (meanT z))]
    change meanT z - meanT (fun _ : Space ↦ meanT z) = 0
    rw [torusData_meanT_const]
    exact sub_self _

/-- Every complexified component of a real vector lift is in `L²`. -/
private theorem torusData_memLp_torusLift_component (z : SpatialField)
    (hz : MemLp (torusLift z) 2 periodicTorusMeasure) (i : Fin 3) :
    MemLp (torusLift (fun x ↦ ((z x i : ℝ) : ℂ))) 2 periodicTorusMeasure := by
  apply hz.of_le
  · exact (Complex.continuous_ofReal.comp
      (PiLp.continuous_apply 2 (fun _ : Fin 3 ↦ ℝ) i)).comp_aestronglyMeasurable
        hz.aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun y ↦ by
      change ‖((torusLift z y i : ℝ) : ℂ)‖ ≤ ‖torusLift z y‖
      simpa using PiLp.norm_apply_le (torusLift z y) i

/-- The Fourier basis representation computes the contract coefficients. -/
private theorem torusData_fourier_repr_toLp (f : Space → ℂ)
    (hf : MemLp (torusLift f) 2 periodicTorusMeasure) (k : PeriodicFrequency) :
    UnitAddTorus.mFourierBasis.repr (hf.toLp (torusLift f)) k =
      periodicFourierCoeff f k := by
  rw [UnitAddTorus.mFourierBasis_repr]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with y hy
  change UnitAddTorus.mFourier (-k) y • (hf.toLp (torusLift f)) y =
    UnitAddTorus.mFourier (-k) y • torusLift f y
  rw [hy]

/-- Fourier coefficients of real fields have conjugate-reflection symmetry. -/
private theorem torusData_periodicFourierCoeff_real_neg
    (f : Space → ℝ) (k : PeriodicFrequency) :
    periodicFourierCoeff (fun x ↦ (f x : ℂ)) (-k) =
      star (periodicFourierCoeff (fun x ↦ (f x : ℂ)) k) := by
  unfold periodicFourierCoeff UnitAddTorus.mFourierCoeff
  rw [Complex.star_def, ← integral_conj]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y ↦ by
    simp [UnitAddTorus.mFourier_neg, smul_eq_mul, torusLift]

/-- Composition-safe copy of reverse vector Parseval. -/
private theorem torusData_parseval_backward :
    ∀ z : SpatialField, IsPeriodicSpatial z →
      MemLp (torusLift z) 2 periodicTorusMeasure →
        ∃ A : PeriodicSobolev 0, IsPeriodicDatum 0 z A := by
  intro z hp hz
  let a : PeriodicVectorData := WithLp.toLp 2 (fun i ↦
    UnitAddTorus.mFourierBasis.repr
      ((torusData_memLp_torusLift_component z hz i).toLp
        (torusLift (fun x ↦ ((z x i : ℝ) : ℂ)))))
  have ha (i : Fin 3) (k : PeriodicFrequency) :
      a i k = periodicFourierCoeff (fun x ↦ ((z x i : ℝ) : ℂ)) k :=
    torusData_fourier_repr_toLp _ _ k
  have hr : a ∈ realPeriodicSubmodule := by
    intro i k
    rw [ha, ha]
    exact torusData_periodicFourierCoeff_real_neg (fun x ↦ z x i) k
  refine ⟨⟨a, hr⟩, hp, hz.integrable (by norm_num), ?_⟩
  intro i k
  simpa using ha i k

/-- The real squared `L²` norm is the integral of the squared pointwise norm. -/
private theorem torusData_norm_toLp_sq_integral {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : PeriodicTorus → E) (hf : MemLp f 2 periodicTorusMeasure) :
    ‖hf.toLp f‖ ^ 2 = ∫ y, ‖f y‖ ^ 2 ∂periodicTorusMeasure := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with y hy
  rw [hy, real_inner_self_eq_norm_sq]

/-- Scalar Parseval for each component of an order-zero datum. -/
private theorem torusData_datum_component_norm_sq (z : SpatialField)
    (A : PeriodicSobolev 0) (hA : IsPeriodicDatum 0 z A)
    (hz : MemLp (torusLift z) 2 periodicTorusMeasure) (i : Fin 3) :
    ‖A.1 i‖ ^ 2 = ∫ y, ‖((torusLift z y i : ℝ) : ℂ)‖ ^ 2 ∂periodicTorusMeasure := by
  have heq : A.1 i = UnitAddTorus.mFourierBasis.repr
      ((torusData_memLp_torusLift_component z hz i).toLp
        (torusLift (fun x ↦ ((z x i : ℝ) : ℂ)))) := by
    ext k
    rw [torusData_fourier_repr_toLp]
    simpa using hA.2.2 i k
  rw [heq, LinearIsometryEquiv.norm_map]
  exact torusData_norm_toLp_sq_integral _ _

/-- Vector Parseval as a real squared-norm identity. -/
private theorem torusData_datum_norm_sq_integral (z : SpatialField)
    (A : PeriodicSobolev 0) (hA : IsPeriodicDatum 0 z A)
    (hz : MemLp (torusLift z) 2 periodicTorusMeasure) :
    ‖A‖ ^ 2 = ∫ y, ‖torusLift z y‖ ^ 2 ∂periodicTorusMeasure := by
  change ‖A.1‖ ^ 2 = _
  rw [PiLp.norm_sq_eq_of_L2]
  simp_rw [torusData_datum_component_norm_sq z A hA hz]
  rw [← integral_finsetSum]
  · apply integral_congr_ae
    exact Filter.Eventually.of_forall fun y ↦ by
      simp [PiLp.norm_sq_eq_of_L2]
  · intro i _
    exact (torusData_memLp_torusLift_component z hz i).integrable_norm_pow (by norm_num)

/-- Composition-safe copy of forward vector Parseval. -/
private theorem torusData_parseval_forward :
    ∀ (z : SpatialField) (A : PeriodicSobolev 0), IsPeriodicDatum 0 z A →
      MemLp (torusLift z) 2 periodicTorusMeasure →
      ‖A‖ₑ = eLpNorm (torusLift z) 2 periodicTorusMeasure := by
  intro z A hA hz
  have hn : ‖A‖ = ‖hz.toLp (torusLift z)‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [torusData_datum_norm_sq_integral z A hA hz,
      torusData_norm_toLp_sq_integral]
  rw [← Lp.enorm_toLp hz, ← ofReal_norm, ← ofReal_norm, hn]

/-! ## 3. The proved API -/

/-- The ten canonical T10 theorems, transported only by definitional equality. -/
def torusData : Contracts.V1.TorusData.TorusDataAPI := {
  datum_unique := NSFormalization.Section3.T10.datum_unique
  datum_real := NSFormalization.Section3.T10.datum_real
  parseval_forward := torusData_parseval_forward
  parseval_backward := torusData_parseval_backward
  torusLift_injective := torusData_torusLift_injective
  torusLift_surjective := torusData_torusLift_surjective
  mean_decomposition := torusData_mean_decomposition
  meanZero_datum := NSFormalization.Section3.T10.meanZero_datum
  leray_exists_contraction := NSFormalization.Section3.T10.leray_exists_contraction
  leray_projector := NSFormalization.Section3.T10.leray_projector
}

end BlowupDensity.Bindings
