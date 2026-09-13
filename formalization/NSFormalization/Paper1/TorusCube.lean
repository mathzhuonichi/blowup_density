import Mathlib.Analysis.Fourier.AddCircleMulti
import NavierStokes.PeriodicIntegration

/-!
# Unit-torus Fourier coefficients and the original physical cube integral

Mathlib's proved fundamental-domain measure equivalence and multidimensional
Fourier Parseval theorem are used directly. The canonical lift uses representatives
in (0,1]^3; boundaries do not change the source cube integral on [0,1]^3.
-/
noncomputable section
namespace NSFormalization.Paper1
open Set MeasureTheory NavierStokes.ProblemStatement NavierStokes.PeriodicIntegration
open scoped ContDiff ENNReal

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

abbrev PeriodicTorus := UnitAddTorus (Fin 3)
abbrev PeriodicFrequency := Fin 3 → ℤ
abbrev periodicTorusMeasure : Measure PeriodicTorus := volume

/-- Canonical measurable realization on the unit torus. -/
def torusLift {E : Type*} (f : Space → E) (z : PeriodicTorus) : E :=
  f (toSpace ((UnitAddTorus.measurableEquivPiIoc (0 : Coords) z).val))

 theorem torusLift_coe {E : Type*} (f : Space → E) (y : Coords)
    (hy : ∀ i, y i ∈ Ioc (0 : ℝ) 1) :
    torusLift f (fun i => (y i : AddCircle (1 : ℝ))) = f (toSpace y) := by
  let Y : {x : Coords // ∀ i, x i ∈ Ioc ((0 : Coords) i) ((0 : Coords) i + 1)} :=
    ⟨y, by simpa using hy⟩
  have h := (UnitAddTorus.measurableEquivPiIoc (0 : Coords)).apply_symm_apply Y
  change (UnitAddTorus.measurableEquivPiIoc (0 : Coords))
    (fun i => (y i : AddCircle (1 : ℝ))) = Y at h
  unfold torusLift
  rw [h]

/-- Exact bridge from Haar integration to the existing physical cube integral. -/
theorem integral_torusLift {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Space → E) : ∫ z : PeriodicTorus, torusLift f z ∂periodicTorusMeasure = cubeIntegral f := by
  rw [UnitAddTorus.integral_preimage (torusLift f) (0 : Coords)]
  have hioc : {y : Coords | ∀ i, y i ∈ Ioc ((0 : Coords) i) ((0 : Coords) i + 1)} =
      Set.univ.pi (fun _ : Fin 3 => Ioc (0 : ℝ) 1) := by ext y; simp
  rw [hioc]
  trans ∫ y in Set.univ.pi (fun _ : Fin 3 => Ioc (0 : ℝ) 1), f (toSpace y)
  · apply setIntegral_congr_fun (MeasurableSet.univ_pi fun _ => measurableSet_Ioc)
    intro y hy
    exact torusLift_coe f y (fun i => hy i (mem_univ i))
  · change _ = ∫ y in Icc (0 : Coords) 1, f (toSpace y)
    apply setIntegral_congr_set
    exact Measure.univ_pi_Ioc_ae_eq_Icc

 theorem measurable_torusLift {f : Space → ℂ} (hf : Continuous f) : Measurable (torusLift f) :=
  (hf.comp toSpace.continuous).measurable.comp
    (measurable_subtype_coe.comp (UnitAddTorus.measurableEquivPiIoc (0 : Coords)).measurable)

 theorem memLp_torusLift {f : Space → ℂ} (hf : Continuous f) (q : ℝ≥0∞) :
    MemLp (torusLift f) q periodicTorusMeasure := by
  obtain ⟨M, hM⟩ := ((isCompact_Icc : IsCompact (Icc (0 : Coords) 1)).image
    (hf.comp toSpace.continuous)).isBounded.exists_norm_le
  apply MemLp.of_bound (measurable_torusLift hf).aestronglyMeasurable M
  apply Filter.Eventually.of_forall
  intro z
  apply hM
  refine ⟨(UnitAddTorus.measurableEquivPiIoc (0 : Coords) z).val, ?_, rfl⟩
  constructor <;> intro i
  · exact ((UnitAddTorus.measurableEquivPiIoc (0 : Coords) z).property i).1.le
  · simpa using ((UnitAddTorus.measurableEquivPiIoc (0 : Coords) z).property i).2

/-- An actual L2 torus vector associated with the original physical field. -/
def torusLp (f : Space → ℂ) (hf : Continuous f) : Lp ℂ 2 periodicTorusMeasure :=
  (memLp_torusLift hf 2).toLp (torusLift f)

/-- Actual multidimensional Fourier coefficients, with the unit-period angular convention. -/
def periodicFourierCoeff (f : Space → ℂ) (k : PeriodicFrequency) : ℂ :=
  UnitAddTorus.mFourierCoeff (torusLift f) k

 theorem mFourierCoeff_torusLp (f : Space → ℂ) (hf : Continuous f) (k : PeriodicFrequency) :
    UnitAddTorus.mFourierCoeff (torusLp f hf) k = periodicFourierCoeff f k := by
  apply integral_congr_ae
  filter_upwards [(memLp_torusLift hf 2).coeFn_toLp] with z hz
  change torusLp f hf z = torusLift f z at hz
  rw [hz]

/-- Parseval for the original cube L2 energy, directly inherited from Mathlib. -/
theorem hasSum_sq_periodicFourierCoeff (f : Space → ℂ) (hf : Continuous f) :
    HasSum (fun k : PeriodicFrequency => ‖periodicFourierCoeff f k‖ ^ 2)
      (cubeIntegral (fun x => ‖f x‖ ^ 2)) := by
  have h := UnitAddTorus.hasSum_sq_mFourierCoeff (torusLp f hf)
  simp_rw [mFourierCoeff_torusLp] at h
  convert h using 1
  rw [← integral_torusLift (fun x => ‖f x‖ ^ 2)]
  apply integral_congr_ae
  filter_upwards [(memLp_torusLift hf 2).coeFn_toLp] with z hz
  change ‖torusLift f z‖ ^ 2 = ‖torusLp f hf z‖ ^ 2
  change torusLp f hf z = torusLift f z at hz
  rw [hz]

end NSFormalization.Paper1
