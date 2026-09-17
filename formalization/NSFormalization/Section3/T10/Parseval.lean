import NSFormalization.Section3.T10.PeriodicData

/-!
# Vector Parseval on the unit three-torus

The scalar Fourier Hilbert basis supplies each component of the coefficient datum.
Its isometry gives scalar Parseval for arbitrary L² lifts; finite additivity of the
Bochner integral then gives vector Parseval as a real squared-norm identity.
`Lp.enorm_toLp` transports that identity to the extended norm in the canonical API.
The local Haar instances are the same ones used in `Paper1.TorusCube`.
-/

noncomputable section
namespace NSFormalization.Section3.T10

open MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField)
open scoped ENNReal BigOperators ComplexConjugate

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The canonical product Haar measure has total mass one. -/
theorem periodicTorusMeasure_probability : IsProbabilityMeasure periodicTorusMeasure :=
  inferInstance

/-- Every complexified component of a real L² vector field is in L². -/
theorem memLp_torusLift_component (z : SpatialField)
    (hz : MemLp (torusLift z) 2 periodicTorusMeasure) (i : Fin 3) :
    MemLp (torusLift (fun x ↦ ((z x i : ℝ) : ℂ))) 2 periodicTorusMeasure := by
  apply hz.of_le
  · exact (Complex.continuous_ofReal.comp
      (PiLp.continuous_apply 2 (fun _ : Fin 3 ↦ ℝ) i)).comp_aestronglyMeasurable
        hz.aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun y ↦ by
      change ‖((torusLift z y i : ℝ) : ℂ)‖ ≤ ‖torusLift z y‖
      simpa using PiLp.norm_apply_le (torusLift z y) i

/-- The Fourier basis representation computes the canonical coefficients for L² lifts. -/
theorem fourier_repr_toLp (f : Space → ℂ)
    (hf : MemLp (torusLift f) 2 periodicTorusMeasure) (k : PeriodicFrequency) :
    UnitAddTorus.mFourierBasis.repr (hf.toLp (torusLift f)) k =
      periodicFourierCoeff f k := by
  rw [UnitAddTorus.mFourierBasis_repr]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with y hy
  change UnitAddTorus.mFourier (-k) y • (hf.toLp (torusLift f)) y =
    UnitAddTorus.mFourier (-k) y • torusLift f y
  rw [hy]

/-- Real fields have conjugate-reflection symmetric Fourier coefficients. -/
theorem periodicFourierCoeff_real_neg (f : Space → ℝ) (k : PeriodicFrequency) :
    periodicFourierCoeff (fun x ↦ (f x : ℂ)) (-k) =
      star (periodicFourierCoeff (fun x ↦ (f x : ℂ)) k) := by
  unfold periodicFourierCoeff NSFormalization.Paper1.periodicFourierCoeff UnitAddTorus.mFourierCoeff
  rw [Complex.star_def, ← integral_conj]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y ↦ by
    simp [UnitAddTorus.mFourier_neg, smul_eq_mul, NSFormalization.Paper1.torusLift]

/-- Reverse Parseval constructs the three ℓ² sequences and their real symmetry. -/
theorem parseval_backward :
    ∀ z : SpatialField, IsPeriodicSpatial z →
      MemLp (torusLift z) 2 periodicTorusMeasure →
        ∃ A : PeriodicSobolev 0, IsPeriodicDatum 0 z A := by
  intro z hp hz
  let a : PeriodicVectorData := WithLp.toLp 2 (fun i ↦
    UnitAddTorus.mFourierBasis.repr
      ((memLp_torusLift_component z hz i).toLp (torusLift (fun x ↦ ((z x i : ℝ) : ℂ)))))
  have ha (i : Fin 3) (k : PeriodicFrequency) :
      a i k = periodicFourierCoeff (fun x ↦ ((z x i : ℝ) : ℂ)) k :=
    fourier_repr_toLp _ _ k
  have hr : a ∈ realPeriodicSubmodule := by
    intro i k
    rw [ha, ha]
    exact periodicFourierCoeff_real_neg (fun x ↦ z x i) k
  refine ⟨⟨a, hr⟩, hp, hz.integrable (by norm_num), ?_⟩
  intro i k
  simpa using ha i k

/-- The real squared L² norm is the integral of the pointwise squared norm. -/
theorem norm_toLp_sq_integral {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : PeriodicTorus → E) (hf : MemLp f 2 periodicTorusMeasure) :
    ‖hf.toLp f‖ ^ 2 = ∫ y, ‖f y‖ ^ 2 ∂periodicTorusMeasure := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with y hy
  rw [hy, real_inner_self_eq_norm_sq]

/-- At order zero, each component of a datum has the scalar Parseval norm. -/
theorem datum_component_norm_sq (z : SpatialField) (A : PeriodicSobolev 0)
    (hA : IsPeriodicDatum 0 z A) (hz : MemLp (torusLift z) 2 periodicTorusMeasure)
    (i : Fin 3) :
    ‖A.1 i‖ ^ 2 = ∫ y, ‖((torusLift z y i : ℝ) : ℂ)‖ ^ 2 ∂periodicTorusMeasure := by
  have heq : A.1 i = UnitAddTorus.mFourierBasis.repr
      ((memLp_torusLift_component z hz i).toLp (torusLift (fun x ↦ ((z x i : ℝ) : ℂ)))) := by
    ext k
    rw [fourier_repr_toLp]
    simpa using hA.2.2 i k
  rw [heq, LinearIsometryEquiv.norm_map]
  exact norm_toLp_sq_integral _ _

/-- Vector Parseval as a real identity, before passing to extended norms. -/
theorem datum_norm_sq_integral (z : SpatialField) (A : PeriodicSobolev 0)
    (hA : IsPeriodicDatum 0 z A) (hz : MemLp (torusLift z) 2 periodicTorusMeasure) :
    ‖A‖ ^ 2 = ∫ y, ‖torusLift z y‖ ^ 2 ∂periodicTorusMeasure := by
  change ‖A.1‖ ^ 2 = _
  rw [PiLp.norm_sq_eq_of_L2]
  simp_rw [datum_component_norm_sq z A hA hz]
  rw [← integral_finsetSum]
  · apply integral_congr_ae
    exact Filter.Eventually.of_forall fun y ↦ by
      simp [PiLp.norm_sq_eq_of_L2]
  · intro i _
    exact (memLp_torusLift_component z hz i).integrable_norm_pow (by norm_num)

/-- Forward vector Parseval, with the physical L² hypothesis of the canonical API. -/
theorem parseval_forward :
    ∀ (z : SpatialField) (A : PeriodicSobolev 0), IsPeriodicDatum 0 z A →
      MemLp (torusLift z) 2 periodicTorusMeasure →
      ‖A‖ₑ = eLpNorm (torusLift z) 2 periodicTorusMeasure := by
  intro z A hA hz
  have hn : ‖A‖ = ‖hz.toLp (torusLift z)‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [datum_norm_sq_integral z A hA hz, norm_toLp_sq_integral]
  rw [← Lp.enorm_toLp hz, ← ofReal_norm, ← ofReal_norm, hn]

end NSFormalization.Section3.T10
