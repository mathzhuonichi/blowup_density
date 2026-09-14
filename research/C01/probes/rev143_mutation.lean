import NSFormalization.Section4.C01.MomentumCarrierB

/-! Reviewer probe (lane 143), NEGATIVE check for `momentum_split_toLp`.
Two substantive mutations of the *statement*, each with the lane's verbatim proof
script.  `set_option autoImplicit false` so a changed statement cannot be rescued
by silent implicit re-binding (LESSONS 077). -/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open EulerLpTranslation EulerLpTranslation.SmoothL2Field EulerOrdinarySobolev EulerSmoothLimit
open NSFormalization.Source.OrdinaryViscousStability
open NavierStokes.ProblemStatement (temporalDerivative advection spatialLaplacian
  pressureGradient coordinateVector spatialDivergence spatialDerivative VelocityField
  PressureField)
open scoped RealInnerProductSpace ContDiff

namespace NSFormalization.Section4.C01

open NSFormalization.Section4.A02 (ClassicalSolutionR MemForceR)

variable {ν : ℝ} {a : A02.SpatialField} {f : A02.SpaceTimeField} {T : ℝ}

/-- MUTATION 1: the `∇p` term's sign is flipped (`- P.toLp` becomes `+ P.toLp`). -/
theorem mut1_sign_flip_pressure (w : ClassicalSolutionR ν a f T) (hf : MemForceR f)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    (temporalSliceField w hf ht).toLp
      = ν • (laplacianField (velocitySliceField w (Ioo_subset_Ico_self ht))).toLp
          - (advectionField (velocitySliceField w (Ioo_subset_Ico_self ht))
              (velocitySliceField w (Ioo_subset_Ico_self ht))).toLp
          + (pressureGradientField w hf ht).toLp
          + (forceSliceField hf (le_of_lt ht.1)).toLp := by
  apply Lp.ext
  filter_upwards [(temporalSliceField w hf ht).toLp_ae,
    Lp.coeFn_add (ν • (laplacianField (velocitySliceField w (Ioo_subset_Ico_self ht))).toLp
        - (advectionField (velocitySliceField w (Ioo_subset_Ico_self ht))
            (velocitySliceField w (Ioo_subset_Ico_self ht))).toLp
        + (pressureGradientField w hf ht).toLp) (forceSliceField hf (le_of_lt ht.1)).toLp,
    Lp.coeFn_add (ν • (laplacianField (velocitySliceField w (Ioo_subset_Ico_self ht))).toLp
        - (advectionField (velocitySliceField w (Ioo_subset_Ico_self ht))
            (velocitySliceField w (Ioo_subset_Ico_self ht))).toLp)
      (pressureGradientField w hf ht).toLp,
    Lp.coeFn_sub (ν • (laplacianField (velocitySliceField w (Ioo_subset_Ico_self ht))).toLp)
      (advectionField (velocitySliceField w (Ioo_subset_Ico_self ht))
        (velocitySliceField w (Ioo_subset_Ico_self ht))).toLp,
    Lp.coeFn_smul ν (laplacianField (velocitySliceField w (Ioo_subset_Ico_self ht))).toLp,
    (laplacianField (velocitySliceField w (Ioo_subset_Ico_self ht))).toLp_ae,
    (advectionField (velocitySliceField w (Ioo_subset_Ico_self ht))
      (velocitySliceField w (Ioo_subset_Ico_self ht))).toLp_ae,
    (pressureGradientField w hf ht).toLp_ae,
    (forceSliceField hf (le_of_lt ht.1)).toLp_ae]
    with x htemp hadd hsub2 hsub1 hsmul hlap hadv hpr hforce
  rw [htemp, hadd, Pi.add_apply, hsub2, Pi.add_apply, hsub1, Pi.sub_apply, hsmul,
    Pi.smul_apply, hlap, hadv, hpr, hforce,
    laplacianField_velocitySlice_field w (Ioo_subset_Ico_self ht) x,
    advectionField_velocitySlice_field w (Ioo_subset_Ico_self ht) x]
  simp only [temporalSliceField_field, pressureGradientField_field, forceSliceField_field]
  rw [D01.temporalDerivative_slice_eq w ht x]
  abel

/-- MUTATION 2: the viscosity is dropped (`ν • Δu` becomes `Δu`). -/
theorem mut2_drop_nu (w : ClassicalSolutionR ν a f T) (hf : MemForceR f)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    (temporalSliceField w hf ht).toLp
      = (laplacianField (velocitySliceField w (Ioo_subset_Ico_self ht))).toLp
          - (advectionField (velocitySliceField w (Ioo_subset_Ico_self ht))
              (velocitySliceField w (Ioo_subset_Ico_self ht))).toLp
          - (pressureGradientField w hf ht).toLp
          + (forceSliceField hf (le_of_lt ht.1)).toLp := by
  apply Lp.ext
  filter_upwards [(temporalSliceField w hf ht).toLp_ae,
    Lp.coeFn_add ((laplacianField (velocitySliceField w (Ioo_subset_Ico_self ht))).toLp
        - (advectionField (velocitySliceField w (Ioo_subset_Ico_self ht))
            (velocitySliceField w (Ioo_subset_Ico_self ht))).toLp
        - (pressureGradientField w hf ht).toLp) (forceSliceField hf (le_of_lt ht.1)).toLp,
    Lp.coeFn_sub ((laplacianField (velocitySliceField w (Ioo_subset_Ico_self ht))).toLp
        - (advectionField (velocitySliceField w (Ioo_subset_Ico_self ht))
            (velocitySliceField w (Ioo_subset_Ico_self ht))).toLp)
      (pressureGradientField w hf ht).toLp,
    Lp.coeFn_sub (laplacianField (velocitySliceField w (Ioo_subset_Ico_self ht))).toLp
      (advectionField (velocitySliceField w (Ioo_subset_Ico_self ht))
        (velocitySliceField w (Ioo_subset_Ico_self ht))).toLp,
    (laplacianField (velocitySliceField w (Ioo_subset_Ico_self ht))).toLp_ae,
    (advectionField (velocitySliceField w (Ioo_subset_Ico_self ht))
      (velocitySliceField w (Ioo_subset_Ico_self ht))).toLp_ae,
    (pressureGradientField w hf ht).toLp_ae,
    (forceSliceField hf (le_of_lt ht.1)).toLp_ae]
    with x htemp hadd hsub2 hsub1 hlap hadv hpr hforce
  rw [htemp, hadd, Pi.add_apply, hsub2, Pi.sub_apply, hsub1, Pi.sub_apply,
    hlap, hadv, hpr, hforce,
    laplacianField_velocitySlice_field w (Ioo_subset_Ico_self ht) x,
    advectionField_velocitySlice_field w (Ioo_subset_Ico_self ht) x]
  simp only [temporalSliceField_field, pressureGradientField_field, forceSliceField_field]
  rw [D01.temporalDerivative_slice_eq w ht x]
  abel

end NSFormalization.Section4.C01
