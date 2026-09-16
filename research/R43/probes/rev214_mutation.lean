import NSFormalization.Section4.R43.ShiftedData

/-!
# Fractional Parseval and the completed critical advection bridge

The homogeneous data are normalized angular Fourier data.  Componentwise
Plancherel and the symbol of the physical Riesz realization transfer their
half-order pairing to the physical pairing with `Λv`.
-/

noncomputable section

open Set MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Paper3 NSFormalization.Source.RealSobolev
open scoped RealInnerProductSpace ComplexConjugate

namespace NSFormalization.Section4.R43.Rev214

open NSFormalization.Section4.A02
  (SpatialField SpaceTimeField ClassicalSolutionR MemForceR MemHInfty)
open NSFormalization.Section4.D01 (componentLp componentLp_ae)
open NSFormalization.Section4.D01.Homogeneous
  (IsHomogeneousSliceDatum isSliceDistribution_unique)
open NSFormalization.Section4.A05

/-- Identify homogeneous slice data with the canonical angular `L²` transform. -/
theorem homogeneous_slice_angular_ae {s : ℝ} {v : SpatialField}
    (hv : MemLp v 2 volume) {A : RealVectorSobolev s}
    (hA : IsHomogeneousSliceDatum s v A) (i : Fin 3) :
    (angularFrequencyDilation (FourierTransform.fourier (componentLp hv i)) :
        Space → ℂ) =ᵐ[volume]
      fun ξ => ((‖ξ‖ ^ (-s) : ℝ) : ℂ) * (A i : FourierData) ξ := by
  obtain ⟨U, hU, hAU⟩ := hA
  have hUV := isSliceDistribution_unique hU (isSliceDistribution_componentLp hv)
  subst U
  exact homogeneousDatum_angularFourier_ae (hAU i)

/-- Scalar real Plancherel, including the normalized angular dilation. -/
theorem angular_real_parseval (g h : FourierData) :
    inner ℝ (angularFrequencyDilation (FourierTransform.fourier g))
        (angularFrequencyDilation (FourierTransform.fourier h)) =
      inner ℝ g h := by
  rw [real_inner_eq_re_complex, angularFrequencyDilation.inner_map_map,
    Lp.inner_fourier_eq, real_inner_eq_re_complex]

/-- The real inner product of complexified component classes is the physical
component pairing. -/
theorem component_real_pairing {u v : SpatialField}
    (hu : MemLp u 2 volume) (hv : MemLp v 2 volume) (i : Fin 3) :
    inner ℝ (componentLp hu i) (componentLp hv i) =
      ∫ x : Space, u x i * v x i := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [componentLp_ae hu i, componentLp_ae hv i] with x hu' hv'
  rw [hu', hv']
  simp [Complex.inner, mul_comm]

/-- Fractional Parseval for any square-integrable first field with half-order
homogeneous datum and any `H^∞` second field with half-order datum. -/
theorem half_order_parseval {u v : SpatialField}
    (hu : MemLp u 2 volume) (hv : MemHInfty v)
    {A B : RealVectorSobolev (1 / 2)}
    (hA : IsHomogeneousSliceDatum (1 / 2) u A)
    (hB : IsHomogeneousSliceDatum (1 / 2) v B) :
    ⟪A, B⟫ = 2 * ∫ x : Space, inner ℝ (u x) (rieszLambda v hv x) := by
  have hscalar (i : Fin 3) :
      inner ℝ (A i) (B i) =
        inner ℝ (componentLp hu i) (componentLp (rieszLambdaMemLp v hv) i) := by
    rw [← angular_real_parseval]
    rw [realSobolev_inner_eq_ambient, real_inner_eq_re_complex,
      real_inner_eq_re_complex]
    congr 1
    rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [homogeneous_slice_angular_ae hu hA i,
      homogeneous_slice_angular_ae (sourceSmoothField v hv).memLp hB i,
      angular_rieszLambda_component_ae v hv i, volume.ae_ne (0 : Space)]
      with ξ ha hb hl hξ
    rw [hl, ha, hb]
    have hn : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
    have hp : ‖ξ‖ * (‖ξ‖ ^ (-(1 / 2 : ℝ)) * ‖ξ‖ ^ (-(1 / 2 : ℝ))) = 1 := by
      rw [← Real.rpow_add hn]
      norm_num
      simpa only [Real.rpow_neg_one] using mul_inv_cancel₀ hn.ne'
    have hpc : (‖ξ‖ : ℂ) *
        (((‖ξ‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          ((‖ξ‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) = 1 := by
      exact_mod_cast hp
    simp only [RCLike.inner_apply, map_mul, Complex.conj_ofReal]
    calc
      _ = (1 : ℂ) * ((B i : FourierData) ξ * conj ((A i : FourierData) ξ)) := by ring
      _ = _ := by rw [← hpc]; ring
  rw [PiLp.inner_apply]
  simp_rw [hscalar, component_real_pairing]
  rw [← integral_finsetSum]
  · apply integral_congr_ae
    filter_upwards [] with x
    simp [PiLp.inner_apply, mul_comm]
  · intro i _
    exact ((EuclideanSpace.proj (𝕜 := ℝ) i).comp_memLp' hu).integrable_mul
      ((EuclideanSpace.proj (𝕜 := ℝ) i).comp_memLp' (rieszLambdaMemLp v hv))

/-- The exact fractional Parseval field for lane 191's chosen shifted data. -/
theorem pairing_identity_of_hcrit
    {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    {w : ClassicalSolutionR ν a f T} {hf : MemForceR f}
    (hcrit : CriticalDatumPath w hf) :
    ∀ t (ht : t ∈ Ioo (0 : ℝ) T),
      ⟪hcrit.advectionHalf t, hcrit.velocityHalf t⟫ =
        ∫ x : Space, (inner ℝ
          (advection (NSFormalization.Section4.C01.lift
            (fun y => w.velocity (t, y))) 0 x)
          ((criticalAdvectionLpBridge_shifted hcrit t ht).lambda x) : ℝ) := by
  intro t ht
  exact half_order_parseval
    (NSFormalization.Section4.A03.SmoothL2.memLp
      (NSFormalization.Section4.D01.advection_slice_smoothL2 w ht))
    (NSFormalization.Section4.C01.velocity_slice_memHInfty w (Ioo_subset_Ico_self ht))
    (hcrit.advectionHalf_isDatum t ht)
    (hcrit.velocityHalf_isDatum t (Ioo_subset_Ico_self ht))

/-- The complete S1b bridge, with no input beyond the critical datum path. -/
def criticalAdvectionLpBridge_of_hcrit
    {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    {w : ClassicalSolutionR ν a f T} {hf : MemForceR f}
    (hcrit : CriticalDatumPath w hf) : CriticalAdvectionLpBridge hcrit where
  shifted := criticalAdvectionLpBridge_shifted hcrit
  pairing_identity := pairing_identity_of_hcrit hcrit

/-- S1b with the carrier and Parseval obligations discharged. -/
theorem criticalTrilinearEstimate_of_hcrit'
    {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    {w : ClassicalSolutionR ν a f T} {hf : MemForceR f}
    (hcrit : CriticalDatumPath w hf) :
    CriticalTrilinearEstimate (C₀ := trilinearConst) hcrit :=
  criticalTrilinearEstimate_of_hcrit hcrit (criticalAdvectionLpBridge_of_hcrit hcrit)

/-- The critical differential inequality, conditional on `hcrit` alone. -/
theorem rcritical1_of_hcrit'
    {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    {w : ClassicalSolutionR ν a f T} (hf : MemForceR f)
    (hcrit : CriticalDatumPath w hf) :
    (∀ t ∈ Ioo (0 : ℝ) T,
      HasDerivAt (fun r => criticalNormAt w.velocity r ^ 2)
        (criticalEnergyDerivative hcrit t) t) ∧
      ∀ t ∈ Ioo (0 : ℝ) T,
        criticalEnergyDerivative hcrit t / 2 +
            (ν - trilinearConst * criticalNormAt w.velocity t) *
              criticalDissipationAt w.velocity t ^ 2
          ≤ criticalForceAt f t * criticalNormAt w.velocity t :=
  rcritical1_of_hcrit hf hcrit (criticalAdvectionLpBridge_of_hcrit hcrit)

end NSFormalization.Section4.R43.Rev214
