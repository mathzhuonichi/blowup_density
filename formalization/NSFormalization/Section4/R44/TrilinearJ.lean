import NSFormalization.Section4.R44.JWeight
import NSFormalization.Section4.R43.Parseval
import NSFormalization.Section4.A04.NonlinearPairing
import NSFormalization.Section4.D01.OrderZeroSymbol
import NSFormalization.Source.BesselFractionalData

/-!
# R44 row S1c: the `J`-weighted trilinear estimate

This module proves the datum-level estimate for the nonlinear pairing with
`J = (I - Δ)^(1/2)`.  The only additional input is the separate
`AdvectionJDatum` package below: it records the negative-half-order advection
datum and the standard `H^∞` regularity needed by the three-factor Hölder
step.  It contains no estimate.  The physical `L²` realization of `Ju` and
the exact Parseval identity are derived here rather than assumed.

The bridge from the inhomogeneous half-order data to the homogeneous data
consumed by A05 is proved here from the bounded multiplier
`|ξ|^(1/2) (1+|ξ|²)^(-1/4)`.  Thus the three critical `L³` bounds are
controlled by the actual `JWeightDatum` norms rather than by extra hypotheses.
-/

noncomputable section

open Set MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Paper3
open NSFormalization.Source RealSobolev
open scoped ENNReal RealInnerProductSpace SchwartzMap

namespace NSFormalization.Section4.R44

open NSFormalization.Section4.A02 (MemHInfty SpatialField)
open NSFormalization.Section4.D01
open NSFormalization.Section4.D01.Homogeneous

/-! ## 1. The half-order inhomogeneous-to-homogeneous datum bridge -/

/-- The scalar half-order homogeneous datum obtained from an inhomogeneous
half-order datum by the contractive Bessel-to-Riesz multiplier. -/
def halfHomogeneousComponent (A : RealSobolevHilbert (1 / 2)) :
    RealSobolevHilbert (1 / 2) :=
  ⟨BesselFractionalData.datum (1 / 2) (by norm_num) (A : FourierData), by
    rw [mem_realSubspace_iff]
    apply Lp.ext
    have hneg := (Measure.measurePreserving_neg
      (volume : Measure Space)).quasiMeasurePreserving.ae
        (BesselFractionalData.datum_coeFn (1 / 2) (by norm_num)
          (A : FourierData))
    have hreal := realSymmetry_ae (A : FourierData)
    rw [(mem_realSubspace_iff (1 / 2) _).mp A.2] at hreal
    filter_upwards [realSymmetry_ae
        (BesselFractionalData.datum (1 / 2) (by norm_num) (A : FourierData)),
      BesselFractionalData.datum_coeFn (1 / 2) (by norm_num)
        (A : FourierData), hneg, hreal] with ξ hout hhere hthere hA
    rw [hout, hthere, map_mul, ← hA, hhere]
    simp [BesselFractionalData.symbol, sobolevBesselWeight] ⟩

@[simp] theorem halfHomogeneousComponent_coe (A : RealSobolevHilbert (1 / 2)) :
    ((halfHomogeneousComponent A : RealSobolevHilbert (1 / 2)) : FourierData) =
      BesselFractionalData.datum (1 / 2) (by norm_num) (A : FourierData) := rfl

/-- Componentwise form of the Bessel-to-Riesz contraction. -/
def halfHomogeneousDatum (A : RealVectorSobolev (1 / 2)) :
    RealVectorSobolev (1 / 2) :=
  WithLp.toLp 2 fun i => halfHomogeneousComponent (A i)

/-- The Bessel-to-Riesz datum map is contractive. -/
theorem halfHomogeneousDatum_norm_le (A : RealVectorSobolev (1 / 2)) :
    ‖halfHomogeneousDatum A‖ ≤ ‖A‖ := by
  rw [PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2]
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro i _
  apply pow_le_pow_left₀ (norm_nonneg _)
  exact BesselFractionalData.datum_norm_le (1 / 2) (by norm_num)
    (A i : FourierData)

/-- At order one half, every inhomogeneous datum supplies the corresponding
homogeneous datum of the same physical field. -/
theorem halfHomogeneousDatum_isDatum
    {z : NSFormalization.Section4.A02.SpatialField}
    {A : RealVectorSobolev (1 / 2)} (hA : IsSobolevDatum (1 / 2) z A) :
    IsHomogeneousSliceDatum (1 / 2) z (halfHomogeneousDatum A) := by
  refine ⟨fun i => angularRealization (1 / 2) (A i : FourierData), ?_, ?_⟩
  · intro i ψ
    exact hA i ψ
  · intro i φ
    let L : FourierData := sobolevOrderLowering (1 / 2) 0 (by norm_num)
      (A i : FourierData)
    have hcancel : (fun ξ : Space => φ ξ *
          (((‖ξ‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
            ((((halfHomogeneousDatum A) i : RealSobolevHilbert (1 / 2)) :
              FourierData) ξ))) =ᵐ[volume]
        fun ξ => φ ξ * L ξ := by
      filter_upwards [BesselFractionalData.datum_coeFn
          (1 / 2) (by norm_num) (A i : FourierData),
        sobolevOrderLowering_coeFn (1 / 2) 0 (by norm_num)
          (A i : FourierData), volume.ae_ne (0 : Space)] with ξ hG hL hξ
      change φ ξ *
          (((‖ξ‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
            (BesselFractionalData.datum (1 / 2) (by norm_num)
              (A i : FourierData)) ξ) = φ ξ * L ξ
      rw [hG, hL]
      have hn : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
      simp only [BesselFractionalData.symbol]
      have hp : ‖ξ‖ ^ (-(1 / 2 : ℝ)) * ‖ξ‖ ^ (1 / 2 : ℝ) = 1 := by
        rw [← Real.rpow_add hn]
        norm_num
      have hpc : (((‖ξ‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          ((‖ξ‖ ^ (1 / 2 : ℝ) : ℝ) : ℂ)) = 1 := by
        exact_mod_cast hp
      rw [show (0 - (1 / 2) : ℝ) = -(1 / 2) by norm_num]
      calc
        _ = φ ξ *
            (((((‖ξ‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
              ((‖ξ‖ ^ (1 / 2 : ℝ) : ℝ) : ℂ)) *
                sobolevBesselWeight (-(1 / 2)) ξ) * (A i : FourierData) ξ) := by ring
        _ = _ := by rw [hpc]; ring
    have hLint : Integrable (fun ξ => φ ξ * L ξ) := by
      change Integrable ((φ : Space → ℂ) * (L : Space → ℂ))
      exact (φ.memLp 2 volume).integrable_mul (Lp.memLp L)
    refine ⟨hLint.congr hcancel.symm, ?_⟩
    have hweighted := weightedAngularFourier_realization
      (1 / 2) (A i : FourierData)
    have hang : angularFourierDistribution
        (angularRealization (1 / 2) (A i : FourierData)) =
          (L : TemperedDistribution Space ℂ) := by
      have h := congrArg (sobolevWeightMultiplier (-(1 / 2))) hweighted
      rw [sobolevWeightMultiplier_add,
        show (1 / 2 : ℝ) + -(1 / 2) = 0 by norm_num,
        sobolevWeightMultiplier_zero] at h
      calc
        _ = sobolevWeightMultiplier (-(1 / 2))
            ((A i : FourierData) : TemperedDistribution Space ℂ) := h
        _ = (L : TemperedDistribution Space ℂ) := by
          change sobolevWeightMultiplier (-(1 / 2))
              ((A i : FourierData) : TemperedDistribution Space ℂ) =
            ((sobolevOrderLowering (1 / 2) 0 (by norm_num)
              (A i : FourierData)) : TemperedDistribution Space ℂ)
          rw [sobolevOrderLowering_toDistribution]
          norm_num
    rw [hang, Lp.toTemperedDistribution_apply]
    exact integral_congr_ae hcancel.symm

/-- A05's homogeneous critical embedding, fed by a genuine inhomogeneous
half-order datum.  Only physical `L²` membership is needed: its three scalar
components provide the input to A05's scalar Riesz realization. -/
theorem inhomogeneousCriticalL3
    {z : NSFormalization.Section4.A02.SpatialField} (hz : MemLp z 2 volume)
    {A : RealVectorSobolev (1 / 2)} (hA : IsSobolevDatum (1 / 2) z A) :
    eLpNorm z 3 volume ≤
      ENNReal.ofReal NSFormalization.Section4.A05.criticalL3Const * ‖A‖ₑ := by
  let G := halfHomogeneousDatum A
  obtain ⟨U, hU, hGU⟩ := halfHomogeneousDatum_isDatum hA
  have hzcomp : ∀ i : Fin 3,
      MemLp (fun x => ((z x i : ℝ) : ℂ)) 2 volume := fun i =>
    (Complex.ofRealCLM.comp (EuclideanSpace.proj i)).comp_memLp' hz
  refine (NSFormalization.Section4.A05.u7_vector_eLpNorm_le_components hzcomp).trans
    ((Finset.sum_le_sum fun i _ =>
      NSFormalization.Section4.A05.u7_component_eLpNorm_le hzcomp hU hGU i).trans
      ((NSFormalization.Section4.A05.u7_component_sum_le G).trans ?_))
  exact mul_le_mul' le_rfl (by
    rw [← ofReal_norm, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (halfHomogeneousDatum_norm_le A))

/-! ## 2. A canonical physical representative of `Ju` -/

/-- The cycles-convention real component underlying an angular real datum. -/
def halfDatumCyclesComponent (A : RealVectorSobolev (1 / 2)) (i : Fin 3) :
    RealSobolevHilbert (1 / 2) :=
  (cyclesToAngularReal (1 / 2)).symm (A i)

/-- The physical complex `L²` component obtained by lowering to order zero
and applying the inverse Fourier transform. -/
def halfDatumPhysicalComponent (A : RealVectorSobolev (1 / 2)) (i : Fin 3) :
    FourierData :=
  NSFormalization.Source.FourierPhysicalJets.physicalLp (1 / 2) (by norm_num)
    (halfDatumCyclesComponent A i : FourierData)

/-- Reality of the datum makes its physical component real almost everywhere. -/
theorem halfDatumPhysicalComponent_real
    (A : RealVectorSobolev (1 / 2)) (i : Fin 3) :
    conjugation (halfDatumPhysicalComponent A i) =
      halfDatumPhysicalComponent A i := by
  change conjugation (FourierTransform.fourierInv
      (sobolevOrderLowering (1 / 2) 0 (by norm_num)
        (halfDatumCyclesComponent A i : FourierData))) =
    FourierTransform.fourierInv
      (sobolevOrderLowering (1 / 2) 0 (by norm_num)
        (halfDatumCyclesComponent A i : FourierData))
  apply (Lp.fourierTransformₗᵢ Space ℂ).injective
  change FourierTransform.fourier
      (conjugation (FourierTransform.fourierInv
        (sobolevOrderLowering (1 / 2) 0 (by norm_num)
          (halfDatumCyclesComponent A i : FourierData)))) =
    FourierTransform.fourier (FourierTransform.fourierInv
      (sobolevOrderLowering (1 / 2) 0 (by norm_num)
        (halfDatumCyclesComponent A i : FourierData)))
  rw [NSFormalization.Section4.D01.fourier_conjugation]
  rw [FourierInvPair.fourier_fourierInv_eq,
    NSFormalization.Section4.D01.realSymmetry_sobolevOrderLowering,
    (mem_realSubspace_iff (1 / 2) _).mp (halfDatumCyclesComponent A i).2]

/-- Assemble the three real parts of the physical scalar representatives. -/
def halfDatumPhysicalLp (A : RealVectorSobolev (1 / 2)) :
    Lp Space 2 (volume : Measure Space) :=
  NSFormalization.Source.FourierPhysicalJets.vectorLpReassembly
    (fun i => halfDatumPhysicalComponent A i)

/-- The literal measurable physical field selected by `halfDatumPhysicalLp`. -/
def halfDatumPhysicalField (A : RealVectorSobolev (1 / 2)) :
    NSFormalization.Section4.A02.SpatialField :=
  halfDatumPhysicalLp A

/-- The canonical physical representative is square-integrable. -/
theorem halfDatumPhysicalField_memLp (A : RealVectorSobolev (1 / 2)) :
    MemLp (halfDatumPhysicalField A) 2 volume :=
  Lp.memLp (halfDatumPhysicalLp A)

/-- The selected physical representative realizes the original half-order
angular datum. -/
theorem halfDatumPhysicalField_isDatum (A : RealVectorSobolev (1 / 2)) :
    IsSobolevDatum (1 / 2) (halfDatumPhysicalField A) A := by
  intro i ψ
  rw [show A i = cyclesToAngularReal (1 / 2)
      (halfDatumCyclesComponent A i) from
    ((cyclesToAngularReal (1 / 2)).apply_symm_apply (A i)).symm]
  rw [angularRealization_cyclesToAngularReal]
  rw [← NSFormalization.Source.FourierPhysicalJets.physicalLp_distribution
    (1 / 2) (by norm_num) (halfDatumCyclesComponent A i : FourierData),
    Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  have hreal := NSFormalization.Section4.D01.conjugation_ae
    (halfDatumPhysicalComponent A i)
  rw [halfDatumPhysicalComponent_real] at hreal
  filter_upwards [NSFormalization.Source.FourierPhysicalJets.vectorLpReassembly_ae
      (fun i => halfDatumPhysicalComponent A i), hreal] with x hvec hrealx
  change ψ x • halfDatumPhysicalComponent A i x =
    ψ x * (((halfDatumPhysicalLp A x i : ℝ) : ℂ))
  change ψ x • halfDatumPhysicalComponent A i x =
    ψ x * (((((NSFormalization.Source.FourierPhysicalJets.vectorLpReassembly
      (fun i => halfDatumPhysicalComponent A i)) x).ofLp i : ℝ)) : ℂ)
  rw [hvec]
  change ψ x * halfDatumPhysicalComponent A i x =
    ψ x * ((halfDatumPhysicalComponent A i x).re : ℂ)
  congr 1
  apply Complex.ext
  · simp
  · have him := congrArg Complex.im hrealx
    simp only [Complex.conj_im] at him
    simp only [Complex.ofReal_im]
    linarith

/-- Inhomogeneous fractional Parseval at the dual orders `-1/2` and `1/2`.

Both fields are only required to be square-integrable.  Their order-zero data
are lowered to the two dual orders; `real_inner_lowering_transfer` moves the
Bessel weights between the factors, and R43's componentwise real Plancherel
lemma identifies the remaining order-zero pairing with the physical integral. -/
theorem inhomogeneous_half_order_parseval
    {u v : NSFormalization.Section4.A02.SpatialField}
    (hu : MemLp u 2 volume) (hv : MemLp v 2 volume)
    {A : RealVectorSobolev (-1 / 2)} {B : RealVectorSobolev (1 / 2)}
    (hA : IsSobolevDatum (-1 / 2) u A)
    (hB : IsSobolevDatum (1 / 2) v B) :
    ⟪A, B⟫ = ∫ x : Space, inner ℝ (u x) (v x) := by
  let U₀ : RealVectorSobolev 0 := orderZeroDatum hu
  let V₀ : RealVectorSobolev 0 := orderZeroDatum hv
  have hA₀ : IsSobolevDatum 0 u U₀ := isSobolevDatum_orderZeroDatum hu
  have hV₀ : IsSobolevDatum 0 v V₀ := isSobolevDatum_orderZeroDatum hv
  have hAlow : IsSobolevDatum (-1 / 2) u
      (lowerVectorL 0 (-1 / 2) (by norm_num) U₀) :=
    NSFormalization.Section4.D01.Leray.isSobolevDatum_lower (by norm_num) hA₀
  have hBlow : IsSobolevDatum 0 v
      (lowerVectorL (1 / 2) 0 (by norm_num) B) :=
    NSFormalization.Section4.D01.Leray.isSobolevDatum_lower (by norm_num) hB
  have hAeq : lowerVectorL 0 (-1 / 2) (by norm_num) U₀ = A :=
    isSobolevDatum_unique hAlow hA
  have hBeq : lowerVectorL (1 / 2) 0 (by norm_num) B = V₀ :=
    isSobolevDatum_unique hBlow hV₀
  have hshift (i : Fin 3) :
      inner ℝ
          ((((lowerVectorL 0 (-1 / 2) (by norm_num) U₀) i :
            RealSobolevHilbert (-1 / 2)) : FourierData))
          ((B i : RealSobolevHilbert (1 / 2)) : FourierData) =
        inner ℝ ((U₀ i : RealSobolevHilbert 0) : FourierData)
          ((((lowerVectorL (1 / 2) 0 (by norm_num) B) i :
            RealSobolevHilbert 0) : FourierData)) := by
    rw [lowerVectorL_apply, lowerVectorL_apply,
      NSFormalization.Section4.A03.coe_lowerDatum,
      NSFormalization.Section4.A03.coe_lowerDatum]
    have ht := NSFormalization.Paper3.real_inner_lowering_transfer
      0 (1 / 2) (-1 / 2) (1 / 2) 0 0 (by norm_num)
      (by norm_num) (le_refl _) (le_refl _) (by norm_num)
      (U₀ i : FourierData) (B i : FourierData)
    simpa only [angularOrderLowering_self] using ht
  have hangularZero (g : FourierData) :
      cyclesToAngular 0 g = angularFrequencyDilation g := by
    have hw : angularWeightEquiv 0 g = g := by
      apply Lp.ext
      filter_upwards [angularWeightEquiv_coeFn 0 g] with ξ hξ
      rw [hξ]
      simp [angularWeightSymbol, sobolevBesselWeight]
    change angularFrequencyDilation (angularWeightEquiv 0 g) = _
    rw [hw]
  have hphysical (i : Fin 3) :
      inner ℝ ((U₀ i : RealSobolevHilbert 0) : FourierData)
        ((V₀ i : RealSobolevHilbert 0) : FourierData) =
          ∫ x : Space, u x i * v x i := by
    change inner ℝ ((orderZeroDatum hu i : RealSobolevHilbert 0) : FourierData)
        ((orderZeroDatum hv i : RealSobolevHilbert 0) : FourierData) = _
    rw [orderZeroDatum_coe, orderZeroDatum_coe, hangularZero, hangularZero,
      NSFormalization.Section4.R43.angular_real_parseval,
      NSFormalization.Section4.R43.component_real_pairing hu hv i]
  rw [← hAeq]
  change (∑ i : Fin 3, inner ℝ
      ((((lowerVectorL 0 (-1 / 2) (by norm_num) U₀) i :
        RealSobolevHilbert (-1 / 2)) : FourierData))
      ((B i : RealSobolevHilbert (1 / 2)) : FourierData)) = _
  simp_rw [hshift]
  rw [hBeq]
  simp_rw [hphysical]
  rw [← integral_finsetSum]
  · apply integral_congr_ae
    filter_upwards [] with x
    simp [PiLp.inner_apply, mul_comm]
  · intro i _
    exact ((EuclideanSpace.proj (𝕜 := ℝ) i).comp_memLp' hu).integrable_mul
      ((EuclideanSpace.proj (𝕜 := ℝ) i).comp_memLp' hv)

/-! ## 3. The advection datum and the physical Hölder step -/

/-- The physical nonlinear field `(u · ∇)u`, with the same spelling used by
the R43 trilinear estimate. -/
def advectionFieldJ (u : NSFormalization.Section4.A02.SpatialField) :
    NSFormalization.Section4.A02.SpatialField :=
  fun x => advection (NSFormalization.Section4.C01.lift u) 0 x

/-- The separate standard datum restriction needed for the nonlinear
`J`-pairing.  It records only `H^∞` regularity and the order `-1/2` datum of
`(u · ∇)u`.  The physical `Ju` field and exact Parseval identity are theorems
above, and no norm estimate is a field. -/
structure AdvectionJDatum {u f : Space → Space} (h : JWeightDatum u f) where
  velocity_memHInfty : MemHInfty u
  advectionNegHalf : RealVectorSobolev (-1 / 2)
  advectionNegHalf_isDatum :
    IsSobolevDatum (-1 / 2) (advectionFieldJ u) advectionNegHalf

/-- The real datum pairing representing `⟨(u · ∇)u, Ju⟩`. -/
def advectionJPairing {u f : Space → Space} (h : JWeightDatum u f)
    (ha : AdvectionJDatum h) : ℝ :=
  ⟪ha.advectionNegHalf, Jmul h.velocityThreeHalf⟫

/-- Three-factor Hölder for the physical `J` realization.  Compared with the
R43 theorem, the third factor needs only `L²` membership (hence strong
measurability), not a full `H^∞` package. -/
theorem advectionJHolder (u jVelocity : NSFormalization.Section4.A02.SpatialField)
    (hu : NSFormalization.Section4.A05.SmoothL2 u)
    (hj : MemLp jVelocity 2 volume) :
    ENNReal.ofReal
        |∫ x : Space, (inner ℝ (advectionFieldJ u x) (jVelocity x) : ℝ)| ≤
      eLpNorm u 3 volume *
        eLpNorm (NSFormalization.Section4.A05.gradTensor u) 3 volume *
          eLpNorm jVelocity 3 volume := by
  have hcg : Continuous (NSFormalization.Section4.A05.gradTensor u) := by
    show Continuous (fun x =>
      (WithLp.toLp 2
        (fun j : Fin 3 => NSFormalization.Section4.A05.dirDeriv j u x) :
          WithLp 2 (Fin 3 → Space)))
    exact Continuous.comp (PiLp.continuous_toLp 2 (fun _ : Fin 3 => Space))
      (continuous_pi fun j => (hu.dir j).contDiff.continuous)
  have hpoint : ∀ x : Space,
      ‖(inner ℝ (advectionFieldJ u x) (jVelocity x) : ℝ)‖ₑ ≤
        ‖u x‖ₑ *
          ‖NSFormalization.Section4.A05.gradTensor u x‖ₑ * ‖jVelocity x‖ₑ := by
    intro x
    have hinner :
        |(inner ℝ (advectionFieldJ u x) (jVelocity x) : ℝ)| ≤
          ‖advectionFieldJ u x‖ * ‖jVelocity x‖ :=
      abs_real_inner_le_norm _ _
    have hreal :
        |(inner ℝ (advectionFieldJ u x) (jVelocity x) : ℝ)| ≤
          ‖u x‖ * ‖NSFormalization.Section4.A05.gradTensor u x‖ *
            ‖jVelocity x‖ := by
      refine hinner.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
      exact NSFormalization.Section4.C01.advection_norm_le u x
    calc
      ‖(inner ℝ (advectionFieldJ u x) (jVelocity x) : ℝ)‖ₑ =
          ENNReal.ofReal |(inner ℝ
            (advectionFieldJ u x) (jVelocity x) : ℝ)| := Real.enorm_eq_ofReal_abs _
      _ ≤ ENNReal.ofReal
          (‖u x‖ * ‖NSFormalization.Section4.A05.gradTensor u x‖ *
            ‖jVelocity x‖) := ENNReal.ofReal_le_ofReal hreal
      _ = ‖u x‖ₑ * ‖NSFormalization.Section4.A05.gradTensor u x‖ₑ *
          ‖jVelocity x‖ₑ := by
        rw [ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm, ofReal_norm, ofReal_norm]
  rw [← Real.enorm_eq_ofReal_abs]
  calc
    ‖∫ x : Space, (inner ℝ
        (advectionFieldJ u x) (jVelocity x) : ℝ)‖ₑ ≤
        ∫⁻ x, ‖(inner ℝ
          (advectionFieldJ u x) (jVelocity x) : ℝ)‖ₑ ∂volume :=
      enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ x, ‖u x‖ₑ *
          ‖NSFormalization.Section4.A05.gradTensor u x‖ₑ *
            ‖jVelocity x‖ₑ ∂volume := lintegral_mono hpoint
    _ ≤ _ := NSFormalization.Section4.R43.lintegral_enorm_mul_three_le
      hu.contDiff.continuous.aestronglyMeasurable hcg.aestronglyMeasurable
      hj.aestronglyMeasurable

/-! ## 3. Assembly -/

/-- The explicit universal constant in the `J`-weighted trilinear estimate.
The factor three packages the three coordinate derivatives. -/
def trilinearConstJ : ℝ :=
  3 * NSFormalization.Section4.A05.criticalL3Const ^ 3

/-- The explicit `J`-trilinear constant is positive. -/
theorem trilinearConstJ_pos : 0 < trilinearConstJ := by
  exact mul_pos (by norm_num)
    (pow_pos NSFormalization.Section4.A05.criticalL3Const_pos 3)

/-- The paper's intermediate form
`|⟨(u·∇)u,Ju⟩| ≤ C Y Z sqrt(Y²+Z²)`. -/
theorem advection_pairing_le_sqrt {u f : Space → Space}
    (h : JWeightDatum u f) (ha : AdvectionJDatum h) :
    |advectionJPairing h ha| ≤
      trilinearConstJ * Y u * Z u * Real.sqrt (Y u ^ 2 + Z u ^ 2) := by
  let C : ℝ := NSFormalization.Section4.A05.criticalL3Const
  have hC : 0 < C := NSFormalization.Section4.A05.criticalL3Const_pos
  have hY : 0 ≤ Y u := ENNReal.toReal_nonneg
  have hZ : 0 ≤ Z u := ENNReal.toReal_nonneg
  have hsum : 0 ≤ Y u ^ 2 + Z u ^ 2 :=
    add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hsqrt : 0 ≤ Real.sqrt (Y u ^ 2 + Z u ^ 2) := Real.sqrt_nonneg _
  have huSmooth : NSFormalization.Section4.A05.SmoothL2 u :=
    NSFormalization.Section4.D01.memHInfty_iff_smoothSquareIntegrableJets.mp
      ha.velocity_memHInfty
  let jVelocity : NSFormalization.Section4.A02.SpatialField :=
    halfDatumPhysicalField (Jmul h.velocityThreeHalf)
  have hjVelocity_memLp : MemLp jVelocity 2 volume :=
    halfDatumPhysicalField_memLp _
  have hjVelocityHalf_isDatum :
      IsSobolevDatum (1 / 2) jVelocity (Jmul h.velocityThreeHalf) :=
    halfDatumPhysicalField_isDatum _
  have hadvection_memLp : MemLp (advectionFieldJ u) 2 volume := by
    change MemLp (NSFormalization.Section4.A03.advectionOf u u) 2 volume
    exact NSFormalization.Section4.A05.SmoothL2.memLp
      (NSFormalization.Section4.D01.advectionOf_smoothL2 huSmooth)
  have hvelocity : eLpNorm u 3 volume ≤
      ENNReal.ofReal C * ENNReal.ofReal (Y u) := by
    refine (inhomogeneousCriticalL3 huSmooth.memLp h.velocityHalf_isDatum).trans_eq ?_
    rw [← ofReal_norm, ← Y_eq_norm h]
  have hgradientStart :
      eLpNorm (NSFormalization.Section4.A05.gradTensor u) 3 volume ≤
        ∑ j : Fin 3,
          eLpNorm (NSFormalization.Section4.A05.dirDeriv j u) 3 volume :=
    NSFormalization.Section4.A05.eLpNorm_le_sum_of_norm_le (by norm_num)
      (fun j => (huSmooth.dir j).contDiff.continuous.aestronglyMeasurable)
      (fun x => NSFormalization.Section4.A05.norm_toLp_le_sum
        (fun j => NSFormalization.Section4.A05.dirDeriv j u x))
  have hcolumns : ∀ j : Fin 3,
      eLpNorm (NSFormalization.Section4.A05.dirDeriv j u) 3 volume ≤
        ENNReal.ofReal C * ‖h.gradientHalf j‖ₑ := by
    intro j
    apply inhomogeneousCriticalL3 (huSmooth.dir j).memLp
    rw [← NSFormalization.Section4.A03.partialDeriv_eq_dirDeriv]
    exact h.gradientHalf_isDatum j
  have hgradientDatum : ∀ j : Fin 3,
      ‖h.gradientHalf j‖ₑ ≤ ENNReal.ofReal (Z u) := by
    intro j
    rw [← ofReal_norm]
    apply ENNReal.ofReal_le_ofReal
    have hj : ‖h.gradientHalf j‖ ^ 2 ≤ Z u ^ 2 := by
      rw [Z_sq_eq_sum_norm h]
      exact Finset.single_le_sum
        (fun k (_hk : k ∈ Finset.univ) => sq_nonneg ‖h.gradientHalf k‖)
        (Finset.mem_univ j)
    nlinarith [norm_nonneg (h.gradientHalf j)]
  have hgradient :
      eLpNorm (NSFormalization.Section4.A05.gradTensor u) 3 volume ≤
        ENNReal.ofReal (3 * C) * ENNReal.ofReal (Z u) := by
    refine hgradientStart.trans ?_
    calc
      ∑ j : Fin 3, eLpNorm (NSFormalization.Section4.A05.dirDeriv j u) 3 volume ≤
          ∑ j : Fin 3, ENNReal.ofReal C * ‖h.gradientHalf j‖ₑ :=
        Finset.sum_le_sum fun j _ => hcolumns j
      _ ≤ ∑ _j : Fin 3, ENNReal.ofReal C * ENNReal.ofReal (Z u) :=
        Finset.sum_le_sum fun j _ => mul_le_mul' le_rfl (hgradientDatum j)
      _ = ENNReal.ofReal (3 * C) * ENNReal.ofReal (Z u) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
        norm_num
        ring
  have hthree : ‖h.velocityThreeHalf‖ =
      Real.sqrt (Y u ^ 2 + Z u ^ 2) := by
    calc
      ‖h.velocityThreeHalf‖ = Real.sqrt (‖h.velocityThreeHalf‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
      _ = Real.sqrt (Y u ^ 2 + Z u ^ 2) := by
        rw [← weight_identity h,
          sobolevENorm_eq_of_isSobolevDatum h.velocityThreeHalf_isDatum,
          toReal_enorm]
  have hjVelocity : eLpNorm jVelocity 3 volume ≤
      ENNReal.ofReal C * ENNReal.ofReal (Real.sqrt (Y u ^ 2 + Z u ^ 2)) := by
    calc
      eLpNorm jVelocity 3 volume ≤
          ENNReal.ofReal C * ‖Jmul h.velocityThreeHalf‖ₑ :=
        inhomogeneousCriticalL3 hjVelocity_memLp hjVelocityHalf_isDatum
      _ = ENNReal.ofReal C * ENNReal.ofReal ‖Jmul h.velocityThreeHalf‖ := by
        rw [ofReal_norm]
      _ = _ := by rw [Jmul_norm, hthree]
  have hholder := advectionJHolder u jVelocity huSmooth hjVelocity_memLp
  have hENN : ENNReal.ofReal |advectionJPairing h ha| ≤
      ENNReal.ofReal trilinearConstJ * ENNReal.ofReal (Y u) *
        ENNReal.ofReal (Z u) *
          ENNReal.ofReal (Real.sqrt (Y u ^ 2 + Z u ^ 2)) := by
    rw [advectionJPairing,
      inhomogeneous_half_order_parseval hadvection_memLp hjVelocity_memLp
        ha.advectionNegHalf_isDatum hjVelocityHalf_isDatum]
    refine hholder.trans ?_
    calc
      eLpNorm u 3 volume *
            eLpNorm (NSFormalization.Section4.A05.gradTensor u) 3 volume *
              eLpNorm jVelocity 3 volume ≤
          (ENNReal.ofReal C * ENNReal.ofReal (Y u)) *
            (ENNReal.ofReal (3 * C) * ENNReal.ofReal (Z u)) *
              (ENNReal.ofReal C *
                ENNReal.ofReal (Real.sqrt (Y u ^ 2 + Z u ^ 2))) := by gcongr
      _ = ENNReal.ofReal trilinearConstJ * ENNReal.ofReal (Y u) *
            ENNReal.ofReal (Z u) *
              ENNReal.ofReal (Real.sqrt (Y u ^ 2 + Z u ^ 2)) := by
        change _ = ENNReal.ofReal (3 * C ^ 3) * ENNReal.ofReal (Y u) *
          ENNReal.ofReal (Z u) *
            ENNReal.ofReal (Real.sqrt (Y u ^ 2 + Z u ^ 2))
        have h3C : ENNReal.ofReal (3 * C) =
            ENNReal.ofReal 3 * ENNReal.ofReal C := by
          rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
        have htri : ENNReal.ofReal (3 * C ^ 3) =
            ENNReal.ofReal 3 * ENNReal.ofReal C ^ 3 := by
          rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3),
            ENNReal.ofReal_pow]
          exact hC.le
        rw [h3C, htri]
        ring
  have htop : ENNReal.ofReal trilinearConstJ * ENNReal.ofReal (Y u) *
        ENNReal.ofReal (Z u) *
          ENNReal.ofReal (Real.sqrt (Y u ^ 2 + Z u ^ 2)) ≠ ⊤ := by
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
        ENNReal.ofReal_ne_top)
      ENNReal.ofReal_ne_top
  have hreal := ENNReal.toReal_mono htop hENN
  simpa only [ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal trilinearConstJ_pos.le,
    ENNReal.toReal_ofReal hY, ENNReal.toReal_ofReal hZ,
    ENNReal.toReal_ofReal hsqrt] using hreal

/-- **R44 S1c.** The `J`-weighted nonlinear pairing obeys
`|⟨(u·∇)u,Ju⟩| ≤ C₀ Y (Y²+Z²)`. -/
theorem advection_pairing_le {u f : Space → Space}
    (h : JWeightDatum u f) (ha : AdvectionJDatum h) :
    |advectionJPairing h ha| ≤
      trilinearConstJ * Y u * (Y u ^ 2 + Z u ^ 2) := by
  have hY : 0 ≤ Y u := ENNReal.toReal_nonneg
  have hZ : 0 ≤ Z u := ENNReal.toReal_nonneg
  have hsum : 0 ≤ Y u ^ 2 + Z u ^ 2 :=
    add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hsqrt : 0 ≤ Real.sqrt (Y u ^ 2 + Z u ^ 2) := Real.sqrt_nonneg _
  have hsqrtSq : Real.sqrt (Y u ^ 2 + Z u ^ 2) ^ 2 =
      Y u ^ 2 + Z u ^ 2 := Real.sq_sqrt hsum
  have hZsqrt : Z u ≤ Real.sqrt (Y u ^ 2 + Z u ^ 2) := by
    nlinarith
  refine (advection_pairing_le_sqrt h ha).trans ?_
  calc
    trilinearConstJ * Y u * Z u * Real.sqrt (Y u ^ 2 + Z u ^ 2) =
        (trilinearConstJ * Y u) *
          (Z u * Real.sqrt (Y u ^ 2 + Z u ^ 2)) := by ring
    _ ≤ (trilinearConstJ * Y u) *
        (Real.sqrt (Y u ^ 2 + Z u ^ 2) *
          Real.sqrt (Y u ^ 2 + Z u ^ 2)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hZsqrt hsqrt)
        (mul_nonneg trilinearConstJ_pos.le hY)
    _ = trilinearConstJ * Y u * (Y u ^ 2 + Z u ^ 2) := by
      rw [← pow_two, hsqrtSq]

end NSFormalization.Section4.R44
