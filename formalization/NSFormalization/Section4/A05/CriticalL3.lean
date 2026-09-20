import NSFormalization.Section4.D01.HomogeneousWitness
import NSFormalization.Section4.D01.DatumToJets
import NSFormalization.Section4.A02.SolutionClass
import NSFormalization.Section4.A03.ScalarTameProduct
import NSFormalization.Section4.A05.SmoothJets
import NSFormalization.Source.FractionalRealization
import NSFormalization.Source.RieszKernelNormalization

/-!
# The critical homogeneous `L³` embedding (A05, lane 165)

This module proves the carrier translation needed for
`04-whole-space.tex:105-112`: for every datum-form `H^∞` spatial field,
`‖z‖_{L³} ≤ C_{1/2} ‖z‖_{Ḣ^{1/2}}`.  The analytic input is the completed
Riesz-potential estimate in `Source.FractionalRealization`; the work here
transports an angular homogeneous datum to its cycles-frequency input, identifies
the resulting physical representative, and packages the three real components.

The implementation follows rows U1, U2, U3, U6, and U7 of
`research/A05/COMPARISON.md` §3.  Rows U4 (`IsRieszPower`) and U5
(`IsBesselPower`) concern additional operator relations from the full draft API;
they are not used by `velocityCriticalL3` and remain separate residuals recorded
in `research/A05/ATTEMPTS_CRITICAL_L3.md`.
-/

noncomputable section

namespace NSFormalization.Section4.A05

open Set MeasureTheory FourierTransform NavierStokes.ProblemStatement
open NSFormalization.Paper3
open NSFormalization.Source
open NSFormalization.Source.RealSobolev
open NSFormalization.RieszPotentialLp
open NSFormalization.RieszPotentialOperator
open NSFormalization.RieszSingularMultiplier
open NSFormalization.RieszL2Fourier
open NSFormalization.Section4.D01
open NSFormalization.Section4.D01.Homogeneous
open scoped ENNReal SchwartzMap

local notation "X" => EuclideanSpace ℝ (Fin 3)

/-- The datum-form homogeneous norm from `research/A05/COMPARISON.md` row U1.

This is copied locally from `research/R43/Spec.lean` and is to be replaced by
D01's canonical `dotHomogeneousENorm` when that definition lands.  In
particular, it is not the pointwise Fourier integral `Data.dotHHalfENorm`. -/
def dotHomogeneousENorm (s : ℝ) (z : Homogeneous.SpatialField) : ℝ≥0∞ :=
  ⨅ G : {G : RealVectorSobolev s // IsHomogeneousSliceDatum s z G}, ‖G.1‖ₑ

/-- Pull an angular homogeneous datum back to cycles frequency (row U2). -/
def cyclesHomogeneousDatum (G : FourierData) : FourierData :=
  angularFrequencyDilation.symm G

/-- The inverse angular-frequency dilation is isometric (row U2). -/
theorem cyclesHomogeneousDatum_norm (G : FourierData) :
    ‖cyclesHomogeneousDatum G‖ = ‖G‖ := by
  exact angularFrequencyDilation.symm.norm_map G

/-- Pointwise a.e. formula for the pulled-back datum (row U2). -/
theorem cyclesHomogeneousDatum_ae (G : FourierData) :
    (cyclesHomogeneousDatum G : X → ℂ) =ᵐ[volume]
      fun ξ => (frequencyUnit ^ (3 / 2 : ℝ)) • G (frequencyUnit • ξ) := by
  have h := angularFrequencyDilation_coeFn (angularFrequencyDilation.symm G)
  rw [LinearIsometryEquiv.apply_symm_apply] at h
  have hp := (Measure.quasiMeasurePreserving_smul (volume : Measure X)
    frequencyUnit_pos.ne').ae h
  filter_upwards [hp] with ξ hξ
  have hξ' : G (frequencyUnit • ξ) =
      frequencyUnit ^ (-3 / 2 : ℝ) • cyclesHomogeneousDatum G ξ := by
    simpa only [cyclesHomogeneousDatum, smul_smul,
      inv_mul_cancel₀ frequencyUnit_pos.ne', one_smul] using hξ
  have hc : frequencyUnit ^ (-3 / 2 : ℝ) * frequencyUnit ^ (3 / 2 : ℝ) = 1 := by
    rw [← Real.rpow_add frequencyUnit_pos]
    norm_num
  calc
    cyclesHomogeneousDatum G ξ =
        1 • cyclesHomogeneousDatum G ξ := by simp
    _ = (frequencyUnit ^ (3 / 2 : ℝ) * frequencyUnit ^ (-3 / 2 : ℝ)) •
        cyclesHomogeneousDatum G ξ := by rw [mul_comm, hc]; simp
    _ = frequencyUnit ^ (3 / 2 : ℝ) •
        (frequencyUnit ^ (-3 / 2 : ℝ) • cyclesHomogeneousDatum G ξ) := by
          rw [smul_smul]
    _ = _ := by rw [← hξ']

/-- **U2** (`research/A05/COMPARISON.md` §3, row U2): after inverse
angular-frequency dilation, the normalized cycles multiplier is exactly the
cycles Fourier transform represented by the angular homogeneous datum. -/
theorem u2_normalizedMultiplier_cyclesDatum {a : ℝ} (ha : 0 ≤ a) (ha3 : a < 3 / 2)
    {G : FourierData} {U : TemperedDistribution X ℂ}
    (hG : IsHomogeneousDatum a G U) :
    normalizedMultiplier a ha ha3 (cyclesHomogeneousDatum G) =
      FourierTransform.fourier U := by
  apply angularDistributionDilation_injective
  ext φ
  change angularDistributionDilation
      (normalizedMultiplier a ha ha3 (cyclesHomogeneousDatum G)) φ =
    angularFourierDistribution U φ
  rw [(hG φ).2, angularDistributionDilation_apply,
    normalizedMultiplier_pairing]
  rw [← integral_smul]
  have hint : Integrable (fun ξ : X =>
      φ ξ * ((((‖ξ‖ ^ (-a) : ℝ) : ℂ)) * G ξ)) := (hG φ).1
  have hscale :
      ∫ ξ : X, φ (frequencyUnit • ξ) *
          (((‖frequencyUnit • ξ‖ ^ (-a) : ℝ) : ℂ) * G (frequencyUnit • ξ)) =
        (frequencyUnit ^ (3 : ℕ))⁻¹ •
          ∫ ξ : X, φ ξ * (((‖ξ‖ ^ (-a) : ℝ) : ℂ) * G ξ) := by
    simpa only [show Module.finrank ℝ X = 3 by simp,
      abs_of_pos (inv_pos.mpr (pow_pos frequencyUnit_pos 3))] using
        (Measure.integral_comp_smul (volume : Measure X)
          (fun ξ : X => φ ξ * (((‖ξ‖ ^ (-a) : ℝ) : ℂ) * G ξ))
          frequencyUnit)
  calc
    ∫ ξ : X, frequencyUnit ^ (3 / 2 : ℝ) •
        (((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ angularFrequencyScale) φ) ξ *
          (((frequencyUnit ^ (-a) : ℝ) : ℂ) *
            NSFormalization.RieszFrequencyCutoffs.symbol a ξ * cyclesHomogeneousDatum G ξ)) =
      ∫ ξ : X, (frequencyUnit ^ (3 : ℕ) : ℝ) •
        (φ (frequencyUnit • ξ) *
          (((‖frequencyUnit • ξ‖ ^ (-a) : ℝ) : ℂ) * G (frequencyUnit • ξ))) := by
        apply integral_congr_ae
        filter_upwards [cyclesHomogeneousDatum_ae G] with ξ hξ
        rw [hξ]
        have hφ :
            ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ angularFrequencyScale) φ) ξ =
              φ (frequencyUnit • ξ) := rfl
        rw [hφ]
        simp only [NSFormalization.RieszFrequencyCutoffs.symbol, Complex.real_smul]
        have hn : ‖frequencyUnit • ξ‖ = frequencyUnit * ‖ξ‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos frequencyUnit_pos]
        rw [hn, Real.mul_rpow frequencyUnit_pos.le (norm_nonneg ξ)]
        have hc3 : frequencyUnit ^ (3 / 2 : ℝ) * frequencyUnit ^ (3 / 2 : ℝ) =
            frequencyUnit ^ (3 : ℕ) := by
          rw [← Real.rpow_add frequencyUnit_pos]
          norm_num
        have hc3c : (((frequencyUnit ^ (3 / 2 : ℝ) : ℝ) : ℂ) ^ 2) =
            ((frequencyUnit ^ (3 : ℕ) : ℝ) : ℂ) := by
          norm_cast
          simpa only [pow_two] using hc3
        push_cast
        ring_nf
        rw [hc3c]
        push_cast
        ring
    _ = (frequencyUnit ^ (3 : ℕ) : ℝ) •
        ∫ ξ : X, φ (frequencyUnit • ξ) *
          (((‖frequencyUnit • ξ‖ ^ (-a) : ℝ) : ℂ) * G (frequencyUnit • ξ)) := by
      rw [integral_smul]
    _ = _ := by
      rw [hscale, smul_smul]
      norm_num [frequencyUnit_pos.ne']

/-- **U1** (`research/A05/COMPARISON.md` §3, row U1): uniqueness of the
homogeneous slice datum makes the defining infimum attain the datum's norm. -/
theorem u1_dotHomogeneousENorm_eq {s : ℝ} {z : Homogeneous.SpatialField}
    {A : RealVectorSobolev s} (hA : IsHomogeneousSliceDatum s z A) :
    dotHomogeneousENorm s z = ‖A‖ₑ := by
  refine le_antisymm (iInf_le_of_le ⟨A, hA⟩ le_rfl) (le_iInf ?_)
  rintro ⟨B, hB⟩
  rw [isHomogeneousSliceDatum_unique hA hB]

/-- The explicit scalar constant furnished by the normalized Riesz-potential
route at order `a`. -/
def scalarCriticalConst (a : ℝ) : ℝ :=
  RieszKernelNormalization.coefficient a *
    (potentialConstant a * (512 : ℝ) ^ (1 / targetExponent a))

/-- Positivity of the scalar Riesz-potential constant in its admissible range. -/
theorem scalarCriticalConst_pos {a : ℝ} (ha : 0 < a) (ha3 : a < 3 / 2) :
    0 < scalarCriticalConst a := by
  unfold scalarCriticalConst
  exact mul_pos (RieszKernelNormalization.coefficient_pos ha (by linarith))
    (mul_pos (by unfold potentialConstant; positivity) (by positivity))

/-- Physical `L²` input whose cycles Fourier transform is the pulled-back
angular homogeneous datum (row U3 carrier support). -/
def criticalInputFromDatum (G : FourierData) : Lp ℂ 2 (volume : Measure X) :=
  FourierTransform.fourierInv (cyclesHomogeneousDatum G)

/-- **U3 support** (`research/A05/COMPARISON.md` §3, row U3): the cycles
Fourier transform of the physical input is the pulled-back angular datum. -/
theorem u3_fourier_criticalInputFromDatum (G : FourierData) :
    FourierTransform.fourier (criticalInputFromDatum G) = cyclesHomogeneousDatum G := by
  exact FourierInvPair.fourier_fourierInv_eq _

/-- **U3 support** (`research/A05/COMPARISON.md` §3, row U3): Plancherel and
the frequency dilation preserve the datum norm.  The full row-U3
`homogeneousLeSobolev` constructor remains outside this lane. -/
theorem u3_norm_criticalInputFromDatum (G : FourierData) :
    ‖criticalInputFromDatum G‖ = ‖G‖ := by
  rw [← Lp.norm_fourier_eq (criticalInputFromDatum G),
    u3_fourier_criticalInputFromDatum, cyclesHomogeneousDatum_norm]

/-- The normalized potential representative attached to one angular
homogeneous datum. -/
def normalizedCriticalRealization {a : ℝ} (ha : 0 < a) (ha3 : a < 3 / 2)
    (G : FourierData) :
    letI : Fact (1 ≤ ENNReal.ofReal (targetExponent a)) :=
      ⟨targetExponent_one_le ha ha3⟩
    Lp ℂ (ENNReal.ofReal (targetExponent a)) (volume : Measure X) := by
  let : Fact (1 ≤ ENNReal.ofReal (targetExponent a)) :=
    ⟨targetExponent_one_le ha ha3⟩
  exact (RieszKernelNormalization.coefficient a : ℂ) •
    potentialOperator ha ha3 (criticalInputFromDatum G)

/-- **U6** (`research/A05/COMPARISON.md` §3, row U6): the completed normalized
potential representative obeys the scalar real-norm estimate. -/
theorem u6_normalizedCriticalRealization_norm_le {a : ℝ}
    (ha : 0 < a) (ha3 : a < 3 / 2) (G : FourierData) :
    letI : Fact (1 ≤ ENNReal.ofReal (targetExponent a)) :=
      ⟨targetExponent_one_le ha ha3⟩
    ‖normalizedCriticalRealization ha ha3 G‖ ≤ scalarCriticalConst a * ‖G‖ := by
  let : Fact (1 ≤ ENNReal.ofReal (targetExponent a)) :=
    ⟨targetExponent_one_le ha ha3⟩
  rw [normalizedCriticalRealization, norm_smul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (RieszKernelNormalization.coefficient_pos ha (by linarith))]
  exact (mul_le_mul_of_nonneg_left
    (potentialOperator_norm_le ha ha3 (criticalInputFromDatum G))
    (RieszKernelNormalization.coefficient_pos ha (by linarith)).le).trans_eq (by
      rw [u3_norm_criticalInputFromDatum]
      simp only [scalarCriticalConst]
      ring)

/-- **U6** (`research/A05/COMPARISON.md` §3, row U6): the completed potential
representative is the original tempered distribution. -/
theorem u6_normalizedCriticalRealization_toDistribution {a : ℝ}
    (ha : 0 < a) (ha3 : a < 3 / 2) {G : FourierData}
    {U : TemperedDistribution X ℂ} (hG : IsHomogeneousDatum a G U) :
    letI : Fact (1 ≤ ENNReal.ofReal (targetExponent a)) :=
      ⟨targetExponent_one_le ha ha3⟩
    (normalizedCriticalRealization ha ha3 G : TemperedDistribution X ℂ) = U := by
  let : Fact (1 ≤ ENNReal.ofReal (targetExponent a)) :=
    ⟨targetExponent_one_le ha ha3⟩
  apply (fourierEquiv ℂ (TemperedDistribution X ℂ)).injective
  change FourierTransform.fourier
      (Lp.toTemperedDistribution (normalizedCriticalRealization ha ha3 G)) =
    FourierTransform.fourier U
  change FourierTransform.fourier
      (Lp.toTemperedDistribution
        ((RieszKernelNormalization.coefficient a : ℂ) •
          potentialOperator ha ha3 (criticalInputFromDatum G))) =
    FourierTransform.fourier U
  rw [show Lp.toTemperedDistribution
      ((RieszKernelNormalization.coefficient a : ℂ) •
        potentialOperator ha ha3 (criticalInputFromDatum G)) =
      (RieszKernelNormalization.coefficient a : ℂ) •
        (Lp.toTemperedDistribution
          (potentialOperator ha ha3 (criticalInputFromDatum G))) by
        exact (Lp.toTemperedDistributionCLM ℂ volume
          (ENNReal.ofReal (targetExponent a))).map_smul _ _,
    fourier_smul]
  change (RieszKernelNormalization.coefficient a : ℂ) •
      physicalFourier ha ha3 (criticalInputFromDatum G) = FourierTransform.fourier U
  rw [normalized_commuting_square, u3_fourier_criticalInputFromDatum,
    u2_normalizedMultiplier_cyclesDatum ha.le ha3 hG]

/-- **U6** (`research/A05/COMPARISON.md` §3, row U6): scalar critical embedding
for a physical `L²` representative of an angular homogeneous datum. -/
theorem u6_scalar_eLpNorm_le {a : ℝ} (ha : 0 < a) (ha3 : a < 3 / 2)
    {f : X → ℂ} (hf : MemLp f 2 volume) {G : FourierData}
    {U : TemperedDistribution X ℂ}
    (hU : ∀ ψ : SchwartzMap X ℂ, U ψ = ∫ x : X, ψ x * f x)
    (hG : IsHomogeneousDatum a G U) :
    eLpNorm f (ENNReal.ofReal (targetExponent a)) volume ≤
      ENNReal.ofReal (scalarCriticalConst a) * ‖G‖ₑ := by
  let : Fact (1 ≤ ENNReal.ofReal (targetExponent a)) :=
    ⟨targetExponent_one_le ha ha3⟩
  let R := normalizedCriticalRealization ha ha3 G
  have hRdist : (R : TemperedDistribution X ℂ) = U :=
    u6_normalizedCriticalRealization_toDistribution ha ha3 hG
  have hRloc : LocallyIntegrable (R : X → ℂ) volume :=
    (Lp.memLp R).locallyIntegrable (targetExponent_one_le ha ha3)
  have hfloc : LocallyIntegrable f volume := hf.locallyIntegrable (by norm_num)
  have hpair : ∀ ψ : SchwartzMap X ℂ,
      (∫ x : X, ψ x * R x) = ∫ x : X, ψ x * f x := by
    intro ψ
    have h := congrArg (fun T : TemperedDistribution X ℂ => T ψ) hRdist
    rw [Lp.toTemperedDistribution_apply, hU ψ] at h
    rw [← h]
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [smul_eq_mul]
  have hae : (R : X → ℂ) =ᵐ[volume] f :=
    NSFormalization.Section4.A03.ae_eq_of_schwartz_pairing hRloc hfloc hpair
  rw [← eLpNorm_congr_ae hae]
  rw [← Lp.enorm_def R]
  change ‖R‖ₑ ≤ ENNReal.ofReal (scalarCriticalConst a) * ‖G‖ₑ
  rw [← ofReal_norm, ← ofReal_norm,
    ← ENNReal.ofReal_mul (scalarCriticalConst_pos ha ha3).le]
  exact ENNReal.ofReal_le_ofReal (u6_normalizedCriticalRealization_norm_le ha ha3 G)

/-- **U7** (`research/A05/COMPARISON.md` §3, row U7): the critical exponent at
order one half is exactly three. -/
theorem u7_targetExponent_half :
    ENNReal.ofReal (targetExponent (1 / 2 : ℝ)) = 3 := by
  norm_num [targetExponent]

/-- The explicit vector constant.  The factor `3` is the finite-dimensional
`l² ≤ l¹` packaging of the three real components. -/
def criticalL3Const : ℝ := 3 * scalarCriticalConst (1 / 2)

/-- Positivity of the explicit three-component constant. -/
theorem criticalL3Const_pos : 0 < criticalL3Const := by
  exact mul_pos (by norm_num) (scalarCriticalConst_pos (by norm_num) (by norm_num))

/-- **U7** (`research/A05/COMPARISON.md` §3, row U7): Euclidean norm is bounded
by the sum of the absolute values of the three complexified coordinates. -/
theorem u7_norm_le_sum_coordinates (x : X) :
    ‖x‖ ≤ ∑ i : Fin 3, ‖((x i : ℝ) : ℂ)‖ := by
  rw [PiLp.norm_eq_of_L2]
  have h : ∑ i : Fin 3, ‖x i‖ ^ 2 ≤ (∑ i : Fin 3, ‖x i‖) ^ 2 :=
    Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => norm_nonneg (x i))
  calc
    Real.sqrt (∑ i : Fin 3, ‖x i‖ ^ 2) ≤
        Real.sqrt ((∑ i : Fin 3, ‖x i‖) ^ 2) := Real.sqrt_le_sqrt h
    _ = ∑ i : Fin 3, ‖x i‖ :=
      Real.sqrt_sq (Finset.sum_nonneg fun i _ => norm_nonneg _)
    _ = ∑ i : Fin 3, ‖((x i : ℝ) : ℂ)‖ := by simp

/-- **U7** (`research/A05/COMPARISON.md` §3, row U7): datum-form `H^∞` supplies
physical `L²` membership for each complexified coordinate. -/
theorem u7_memLp_components_of_memHInfty {z : Homogeneous.SpatialField}
    (hz : NSFormalization.Section4.A02.MemHInfty z) :
    ∀ i : Fin 3, MemLp (fun x : X => ((z x i : ℝ) : ℂ)) 2 volume := by
  have hzL2 : MemLp z 2 volume :=
    ((memHInfty_jets hz.1 hz.2) 0).congr_norm hz.1.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall fun _ => norm_iteratedFDeriv_zero)
  exact fun i => (Complex.ofRealCLM.comp (EuclideanSpace.proj i)).comp_memLp' hzL2

/-- **U7** (`research/A05/COMPARISON.md` §3, row U7): apply the scalar U6
estimate to one component of a real-vector homogeneous datum. -/
theorem u7_component_eLpNorm_le {z : Homogeneous.SpatialField}
    {U : Homogeneous.VectorDistribution} {G : RealVectorSobolev (1 / 2 : ℝ)}
    (hzcomp : ∀ i : Fin 3, MemLp (fun x : X => ((z x i : ℝ) : ℂ)) 2 volume)
    (hU : IsSliceDistribution z U)
    (hGU : IsHomogeneousVectorDatum (1 / 2 : ℝ) U G) (i : Fin 3) :
    eLpNorm (fun x : X => ((z x i : ℝ) : ℂ)) 3 volume ≤
      ENNReal.ofReal (scalarCriticalConst (1 / 2)) * ‖G i‖ₑ := by
  have hi := u6_scalar_eLpNorm_le (a := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
    (hzcomp i) (hU i) (hGU i)
  rwa [u7_targetExponent_half] at hi

/-- **U7** (`research/A05/COMPARISON.md` §3, row U7): pointwise coordinate
control gives the corresponding `L³` seminorm inequality. -/
theorem u7_vector_eLpNorm_le_components {z : Homogeneous.SpatialField}
    (hzcomp : ∀ i : Fin 3, MemLp (fun x : X => ((z x i : ℝ) : ℂ)) 2 volume) :
    eLpNorm z 3 volume ≤
      ∑ i : Fin 3, eLpNorm (fun x : X => ((z x i : ℝ) : ℂ)) 3 volume :=
  eLpNorm_le_sum_of_norm_le (f := z)
    (g := fun i x => ((z x i : ℝ) : ℂ)) (by norm_num)
    (fun i => (hzcomp i).aestronglyMeasurable) (fun x => u7_norm_le_sum_coordinates (z x))

/-- **U7** (`research/A05/COMPARISON.md` §3, row U7): three coordinate datum
norms are controlled by three times the real-vector datum norm. -/
theorem u7_component_sum_le (G : RealVectorSobolev (1 / 2 : ℝ)) :
    ∑ i : Fin 3, ENNReal.ofReal (scalarCriticalConst (1 / 2)) * ‖G i‖ₑ ≤
      ENNReal.ofReal criticalL3Const * ‖G‖ₑ := by
  have hcomponent_enorm : ∀ i : Fin 3, ‖G i‖ₑ ≤ ‖G‖ₑ := by
    intro i
    rw [← ofReal_norm, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (PiLp.norm_apply_le G i)
  calc
    ∑ i : Fin 3, ENNReal.ofReal (scalarCriticalConst (1 / 2)) * ‖G i‖ₑ ≤
        ∑ _i : Fin 3,
        ENNReal.ofReal (scalarCriticalConst (1 / 2)) * ‖G‖ₑ :=
      Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (hcomponent_enorm i) bot_le
    _ = ENNReal.ofReal criticalL3Const * ‖G‖ₑ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      simp only [criticalL3Const]
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
      norm_num
      ring

/-- **U7** (`research/A05/COMPARISON.md` §3, row U7): vector critical `L³`
embedding when a particular order-half homogeneous datum is supplied. -/
theorem u7_vector_eLpNorm_le_of_datum {z : Homogeneous.SpatialField}
    (hz : NSFormalization.Section4.A02.MemHInfty z)
    {G : RealVectorSobolev (1 / 2 : ℝ)}
    (hG : IsHomogeneousSliceDatum (1 / 2 : ℝ) z G) :
    eLpNorm z 3 volume ≤ ENNReal.ofReal criticalL3Const * ‖G‖ₑ := by
  obtain ⟨U, hU, hGU⟩ := hG
  have hzcomp := u7_memLp_components_of_memHInfty hz
  exact (u7_vector_eLpNorm_le_components hzcomp).trans
    ((Finset.sum_le_sum fun i _ => u7_component_eLpNorm_le hzcomp hU hGU i).trans
      (u7_component_sum_le G))

/-- `research/A05/Spec.lean:366` (`velocityCriticalL3`), completing row U7:
every datum-form `H^∞` spatial field satisfies the critical embedding with the
explicit universal constant `criticalL3Const`.  If no order-half datum exists,
the datum-form norm is `⊤`, so the totalized statement remains fail-safe. -/
theorem velocityCriticalL3 (z : NSFormalization.Section4.A02.SpatialField)
    (hz : NSFormalization.Section4.A02.MemHInfty z) :
    eLpNorm z 3 volume ≤
      ENNReal.ofReal criticalL3Const * dotHomogeneousENorm (1 / 2) z := by
  by_cases hex : ∃ G : RealVectorSobolev (1 / 2 : ℝ),
      IsHomogeneousSliceDatum (1 / 2 : ℝ) z G
  · obtain ⟨G, hG⟩ := hex
    rw [u1_dotHomogeneousENorm_eq hG]
    exact u7_vector_eLpNorm_le_of_datum hz hG
  · have : IsEmpty {G : RealVectorSobolev (1 / 2 : ℝ) //
        IsHomogeneousSliceDatum (1 / 2 : ℝ) z G} :=
      ⟨fun G => hex ⟨G.1, G.2⟩⟩
    rw [dotHomogeneousENorm, iInf_of_isEmpty, sInf_empty]
    rw [ENNReal.mul_top]
    left
    exact ne_of_gt (ENNReal.ofReal_pos.mpr criticalL3Const_pos)

end NSFormalization.Section4.A05
