import NSFormalization.Section3.T11.PhysicalRecovery
import Mathlib.Analysis.Calculus.SmoothSeries

/-! # All-order coefficients in physical recovery

The persistence premise identifies **unweighted** coefficients. The Sobolev
order is phantom in the carrier, so equality of weighted carriers is not an
acceptable substitute. This module is a partial U9d2 delivery; it does not
assert the general classical existence target.
-/
noncomputable section
namespace NSFormalization.Section3.T11
open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField)
open NavierStokes.PeriodicIntegration (spatialPartial)
open NSFormalization.Section3.T10
open scoped BigOperators ContDiff ComplexConjugate NNReal

local instance assemblyNormedGroup (s : ℝ) : NormedAddCommGroup (PeriodicSobolev s) :=
  realPeriodicSubmodule.normedAddCommGroup
local instance assemblyNormedSpace (s : ℝ) : NormedSpace ℝ (PeriodicSobolev s) :=
  realPeriodicSubmodule.normedSpace

/-- U9d1's conclusion on the original horizon, with equality of physical coefficients. -/
def PersistenceInput (T : ℝ) (u : ℝ → PeriodicSobolev 3) : Prop :=
  ∀ m : ℕ, ∃ u_m : ℝ → PeriodicSobolev (m : ℝ),
    ContinuousOn u_m (Ico 0 T) ∧
      ∀ t ∈ Ico 0 T, ∀ i k,
        torusPhysicalCoeff (m : ℝ) (u_m t) i k = torusPhysicalCoeff 3 (u t) i k

/-- Equality of physical coefficients is precisely the canonical change of order. -/
theorem physicalCoeff_eq_iff_reweight {s r : ℝ}
    (A : PeriodicSobolev s) (B : PeriodicSobolev r) :
    (∀ i k, torusPhysicalCoeff r B i k = torusPhysicalCoeff s A i k) ↔
      IsPeriodicReweight s r A B := by
  have hw (k : PeriodicFrequency) : 0 < periodicFrequencyWeight k := by
    unfold periodicFrequencyWeight; positivity
  constructor
  · intro h i k
    have he := congrArg (fun z : ℂ ↦ (periodicFrequencyWeight k ^ (r/2) : ℝ) * z)
      (h i k)
    simp only [torusPhysicalCoeff, ← mul_assoc, ← Complex.ofReal_mul] at he
    rw [← Real.rpow_add (hw k), ← Real.rpow_add (hw k)] at he
    simpa only [show r/2 + -r/2 = 0 by ring, Real.rpow_zero, Complex.ofReal_one,
      one_mul, show r/2 + -s/2 = (r-s)/2 by ring, Complex.real_smul] using he
  · intro h i k
    rw [torusPhysicalCoeff, h i k]
    simp only [Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul]
    rw [← Real.rpow_add (hw k), show -r/2 + (r-s)/2 = -s/2 by ring]
    rfl

/-- This is exactly the `sobolev` field for the recovered physical velocity. -/
theorem persistence_physical_sobolev {T : ℝ} {u : ℝ → PeriodicSobolev 3}
    (h : PersistenceInput T u) :
    ∀ m : ℕ, ∃ G : ℝ → PeriodicSobolev (m : ℝ),
      ContinuousOn G (Ico (0 : ℝ) T) ∧
        ∀ t ∈ Ico (0 : ℝ) T,
          IsPeriodicDatum (m : ℝ) (fun x ↦ torusPhysicalVelocity u (t, x)) (G t) := by
  intro m
  obtain ⟨G, hG, hc⟩ := h m
  exact ⟨G, hG, torusPhysicalVelocity_reweight
    (fun t ht ↦ (physicalCoeff_eq_iff_reweight _ _).mp (hc t ht))⟩

/-- Polynomially weighted absolute summability follows from the actual order `2*N+3`. -/
theorem persistence_weighted_summable {T : ℝ} {u : ℝ → PeriodicSobolev 3}
    (h : PersistenceInput T u) {t : ℝ} (ht : t ∈ Ico 0 T) (N : ℕ) (i : Fin 3) :
    Summable (fun k ↦ periodicFrequencyWeight k ^ N * ‖torusPhysicalCoeff 3 (u t) i k‖) := by
  obtain ⟨G, _, hc⟩ := h (2*N+3)
  have he (k : PeriodicFrequency) :
      torusPhysicalCoeff 3 (G t) i k =
        (periodicFrequencyWeight k ^ N : ℝ) * torusPhysicalCoeff 3 (u t) i k := by
    rw [← hc t ht i k]
    unfold torusPhysicalCoeff
    rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.rpow_natCast,
      ← Real.rpow_add (by unfold periodicFrequencyWeight; positivity)]
    congr 2
    congr 1
    push_cast
    ring
  have hs := torusPhysicalCoeff_summable (G t) i
  have hp (k : PeriodicFrequency) : 0 ≤ periodicFrequencyWeight k ^ N := by
    unfold periodicFrequencyWeight; positivity
  simpa only [he, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (hp _)] using hs

/-- Persistence is inhabited on a nonstationary trajectory driven by nonzero constant force. -/
theorem persistence_affine_constant (T : ℝ) (c : Space) :
    PersistenceInput T (fun t ↦ (1+t) • torusConstantDatum 3 c) := by
  intro m
  refine ⟨fun t ↦ (1+t) • torusConstantDatum (m : ℝ) c,
    (continuous_const.add continuous_id |>.smul continuous_const).continuousOn, ?_⟩
  intro t _ i k
  rw [torusPhysicalCoeff_eq (torusConstantDatum_smul (m : ℝ) (1+t) c),
    torusPhysicalCoeff_eq (torusConstantDatum_smul 3 (1+t) c)]

-- Multilinear operator norm elaboration needs the larger local budget.
set_option maxHeartbeats 400000 in
/-- Uniform derivative bounds for a Fourier character at every order. -/
theorem assembly_character_derivative_bound (k : PeriodicFrequency) (n : ℕ) (x : Space) :
    ‖iteratedFDeriv ℝ n (NSFormalization.Paper1.periodicCharacter k) x‖ ≤
      ‖NSFormalization.Paper1.periodicPhase k‖ ^ n := by
  induction n with
  | zero => simp [norm_iteratedFDeriv_zero, torusCharacter_norm]
  | succ n ih =>
    rw [← norm_iteratedFDeriv_fderiv]
    have he : fderiv ℝ (NSFormalization.Paper1.periodicCharacter k) =
        fun y ↦ NSFormalization.Paper1.periodicCharacter k y •
          NSFormalization.Paper1.periodicPhase k := by
      funext y
      exact (NSFormalization.Paper1.periodicPhase k).hasFDerivAt.cexp.fderiv
    rw [he, iteratedFDeriv_smul_const_apply
      ((NSFormalization.Paper1.periodicCharacter_smooth k).of_le (by simp)).contDiffAt]
    refine (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans ?_
    have hL : ‖(ContinuousLinearMap.id ℝ ℂ).smulRight
        (NSFormalization.Paper1.periodicPhase k)‖ ≤ ‖NSFormalization.Paper1.periodicPhase k‖ := by
      apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
      intro z
      change ‖z • NSFormalization.Paper1.periodicPhase k‖ ≤ _
      rw [norm_smul, mul_comm]
    refine (mul_le_mul_of_nonneg_right hL (norm_nonneg _)).trans ?_
    simpa only [pow_succ, mul_comm] using mul_le_mul_of_nonneg_left ih
      (norm_nonneg (NSFormalization.Paper1.periodicPhase k))

-- The Euclidean operator norm and finite frequency sum expand during elaboration.
set_option maxHeartbeats 400000 in
/-- A coarse polynomial bound suffices for all-order Fourier inversion. -/
theorem assembly_phase_norm_le (k : PeriodicFrequency) :
    ‖NSFormalization.Paper1.periodicPhase k‖ ≤ 3 * periodicFrequencyWeight k := by
  have hW : 1 ≤ periodicFrequencyWeight k := by
    rw [periodicFrequencyWeight_eq_paper1]
    exact NSFormalization.Paper1.one_le_periodicFrequencyWeight k
  have hc (i : Fin 3) : ‖(2 * Real.pi * Complex.I : ℂ) * (k i : ℂ)‖ ≤
      periodicFrequencyWeight k := by
    have hs := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 3))) ↦
      sq_nonneg ‖(2 * Real.pi * Complex.I : ℂ) * (k j : ℂ)‖) (Finset.mem_univ i)
    have he := periodicFrequencyWeight_eq_paper1 k
    unfold NSFormalization.Paper1.periodicFrequencyWeight at he
    nlinarith only [hs, he, hW, sq_nonneg (‖(2 * Real.pi * Complex.I : ℂ) * (k i : ℂ)‖ - 1)]
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  rw [NSFormalization.Paper1.periodicPhase_apply, Finset.mul_sum]
  calc
    _ ≤ ∑ i : Fin 3, ‖(2 * Real.pi * Complex.I : ℂ) * ((k i : ℂ) * (x i : ℂ))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _i : Fin 3, periodicFrequencyWeight k * ‖x‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [← mul_assoc, norm_mul, Complex.norm_real]
      exact mul_le_mul (hc i) (PiLp.norm_apply_le x i) (norm_nonneg _) (by positivity)
    _ = _ := by simp; ring

/-- Every spatial slice of a persistent coefficient path is smooth. -/
theorem persistence_physical_spatial_smooth {T : ℝ} {u : ℝ → PeriodicSobolev 3}
    (h : PersistenceInput T u) {t : ℝ} (ht : t ∈ Ico 0 T) :
    ContDiff ℝ ∞ (fun x ↦ torusPhysicalVelocity u (t, x)) := by
  apply (PiLp.contDiff_toLp (p := 2)).comp
  apply contDiff_pi.mpr
  intro i
  apply Complex.reCLM.contDiff.comp
  change ContDiff ℝ ∞ (fun x ↦ ∑' k, torusPhysicalCoeff 3 (u t) i k *
    NSFormalization.Paper1.periodicCharacter k x)
  apply contDiff_tsum (v := fun n k ↦ 3^n *
    (periodicFrequencyWeight k ^ n * ‖torusPhysicalCoeff 3 (u t) i k‖))
  · intro k
    exact contDiff_const.mul (NSFormalization.Paper1.periodicCharacter_smooth k)
  · intro n _
    exact (persistence_weighted_summable h ht n i).mul_left _
  · intro n k x _
    have he : (fun y ↦ torusPhysicalCoeff 3 (u t) i k *
        NSFormalization.Paper1.periodicCharacter k y) =
        torusPhysicalCoeff 3 (u t) i k • NSFormalization.Paper1.periodicCharacter k := rfl
    rw [he, iteratedFDeriv_const_smul_apply
      ((NSFormalization.Paper1.periodicCharacter_smooth k).of_le (by simp)).contDiffAt,
      norm_smul]
    calc
      _ ≤ ‖torusPhysicalCoeff 3 (u t) i k‖ * ‖NSFormalization.Paper1.periodicPhase k‖ ^ n :=
        mul_le_mul_of_nonneg_left (assembly_character_derivative_bound k n x) (norm_nonneg _)
      _ ≤ ‖torusPhysicalCoeff 3 (u t) i k‖ * (3 * periodicFrequencyWeight k) ^ n :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (assembly_phase_norm_le k) n)
          (norm_nonneg _)
      _ = _ := by rw [mul_pow]; ring

/-- The divergence of the complexified velocity is the complexified physical trace. -/
theorem assembly_complex_divergence {a : SpatialField} (ha : ContDiff ℝ ∞ a) (x : Space) :
    (∑ j : Fin 3, spatialPartial j (fun y ↦ (a y j : ℂ)) x) =
      (spatialDivergence (fun z ↦ a z.2) 0 x : ℂ) := by
  rw [spatialDivergence, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro j _
  let L : Space →L[ℝ] ℂ := Complex.ofRealCLM.comp (EuclideanSpace.proj j)
  change fderiv ℝ (L ∘ a) x (coordinateVector j) = _
  rw [(L.hasFDerivAt.comp x (ha.differentiable (by simp) x).hasFDerivAt).fderiv]
  rfl

/-- Fourier divergence identity in the weighted datum convention. -/
theorem assembly_fourier_divergence {s : ℝ} {a : SpatialField}
    {A : PeriodicSobolev s} (ha : ContDiff ℝ ∞ a) (hA : IsPeriodicDatum s a A)
    (k : PeriodicFrequency) :
    periodicFourierCoeff (fun x ↦ ∑ j : Fin 3,
      spatialPartial j (fun y ↦ (a y j : ℂ)) x) k =
        (periodicFrequencyWeight k ^ (-s/2) : ℝ) *
          ∑ j : Fin 3, periodicDerivativeSymbol j k * A.1 j k := by
  have hj (j : Fin 3) : ContDiff ℝ ∞ (fun y ↦ (a y j : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp ((EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.comp ha)
  have hd (j : Fin 3) : Continuous (spatialPartial j (fun y ↦ (a y j : ℂ))) := by
    have hds : ContDiff ℝ ∞ (spatialPartial j (fun y ↦ (a y j : ℂ))) :=
      ((hj j).fderiv_right (by simp)).clm_apply contDiff_const
    exact hds.continuous
  have he : periodicFourierCoeff (fun x ↦ ∑ j : Fin 3,
      spatialPartial j (fun y ↦ (a y j : ℂ)) x) k =
        ∑ j : Fin 3, periodicFourierCoeff (spatialPartial j (fun y ↦ (a y j : ℂ))) k := by
    simp only [periodicFourierCoeff, NSFormalization.Paper1.periodicFourierCoeff_eq_cube,
      Finset.mul_sum, NavierStokes.PeriodicIntegration.cubeIntegral]
    apply integral_finsetSum
    intro j _
    exact NavierStokes.PeriodicIntegration.integrable_cube
      ((NSFormalization.Paper1.periodicCharacter_smooth (-k)).continuous.mul (hd j))
  rw [he, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  calc
    _ = periodicDerivativeSymbol j k * periodicFourierCoeff (fun y ↦ (a y j : ℂ)) k :=
      periodicFourierCoeff_fderiv (fun x l ↦ by dsimp; rw [hA.1 x l])
        ((hj j).of_le (by simp)) j k
    _ = _ := by
      rw [← torusPhysicalCoeff_eq hA]
      unfold torusPhysicalCoeff
      ring

/-- Smooth physical solenoidality follows from weighted coefficient solenoidality. -/
theorem assembly_solenoidal_of_datum {s : ℝ} {a : SpatialField}
    {A : PeriodicSobolev s} (ha : ContDiff ℝ ∞ a) (hA : IsPeriodicDatum s a A)
    (hdiv : IsSolenoidalPeriodicDatum A) (x : Space) :
    spatialDivergence (fun z ↦ a z.2) 0 x = 0 := by
  let d : Space → ℂ := fun x ↦ ∑ j : Fin 3,
    spatialPartial j (fun y ↦ (a y j : ℂ)) x
  have hj (j : Fin 3) : ContDiff ℝ ∞ (fun y ↦ (a y j : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp ((EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.comp ha)
  have hd : ContDiff ℝ ∞ d := by
    apply ContDiff.sum
    intro j _
    exact ((hj j).fderiv_right (by simp)).clm_apply contDiff_const
  have hp : IsPeriodicSpatial d := by
    intro y l
    apply Finset.sum_congr rfl
    intro j _
    exact NavierStokes.PeriodicUniqueness.spatial_partial_periodic
      (fun z q ↦ by dsimp; rw [hA.1 z q]) j y l
  have hc (k : PeriodicFrequency) : periodicFourierCoeff d k = 0 := by
    rw [assembly_fourier_divergence ha hA, hdiv k, mul_zero]
  have hi := periodic_eq_tsum_mFourier hp hd.continuous
    (summable_periodicFourierCoeff_of_smooth hp hd) x
  simp only [hc, zero_mul, tsum_zero] at hi
  rw [show d x = (spatialDivergence (fun z ↦ a z.2) 0 x : ℂ) from
    assembly_complex_divergence ha x] at hi
  exact Complex.ofReal_eq_zero.mp hi

/-- The coefficient-to-physical divergence bridge on a persistent path. -/
theorem persistence_physical_divergence {T : ℝ} {u : ℝ → PeriodicSobolev 3}
    (h : PersistenceInput T u) {t : ℝ} (ht : t ∈ Ico 0 T)
    (hdiv : IsSolenoidalPeriodicDatum (u t)) (x : Space) :
    spatialDivergence (torusPhysicalVelocity u) t x = 0 :=
  assembly_solenoidal_of_datum (persistence_physical_spatial_smooth h ht)
    (torusPhysicalField_datum (u t)) hdiv x

/-- The projected equation field follows from the existing classical momentum and divergence. -/
theorem classicalSolutionT_projected {ν T : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (w : ClassicalSolutionT ν a f T) :
    ∀ t ∈ Ioo (0 : ℝ) T, ∀ x : Space,
      temporalDerivative w.velocity t x - ν • spatialLaplacian w.velocity t x =
        (f (t, x) - convectionDivergenceT w.velocity t x) -
          pressureGradient w.pressure t x := by
  intro t ht x
  have ht' : t ∈ Ico (0 : ℝ) T := ⟨ht.1.le, ht.2⟩
  have hs : ContDiff ℝ ∞ (fun y : Space ↦ w.velocity (t, y)) :=
    w.velocity_smooth.comp_contDiff (contDiff_const.prodMk contDiff_id)
      (fun y ↦ ⟨ht', mem_univ y⟩)
  exact (NSFormalization.Section4.A01.navierStokesResidual_eq_iff_projected
    ν w.velocity w.pressure t x (f (t, x))
    (hs.differentiable (by simp) x) (w.divergence t ht' x)).mp (w.momentum t ht x)

/-- Every classical solution with the prescribed H³ data satisfies the persistence input. -/
theorem persistence_of_classicalSolutionT {ν T : ℝ} {a : SpatialField} {g : SpaceTimeField}
    (w : ClassicalSolutionT ν a g T) {u : ℝ → PeriodicSobolev 3}
    (hu : IsPeriodicSobolevPathOn 3 (Ico 0 T) w.velocity u) :
    PersistenceInput T u := by
  intro m
  obtain ⟨G, hG, hdatum⟩ := w.sobolev m
  refine ⟨G, hG, fun t ht i k ↦ ?_⟩
  rw [torusPhysicalCoeff_eq (hdatum t ht), torusPhysicalCoeff_eq (hu t ht)]

/-- The divergence of a fixed Fourier mode is a continuous real-linear functional. -/
def assemblyDivergenceCLM (s : ℝ) (k : PeriodicFrequency) : PeriodicSobolev s →L[ℝ] ℂ :=
  ∑ j : Fin 3, periodicDerivativeSymbol j k •
    ((lp.evalCLM ℝ (fun _ : PeriodicFrequency ↦ ℂ) 2 k).comp
      ((PiLp.proj 2 (fun _ : Fin 3 ↦ PeriodicScalarData) j).comp
        realPeriodicSubmodule.subtypeL))

theorem assemblyDivergenceCLM_apply (s : ℝ) (k : PeriodicFrequency) (A : PeriodicSobolev s) :
    assemblyDivergenceCLM s k A = ∑ j : Fin 3, periodicDerivativeSymbol j k * A.1 j k := by
  simp only [assemblyDivergenceCLM, sum_apply,
    smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul]
  rfl

/-- Any scalar Fourier multiplier preserves coefficient solenoidality. -/
theorem assembly_multiplier_solenoidal {s r : ℝ} {A : PeriodicSobolev s}
    {B : PeriodicSobolev r} (hA : IsSolenoidalPeriodicDatum A)
    (m : PeriodicFrequency → ℂ) (hB : ∀ i k, B.1 i k = m k * A.1 i k) :
    IsSolenoidalPeriodicDatum B := by
  intro k
  simp_rw [hB, mul_left_comm (periodicDerivativeSymbol _ k) (m k)]
  rw [← Finset.mul_sum, hA k, mul_zero]

/-- Every exact contract's nonlinear output is solenoidal. -/
theorem assembly_bilinear_solenoidal {ν : ℝ} (C : TorusTwoSpaceContract ν)
    (A B : PeriodicSobolev 3) : IsSolenoidalPeriodicDatum (C.analytic.bilinear A B) := by
  have he : C.analytic.bilinear A B = torusProjectedConvectionDatum A B := by
    apply Subtype.ext
    apply WithLp.ofLp_injective 2
    funext i
    ext k
    rw [C.bilinear_symbol, torusProjectedConvectionDatum_coeff]
  rw [he]
  exact (Classical.choose_spec (leray_exists_contraction 2 (torusConvectionDatum A B))).2.2

/-- Solenoidality commutes with a genuine Bochner interval integral. -/
theorem assembly_integral_solenoidal {f : ℝ → PeriodicSobolev 3} {t : ℝ}
    (ht : 0 ≤ t) (hi : IntervalIntegrable f volume 0 t)
    (hf : ∀ s ∈ Icc 0 t, IsSolenoidalPeriodicDatum (f s)) :
    IsSolenoidalPeriodicDatum (∫ s in (0 : ℝ)..t, f s) := by
  intro k
  rw [← assemblyDivergenceCLM_apply, ← (assemblyDivergenceCLM 3 k).intervalIntegral_comp_comm hi]
  calc
    _ = ∫ _s in (0 : ℝ)..t, (0 : ℂ) := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le ht] at hs
      exact (assemblyDivergenceCLM_apply 3 k (f s)).trans (hf s hs k)
    _ = 0 := intervalIntegral.integral_zero

/-- The forced mild equation preserves coefficient solenoidality on the original horizon. -/
theorem assembly_mild_solenoidal {ν T : ℝ} {C : TorusTwoSpaceContract ν}
    {A : PeriodicSobolev 3} {P u : ℝ → PeriodicSobolev 3}
    (hA : IsSolenoidalPeriodicDatum A)
    (hP : ∀ t : ℝ, 0 ≤ t → IsSolenoidalPeriodicDatum (P t))
    (hu : TorusForcedMildOn C A P T u) {t : ℝ} (ht : t ∈ Icc 0 T) :
    IsSolenoidalPeriodicDatum (u t) := by
  have hheat (r : ℝ≥0) (B : PeriodicSobolev 3) (hB : IsSolenoidalPeriodicDatum B) :
      IsSolenoidalPeriodicDatum (C.analytic.linearEvolution r B) :=
    assembly_multiplier_solenoidal hB (fun k ↦ (torusHeatSymbol ν r k : ℂ))
      (C.linear_symbol r B)
  have hnonlinear (s : ℝ) : IsSolenoidalPeriodicDatum (C.analytic.duhamelIntegrand t u s) := by
    change IsSolenoidalPeriodicDatum
      (MNS2.endpointSafePositiveOperator C.analytic.positiveSmoothing (t-s)
        (C.analytic.bilinear (u s) (u s)))
    unfold MNS2.endpointSafePositiveOperator
    split_ifs with hts
    · exact assembly_multiplier_solenoidal (assembly_bilinear_solenoidal C (u s) (u s))
        (fun k ↦ ((Real.sqrt (periodicFrequencyWeight k) * torusHeatSymbol ν (t-s) k : ℝ) : ℂ))
        (C.smoothing_symbol (t-s) hts _)
    · intro k
      simp
  have hforce := assembly_integral_solenoidal ht.1 (hu.force_integrable t ht)
    (fun s hs ↦ hheat _ _ (hP s hs.1))
  have hconv := assembly_integral_solenoidal ht.1 (hu.nonlinear_integrable t ht)
    (fun s _ ↦ hnonlinear s)
  rw [hu.equation t ht]
  intro k
  change assemblyDivergenceCLM 3 k (torusForcedPicard C A P u ⟨t, ht.1⟩) = 0
  unfold torusForcedPicard
  rw [map_sub, map_add]
  simp only [assemblyDivergenceCLM_apply]
  calc
    _ = (0 : ℂ) + 0 - 0 :=
      congrArg₂ (· - ·) (congrArg₂ (· + ·) (hheat ⟨t, ht.1⟩ A hA k) (hforce k)) (hconv k)
    _ = 0 := by ring

/-- Initial physical incompressibility gives the precise weighted Fourier constraint. -/
theorem assembly_datum_solenoidal {s : ℝ} {a : SpatialField} {A : PeriodicSobolev s}
    (ha : ContDiff ℝ ∞ a) (hA : IsPeriodicDatum s a A)
    (hdiv : NSFormalization.Section4.A02.IsSolenoidal a) :
    IsSolenoidalPeriodicDatum A := by
  intro k
  have h := assembly_fourier_divergence ha hA k
  have he : (fun x ↦ ∑ j : Fin 3, spatialPartial j (fun y ↦ (a y j : ℂ)) x) =
      fun _ ↦ (0 : ℂ) := by
    funext x
    rw [assembly_complex_divergence ha x, hdiv x, Complex.ofReal_zero]
  rw [he] at h
  have hz : periodicFourierCoeff (fun _ : Space ↦ (0 : ℂ)) k = 0 := by
    simp [periodicFourierCoeff, NSFormalization.Paper1.periodicFourierCoeff_eq_cube,
      NavierStokes.PeriodicIntegration.cubeIntegral]
  rw [hz] at h
  have hw : (periodicFrequencyWeight k ^ (-s/2) : ℝ) ≠ 0 := by
    apply ne_of_gt
    apply Real.rpow_pos_of_pos
    unfold periodicFrequencyWeight
    positivity
  exact (mul_eq_zero.mp h.symm).resolve_left (Complex.ofReal_ne_zero.mpr hw)

/-- The canonical Leray graph has solenoidal range for any supplied representative. -/
theorem assembly_leray_solenoidal {s : ℝ} {A B : PeriodicSobolev s}
    (h : IsPeriodicLerayDatum A B) : IsSolenoidalPeriodicDatum B := by
  obtain ⟨D, hD, _, hd⟩ := leray_exists_contraction s A
  have he : B = D := by
    apply Subtype.ext
    apply WithLp.ofLp_injective 2
    funext i
    ext k
    exact (h i k).trans (hD i k).symm
  rw [he]
  exact hd

/-- The complete divergence field of the U9d target, on `Ico` including time zero. -/
theorem persistence_mild_physical_divergence {ν T : ℝ} {C : TorusTwoSpaceContract ν}
    {a : SpatialField} {A : PeriodicSobolev 3} {F P u : ℝ → PeriodicSobolev 3}
    (ha : a ∈ initialClassT) (hA : IsPeriodicDatum 3 a A)
    (hP : ∀ t : ℝ, 0 ≤ t → IsPeriodicLerayDatum (F t) (P t))
    (hu : TorusForcedMildOn C A P T u) (hp : PersistenceInput T u) :
    ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Space,
      spatialDivergence (torusPhysicalVelocity u) t x = 0 := by
  intro t ht x
  exact persistence_physical_divergence hp ht
    (assembly_mild_solenoidal (assembly_datum_solenoidal ha.1 hA ha.2.2)
      (fun s hs ↦ assembly_leray_solenoidal (hP s hs)) hu ⟨ht.1, ht.2.le⟩) x

/-- Persistence is tested together with an actual forced mild solution and full classical recovery. -/
theorem classicalAssembly_nonzero :
    ∃ C : TorusTwoSpaceContract 1,
      let c := coordinateVector 0
      let u := fun t : ℝ ↦ (1+t) • torusConstantDatum 3 c
      PersistenceInput 1 u ∧
      TorusForcedMildOn C (torusConstantDatum 3 c)
        (fun _ ↦ torusConstantDatum 3 c) 1 u ∧
      (∃ w : ClassicalSolutionT 1 (fun _ ↦ c) (fun _ ↦ c) 1,
        PeriodicLocalRegularity 1 (fun _ ↦ c) (fun _ ↦ c) 1 w ∧
        IsPeriodicSobolevPathOn 3 (Ico 0 1) w.velocity u) ∧
      torusPhysicalVelocity u (0, 0) ≠ 0 ∧ c ≠ 0 := by
  obtain ⟨C⟩ := torusTwoSpaceContract_nonempty' 1 (by norm_num)
  refine ⟨C, persistence_affine_constant 1 _,
    torusForcedMildOn_affine_constant C _ (by norm_num),
    torusPhysicalRecovery_affine_constant 1 1 _ (by norm_num), ?_, ?_⟩
  · change torusPhysicalField ((1+(0 : ℝ)) • torusConstantDatum 3 (coordinateVector 0)) 0 ≠ 0
    rw [add_zero, one_smul, torusPhysicalField_constant]
    intro he
    have hc := congrArg (fun v : Space ↦ v 0) he
    norm_num [coordinateVector] at hc
  · intro he
    have hc := congrArg (fun v : Space ↦ v 0) he
    norm_num [coordinateVector] at hc

example : PersistenceInput 1 (fun t ↦ (1+t) • torusConstantDatum 3 (coordinateVector 0)) :=
  persistence_affine_constant 1 (coordinateVector 0)

end NSFormalization.Section3.T11
