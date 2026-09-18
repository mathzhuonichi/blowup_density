import NSFormalization.Section3.T11.LocalTheory
import NSFormalization.Section3.T10.DatumBasics
import NSFormalization.Paper1.PeriodicHeatMultiplier
import Formal.EndpointSafeTwoSpacePicard
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# U9a: torus local-existence route probe

The sole unresolved local-existence input is `PeriodicQuantitativeLocalInput`,
with the quantifiers fixed by T11_SPLIT. The two-space structure below is a
specification of analytic operators, NOT an inhabitant and NOT a second local
existence assumption. The proved first rung constructs real vector multipliers
on the canonical carrier, including the one-derivative heat estimate.

R2 is the construction route: coefficient paths, causal windows, and a common
horizon. R1's endpoint-safe integration remains reusable analytic infrastructure.
-/
noncomputable section
namespace NSFormalization.Section3.T11

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField SpaceTimeScalar)
open NSFormalization.Section3.T10
open scoped ContDiff ENNReal NNReal BigOperators

-- Pin the normed route through the submodule for nested continuous linear maps.
local instance torusProbeNormedGroup : NormedAddCommGroup (PeriodicSobolev 3) :=
  realPeriodicSubmodule.normedAddCommGroup

local instance torusProbeNormedSpace : NormedSpace ℝ (PeriodicSobolev 3) :=
  realPeriodicSubmodule.normedSpace

/-- U9's sole named unresolved input; no force-support or higher-datum-norm change. -/
def PeriodicQuantitativeLocalInput : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ K : ℝ≥0∞, K ≠ ⊤ → ∃ δ : ℝ, 0 < δ ∧
    ∀ a : SpatialField, a ∈ initialClassT → periodicSobolevENorm 1 a ≤ K →
      ∀ g : SpaceTimeField, ContDiff ℝ ∞ g → IsPeriodicOn univ g →
        (∀ m : ℕ, forceSobolevENormT 1 (m : ℝ) g ≤ K) →
          ∃ w : ClassicalSolutionT ν a g δ, PeriodicLocalRegularity ν a g δ w

/-- Bounded real even symbols act on the complete weighted coefficient space.
Both Sobolev indices are explicit: changing an index alone never reweights data. -/
def torusMultiplier (s r : ℝ) (m : PeriodicFrequency → ℝ) (C : ℝ)
    (_hC : 0 ≤ C) (hm : ∀ k, |m k| ≤ C) (he : ∀ k, m (-k) = m k)
    (A : PeriodicSobolev s) : PeriodicSobolev r := by
  let B : Fin 3 → PeriodicScalarData := fun i ↦
    ⟨fun k ↦ (m k : ℂ) * A.1 i k,
      ((lp.memℓp (A.1 i)).norm.const_mul C).mono (by
        intro k
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (hm k) (norm_nonneg _))⟩
  refine ⟨WithLp.toLp 2 B, ?_⟩
  intro i k
  change (m (-k) : ℂ) * A.1 i (-k) = star ((m k : ℂ) * A.1 i k)
  rw [he k, A.2 i k]
  simp

/-- The vector estimate uses the Euclidean product norm, with no factor of three. -/
theorem torusMultiplier_norm_le (s r : ℝ) (m : PeriodicFrequency → ℝ) (C : ℝ)
    (hC : 0 ≤ C) (hm : ∀ k, |m k| ≤ C) (he : ∀ k, m (-k) = m k)
    (A : PeriodicSobolev s) :
    ‖torusMultiplier s r m C hC hm he A‖ ≤ C * ‖A‖ := by
  let B := torusMultiplier s r m C hC hm he A
  have hc (i : Fin 3) : ‖B.1 i‖ ≤ C * ‖A.1 i‖ := by
    have h := lp.norm_mono (p := (2 : ℝ≥0∞)) (by norm_num)
      (x := B.1 i) (y := C • A.1 i) (by
        intro k
        change ‖(m k : ℂ) * A.1 i k‖ ≤ ‖C • A.1 i k‖
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_smul,
          Real.norm_eq_abs, abs_of_nonneg hC]
        exact mul_le_mul_of_nonneg_right (hm k) (norm_nonneg _))
    simpa [norm_smul, Real.norm_eq_abs, abs_of_nonneg hC] using h
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mp
  change ‖B.1‖ ^ 2 ≤ (C * ‖A.1‖) ^ 2
  rw [mul_pow, PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ ↦ by
    simpa only [mul_pow] using
      pow_le_pow_left₀ (norm_nonneg _) (hc i) 2

/-- Canonical T10 and existing Paper1 weights coincide by real algebra. -/
theorem torus_weight_eq (k : PeriodicFrequency) :
    periodicFrequencyWeight k = NSFormalization.Paper1.periodicFrequencyWeight k := by
  rw [NSFormalization.Paper1.periodicFrequencyWeight_eq]
  unfold periodicFrequencyWeight
  ring

/-- Reflection law needed to preserve real-valued Fourier data. -/
theorem torus_weight_neg (k : PeriodicFrequency) :
    periodicFrequencyWeight (-k) = periodicFrequencyWeight k := by
  simp [periodicFrequencyWeight]

/-- The actual heat symbol; the torus zero mode is retained. -/
def torusHeatSymbol (ν t : ℝ) (k : PeriodicFrequency) : ℝ :=
  NSFormalization.Paper1.PeriodicHeatMultiplier.heatSymbol ν t k

theorem torusHeatSymbol_neg (ν t : ℝ) (k : PeriodicFrequency) :
    torusHeatSymbol ν t (-k) = torusHeatSymbol ν t k := by
  unfold torusHeatSymbol NSFormalization.Paper1.PeriodicHeatMultiplier.heatSymbol
    NSFormalization.Paper1.PeriodicHeatMultiplier.laplaceEigenvalue
  rw [← torus_weight_eq, ← torus_weight_eq, torus_weight_neg]

/-- The exact positive-time smoothing kernel, including the constant mode. -/
def torusSmoothingKernel (ν t : ℝ) : ℝ := Real.sqrt (1 + 1 / (ν * t))

/-- The same-order real vector heat evolution on canonical weighted data. -/
def torusHeat (s : ℝ) {ν t : ℝ} (hν : 0 ≤ ν) (ht : 0 ≤ t)
    (A : PeriodicSobolev s) : PeriodicSobolev s :=
  torusMultiplier s s (torusHeatSymbol ν t) 1 zero_le_one
    (fun k ↦ by
      unfold torusHeatSymbol
      rw [abs_of_nonneg (NSFormalization.Paper1.PeriodicHeatMultiplier.heatSymbol_nonneg ν t k)]
      exact NSFormalization.Paper1.PeriodicHeatMultiplier.heatSymbol_le_one hν ht k)
    (torusHeatSymbol_neg ν t) A

/-- First rung: a genuine canonical vector-carrier contraction. -/
theorem torusHeat_norm_le (s : ℝ) {ν t : ℝ} (hν : 0 ≤ ν) (ht : 0 ≤ t)
    (A : PeriodicSobolev s) : ‖torusHeat s hν ht A‖ ≤ ‖A‖ := by
  unfold torusHeat
  simpa only [one_mul] using torusMultiplier_norm_le s s _ 1 zero_le_one _ _ A

/-- Positive-time smoothing from weighted H^s to weighted H^(s+1). -/
def torusHeatSmoothing (s : ℝ) {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t)
    (A : PeriodicSobolev s) : PeriodicSobolev (s + 1) :=
  torusMultiplier s (s + 1)
    (fun k ↦ Real.sqrt (periodicFrequencyWeight k) * torusHeatSymbol ν t k)
    (torusSmoothingKernel ν t) (Real.sqrt_nonneg _)
    (fun k ↦ by
      unfold torusHeatSymbol
      rw [abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _)
        (NSFormalization.Paper1.PeriodicHeatMultiplier.heatSymbol_nonneg ν t k)), torus_weight_eq]
      exact NSFormalization.Paper1.PeriodicHeatMultiplier.sqrt_weight_mul_heatSymbol_le hν ht k)
    (fun k ↦ by rw [torus_weight_neg, torusHeatSymbol_neg]) A

/-- First rung: H^s → H^(s+1) with the exact scalar kernel on real three-vectors. -/
theorem torusHeatSmoothing_norm_le (s : ℝ) {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t)
    (A : PeriodicSobolev s) :
    ‖torusHeatSmoothing s hν ht A‖ ≤ torusSmoothingKernel ν t * ‖A‖ :=
  torusMultiplier_norm_le _ _ _ _ _ _ _ A

/-- Coefficients specify the order conversion; H² and H³ are phantom-index aliases. -/
theorem torusHeatSmoothing_apply (s : ℝ) {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t)
    (A : PeriodicSobolev s) (i : Fin 3) (k : PeriodicFrequency) :
    (torusHeatSmoothing s hν ht A).1 i k =
      ((Real.sqrt (periodicFrequencyWeight k) * torusHeatSymbol ν t k : ℝ) : ℂ) *
        A.1 i k := rfl


/-- Honest same-order initial-time identity. -/
theorem torusHeat_zero (s : ℝ) {ν : ℝ} (hν : 0 ≤ ν) (A : PeriodicSobolev s) :
    torusHeat s hν (le_refl 0) A = A := by
  apply Subtype.ext
  apply WithLp.ofLp_injective 2
  funext i
  ext k
  change (torusHeatSymbol ν 0 k : ℂ) * A.1 i k = A.1 i k
  simp [torusHeatSymbol]

/-- The same-order heat semigroup law on the real three-vector carrier. -/
theorem torusHeat_add (s : ℝ) {ν t u : ℝ} (hν : 0 ≤ ν) (ht : 0 ≤ t) (hu : 0 ≤ u)
    (A : PeriodicSobolev s) :
    torusHeat s hν (add_nonneg ht hu) A = torusHeat s hν ht (torusHeat s hν hu A) := by
  apply Subtype.ext
  apply WithLp.ofLp_injective 2
  funext i
  ext k
  change (torusHeatSymbol ν (t + u) k : ℂ) * A.1 i k =
    (torusHeatSymbol ν t k : ℂ) * ((torusHeatSymbol ν u k : ℂ) * A.1 i k)
  simp [torusHeatSymbol, NSFormalization.Paper1.PeriodicHeatMultiplier.heatSymbol_add, mul_assoc]

/-- Positive smoothing coheres with same-order evolution; no value at zero is assumed. -/
theorem torusHeatSmoothing_coherent (s : ℝ) {ν t u : ℝ}
    (hν : 0 < ν) (ht : 0 < t) (hu : 0 ≤ u) (A : PeriodicSobolev s) :
    torusHeatSmoothing s hν (add_pos_of_pos_of_nonneg ht hu) A =
      torusHeat (s + 1) hν.le hu (torusHeatSmoothing s hν ht A) := by
  apply Subtype.ext
  apply WithLp.ofLp_injective 2
  funext i
  ext k
  change ((Real.sqrt (periodicFrequencyWeight k) * torusHeatSymbol ν (t + u) k : ℝ) : ℂ) *
      A.1 i k = (torusHeatSymbol ν u k : ℂ) *
        (((Real.sqrt (periodicFrequencyWeight k) * torusHeatSymbol ν t k : ℝ) : ℂ) * A.1 i k)
  simp only [torusHeatSymbol, NSFormalization.Paper1.PeriodicHeatMultiplier.heatSymbol_add,
    Complex.ofReal_mul]
  ring

/-- Multiplication by a scalar frequency symbol preserves incompressibility. -/
theorem torusHeat_solenoidal (s : ℝ) {ν t : ℝ} (hν : 0 ≤ ν) (ht : 0 ≤ t)
    (A : PeriodicSobolev s) (hA : IsSolenoidalPeriodicDatum A) :
    IsSolenoidalPeriodicDatum (torusHeat s hν ht A) := by
  intro k
  change ∑ j : Fin 3, periodicDerivativeSymbol j k * ((torusHeatSymbol ν t k : ℂ) * A.1 j k) = 0
  calc
    _ = (torusHeatSymbol ν t k : ℂ) * ∑ j : Fin 3, periodicDerivativeSymbol j k * A.1 j k := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = 0 := by rw [hA k, mul_zero]

/-- R1/R2 common nonlinear symbol: H³ × H³ → H² tensor divergence.
The order-three weights are removed before convolution, then order two is restored. -/
def torusConvectionSymbol (A B : PeriodicSobolev 3)
    (i : Fin 3) (k : PeriodicFrequency) : ℂ :=
  (periodicFrequencyWeight k : ℂ) *
    ∑ j : Fin 3, periodicDerivativeSymbol j k *
      ∑' l : PeriodicFrequency,
        (((periodicFrequencyWeight l) ^ (-(3 : ℝ) / 2) : ℝ) : ℂ) * A.1 j l *
          (((periodicFrequencyWeight (k - l)) ^ (-(3 : ℝ) / 2) : ℝ) : ℂ) * B.1 i (k - l)

/-- Exact Leray-projected bilinear symbol, with the full zero mode convention. -/
def torusProjectedConvectionSymbol (A B : PeriodicSobolev 3)
    (i : Fin 3) (k : PeriodicFrequency) : ℂ :=
  if k = 0 then torusConvectionSymbol A B i k else
    torusConvectionSymbol A B i k -
      ((k i : ℂ) / ((∑ j : Fin 3, (k j : ℝ) ^ 2 : ℝ) : ℂ)) *
        ∑ j : Fin 3, (k j : ℂ) * torusConvectionSymbol A B j k

/-- Exact two-space contract on T³. No inhabitant is asserted by this probe.
The symbol clauses prevent replacing Navier--Stokes by a zero bilinear map. -/
structure TorusTwoSpaceContract (ν : ℝ) where
  analytic : MNS2.EndpointSafeTwoSpaceDuhamelContract ℝ
    (PeriodicSobolev 3) (PeriodicSobolev 2)
  linear_symbol : ∀ t A i k,
    (analytic.linearEvolution t A).1 i k = (torusHeatSymbol ν t k : ℂ) * A.1 i k
  smoothing_symbol : ∀ t ht A i k,
    (analytic.positiveSmoothing t ht A).1 i k =
      ((Real.sqrt (periodicFrequencyWeight k) * torusHeatSymbol ν t k : ℝ) : ℂ) * A.1 i k
  bilinear_symbol : ∀ A B i k,
    (analytic.bilinear A B).1 i k = torusProjectedConvectionSymbol A B i k
  kernel_eq : analytic.smoothingKernel = torusSmoothingKernel ν

/-- Forced Picard operator. F is the projected H³ force datum path;
its integration uses the same-order evolution, not a fictitious endpoint smoother. -/
def torusForcedPicard {ν : ℝ} (C : TorusTwoSpaceContract ν)
    (a : PeriodicSobolev 3) (F u : ℝ → PeriodicSobolev 3) (t : ℝ≥0) :
    PeriodicSobolev 3 :=
  C.analytic.linearEvolution t a +
    (∫ s in (0 : ℝ)..(t : ℝ),
      C.analytic.linearEvolution (Real.toNNReal ((t : ℝ) - s)) (F s)) -
    ∫ s in (0 : ℝ)..(t : ℝ), C.analytic.duhamelIntegrand t u s

/-- Semantic target for the forced coefficient solver. Both integrability clauses
are explicit, so totalized divergent integrals cannot certify a mild solution. -/
structure TorusForcedMildOn {ν : ℝ} (C : TorusTwoSpaceContract ν)
    (a : PeriodicSobolev 3) (F : ℝ → PeriodicSobolev 3) (T : ℝ)
    (u : ℝ → PeriodicSobolev 3) : Prop where
  time_nonneg : 0 ≤ T
  continuous_path : ContinuousOn u (Icc 0 T)
  initial : u 0 = a
  force_integrable : ∀ t ∈ Icc (0 : ℝ) T,
    IntervalIntegrable (fun s ↦
      C.analytic.linearEvolution (Real.toNNReal (t - s)) (F s)) volume 0 t
  nonlinear_integrable : ∀ t ∈ Icc (0 : ℝ) T,
    IntervalIntegrable (C.analytic.duhamelIntegrand t u) volume 0 t
  equation : ∀ t, ∀ ht : t ∈ Icc (0 : ℝ) T,
    u t = torusForcedPicard C a F u ⟨t, ht.1⟩

/-- Quantitative ball obligations: b is the norm of the forced linear path,
radius R; beta is the integrated bilinear constant. These are numeric certificates,
not local existence hypotheses. -/
structure TorusPicardConstants {ν : ℝ} (C : TorusTwoSpaceContract ν) (T R b : ℝ) where
  time_pos : 0 < T
  radius_pos : 0 < R
  linear_nonneg : 0 ≤ b
  self_map_bound : b + ‖C.analytic.bilinear‖ * C.analytic.kernelPrimitive T * R ^ 2 ≤ R
  contraction_bound : 2 * ‖C.analytic.bilinear‖ * C.analytic.kernelPrimitive T * R < 1

/-- The package's quadratic estimate, now on the actual torus carriers. -/
theorem torus_bilinear_bound {ν : ℝ} (C : TorusTwoSpaceContract ν)
    (A B : PeriodicSobolev 3) :
    ‖C.analytic.bilinear A B‖ ≤ ‖C.analytic.bilinear‖ * ‖A‖ * ‖B‖ :=
  MNS2.norm_continuousBilinear_apply_le C.analytic.bilinear A B

/-- Zero-mode datum of an arbitrary real constant vector, at every order. -/
def torusConstantDatum (s : ℝ) (c : Space) : PeriodicSobolev s := by
  refine ⟨WithLp.toLp 2 (fun i ↦ lp.single 2 (0 : PeriodicFrequency) (c i : ℂ)), ?_⟩
  intro i k
  change (lp.single 2 0 (c i : ℂ) : PeriodicScalarData) (-k) = star ((lp.single 2 0 (c i : ℂ) : PeriodicScalarData) k)
  by_cases hk : k = 0
  · subst k
    simp
  · simp [lp.single_apply, hk, neg_ne_zero.mpr hk]

/-- Nonzero constant modes satisfy the genuine canonical datum predicate. -/
theorem torusConstantDatum_isDatum (s : ℝ) (c : Space) :
    IsPeriodicDatum s (fun _ ↦ c) (torusConstantDatum s c) := by
  refine ⟨fun _ _ ↦ rfl, integrable_const c, ?_⟩
  intro i k
  change (lp.single 2 0 (c i : ℂ) : PeriodicScalarData) k =
    periodicFrequencyWeight k ^ (s / 2) • periodicFourierCoeff (fun _ ↦ (c i : ℂ)) k
  rw [periodicFourierCoeff_const]
  by_cases hk : k = 0
  · subst k
    simp [periodicFrequencyWeight]
  · simp [lp.single_apply, hk]

/-- Scalar paths through a constant mode remain honest weighted Fourier data. -/
theorem torusConstantDatum_smul (s r : ℝ) (c : Space) :
    IsPeriodicDatum s (fun _ ↦ r • c) (r • torusConstantDatum s c) := by
  have heq : r • torusConstantDatum s c = torusConstantDatum s (r • c) := by
    apply Subtype.ext
    ext i k
    change r • (lp.single 2 0 (c i : ℂ) : PeriodicScalarData) k = (lp.single 2 0 ((r • c) i : ℂ) : PeriodicScalarData) k
    by_cases hk : k = 0
    · subst k
      simp [Complex.real_smul]
    · simp [lp.single_apply, hk]
  rw [heq]
  exact torusConstantDatum_isDatum s (r • c)

/-- A spatially homogeneous, genuinely forced classical solution.
No restriction is imposed on the continuation of the time profile past T. -/
def torusHomogeneousSolution (ν T : ℝ) (hT : 0 < T) (c : Space)
    (b d : ℝ → ℝ) (hb : ContDiff ℝ ∞ b) (hb0 : b 0 = 1)
    (hd : ∀ t, HasDerivAt b (d t) t) :
    ClassicalSolutionT ν (fun _ ↦ c) (fun z ↦ d z.1 • c) T where
  velocity := fun z ↦ b z.1 • c
  pressure := 0
  horizon_pos := hT
  velocity_smooth := (hb.comp contDiff_fst |>.smul contDiff_const).contDiffOn
  pressure_smooth := contDiff_const.contDiffOn
  initial := by intro x; simp [hb0]
  divergence := by intro t ht x; simp [spatialDivergence, spatialDerivative]
  momentum := by
    intro t ht x
    have hder := (hd t).smul_const c
    have he : temporalDerivative (fun z ↦ b z.1 • c) t x = d t • c := by
      unfold temporalDerivative
      rw [hder.hasFDerivAt.fderiv]
      simp
    simp [NavierStokesR3.ProblemStatement.navierStokesResidual, he,
      advection, spatialDerivative, spatialLaplacian, pressureGradient]
  sobolev := by
    intro m
    exact ⟨fun t ↦ b t • torusConstantDatum m c,
      (hb.continuous.smul continuous_const).continuousOn,
      fun t _ ↦ torusConstantDatum_smul m (b t) c⟩
  pressure_gradient := by
    intro t ht
    have he : (fun x : Space ↦ pressureGradient (0 : SpaceTimeScalar) t x) = 0 := by
      funext x
      simp [pressureGradient]
    rw [he]
    exact memLp_const (0 : Space)
  velocity_periodic := fun _ _ _ _ ↦ rfl
  pressure_periodic := fun _ _ _ _ ↦ rfl
  pressure_gauge := by intro t ht; simp [pressureMeanT, torusLift, NSFormalization.Paper1.torusLift]

/-- The homogeneous witness has every clause of the unmodified regularity record. -/
theorem torusHomogeneousSolution_regularity (ν T : ℝ) (hT : 0 < T) (c : Space)
    (b d : ℝ → ℝ) (hb : ContDiff ℝ ∞ b) (hb0 : b 0 = 1)
    (hd : ∀ t, HasDerivAt b (d t) t) :
    PeriodicLocalRegularity ν (fun _ ↦ c) (fun z ↦ d z.1 • c) T
      (torusHomogeneousSolution ν T hT c b d hb hb0 hd) := by
  refine ⟨?_, ?_, ?_⟩
  · intro m
    exact ⟨fun t ↦ b t • torusConstantDatum m c,
      fun t _ ↦ torusConstantDatum_smul m (b t) c,
      (hb.smul contDiff_const).contDiffOn⟩
  · intro t ht x
    simp [torusHomogeneousSolution, scalarSpatialLaplacianT, spatialDivergence,
      spatialDerivative, convectionDivergenceT, NSFormalization.Section4.A01.convectionDivergence]
  · intro t ht x
    have he : temporalDerivative (fun z : SpaceTime ↦ b z.1 • c) t x = d t • c := by
      unfold temporalDerivative
      rw [((hd t).smul_const c).hasFDerivAt.fderiv]
      simp
    simp [torusHomogeneousSolution, he, spatialLaplacian, spatialDerivative,
      pressureGradient, convectionDivergenceT, NSFormalization.Section4.A01.convectionDivergence]

/-- A quantitative consequence for every datum and force allowed by the exact input. -/
theorem quantitative_lifespan_lower_bound (H : PeriodicQuantitativeLocalInput) :
    ∀ ν : ℝ, 0 < ν → ∀ K : ℝ≥0∞, K ≠ ⊤ → ∃ δ : ℝ, 0 < δ ∧
      ∀ a : SpatialField, a ∈ initialClassT → periodicSobolevENorm 1 a ≤ K →
        ∀ g : SpaceTimeField, ContDiff ℝ ∞ g → IsPeriodicOn univ g →
          (∀ m : ℕ, forceSobolevENormT 1 (m : ℝ) g ≤ K) →
            ENNReal.ofReal δ ≤ maximalLifespanT ν a g := by
  intro ν hν K hK
  obtain ⟨δ, hδ, hlocal⟩ := H ν hν K hK
  refine ⟨δ, hδ, ?_⟩
  intro a ha hKa g hg hp hKg
  obtain ⟨w, _⟩ := hlocal a ha hKa g hg hp hKg
  exact le_iSup_of_le δ (le_iSup_of_le (show Nonempty (ClassicalSolutionT ν a g δ) from ⟨w⟩) le_rfl)

-- The witness packages all-order datum and force infima; allow bounded elaboration headroom.
set_option maxHeartbeats 400000 in
/-- Satisfiability check for the exact input's premises and output, with BOTH
nonzero force and nonzero solution. The force is smooth at the new time zero,
spatially constant, and integrable on the whole positive half-line. -/
theorem nonzero_forced_witness :
    ∃ (K : ℝ≥0∞) (a : SpatialField) (g : SpaceTimeField),
      K ≠ ⊤ ∧ a ∈ initialClassT ∧ periodicSobolevENorm 1 a ≤ K ∧
      ContDiff ℝ ∞ g ∧ IsPeriodicOn univ g ∧
      (∀ m : ℕ, forceSobolevENormT 1 (m : ℝ) g ≤ K) ∧
      ∃ w : ClassicalSolutionT 1 a g 1,
        PeriodicLocalRegularity 1 a g 1 w ∧
        w.velocity (0, 0) ≠ 0 ∧ g (0, 0) ≠ 0 := by
  let c : Space := coordinateVector 0
  let a : SpatialField := fun _ ↦ c
  let g : SpaceTimeField := fun z ↦ Real.exp (-z.1) • c
  let A : PeriodicSobolev 1 := torusConstantDatum 1 c
  let G : ℝ → PeriodicSobolev 1 := fun t ↦ Real.exp (-t) • A
  have hG : Integrable G NSFormalization.Section4.A02.forceTimeMeasure :=
    (integrableOn_exp_neg_Ioi 0).smul_const A
  let K : ℝ≥0∞ := max ‖A‖ₑ (eLpNorm G 1 NSFormalization.Section4.A02.forceTimeMeasure)
  have hK : K ≠ ⊤ := by
    exact ne_of_lt (max_lt (enorm_lt_top (x := A)) (memLp_one_iff_integrable.mpr hG).2)
  have ha : a ∈ initialClassT := by
    refine ⟨contDiff_const, fun _ _ ↦ rfl, ?_⟩
    intro x
    simp [a, spatialDivergence, spatialDerivative]
  have hA : periodicSobolevENorm 1 a ≤ K := by
    apply le_trans (b := ‖A‖ₑ)
    · unfold periodicSobolevENorm
      exact iInf_le_of_le ⟨A, torusConstantDatum_isDatum 1 c⟩ le_rfl
    · exact le_max_left _ _
  have hg : ContDiff ℝ ∞ g := by
    dsimp [g]
    fun_prop
  have hgK : ∀ m : ℕ, forceSobolevENormT 1 (m : ℝ) g ≤ K := by
    intro m
    have hpath : IsPeriodicSobolevPath (m : ℝ) g G :=
      fun t _ ↦ torusConstantDatum_smul m (Real.exp (-t)) c
    apply le_trans (b := eLpNorm G 1 NSFormalization.Section4.A02.forceTimeMeasure)
    · unfold forceSobolevENormT
      exact iInf_le_of_le ⟨G, hpath, hG.aestronglyMeasurable⟩ le_rfl
    · exact le_max_right _ _
  let b : ℝ → ℝ := fun t ↦ 2 - Real.exp (-t)
  have hb : ContDiff ℝ ∞ b := by dsimp [b]; fun_prop
  have hb0 : b 0 = 1 := by norm_num [b]
  have hd : ∀ t, HasDerivAt b (Real.exp (-t)) t := by
    intro t
    convert! (hasDerivAt_const t (2 : ℝ)).sub ((hasDerivAt_id t).neg.exp) using 1
    simp
  let w := torusHomogeneousSolution 1 1 zero_lt_one c b (fun t ↦ Real.exp (-t)) hb hb0 hd
  have hc : c ≠ 0 := by
    intro h
    have he := congrArg (fun x : Space ↦ x 0) h
    simp [c, coordinateVector] at he
  refine ⟨K, a, g, hK, ha, hA, hg, fun _ _ _ _ ↦ rfl, hgK, w,
    torusHomogeneousSolution_regularity 1 1 zero_lt_one c b _ hb hb0 hd, ?_, ?_⟩
  · simpa [w, torusHomogeneousSolution, hb0] using hc
  · simpa [g] using hc

example :
    ∃ (a : SpatialField) (g : SpaceTimeField) (w : ClassicalSolutionT 1 a g 1),
      PeriodicLocalRegularity 1 a g 1 w ∧ w.velocity (0, 0) ≠ 0 ∧ g (0, 0) ≠ 0 := by
  obtain ⟨_, a, g, _, _, _, _, _, _, w, hw⟩ := nonzero_forced_witness
  exact ⟨a, g, w, hw⟩

end NSFormalization.Section3.T11
