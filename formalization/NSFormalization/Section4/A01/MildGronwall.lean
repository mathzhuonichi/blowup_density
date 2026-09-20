import NSFormalization.Section4.A01.AprioriFamily
import Euler.RegularizedWordEquation
import Euler.QuadraticSourceLimit
import Euler.RegularizedEnergyFamily

/-!
Finite-order mild energy reduction. The scalar absorption and Grönwall interface
are proved below. `FiniteMildEnergy` is the remaining analytic hypothesis; this
file does NOT assert that the vendor's metric estimate supplies it.
-/
noncomputable section
namespace NSFormalization.Section4.A01
open Set MeasureTheory EulerSmoothLimit EulerLpTranslation EulerMeanOrdinaryLift
open EulerMeanSmoothRepresentative EulerCylinderSobolevSpace EulerLiftedGradientSpace
open EulerSmoothFieldSobolevTime EulerQuadraticSource EulerSobolevHeat EulerVolterraConvolution
open EulerQuadraticSourceLimit EulerRegularizedWordEquation EulerMetricHeatEnergy
open NSFormalization.Source.ForcedCylinderLocal
open scoped Topology ContDiff
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-- Explicit comparison constant for every derivative word through order q+1. -/
def mildNormConstant (q : ℕ) : ℝ := Real.sqrt (Fintype.card (SobolevWord (q+1)) : ℝ)

theorem mildNormConstant_nonneg (q : ℕ) : 0 ≤ mildNormConstant q := Real.sqrt_nonneg _

/-- Constant Euclidean metric, full finite word family. -/
def euclideanWordNorm {q : ℕ} (u : SobolevSpace 1 (q+1)) : ℝ :=
  EulerFiniteMetricEnergy.familyMetricNorm (ContinuousLinearMap.id ℝ (LiftL2 1)) u.val

/-- The metric norm is the square root of the sum of all word squares. -/
theorem euclideanWordNorm_eq {q : ℕ} (u : SobolevSpace 1 (q+1)) :
    euclideanWordNorm u = Real.sqrt (∑ w : SobolevWord (q+1), ‖u.val w‖^2) := by
  simp only [euclideanWordNorm, EulerFiniteMetricEnergy.familyMetricNorm,
    EulerFiniteMetricEnergy.familyEnergy, ContinuousLinearMap.id_apply,
    real_inner_self_eq_norm_sq]

/-- Both norm comparisons, with no spatial smoothness or solenoidality premise. -/
theorem euclideanWordNorm_bounds {q : ℕ} (u : SobolevSpace 1 (q+1)) :
    ‖u‖ ≤ euclideanWordNorm u ∧ euclideanWordNorm u ≤ mildNormConstant q * ‖u‖ := by
  rw [euclideanWordNorm_eq]
  constructor
  · change ‖u.val‖ ≤ _
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
    intro w
    apply Real.le_sqrt_of_sq_le
    exact Finset.single_le_sum (fun v _ => sq_nonneg ‖u.val v‖) (Finset.mem_univ w)
  · have hs : (∑ w : SobolevWord (q+1), ‖u.val w‖^2) ≤
        (Fintype.card (SobolevWord (q+1)) : ℝ) * ‖u‖^2 := by
      simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using
        Finset.sum_le_sum (s := Finset.univ) (fun w _ =>
          pow_le_pow_left₀ (norm_nonneg _) (word_norm_le 1 u w) 2)
    calc
      _ ≤ Real.sqrt ((Fintype.card (SobolevWord (q+1)) : ℝ) * ‖u‖^2) :=
        Real.sqrt_le_sqrt hs
      _ = _ := by rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (norm_nonneg _)]; rfl

/-- The concrete Euclidean word energy is continuous along every finite-order path. -/
theorem continuous_euclideanWordNorm (q : ℕ) :
    Continuous (euclideanWordNorm (q := q)) := by
  have he : euclideanWordNorm (q := q) =
      fun u : SobolevSpace 1 (q+1) => Real.sqrt (∑ w : SobolevWord (q+1), ‖u.val w‖^2) :=
    funext euclideanWordNorm_eq
  rw [he]
  apply Continuous.sqrt
  apply continuous_finsetSum
  intro w _
  exact (wordOperator 1 w).continuous.norm.pow 2

/-- Uniform convergence of the genuine full-word Euclidean metric paths.
This specializes the vendor's regularized family limit at the identity metric;
passing the nonlinear forcing estimate to this limit remains separate. -/
theorem euclidean_full_word_limit (q : ℕ) (T : ℝ)
    (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q+1))) :
    let d := fun (_ : Unit) (W : SobolevWord (q+1)) => W.1.val
    let w := fun (_ : Unit) (W : SobolevWord (q+1)) => W.2
    let hd : ∀ i W, d i W ≤ q+1 := fun _ W => Nat.le_of_lt_succ W.1.isLt
    let K := ContinuousMap.const (Icc (0 : ℝ) T) (ContinuousLinearMap.id ℝ (LiftL2 1))
    Filter.Tendsto (fun n => EulerMetricPathConvergence.metricPath T K
      (EulerRegularizedEnergyFamily.regularizedValueFamily 1 d w hd n T u ()))
      Filter.atTop (𝓝 (EulerMetricPathConvergence.metricPath T K
        (EulerRegularizedEnergyFamily.energyValueFamily 1 d w hd T u ()))) := by
  dsimp only
  apply EulerMetricPathConvergence.metricPath_tendsto
  exact EulerRegularizedEnergyFamily.regularizedValueFamily_tendsto 1 _ _ _ T u ()

/-- The actual full-order regularized word equation, specialized to a quadratic
mild competitor. No divergence, classical solution, or higher-order path is assumed. -/
theorem quadratic_regularized_word {q m : ℕ} (hm : m ≤ q+1) (n : ℕ)
    (w : Fin m → Fin 4) {ν S T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) (hTS : T ≤ S)
    (D : Coefficients (Icc (0 : ℝ) S) (SobolevSpace 1 (q+1)) (SobolevSpace 1 q))
    (u₀ : SobolevSpace 1 (q+1)) (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q+1)))
    (hu : ∀ t, u t = quadraticDuhamel 1 ν hν hT hTS D u₀ u t)
    (t : ℝ) (ht : t ∈ Ioo 0 T) :
    HasDerivAt (fun r => value 1 (extendPath T hT (regularizedWordPath 1 hm n w T u) r))
      (ν • jetLaplacian 1 (toJet 1 (regularizedWordPath 1 hm n w T u
        ⟨t, ht.1.le, ht.2.le⟩)) +
        value 1 (regularizedWordBlock 1 hm n w
          (sourcePath (D.comp (timeInclusion hTS)) u ⟨t, ht.1.le, ht.2.le⟩))) t := by
  apply regularized_word_hasDerivAt 1 hm n w ν hν T hT u₀
    (sourcePath (D.comp (timeInclusion hTS)) u) u ?_ t ht
  exact hu

/-- Young absorption with the literal lane-193 driver. The factor 256 is
exactly 16 squared, and the resulting coefficient is A²/(4ν). -/
theorem mild_energy_absorption {ν A l x g b d : ℝ} (hν : 0 < ν) (hx : 0 ≤ x)
    (h : (1/2)*d + ν*g^2 ≤ A*(16*l)*Real.sqrt x*g + b*Real.sqrt x) :
    d ≤ 2 * ((A^2/(4*ν)) * (256*l^2) * x + b*Real.sqrt x) := by
  have ha := A04.young_high_real hν h
  rw [Real.sq_sqrt hx] at ha
  nlinarith [ha]

/-- The real tame tensor bound followed by the low-order comparison. The
comparison is explicit: this lemma does not assert descent of a mild path. -/
theorem outer_tame_low {m : ℕ} (hm : 2 ≤ m) {z : Space → Space}
    (hz : A03.MemHmVector m z)
    (h2 : D01.sobolevENorm 2 z ≠ ⊤) (hmz : D01.sobolevENorm (m : ℝ) z ≠ ⊤)
    {l : ℝ} (hl : (D01.sobolevENorm 2 z).toReal ≤ 16*l) :
    (A03.outerSobolevENorm (m : ℝ) z z).toReal ≤
      A03.outerTameConst m * (16*l) * (D01.sobolevENorm (m : ℝ) z).toReal := by
  calc
    _ ≤ A03.outerTameConst m *
        ((D01.sobolevENorm 2 z).toReal * (D01.sobolevENorm (m : ℝ) z).toReal) :=
      A04.outerSobolevNormAt_le hm hz h2 hmz
    _ ≤ A03.outerTameConst m * ((16*l) * (D01.sobolevENorm (m : ℝ) z).toReal) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hl ENNReal.toReal_nonneg) (A03.outerTameConst_pos m).le
    _ = _ := by ring

open scoped RealInnerProductSpace in
/-- The algebraic energy assembly and absorption on any real Hilbert carrier.
All PDE/pairing hypotheses remain visible; no classical-level lemma is used. -/
theorem inner_mild_energy {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {G Gt N P L F : H} {ν A l x g b d : ℝ} (hν : 0 < ν) (hx : 0 ≤ x)
    (hd : d = 2 * ⟪G, Gt⟫) (hmom : Gt = ν • L - N - P + F)
    (hlap : ⟪G, L⟫ ≤ -g^2) (hpr : ⟪G, P⟫ = 0)
    (hnl : -⟪G, N⟫ ≤ A*(16*l)*Real.sqrt x*g)
    (hG : ‖G‖ = Real.sqrt x) (hF : ‖F‖ = b) :
    d ≤ 2 * ((A^2/(4*ν)) * (256*l^2) * x + b*Real.sqrt x) :=
  mild_energy_absorption hν hx
    (A04.inner_energy_Rhigh hν.le hd hmom hlap hpr hnl hG hF)

/-- One remaining analytic input: a differentiable scalar squared-energy
ENVELOPE, with a dissipation and the unabsorbed tame bound. It is not required
to equal the squared norm, nor to be differentiable at either endpoint.
Constants are fixed before choosing a window or a mild competitor.

Constructing this envelope (including its norm comparisons) from the actual
regularized word family is not proved here. -/
def FiniteMildEnergy {q : ℕ} (hq : 6 ≤ q) {ν S : ℝ} (hν : 0 < ν)
    (a : SmoothL2Field Space) (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n) (E A : ℝ) : Prop :=
  ∀ (T : ℝ) (hT : 0 ≤ T) (hTS : T ≤ S)
    (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q+1))),
    (∀ t, u t = quadraticDuhamel 1 ν hν hT hTS
      (coefficients 1 hq (sobolevPath F hF q))
      (ordinarySobolev (q+1) a.toLp a.translation_contDiff) u t) →
    ∃ (x : C(Icc (0 : ℝ) T, ℝ)) (d g : ℝ → ℝ),
      (∀ t, 0 ≤ x t) ∧ (∀ t, ‖u t‖ ≤ Real.sqrt (x t)) ∧
      Real.sqrt (x ⟨0, le_rfl, hT⟩) ≤
        E * ‖ordinarySobolev (q+1) a.toLp a.translation_contDiff‖ ∧
      (∀ t ∈ Ioo 0 T, HasDerivAt (extendPath T hT x) (d t) t) ∧
      ∀ t ∈ Ioo 0 T,
        (1/2) * d t + ν * (g t)^2 ≤
          A * (16 * ‖restrictOperator 1 (Nat.succ_le_succ hq)
            (extendPath T hT u t)‖) * Real.sqrt (extendPath T hT x t) * g t +
          (E * ‖sobolevPath F hF (q+1)‖) * Real.sqrt (extendPath T hT x t)

/-- Conditional finite-order result. The single analytic premise is explicit;
the conclusion is exactly `AprioriFamily.MildGronwall`, with C = A²/(4ν). -/
theorem mildGronwall {q : ℕ} (hq : 6 ≤ q) {ν S : ℝ} (hν : 0 < ν)
    (a : SmoothL2Field Space) (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n) {E A : ℝ} (hE : 0 ≤ E)
    (henergy : FiniteMildEnergy hq hν a ha F hF E A) :
    MildGronwall hq hν a ha F hF E (A^2/(4*ν)) := by
  intro T hT hTS u hu
  obtain ⟨x, d, g, hx, hux, hx0, hxd, hineq⟩ := henergy T hT hTS u hu
  let y : C(Icc (0 : ℝ) T, ℝ) := ⟨fun t => Real.sqrt (x t), x.continuous.sqrt⟩
  refine ⟨y, hux, hx0, ?_⟩
  have hxc := extendPath_continuous T hT x
  have huc := extendPath_continuous T hT u
  have hxnn : ∀ t : ℝ, 0 ≤ extendPath T hT x t :=
    fun t => hx (projIcc 0 T hT t)
  have hc : 0 ≤ A^2/(4*ν) := div_nonneg (sq_nonneg A) (by positivity)
  have hk : Continuous (fun s => (A^2/(4*ν)) *
      (256 * ‖restrictOperator 1 (Nat.succ_le_succ hq) (extendPath T hT u s)‖^2)) :=
    continuous_const.mul (continuous_const.mul
      (((restrictOperator 1 (Nat.succ_le_succ hq)).continuous.comp huc).norm.pow 2))
  have hb : 0 ≤ E * ‖sobolevPath F hF (q+1)‖ := mul_nonneg hE (norm_nonneg _)
  have hstep := A04.sqrt_le_primitive_linear hT hxc.continuousOn hk.continuousOn
    (continuousOn_const (c := E * ‖sobolevPath F hF (q+1)‖))
    (fun t _ => hxnn t) (fun t _ => mul_nonneg hc (mul_nonneg (by norm_num) (sq_nonneg _)))
    (fun _ _ => hb) hxd
    (fun t ht => mild_energy_absorption hν (hxnn t) (hineq t ht))
  intro t
  have hh := hstep t.val t.property
  simpa only [extendPath, projIcc_of_mem _ t.property,
    projIcc_of_mem _ (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl, hT⟩),
    ContinuousMap.coe_mk, y] using hh

/-- Family assembly from the one finite-order energy input, with explicit
absorbed constants. This corollary is conditional, not an unconditional closure. -/
theorem hb_of_base' {ν S R₆ : ℝ} (hν : 0 < ν) (hS : 0 ≤ S)
    (a : SmoothL2Field Space) (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n)
    (u₆ : C(Icc (0 : ℝ) S, SobolevSpace 1 7)) (hR : ‖u₆‖ ≤ R₆)
    (h₆ : ∀ t, u₆ t = quadraticDuhamel 1 ν hν hS le_rfl
      (coefficients 1 (le_refl 6) (sobolevPath F hF 6))
      (ordinarySobolev 7 a.toLp a.translation_contDiff) u₆ t)
    (E A : ℕ → ℝ) (hE : ∀ q, 0 ≤ E q)
    (henergy : ∀ q (hq : 6 ≤ q), FiniteMildEnergy hq hν a ha F hF (E q) (A q)) :
    ∀ q (hq : 6 ≤ q), HasAprioriBound hq hν a F hF
      (aprioriRadius a F hF R₆ E (fun q => A q^2/(4*ν)) q) :=
  hb_of_base hν hS a ha F hF u₆ hR h₆ E (fun q => A q^2/(4*ν)) hE
    (fun q => div_nonneg (sq_nonneg _) (by positivity))
    (fun q hq => mildGronwall hq hν a ha F hF (hE q) (henergy q hq))

/-- The same family for angle-invariant competitors. -/
theorem hb_of_base_inv' {ν S R₆ : ℝ} (hν : 0 < ν) (hS : 0 ≤ S)
    (a : SmoothL2Field Space) (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n)
    (u₆ : C(Icc (0 : ℝ) S, SobolevSpace 1 7)) (hR : ‖u₆‖ ≤ R₆)
    (h₆ : ∀ t, u₆ t = quadraticDuhamel 1 ν hν hS le_rfl
      (coefficients 1 (le_refl 6) (sobolevPath F hF 6))
      (ordinarySobolev 7 a.toLp a.translation_contDiff) u₆ t)
    (E A : ℕ → ℝ) (hE : ∀ q, 0 ≤ E q)
    (henergy : ∀ q (hq : 6 ≤ q), FiniteMildEnergy hq hν a ha F hF (E q) (A q)) :
    ∀ q (hq : 6 ≤ q), HasAprioriBoundInv hq hν a F hF
      (aprioriRadius a F hF R₆ E (fun q => A q^2/(4*ν)) q) :=
  fun q hq => (hb_of_base' hν hS a ha F hF u₆ hR h₆ E A hE henergy q hq).toInv

end NSFormalization.Section4.A01
