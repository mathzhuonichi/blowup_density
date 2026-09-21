import NSFormalization.Section4.A01.MildUniqueness
import NSFormalization.Section4.A01.GronwallEndpoint

/-! The base-order route. No all-order solution constructor is used. -/
noncomputable section
namespace NSFormalization.Section4.A01
open Set MeasureTheory EulerSmoothLimit EulerLpTranslation EulerMeanOrdinaryLift
open EulerMeanSmoothRepresentative EulerCylinderSobolevSpace EulerLiftedGradientSpace
open EulerSmoothFieldSobolevTime EulerQuadraticSource EulerSobolevHeat EulerVolterraConvolution
open NSFormalization.Source.ForcedCylinderLocal NSFormalization.Source.OrdinaryCylinderDescent
open NSFormalization.Section4.A04 (sobolevNormAt)
open scoped Topology ContDiff
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-- Restricting time in a fixed point preserves the Duhamel equation. -/
theorem quadratic_mild_prefix {q : ℕ} {ν S T : ℝ} (hν : 0 < ν)
    (hT : 0 ≤ T) (hTS : T ≤ S)
    (C : Coefficients (Icc (0 : ℝ) S) (SobolevSpace 1 (q+1)) (SobolevSpace 1 q))
    (a : SobolevSpace 1 (q+1)) (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q+1)))
    (hu : ∀ t, u t = quadraticDuhamel 1 ν hν (hT.trans hTS) le_rfl C a u t) :
    ∀ t, (u.comp (timeInclusion hTS)) t = quadraticDuhamel 1 ν hν hT hTS C a
      (u.comp (timeInclusion hTS)) t := by
  intro t
  rw [ContinuousMap.comp_apply, hu]
  unfold quadraticDuhamel
  apply congrArg (fun z => heatOperator 1 (q+1) (2*ν*t.val).toNNReal a + z)
  apply intervalIntegral.integral_congr
  intro r hr
  dsimp only [timeInclusion, ContinuousMap.coe_mk] at hr ⊢
  rw [uIcc_of_le t.property.1] at hr
  have hm : 0 ≤ t.val - r ∧ t.val - r ≤ T := by
    constructor <;> linarith [t.property.2, hr.1, hr.2]
  rw [projIcc_of_mem _ hm, projIcc_of_mem _ ⟨hm.1, hm.2.trans hTS⟩]
  rfl

/-- Uniqueness also covers the singleton window, where the integral is zero. -/
theorem quadratic_mild_unique_window {q : ℕ} {ν S T : ℝ} (hν : 0 < ν)
    (hT : 0 ≤ T) (hTS : T ≤ S)
    (C : Coefficients (Icc (0 : ℝ) S) (SobolevSpace 1 (q+1)) (SobolevSpace 1 q))
    (a : SobolevSpace 1 (q+1)) (u v : C(Icc (0 : ℝ) T, SobolevSpace 1 (q+1)))
    (hu : ∀ t, u t = quadraticDuhamel 1 ν hν hT hTS C a u t)
    (hv : ∀ t, v t = quadraticDuhamel 1 ν hν hT hTS C a v t) : u = v := by
  rcases hT.eq_or_lt with he | hp
  · have hzero : T = 0 := he.symm
    subst T
    apply ContinuousMap.ext
    intro t
    have ht : t.val = 0 := le_antisymm t.property.2 t.property.1
    rw [hu, hv]
    simp only [quadraticDuhamel, ht, intervalIntegral.integral_same]
  · exact quadratic_mild_unique hν hp (C.comp (timeInclusion hTS)) a u v hu hv

/-- Any base-order competitor is the restriction of the chosen base solution. -/
theorem base_identification {ν S T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) (hTS : T ≤ S)
    (a : SmoothL2Field Space) (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n)
    (u₆ : C(Icc (0 : ℝ) S, SobolevSpace 1 7))
    (h₆ : ∀ t, u₆ t = quadraticDuhamel 1 ν hν (hT.trans hTS) le_rfl
      (coefficients 1 (le_refl 6) (sobolevPath F hF 6))
      (ordinarySobolev 7 a.toLp a.translation_contDiff) u₆ t)
    (u : C(Icc (0 : ℝ) T, SobolevSpace 1 7))
    (hu : ∀ t, u t = quadraticDuhamel 1 ν hν hT hTS
      (coefficients 1 (le_refl 6) (sobolevPath F hF 6))
      (ordinarySobolev 7 a.toLp a.translation_contDiff) u t) :
    u = u₆.comp (timeInclusion hTS) :=
  quadratic_mild_unique_window hν hT hTS _ _ u _ hu
    (quadratic_mild_prefix hν hT hTS _ _ u₆ h₆)

/-- A single bounded base solution gives the unrestricted base a-priori bound. -/
theorem hasAprioriBound_base {ν S R₆ : ℝ} (hν : 0 < ν) (hS : 0 ≤ S)
    (a : SmoothL2Field Space) (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n)
    (u₆ : C(Icc (0 : ℝ) S, SobolevSpace 1 7)) (hR : ‖u₆‖ ≤ R₆)
    (h₆ : ∀ t, u₆ t = quadraticDuhamel 1 ν hν hS le_rfl
      (coefficients 1 (le_refl 6) (sobolevPath F hF 6))
      (ordinarySobolev 7 a.toLp a.translation_contDiff) u₆ t) :
    HasAprioriBound (le_refl 6) hν a F hF R₆ := by
  intro T hT hTS u hu
  rw [base_identification hν hT hTS a F hF u₆ h₆ u hu]
  apply (ContinuousMap.norm_le _ ((norm_nonneg _).trans hR)).mpr
  intro t
  exact (u₆.norm_coe_le_norm _).trans hR

/-- Lowering on a subwindow identifies every higher-order competitor with the base path. -/
theorem lower_identification {q : ℕ} (hq : 6 ≤ q) {ν S T : ℝ}
    (hν : 0 < ν) (hT : 0 ≤ T) (hTS : T ≤ S)
    (a : SmoothL2Field Space) (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n)
    (u₆ : C(Icc (0 : ℝ) S, SobolevSpace 1 7))
    (h₆ : ∀ t, u₆ t = quadraticDuhamel 1 ν hν (hT.trans hTS) le_rfl
      (coefficients 1 (le_refl 6) (sobolevPath F hF 6))
      (ordinarySobolev 7 a.toLp a.translation_contDiff) u₆ t)
    (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q+1)))
    (hu : ∀ t, u t = quadraticDuhamel 1 ν hν hT hTS
      (coefficients 1 hq (sobolevPath F hF q))
      (ordinarySobolev (q+1) a.toLp a.translation_contDiff) u t) :
    (restrictOperator 1 (Nat.succ_le_succ hq)).compLeftContinuous ℝ _ u =
      u₆.comp (timeInclusion hTS) := by
  have hl := lower_forced_mild hq (le_refl 6) hq hν hT a
    (fun t => F (timeInclusion hTS t))
    (fun n => (hF n).comp (timeInclusion hTS).continuous) u hu
  exact base_identification hν hT hTS a F hF u₆ h₆ _ hl


/-- The vendor supplies a positive base horizon and its radius before any higher order. -/
theorem exists_base_apriori {ν S : ℝ} (hν : 0 < ν) (hS : 0 < S)
    (a : SmoothL2Field Space) (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n) :
    ∃ (T : ℝ) (_hT : 0 < T) (hTS : T ≤ S),
      HasAprioriBound (le_refl 6) hν a (fun t => F (timeInclusion hTS t))
        (fun n => (hF n).comp (timeInclusion hTS).continuous)
        (‖ordinarySobolev 7 a.toLp a.translation_contDiff‖ + 1) := by
  obtain ⟨T, hT, hTS, u, hR, _, hu⟩ := exists_local_quadratic_mild 1 6 ν hν S hS
    (ordinarySobolev 7 a.toLp a.translation_contDiff)
    (coefficients 1 (le_refl 6) (sobolevPath F hF 6))
  exact ⟨T, hT, hTS, hasAprioriBound_base hν hT.le a _ _ u hR hu⟩

/-- Physical H² cap transferred through an identified lower path, with no high-order radius. -/
theorem h2_cap_transfer {q : ℕ} (hq : 6 ≤ q) {S T R₆ : ℝ}
    (hTS : T ≤ S) (u₆ : C(Icc (0 : ℝ) S, SobolevSpace 1 7)) (hR : ‖u₆‖ ≤ R₆)
    (hi : ∀ (θ : AddCircle (1 : ℝ)) t, sobolevTranslation 1 7 (0, θ) (u₆ t) = u₆ t)
    (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q+1)))
    (hl : (restrictOperator 1 (Nat.succ_le_succ hq)).compLeftContinuous ℝ _ u =
      u₆.comp (timeInclusion hTS))
    (U : C(Icc (0 : ℝ) T, EulerMeanSolenoidal.L2))
    (hU : ∀ t, ordinaryLift (U t) = value 1 (u t))
    (v : A02.SpaceTimeField)
    (hslice : ∀ t : Icc (0 : ℝ) T, (fun x => v (↑t, x)) =ᵐ[volume] ⇑(U t))
    (hcont : ContinuousOn (fun s => sobolevNormAt 2 v s) (Ico (0 : ℝ) T)) :
    ∀ t ∈ Icc (0 : ℝ) T,
      (∫ s in (0 : ℝ)..t, sobolevNormAt 2 v s ^ 2) ≤ 256 * R₆ ^ 2 * T := by
  apply kbnd_of_sup_bound_Icc_endpoint (q := 6) (u₆.comp (timeInclusion hTS)) U
    (fun θ t => hi θ _) _ (by norm_num) v hslice _ hcont
  · intro t
    rw [← hl]
    exact hU t
  · apply (ContinuousMap.norm_le _ ((norm_nonneg _).trans hR)).mpr
    exact fun t => (u₆.norm_coe_le_norm _).trans hR

/-- A continuous scalar energy envelope for a finite-order mild solution.
The one unproved PDE input is the integrated high-energy inequality, including
its norm comparisons. `E` absorbs the fixed equivalence constants; `C` is the
energy constant (depending on the order and viscosity). These are fixed before
all windows and competitors. The force is measured at order `q+1`.
This is a restriction of the usual finite-order energy estimate, not an
all-order smooth-solution constructor. -/
def MildGronwall {q : ℕ} (hq : 6 ≤ q) {ν S : ℝ} (hν : 0 < ν)
    (a : SmoothL2Field Space) (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n) (E C : ℝ) : Prop :=
  ∀ (T : ℝ) (hT : 0 ≤ T) (hTS : T ≤ S)
    (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q+1))),
    (∀ t, u t = quadraticDuhamel 1 ν hν hT hTS
      (coefficients 1 hq (sobolevPath F hF q))
      (ordinarySobolev (q+1) a.toLp a.translation_contDiff) u t) →
    ∃ y : C(Icc (0 : ℝ) T, ℝ),
      (∀ t, ‖u t‖ ≤ y t) ∧
      y ⟨0, le_rfl, hT⟩ ≤ E * ‖ordinarySobolev (q+1) a.toLp a.translation_contDiff‖ ∧
      ∀ t : Icc (0 : ℝ) T,
        y t ≤ y ⟨0, le_rfl, hT⟩ + ∫ s in (0 : ℝ)..t.val,
          (C * (256 * ‖restrictOperator 1 (Nat.succ_le_succ hq)
            (extendPath T hT u s)‖ ^ 2) * extendPath T hT y s +
            E * ‖sobolevPath F hF (q+1)‖)

/-- Explicit uniform radius; the force integral is bounded by horizon times its sup norm. -/
def aprioriRadius {S : ℝ} (a : SmoothL2Field Space)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n)
    (R₆ : ℝ) (E C : ℕ → ℝ) (q : ℕ) : ℝ :=
  E q * (‖ordinarySobolev (q+1) a.toLp a.translation_contDiff‖ +
    S * ‖sobolevPath F hF (q+1)‖) * Real.exp (C q * (256 * R₆^2 * S))


-- The dependent orders, extended paths, and scalar Grönwall application require extra elaboration.
set_option maxHeartbeats 400000 in
/-- The all-order radius family follows from a single bounded base solution and
one finite-order energy-envelope input per order. -/
theorem hb_of_base {ν S R₆ : ℝ} (hν : 0 < ν) (hS : 0 ≤ S)
    (a : SmoothL2Field Space) (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n)
    (u₆ : C(Icc (0 : ℝ) S, SobolevSpace 1 7)) (hR : ‖u₆‖ ≤ R₆)
    (h₆ : ∀ t, u₆ t = quadraticDuhamel 1 ν hν hS le_rfl
      (coefficients 1 (le_refl 6) (sobolevPath F hF 6))
      (ordinarySobolev 7 a.toLp a.translation_contDiff) u₆ t)
    (E C : ℕ → ℝ) (hE : ∀ q, 0 ≤ E q) (hC : ∀ q, 0 ≤ C q)
    (hMG : ∀ q (hq : 6 ≤ q), MildGronwall hq hν a ha F hF (E q) (C q)) :
    ∀ q (hq : 6 ≤ q), HasAprioriBound hq hν a F hF (aprioriRadius a F hF R₆ E C q) := by
  intro q hq T hT hTS u hu
  obtain ⟨y, hyu, hy0, hstep⟩ := hMG q hq T hT hTS u hu
  let Y := extendPath T hT y
  let k := fun s => 256 * ‖restrictOperator 1 (Nat.succ_le_succ hq)
    (extendPath T hT u s)‖ ^ 2
  let B := E q * ‖sobolevPath F hF (q+1)‖
  have hB : 0 ≤ B := mul_nonneg (hE q) (norm_nonneg _)
  have hY : Continuous Y := extendPath_continuous T hT y
  have hk : Continuous k := continuous_const.mul
    (((restrictOperator 1 (Nat.succ_le_succ hq)).continuous.comp
      (extendPath_continuous T hT u)).norm.pow 2)
  have hext (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : Y t = y ⟨t, ht⟩ := by
    dsimp [Y, extendPath]
    rw [projIcc_of_mem _ ht]
  have hzero : Y 0 = y ⟨0, le_rfl, hT⟩ := hext 0 ⟨le_rfl, hT⟩
  have hG := A04.gronwall_integral_mul hT (hC q) hY.continuousOn hk.continuousOn
    (b := fun _ => B) continuousOn_const (fun s _ => by dsimp [k]; positivity)
    (fun _ _ => hB) (fun t ht => by
      rw [hext t ht, hzero]
      exact hstep ⟨t, ht⟩)
  have hl := lower_identification hq hν hT hTS a F hF u₆ h₆ u hu
  have hRnn : 0 ≤ R₆ := (norm_nonneg _).trans hR
  have hkn (s : ℝ) : k s ≤ 256 * R₆^2 := by
    have hv := congrArg (fun v : C(Icc (0 : ℝ) T, SobolevSpace 1 7) =>
      v (projIcc 0 T hT s)) hl
    have hn : ‖restrictOperator 1 (Nat.succ_le_succ hq) (extendPath T hT u s)‖ ≤ R₆ := by
      change ‖((restrictOperator 1 (Nat.succ_le_succ hq)).compLeftContinuous ℝ _ u)
        (projIcc 0 T hT s)‖ ≤ R₆
      rw [hv]
      exact (u₆.norm_coe_le_norm _).trans hR
    exact mul_le_mul_of_nonneg_left (sq_le_sq₀ (norm_nonneg _) hRnn |>.mpr hn) (by norm_num)
  have hcap (t : Icc (0 : ℝ) T) : (∫ s in (0 : ℝ)..t.val, k s) ≤ 256 * R₆^2 * S := by
    calc
      _ ≤ ∫ _s in (0 : ℝ)..t.val, (256 * R₆^2) :=
        intervalIntegral.integral_mono_on t.property.1 (hk.intervalIntegrable 0 t.val)
          intervalIntegrable_const (fun s _ => hkn s)
      _ = 256 * R₆^2 * t.val := by rw [intervalIntegral.integral_const]; simp; ring
      _ ≤ 256 * R₆^2 * S := mul_le_mul_of_nonneg_left (t.property.2.trans hTS) (by positivity)
  have hAn : 0 ≤ E q * (‖ordinarySobolev (q+1) a.toLp a.translation_contDiff‖ +
      S * ‖sobolevPath F hF (q+1)‖) :=
    mul_nonneg (hE q) (add_nonneg (norm_nonneg _) (mul_nonneg hS (norm_nonneg _)))
  apply (ContinuousMap.norm_le _ (mul_nonneg hAn (Real.exp_pos _).le)).mpr
  intro t
  have hg := hG t.val t.property
  rw [hext t.val t.property, hzero, intervalIntegral.integral_const] at hg
  simp only [sub_zero, smul_eq_mul] at hg
  have hbase : y ⟨0, le_rfl, hT⟩ + t.val * B ≤
      E q * (‖ordinarySobolev (q+1) a.toLp a.translation_contDiff‖ +
        S * ‖sobolevPath F hF (q+1)‖) := by
    calc
      _ ≤ E q * ‖ordinarySobolev (q+1) a.toLp a.translation_contDiff‖ + S * B :=
        add_le_add hy0 (mul_le_mul_of_nonneg_right (t.property.2.trans hTS) hB)
      _ = _ := by dsimp [B]; ring
  exact (hyu t).trans (hg.trans ((mul_le_mul_of_nonneg_right hbase (Real.exp_pos _).le).trans
    (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hcap t) (hC q))) hAn)))

/-- The invariant variant is an immediate restriction of the unrestricted family. -/
theorem hb_of_base_inv {ν S R₆ : ℝ} (hν : 0 < ν) (hS : 0 ≤ S)
    (a : SmoothL2Field Space) (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n)
    (u₆ : C(Icc (0 : ℝ) S, SobolevSpace 1 7)) (hR : ‖u₆‖ ≤ R₆)
    (h₆ : ∀ t, u₆ t = quadraticDuhamel 1 ν hν hS le_rfl
      (coefficients 1 (le_refl 6) (sobolevPath F hF 6))
      (ordinarySobolev 7 a.toLp a.translation_contDiff) u₆ t)
    (E C : ℕ → ℝ) (hE : ∀ q, 0 ≤ E q) (hC : ∀ q, 0 ≤ C q)
    (hMG : ∀ q (hq : 6 ≤ q), MildGronwall hq hν a ha F hF (E q) (C q)) :
    ∀ q (hq : 6 ≤ q), HasAprioriBoundInv hq hν a F hF (aprioriRadius a F hF R₆ E C q) :=
  fun q hq => HasAprioriBound.toInv hq hν a F hF _
    (hb_of_base hν hS a ha F hF u₆ hR h₆ E C hE hC hMG q hq)

end NSFormalization.Section4.A01
