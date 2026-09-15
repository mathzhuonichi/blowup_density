import NSFormalization.Section4.A01.Horizon

/-!
# A01 residual row (iv): invariant a-priori bounds

Route β closes. The bound is required only for angle-invariant mild solutions.
The continuation induction from `ContinuationInvariant` already carries this property;
we supply it at both uses of the bound (restart and final horizon). No unrestricted
uniqueness or contraction hypothesis on the prescribed horizon is needed.
-/

noncomputable section

namespace NSFormalization.Section4.A01

open Set MeasureTheory EulerSmoothLimit EulerLpTranslation EulerMeanOrdinaryLift
open EulerMeanSmoothRepresentative EulerCylinderSobolevSpace EulerLiftedGradientSpace
open EulerSmoothFieldSobolevTime EulerQuadraticSource EulerSobolevHeat EulerVolterraConvolution
open NSFormalization.Source.ForcedCylinderLocal NSFormalization.Source.OrdinaryCylinderDescent
open EulerBoundedMildContinuation EulerDivergenceFreeHeat EulerUniformHeatLocal
open EulerTimePathGluing EulerQuadraticMildPasting
open scoped Topology ContDiff

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-- Uniform bound over invariant Duhamel solutions on every subwindow. -/
def HasAprioriBoundInv {q : ℕ} (hq : 6 ≤ q) {ν S : ℝ} (hν : 0 < ν)
    (a : SmoothL2Field Space)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space) (hF : ∀ n, Continuous fun t => (F t).jetLp n)
    (R : ℝ) : Prop :=
  ∀ (T : ℝ) (hT : 0 ≤ T) (hTS : T ≤ S)
      (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q + 1))),
      (∀ t, u t = quadraticDuhamel 1 ν hν hT hTS
          (coefficients 1 hq (sobolevPath F hF q))
          (ordinarySobolev (q + 1) a.toLp a.translation_contDiff) u t) →
      (∀ (θ : AddCircle (1 : ℝ)) t,
        sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t) → ‖u‖ ≤ R

/-- An unrestricted a-priori bound also bounds invariant solutions. -/
theorem HasAprioriBound.toInv {q : ℕ} (hq : 6 ≤ q) {ν S : ℝ} (hν : 0 < ν)
    (a : SmoothL2Field Space)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space) (hF : ∀ n, Continuous fun t => (F t).jetLp n)
    (R : ℝ) (hb : HasAprioriBound hq hν a F hF R) :
    HasAprioriBoundInv hq hν a F hF R := by
  intro T hT hTS u hsol _hinv
  exact hb T hT hTS u hsol

/-- Core mild continuation using only the invariant-solution bound.
This is the invariance-carrying window induction underlying the full seven-clause export. -/
theorem forced_global_mild_core_of_boundInv {q : ℕ} (hq : 6 ≤ q) {ν S R : ℝ}
    (hν : 0 < ν) (hS : 0 < S) (hR : 0 ≤ R)
    (a : SmoothL2Field Space)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space) (hF : ∀ n, Continuous fun t => (F t).jetLp n)
    (hu₀ : ‖ordinarySobolev (q + 1) a.toLp a.translation_contDiff‖ ≤ R)
    (hbound : HasAprioriBoundInv hq hν a F hF R) :
    ∃ u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)),
      ‖u‖ ≤ R ∧
      u ⟨0, le_rfl, hS.le⟩ = ordinarySobolev (q + 1) a.toLp a.translation_contDiff ∧
      (∀ t, u t = quadraticDuhamel 1 ν hν hS.le le_rfl
        (coefficients 1 hq (sobolevPath F hF q))
        (ordinarySobolev (q + 1) a.toLp a.translation_contDiff) u t) ∧
      ∀ (θ : AddCircle (1 : ℝ)) t, sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t := by
  set u₀ := ordinarySobolev (q + 1) a.toLp a.translation_contDiff with hu₀def
  set C := coefficients 1 hq (sobolevPath F hF q) with hCdef
  have hu₀inv : ∀ θ : AddCircle (1 : ℝ), sobolevTranslation 1 (q + 1) (0, θ) u₀ = u₀ :=
    fun θ => ordinarySobolev_angle (q + 1) a.toLp a.translation_contDiff θ
  obtain ⟨δ, hδ, _hδS, hlocal⟩ := exists_uniform_restart_time_invariant hq hν hS hR F hF
  have hind : ∀ n : ℕ, ∃ (a' : ℝ) (ha' : 0 ≤ a') (ha'S : a' ≤ S),
      min ((n : ℝ) * δ) S ≤ a' ∧
      ∃ u : C(Icc (0 : ℝ) a', SobolevSpace 1 (q + 1)),
        (∀ t, u t = quadraticDuhamel 1 ν hν ha' ha'S C u₀ u t) ∧
        ∀ (θ : AddCircle (1 : ℝ)) t, sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t := by
    intro n
    induction n with
    | zero =>
      obtain ⟨u, _, _, hsol, hinvu⟩ := hlocal 0 0 le_rfl le_rfl (by linarith) hδ.le u₀ hu₀ hu₀inv
      refine ⟨0, le_rfl, hS.le, ?_, u, ?_, hinvu⟩
      · simpa only [Nat.cast_zero, zero_mul] using min_le_left (0 : ℝ) S
      · exact (quadratic_mild_window_iff 1 ν hν le_rfl hS.le C u₀ u).mpr hsol
    | succ n ih =>
      obtain ⟨a', ha', ha'S, hgrid, u, hsolu, hinvu⟩ := ih
      let b := min δ (S - a')
      have hb : 0 ≤ b := le_min hδ.le (sub_nonneg.mpr ha'S)
      have hbδ : b ≤ δ := min_le_left _ _
      have habS : a' + b ≤ S := by have h := min_le_right δ (S - a'); dsimp [b]; linarith
      have hu : ‖u ⟨a', ha', le_rfl⟩‖ ≤ R :=
        (u.norm_coe_le_norm _).trans (hbound a' ha' ha'S u hsolu hinvu)
      have hdatinv : ∀ θ : AddCircle (1 : ℝ),
          sobolevTranslation 1 (q + 1) (0, θ) (u ⟨a', ha', le_rfl⟩) = u ⟨a', ha', le_rfl⟩ :=
        fun θ => hinvu θ _
      obtain ⟨v, _, hv0, hsolv, hinvv⟩ :=
        hlocal a' b ha' hb habS hbδ (u ⟨a', ha', le_rfl⟩) hu hdatinv
      refine ⟨a' + b, add_nonneg ha' hb, habS, advance_grid S δ a' hδ.le n hgrid,
        gluePath a' b ha' hb u v hv0.symm, ?_, ?_⟩
      · exact glue_quadratic_mild 1 ν hν C a' b ha' hb ha'S habS u v hv0.symm u₀ hsolu hsolv
      · exact gluePath_invariant ha' hb u v hv0.symm hinvu hinvv
  obtain ⟨n, hn⟩ := exists_nat_ge (S / δ)
  have hN : S ≤ (n : ℝ) * δ := (div_le_iff₀ hδ).mp hn
  obtain ⟨a', ha', ha'S, hgrid, u, hsol, hinvu⟩ := hind n
  have hSa : S ≤ a' := by simpa only [min_eq_right hN] using hgrid
  have he : a' = S := le_antisymm ha'S hSa
  subst a'
  refine ⟨u, hbound S ha' ha'S u hsol hinvu, ?_, hsol, hinvu⟩
  have hz := hsol ⟨0, le_rfl, hS.le⟩
  simpa only [quadraticDuhamel, mul_zero, Real.toNNReal_zero, heatOperator_zero,
    intervalIntegral.integral_same, add_zero] using hz

/-- Full continuation from the invariant-solution bound, with the same seven-clause conclusion as
`forced_global_of_bound_unconditional`. -/
theorem forced_global_of_boundInv {q : ℕ} (hq : 6 ≤ q) {ν S R : ℝ}
    (hν : 0 < ν) (hS : 0 < S) (hR : 0 ≤ R)
    (a : SmoothL2Field Space) (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space) (hF : ∀ n, Continuous fun t => (F t).jetLp n)
    (hu₀ : ‖ordinarySobolev (q + 1) a.toLp a.translation_contDiff‖ ≤ R)
    (hbound : HasAprioriBoundInv hq hν a F hF R) :
    ∃ (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)))
      (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2)),
        ‖u‖ ≤ R ∧
        u ⟨0, le_rfl, hS.le⟩ = ordinarySobolev (q + 1) a.toLp a.translation_contDiff ∧
        U ⟨0, le_rfl, hS.le⟩ = a.toLp ∧
        (∀ t, ordinaryLift (U t) = value 1 (u t)) ∧
        (∀ t, value 1 (u t) ∈ divergenceFreeSpace 1 1 0) ∧
        (∀ t, u t = quadraticDuhamel 1 ν hν hS.le le_rfl
          (coefficients 1 hq (sobolevPath F hF q))
          (ordinarySobolev (q + 1) a.toLp a.translation_contDiff) u t) ∧
        ∀ (θ : AddCircle (1 : ℝ)) t, sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t := by
  obtain ⟨u, hu, hi, hm, hinvu⟩ :=
    forced_global_mild_core_of_boundInv hq hν hS hR a F hF hu₀ hbound
  have hd := forced_mild_divergenceFree hq hν hS a ha F hF u hm
  obtain ⟨U, hU0, hUl⟩ := forced_ordinary_descent hq hS a u hi hinvu
  exact ⟨u, U, hu, hi, hU0, hUl, hd, hm, hinvu⟩

/-- Full prescribed-horizon consumer from the invariant-solution bound. -/
theorem localTheory_on_prescribed_horizon_of_boundInv {q : ℕ} (hq : 6 ≤ q) {ν S R : ℝ}
    (hν : 0 < ν) (hS : 0 < S) (hR : 0 ≤ R)
    (a : SmoothL2Field Space) (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space) (hF : ∀ n, Continuous fun t => (F t).jetLp n)
    (hu₀ : ‖ordinarySobolev (q + 1) a.toLp a.translation_contDiff‖ ≤ R)
    (hbound : HasAprioriBoundInv hq hν a F hF R) :
    ∃ (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)))
      (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2)),
        ‖u‖ ≤ R ∧
        u ⟨0, le_rfl, hS.le⟩ = ordinarySobolev (q + 1) a.toLp a.translation_contDiff ∧
        U ⟨0, le_rfl, hS.le⟩ = a.toLp ∧
        (∀ t, ordinaryLift (U t) = value 1 (u t)) ∧
        (∀ t, value 1 (u t) ∈ divergenceFreeSpace 1 1 0) ∧
        (∀ t, u t = quadraticDuhamel 1 ν hν hS.le le_rfl
          (coefficients 1 hq (sobolevPath F hF q))
          (ordinarySobolev (q + 1) a.toLp a.translation_contDiff) u t) ∧
        ∀ (θ : AddCircle (1 : ℝ)) t, sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t :=
  forced_global_of_boundInv hq hν hS hR a ha F hF hu₀ hbound

end NSFormalization.Section4.A01
