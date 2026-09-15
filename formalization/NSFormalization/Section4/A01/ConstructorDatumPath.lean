import NSFormalization.Section4.A01.ConstructorPieces
import NSFormalization.Section4.A01.OrderTwoCap
import NSFormalization.Section4.D01.OrderZeroAlgebra

/-!
# Continuous finite-order angular datum paths from cylinder paths

The full-order weak derivative descent carries the cylinder norm bound. Applied to
cylinder differences, it controls angular datum differences and proves continuity
at every available order, without a smooth representative or time derivatives.
-/

noncomputable section
namespace NSFormalization.Section4.A01

open Set MeasureTheory Filter Topology
open NSFormalization.Section4.D01
open EulerPressureSpatialRegularity
open NSFormalization.Paper3 (RealVectorSobolev)
open NavierStokes.ProblemStatement (Space)
open EulerMeanOrdinaryLift EulerCylinderSobolevSpace EulerLiftedGradientSpace
  EulerCylinderSobolev EulerLpTranslation

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-- The uniform cylinder norm bounds every descended derivative, including top order. -/
theorem hasWeakDerivsL2Bound_of_word_full {q : ℕ} (u : SobolevSpace 1 (q + 1))
    (hu : ∀ θ : AddCircle (1 : ℝ), sobolevTranslation 1 (q + 1) (0, θ) u = u) :
    ∀ (m n : ℕ) (hn : n ≤ q + 1) (_hnm : n + m ≤ q + 1) (w : Fin n → Fin 3)
      (Zw : EulerMeanSolenoidal.L2),
      ordinaryLift Zw = word 1 u hn (fun i => (w i).succ) →
      HasWeakDerivsL2Bound (⇑Zw) (‖u‖ ^ 2) m
  | 0, _n, hn, _hnm, w, Zw, hZw => ⟨Lp.memLp Zw, eLpNorm_descend_le u hn (fun i => (w i).succ) Zw hZw⟩
  | (k + 1), n, hn, hnm, w, Zw, hZw => by
      refine ⟨⟨Lp.memLp Zw, eLpNorm_descend_le u hn (fun i => (w i).succ) Zw hZw⟩, fun j => ?_⟩
      have hlt : n < q + 1 := by omega
      have hn1 : n + 1 ≤ q + 1 := by omega
      obtain ⟨Zc, hZc⟩ := word_descent_ae_top u hu (n + 1) hn1 (Fin.cons j w)
      have hcons : (fun i : Fin (n + 1) => ((Fin.cons j w : Fin (n + 1) → Fin 3) i).succ) =
          Fin.cons j.succ (fun i => (w i).succ) := by
        funext i
        refine Fin.cases ?_ ?_ i
        · rfl
        · intro k; rfl
      refine ⟨⇑Zc, ?_, ?_⟩
      · exact hasWeakDerivsL2Bound_of_word_full u hu k (n + 1) hn1 (by omega)
          (Fin.cons j w) Zc hZc
      · intro i ψ
        have hderiv := word_hasDerivAt 1 u hlt (fun i => (w i).succ) j.succ
        rw [hcons] at hZc
        rw [← hZw, ← hZc] at hderiv
        exact weakDeriv_pairing_of_lift_hasDerivAt j Zw Zc hderiv i ψ

/-- The ordinary carrier has weak derivatives at every available cylinder order. -/
theorem hasWeakDerivsL2Bound_of_cylinder_full {q : ℕ} (u : SobolevSpace 1 (q + 1))
    (hu : ∀ θ : AddCircle (1 : ℝ), sobolevTranslation 1 (q + 1) (0, θ) u = u)
    (U : EulerMeanSolenoidal.L2) (hU : ordinaryLift U = value 1 u)
    (m : ℕ) (hm : m ≤ q + 1) : HasWeakDerivsL2Bound (⇑U) (‖u‖ ^ 2) m := by
  refine hasWeakDerivsL2Bound_of_word_full u hu m 0 (Nat.zero_le _) (by omega) Fin.elim0 U ?_
  have hempty : (fun i : Fin 0 => (Fin.elim0 i : Fin 3).succ) =
      (Fin.elim0 : Fin 0 → Fin 4) := Subsingleton.elim _ _
  rw [hempty, hU]
  rfl

/-- Datum differences are controlled by cylinder differences at every available order. -/
theorem norm_datum_sub_sq_le_of_cylinder {q m : ℕ}
    (u v : SobolevSpace 1 (q + 1))
    (hu : ∀ θ : AddCircle (1 : ℝ), sobolevTranslation 1 (q + 1) (0, θ) u = u)
    (hv : ∀ θ : AddCircle (1 : ℝ), sobolevTranslation 1 (q + 1) (0, θ) v = v)
    (U V : EulerMeanSolenoidal.L2)
    (hU : ordinaryLift U = value 1 u) (hV : ordinaryLift V = value 1 v)
    (hm : m ≤ q + 1) (A B : RealVectorSobolev (m : ℝ))
    (hA : D01.IsSobolevDatum (m : ℝ) (⇑U) A)
    (hB : D01.IsSobolevDatum (m : ℝ) (⇑V) B) :
    ‖A - B‖ ^ 2 ≤ (4 : ℝ) ^ m * ‖u - v‖ ^ 2 := by
  have huv : ∀ θ : AddCircle (1 : ℝ),
      sobolevTranslation 1 (q + 1) (0, θ) (u - v) = u - v := by
    intro θ
    rw [map_sub, hu θ, hv θ]
  have hUV : ordinaryLift (U - V) = value 1 (u - v) := by
    rw [map_sub, hU, hV]
    rfl
  have hbnd := hasWeakDerivsL2Bound_of_cylinder_full (u - v) huv (U - V) hUV m hm
  have hsub := D01.isSobolevDatum_sub
    (schwartzPairable_of_memLp (fun i => memLp_component (Lp.memLp U) i))
    (schwartzPairable_of_memLp (fun i => memLp_component (Lp.memLp V) i)) hA hB
  have hdat : D01.IsSobolevDatum (m : ℝ) (⇑(U - V)) (A - B) :=
    IsSobolevDatum.congr_field hsub (Lp.coeFn_sub U V).symm
  exact norm_isSobolevDatum_le_of_memLp_derivs_sharp m _ _ hbnd _ hdat

/-- Any choice of the finite-order data along a continuous cylinder path is continuous. -/
theorem datum_path_continuous_of_cylinder {q m : ℕ} {S : ℝ}
    (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)))
    (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2))
    (hu : ∀ (θ : AddCircle (1 : ℝ)) t, sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t)
    (hU : ∀ t, ordinaryLift (U t) = value 1 (u t))
    (hm : m ≤ q + 1) (A : Icc (0 : ℝ) S → RealVectorSobolev (m : ℝ))
    (hA : ∀ t, D01.IsSobolevDatum (m : ℝ) (⇑(U t)) (A t)) : Continuous A := by
  rw [continuous_iff_continuousAt]
  intro t₀
  have hbndcont : Continuous (fun t : Icc (0 : ℝ) S =>
      Real.sqrt ((4 : ℝ) ^ m * ‖u t - u t₀‖ ^ 2)) :=
    Real.continuous_sqrt.comp (continuous_const.mul
      ((u.continuous.sub continuous_const).norm.pow 2))
  have hcont0 : Tendsto (fun t : Icc (0 : ℝ) S =>
      Real.sqrt ((4 : ℝ) ^ m * ‖u t - u t₀‖ ^ 2)) (𝓝 t₀) (𝓝 0) := by
    simpa using hbndcont.tendsto t₀
  have hsub : Tendsto (fun t => A t - A t₀) (𝓝 t₀) (𝓝 0) := by
    refine squeeze_zero_norm (fun t => ?_) hcont0
    rw [← Real.sqrt_sq (norm_nonneg _)]
    exact Real.sqrt_le_sqrt (norm_datum_sub_sq_le_of_cylinder (u t) (u t₀)
      (fun θ => hu θ t) (fun θ => hu θ t₀) (U t) (U t₀) (hU t) (hU t₀)
      hm (A t) (A t₀) (hA t) (hA t₀))
  exact tendsto_sub_nhds_zero_iff.mp hsub

/-- Construct the continuous angular datum path through every available finite order. -/
theorem exists_continuous_datum_path_of_cylinder {q : ℕ} {S : ℝ}
    (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)))
    (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2))
    (hu : ∀ (θ : AddCircle (1 : ℝ)) t, sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t)
    (hU : ∀ t, ordinaryLift (U t) = value 1 (u t))
    {m : ℕ} (hm : m ≤ q + 1) :
    ∃ A : C(Icc (0 : ℝ) S, RealVectorSobolev (m : ℝ)),
      ∀ t, D01.IsSobolevDatum (m : ℝ) (⇑(U t)) (A t) := by
  choose A hA using fun t => exists_isSobolevDatum_of_memLp_derivs m (⇑(U t))
    (hasWeakDerivsL2_of_cylinder_full (u t) (fun θ => hu θ t) (U t) (hU t) m hm)
  exact ⟨⟨A, datum_path_continuous_of_cylinder u U hu hU hm A hA⟩, hA⟩

/-- Transfer the continuous path to any a.e.-agreeing velocity slices. -/
theorem exists_continuous_datum_slice_of_cylinder {q : ℕ} {S : ℝ}
    (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)))
    (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2))
    (hu : ∀ (θ : AddCircle (1 : ℝ)) t, sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t)
    (hU : ∀ t, ordinaryLift (U t) = value 1 (u t))
    (velocity : A02.SpaceTimeField)
    (hslice : ∀ t : Icc (0 : ℝ) S, (fun x : Space => velocity (↑t, x)) =ᵐ[volume] ⇑(U t))
    {m : ℕ} (hm : m ≤ q + 1) :
    ∃ A : C(Icc (0 : ℝ) S, RealVectorSobolev (m : ℝ)),
      ∀ t : Icc (0 : ℝ) S, A02.IsSobolevDatum (m : ℝ) (fun x : Space => velocity (↑t, x)) (A t) := by
  obtain ⟨A, hA⟩ := exists_continuous_datum_path_of_cylinder u U hu hU hm
  exact ⟨A, fun t => IsSobolevDatum.congr_field (hA t) (hslice t).symm⟩

end NSFormalization.Section4.A01
