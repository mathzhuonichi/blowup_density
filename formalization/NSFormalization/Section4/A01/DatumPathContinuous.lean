import NSFormalization.Section4.A01.L2Descent
import NSFormalization.Section4.D01.OrderZeroAlgebra

/-! # Continuous finite-order data of the cylinder path

The quantitative weak-derivative constructor applied to differences controls datum
increments by cylinder increments. No time differentiability or classical solution
is assumed. The L² descent reaches the top order without loss.
-/

noncomputable section
namespace NSFormalization.Section4.A01
open Set MeasureTheory
open NSFormalization.Section4.D01
open NSFormalization.Paper3 (RealVectorSobolev)
open NavierStokes.ProblemStatement (Space coordinateVector)
open EulerMeanOrdinaryLift EulerCylinderSobolevSpace EulerLiftedGradientSpace
  EulerCylinderSobolev EulerPressureSpatialRegularity
open scoped LineDeriv SchwartzMap
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-- Every finite word coordinate of the cylinder path is continuous. -/
theorem continuous_cylinder_word {q n : ℕ} {S : ℝ}
    (u : C(Icc (0 : ℝ) S, SobolevSpace 1 q)) (hn : n ≤ q) (w : Fin n → Fin 4) :
    Continuous (fun t => word 1 (u t) hn w) := by
  exact (continuous_apply (⟨⟨n, Nat.lt_succ_of_le hn⟩, w⟩ : SobolevWord q)).comp
    (continuous_subtype_val.comp u.continuous)

/-- Quantitative weak derivatives for every word, including the top order. -/
theorem weakDerivsBound_word_top {q : ℕ} (u : SobolevSpace 1 q)
    (hu : ∀ θ : AddCircle (1 : ℝ), sobolevTranslation 1 q (0, θ) u = u) :
    ∀ (m n : ℕ) (hn : n ≤ q), n + m ≤ q → ∀ (w : Fin n → Fin 4)
      (Z : EulerMeanSolenoidal.L2), ordinaryLift Z = word 1 u hn w →
      HasWeakDerivsL2Bound (⇑Z) (‖u‖ ^ 2) m
  | 0, _, hn, _, w, Z, hZ => ⟨Lp.memLp Z, eLpNorm_descend_le u hn w Z hZ⟩
  | k + 1, n, hn, hnm, w, Z, hZ => by
      refine ⟨⟨Lp.memLp Z, eLpNorm_descend_le u hn w Z hZ⟩, fun j => ?_⟩
      have hlt : n < q := by omega
      obtain ⟨W, hW⟩ := exists_ordinaryLift_of_invariant
        (word 1 u (Nat.succ_le_of_lt hlt) (Fin.cons j.succ w)) (fun θ =>
          congrArg (fun v : SobolevSpace 1 q =>
            v.val ⟨⟨n + 1, Nat.lt_succ_of_le hlt⟩, Fin.cons j.succ w⟩) (hu θ))
      refine ⟨⇑W, weakDerivsBound_word_top u hu k (n + 1) hlt (by omega)
        (Fin.cons j.succ w) W hW, ?_⟩
      intro i ψ
      have hd := word_hasDerivAt 1 u hlt w j.succ
      rw [← hZ, ← hW] at hd
      exact weakDeriv_pairing_of_lift_hasDerivAt j Z W hd i ψ

/-- The full finite-order quantitative bound, with no three-order loss. -/
theorem weakDerivsBound_cylinder_top {q : ℕ} (u : SobolevSpace 1 (q + 1))
    (hu : ∀ θ : AddCircle (1 : ℝ), sobolevTranslation 1 (q + 1) (0, θ) u = u)
    (U : EulerMeanSolenoidal.L2) (hU : ordinaryLift U = value 1 u)
    (m : ℕ) (hm : m ≤ q + 1) : HasWeakDerivsL2Bound (⇑U) (‖u‖ ^ 2) m := by
  exact weakDerivsBound_word_top u hu m 0 (Nat.zero_le _) (by omega) Fin.elim0 U hU

/-- Datum increments are controlled by cylinder increments. -/
theorem datum_sub_norm_sq_le {q m : ℕ} (hm : m ≤ q + 1)
    (u v : SobolevSpace 1 (q + 1))
    (hu : ∀ θ : AddCircle (1 : ℝ), sobolevTranslation 1 (q + 1) (0, θ) u = u)
    (hv : ∀ θ : AddCircle (1 : ℝ), sobolevTranslation 1 (q + 1) (0, θ) v = v)
    (U V : EulerMeanSolenoidal.L2) (hU : ordinaryLift U = value 1 u)
    (hV : ordinaryLift V = value 1 v)
    (A B : RealVectorSobolev (m : ℝ))
    (hA : IsSobolevDatum (m : ℝ) (⇑U) A) (hB : IsSobolevDatum (m : ℝ) (⇑V) B) :
    ‖A - B‖ ^ 2 ≤ (4 : ℝ) ^ m * ‖u - v‖ ^ 2 := by
  have hinv : ∀ θ : AddCircle (1 : ℝ),
      sobolevTranslation 1 (q + 1) (0, θ) (u - v) = u - v := by
    intro θ
    rw [map_sub, hu θ, hv θ]
  have hlift : ordinaryLift (U - V) = value 1 (u - v) := by
    rw [map_sub, hU, hV]
    rfl
  have hd := D01.isSobolevDatum_sub
    (schwartzPairable_of_memLp (fun i => memLp_component (Lp.memLp U) i))
    (schwartzPairable_of_memLp (fun i => memLp_component (Lp.memLp V) i)) hA hB
  have hd' : IsSobolevDatum (m : ℝ) (⇑(U - V)) (A - B) :=
    IsSobolevDatum.congr_field hd (Lp.coeFn_sub U V).symm
  exact norm_isSobolevDatum_le_of_memLp_derivs_sharp m _ _
    (weakDerivsBound_cylinder_top (u - v) hinv (U - V) hlift m hm) (A - B) hd'

/-- R1: a continuous selection on the closed interval, through the top order. -/
theorem exists_continuous_datumPath {q : ℕ} {S : ℝ}
    (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)))
    (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2))
    (hu : ∀ (θ : AddCircle (1 : ℝ)) t, sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t)
    (hU : ∀ t, ordinaryLift (U t) = value 1 (u t))
    (m : ℕ) (hm : m ≤ q + 1) :
    ∃ A : Icc (0 : ℝ) S → RealVectorSobolev (m : ℝ),
      (∀ t, IsSobolevDatum (m : ℝ) (⇑(U t)) (A t)) ∧ Continuous A := by
  choose A hA hbound using fun t => exists_isSobolevDatum_norm_le_sharp m _ _
    (weakDerivsBound_cylinder_top (u t) (fun θ => hu θ t) (U t) (hU t) m hm)
  refine ⟨A, hA, continuous_iff_continuousAt.mpr (fun t => ?_)⟩
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hb : ∀ s, ‖A s - A t‖ ≤ (2 : ℝ) ^ m * ‖u s - u t‖ := by
    intro s
    have h := datum_sub_norm_sq_le hm (u s) (u t) (fun θ => hu θ s)
      (fun θ => hu θ t) (U s) (U t) (hU s) (hU t) (A s) (A t) (hA s) (hA t)
    have hp : ((2 : ℝ) ^ m) ^ 2 = (4 : ℝ) ^ m := by rw [← pow_mul, Nat.mul_comm, pow_mul]; norm_num
    have hs : ‖A s - A t‖ ^ 2 ≤ ((2 : ℝ) ^ m * ‖u s - u t‖) ^ 2 := by
      simpa only [mul_pow, hp] using h
    exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hs
  have ht : Filter.Tendsto (fun s => (2 : ℝ) ^ m * ‖u s - u t‖) (nhds t) (nhds 0) := by
    simpa using (((u.continuous.continuousAt (x := t)).sub (continuousAt_const (y := u t))).norm.tendsto.const_mul ((2 : ℝ) ^ m))
  exact squeeze_zero (fun s => norm_nonneg _) hb ht

end NSFormalization.Section4.A01
