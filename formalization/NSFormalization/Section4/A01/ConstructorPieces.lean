import NSFormalization.Section4.A01.EulerPairing
import NSFormalization.Section4.A01.L2Descent
import NSFormalization.Section4.A02.SolutionClass

/-!
# A01 constructor pieces: all available datum orders and continuous derivative-word paths

From the angle-invariant cylinder pair `(u,U)` on `Icc 0 S`, this module supplies
weak derivatives and a Sobolev datum at every `m ≤ q+1`, including the top three
orders omitted by the earlier jet-level descent. Each spatial derivative word also
has a continuous ordinary `L²` path: continuity is reflected by `ordinaryLift`, an
isometry. These are supply-side results, requiring no classical solution.

The full constructor still needs the joint smooth representative, time derivatives
from Duhamel, compatible all-order regularity on one horizon, and extension beyond
`S`. Continuous `L²` word paths are not yet a proof of continuity into the angular
order-`m` datum norm. See `research/A01/CONSTRUCTOR_SPLIT.md` for the precise residual.
-/

noncomputable section

namespace NSFormalization.Section4.A01

open Set MeasureTheory
open NSFormalization.Section4.D01
open EulerPressureSpatialRegularity
open NSFormalization.Paper3 (RealVectorSobolev)
open NSFormalization.Section4.A02 (SpaceTimeField SpatialField ClassicalSolutionR)
open NavierStokes.ProblemStatement (Space)
open EulerMeanOrdinaryLift EulerCylinderSobolevSpace EulerLiftedGradientSpace
  EulerCylinderSobolev EulerLpTranslation

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-- All remaining spatial derivative words descend without a loss of three orders. -/
theorem hasWeakDerivsL2_of_word_full {q : ℕ} (u : SobolevSpace 1 (q + 1))
    (hu : ∀ θ : AddCircle (1 : ℝ), sobolevTranslation 1 (q + 1) (0, θ) u = u) :
    ∀ (m n : ℕ) (hn : n ≤ q + 1) (_hnm : n + m ≤ q + 1) (w : Fin n → Fin 3)
      (Zw : EulerMeanSolenoidal.L2),
      ordinaryLift Zw = word 1 u hn (fun i => (w i).succ) →
      HasWeakDerivsL2 (⇑Zw) m
  | 0, _n, _hn, _hnm, _w, Zw, _ => Lp.memLp Zw
  | (k + 1), n, hn, hnm, w, Zw, hZw => by
      refine ⟨Lp.memLp Zw, fun j => ?_⟩
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
      · exact hasWeakDerivsL2_of_word_full u hu k (n + 1) hn1 (by omega)
          (Fin.cons j w) Zc hZc
      · intro i ψ
        have hderiv := word_hasDerivAt 1 u hlt (fun i => (w i).succ) j.succ
        rw [hcons] at hZc
        rw [← hZw, ← hZc] at hderiv
        exact weakDeriv_pairing_of_lift_hasDerivAt j Zw Zc hderiv i ψ

/-- The ordinary carrier has weak derivatives at every available cylinder order. -/
theorem hasWeakDerivsL2_of_cylinder_full {q : ℕ} (u : SobolevSpace 1 (q + 1))
    (hu : ∀ θ : AddCircle (1 : ℝ), sobolevTranslation 1 (q + 1) (0, θ) u = u)
    (U : EulerMeanSolenoidal.L2) (hU : ordinaryLift U = value 1 u)
    (m : ℕ) (hm : m ≤ q + 1) : HasWeakDerivsL2 (⇑U) m := by
  refine hasWeakDerivsL2_of_word_full u hu m 0 (Nat.zero_le _) (by omega) Fin.elim0 U ?_
  have hempty : (fun i : Fin 0 => (Fin.elim0 i : Fin 3).succ) =
      (Fin.elim0 : Fin 0 → Fin 4) := Subsingleton.elim _ _
  rw [hempty, hU]
  rfl

/-- Each descended spatial word is a continuous ordinary `L²` path, including the top order.
Continuity follows through the isometric lift; no time derivative is asserted. -/
theorem exists_continuous_word_descent {q : ℕ} {S : ℝ}
    (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)))
    (hu : ∀ (θ : AddCircle (1 : ℝ)) t, sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t)
    (n : ℕ) (hn : n ≤ q + 1) (w : Fin n → Fin 3) :
    ∃ Z : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2),
      ∀ t, ordinaryLift (Z t) = word 1 (u t) hn (fun i => (w i).succ) := by
  choose Z hZ using fun t => word_descent_ae_top (u t) (fun θ => hu θ t) n hn w
  have hc : Continuous (fun t => ordinaryLift (Z t)) := by
    simp_rw [hZ]
    exact (continuous_apply ⟨⟨n, Nat.lt_succ_of_le hn⟩, fun i => (w i).succ⟩).comp
      (continuous_subtype_val.comp u.continuous)
  exact ⟨⟨Z, ordinaryLift.isometry.comp_continuous_iff.mp hc⟩, hZ⟩

/-- A candidate velocity agreeing a.e. with the ordinary carrier has a Sobolev
 datum at every available cylinder order. The datum is constructed from weak
 derivatives, then transported by the a.e. identity; no solution is assumed. -/
theorem exists_isSobolevDatum_slice_of_cylinder {q : ℕ} {S : ℝ}
    (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)))
    (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2))
    (hu : ∀ (θ : AddCircle (1 : ℝ)) t, sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t)
    (hU : ∀ t, ordinaryLift (U t) = value 1 (u t))
    (velocity : SpaceTimeField)
    (hslice : ∀ t : Icc (0 : ℝ) S, (fun x : Space => velocity (↑t, x)) =ᵐ[volume] ⇑(U t))
    {m : ℕ} (hm : m ≤ q + 1) (t : Icc (0 : ℝ) S) :
    ∃ A : RealVectorSobolev (m : ℝ),
      NSFormalization.Section4.A02.IsSobolevDatum (m : ℝ)
        (fun x : Space => velocity (↑t, x)) A :=
  exists_isSobolevDatum_m_of_ae m (U t) (fun x : Space => velocity (↑t, x)) (hslice t)
    (hasWeakDerivsL2_of_cylinder_full (u t) (fun θ => hu θ t) (U t) (hU t) m hm)

end NSFormalization.Section4.A01
