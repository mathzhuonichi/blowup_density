import NSFormalization.Section4.A01.CarrierWords

/-! Lane-151 probe for piece **(a)** `word_descent_ae_partial`.

**Status: (a) is PROVED** and landed in `Section4/A01/CarrierWords.lean` (`word_descent_ae_partial`,
with `descent_step_ae` / `wordField` / `wordField_field` / `word_descent_ae`).  The bridge is a tree
theorem, `NSFormalization.Section4.A03.ae_eq_of_schwartz_pairing`
(`Section4/A03/ScalarTameProduct.lean:136`), which consumes exactly the **complex-Schwartz**
`∫ ψ x * f x` pairing the descent produces and performs the complex→real and Schwartz→compact-support
conversions internally; the classical side is `D01.smoothField_weakDeriv_pairing`
(`FiniteOrderConstructor.lean:306`).  (An earlier version of this probe wrongly recorded (a) as an
L-level open problem "not in the tree" — corrected per `research/A01/REVIEW_CARRIER_WORDS.md` §3/N1.)

This file keeps the base-case argument (a reduces to `⇑U =ᵐ z` at `n = 0`) and `#check`s the two
pairings that are cancelled against each other. -/

noncomputable section

namespace Probe151DescentA

open Set MeasureTheory
open NavierStokes.ProblemStatement (Space coordinateVector)
open EulerMeanOrdinaryLift EulerCylinderSobolevSpace EulerCylinderSobolev
open scoped ENNReal ContDiff

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-- **(a) at `n = 0`.**  The empty spatial word descends to `U` itself, so the identity is exactly
the a.e. hand-off `⇑U =ᵐ z` (`iteratedFDeriv ℝ 0 z x _ = z x`). -/
theorem word_descent_ae_base {q : ℕ} (u : SobolevSpace 1 (q + 1))
    (U : EulerMeanSolenoidal.L2) (hU : ordinaryLift U = value 1 u)
    {z : Space → Space} (hUz : (⇑U) =ᵐ[volume] z)
    (Zw : EulerMeanSolenoidal.L2)
    (hZw : ordinaryLift Zw
      = word 1 u (Nat.zero_le _) (fun i => ((Fin.elim0 : Fin 0 → Fin 3) i).succ)) :
    (⇑Zw) =ᵐ[volume]
      fun x => iteratedFDeriv ℝ 0 z x (fun i => coordinateVector ((Fin.elim0 : Fin 0 → Fin 3) i)) := by
  have hwemp : (fun i => ((Fin.elim0 : Fin 0 → Fin 3) i).succ) = (Fin.elim0 : Fin 0 → Fin 4) :=
    Subsingleton.elim _ _
  have hval : word 1 u (Nat.zero_le _) (fun i => ((Fin.elim0 : Fin 0 → Fin 3) i).succ)
      = value 1 u := by rw [hwemp]; rfl
  have hZU : Zw = U := ordinaryLift.injective (by rw [hZw, hval, hU])
  subst hZU
  refine hUz.trans (Filter.EventuallyEq.of_eq ?_)
  funext x; rw [iteratedFDeriv_zero_apply]

/-! ### The two pairings the proof cancels (both complex Schwartz).

`descent_step_ae` in the module feeds these into `A03.ae_eq_of_schwartz_pairing`. -/
#check @NSFormalization.Section4.A01.weakDeriv_pairing_of_lift_hasDerivAt
#check @NSFormalization.Section4.D01.smoothField_weakDeriv_pairing
#check @NSFormalization.Section4.A03.ae_eq_of_schwartz_pairing

end Probe151DescentA
