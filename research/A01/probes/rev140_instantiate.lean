-- Reviewer probe (lane 140 review, REVIEW_EULER_PAIRING.md), preserved verbatim; compiles on this branch.
import NSFormalization.Section4.A01.EulerPairing
import NSFormalization.Source.OrdinaryForcedLocal

open NSFormalization.Section4.A01 NSFormalization.Section4.D01
open MeasureTheory NavierStokes.ProblemStatement Set
open NSFormalization.Paper3 (RealVectorSobolev)
open EulerLpTranslation EulerCylinderSobolevSpace EulerMeanOrdinaryLift

/-- NON-VACUITY: `exists_isSobolevDatum_m_of_cylinder` fires on the actual output of
`Source.OrdinaryForcedLocal.exists_local`, consuming only clause 4 (`ordinaryLift (U t) = value 1 (u t)`)
and clause 7 (angle invariance).  For `q ≥ 6` the order budget `m + 3 ≤ q + 1` admits `m = 0,…,q-2`
(so `m ≤ 4` already at the minimal `q = 6`).  Note `T` is produced *after* `q`: it is `T(q)`. -/
theorem datum_on_exists_local {q : ℕ} (hq : 6 ≤ q) {ν S : ℝ} (hν : 0 < ν) (hS : 0 < S)
    (a : SmoothL2Field Space) (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous (fun t => (F t).jetLp n)) :
    ∃ (T : ℝ) (hT : 0 < T), T ≤ S ∧
      ∃ U : C(Icc (0 : ℝ) T, EulerMeanSolenoidal.L2),
        U ⟨0, le_rfl, hT.le⟩ = a.toLp ∧
        ∀ (m : ℕ), m + 3 ≤ q + 1 → ∀ t : Icc (0 : ℝ) T,
          ∃ A : RealVectorSobolev (m : ℝ), IsSobolevDatum (m : ℝ) (⇑(U t)) A := by
  obtain ⟨T, hT, hTS, u, U, _hu, _hi, hU0, h4, _h5, _h6, h7⟩ :=
    NSFormalization.Source.OrdinaryForcedLocal.exists_local hq hν hS a ha F hF
  exact ⟨T, hT, hTS, U, hU0, fun m hm t =>
    exists_isSobolevDatum_m_of_cylinder (u t) (fun θ => h7 θ t) (U t) (h4 t) m hm⟩

/-- The budget really is `m ≤ q - 2`: at the minimal `q = 6` the largest admissible order is `4`. -/
example : (4 : ℕ) + 3 ≤ 6 + 1 := by norm_num
example : ¬ ((5 : ℕ) + 3 ≤ 6 + 1) := by norm_num

#print axioms datum_on_exists_local
