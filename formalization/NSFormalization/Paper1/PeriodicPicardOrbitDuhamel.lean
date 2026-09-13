import NSFormalization.Paper1.PeriodicPicardDuhamelLipschitz

noncomputable section
namespace NSFormalization.Paper1

open PeriodicForcedDuhamel

/-- Conditional one-step estimate obtained by composing a Duhamel Lipschitz
contract with an explicit map-to-Duhamel comparison. -/
theorem duhamel_lipschitz_implies_picard_step
    {E : Type*} [NormedAddCommGroup E]
    (T : E → E) {x y : E} {ν t D q : ℝ}
    (C : PicardDuhamelLipschitzContract (ν := ν) (t := t) (D := D)
      (fun _ => (0 : FourierHilbert)) (fun _ => (0 : FourierHilbert)))
    (hmap : ‖T x - T y‖ ≤ ‖duhamel ν C.hν t (fun _ => 0) -
      duhamel ν C.hν t (fun _ => 0)‖)
    (hscalar : t * D ≤ q * ‖x - y‖) :
    ‖T x - T y‖ ≤ q * ‖x - y‖ := by
  exact hmap.trans ((C.bound).trans hscalar)

end NSFormalization.Paper1
