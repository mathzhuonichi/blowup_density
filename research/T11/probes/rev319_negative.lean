import NSFormalization.Section3.T11.Persistence

noncomputable section
namespace NSFormalization.Section3.T11.Review319Negative

open NSFormalization.Section3.T10
open NSFormalization.Section3.T11

/- A substantive mutation of the transitivity target: the output order is
   widened from q to q+1.  Reusing the claimed proof must fail by a type
   mismatch, not by dropping an argument. -/
example {s r q : ℝ}
    {A : PeriodicSobolev s} {B : PeriodicSobolev r} {D : PeriodicSobolev q}
    (hAB : IsPeriodicReweight s r A B) (hBD : IsPeriodicReweight r q B D) :
    IsPeriodicReweight s (q + 1) A D := by
  exact persistence_reweight_trans hAB hBD

end NSFormalization.Section3.T11.Review319Negative
