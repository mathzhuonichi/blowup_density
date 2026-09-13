import NSFormalization.Paper1.PeriodicPicardTwoStepDuhamel

noncomputable section
namespace NSFormalization.Paper1

theorem picard_two_step_first_error
    {e d : ℕ → ℝ} {t q : ℝ}
    (hgain : e 1 ≤ t * d 0)
    (hcompare : t * d 0 ≤ q * e 0) :
    e 1 ≤ q * e 0 := hgain.trans hcompare

end NSFormalization.Paper1
