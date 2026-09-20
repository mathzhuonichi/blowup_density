import NSFormalization.Section4.A01.MildGronwall

noncomputable section
namespace NSFormalization.Section4.A01

/- A substantive mutation of the lane's sharp Young-absorption conclusion:
replace 16^2 = 256 by 255.  The original proof must not close. -/
theorem mild_energy_absorption_255 {nu A l x g b d : Real}
    (hnu : 0 < nu) (hx : 0 <= x)
    (h : (1 / 2) * d + nu * g ^ 2 <=
      A * (16 * l) * Real.sqrt x * g + b * Real.sqrt x) :
    d <= 2 * ((A ^ 2 / (4 * nu)) * (255 * l ^ 2) * x + b * Real.sqrt x) := by
  have ha := NSFormalization.Section4.A04.young_high_real hnu h
  rw [Real.sq_sqrt hx] at ha
  nlinarith [ha]

end NSFormalization.Section4.A01
