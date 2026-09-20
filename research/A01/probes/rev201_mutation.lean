import NSFormalization.Section4.A01.RootComparison
namespace NSFormalization.Section4.A01
theorem rev201_bad_absorption {ν k r g b d : ℝ} (hν : 0 < ν) (hr : 0 < r)
    (h : r*d + ν*g^2 ≤ k*r*g + b*r) : d ≤ k^2/(8*ν)*r+b := by
  have hh := A04.young_high_real (C := k) (a := 1) (n := r) (d := 2*r*d) hν
    (by nlinarith [h] : (1/2 : ℝ)*(2*r*d)+ν*g^2 ≤ k*1*r*g+b*r)
  have hm : r*d ≤ r*(k^2/(4*ν)*r+b) := by nlinarith [hh]
  exact (mul_le_mul_iff_right₀ hr).mp hm

end NSFormalization.Section4.A01
