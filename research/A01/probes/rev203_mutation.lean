import NSFormalization.Section4.A01.SignedLimit

namespace NSFormalization.Section4.A01

-- Substantive mutation: demand the stronger, false Young coefficient `1 / (8 * ν)`.
example {ν k r g z b ε : ℝ}
    (hν : 0 < ν) (hr : 0 ≤ r) (hb : 0 ≤ b) (hε : 0 < ε)
    (h : r * z ≤ k * r * g + b * r) :
    (r * z - ν * g ^ 2) / Real.sqrt (r ^ 2 + ε ^ 2) ≤ k ^ 2 / (8 * ν) * r + b := by
  exact signed_quotient_absorption hν hr hb hε h

end NSFormalization.Section4.A01
