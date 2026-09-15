import NSFormalization.Section4.A01.MildGronwall

noncomputable section
namespace NSFormalization.Section4.A01

/- At nu=A=l=x=1, g=8, b=0, d=128, the unabsorbed hypothesis is
an equality.  The correct 256 conclusion is also an equality, while its
255 mutation says 128 <= 127.5. -/
example :
    (1 / 2 : Real) * 128 + 1 * 8 ^ 2 <=
      1 * (16 * 1) * Real.sqrt 1 * 8 + 0 * Real.sqrt 1 := by
  norm_num

example : Not ((128 : Real) <=
    2 * ((1 ^ 2 / (4 * 1)) * (255 * 1 ^ 2) * 1 + 0 * Real.sqrt 1)) := by
  norm_num

end NSFormalization.Section4.A01
