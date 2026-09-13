import Euler.EulerProof

/-!
# Packet shift arithmetic with default resource limits

This is an independent copy of `Euler.PacketShiftArithmetic`, in a separate namespace
so both modules can be imported together. The definitions and theorem statements are
unchanged.

Removing the original recursion-depth override makes all nine `simp only` calls fail
before reaching `omega`. Replacing them with `dsimp only` suffices: only definitional
unfolding is needed, and all the original `omega` steps then succeed with Lean's default
recursion-depth and heartbeat limits. No resource-limit override is needed in this file.

Check with the Euler library's strict compiler options:
`lake env lean -DautoImplicit=false -DwarningAsError=true Euler/PacketShiftArithmeticNoOptions.lean`
-/

namespace EulerPacketShiftArithmeticNoOptions

def highShift (p : ℕ) : ℕ := 100*p-80
def meanShift (p : ℕ) : ℕ := 100*p-140
def highForceShift (p : ℕ) : ℕ := highShift p-10
def meanForceShift (p : ℕ) : ℕ := meanShift p-10

theorem primary_shift : highShift 1=20 := rfl

theorem slow_high_high_room (i j p : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j) (hp : i+j=p) :
    highShift i+highShift j+2+8 ≤ meanForceShift p := by
  dsimp only [highShift, meanShift, meanForceShift]
  omega

theorem slow_mean_high_room (i j p : ℕ) (hi : 2 ≤ i) (hj : 1 ≤ j) (hp : i+j=p) :
    meanShift i+highShift j+2+8 ≤ meanForceShift p := by
  dsimp only [highShift, meanShift, meanForceShift]
  omega

theorem slow_mean_mean_room (i j p : ℕ) (hi : 2 ≤ i) (hj : 2 ≤ j) (hp : i+j=p) :
    meanShift i+meanShift j+2+8 ≤ meanForceShift p := by
  dsimp only [meanShift, meanForceShift]
  omega

theorem fast_mean_high_room (i j p : ℕ) (hi : 2 ≤ i) (hj : 1 ≤ j) (hp : i+j=p+1) :
    meanShift i+highShift j+2+8 ≤ highForceShift p := by
  dsimp only [highShift, meanShift, highForceShift]
  omega

theorem fast_corrector_high_room (i j p : ℕ) (hi : 2 ≤ i) (hj : 1 ≤ j) (hp : i+j=p+1) :
    highShift (i-1)+highShift j+2+8 ≤ meanForceShift p := by
  dsimp only [highShift, meanShift, meanForceShift]
  omega

theorem fast_corrector_corrector_room (i j p : ℕ) (hi : 2 ≤ i) (hj : 2 ≤ j)
    (hp : i+j=p+1) :
    highShift (i-1)+highShift (j-1)+2+8 ≤ meanForceShift p := by
  dsimp only [highShift, meanShift, meanForceShift]
  omega

theorem previous_linear_room (p : ℕ) (hp : 2 ≤ p) :
    highShift (p-1)+2+8 ≤ meanForceShift p := by
  dsimp only [highShift, meanShift, meanForceShift]
  omega

theorem mean_force_le_high_force (p : ℕ) : meanForceShift p ≤ highForceShift p := by
  dsimp only [highShift, meanShift, meanForceShift, highForceShift]
  omega

theorem force_shift_dominates_grade (p : ℕ) (hp : 2 ≤ p) :
    25*p ≤ meanForceShift p ∧ 25*p ≤ highForceShift p := by
  dsimp only [highShift, meanShift, meanForceShift, highForceShift]
  omega

end EulerPacketShiftArithmeticNoOptions
