import NSFormalization.Paper1.PeriodicHeatMultiplier

noncomputable section
namespace NSFormalization.Paper1.PeriodicForcedDuhamel

open Set MeasureTheory
open NSFormalization.Paper1.PeriodicHeatMultiplier

abbrev FourierHilbert := PeriodicHeatMultiplier.FourierHilbert

/-- Linear forced Duhamel operator on the native periodic Fourier carrier.
The `max` delay keeps the integrand globally defined; on a forward interval it
coincides with the expected heat delay `t - τ`. -/
def duhamel (ν : ℝ) (hν : 0 ≤ ν) (t : ℝ) (G : ℝ → FourierHilbert) : FourierHilbert :=
  ∫ τ in (0 : ℝ)..t, heat hν (show 0 ≤ max (t - τ) 0 by positivity) (G τ)

@[simp] theorem duhamel_zero (ν : ℝ) (hν : 0 ≤ ν) (t : ℝ) :
    duhamel ν hν t (fun _ => (0 : FourierHilbert)) = 0 := by
  unfold duhamel
  have hz : (fun τ => heat hν (show 0 ≤ max (t - τ) 0 by positivity) (0 : FourierHilbert)) = (fun _ => (0 : FourierHilbert)) := by
    funext τ
    ext k
    simp [heat_apply]
  rw [hz, intervalIntegral.integral_zero]

/-- Additivity in the forcing, with the two required integrability certificates
made explicit rather than hidden in typeclass inference. -/
theorem duhamel_add {ν : ℝ} {hν : 0 ≤ ν} {t : ℝ}
    {G H : ℝ → FourierHilbert}
    (hG : IntervalIntegrable (fun τ => heat hν (show 0 ≤ max (t - τ) 0 by positivity) (G τ)) volume 0 t)
    (hH : IntervalIntegrable (fun τ => heat hν (show 0 ≤ max (t - τ) 0 by positivity) (H τ)) volume 0 t) :
    duhamel ν hν t (fun τ => G τ + H τ) = duhamel ν hν t G + duhamel ν hν t H := by
  simp only [duhamel]
  have hsum : (fun τ => heat hν (show 0 ≤ max (t - τ) 0 by positivity) (G τ + H τ)) =
      (fun τ => heat hν (show 0 ≤ max (t - τ) 0 by positivity) (G τ) +
        heat hν (show 0 ≤ max (t - τ) 0 by positivity) (H τ)) := by
    funext τ
    exact (heatCLM hν (show 0 ≤ max (t - τ) 0 by positivity)).map_add (G τ) (H τ)
  rw [hsum, intervalIntegral.integral_add hG hH]

/-- Complex scalar multiplication commutes with the forced heat integral.
The total Bochner integral identity does not require an integrability assumption. -/
theorem duhamel_smul {ν : ℝ} {hν : 0 ≤ ν} {t : ℝ}
    (c : ℂ) (G : ℝ → FourierHilbert) :
    duhamel ν hν t (fun τ => c • G τ) = c • duhamel ν hν t G := by
  unfold duhamel
  have hscale :
      (fun τ => heat hν (show 0 ≤ max (t - τ) 0 by positivity) (c • G τ)) =
      (fun τ => c • heat hν (show 0 ≤ max (t - τ) 0 by positivity) (G τ)) := by
    funext τ
    exact (heatCLM hν (show 0 ≤ max (t - τ) 0 by positivity)).map_smul c (G τ)
  rw [hscale, intervalIntegral.integral_smul]

end NSFormalization.Paper1.PeriodicForcedDuhamel

namespace NSFormalization.Paper1.PeriodicForcedDuhamel

/-- Every Duhamel integral vanishes at zero time, independently of the forcing. -/
theorem duhamel_at_zero {ν : ℝ} (hν : 0 ≤ ν) (G : ℝ → FourierHilbert) :
    duhamel ν hν 0 G = 0 := by
  unfold duhamel
  exact intervalIntegral.integral_same

end NSFormalization.Paper1.PeriodicForcedDuhamel

namespace NSFormalization.Paper1.PeriodicForcedDuhamel

open NSFormalization.Paper1.PeriodicHeatMultiplier

/-- Coefficient-level zero-time identity for the forced Duhamel operator. -/
theorem duhamel_apply_at_zero {ν : ℝ} (hν : 0 ≤ ν)
    (G : ℝ → FourierHilbert) (k : PeriodicFrequency) :
    duhamel ν hν 0 G k = 0 := by
  have hzero : duhamel ν hν 0 G = 0 := duhamel_at_zero hν G
  exact congrArg (fun f : FourierHilbert => f k) hzero

end NSFormalization.Paper1.PeriodicForcedDuhamel

namespace NSFormalization.Paper1.PeriodicForcedDuhamel

open Set MeasureTheory
open NSFormalization.Paper1.PeriodicHeatMultiplier

/-- Coefficient-level additivity under explicit interval-integrability certificates. -/
theorem duhamel_apply_add {ν : ℝ} {hν : 0 ≤ ν} {t : ℝ}
    {G H : ℝ → FourierHilbert}
    (hG : IntervalIntegrable
      (fun τ => heat hν (show 0 ≤ max (t - τ) 0 by positivity) (G τ)) volume 0 t)
    (hH : IntervalIntegrable
      (fun τ => heat hν (show 0 ≤ max (t - τ) 0 by positivity) (H τ)) volume 0 t)
    (k : PeriodicFrequency) :
    duhamel ν hν t (fun τ => G τ + H τ) k =
      duhamel ν hν t G k + duhamel ν hν t H k := by
  have hadd : duhamel ν hν t (fun τ => G τ + H τ) =
      duhamel ν hν t G + duhamel ν hν t H :=
    @duhamel_add ν hν t G H hG hH
  have heval := congrArg (fun f : FourierHilbert => f k) hadd
  simpa using heval

end NSFormalization.Paper1.PeriodicForcedDuhamel
