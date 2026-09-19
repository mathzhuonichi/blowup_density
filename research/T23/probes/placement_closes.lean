import NSFormalization.Section3.T23.Placement
import NSFormalization.Section3.T13.ConstantEndpoints

/-!
# T23 U1 consumer probe

The prescribed ball is centered at `(5,5,5)`, has radius `1`, and lies in the
domain ball with the same center and radius `2`.  In particular, the domain
does not contain the origin.  The raw packet carrier is the nonempty closed
unit ball at the origin; the force is the compactly supported zero field.

Every one of the sixteen `DomainPlacementData` fields is consumed below by an
`exact` proof.  The final theorem consumes the separate
`interiorBall_in_domain` geometry theorem.
-/

noncomputable section

namespace NSFormalization.Section3.T23.Probe

open Set
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T13

def translatedCenter : Space :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm (fun _ => (5 : ℝ))

def translatedDomain : Set Space := Metric.ball translatedCenter 2

def probeVelocity : VelocityField := 0
def probePressure : PressureField := 0
def probeForce : VelocityField := 0
def probeCarrier : Set Space := Metric.closedBall (0 : Space) 1

theorem probeCarrier_compact : IsCompact probeCarrier := by
  exact isCompact_closedBall (0 : Space) 1

theorem probeForce_compact : HasCompactSupport probeForce := by
  exact HasCompactSupport.zero

theorem translatedCenter_mem_ball :
    translatedCenter ∈ Metric.ball translatedCenter 1 := by
  exact Metric.mem_ball_self (by norm_num)

theorem translatedBall_in_domain :
    closure (Metric.ball translatedCenter 1) ⊆ translatedDomain := by
  intro x hx
  have hdist : dist x translatedCenter ≤ 1 :=
    Metric.closure_ball_subset_closedBall hx
  exact Metric.mem_ball.mpr (by
    change dist x translatedCenter < 2
    linarith)

theorem origin_not_mem_translatedDomain :
    (0 : Space) ∉ translatedDomain := by
  intro hzero
  have hnorm : ‖translatedCenter‖ < 2 := by
    simpa only [translatedDomain, Metric.mem_ball, dist_eq_norm, zero_sub,
      norm_neg] using hzero
  have hcoord := abs_spaceCoord_le_norm translatedCenter (0 : Fin 3)
  have hvalue : translatedCenter (0 : Fin 3) = 5 := rfl
  rw [hvalue, abs_of_pos (by norm_num)] at hcoord
  linarith

def translatedPlacement :
    DomainPlacementData probeVelocity probePressure probeForce probeCarrier :=
  domainPlacementData probeCarrier_compact probeForce_compact translatedCenter 1
    (by norm_num) translatedBall_in_domain translatedCenter translatedCenter_mem_ball
    1 (by norm_num)

-- Field 1: `T`.
example : translatedPlacement.T = 1 := by
  exact rfl

-- Field 2: `time_pos`.
example : 0 < translatedPlacement.T := by
  exact translatedPlacement.time_pos

-- Field 3: `chartCenter`.
example : translatedPlacement.chartCenter = translatedCenter := by
  exact rfl

-- Field 4: `chartRadius`.
example : translatedPlacement.chartRadius = 1 := by
  exact rfl

-- Field 5: `chartRadius_pos`.
example : 0 < translatedPlacement.chartRadius := by
  exact translatedPlacement.chartRadius_pos

-- Field 6: `x₀`.
example : translatedPlacement.x₀ = translatedCenter := by
  exact rfl

-- Field 7: `x₀_mem`.
example : translatedPlacement.x₀ ∈
    Metric.ball translatedPlacement.chartCenter translatedPlacement.chartRadius := by
  exact translatedPlacement.x₀_mem

-- Field 8: `Kstar`.
example : translatedPlacement.Kstar =
    domainPlacementCarrier probeCarrier probeForce := by
  exact rfl

-- Field 9: `Kstar_compact`.
example : IsCompact translatedPlacement.Kstar := by
  exact translatedPlacement.Kstar_compact

-- Field 10: `carrier_subset`.
example : probeCarrier ⊆ translatedPlacement.Kstar := by
  exact translatedPlacement.carrier_subset

-- Field 11: `force_projection_subset`.
example : ∀ t : ℝ, ∀ x : Space,
    (t, x) ∈ tsupport probeForce → x ∈ translatedPlacement.Kstar := by
  exact translatedPlacement.force_projection_subset

-- Field 12: `ε₀`.
example : translatedPlacement.ε₀ =
    domainPlacementThreshold probeCarrier_compact probeForce_compact 1
      translatedCenter translatedCenter 1 := by
  exact rfl

-- Field 13: `eps_pos`.
example : 0 < translatedPlacement.ε₀ := by
  exact translatedPlacement.eps_pos

-- Field 14: `eps_le_one`.
example : translatedPlacement.ε₀ ≤ 1 := by
  exact translatedPlacement.eps_le_one

-- Field 15: `eps_time`.
example : ∀ ε ∈ Ioc (0 : ℝ) translatedPlacement.ε₀,
    2 * ε ^ 2 < translatedPlacement.T := by
  exact translatedPlacement.eps_time

-- Field 16: `eps_space`.
example : ∀ ε ∈ Ioc (0 : ℝ) translatedPlacement.ε₀,
    ∀ y ∈ translatedPlacement.Kstar,
      translatedPlacement.x₀ + ε • y ∈
        Metric.ball translatedPlacement.chartCenter translatedPlacement.chartRadius := by
  exact translatedPlacement.eps_space

theorem translated_interiorBall_in_domain :
    closure (Metric.ball translatedPlacement.chartCenter
      translatedPlacement.chartRadius) ⊆ translatedDomain := by
  exact interiorBall_in_domain probeCarrier_compact probeForce_compact translatedCenter 1
    (by norm_num) translatedBall_in_domain translatedCenter translatedCenter_mem_ball
    1 (by norm_num)

end NSFormalization.Section3.T23.Probe
