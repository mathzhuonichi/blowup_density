import NSFormalization.Section3.T18.Momentum

/- Reviewer-only probes.  The first theorem widens the packet's zero-past
   interval from `T - ε^2` to `T`; its proof must fail.  The second confirms
   that the admitted scale interval is nonempty for every threaded datum. -/

noncomputable section
namespace NSFormalization.Section3.T18.Rev433

open Set
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T15

-- Substantive mutation: the claimed zero-past interval is widened to `t ≤ T`.
-- This is intentionally unprovable: after activation the packet need not be zero.
theorem widened_packet_slice_zero (data : InsertionData) {ε t : ℝ}
    (ht : t ≤ data.place.T) :
    (fun y : Space ↦
        periodizedScaledVelocity data.packetVelocity data.place.x₀ data.place.T ε (t, y))
      = fun _ ↦ 0 := by
  exact packet_slice_zero data (by linarith)

-- Non-vacuity of the quantifier range used by all three reviewed fields.
example (data : InsertionData) : ∃ ε : ℝ, ε ∈ Ioc (0 : ℝ) (ε₀ data) := by
  refine ⟨ε₀ data, ?_⟩
  exact ⟨eps_pos data, le_rfl⟩

end NSFormalization.Section3.T18.Rev433
