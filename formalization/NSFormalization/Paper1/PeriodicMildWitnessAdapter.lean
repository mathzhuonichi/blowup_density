import NSFormalization.Source.ForcedCylinderLocal

noncomputable section
namespace NSFormalization.Paper1

/-- A mild witness packaged as a fixed point of an explicitly supplied Picard map.
No contraction or PDE existence is encoded by this adapter. -/
structure MildPicardFixedPointWitness (E : Type*) [NormedAddCommGroup E] where
  trajectory : E
  map : E → E
  norm_bound : ℝ
  trajectory_bound : ‖trajectory‖ ≤ norm_bound
  fixed : map trajectory = trajectory

/-- Convert the orientation commonly returned by a mild solver (`u = T u`)
into the fixed-point orientation used by Picard contracts. -/
theorem mild_witness_fixed_orientation
    {E : Type*} [NormedAddCommGroup E]
    {u : E} {T : E → E} (h : u = T u) : T u = u := h.symm

end NSFormalization.Paper1
