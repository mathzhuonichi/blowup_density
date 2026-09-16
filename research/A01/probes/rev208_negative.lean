import NSFormalization.Section4.A01.LocalSolution
open NSFormalization.Section4
open NSFormalization.Section4.A01
-- Substantive sign mutation of LocalSolution.lean:109, with the original proof.
theorem rev208_negative {ν : ℝ} {a : A02.SpatialField} {f : A02.SpaceTimeField}
    (hν : 0 < ν) (ha : a ∈ A02.initialClassR) (hf : D01.MemForceR f) :
    localHorizon ν a f < 0 := (localHorizon_spec hν ha hf).1
