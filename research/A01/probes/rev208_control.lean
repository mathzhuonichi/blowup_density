import NSFormalization.Section4.A01.LocalSolution
open NSFormalization.Section4
open NSFormalization.Section4.A01
-- Restore the original sign to validate the mutation harness.
theorem rev208_control {ν : ℝ} {a : A02.SpatialField} {f : A02.SpaceTimeField}
    (hν : 0 < ν) (ha : a ∈ A02.initialClassR) (hf : D01.MemForceR f) :
    0 < localHorizon ν a f := (localHorizon_spec hν ha hf).1
