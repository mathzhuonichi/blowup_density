import NSFormalization.Section4.R43.CriticalMomentum

open Set
open NSFormalization.Section4.A02
open NSFormalization.Section4.R43

-- Negative probe: mutate the physical pressure term from `-∇p` to `+∇p`.
example
    {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    (hν : 0 < ν) (hf : MemForceR f) (w : ClassicalSolutionR ν a f T) :
    ∀ t ∈ Ioo (0 : ℝ) T,
      deriv (criticalVelocityHalf w) t =
        ν • criticalLaplacianHalf w t - criticalAdvectionHalf w t +
          criticalPressureHalf w t + criticalForceHalf (f := f) t := by
  exact criticalVelocityHalf_momentum hν hf w
