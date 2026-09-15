import NSFormalization.Section4.D01.FiniteOrderConstructor
open MeasureTheory NSFormalization.Source NSFormalization.Source.RealSobolev
open scoped ENNReal
noncomputable section
-- Plancherel
#check @Lp.norm_fourier_eq
-- MemLp.norm_toLp
#check @MemLp.norm_toLp
#check @Lp.norm_toLp
-- PiLp norm sq
#check @PiLp.norm_sq_eq_of_L2
-- eLpNorm lemmas
#check @eLpNorm_mono
#check @eLpNorm_add_le
#check @eLpNorm_norm
#check @eLpNorm_const_smul
-- coordinate bound EuclideanSpace
example (x : EuclideanSpace ℝ (Fin 3)) (i : Fin 3) : ‖x i‖ ≤ ‖x‖ := by exact?
