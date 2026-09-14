import NSFormalization.Section4.D01.LerayLowering

open Set MeasureTheory FourierTransform NavierStokes.ProblemStatement
open NSFormalization.Paper3
open NSFormalization.Source NSFormalization.Source.RealSobolev
open scoped ENNReal ComplexConjugate

namespace Probe

-- IsSobolevDatum (D01 restatement)
#check @NSFormalization.Section4.D01.IsSobolevDatum
-- angular order lowering raw coeFn (angular convention, simplified Bessel form)
#check @NSFormalization.Section4.D01.Leray.angularOrderLowering_coeFn'
-- angular realization is preserved by order lowering
#check @angularRealization_orderLowering
-- sobolevBesselWeight and its multiplicativity
#check @sobolevBesselWeight
#check @sobolevBesselWeight_mul
-- reality subspace machinery
#check @realSymmetry_ae
#check @mem_realSubspace_iff
#check @RealSobolevHilbert
-- RealVectorSobolev is a PiLp over Fin 3
#check @RealVectorSobolev
-- angularOrderLowering CLM
#check @angularOrderLowering
-- Space norm expansion
example (ξ : Space) : ‖ξ‖ = Real.sqrt (∑ i, ‖ξ i‖ ^ 2) := EuclideanSpace.norm_eq ξ
-- MemLp.toLp and coeFn
#check @MemLp.toLp
#check @MemLp.coeFn_toLp
-- Lp.ext
#check @Lp.ext
-- WithLp.toLp for building RealVectorSobolev
example (s : ℝ) (f : Fin 3 → RealSobolevHilbert s) : RealVectorSobolev s := WithLp.toLp 2 f
example (s : ℝ) (f : Fin 3 → RealSobolevHilbert s) (i : Fin 3) :
    (WithLp.toLp 2 f : RealVectorSobolev s) i = f i := rfl

end Probe
