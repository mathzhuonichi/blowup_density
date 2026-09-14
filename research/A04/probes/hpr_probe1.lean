import NSFormalization.Section4.D01.PressureJets
import NSFormalization.Section4.D01.RealPairing
import Mathlib.Analysis.InnerProductSpace.Adjoint

open Set MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Paper3 (RealVectorSobolev)
open NSFormalization.Source.RealSobolev (FourierData RealSobolevHilbert)
open NSFormalization.Section4.D01
open NSFormalization.Section4.D01.Leray
open NSFormalization.Source.FiniteHilbertBochner (assemble coordinates coord Product)
open scoped ComplexConjugate

namespace Probe1

-- (H1) bilinear coordinates inner
theorem coordinates_inner_bilin {ι : Type*} [Fintype ι] {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (b b' : Lp (Product ι ℂ) 2 μ) :
    (inner ℂ (WithLp.toLp 2 (coordinates 2 μ b) : Product ι (Lp ℂ 2 μ))
      (WithLp.toLp 2 (coordinates 2 μ b')) : ℂ) = inner ℂ b b' := by
  rw [PiLp.inner_apply]
  have key : ∀ i, (inner ℂ (coordinates 2 μ b i) (coordinates 2 μ b' i) : ℂ)
      = ∫ t, (inner ℂ ((coordinates 2 μ b i) t) ((coordinates 2 μ b' i) t) : ℂ) ∂μ :=
    fun i => L2.inner_def _ _
  simp_rw [key]
  rw [← MeasureTheory.integral_finsetSum Finset.univ
      (fun i (_ : i ∈ Finset.univ) =>
        L2.integrable_inner (coordinates 2 μ b i) (coordinates 2 μ b' i)),
    L2.inner_def b b']
  refine integral_congr_ae ?_
  filter_upwards [ae_all_iff.2 (fun i => coordinates_ae μ b i),
    ae_all_iff.2 (fun i => coordinates_ae μ b' i)] with t ht ht'
  rw [PiLp.inner_apply]
  exact Finset.sum_congr rfl (fun i _ => by rw [ht i, ht' i])

-- fibre self-adjointness
theorem complementSymbolComplex_inner_left (ξ : MNS2.R3) (v w : MNS2.R3C) :
    (inner ℂ (complementSymbolComplex ξ v) w : ℂ) = inner ℂ v (complementSymbolComplex ξ w) := by
  have hsym := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (isSelfAdjoint_starProjection (ℂ ∙ MNS2.r3FrequencyVectorComplex ξ)))
  exact hsym v w

-- (H2) lerayComplementL2 complex self-adjoint
theorem lerayComplementL2_inner_left (x y : MNS2.R3L2Velocity) :
    (inner ℂ (lerayComplementL2 x) y : ℂ) = inner ℂ x (lerayComplementL2 y) := by
  rw [L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [lerayComplementL2_ae x, lerayComplementL2_ae y] with ξ hx hy
  rw [hx, hy]
  exact complementSymbolComplex_inner_left ξ (x ξ) (y ξ)

end Probe1
