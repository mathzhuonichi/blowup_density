import NavierStokes.R3PressureFourier
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Euclidean space-time for pressure recovery

The `L²` product of time and three-space has the product Lebesgue measure.
A compact time cutoff of a uniformly finite-energy velocity therefore lives
in an ordinary Sobolev space on this four-dimensional inner product space.
-/

noncomputable section
namespace NavierStokes.R3SpaceTime

open Set Filter MeasureTheory ProblemStatement FourierTransform TemperedDistribution
open scoped SchwartzMap LineDeriv Topology RealInnerProductSpace

abbrev Domain := WithLp 2 (ℝ × Space)

def timeProj : Domain →L[ℝ] ℝ := WithLp.fstL 2 ℝ ℝ Space

def spaceProj : Domain →L[ℝ] Space := WithLp.sndL 2 ℝ ℝ Space

def timeDirection : Domain := WithLp.toLp 2 (1, (0 : Space))

def spaceDirection (i : Fin 3) : Domain := WithLp.toLp 2 (0, coordinateVector i)

def pack (t : ℝ) (x : Space) : Domain := WithLp.toLp 2 (t, x)

@[simp] theorem timeProj_pack (t : ℝ) (x : Space) : timeProj (pack t x) = t := rfl
@[simp] theorem spaceProj_pack (t : ℝ) (x : Space) : spaceProj (pack t x) = x := rfl
@[simp] theorem pack_proj (z : Domain) : pack (timeProj z) (spaceProj z) = z := rfl

theorem finrank_domain : Module.finrank ℝ Domain = 4 := by
  rw [(WithLp.linearEquiv 2 ℝ (ℝ × Space)).finrank_eq, Module.finrank_prod]
  norm_num

theorem norm_spaceProj_le (z : Domain) : ‖spaceProj z‖ ≤ ‖z‖ := WithLp.norm_snd_le ℝ z

theorem integral_eq_prod {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Domain → F) : (∫ z : Domain, f z) = ∫ tx : ℝ × Space, f (pack tx.1 tx.2) :=
  ((WithLp.volume_preserving_toLp ℝ Space).integral_comp
    (MeasurableEquiv.toLp 2 (ℝ × Space)).measurableEmbedding f).symm

theorem integrable_iff_prod {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Domain → F) : Integrable f ↔ Integrable (fun tx : ℝ × Space => f (pack tx.1 tx.2)) :=
  ((WithLp.volume_preserving_toLp ℝ Space).integrable_comp_emb
    (MeasurableEquiv.toLp 2 (ℝ × Space)).measurableEmbedding).symm

theorem volume_spatial_zero : volume {z : Domain | spaceProj z = 0} = 0 := by
  have he : {z : Domain | spaceProj z = 0} = WithLp.ofLp ⁻¹' (univ ×ˢ ({0} : Set Space)) := by
    ext z
    simp [spaceProj, WithLp.sndL]
  rw [he, (WithLp.volume_preserving_ofLp ℝ Space).measure_preimage (by measurability)]
  change ((volume : Measure ℝ).prod (volume : Measure Space)) (univ ×ˢ {0}) = 0
  rw [Measure.prod_prod]
  simp

theorem inner_spaceDirection (z : Domain) (i : Fin 3) : inner ℝ z (spaceDirection i) = spaceProj z i := by
  simp [spaceDirection, WithLp.prod_inner_apply, spaceProj, WithLp.sndL,
    coordinateVector, EuclideanSpace.inner_single_right]

def coordinateSymbol (i : Fin 3) (z : Domain) : ℂ := (spaceProj z i : ℝ)

def laplacianSymbol (z : Domain) : ℂ := (‖spaceProj z‖ ^ 2 : ℝ)

def spatialLaplacian (f : 𝓢'(Domain, ℂ)) : 𝓢'(Domain, ℂ) :=
  ∑ i : Fin 3, ∂_{spaceDirection i} (∂_{spaceDirection i} f)

theorem coordinateSymbol_temperate (i : Fin 3) : (coordinateSymbol i).HasTemperateGrowth := by
  exact (Complex.ofRealCLM.comp ((EuclideanSpace.proj i).comp spaceProj)).hasTemperateGrowth

theorem laplacianSymbol_temperate : laplacianSymbol.HasTemperateGrowth := by
  exact Complex.ofRealCLM.hasTemperateGrowth.comp
    ((Function.hasTemperateGrowth_norm_sq Space).comp spaceProj.hasTemperateGrowth)

theorem laplacianSymbol_eq_sum : laplacianSymbol = ∑ i : Fin 3, coordinateSymbol i * coordinateSymbol i := by
  funext z
  simp only [laplacianSymbol, coordinateSymbol, Finset.sum_apply, Pi.mul_apply]
  rw [PiLp.norm_sq_eq_of_L2]
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  simp only [Real.norm_eq_abs]
  norm_cast
  simpa only [pow_two] using sq_abs (spaceProj z i)

theorem fourier_second_derivative (i j : Fin 3) (f : 𝓢'(Domain, ℂ)) :
    𝓕 (∂_{spaceDirection i} (∂_{spaceDirection j} f)) =
      -(2 * Real.pi : ℂ) ^ 2 •
        smulLeftCLM ℂ (coordinateSymbol i * coordinateSymbol j) (𝓕 f) := by
  rw [fourier_lineDerivOp_eq, fourier_lineDerivOp_eq]
  have he (i : Fin 3) : (fun z : Domain => Complex.ofReal (inner ℝ z (spaceDirection i))) = coordinateSymbol i := by
    funext z
    rw [inner_spaceDirection]
    rfl
  rw [he i, he j, map_smul, smul_smul,
    smulLeftCLM_smulLeftCLM_apply (coordinateSymbol_temperate j) (coordinateSymbol_temperate i),
    mul_comm (coordinateSymbol j) (coordinateSymbol i)]
  congr 1
  ring_nf
  simp

theorem fourier_spatialLaplacian (f : 𝓢'(Domain, ℂ)) :
    𝓕 (spatialLaplacian f) = -(2 * Real.pi : ℂ) ^ 2 • smulLeftCLM ℂ laplacianSymbol (𝓕 f) := by
  rw [spatialLaplacian, fourier_sum]
  simp only [fourier_second_derivative]
  rw [← Finset.smul_sum, laplacianSymbol_eq_sum]
  congr 1
  change (∑ i : Fin 3, (smulLeftCLM ℂ (coordinateSymbol i * coordinateSymbol i)) (𝓕 f)) =
    (smulLeftCLM ℂ (fun z => ∑ i : Fin 3, (coordinateSymbol i * coordinateSymbol i) z)) (𝓕 f)
  rw [smulLeftCLM_sum (fun i _ => (coordinateSymbol_temperate i).mul (coordinateSymbol_temperate i))]
  simp only [sum_apply]

end NavierStokes.R3SpaceTime
