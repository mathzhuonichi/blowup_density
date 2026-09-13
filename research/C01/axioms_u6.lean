import Contracts.V1.Data
import Contracts.V1.GradientL6
import Bindings.GradientL6
import NSFormalization.Section4.C01.Trilinear

/-!
# C01 unit U6 conformance check

The three spec fields `trilinearHolder`, `trilinearAbsorbed`, `laplacianSqENorm`
of `BlowupDensity.C01.Draft.EnergyAbsorptionAPI` (`research/C01/Spec.lean:410-473`),
written here in the **contract's own vocabulary** (`Contracts.V1.gradientTensor`,
`Contracts.V1.laplacian`, `Contracts.V1.SmoothSquareIntegrableJets`, and the spec
`def`s `advectionWork`, `criticalL3`, `laplacianSq` restated token-for-token from
`Spec.lean`), each discharged by the corresponding theorem of
`NSFormalization.Section4.C01`.

`C₁` in `trilinearAbsorbed` is taken as `BlowupDensity.Bindings.gradientL6.Csix`, i.e. the
constant of the **registered** gradient-`L⁶` contract `A05.gradient_l6`
(`= NSFormalization.Section4.A05.gradientL6Const`, `verification/Bindings/GradientL6.lean:43`).

`lake env lean` from `verification/`; `#print axioms` at the bottom must show only
`[propext, Classical.choice, Quot.sound]`.
-/

noncomputable section

open Set MeasureTheory
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1
  (lift gradientTensor laplacian SmoothSquareIntegrableJets)
open BlowupDensity.Contracts.V1.Data
open scoped ENNReal

namespace C01ConformanceU6

/-- `research/C01/Spec.lean:202` `advectionWork`, in the contract's vocabulary. -/
def advectionWork (z : SpatialField) : ℝ :=
  ∫ x : Space, (inner ℝ (advection (lift z) 0 x) (laplacian z x) : ℝ)

/-- `research/C01/Spec.lean:212` `criticalL3`. -/
def criticalL3 (z : SpatialField) : ℝ≥0∞ := eLpNorm z 3 volume

/-- `research/C01/Spec.lean:191` `laplacianSq`. -/
def laplacianSq (z : SpatialField) : ℝ := ∫ x : Space, ‖laplacian z x‖ ^ 2

/-- Spec field `trilinearHolder` (`Spec.lean:410`). -/
example : ∀ z : SpatialField, SmoothSquareIntegrableJets z →
    ENNReal.ofReal |advectionWork z| ≤
      criticalL3 z * eLpNorm (gradientTensor z) 6 volume * eLpNorm (laplacian z) 2 volume :=
  fun z hz => NSFormalization.Section4.C01.trilinearHolder z hz

/-- Spec field `trilinearAbsorbed` (`Spec.lean:435`), with `C₁ = gradientL6.Csix`. -/
example : ∀ z : SpatialField, SmoothSquareIntegrableJets z →
    ENNReal.ofReal |advectionWork z| ≤
      ENNReal.ofReal (BlowupDensity.Bindings.gradientL6.Csix) * criticalL3 z *
        eLpNorm (laplacian z) 2 volume ^ (2 : ℝ) :=
  fun z hz => NSFormalization.Section4.C01.trilinearAbsorbed z hz

/-- Spec field `laplacianSqENorm` (`Spec.lean:471`). -/
example : ∀ z : SpatialField, SmoothSquareIntegrableJets z →
    eLpNorm (laplacian z) 2 volume ^ (2 : ℝ) = ENNReal.ofReal (laplacianSq z) :=
  fun z hz => NSFormalization.Section4.C01.laplacianSqENorm z hz

/-- Certified lintegral bound behind `trilinearHolder` (review finding 1). -/
example : ∀ z : SpatialField, SmoothSquareIntegrableJets z →
    ∫⁻ x, ‖(inner ℝ (advection (lift z) 0 x) (laplacian z x) : ℝ)‖ₑ ∂volume ≤
      criticalL3 z * eLpNorm (gradientTensor z) 6 volume * eLpNorm (laplacian z) 2 volume :=
  fun z hz => NSFormalization.Section4.C01.lintegral_advection_inner_laplacian_le z hz

/-- `advectionWork z` is the true integral (not junk `0`) once `‖z‖₃ < ⊤`
(review finding 1); the certified non-junk fact U7's `enstrophyIdentity` needs. -/
example : ∀ z : SpatialField, SmoothSquareIntegrableJets z → criticalL3 z ≠ ⊤ →
    Integrable (fun x => (inner ℝ (advection (lift z) 0 x) (laplacian z x) : ℝ)) volume :=
  fun z hz hL3 => NSFormalization.Section4.C01.integrable_advection_inner_laplacian z hz hL3

end C01ConformanceU6

#print axioms NSFormalization.Section4.C01.trilinearHolder
#print axioms NSFormalization.Section4.C01.trilinearAbsorbed
#print axioms NSFormalization.Section4.C01.laplacianSqENorm
#print axioms NSFormalization.Section4.C01.lintegral_advection_inner_laplacian_le
#print axioms NSFormalization.Section4.C01.integrable_advection_inner_laplacian
