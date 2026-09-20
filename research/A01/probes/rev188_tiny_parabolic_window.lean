import NSFormalization.Section4.A01.MildUniqueness

noncomputable section
namespace NSFormalization.Section4.A01
open Set EulerCylinderSobolevSpace EulerQuadraticSource
open EulerSobolevHeat EulerVolterraConvolution
open scoped Topology NNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
private local instance probeSobolevGroup (q : ℕ) :
    NormedAddCommGroup (SobolevSpace 1 q) := inferInstance
private local instance probeSobolevSpace (q : ℕ) :
    NormedSpace ℝ (SobolevSpace 1 q) := inferInstance

/-- The window estimate specializes to an arbitrarily tiny window for the
inverse-square-root parabolic majorant; the factor remains exactly its mass on
that tiny window. -/
example {q : ℕ} {ν S a δ : ℝ} (hν : 0 < ν) (hS : 0 < S) (ha : 0 ≤ a)
    (hδ : 0 < δ) (htiny : δ ≤ S / 100) (haδ : a + δ ≤ S)
    (d : C(Icc (0 : ℝ) S, SobolevSpace 1 (q+1)))
    (f : C(Icc (0 : ℝ) S, SobolevSpace 1 q)) (L : ℝ) (hL : 0 ≤ L)
    (hf : ∀ t, ‖f t‖ ≤ L * ‖d t‖)
    (hd : d = convolution S hS.le (heatKernel 1 q ν hν) (parabolicKernelBound ν)
      (heatKernel_joint_continuous 1 q ν hν)
      (parabolicKernelBound_integrable ν S hS.le)
      (fun r hr => parabolicKernelBound_nonneg ν r hr.1)
      (fun r hr y => heatKernel_bound 1 q ν hν r hr.1 y) f)
    (hpast : ∀ t : Icc (0 : ℝ) S, t.val ≤ a → d t = 0) :
    ‖d.comp (timeInclusion haδ)‖ ≤
      (kernelMass δ (parabolicKernelBound ν) * L) * ‖d.comp (timeInclusion haδ)‖ := by
  have hδS : δ ≤ S := by linarith
  exact volterra_window_bound hS.le (heatKernel 1 q ν hν) (parabolicKernelBound ν)
    (heatKernel_joint_continuous 1 q ν hν)
    (parabolicKernelBound_integrable ν S hS.le)
    (fun r hr => parabolicKernelBound_nonneg ν r hr.1)
    (fun r hr y => heatKernel_bound 1 q ν hν r hr.1 y)
    d f L hL hf hd (by positivity) haδ hδS le_rfl hpast

end NSFormalization.Section4.A01
