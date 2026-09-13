import NavierStokes.R3WeakPressure

/-!
# The smooth momentum equation supplies the pressure representation

All representation identities use compact test functions. Only the velocity
and stress, rather than their derivatives or the pressure, require global
integrability.
-/

noncomputable section
namespace NavierStokes.R3WeakPressure

open Set Filter MeasureTheory TemperedDistribution FourierTransform
open R3SpaceTime R3SpaceTimePressure
open scoped SchwartzMap LineDeriv Topology ContDiff ENNReal

theorem represents_zero : Represents (0 : 𝓢'(Domain, ℂ)) (fun _ => 0) := by
  intro φ _
  simp

theorem Represents.congr {T : 𝓢'(Domain, ℂ)} {f g : Domain → ℂ}
    (hT : Represents T f) (he : f = g) : Represents T g := he ▸ hT

theorem Represents.add {S T : 𝓢'(Domain, ℂ)} {f g : Domain → ℂ}
    (hS : Represents S f) (hT : Represents T g) (hf : Continuous f) (hg : Continuous g) :
    Represents (S + T) (fun z => f z + g z) := by
  intro φ hφ
  rw [add_apply, hS φ hφ, hT φ hφ]
  simp_rw [mul_add]
  exact (integral_add
    ((φ.continuous.mul hf).integrable_of_hasCompactSupport hφ.mul_right)
    ((φ.continuous.mul hg).integrable_of_hasCompactSupport hφ.mul_right)).symm

theorem Represents.neg {T : 𝓢'(Domain, ℂ)} {f : Domain → ℂ}
    (hT : Represents T f) : Represents (-T) (fun z => -f z) := by
  intro φ hφ
  rw [neg_apply, hT φ hφ]
  simp only [mul_neg, integral_neg]

theorem Represents.sub {S T : 𝓢'(Domain, ℂ)} {f g : Domain → ℂ}
    (hS : Represents S f) (hT : Represents T g) (hf : Continuous f) (hg : Continuous g) :
    Represents (S - T) (fun z => f z - g z) := by
  simpa only [sub_eq_add_neg] using hS.add hT.neg hf hg.neg

theorem Represents.sum {ι : Type*} (s : Finset ι) (T : ι → 𝓢'(Domain, ℂ))
    (f : ι → Domain → ℂ) (hT : ∀ i ∈ s, Represents (T i) (f i))
    (hf : ∀ i ∈ s, Continuous (f i)) : Represents (∑ i ∈ s, T i) (fun z => ∑ i ∈ s, f i z) := by
  intro φ hφ
  simp only [sum_apply, Finset.mul_sum]
  rw [integral_finsetSum _ (fun i hi => show Integrable (fun z => φ z * f i z) from
    (φ.continuous.mul (hf i hi)).integrable_of_hasCompactSupport hφ.mul_right)]
  apply Finset.sum_congr rfl
  intro i hi
  exact hT i hi φ hφ

def functionLaplacian (f : Domain → ℂ) (z : Domain) : ℂ :=
  ∑ i, directional (spaceDirection i) (directional (spaceDirection i) f) z

theorem functionLaplacian_contDiff {f : Domain → ℂ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (functionLaplacian f) := by
  exact ContDiff.sum fun i _ => partial_contDiff (partial_contDiff hf _) _

theorem Represents.spatialLaplacian {T : 𝓢'(Domain, ℂ)} {f : Domain → ℂ}
    (hT : Represents T f) (hf : ContDiff ℝ ∞ f) :
    Represents (spatialLaplacian T) (functionLaplacian f) := by
  apply Represents.sum
  · intro i _
    exact (hT.lineDeriv (hf.of_le (by simp)) _).lineDeriv
      ((partial_contDiff hf _).of_le (by simp)) _
  · intro i _
    exact (partial_contDiff (partial_contDiff hf _) _).continuous

def functionDivergence (U : Fin 3 → Domain → ℂ) (z : Domain) : ℂ :=
  ∑ i, directional (spaceDirection i) (U i) z

theorem divergence_zero_of_smooth (U : Fin 3 → Domain → ℂ)
    (hU : ∀ i, MemLp (U i) 2) (hs : ∀ i, ContDiff ℝ ∞ (U i))
    (hd : ∀ z, functionDivergence U z = 0) :
    divergence (fun i => ((hU i).toLp (U i) : 𝓢'(Domain, ℂ))) = 0 := by
  have hr : Represents (divergence (fun i => ((hU i).toLp (U i) : 𝓢'(Domain, ℂ))))
      (functionDivergence U) := by
    apply Represents.sum
    · intro i _
      exact (represents_lp (hU i)).lineDeriv ((hs i).of_le (by simp)) _
    · intro i _
      exact (partial_contDiff (hs i) _).continuous
  exact (hr.congr (funext hd)).ext represents_zero

def functionMomentum (U V : Fin 3 → Domain → ℂ) (G : Fin 3 → Fin 3 → Domain → ℂ)
    (i : Fin 3) (z : Domain) : ℂ :=
  functionLaplacian (U i) z - directional timeDirection (U i) z + V i z -
    ∑ j, directional (spaceDirection j) (G i j) z

theorem represents_momentumGradient
    (U V : Fin 3 → Domain → ℂ) (G : Fin 3 → Fin 3 → Domain → ℂ)
    (hU : ∀ i, MemLp (U i) 2) (hV : ∀ i, MemLp (V i) 2)
    (hG : ∀ i j, MemLp (G i j) 1)
    (sU : ∀ i, ContDiff ℝ ∞ (U i)) (sV : ∀ i, ContDiff ℝ ∞ (V i))
    (sG : ∀ i j, ContDiff ℝ ∞ (G i j)) (i : Fin 3) :
    Represents (momentumGradient (fun i => (hU i).toLp (U i))
      (fun i => (hV i).toLp (V i)) (fun i j => (hG i j).toLp (G i j)) i)
      (functionMomentum U V G i) := by
  apply Represents.sub
  · apply Represents.add
    · exact ((represents_lp (hU i)).spatialLaplacian (sU i)).sub
        ((represents_lp (hU i)).lineDeriv ((sU i).of_le (by simp)) _)
        (functionLaplacian_contDiff (sU i)).continuous (partial_contDiff (sU i) _).continuous
    · exact represents_lp (hV i)
    · exact (functionLaplacian_contDiff (sU i)).continuous.sub (partial_contDiff (sU i) _).continuous
    · exact (sV i).continuous
  · apply Represents.sum
    · intro j _
      exact (represents_lp (hG i j)).lineDeriv ((sG i j).of_le (by simp)) _
    · intro j _
      exact (partial_contDiff (sG i j) _).continuous
  · exact ((functionLaplacian_contDiff (sU i)).continuous.sub
      (partial_contDiff (sU i) _).continuous).add (sV i).continuous
  · exact continuous_finsetSum _ fun j _ => (partial_contDiff (sG i j) _).continuous

/-- Direct pressure recovery from a smooth, divergence-free momentum
identity. This is the form used after multiplying the equation by a compact
time cutoff. -/
theorem smooth_pressure_gradient
    (U V : Fin 3 → Domain → ℂ) (G : Fin 3 → Fin 3 → Domain → ℂ) (p : Domain → ℂ)
    (hU : ∀ i, MemLp (U i) 2) (hV : ∀ i, MemLp (V i) 2)
    (hG : ∀ i j, MemLp (G i j) 1)
    (sU : ∀ i, ContDiff ℝ ∞ (U i)) (sV : ∀ i, ContDiff ℝ ∞ (V i))
    (sG : ∀ i j, ContDiff ℝ ∞ (G i j)) (sp : ContDiff ℝ ∞ p)
    (dU : ∀ z, functionDivergence U z = 0) (dV : ∀ z, functionDivergence V z = 0)
    (heq : ∀ i z, functionMomentum U V G i z = directional (spaceDirection i) p z)
    (i : Fin 3) :
    Represents (∂_{spaceDirection i} (stressPressure (fun i j => (hG i j).toLp (G i j))))
      (directional (spaceDirection i) p) := by
  let UL i := (hU i).toLp (U i)
  let VL i := (hV i).toLp (V i)
  let stressLp (i j : Fin 3) := (hG i j).toLp (G i j)
  have hrep i : Represents (momentumGradient UL VL stressLp i) (directional (spaceDirection i) p) :=
    (represents_momentumGradient U V G hU hV hG sU sV sG i).congr (funext (heq i))
  have hn i := pressure_gradient_unique UL VL stressLp p
    (divergence_zero_of_smooth U hU sU dU) (divergence_zero_of_smooth V hV sV dV)
    (fun i φ hφ => (hrep i φ hφ).trans (integration_by_parts (sp.of_le (by simp)) φ hφ _)) i
  rw [← hn i]
  exact hrep i

end NavierStokes.R3WeakPressure
