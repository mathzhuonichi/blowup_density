import NSFormalization.Paper3.SobolevDirectionalDerivative
import NSFormalization.Source.WeakClassicalDerivative
import Euler.ParameterWordHigher
import Euler.LpFiniteTensorReconstruction
import Euler.LpSmoothFieldJets

noncomputable section
namespace NSFormalization.Source.FourierPhysicalJets
open MeasureTheory FourierTransform NavierStokes.ProblemStatement
open NSFormalization.Paper3 EulerParameterWordGevrey
open scoped SchwartzMap LineDeriv ENNReal ContDiff

/-- Physical identification is initially required only on compact tests. -/
def CompactRep (s : ℝ) (h : SobolevHilbert s) (f : Space → ℂ) : Prop :=
  ∀ ψ : SchwartzMap Space ℂ, HasCompactSupport (ψ : Space → ℂ) →
    sobolevRealization s h ψ = ∫ x : Space, ψ x • f x

/-- The actual physical L2 class obtained by lowering and inverse Fourier. -/
def physicalLp (s : ℝ) (hs : 0 ≤ s) : SobolevHilbert s →L[ℂ] Lp ℂ 2 (volume : Measure Space) :=
  (fourierInvCLM ℂ (Lp ℂ 2 (volume : Measure Space))).comp (sobolevOrderLowering s 0 hs)

theorem physicalLp_distribution (s : ℝ) (hs : 0 ≤ s) (h : SobolevHilbert s) :
    (physicalLp s hs h : 𝓢'(Space, ℂ)) = sobolevRealization s h := by
  change ((𝓕⁻ (sobolevOrderLowering s 0 hs h) : Lp ℂ 2 (volume : Measure Space)) : 𝓢'(Space, ℂ)) = _
  rw [← sobolevRealization_zero,
    sobolevRealization_orderLowering]

theorem physicalLp_ae {s : ℝ} (hs : 0 ≤ s) {h : SobolevHilbert s} {f : Space → ℂ}
    (hf : Continuous f) (hrep : CompactRep s h f) :
    (physicalLp s hs h : Space → ℂ) =ᵐ[volume] f := by
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp _).locallyIntegrable (by norm_num)) hf.locallyIntegrable
  intro g hg hgc
  have hc : HasCompactSupport (Complex.ofRealCLM ∘ g) := hgc.comp_left rfl
  have hd : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) := by fun_prop
  let ψ := hc.toSchwartzMap hd
  calc
    _ = (physicalLp s hs h : 𝓢'(Space, ℂ)) ψ := by simp [ψ]
    _ = sobolevRealization s h ψ := by rw [physicalLp_distribution]
    _ = ∫ x : Space, ψ x • f x := hrep ψ hc
    _ = _ := by simp [ψ]

theorem compactRep_of_physicalLp_ae {s : ℝ} (hs : 0 ≤ s)
    {h : SobolevHilbert s} {f : Space → ℂ}
    (he : (physicalLp s hs h : Space → ℂ) =ᵐ[volume] f) : CompactRep s h f := by
  intro ψ _
  rw [← physicalLp_distribution s hs h, Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [he] with x hx
  rw [hx]

/-- The bounded Fourier derivative realizes the classical derivative; its
weak-derivative premise is derived, not assumed. -/
theorem compactRep_directional (n : ℕ) {f : Space → ℂ} (hf : ContDiff ℝ ∞ f)
    (h : SobolevHilbert (n + 1)) (hrep : CompactRep (n + 1) h f) (a : Space) :
    CompactRep n (sobolevDirectionalDerivative (n + 1) a h)
      (fun x => fderiv ℝ f x a) := by
  have hs : (0 : ℝ) ≤ n + 1 := by positivity
  have hn : (0 : ℝ) ≤ n := by positivity
  have hu := physicalLp_ae hs hf.continuous hrep
  have hD : ∂_{a} (physicalLp (n + 1) hs h : 𝓢'(Space, ℂ)) =
      (physicalLp n hn (sobolevDirectionalDerivative (n + 1) a h) : 𝓢'(Space, ℂ)) := by
    rw [physicalLp_distribution, physicalLp_distribution]
    convert (sobolevRealization_directionalDerivative (n + 1) a h).symm using 2
    congr 1
    ring
  exact compactRep_of_physicalLp_ae hn
    (WeakClassicalDerivative.ae_eq_classical_derivative (hf.of_le (by simp)) _ _ a hu hD)

/-- Ordered coordinate derivatives as explicit bounded maps to physical L2. -/
def coordinateWordLp : (n : ℕ) → (Fin n → Fin 3) →
    SobolevHilbert n →L[ℂ] Lp ℂ 2 (volume : Measure Space)
  | 0, _ => physicalLp 0 (by norm_num)
  | n + 1, w => (coordinateWordLp n (Fin.init w)).comp
      (sobolevDirectionalDerivative (n + 1) (EulerLpFiniteTensor.direction (w (Fin.last n))))

/-- The explicit Fourier word class is the actual classical coordinate word. -/
theorem coordinateWordLp_ae (n : ℕ) (w : Fin n → Fin 3) {f : Space → ℂ}
    (hf : ContDiff ℝ ∞ f) (h : SobolevHilbert n) (hrep : CompactRep n h f) :
    (coordinateWordLp n w h : Space → ℂ) =ᵐ[volume]
      wordDerivative EulerLpFiniteTensor.direction f w := by
  induction n generalizing f with
  | zero =>
    have hrep0 : CompactRep 0 h f := by
      convert hrep using 1
      norm_num
    have H := physicalLp_ae (s := 0) (h := h) (f := f) (by norm_num) hf.continuous hrep0
    change (physicalLp 0 (by norm_num) h : Space → ℂ) =ᵐ[volume] _
    rw [show wordDerivative EulerLpFiniteTensor.direction f w = f from
      funext (wordDerivative_zero EulerLpFiniteTensor.direction f w)]
    exact H
  | succ n ih =>
    have hreps : CompactRep ((n : ℝ) + 1) h f := by
      convert hrep using 1
      push_cast
      rfl
    have H := ih (Fin.init w)
      (directional_contDiff EulerLpFiniteTensor.direction f hf (w (Fin.last n)))
      (sobolevDirectionalDerivative (n + 1) (EulerLpFiniteTensor.direction (w (Fin.last n))) h)
      (compactRep_directional n hf h hreps (EulerLpFiniteTensor.direction (w (Fin.last n))))
    have hw : wordDerivative EulerLpFiniteTensor.direction f w =
        wordDerivative EulerLpFiniteTensor.direction
          (directional EulerLpFiniteTensor.direction f (w (Fin.last n))) (Fin.init w) := by
      funext x
      simpa only [Fin.snoc_init_self] using
        wordDerivative_snoc EulerLpFiniteTensor.direction f hf (Fin.init w) (w (Fin.last n)) x
    rw [hw]
    exact H

/-- Complexification of one literal real-vector component. -/
def complexComponent (i : Fin 3) : Space →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (EuclideanSpace.proj i)

/-- Take real parts and assemble the actual Euclidean vector. -/
def complexTupleToVector : (Fin 3 → ℂ) →L[ℝ] Space :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => Complex.reCLM.comp (ContinuousLinearMap.proj i)))

def vectorLpReassembly : (Fin 3 → Lp ℂ 2 (volume : Measure Space)) →L[ℝ]
    Lp Space 2 (volume : Measure Space) :=
  (complexTupleToVector.compLpL 2 volume).comp (EulerLpFiniteTensor.tupleLp volume)

theorem vectorLpReassembly_ae (u : Fin 3 → Lp ℂ 2 (volume : Measure Space)) :
    (vectorLpReassembly u : Space → Space) =ᵐ[volume]
      fun x => complexTupleToVector (fun i => u i x) := by
  filter_upwards [complexTupleToVector.coeFn_compLpL (EulerLpFiniteTensor.tupleLp volume u),
    EulerLpFiniteTensor.tupleLp_ae volume u] with x hx hu
  exact hx.trans (congrArg complexTupleToVector hu)

def vectorWordLp (n : ℕ) (w : Fin n → Fin 3) :
    (Fin 3 → SobolevHilbert n) →L[ℝ] Lp Space 2 (volume : Measure Space) :=
  vectorLpReassembly.comp (ContinuousLinearMap.pi (fun i =>
    ((coordinateWordLp n w).restrictScalars ℝ).comp (ContinuousLinearMap.proj i)))

theorem vectorWordLp_ae (n : ℕ) (w : Fin n → Fin 3) {f : Space → Space}
    (hf : ContDiff ℝ ∞ f) (h : Fin 3 → SobolevHilbert n)
    (hrep : ∀ i, CompactRep n (h i) (fun x => (f x i : ℂ))) :
    (vectorWordLp n w h : Space → Space) =ᵐ[volume]
      wordDerivative EulerLpFiniteTensor.direction f w := by
  have hi (i : Fin 3) : (coordinateWordLp n w (h i) : Space → ℂ) =ᵐ[volume]
      wordDerivative EulerLpFiniteTensor.direction (complexComponent i ∘ f) w :=
    coordinateWordLp_ae n w ((complexComponent i).contDiff.comp hf) (h i) (hrep i)
  change (vectorLpReassembly (fun i => coordinateWordLp n w (h i)) : Space → Space) =ᵐ[volume] _
  filter_upwards [vectorLpReassembly_ae (fun i => coordinateWordLp n w (h i)),
    ae_all_iff.mpr hi] with x hx hix
  rw [hx]
  ext i
  change (coordinateWordLp n w (h i) x).re =
    wordDerivative EulerLpFiniteTensor.direction f w x i
  rw [hix i, wordDerivative_comp_clm EulerLpFiniteTensor.direction (complexComponent i) f hf w x]
  rfl

/-- Literal Fréchet tensor data reconstructed by the existing bounded map. -/
def physicalJetLp (n : ℕ) : (Fin 3 → SobolevHilbert n) →L[ℝ]
    Lp (Space [×n]→L[ℝ] Space) 2 (volume : Measure Space) :=
  (EulerLpFiniteTensor.tensorLpReassembly volume n).comp
    (ContinuousLinearMap.pi (vectorWordLp n))

theorem physicalJetLp_ae (n : ℕ) {f : Space → Space} (hf : ContDiff ℝ ∞ f)
    (h : Fin 3 → SobolevHilbert n)
    (hrep : ∀ i, CompactRep n (h i) (fun x => (f x i : ℂ))) :
    (physicalJetLp n h : Space → (Space [×n]→L[ℝ] Space)) =ᵐ[volume]
      iteratedFDeriv ℝ n f := by
  exact EulerLpFiniteTensor.tensorLpReassembly_eq_ae volume n
    (fun w => vectorWordLp n w h) (iteratedFDeriv ℝ n f)
    (fun w => vectorWordLp_ae n w hf h hrep)

/-- Build the original smooth field with its now-proved actual L2 jets. -/
def smoothL2FieldOfFourier (f : Space → Space) (hf : ContDiff ℝ ∞ f)
    (h : ∀ n : ℕ, Fin 3 → SobolevHilbert n)
    (hrep : ∀ (n : ℕ) i, CompactRep n (h n i) (fun x => (f x i : ℂ))) :
    EulerLpTranslation.SmoothL2Field Space where
  field := f
  smooth := hf
  integrable n := (memLp_congr_ae (physicalJetLp_ae n hf (h n) (hrep n))).mp (Lp.memLp _)

theorem smoothL2FieldOfFourier_jetLp (f : Space → Space) (hf : ContDiff ℝ ∞ f)
    (h : ∀ n : ℕ, Fin 3 → SobolevHilbert n)
    (hrep : ∀ (n : ℕ) i, CompactRep n (h n i) (fun x => (f x i : ℂ))) (n : ℕ) :
    (smoothL2FieldOfFourier f hf h hrep).jetLp n = physicalJetLp n (h n) := by
  apply Lp.ext
  exact (smoothL2FieldOfFourier f hf h hrep).jetLp_ae n |>.trans
    (physicalJetLp_ae n hf (h n) (hrep n)).symm

/-- Continuous componentwise Fourier data for an already smooth real-vector
path yield the same actual field with every jet continuous in L2. -/
theorem exists_smoothL2Field_path {K : Type*} [TopologicalSpace K]
    (u : K → Space → Space) (hu : ∀ t, ContDiff ℝ ∞ (u t))
    (h : ∀ n : ℕ, K → Fin 3 → SobolevHilbert n)
    (hc : ∀ n i, Continuous (fun t => h n t i))
    (hrep : ∀ (n : ℕ) t i, CompactRep n (h n t i) (fun x => (u t x i : ℂ))) :
    ∃ A : K → EulerLpTranslation.SmoothL2Field Space,
      (∀ t, (A t).field = u t) ∧ ∀ n, Continuous (fun t => (A t).jetLp n) := by
  let A (t : K) := smoothL2FieldOfFourier (u t) (hu t) (fun n => h n t)
    (fun n => hrep n t)
  refine ⟨A, fun _ => rfl, ?_⟩
  intro n
  have he : (fun t => (A t).jetLp n) = fun t => physicalJetLp n (h n t) := by
    funext t
    exact smoothL2FieldOfFourier_jetLp (u t) (hu t) (fun n => h n t) (fun n => hrep n t) n
  rw [he]
  exact (physicalJetLp n).continuous.comp (continuous_pi (hc n))

end NSFormalization.Source.FourierPhysicalJets
