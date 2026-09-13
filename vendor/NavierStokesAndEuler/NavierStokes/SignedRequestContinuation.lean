import NavierStokes.ActualCorrectionModels

/-!
# Continuation of the actual mean residual and signed request

The input consists of continued primitive velocity and pressure components.
Covariances, graph derivatives, mean residuals, and the moving signed radial
primitive are computed from those components.  Agreement always retains the
entire free radial and torus fibers, as well as the free angular variable.
-/

noncomputable section

namespace NavierStokes.SignedRequestContinuation

open Set Function Filter MeasureTheory
open scoped ContDiff Topology Interval BigOperators


abbrev Slow := TorusInverse.Plane
abbrev Point := LocalSignedRequest.Point
abbrev ScalarField := MeanIncrementBounds.Field Point

/-! ## Support of the literal differential expressions -/

def Supported (a b : ℝ) (ell : Slow → ℝ) (U : Set Slow) (f : ScalarField) : Prop :=
  ∀ n, VariableGaugeMean.SupportedGauge a b ell U (f n)

namespace Supported

variable {a b : ℝ} {ell : Slow → ℝ} {U : Set Slow} {f g : ScalarField}

theorem zero : Supported a b ell U (0 : ScalarField) :=
  fun _ _ _ hn => (hn rfl).elim

theorem add (hf : Supported a b ell U f) (hg : Supported a b ell U g) :
    Supported a b ell U (f + g) := by
  intro n x hx hn
  by_contra hnot
  have hf0 : f n x = 0 := by by_contra he; exact hnot (hf n x hx he)
  have hg0 : g n x = 0 := by by_contra he; exact hnot (hg n x hx he)
  exact hn (by simp [hf0, hg0])

theorem neg (hf : Supported a b ell U f) : Supported a b ell U (-f) :=
  fun n x hx hn => hf n x hx (neg_ne_zero.mp hn)

theorem sub (hf : Supported a b ell U f) (hg : Supported a b ell U g) :
    Supported a b ell U (f - g) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem mul_left (hf : Supported a b ell U f) (g : ScalarField) :
    Supported a b ell U (g * f) :=
  fun n x hx hn => hf n x hx (right_ne_zero_of_mul hn)

theorem mul_right (hf : Supported a b ell U f) (g : ScalarField) :
    Supported a b ell U (f * g) :=
  fun n x hx hn => hf n x hx (left_ne_zero_of_mul hn)

theorem band_mul (hf : Supported a b ell U f) (c : ℕ → ℝ) :
    Supported a b ell U (fun n x => c n * f n x) :=
  fun n x hx hn => hf n x hx (right_ne_zero_of_mul hn)

theorem smul (hf : Supported a b ell U f) (c : ℝ) :
    Supported a b ell U (c • f) := hf.band_mul (fun _ => c)

theorem directional (hf : Supported a b ell U f) (hU : IsOpen U)
    (hell : ContinuousOn ell U) (v : Point) :
    Supported a b ell U (fun n x => fderiv ℝ (f n) x v) :=
  fun n => LocalRankDefect.supportedGauge_directional hU hell (hf n) v

theorem dr (hf : Supported a b ell U f) (hU : IsOpen U)
    (hell : ContinuousOn ell U) (o : MeanIncrementBounds.Operators Point) :
    Supported a b ell U (o.dr f) :=
  (hf.directional hU hell o.eR).add
    (((hf.directional hU hell o.vR).mul_left (fun _ => o.radialProfile)).band_mul o.radialFrequency)

theorem dz (hf : Supported a b ell U f) (hU : IsOpen U)
    (hell : ContinuousOn ell U) (o : MeanIncrementBounds.Operators Point) :
    Supported a b ell U (o.dz f) := (hf.directional hU hell o.eZ).band_mul o.epsilon

theorem time (hf : Supported a b ell U f) (hU : IsOpen U)
    (hell : ContinuousOn ell U) (o : MeanIncrementBounds.Operators Point) :
    Supported a b ell U (o.time f) :=
  ((hf.directional hU hell o.eT).band_mul o.epsilon).neg.add
    ((hf.directional hU hell o.vT).band_mul o.fastCoefficient)

theorem radialDiv (hf : Supported a b ell U f) (hU : IsOpen U)
    (hell : ContinuousOn ell U) (o : MeanIncrementBounds.Operators Point) (c : ℝ) :
    Supported a b ell U (o.radialDiv c f) :=
  (hf.dr hU hell o).add ((hf.mul_left o.invRadius).smul c)

theorem viscosity (hf : Supported a b ell U f) (hU : IsOpen U)
    (hell : ContinuousOn ell U) (o : MeanIncrementBounds.Operators Point) (c : ℝ) :
    Supported a b ell U (o.viscosity c f) :=
  (((((hf.dr hU hell o).dr hU hell o).add ((hf.dr hU hell o).mul_left o.invRadius)).add
    ((hf.dz hU hell o).dz hU hell o)).sub
      (((hf.mul_left o.invRadius).mul_left o.invRadius).smul c)).band_mul o.epsilon

end Supported

structure SupportedTriple (a b : ℝ) (ell : Slow → ℝ) (U : Set Slow)
    (m : MeanIncrementBounds.Triple Point) : Prop where
  radial : Supported a b ell U m.radial
  angular : Supported a b ell U m.angular
  axial : Supported a b ell U m.axial

namespace SupportedTriple

variable {a b : ℝ} {ell : Slow → ℝ} {U : Set Slow} {m : MeanIncrementBounds.Triple Point}
  (hm : SupportedTriple a b ell U m) (base : MeanIncrementBounds.Triple Point)

include hm

theorem thetaRadial : Supported a b ell U (MeanIncrementBounds.thetaRadial base m) :=
  ((hm.angular.mul_left base.radial).add (hm.radial.mul_right base.angular)).add
    (hm.radial.mul_right m.angular)

theorem thetaAxial : Supported a b ell U (MeanIncrementBounds.thetaAxial base m) :=
  ((hm.angular.mul_left base.axial).add (hm.axial.mul_left base.angular)).add
    (hm.axial.mul_right m.angular)

theorem axialRadial : Supported a b ell U (MeanIncrementBounds.axialRadial base m) :=
  ((hm.axial.mul_left base.radial).add (hm.radial.mul_right base.axial)).add
    (hm.radial.mul_right m.axial)

theorem axialAxial : Supported a b ell U (MeanIncrementBounds.axialAxial base m) :=
  ((hm.axial.mul_left base.axial).smul 2).add (hm.axial.mul_right m.axial)

theorem radialRadial : Supported a b ell U (MeanIncrementBounds.radialRadial base m) :=
  ((hm.radial.mul_left base.radial).smul 2).add (hm.radial.mul_right m.radial)

theorem radialAngular : Supported a b ell U (MeanIncrementBounds.radialAngular base m) :=
  ((hm.angular.mul_left base.angular).smul 2).add (hm.angular.mul_right m.angular)

end SupportedTriple

theorem thetaResidual_supported {a b : ℝ} {ell : Slow → ℝ} {U : Set Slow}
    (hU : IsOpen U) (hell : ContinuousOn ell U) (o : MeanIncrementBounds.Operators Point) (base : MeanIncrementBounds.Triple Point)
    {m : MeanIncrementBounds.Triple Point} (hm : SupportedTriple a b ell U m)
    (W : Fin 3 → Fin 3 → ScalarField) (hW : ∀ i j, Supported a b ell U (W i j))
    {T : ScalarField} (hT : Supported a b ell U T) :
    Supported a b ell U (MeanIncrementBounds.thetaResidual o base m W T) :=
  ((((hm.angular.time hU hell o).add (((hm.thetaRadial base).add (hW 0 1)).radialDiv hU hell o 2)).add
    (((hm.thetaAxial base).add (hW 2 1)).dz hU hell o)).sub
      (hm.angular.viscosity hU hell o 1)).sub (hT.radialDiv hU hell o 2)

theorem axialResidual_supported {a b : ℝ} {ell : Slow → ℝ} {U : Set Slow}
    (hU : IsOpen U) (hell : ContinuousOn ell U) (o : MeanIncrementBounds.Operators Point) (base : MeanIncrementBounds.Triple Point)
    {m : MeanIncrementBounds.Triple Point} (hm : SupportedTriple a b ell U m)
    (W : Fin 3 → Fin 3 → ScalarField) (hW : ∀ i j, Supported a b ell U (W i j))
    {p T : ScalarField} (hp : Supported a b ell U p) (hT : Supported a b ell U T) :
    Supported a b ell U (MeanIncrementBounds.axialResidual o base m W p T) :=
  ((((hm.axial.time hU hell o).add (((hm.axialRadial base).add (hW 0 2)).radialDiv hU hell o 1)).add
    ((((hm.axialAxial base).add (hW 2 2)).add hp).dz hU hell o)).sub
      (hm.axial.viscosity hU hell o 0)).sub (hT.radialDiv hU hell o 1)

theorem gr_supported {a b : ℝ} {ell : Slow → ℝ} {U : Set Slow}
    (hU : IsOpen U) (hell : ContinuousOn ell U) (o : MeanIncrementBounds.Operators Point) (base : MeanIncrementBounds.Triple Point)
    {m : MeanIncrementBounds.Triple Point} (hm : SupportedTriple a b ell U m)
    (W : Fin 3 → Fin 3 → ScalarField) (hW : ∀ i j, Supported a b ell U (W i j)) :
    Supported a b ell U (MeanIncrementBounds.gr o base m W) :=
  (((((hm.radial.time hU hell o).add (((hm.radialRadial base).add (hW 0 0)).radialDiv hU hell o 1)).add
    (((hm.axialRadial base).add (hW 2 0)).dz hU hell o)).sub
      (((hm.radialAngular base).add (hW 1 1)).mul_left o.invRadius)).sub
        (hm.radial.viscosity hU hell o 1)).neg

/-! ## Smoothness with actual axis zero germs -/

theorem thetaRadial_localShell {a b : ℝ} (ha : 0 < a) {U : Set Slow} (hU : IsOpen U)
    {base m : MeanIncrementBounds.Triple Point} (hb : MeanIncrementBounds.SmoothTriple (LocalRankDefect.positiveDomain U) base)
    (hm : LocalRankDefect.LocalTriple a b U m) : LocalRankDefect.LocalShell a b U (MeanIncrementBounds.thetaRadial base m) :=
  ((hm.angular.coefficient_mul ha hU hb.radial).add
    (hm.radial.mul_coefficient ha hU hb.angular)).add (hm.radial.mul hm.angular)

theorem thetaResidual_localShell {a b : ℝ} (ha : 0 < a) {U : Set Slow} (hU : IsOpen U)
    {o : MeanIncrementBounds.Operators Point} (ho : LocalRankDefect.LocalOperators U o)
    {base m : MeanIncrementBounds.Triple Point} (hb : MeanIncrementBounds.SmoothTriple (LocalRankDefect.positiveDomain U) base)
    (hm : LocalRankDefect.LocalTriple a b U m) (W : Fin 3 → Fin 3 → ScalarField)
    (hW : ∀ i j, LocalRankDefect.LocalShell a b U (W i j))
    {T : ScalarField} (hT : LocalRankDefect.LocalShell a b U T) :
    LocalRankDefect.LocalShell a b U (MeanIncrementBounds.thetaResidual o base m W T) :=
  ((((hm.angular.time hU o).add (((thetaRadial_localShell ha hU hb hm).add
    (hW 0 1)).radialDiv ha hU ho 2)).add
      (((LocalRankDefect.thetaAxial_localShell ha hU hb hm).add (hW 2 1)).dz hU o)).sub
        (hm.angular.viscosity ha hU ho 1)).sub (hT.radialDiv ha hU ho 2)

theorem axialResidual_localShell {a b : ℝ} (ha : 0 < a) {U : Set Slow} (hU : IsOpen U)
    {o : MeanIncrementBounds.Operators Point} (ho : LocalRankDefect.LocalOperators U o)
    {base m : MeanIncrementBounds.Triple Point} (hb : MeanIncrementBounds.SmoothTriple (LocalRankDefect.positiveDomain U) base)
    (hm : LocalRankDefect.LocalTriple a b U m) (W : Fin 3 → Fin 3 → ScalarField)
    (hW : ∀ i j, LocalRankDefect.LocalShell a b U (W i j))
    {p T : ScalarField} (hp : LocalRankDefect.LocalShell a b U p) (hT : LocalRankDefect.LocalShell a b U T) :
    LocalRankDefect.LocalShell a b U (MeanIncrementBounds.axialResidual o base m W p T) :=
  ((((hm.axial.time hU o).add (((LocalRankDefect.axialRadial_localShell ha hU hb hm).add
    (hW 0 2)).radialDiv ha hU ho 1)).add
      ((((LocalRankDefect.axialAxial_localShell ha hU hb hm).add (hW 2 2)).add hp).dz hU o)).sub
        (hm.axial.viscosity ha hU ho 0)).sub (hT.radialDiv ha hU ho 1)

/-! ## Covariance is continued by its actual angular integral -/

theorem covariance_smooth {U : Set Slow} (hU : IsOpen U) (u : CorrectionState.State Point)
    (hu : ∀ n i, ContDiffOn ℝ ∞ (fun x => u.oscillation n x i)
      (PhysicalMeanDomain.slowDomain U ×ˢ univ)) (i j : Fin 3) :
    MeanIncrementBounds.SmoothOn (PhysicalMeanDomain.slowDomain U) (u.covariance i j) := by
  intro n
  exact (ParametricRephase.intervalIntegral_contDiffOn_of_joint _ _ (PhysicalMeanDomain.slowDomain_open hU)
    ((hu n i).mul (hu n j)) 0 (2 * Real.pi) (by positivity)).div_const _

theorem covariance_supported {a b : ℝ} {ell : Slow → ℝ} {U : Set Slow}
    (u : CorrectionState.State Point)
    (hu : ∀ n i θ, VariableGaugeMean.SupportedGauge a b ell U (fun x => u.oscillation n (x, θ) i))
    (i j : Fin 3) : Supported a b ell U (u.covariance i j) := by
  intro n x hx hn
  by_contra hnot
  have hz (θ : ℝ) : u.oscillation n (x, θ) i = 0 := by
    by_contra he
    exact hnot (hu n i θ x hx he)
  exact hn (by simp [CorrectionState.State.covariance, CorrectionState.bilinearCovariance, CorrectionState.angularAverage, hz])

theorem covariance_agreement {U : Set Slow} {v u : CorrectionState.State Point}
    (hu : ∀ n i θ, OffplaneCorrectionExtensions.FiberAgreement U
      (fun x => v.oscillation n (x, θ) i) (fun x => u.oscillation n (x, θ) i))
    (i j : Fin 3) (n : ℕ) : OffplaneCorrectionExtensions.FiberAgreement U (v.covariance i j n) (u.covariance i j n) := by
  intro x hx
  unfold CorrectionState.State.covariance CorrectionState.bilinearCovariance CorrectionState.angularAverage
  congr 1
  apply intervalIntegral.integral_congr
  intro θ _
  exact congrArg₂ (· * ·) (hu n i θ hx) (hu n j θ hx)

/-! ## Full-fiber equality is preserved by the residual algebra -/

def Agrees (U : Set Slow) (f g : ScalarField) : Prop :=
  ∀ n, OffplaneCorrectionExtensions.FiberAgreement U (f n) (g n)

namespace Agrees

variable {U : Set Slow} {f f' g g' : ScalarField}

theorem refl (f : ScalarField) : Agrees U f f := fun _ _ _ => rfl
theorem add (hf : Agrees U f f') (hg : Agrees U g g') : Agrees U (f + g) (f' + g') :=
  fun n _ hx => congrArg₂ (· + ·) (hf n hx) (hg n hx)
theorem sub (hf : Agrees U f f') (hg : Agrees U g g') : Agrees U (f - g) (f' - g') :=
  fun n _ hx => congrArg₂ (· - ·) (hf n hx) (hg n hx)
theorem mul (hf : Agrees U f f') (hg : Agrees U g g') : Agrees U (f * g) (f' * g') :=
  fun n _ hx => congrArg₂ (· * ·) (hf n hx) (hg n hx)
theorem neg (hf : Agrees U f f') : Agrees U (-f) (-f') :=
  fun n _ hx => congrArg Neg.neg (hf n hx)
theorem smul (hf : Agrees U f f') (c : ℝ) : Agrees U (c • f) (c • f') :=
  fun n _ hx => congrArg (c * ·) (hf n hx)
theorem dr (hf : Agrees U f f') (hU : IsOpen U) (o : MeanIncrementBounds.Operators Point) :
    Agrees U (o.dr f) (o.dr f') := ActualCorrectionModels.fiberAgreement_dr hU o hf
theorem dz (hf : Agrees U f f') (hU : IsOpen U) (o : MeanIncrementBounds.Operators Point) :
    Agrees U (o.dz f) (o.dz f') := ActualCorrectionModels.fiberAgreement_dz hU o hf
theorem time (hf : Agrees U f f') (hU : IsOpen U) (o : MeanIncrementBounds.Operators Point) :
    Agrees U (o.time f) (o.time f') := ActualCorrectionModels.fiberAgreement_time hU o hf
theorem radialDiv (hf : Agrees U f f') (hU : IsOpen U) (o : MeanIncrementBounds.Operators Point) (c : ℝ) :
    Agrees U (o.radialDiv c f) (o.radialDiv c f') :=
  (hf.dr hU o).add (((refl o.invRadius).mul hf).smul c)
theorem viscosity (hf : Agrees U f f') (hU : IsOpen U) (o : MeanIncrementBounds.Operators Point) (c : ℝ) :
    Agrees U (o.viscosity c f) (o.viscosity c f') := ActualCorrectionModels.fiberAgreement_viscosity hU o c hf

end Agrees

structure TripleAgrees (U : Set Slow) (m m' : MeanIncrementBounds.Triple Point) : Prop where
  radial : Agrees U m.radial m'.radial
  angular : Agrees U m.angular m'.angular
  axial : Agrees U m.axial m'.axial

namespace TripleAgrees

variable {U : Set Slow} {b b' m m' : MeanIncrementBounds.Triple Point}
  (hb : TripleAgrees U b b') (hm : TripleAgrees U m m')

include hb hm

theorem thetaRadial : Agrees U (MeanIncrementBounds.thetaRadial b m) (MeanIncrementBounds.thetaRadial b' m') :=
  ((hb.radial.mul hm.angular).add (hm.radial.mul hb.angular)).add (hm.radial.mul hm.angular)
theorem thetaAxial : Agrees U (MeanIncrementBounds.thetaAxial b m) (MeanIncrementBounds.thetaAxial b' m') :=
  ((hb.axial.mul hm.angular).add (hb.angular.mul hm.axial)).add (hm.axial.mul hm.angular)
theorem axialRadial : Agrees U (MeanIncrementBounds.axialRadial b m) (MeanIncrementBounds.axialRadial b' m') :=
  ((hb.radial.mul hm.axial).add (hm.radial.mul hb.axial)).add (hm.radial.mul hm.axial)
theorem axialAxial : Agrees U (MeanIncrementBounds.axialAxial b m) (MeanIncrementBounds.axialAxial b' m') :=
  ((hb.axial.mul hm.axial).smul 2).add (hm.axial.mul hm.axial)
theorem radialRadial : Agrees U (MeanIncrementBounds.radialRadial b m) (MeanIncrementBounds.radialRadial b' m') :=
  ((hb.radial.mul hm.radial).smul 2).add (hm.radial.mul hm.radial)
theorem radialAngular : Agrees U (MeanIncrementBounds.radialAngular b m) (MeanIncrementBounds.radialAngular b' m') :=
  ((hb.angular.mul hm.angular).smul 2).add (hm.angular.mul hm.angular)

end TripleAgrees

theorem thetaResidual_agrees {U : Set Slow} (hU : IsOpen U) (o : MeanIncrementBounds.Operators Point)
    {b b' m m' : MeanIncrementBounds.Triple Point} (hb : TripleAgrees U b b') (hm : TripleAgrees U m m')
    {W W' : Fin 3 → Fin 3 → ScalarField} (hW : ∀ i j, Agrees U (W i j) (W' i j))
    {T T' : ScalarField} (hT : Agrees U T T') :
    Agrees U (MeanIncrementBounds.thetaResidual o b m W T) (MeanIncrementBounds.thetaResidual o b' m' W' T') :=
  ((((hm.angular.time hU o).add (((hb.thetaRadial hm).add (hW 0 1)).radialDiv hU o 2)).add
    (((hb.thetaAxial hm).add (hW 2 1)).dz hU o)).sub
      (hm.angular.viscosity hU o 1)).sub (hT.radialDiv hU o 2)

theorem axialResidual_agrees {U : Set Slow} (hU : IsOpen U) (o : MeanIncrementBounds.Operators Point)
    {b b' m m' : MeanIncrementBounds.Triple Point} (hb : TripleAgrees U b b') (hm : TripleAgrees U m m')
    {W W' : Fin 3 → Fin 3 → ScalarField} (hW : ∀ i j, Agrees U (W i j) (W' i j))
    {p p' T T' : ScalarField} (hp : Agrees U p p') (hT : Agrees U T T') :
    Agrees U (MeanIncrementBounds.axialResidual o b m W p T) (MeanIncrementBounds.axialResidual o b' m' W' p' T') :=
  ((((hm.axial.time hU o).add (((hb.axialRadial hm).add (hW 0 2)).radialDiv hU o 1)).add
    ((((hb.axialAxial hm).add (hW 2 2)).add hp).dz hU o)).sub
      (hm.axial.viscosity hU o 0)).sub (hT.radialDiv hU o 1)

theorem gr_agrees {U : Set Slow} (hU : IsOpen U) (o : MeanIncrementBounds.Operators Point)
    {b b' m m' : MeanIncrementBounds.Triple Point} (hb : TripleAgrees U b b') (hm : TripleAgrees U m m')
    {W W' : Fin 3 → Fin 3 → ScalarField} (hW : ∀ i j, Agrees U (W i j) (W' i j)) :
    Agrees U (MeanIncrementBounds.gr o b m W) (MeanIncrementBounds.gr o b' m' W') :=
  (((((hm.radial.time hU o).add (((hb.radialRadial hm).add (hW 0 0)).radialDiv hU o 1)).add
    (((hb.axialRadial hm).add (hW 2 0)).dz hU o)).sub
      ((Agrees.refl o.invRadius).mul ((hb.radialAngular hm).add (hW 1 1)))).sub
        (hm.radial.viscosity hU o 1)).neg

/-! ## Primitive inputs and their literal state -/

/-- Only primitive fields are supplied.  No covariance, residual, or signed
request continuation is part of this structure. -/
structure Primitives {coord : ℝ} (P : SignedStressPrimitive.Patch) (W : OffplaneCorrectionExtensions.Window coord P.a P.b)
    (u : CorrectionState.State Point) where
  radial : ∀ n, OffplaneCorrectionExtensions.SupportedContinuation W (u.mean.radial n)
  angular : ∀ n, OffplaneCorrectionExtensions.SupportedContinuation W (u.mean.angular n)
  axial : ∀ n, OffplaneCorrectionExtensions.SupportedContinuation W (u.mean.axial n)
  pressure : ∀ n, OffplaneCorrectionExtensions.SupportedContinuation W (u.pressure n)
  oscillation : CorrectionState.Oscillation Point
  oscillation_smooth : ∀ n i, ContDiffOn ℝ ∞ (fun x => oscillation n x i)
    (PhysicalMeanDomain.slowDomain W.carrier ×ˢ univ)
  oscillation_supported : ∀ n i θ, VariableGaugeMean.SupportedGauge P.a P.b (OffplaneCorrectionExtensions.stableLength coord) W.carrier
    (fun x => oscillation n (x, θ) i)
  oscillation_agrees : ∀ n i θ, OffplaneCorrectionExtensions.FiberAgreement W.carrier
    (fun x => oscillation n (x, θ) i) (fun x => u.oscillation n (x, θ) i)

namespace Primitives

variable {coord : ℝ} {P : SignedStressPrimitive.Patch} {W : OffplaneCorrectionExtensions.Window coord P.a P.b}
  {u : CorrectionState.State Point} (d : Primitives P W u)

noncomputable def state : CorrectionState.State Point :=
  {u with
    mean := ⟨fun n => (d.radial n).value, fun n => (d.angular n).value, fun n => (d.axial n).value⟩
    pressure := fun n => (d.pressure n).value
    oscillation := d.oscillation }

theorem mean_localShell : LocalRankDefect.LocalTriple W.lower W.upper W.carrier d.state.mean :=
  ⟨⟨fun n => (d.radial n).smooth, fun n => W.fixed_support (d.radial n).supported⟩,
   ⟨fun n => (d.angular n).smooth, fun n => W.fixed_support (d.angular n).supported⟩,
   ⟨fun n => (d.axial n).smooth, fun n => W.fixed_support (d.axial n).supported⟩⟩

theorem mean_supported : SupportedTriple P.a P.b (OffplaneCorrectionExtensions.stableLength coord) W.carrier d.state.mean :=
  ⟨fun n => (d.radial n).supported, fun n => (d.angular n).supported, fun n => (d.axial n).supported⟩

theorem pressure_localShell : LocalRankDefect.LocalShell W.lower W.upper W.carrier d.state.pressure :=
  ⟨fun n => (d.pressure n).smooth, fun n => W.fixed_support (d.pressure n).supported⟩

theorem pressure_supported : Supported P.a P.b (OffplaneCorrectionExtensions.stableLength coord) W.carrier d.state.pressure :=
  fun n => (d.pressure n).supported

theorem covariance_localShell (i j : Fin 3) :
    LocalRankDefect.LocalShell W.lower W.upper W.carrier (d.state.covariance i j) :=
  ⟨covariance_smooth W.isOpen d.state d.oscillation_smooth i j,
    fun n => W.fixed_support (covariance_supported d.state d.oscillation_supported i j n)⟩

theorem covariance_supported (i j : Fin 3) :
    Supported P.a P.b (OffplaneCorrectionExtensions.stableLength coord) W.carrier (d.state.covariance i j) :=
  SignedRequestContinuation.covariance_supported d.state d.oscillation_supported i j

theorem mean_agrees : TripleAgrees W.carrier d.state.mean u.mean :=
  ⟨fun n => (d.radial n).agrees, fun n => (d.angular n).agrees, fun n => (d.axial n).agrees⟩

theorem pressure_agrees : Agrees W.carrier d.state.pressure u.pressure :=
  fun n => (d.pressure n).agrees

theorem covariance_agrees (i j : Fin 3) : Agrees W.carrier (d.state.covariance i j) (u.covariance i j) :=
  covariance_agreement d.oscillation_agrees i j

end Primitives

/-! ## The moving signed primitive at any positive smooth scale -/

noncomputable def profileMap (q : Slow → ℝ) (x : Point) : Point :=
  (x.1 / Real.sqrt (q x.2.1), x.2)

noncomputable def inverseProfileMap (q : Slow → ℝ) (x : Point) : Point :=
  (Real.sqrt (q x.2.1) * x.1, x.2)

theorem profileMap_smooth {U : Set Slow} {q : Slow → ℝ}
    (hq : ContDiffOn ℝ ∞ q U) (hp : ∀ s ∈ U, 0 < q s) :
    ContDiffOn ℝ ∞ (profileMap q) (PhysicalMeanDomain.slowDomain U) :=
  (contDiffOn_fst.div ((hq.comp contDiffOn_snd.fst (fun _ hx => hx)).sqrt
    (fun _ hx => (hp _ hx).ne')) (fun _ hx => (Real.sqrt_pos.mpr (hp _ hx)).ne')).prodMk contDiffOn_snd

theorem inverseProfileMap_smooth {U : Set Slow} {q : Slow → ℝ}
    (hq : ContDiffOn ℝ ∞ q U) (hp : ∀ s ∈ U, 0 < q s) :
    ContDiffOn ℝ ∞ (inverseProfileMap q) (PhysicalMeanDomain.slowDomain U) :=
  (((hq.comp contDiffOn_snd.fst (fun _ hx => hx)).sqrt (fun _ hx => (hp _ hx).ne')).mul
    contDiffOn_fst).prodMk contDiffOn_snd

theorem inverseProfileMap_supported (P : SignedStressPrimitive.Patch) {U : Set Slow} {q : Slow → ℝ}
    (hp : ∀ s ∈ U, 0 < q s) {f : Point → ℝ}
    (hs : VariableGaugeMean.SupportedGauge P.a P.b (SignedStressPrimitive.lengthScale q) U f) :
    PhysicalMeanDomain.SupportedOn P.a P.b U (fun x => f (inverseProfileMap q x)) := by
  intro x hx hn
  have h := hs (inverseProfileMap q x) hx hn
  have he : 0 < Real.sqrt (q x.2.1) := Real.sqrt_pos.mpr (hp _ hx)
  exact ⟨(mul_le_mul_iff_right₀ he).mp h.1, (mul_le_mul_iff_right₀ he).mp h.2⟩

theorem physicalBarSigma_profile (P : SignedStressPrimitive.Patch) (e : ℕ) (q : Slow → ℝ) (f : Point → ℝ) (x : Point) :
    SignedStressPrimitive.physicalBarSigma P e q f (x.1, x.2.1) =
      Real.sqrt (q x.2.1) * SignedStressPrimitive.barSigma P e (fun y => f (inverseProfileMap q y))
        ((profileMap q x).1, x.2.1) := rfl

theorem physicalBarSigma_smooth (P : SignedStressPrimitive.Patch) (e : ℕ) {U : Set Slow} (hU : IsOpen U)
    {q : Slow → ℝ} (hq : ContDiffOn ℝ ∞ q U) (hp : ∀ s ∈ U, 0 < q s)
    {f : Point → ℝ} (hf : ContDiffOn ℝ ∞ f (PhysicalMeanDomain.slowDomain U))
    (hs : VariableGaugeMean.SupportedGauge P.a P.b (SignedStressPrimitive.lengthScale q) U f) :
    ContDiffOn ℝ ∞ (fun x : Point => SignedStressPrimitive.physicalBarSigma P e q f (x.1, x.2.1))
      (PhysicalMeanDomain.slowDomain U) := by
  have hg := hf.comp (inverseProfileMap_smooth hq hp) (fun _ hx => hx)
  have hgs := inverseProfileMap_supported P hp hs
  have hb := LocalSignedRequest.sigma_contDiffOn P e hU
    (PhysicalMeanDomain.liftedTorusAverage_contDiffOn hU hg)
    (PhysicalMeanDomain.liftedTorusAverage_supportedOn hU hg hgs)
  have hell : ContDiffOn ℝ ∞ (fun x : Point => Real.sqrt (q x.2.1))
      (PhysicalMeanDomain.slowDomain U) :=
    (hq.comp contDiffOn_snd.fst (fun _ hx => hx)).sqrt (fun _ hx => (hp _ hx).ne')
  have h := hell.mul (hb.comp (profileMap_smooth hq hp) (fun _ hx => hx))
  simp only [Function.comp_def, SignedWaveUpdate.sigma_liftedTorusAverage] at h
  exact h

/-- Freezing is used only to apply the exact one-fiber integral theorem;
the smooth continuation above retains the full slow dependence. -/
noncomputable def frozenAverage (f : Point → ℝ) (s : Slow) (x : ℝ × ℝ) : ℝ :=
  PressureStream.torusAverage f (x.1, s)

theorem frozenAverage_smooth {U : Set Slow} (hU : IsOpen U) {s : Slow} (hs : s ∈ U)
    {f : Point → ℝ} (hf : ContDiffOn ℝ ∞ f (PhysicalMeanDomain.slowDomain U)) :
    ContDiff ℝ ∞ (frozenAverage f s) := by
  have hb := PhysicalMeanDomain.liftedTorusAverage_contDiffOn hU hf
  rw [contDiff_iff_contDiffAt]
  intro x
  change ContDiffAt ℝ ∞ (fun z : ℝ × ℝ =>
    MeanMomentBounds.liftedTorusAverage f (z.1, (s, (0 : Slow)))) x
  exact (hb.contDiffAt ((PhysicalMeanDomain.slowDomain_open hU).mem_nhds hs)).comp x
    (contDiffAt_fst.prodMk (contDiffAt_const.prodMk contDiffAt_const))

theorem frozenAverage_supported (P : SignedStressPrimitive.Patch) {U : Set Slow} {q : Slow → ℝ}
    (hp : ∀ s ∈ U, 0 < q s) {s : Slow} (hs : s ∈ U) {f : Point → ℝ}
    (hfs : VariableGaugeMean.SupportedGauge P.a P.b (SignedStressPrimitive.lengthScale q) U f) :
    SignedStressPrimitive.PhysicalSupport P (fun _ : ℝ => q s) (frozenAverage f s) := by
  intro x hx
  by_contra hn
  apply hx
  apply PressureStream.torusAverage_zero_of_forall
  intro Y
  by_contra hY
  have hh := hfs (x.1, (s, Y)) hs hY
  have hpos : 0 < SignedStressPrimitive.lengthScale q s := Real.sqrt_pos.mpr (hp _ hs)
  apply hn
  exact ⟨(le_div_iff₀ hpos).mpr (by simpa only [mul_comm] using hh.1),
    (div_le_iff₀ hpos).mpr (by simpa only [mul_comm] using hh.2)⟩

theorem physicalBarSigma_frozen (P : SignedStressPrimitive.Patch) (e : ℕ) (q : Slow → ℝ)
    (f : Point → ℝ) (s : Slow) (r : ℝ) :
    SignedStressPrimitive.physicalBarSigma P e q f (r, s) =
      SignedStressPrimitive.physicalSigma P e (fun _ : ℝ => q s) (frozenAverage f s) (r, 0) :=
  LocalSignedRequest.physicalSigma_fiber_congr (S := Slow) (T := ℝ) P e
    (q := q) (q' := fun _ : ℝ => q s) (f := PressureStream.torusAverage f)
    (g := frozenAverage f s) (s := s) (t := 0) rfl (fun _ => rfl) r

theorem physicalBarSigma_supported (P : SignedStressPrimitive.Patch) (e : ℕ) {U : Set Slow} (hU : IsOpen U)
    {q : Slow → ℝ} (hp : ∀ s ∈ U, 0 < q s)
    {f : Point → ℝ} (hf : ContDiffOn ℝ ∞ f (PhysicalMeanDomain.slowDomain U))
    (hs : VariableGaugeMean.SupportedGauge P.a P.b (SignedStressPrimitive.lengthScale q) U f) :
    VariableGaugeMean.SupportedGauge P.a P.b (SignedStressPrimitive.lengthScale q) U
      (fun x : Point => SignedStressPrimitive.physicalBarSigma P e q f (x.1, x.2.1)) := by
  intro x hx hn
  change SignedStressPrimitive.physicalBarSigma P e q f (x.1, x.2.1) ≠ 0 at hn
  rw [physicalBarSigma_frozen] at hn
  have h := SignedStressPrimitive.physicalSigma_supported P e contDiff_const (fun _ => hp _ hx)
    (frozenAverage_smooth hU hx hf) (frozenAverage_supported P hp hx hs) (x.1, 0) hn
  have he : 0 < SignedStressPrimitive.lengthScale q x.2.1 := Real.sqrt_pos.mpr (hp _ hx)
  exact ⟨by simpa only [mul_comm] using (le_div_iff₀ he).mp h.1,
    by simpa only [mul_comm] using (div_le_iff₀ he).mp h.2⟩

theorem physicalBarSigma_integral (P : SignedStressPrimitive.Patch) (e : ℕ) {U : Set Slow} (hU : IsOpen U)
    {q : Slow → ℝ} (hp : ∀ s ∈ U, 0 < q s)
    {f : Point → ℝ} (hf : ContDiffOn ℝ ∞ f (PhysicalMeanDomain.slowDomain U))
    (hs : VariableGaugeMean.SupportedGauge P.a P.b (SignedStressPrimitive.lengthScale q) U f) {s : Slow} (hsp : s ∈ U) (r : ℝ) :
    SignedStressPrimitive.physicalBarSigma P e q f (r, s) = -(∫ t in (0 : ℝ)..r,
      t ^ e * SignedStressPrimitive.physicalAdjusted P e q (PressureStream.torusAverage f) (t, s)) / r ^ e := by
  rw [physicalBarSigma_frozen]
  exact SignedStressPrimitive.physicalSigma_eq_negative_primitive P e contDiff_const (fun _ => hp _ hsp)
    (frozenAverage_smooth hU hsp hf) (frozenAverage_supported P hp hsp hs) (r, 0)

theorem physicalBarSigma_agrees (P : SignedStressPrimitive.Patch) (e : ℕ) {U : Set Slow}
    {q q' : Slow → ℝ} (hq : EqOn q q' (U ∩ OffplaneCorrectionExtensions.positiveSlow))
    {f g : Point → ℝ} (he : OffplaneCorrectionExtensions.FiberAgreement U f g) :
    OffplaneCorrectionExtensions.FiberAgreement U
      (fun x : Point => SignedStressPrimitive.physicalBarSigma P e q f (x.1, x.2.1))
      (fun x : Point => SignedStressPrimitive.physicalBarSigma P e q' g (x.1, x.2.1)) := by
  intro x hx
  apply LocalSignedRequest.physicalSigma_fiber_congr P e (hq hx)
  intro r
  exact PressureStream.torusAverage_congr_slice (r, x.2.1) (fun Y => he hx)

/-- Continuation of the exact signed primitive, including both averages
and its moving radial scaling. -/
noncomputable def signedPrimitive {coord : ℝ} (hc : 0 < coord) (hc1 : coord < 1)
    {P : SignedStressPrimitive.Patch} {W : OffplaneCorrectionExtensions.Window coord P.a P.b} {f : Point → ℝ}
    (d : OffplaneCorrectionExtensions.SupportedContinuation W f) (e : ℕ) :
    OffplaneCorrectionExtensions.SupportedContinuation W (fun x : Point => SignedStressPrimitive.physicalBarSigma P e
      (SimilarityCoordinates.coordinateQ coord) f (x.1, x.2.1)) where
  value x := SignedStressPrimitive.physicalBarSigma P e (OffplaneCorrectionExtensions.stableQ coord) d.value (x.1, x.2.1)
  smooth := physicalBarSigma_smooth P e W.isOpen
    (fun _ hx => (OffplaneCorrectionExtensions.stableQ_contDiffAt hc hc1 (W.stable hx)).contDiffWithinAt)
    (fun _ hx => OffplaneCorrectionExtensions.stableQ_pos (W.stable hx)) d.smooth d.supported
  supported := physicalBarSigma_supported P e W.isOpen
    (fun _ hx => OffplaneCorrectionExtensions.stableQ_pos (W.stable hx)) d.smooth d.supported
  agrees := physicalBarSigma_agrees P e
    (fun _ hx => OffplaneCorrectionExtensions.stableQ_eq_coordinateQ hc hc1 hx.2) d.agrees

/-! ## Instantiation with the same constructed slow base -/

section ActualContext

variable {F : OutgoingProfile.Profile} {W₀ : NominalProfile.Witness F}
  (H : NominalConeAssembly.Certificate W₀) {ld : ModulatedProfileAssembly.LoopData W₀}
  (v : ModulatedProfileAssembly.Witness ld) (upper : ℝ) (B : ℕ) (index : ℕ → ℕ)
  {P : SignedStressPrimitive.Patch} (W : OffplaneCorrectionExtensions.Window (2 * F.data.h) P.a P.b)

theorem actual_base_smooth : MeanIncrementBounds.SmoothTriple (LocalRankDefect.positiveDomain W.carrier)
    (ActualCorrectionModels.context H v upper B index).base := by
  have hsub : LocalRankDefect.positiveDomain W.carrier ⊆ ActualCorrectionModels.contextDomain F.data.h :=
    fun _ hx => ⟨W.stable hx.2, hx.1⟩
  have hb := ActualCorrectionModels.context_base_smooth H v upper B index
  exact ⟨fun n => (hb.radial n).mono hsub, fun n => (hb.angular n).mono hsub,
    fun n => (hb.axial n).mono hsub⟩

theorem actual_operators_local : LocalRankDefect.LocalOperators W.carrier (ActualCorrectionModels.context H v upper B index).operators :=
  CommonBaseContext.context_operators_local H v upper B W.carrier index

theorem actual_stress_smooth (n : ℕ) :
    ContDiffOn ℝ ∞ ((ActualCorrectionModels.context H v upper B index).virtualTheta n) (PhysicalMeanDomain.slowDomain W.carrier) ∧
    ContDiffOn ℝ ∞ ((ActualCorrectionModels.context H v upper B index).virtualAxial n) (PhysicalMeanDomain.slowDomain W.carrier) := by
  constructor <;> intro x hx
  · exact (((ActualCorrectionModels.virtualStress_smoothAt H v upper B n
      (p := BaseContextAssembly.slowCoordinates x) (W.stable hx)).comp x
      BaseContextAssembly.slowCoordinates.contDiff.contDiffAt).fst).contDiffWithinAt
  · exact (((ActualCorrectionModels.virtualStress_smoothAt H v upper B n
      (p := BaseContextAssembly.slowCoordinates x) (W.stable hx)).comp x
      BaseContextAssembly.slowCoordinates.contDiff.contDiffAt).snd).contDiffWithinAt

theorem actual_base_agrees : TripleAgrees W.carrier (ActualCorrectionModels.context H v upper B index).base
    (CommonBaseContext.context H v upper B index).base :=
  ⟨fun n => (ActualCorrectionModels.context_base_fiberAgreement H v upper B index n W.carrier).1,
   fun n => (ActualCorrectionModels.context_base_fiberAgreement H v upper B index n W.carrier).2.1,
   fun n => (ActualCorrectionModels.context_base_fiberAgreement H v upper B index n W.carrier).2.2⟩

variable {u : CorrectionState.State Point} (d : Primitives P W u)

/-- The continued radial source is computed before pressure reconstruction. -/
noncomputable def radialSource (n : ℕ) :
    OffplaneCorrectionExtensions.SupportedContinuation W (u.gr (CommonBaseContext.context H v upper B index) n) where
  value := d.state.gr (ActualCorrectionModels.context H v upper B index) n
  smooth := (LocalRankDefect.gr_localShell W.lower_pos W.isOpen
    (actual_base_smooth H v upper B index W) d.mean_localShell
    (actual_operators_local H v upper B index W) d.state.covariance d.covariance_localShell).smooth n
  supported := gr_supported W.isOpen
    (W.length_smooth (by linarith [F.data.h_pos]) (by linarith [F.data.h_lt_half])).continuousOn
    (ActualCorrectionModels.context H v upper B index).operators (ActualCorrectionModels.context H v upper B index).base
    d.mean_supported d.state.covariance d.covariance_supported n
  agrees := gr_agrees W.isOpen (ActualCorrectionModels.context H v upper B index).operators
    (actual_base_agrees H v upper B index W) d.mean_agrees d.covariance_agrees n

/-- This is primitive support geometry for the continued virtual tensor.
It does not assume any residual or request bound or continuation. -/
structure ContextSupport : Prop where
  theta : Supported P.a P.b (OffplaneCorrectionExtensions.stableLength (2 * F.data.h)) W.carrier
    (ActualCorrectionModels.context H v upper B index).virtualTheta
  axial : Supported P.a P.b (OffplaneCorrectionExtensions.stableLength (2 * F.data.h)) W.carrier
    (ActualCorrectionModels.context H v upper B index).virtualAxial

variable (hT : ContextSupport H v upper B index W)

noncomputable def thetaSource (n : ℕ) :
    OffplaneCorrectionExtensions.SupportedContinuation W (u.thetaResidual (CommonBaseContext.context H v upper B index) n) where
  value := d.state.thetaResidual (ActualCorrectionModels.context H v upper B index) n
  smooth := (thetaResidual_localShell W.lower_pos W.isOpen
    (actual_operators_local H v upper B index W) (actual_base_smooth H v upper B index W)
    d.mean_localShell d.state.covariance d.covariance_localShell
    ⟨fun k => (actual_stress_smooth H v upper B index W k).1,
      fun k => W.fixed_support (hT.theta k)⟩).smooth n
  supported := thetaResidual_supported W.isOpen
    (W.length_smooth (by linarith [F.data.h_pos]) (by linarith [F.data.h_lt_half])).continuousOn
    (ActualCorrectionModels.context H v upper B index).operators (ActualCorrectionModels.context H v upper B index).base
    d.mean_supported d.state.covariance d.covariance_supported hT.theta n
  agrees := thetaResidual_agrees W.isOpen (ActualCorrectionModels.context H v upper B index).operators
    (actual_base_agrees H v upper B index W) d.mean_agrees d.covariance_agrees
    (fun k => (ActualCorrectionModels.context_stress_fiberAgreement H v upper B index k W.carrier).1) n

noncomputable def axialSource (n : ℕ) :
    OffplaneCorrectionExtensions.SupportedContinuation W (u.axialResidual (CommonBaseContext.context H v upper B index) n) where
  value := d.state.axialResidual (ActualCorrectionModels.context H v upper B index) n
  smooth := (axialResidual_localShell W.lower_pos W.isOpen
    (actual_operators_local H v upper B index W) (actual_base_smooth H v upper B index W)
    d.mean_localShell d.state.covariance d.covariance_localShell d.pressure_localShell
    ⟨fun k => (actual_stress_smooth H v upper B index W k).2,
      fun k => W.fixed_support (hT.axial k)⟩).smooth n
  supported := axialResidual_supported W.isOpen
    (W.length_smooth (by linarith [F.data.h_pos]) (by linarith [F.data.h_lt_half])).continuousOn
    (ActualCorrectionModels.context H v upper B index).operators (ActualCorrectionModels.context H v upper B index).base
    d.mean_supported d.state.covariance d.covariance_supported d.pressure_supported hT.axial n
  agrees := axialResidual_agrees W.isOpen (ActualCorrectionModels.context H v upper B index).operators
    (actual_base_agrees H v upper B index W) d.mean_agrees d.covariance_agrees d.pressure_agrees
    (fun k => (ActualCorrectionModels.context_stress_fiberAgreement H v upper B index k W.carrier).2) n

/-- The moving pressure reconstruction applied to the derived radial
source.  No pressure-output continuation is assumed here. -/
noncomputable def pressureFromRadial (n : ℕ) {exponent : ℝ} (he : 0 < exponent)
    (M : ℝ) (vr : Slow) :
    OffplaneCorrectionExtensions.SupportedContinuation W
      (VariableGaugeMean.meanPressure exponent P.a P.b M P.a_lt_b (VariableGaugeMean.qLength (2 * F.data.h)) vr
        (u.gr (CommonBaseContext.context H v upper B index) n)) :=
  (radialSource H v upper B index W d n).pressure (by linarith [F.data.h_pos])
    (by linarith [F.data.h_lt_half]) P.a_pos P.a_lt_b he M vr

/-- The actual pressure reconstruction preserves primitive continuation
data, with no assumption on its output. -/
noncomputable def reconstructPrimitives (g : VariableGaugeMean.GaugeData Slow)
    (ha : g.radial.inner = P.a) (hb : g.radial.outer = P.b)
    (hell : ∀ n, g.length n = VariableGaugeMean.qLength (2 * F.data.h)) (he : 0 < g.radial.exponent) :
    Primitives P W (VariableGaugeMean.reconstructState g (CommonBaseContext.context H v upper B index) u) where
  radial := d.radial
  angular := d.angular
  axial := d.axial
  pressure := fun n => by
    let p := pressureFromRadial H v upper B index W d n he
      (g.radial.frequency n) g.radial.radialDirection
    refine ⟨p.value, p.smooth, p.supported, ?_⟩
    intro x hx
    have h := p.agrees hx
    change p.value x = VariableGaugeMean.meanPressure g.radial.exponent g.radial.inner
      g.radial.outer (g.radial.frequency n) g.radial.inner_lt_outer (g.length n)
      g.radial.radialDirection (u.gr (CommonBaseContext.context H v upper B index) n) x
    simpa only [ha, hb, hell] using h
  oscillation := d.oscillation
  oscillation_smooth := d.oscillation_smooth
  oscillation_supported := d.oscillation_supported
  oscillation_agrees := d.oscillation_agrees

/-- The continued reconstructed pressure is the same integral recipe at
the stable positive scale, applied to the derived continued radial source. -/
theorem reconstructPrimitives_pressure (g : VariableGaugeMean.GaugeData Slow)
    (ha : g.radial.inner = P.a) (hb : g.radial.outer = P.b)
    (hell : ∀ n, g.length n = VariableGaugeMean.qLength (2 * F.data.h)) (he : 0 < g.radial.exponent)
    (n : ℕ) (x : Point) :
    (reconstructPrimitives H v upper B index W d g ha hb hell he).state.pressure n x =
      VariableGaugeMean.meanPressure g.radial.exponent P.a P.b (g.radial.frequency n) P.a_lt_b
        (OffplaneCorrectionExtensions.stableLength (2 * F.data.h)) g.radial.radialDirection
        (d.state.gr (ActualCorrectionModels.context H v upper B index) n) x := rfl

/-- The literal normalized request: the same two derived residuals, the same patch,
the actual moving signed primitive, and the original epsilon factor. -/
noncomputable def fullRequest (s : WeightedClasses.StripData Point) :
    ℕ → Point × ℝ → SignedWaveUpdate.Vec2 :=
  fun n x => (s.epsilon n)⁻¹ •
    ![SignedStressPrimitive.physicalBarSigma P 2 (OffplaneCorrectionExtensions.stableQ (2 * F.data.h))
        (d.state.thetaResidual (ActualCorrectionModels.context H v upper B index) n) (x.1.1, x.1.2.1),
      SignedStressPrimitive.physicalBarSigma P 1 (OffplaneCorrectionExtensions.stableQ (2 * F.data.h))
        (d.state.axialResidual (ActualCorrectionModels.context H v upper B index) n) (x.1.1, x.1.2.1)]

include hT in
theorem fullRequest_smooth (s : WeightedClasses.StripData Point) (n : ℕ) :
    ContDiffOn ℝ ∞ (fullRequest H v upper B index W d s n)
      (PhysicalMeanDomain.slowDomain W.carrier ×ˢ univ) := by
  let θ := signedPrimitive (by linarith [F.data.h_pos]) (by linarith [F.data.h_lt_half])
    (thetaSource H v upper B index W d hT n) 2
  let z := signedPrimitive (by linarith [F.data.h_pos]) (by linarith [F.data.h_lt_half])
    (axialSource H v upper B index W d hT n) 1
  have hθ : ContDiffOn ℝ ∞ (fun x : Point × ℝ => θ.value x.1)
      (PhysicalMeanDomain.slowDomain W.carrier ×ˢ univ) :=
    θ.smooth.comp contDiffOn_fst (fun _ hx => hx.1)
  have hz : ContDiffOn ℝ ∞ (fun x : Point × ℝ => z.value x.1)
      (PhysicalMeanDomain.slowDomain W.carrier ×ˢ univ) :=
    z.smooth.comp contDiffOn_fst (fun _ hx => hx.1)
  apply contDiffOn_pi.mpr
  intro i
  fin_cases i
  · exact contDiffOn_const.mul hθ
  · exact contDiffOn_const.mul hz

include hT in
theorem fullRequest_supported (s : WeightedClasses.StripData Point) (n : ℕ) (i : Fin 2) (θ : ℝ) :
    VariableGaugeMean.SupportedGauge P.a P.b (OffplaneCorrectionExtensions.stableLength (2 * F.data.h)) W.carrier
      (fun x => fullRequest H v upper B index W d s n (x, θ) i) := by
  let th := signedPrimitive (by linarith [F.data.h_pos]) (by linarith [F.data.h_lt_half])
    (thetaSource H v upper B index W d hT n) 2
  let z := signedPrimitive (by linarith [F.data.h_pos]) (by linarith [F.data.h_lt_half])
    (axialSource H v upper B index W d hT n) 1
  intro x hx hn
  fin_cases i
  · exact th.supported x hx (right_ne_zero_of_mul hn)
  · exact z.supported x hx (right_ne_zero_of_mul hn)

include hT in
theorem fullRequest_agrees (s : WeightedClasses.StripData Point) (n : ℕ) (θ : ℝ) :
    OffplaneCorrectionExtensions.FiberAgreement W.carrier
      (fun x => fullRequest H v upper B index W d s n (x, θ))
      (fun x => LocalSignedRequest.fullRequest s P (2 * F.data.h)
        (CommonBaseContext.context H v upper B index) u n (x, θ)) := by
  let th := signedPrimitive (by linarith [F.data.h_pos]) (by linarith [F.data.h_lt_half])
    (thetaSource H v upper B index W d hT n) 2
  let z := signedPrimitive (by linarith [F.data.h_pos]) (by linarith [F.data.h_lt_half])
    (axialSource H v upper B index W d hT n) 1
  intro x hx
  funext i
  fin_cases i
  · exact congrArg ((s.epsilon n)⁻¹ * ·) (th.agrees hx)
  · exact congrArg ((s.epsilon n)⁻¹ * ·) (z.agrees hx)

noncomputable def fullRequestComponent (s : WeightedClasses.StripData Point) (n : ℕ) (i : Fin 2) (θ : ℝ) :
    OffplaneCorrectionExtensions.SupportedContinuation W (fun x => LocalSignedRequest.fullRequest s P (2 * F.data.h)
      (CommonBaseContext.context H v upper B index) u n (x, θ) i) where
  value x := fullRequest H v upper B index W d s n (x, θ) i
  smooth := (contDiffOn_pi.mp ((fullRequest_smooth H v upper B index W d hT s n).comp
    (contDiffOn_id.prodMk contDiffOn_const) (fun _ hx => ⟨hx, mem_univ _⟩))) i
  supported := fullRequest_supported H v upper B index W d hT s n i θ
  agrees := fun _ hx => congrFun (fullRequest_agrees H v upper B index W d hT s n θ hx) i

theorem fullRequest_free_variables (s : WeightedClasses.StripData Point) (n : ℕ)
    (r : ℝ) (p Y Y' : Slow) (θ θ' : ℝ) :
    fullRequest H v upper B index W d s n ((r, (p, Y)), θ) =
      fullRequest H v upper B index W d s n ((r, (p, Y')), θ') := rfl

end ActualContext

/-! The agreement is a neighborhood equality at positive time, so every
fixed ambient derivative tensor is also the tensor of the original field. -/
theorem continuation_jets {coord a b : ℝ} {W : OffplaneCorrectionExtensions.Window coord a b}
    {f : Point → ℝ} (d : OffplaneCorrectionExtensions.SupportedContinuation W f) {x : Point}
    (hx : x.2.1 ∈ W.carrier) (ht : 0 < x.2.1.1) (m : ℕ) :
    iteratedFDeriv ℝ m d.value x = iteratedFDeriv ℝ m f x := by
  have he := d.agrees.eventuallyEq W.isOpen hx ht
  have hw : d.value =ᶠ[𝓝[univ] x] f := by simpa only [nhdsWithin_univ] using he
  simpa only [iteratedFDerivWithin_univ] using hw.iteratedFDerivWithin_eq he.self_of_nhds m

end NavierStokes.SignedRequestContinuation
