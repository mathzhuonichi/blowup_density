import NSFormalization.Section4.A01.ConstructorDivergenceSlice
import NSFormalization.Section4.A04.Forcing
import NSFormalization.Section4.C01.JetPaths

/-!
# A01 constructor row (v): consume a global paper force

The A01 consumer starts with a physical force `f` and `hf : D01.MemForceR f`.  Its carrier-B
input is the canonical restriction `C01.forcePath hf`; `C01.forcePath_jetLp_continuous` supplies
exactly the continuity premise used by `HasAprioriBound` and
`localTheory_on_prescribed_horizon`.  The constructor retains the original physical force
`f' := f`, its original proof `hf`, and the consequence `A04.memL1Hm_of_memForceR hf`.

For comparison on the prescribed horizon, `forceOfPath` only reads the physical field represented
by a carrier path and uses zero off `[0,S]`.  No global smoothness or `MemForceR` claim is made for
this zero extension: when the endpoint slice is nonzero, it is discontinuous at `S`.  Its sole use
here is the pointwise identity `forceOfPath (C01.forcePath hf) = f` on `[0,S]`.

The initial-datum theorem consumes the cylinder divergence handoff from lane 162.  In particular,
it takes the actual angular-invariance, ordinary-lift, divergence-free-space, and a.e.-slice
hypotheses required by `divergence_ae_of_cylinder`; it does not assume pointwise divergence as an
unexplained external premise.

Paper reference: `paper/sections/02-preliminaries.tex:17-26`.
-/

noncomputable section

namespace NSFormalization.Section4.A01

open Set MeasureTheory NavierStokes.ProblemStatement
open EulerLpTranslation EulerLpTranslation.SmoothL2Field
open EulerMeanOrdinaryLift EulerCylinderSobolevSpace EulerLiftedGradientSpace
  EulerCylinderSobolev EulerPressureSpatialRegularity
open scoped ContDiff

/-! ## 1. The consumer-facing force bridge -/

/-- Read the physical force represented by a finite-horizon carrier path, using zero only outside
the prescribed horizon.  This definition is not asserted to preserve global smoothness. -/
def forceOfPath {S : ℝ} (F : Icc (0 : ℝ) S → SmoothL2Field Space) : A02.SpaceTimeField :=
  fun z => if hz : z.1 ∈ Icc (0 : ℝ) S then (F ⟨z.1, hz⟩).field z.2 else 0

/-- On `[0,S]`, `forceOfPath` recovers the physical field of its carrier slice pointwise. -/
@[simp] theorem forceOfPath_apply {S : ℝ} (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (t : Icc (0 : ℝ) S) (x : Space) : forceOfPath F (t.1, x) = (F t).field x := by
  simp only [forceOfPath, t.2, dite_true]

/-- Restricting a global manuscript force to `[0,S]` and reading its physical slices returns the
original force pointwise on that horizon.  The physical force retained by the constructor is `f`,
not the zero extension outside the horizon. -/
theorem forceOfPath_forcePath_eq_on_horizon {S : ℝ} {f : A02.SpaceTimeField}
    (hf : D01.MemForceR f) (t : Icc (0 : ℝ) S) (x : Space) :
    forceOfPath (C01.forcePath (S := S) hf) (t.1, x) = f (t.1, x) := by
  rw [forceOfPath_apply]
  rfl

/-- **A01 constructor row (v), in the consumer direction.**

Given the paper's global force `f ∈ F_R`, this packages the canonical carrier path `F`, the
jet-continuity proof required by `HasAprioriBound` / `localTheory_on_prescribed_horizon`, and the
unchanged physical force's `L¹_t H^m_x` property.  The equation `F = C01.forcePath hf` prevents the
existential package from being witnessed by an unrelated path. -/
theorem forcePath_of_memForceR {S : ℝ} {f : A02.SpaceTimeField} (hf : D01.MemForceR f) :
    ∃ F : Icc (0 : ℝ) S → SmoothL2Field Space,
      F = C01.forcePath hf ∧
      (∀ n, Continuous fun t => (F t).jetLp n) ∧
      A04.MemL1Hm f := by
  refine ⟨C01.forcePath hf, rfl, ?_, A04.memL1Hm_of_memForceR hf⟩
  exact C01.forcePath_jetLp_continuous hf

/-! ## 2. The initial datum via lane 162's divergence handoff -/

/-- A smooth all-jet-`L²` representative of a divergence-free cylinder slice belongs to the
manuscript initial class.

The divergence input is the actual lane-162 bridge `divergence_ae_of_cylinder`: angle invariance,
ordinary descent, membership in the cylinder `divergenceFreeSpace`, and the a.e. identification of
`a.field` with the ordinary carrier.  Smoothness of `a` upgrades the resulting a.e. coordinate
divergence to the pointwise `A02.IsSolenoidal` predicate. -/
theorem initialClassR_of_smoothL2 {q : ℕ}
    (u : SobolevSpace 1 (q + 1))
    (U : EulerMeanSolenoidal.L2)
    (hu : ∀ θ : AddCircle (1 : ℝ), sobolevTranslation 1 (q + 1) (0, θ) u = u)
    (hU : ordinaryLift U = value 1 u)
    (hdiv : value 1 u ∈ divergenceFreeSpace 1 1 0)
    (a : SmoothL2Field Space)
    (ha : a.field =ᵐ[volume] ⇑U) :
    a.field ∈ A02.initialClassR := by
  refine ⟨D01.memHInfty_of_contDiff_memLp a.smooth a.integrable, ?_⟩
  have hdiv_ae := divergence_ae_of_cylinder u U hu hU hdiv a ha
  have hdiv_cont : Continuous (fun x : Space =>
      ∑ i : Fin 3, (fderiv ℝ a.field x (coordinateVector i)) i) := by
    apply continuous_finsetSum
    intro i _
    exact (EuclideanSpace.proj i).continuous.comp
      ((a.smooth.continuous_fderiv (by simp)).clm_apply continuous_const)
  have hdiv_fun : (fun x : Space =>
      ∑ i : Fin 3, (fderiv ℝ a.field x (coordinateVector i)) i) = 0 := by
    apply (hdiv_cont.ae_eq_iff_eq volume
      (continuous_const : Continuous (0 : Space → ℝ))).mp
    exact hdiv_ae
  intro x
  have hx := congrFun hdiv_fun x
  simp only [Pi.zero_apply] at hx
  simpa only [spatialDivergence, spatialDerivative, coordinateVector] using hx

end NSFormalization.Section4.A01
