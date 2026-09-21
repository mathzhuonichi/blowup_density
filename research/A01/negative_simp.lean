import NSFormalization.Section4.A01.ConvectionDivergence
import NSFormalization.Section4.A01.RadialPotential
import NSFormalization.Section4.A01.PressureGauge
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# A01 load-bearing checks (lane 113 SIMP/tester, revised after REVIEW_SIMP.md)

**This file must compile SILENTLY** (exit 0, no errors, no warnings).  It holds the
*genuine* load-bearing evidence for the A01 exports, in the form the lane-113
reviewer required (`research/A01/REVIEW_SIMP.md` §6): counterexamples that *refute*
the hypothesis-free statement, and one *derivation* showing a hypothesis is in fact
redundant.  The companion file `research/A01/negative_simp_fail.lean` holds the
weaker "signature checks" (which must FAIL); see its header and F4 of the review.

Contents (reviewer's §6 probes, transcribed here so the evidence survives the
volatile `/tmp/rev113`; deprecation-only edits applied to keep the file warning-free,
mathematics unchanged):

* §6.1 `Rev113.ConvDiv.hdiv_load_bearing` — `hdiv` in `navierStokesResidual_eq_iff_projected`
  is load-bearing: the hypothesis-free version is FALSE (`u(t,y) = y₀ e₀`).
* §6.2 `Rev113.Radial.{G_not_symm, pot_eq, hG_load_bearing}` — `hG` in
  `hasFDerivAt_radialPotential` is load-bearing: counterexample `G(y) = y₁ e₀`.
* §6.3 `Rev113.Gauge.{hsym_redundant, pressure_potential_of_pointwise_without_hsym}` —
  `hsym` in `pressure_potential_of_pointwise` is NOT load-bearing (F1): it follows
  from `hsm` + `hdp`.  (Frozen statement stays; this is a V2 note.)
* §6.5 `Rev113.Fidelity.*` — each reviewer probe's premise `H` is EXACTLY the real
  theorem minus one hypothesis (derived from the real theorem + that hypothesis).
-/

noncomputable section

/-! ## §6.1 — `hdiv` is load-bearing (refutation) -/
namespace Rev113.ConvDiv

open Set
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A01

/-- `u(t,y) = y₀ e₀`: linear (so spatially differentiable), divergence `1`, nonzero at `e₀`. -/
def Lin : Space →L[ℝ] Space := (EuclideanSpace.proj (0 : Fin 3)).smulRight (coordinateVector 0)

def U : VelocityField := fun z => Lin z.2

theorem U_slice (t : ℝ) : (fun y : Space => U (t, y)) = ⇑Lin := rfl

theorem spatialDerivative_U (t : ℝ) (x : Space) : spatialDerivative U t x = Lin := by
  rw [spatialDerivative, U_slice, Lin.fderiv]

theorem div_U (t : ℝ) (x : Space) : spatialDivergence U t x = 1 := by
  rw [spatialDivergence]
  simp [spatialDerivative_U, Lin, coordinateVector, Fin.sum_univ_three,
    PiLp.single_apply]

theorem U_ne (t : ℝ) : U (t, coordinateVector 0) ≠ 0 := by
  intro h
  have h0 : (U (t, coordinateVector (0 : Fin 3))) 0 = (0 : Space) 0 := by rw [h]
  simp [U, Lin, coordinateVector] at h0

set_option autoImplicit false in
/-- **`hdiv` is load-bearing**: without it the statement is FALSE. -/
theorem hdiv_load_bearing
    (H : ∀ (ν : ℝ) (u : VelocityField) (p : PressureField) (t : ℝ) (x : Space) (F : Space),
        DifferentiableAt ℝ (fun y : Space => u (t, y)) x →
        (NavierStokesR3.ProblemStatement.navierStokesResidual ν u p t x = F
          ↔ temporalDerivative u t x - ν • spatialLaplacian u t x
              = (F - convectionDivergence u t x) - pressureGradient p t x)) :
    False := by
  have hdiff : DifferentiableAt ℝ (fun y : Space => U (0, y)) (coordinateVector 0) := by
    rw [U_slice]; exact Lin.differentiableAt
  have key := (H 0 U (fun _ => 0) 0 (coordinateVector 0)
      (NavierStokesR3.ProblemStatement.navierStokesResidual 0 U (fun _ => 0) 0
        (coordinateVector 0)) hdiff).mp rfl
  have hres : NavierStokesR3.ProblemStatement.navierStokesResidual 0 U (fun _ => 0) 0
      (coordinateVector 0)
      = temporalDerivative U 0 (coordinateVector 0) + advection U 0 (coordinateVector 0)
        - (0 : ℝ) • spatialLaplacian U 0 (coordinateVector 0)
        + pressureGradient (fun _ => 0) 0 (coordinateVector 0) := rfl
  rw [hres, convectionDivergence_eq_advection_add_smul_div U 0 (coordinateVector 0) hdiff] at key
  have h3 := sub_eq_zero_of_eq key
  have h4 : spatialDivergence U 0 (coordinateVector 0) • U (0, coordinateVector 0)
      = (temporalDerivative U 0 (coordinateVector 0)
          - (0 : ℝ) • spatialLaplacian U 0 (coordinateVector 0))
        - (((temporalDerivative U 0 (coordinateVector 0) + advection U 0 (coordinateVector 0)
              - (0 : ℝ) • spatialLaplacian U 0 (coordinateVector 0)
              + pressureGradient (fun _ => 0) 0 (coordinateVector 0))
            - (advection U 0 (coordinateVector 0)
              + spatialDivergence U 0 (coordinateVector 0) • U (0, coordinateVector 0)))
          - pressureGradient (fun _ => 0) 0 (coordinateVector 0)) := by abel
  have h5 : spatialDivergence U 0 (coordinateVector 0) • U (0, coordinateVector 0) = 0 := by
    rw [h4]; exact h3
  rw [div_U, one_smul] at h5
  exact U_ne 0 h5

end Rev113.ConvDiv

/-! ## §6.2 — `hG` is load-bearing (counterexample) -/
namespace Rev113.Radial

open NavierStokes.ProblemStatement
open NSFormalization.Section4.A01.RadialPotential
open scoped ContDiff RealInnerProductSpace

/-- `G(y) = y₁ e₀`: smooth, but `∂₀G₁ = 0 ≠ 1 = ∂₁G₀`. -/
def M : Space →L[ℝ] Space := (EuclideanSpace.proj (1 : Fin 3)).smulRight (coordinateVector 0)

def G : SpatialField := fun y => M y

theorem G_contDiff : ContDiff ℝ ∞ G := M.contDiff

/-- `G` really fails the symmetric-Jacobian hypothesis. -/
theorem G_not_symm : ¬ HasSymmetricJacobian G := by
  rintro ⟨-, hsym⟩
  have h := hsym 0 0 1
  rw [show G = ⇑M from rfl, M.fderiv] at h
  simp [M, coordinateVector] at h

/-- The radial potential of `G` is `y ↦ y₁y₀/2`. -/
theorem pot_eq : (fun y : Space => ∫ r in (0:ℝ)..1, (inner ℝ (G (r • y)) y : ℝ))
    = fun y : Space => (y 1 * y 0) / 2 := by
  funext y
  have hi : ∀ r : ℝ, (inner ℝ (G (r • y)) y : ℝ) = r * (y 1 * y 0) := by
    intro r
    simp [G, M, coordinateVector, real_inner_smul_left, EuclideanSpace.inner_single_left]
  simp only [hi]
  rw [intervalIntegral.integral_mul_const, integral_id]
  ring

set_option autoImplicit false in
/-- **`hG` is load-bearing**: without it the statement is FALSE. -/
theorem hG_load_bearing
    (H : ∀ (G' : SpatialField), ContDiff ℝ ∞ G' → ∀ x : Space,
        HasFDerivAt (fun y => ∫ r in (0:ℝ)..1, (inner ℝ (G' (r • y)) y : ℝ))
          (innerSL ℝ (G' x)) x) :
    False := by
  have h := H G G_contDiff (coordinateVector 0)
  rw [pot_eq] at h
  have hG0 : G (coordinateVector (0 : Fin 3)) = 0 := by
    simp [G, M, coordinateVector]
  rw [hG0, map_zero] at h
  have hpt : (coordinateVector (0 : Fin 3) : Space) + (0:ℝ) • (coordinateVector (1 : Fin 3) : Space)
      = coordinateVector 0 := by simp
  have h' : HasFDerivAt (fun y : Space => ((y 1 : ℝ) * y 0) / 2) (0 : Space →L[ℝ] ℝ)
      ((coordinateVector (0 : Fin 3) : Space) + (0:ℝ) • (coordinateVector (1 : Fin 3) : Space)) := by
    rw [hpt]; exact h
  have hγ : HasDerivAt
      (fun s : ℝ => (coordinateVector (0 : Fin 3) : Space) + s • (coordinateVector (1 : Fin 3) : Space))
      (coordinateVector 1) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const (coordinateVector (1 : Fin 3))).const_add
      (coordinateVector (0 : Fin 3))
  have hcomp := h'.comp_hasDerivAt 0 hγ
  simp only [zero_apply] at hcomp
  have hfun : ((fun y : Space => ((y 1 : ℝ) * y 0) / 2) ∘
      fun s : ℝ => (coordinateVector (0 : Fin 3) : Space) + s • (coordinateVector (1 : Fin 3) : Space))
      = fun s : ℝ => s / 2 := by
    funext s
    simp [coordinateVector]
  rw [hfun] at hcomp
  have hreal : HasDerivAt (fun s : ℝ => s / 2) (1/2) 0 := by
    simpa using (hasDerivAt_id (0:ℝ)).div_const 2
  have hcontra := hcomp.unique hreal
  norm_num at hcontra

end Rev113.Radial

/-! ## §6.3 — `hsym` is redundant (F1: NOT load-bearing) -/
namespace Rev113.Gauge

open Set
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A01.RadialPotential
open NSFormalization.Section4.A01.PressureGauge
open scoped ContDiff RealInnerProductSpace

/-! The two `private` helpers of `PressureGauge.lean`, copied verbatim (post-113 proofs)
    because they are not exported. -/

private theorem fderiv_apply_component {G : Space → Space} {x : Space}
    (hG : DifferentiableAt ℝ G x) (v : Space) (b : Fin 3)
    {H : Space → ℝ} (hH : H = fun y : Space => (G y) b) :
    (fderiv ℝ G x v) b = fderiv ℝ H x v := by
  have heq : H = ⇑(EuclideanSpace.proj b) ∘ G := hH
  rw [heq, ((EuclideanSpace.proj b).hasFDerivAt.comp x hG.hasFDerivAt).fderiv,
    ContinuousLinearMap.comp_apply]
  rfl

private theorem fderiv_fderiv_apply {f : Space → ℝ} {x : Space}
    (hf : DifferentiableAt ℝ (fderiv ℝ f) x) (v w : Space) :
    fderiv ℝ (fun y : Space => (fderiv ℝ f y) w) x v = (fderiv ℝ (fderiv ℝ f) x v) w := by
  rw [fderiv_clm_apply hf (differentiableAt_const w)]; simp

set_option autoImplicit false in
/-- **`hsym` is NOT load-bearing**: it is implied by `hsm` + `hdp`. -/
theorem hsym_redundant {T : ℝ} (p : PressureField)
    (hsm : ∀ t ∈ Ico (0:ℝ) T, ContDiff ℝ ∞ (fun y : Space => pressureGradient p t y))
    (hdp : ∀ t ∈ Ico (0:ℝ) T, Differentiable ℝ (fun y : Space => p (t, y))) :
    ∀ t ∈ Ico (0:ℝ) T, HasSymmetricJacobian (fun y : Space => pressureGradient p t y) := by
  intro t ht
  have hgrad := hsm t ht
  have hfd : fderiv ℝ (fun y : Space => p (t, y))
      = fun x : Space => (innerSL ℝ (pressureGradient p t x) : Space →L[ℝ] ℝ) := by
    funext x
    apply ContinuousLinearMap.ext
    intro v
    simpa using pressureGradient_fderiv_slice p t x v
  have hslice : ContDiff ℝ ∞ (fun z : Space => p (t, z)) := by
    rw [contDiff_infty_iff_fderiv]
    refine ⟨hdp t ht, ?_⟩
    rw [hfd]
    exact (innerSL ℝ (E := Space)).contDiff.comp hgrad
  refine ⟨hgrad.differentiable (by simp), ?_⟩
  intro x i j
  have hGdiff : DifferentiableAt ℝ (fun y : Space => pressureGradient p t y) x :=
    (hgrad.differentiable (by simp)) x
  have hff : DifferentiableAt ℝ (fderiv ℝ (fun z : Space => p (t, z))) x :=
    ((hslice.fderiv_right (m := ∞) (by simp)).differentiable (by simp)) x
  have hsymm := (hslice.contDiffAt (x := x)).isSymmSndFDerivAt (n := ∞) (by simp)
  have hcomp : ∀ (a b : Fin 3),
      (fderiv ℝ (fun y : Space => pressureGradient p t y) x (coordinateVector a)) b
        = (fderiv ℝ (fderiv ℝ (fun z : Space => p (t, z))) x (coordinateVector a))
            (coordinateVector b) := by
    intro a b
    have hH : (fun y : Space => (fderiv ℝ (fun z : Space => p (t, z)) y) (coordinateVector b))
        = fun y : Space => ((fun y : Space => pressureGradient p t y) y) b :=
      funext (fun y => (pressureGradient_apply p t y b).symm)
    rw [fderiv_apply_component hGdiff (coordinateVector a) b hH,
      fderiv_fderiv_apply hff (coordinateVector a) (coordinateVector b)]
  rw [hcomp i j, hcomp j i]
  exact hsymm.eq (coordinateVector i) (coordinateVector j)

set_option autoImplicit false in
/-- Therefore the `hsym`-free version of `pressure_potential_of_pointwise` is provable. -/
theorem pressure_potential_of_pointwise_without_hsym {T : ℝ} (p : PressureField)
    (hsm : ∀ t ∈ Ico (0:ℝ) T, ContDiff ℝ ∞ (fun y : Space => pressureGradient p t y))
    (hdp : ∀ t ∈ Ico (0:ℝ) T, Differentiable ℝ (fun y : Space => p (t, y))) :
    NSFormalization.Section4.A02.PressureGaugeEquivOn (Ico (0:ℝ) T)
      (pressurePotential (fun z : SpaceTime => pressureGradient p z.1 z.2)) p :=
  pressure_potential_of_pointwise p (hsym_redundant p hsm hdp) hsm hdp

end Rev113.Gauge

/-! ## §6.5 — fidelity: each probe's premise is the real theorem minus one hypothesis -/
namespace Rev113.Fidelity

open Set
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A01
open NSFormalization.Section4.A01.RadialPotential
open NSFormalization.Section4.A01.PressureGauge
open scoped ContDiff RealInnerProductSpace

set_option autoImplicit false in
example : ∀ (ν : ℝ) (u : VelocityField) (p : PressureField) (t : ℝ) (x : Space) (F : Space),
    DifferentiableAt ℝ (fun y : Space => u (t, y)) x →
    spatialDivergence u t x = 0 →
    (NavierStokesR3.ProblemStatement.navierStokesResidual ν u p t x = F
      ↔ temporalDerivative u t x - ν • spatialLaplacian u t x
          = (F - convectionDivergence u t x) - pressureGradient p t x) :=
  fun ν u p t x F hu hdiv => navierStokesResidual_eq_iff_projected ν u p t x F hu hdiv

set_option autoImplicit false in
example : ∀ (G' : SpatialField), HasSymmetricJacobian G' → ContDiff ℝ ∞ G' → ∀ x : Space,
    HasFDerivAt (fun y => ∫ r in (0:ℝ)..1, (inner ℝ (G' (r • y)) y : ℝ))
      (innerSL ℝ (G' x)) x :=
  fun _G' hG hsm x => hasFDerivAt_radialPotential hG hsm x

set_option autoImplicit false in
example : ∀ (T : ℝ) (p : PressureField),
    (∀ t ∈ Ico (0:ℝ) T, HasSymmetricJacobian (fun y : Space => pressureGradient p t y)) →
    (∀ t ∈ Ico (0:ℝ) T, ContDiff ℝ ∞ (fun y : Space => pressureGradient p t y)) →
    (∀ t ∈ Ico (0:ℝ) T, Differentiable ℝ (fun y : Space => p (t, y))) →
    NSFormalization.Section4.A02.PressureGaugeEquivOn (Ico (0:ℝ) T)
      (pressurePotential (fun z : SpaceTime => pressureGradient p z.1 z.2)) p :=
  fun _T p hsym hsm hdp => pressure_potential_of_pointwise p hsym hsm hdp

end Rev113.Fidelity

end
