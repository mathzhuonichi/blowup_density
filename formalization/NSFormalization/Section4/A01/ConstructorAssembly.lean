import NSFormalization.Section4.A01.AprioriInvariance
import NSFormalization.Section4.A01.ConstructorDivergence
import NSFormalization.Section4.A01.ConstructorPressure
import NSFormalization.Section4.A01.CylinderWiring
import NSFormalization.Section4.A01.DatumPathContinuous
import NSFormalization.Section4.A01.DatumPathDeriv
import NSFormalization.Section4.A01.ForceBridge
import NSFormalization.Section4.A01.JointRepresentative
import NSFormalization.Section4.A01.SliceWiring
import NavierStokes.GenericEndpointExtension

/-!
# A01 unit B2: conditional classical constructor assembly

This module builds a `ClassicalSolutionR` from the smooth representative chosen
by B1 R4.  The constructor is parameterized by an arbitrary spacetime field
`velocity` together with its a.e. slice identity against the ordinary `L²`
path.  In particular, joint smoothness is never requested of the raw `Lp`
coercion.  The clamped raw representative is retained only as a convenient
zero-instance witness.
-/

noncomputable section

namespace NSFormalization.Section4.A01

open Set MeasureTheory Filter Topology EulerLpTranslation EulerMeanOrdinaryLift
open EulerMeanSmoothRepresentative EulerCylinderSobolevSpace EulerLiftedGradientSpace
open EulerCylinderSobolev EulerQuadraticSource EulerSobolevHeat EulerVolterraConvolution
open EulerSmoothFieldSobolevTime EulerMetricTransport
open NSFormalization.Source.ForcedCylinderLocal
open NSFormalization.Section4.D01
open NSFormalization.Paper3 (RealVectorSobolev)
open NavierStokes.ProblemStatement
  (Space SpaceTime coordinateVector pressureGradient spatialDivergence)
open NSFormalization.Section4.A02 (ClassicalSolutionR SpaceTimeField SpatialField)
open scoped ContDiff

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-- The pointwise ordinary carrier, clamped to the prescribed cylinder horizon.

For `t ∈ [0,S]` its slice is definitionally `⇑(U t)`.  For `t > S` it is
constant with value `⇑(U S)`.  Those values are deliberately irrelevant to the
classical horizon `T := S`. -/
def constructedVelocity {S : ℝ} (hS : 0 ≤ S)
    (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2)) : SpaceTimeField :=
  fun z => (U (projIcc 0 S hS z.1) : Space → Space) z.2

/-- On the prescribed closed horizon, `constructedVelocity` is the ordinary
`L²` representative of the supplied carrier, with no a.e. transport needed. -/
theorem constructedVelocity_slice {S : ℝ} (hS : 0 ≤ S)
    (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2))
    (t : Icc (0 : ℝ) S) :
    (fun x : Space => constructedVelocity hS U (t.1, x)) =ᵐ[volume] ⇑(U t) := by
  have ht : projIcc 0 S hS t.1 = t := by
    exact Subtype.ext (congrArg Subtype.val (projIcc_of_mem hS t.2))
  change (fun x : Space => (U (projIcc 0 S hS t.1) : Space → Space) x) =ᵐ[volume] ⇑(U t)
  rw [ht]

/-- The clamped carrier of the zero path is the zero spacetime field. -/
theorem constructedVelocity_zero {S : ℝ} (hS : 0 ≤ S) :
    constructedVelocity hS
      (0 : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2)) = 0 := by
  funext z
  simp [constructedVelocity]

/-- Any jointly smooth representative of the ordinary cylinder path is
pointwise divergence-free.  The a.e. slice identity is lifted through the
measure-preserving ordinary projection before applying the vendor's direct
weak-to-classical divergence theorem. -/
theorem velocity_divergence {q : ℕ} {S : ℝ}
    (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)))
    (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2))
    (hU : ∀ t, ordinaryLift (U t) = value 1 (u t))
    (hdiv : ∀ t, value 1 (u t) ∈ divergenceFreeSpace 1 1 0)
    (velocity : SpaceTimeField)
    (hslice : ∀ t : Icc (0 : ℝ) S,
      (fun x : Space => velocity (t.1, x)) =ᵐ[volume] ⇑(U t))
    (hc3 : ContDiffOn ℝ ∞ velocity
      (Ico (0 : ℝ) S ×ˢ (univ : Set Space))) :
    ∀ t ∈ Ico (0 : ℝ) S, ∀ x : Space,
      spatialDivergence velocity t x = 0 := by
  intro t ht x
  let τ : Icc (0 : ℝ) S := ⟨t, ht.1, ht.2.le⟩
  have hrep0 := ordinaryLift_ae (U τ)
  rw [hU τ] at hrep0
  have hvelocityLift : (fun p : LiftDomain 1 => U τ p.1) =ᵐ[liftMeasure 1]
      fun p : LiftDomain 1 => velocity (t, p.1) := by
    exact ordinaryProjection_measurePreserving.quasiMeasurePreserving.ae
      (hslice τ).symm
  have hrep : ((value 1 (u τ) : LiftDomain 1 → Space)) =ᵐ[liftMeasure 1]
      fun p : LiftDomain 1 => velocity (t, p.1) :=
    hrep0.trans hvelocityLift
  have hsmooth : ContDiff ℝ ∞ (fun y : Space => velocity (t, y)) :=
    NSFormalization.Section4.D01.contDiff_slice hc3 ht
  have hlocal : ∀ p : LiftDomain 1,
      ContDiff ℝ ∞
        (localFieldLift 1 (fun z : LiftDomain 1 => velocity (t, z.1)) p) := by
    intro p
    exact hsmooth.comp (contDiff_const.add contDiff_fst)
  have hlifted_zero :=
    EulerClassicalDivergence.divergenceFree_classical_divergence_zero
      1 1 (0 : Space) (value 1 (u τ)) (hdiv τ)
      (fun p : LiftDomain 1 => velocity (t, p.1)) hrep hlocal
  have hx := hlifted_zero (x, 0)
  simpa [EulerMeanCylinderSolenoidal.fieldDerivative_spatial 1
    (fun y : Space => velocity (t, y)) hsmooth,
    coordinateDirection, coordinateVector, spatialDivergence,
    NavierStokes.ProblemStatement.spatialDerivative] using hx

/-- An all-order datum path for the abstract `L²` carrier is also an all-order
datum path for any a.e.-agreeing representative.  This is the exact
`ContinuousOn`/`Ico` spelling consumed by lane 189. -/
theorem velocitySobolev_of_hslice {S : ℝ}
    (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2))
    (velocity : SpaceTimeField)
    (hslice : ∀ t : Icc (0 : ℝ) S,
      (fun x : Space => velocity (t.1, x)) =ᵐ[volume] ⇑(U t))
    (hsob : ∀ m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
      ContDiffOn ℝ 0 G (Icc (0 : ℝ) S) ∧
      ∀ t : Icc (0 : ℝ) S, IsSobolevDatum (m : ℝ) (⇑(U t)) (G t.1)) :
    ∀ m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
      ContinuousOn G (Icc (0 : ℝ) S) ∧
      ∀ t ∈ Ico (0 : ℝ) S,
        IsSobolevDatum (m : ℝ) (fun x : Space => velocity (t, x)) (G t) := by
  intro m
  obtain ⟨G, hG, hGdatum⟩ := hsob m
  refine ⟨G, hG.continuousOn, ?_⟩
  intro t ht
  let τ : Icc (0 : ℝ) S := ⟨t, ht.1, ht.2.le⟩
  exact IsSobolevDatum.congr_field (hGdatum τ) (hslice τ).symm

/-! ## Slab-local smoothness of the radial pressure -/

/-- A jointly smooth vector field on the physical half-open slab has a jointly
smooth radial potential on that same slab.  This is the slab form needed by
`ClassicalSolutionR.pressure_smooth`.

`ConstructorPressure.pressure_smooth_of_velocity_smooth` asks for a globally
smooth vector field because its compact-parameter integral lemma is global.
Here, at each point of `[0,S)`, we rescale a smaller closed slab `[0,b]` to the
vendor's closed strip `[-1,1]`, use
`GenericEndpointExtension.closedStripExtension` to obtain a genuine smooth
extension, apply the same compact-parameter argument, and transfer the result
back by local equality.  Thus no smoothness across `t = S` (or on negative
times) is assumed. -/
theorem pressurePotential_contDiffOn_slab {S : ℝ} (G : SpaceTimeField)
    (hG : ContDiffOn ℝ ∞ G (Ico (0 : ℝ) S ×ˢ (univ : Set Space))) :
    ContDiffOn ℝ ∞ (RadialPotential.pressurePotential G)
      (Ico (0 : ℝ) S ×ˢ (univ : Set Space)) := by
  intro z hz
  let b : ℝ := (z.1 + S) / 2
  have hzb : z.1 < b := by dsimp [b]; linarith [hz.1.2]
  have hbS : b < S := by dsimp [b]; linarith [hz.1.2]
  have hb : 0 < b := lt_of_le_of_lt hz.1.1 hzb
  let F : SpaceTimeField := fun y => G (b * (y.1 + 1) / 2, y.2)
  have hF : ContDiffOn ℝ ∞ F
      (NavierStokes.GenericEndpointExtension.closedStrip (X := Space)) := by
    apply hG.comp (by fun_prop)
    rintro y ⟨hy, -⟩
    refine ⟨⟨?_, ?_⟩, mem_univ _⟩
    · nlinarith [hy.1, hb]
    · have hle : b * (y.1 + 1) / 2 ≤ b := by nlinarith [hy.2, hb]
      exact lt_of_le_of_lt hle hbS
  let E : SpaceTimeField :=
    NavierStokes.GenericEndpointExtension.closedStripExtension F hF
  have hE : ContDiff ℝ ∞ E :=
    NavierStokes.GenericEndpointExtension.closedStripExtension_contDiff hF
  let Gext : SpaceTimeField := fun y => E (2 * y.1 / b - 1, y.2)
  have hGext : ContDiff ℝ ∞ Gext := hE.comp (by fun_prop)
  have hGext_eq (y : SpaceTime) (hy : y.1 ∈ Icc (0 : ℝ) b) : Gext y = G y := by
    have hscaled : 2 * y.1 / b - 1 ∈ Icc (-1 : ℝ) 1 := by
      constructor <;> (field_simp; nlinarith [hy.1, hy.2, hb])
    rw [show Gext y = E (2 * y.1 / b - 1, y.2) by rfl]
    rw [show E (2 * y.1 / b - 1, y.2) = F (2 * y.1 / b - 1, y.2) by
      exact NavierStokes.GenericEndpointExtension.closedStripExtension_eq hF
        ⟨hscaled, mem_univ _⟩]
    change G (b * ((2 * y.1 / b - 1) + 1) / 2, y.2) = G y
    congr 2
    field_simp
    ring
  have hPext : ContDiff ℝ ∞ (RadialPotential.pressurePotential Gext) := by
    let H : SpaceTime × ℝ → ℝ := fun p =>
      inner ℝ (Gext (p.1.1, p.2 • p.1.2)) p.1.2
    have harg : ContDiff ℝ ∞
        (fun p : SpaceTime × ℝ => ((p.1.1, p.2 • p.1.2) : SpaceTime)) := by
      fun_prop
    have hx : ContDiff ℝ ∞ (fun p : SpaceTime × ℝ => p.1.2) := by
      fun_prop
    have hH : ContDiff ℝ ∞ H := (hGext.comp harg).inner ℝ hx
    exact EulerCompactParameterIntegral.integral_contDiff 0 1 (by norm_num) H hH
  have heq : RadialPotential.pressurePotential G =ᶠ[
      𝓝[Ico (0 : ℝ) S ×ˢ (univ : Set Space)] z]
      RadialPotential.pressurePotential Gext := by
    have hopen : Iio b ×ˢ (univ : Set Space) ∈ 𝓝 z :=
      (isOpen_Iio.prod isOpen_univ).mem_nhds ⟨hzb, mem_univ _⟩
    have hopen' : Iio b ×ˢ (univ : Set Space) ∈
        𝓝[Ico (0 : ℝ) S ×ˢ (univ : Set Space)] z :=
      nhdsWithin_le_nhds hopen
    filter_upwards [hopen', self_mem_nhdsWithin]
      with y hyopen hyD
    simp only [RadialPotential.pressurePotential]
    apply intervalIntegral.integral_congr
    intro r _
    exact congrArg (fun v : Space => inner ℝ v y.2)
      (hGext_eq (y.1, r • y.2) ⟨hyD.1.1, hyopen.1.le⟩).symm
  exact hPext.contDiffAt.contDiffWithinAt.congr_of_eventuallyEq_of_mem heq hz

/-- Momentum from a supplier-provided pressure-gradient representative.  The
representative is required to agree with the velocity-derived expression only
on the open time interior, exactly where `ClassicalSolutionR.momentum` is
stated.  Its separate slab regularity is what makes the radial pressure smooth
at the initial endpoint. -/
theorem momentum_of_supplied_gradient {T : ℝ} (ν : ℝ)
    (f velocity G : SpaceTimeField)
    (hvelocity : ContDiffOn ℝ ∞ velocity
      (Ico (0 : ℝ) T ×ˢ (univ : Set Space)))
    (hdiv : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Space,
      spatialDivergence velocity t x = 0)
    (hG_int : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x : Space,
      G (t, x) = pressureGradientOfVelocity ν f velocity (t, x))
    (hG_smooth : ∀ t ∈ Ioo (0 : ℝ) T,
      ContDiff ℝ ∞ (fun x : Space => G (t, x)))
    (hG_symm : ∀ t ∈ Ioo (0 : ℝ) T,
      RadialPotential.HasSymmetricJacobian (fun x : Space => G (t, x))) :
    ∀ t ∈ Ioo (0 : ℝ) T, ∀ x : Space,
      NavierStokesR3.ProblemStatement.navierStokesResidual ν velocity
        (RadialPotential.pressurePotential G) t x = f (t, x) := by
  intro t ht x
  have htIco : t ∈ Ico (0 : ℝ) T := ⟨ht.1.le, ht.2⟩
  have hu : DifferentiableAt ℝ (fun y : Space => velocity (t, y)) x :=
    ((NSFormalization.Section4.D01.contDiff_slice hvelocity htIco).differentiable
      (by simp)) x
  refine (navierStokesResidual_eq_iff_projected ν velocity
    (RadialPotential.pressurePotential G) t x (f (t, x)) hu
      (hdiv t htIco x)).2 ?_
  rw [RadialPotential.pressureGradient_pressurePotential
    (hG_symm t ht) (hG_smooth t ht) (fun _ => rfl) x]
  rw [hG_int t ht x]
  rw [convectionDivergence_eq_advection velocity t x hu (hdiv t htIco x)]
  simp only [pressureGradientOfVelocity, momentumResidualOfVelocity]
  abel

/-- Assemble the classical solution from one prescribed-horizon local-theory
carrier and the smooth representative selected by B1 R4.  The open analytic
rungs are the three explicitly named inputs:

* `hsob` is lane 192's `hsob_of_bounds` output (the all-order datum paths at
  `j = 0`), supplied from the all-order a-priori bound;
* `velocity`, `hslice`, and `hc3` are exactly the existential field, a.e. slice
  identity, and joint-smoothness output of lane 190;
* `G`, `hG_int`, and `hG` are the pressure-regularity output owed by lane 189:
  an interior representative of `pressureGradientOfVelocity` that is smooth
  on the closed initial slab and whose slices are square-integrable with
  symmetric spatial Jacobian.

All remaining `ClassicalSolutionR` fields are constructed below. -/
theorem carrierConstructor_of_localTheory {q : ℕ} {S ν : ℝ}
    (hS : 0 < S)
    (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)))
    (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2))
    (hU : ∀ t, ordinaryLift (U t) = value 1 (u t))
    (hdiv : ∀ t, value 1 (u t) ∈ divergenceFreeSpace 1 1 0)
    (f : SpaceTimeField)
    (velocity : SpaceTimeField)
    (hslice : ∀ t : Icc (0 : ℝ) S,
      (fun x : Space => velocity (t.1, x)) =ᵐ[volume] ⇑(U t))
    (hsob : ∀ m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
      ContDiffOn ℝ 0 G (Icc (0 : ℝ) S) ∧
      ∀ t : Icc (0 : ℝ) S, IsSobolevDatum (m : ℝ) (⇑(U t)) (G t.1))
    (hc3 : ContDiffOn ℝ ∞ velocity
      (Ico (0 : ℝ) S ×ˢ (univ : Set Space)))
    (G : SpaceTimeField)
    (hG_int : ∀ t ∈ Ioo (0 : ℝ) S, ∀ x : Space,
      G (t, x) = pressureGradientOfVelocity ν f velocity (t, x))
    (hG :
      ContDiffOn ℝ ∞ G (Ico (0 : ℝ) S ×ˢ (univ : Set Space)) ∧
      ∀ t ∈ Ico (0 : ℝ) S,
        MemLp (fun x : Space => G (t, x)) 2 volume ∧
        RadialPotential.HasSymmetricJacobian (fun x : Space => G (t, x))) :
    ∃ w : ClassicalSolutionR ν
        (fun x : Space => velocity (0, x)) f S,
      w.velocity = velocity ∧
        ∀ t : Icc (0 : ℝ) S,
          (fun x : Space => w.velocity (t.1, x)) =ᵐ[volume] ⇑(U t) := by
  let pressure := RadialPotential.pressurePotential G
  have hdivergence : ∀ t ∈ Ico (0 : ℝ) S, ∀ x : Space,
      spatialDivergence velocity t x = 0 :=
    velocity_divergence u U hU hdiv velocity hslice hc3
  have hsob_velocity := velocitySobolev_of_hslice U velocity hslice hsob
  have hgradient_slice : ∀ t ∈ Ico (0 : ℝ) S,
      ContDiff ℝ ∞ (fun x : Space => G (t, x)) := by
    intro t ht
    exact NSFormalization.Section4.D01.contDiff_slice hG.1 ht
  have hgradient_symm : ∀ t ∈ Ico (0 : ℝ) S,
      RadialPotential.HasSymmetricJacobian (fun x : Space => G (t, x)) := by
    intro t ht
    exact (hG.2 t ht).2
  let w : ClassicalSolutionR ν
      (fun x : Space => velocity (0, x)) f S :=
    { velocity := velocity
      pressure := pressure
      horizon_pos := hS
      velocity_smooth := hc3
      pressure_smooth := by
        exact pressurePotential_contDiffOn_slab G hG.1
      initial := fun _ => rfl
      divergence := hdivergence
      momentum := momentum_of_supplied_gradient ν f velocity G hc3 hdivergence hG_int
        (fun t ht => hgradient_slice t ⟨ht.1.le, ht.2⟩)
        (fun t ht => hgradient_symm t ⟨ht.1.le, ht.2⟩)
      sobolev := by
        intro m
        obtain ⟨G, hG, hGdatum⟩ := hsob_velocity m
        exact ⟨G, hG.mono Ico_subset_Icc_self, hGdatum⟩
      pressure_gradient := by
        intro t ht
        have hfield :
            (fun x : Space => pressureGradient pressure t x) =
              fun x : Space => G (t, x) := by
          funext x
          exact RadialPotential.pressureGradient_pressurePotential
            (hgradient_symm t ht) (hgradient_slice t ht) (fun _ => rfl) x
        rw [hfield]
        exact (hG.2 t ht).1 }
  refine ⟨w, rfl, ?_⟩
  exact hslice

/-- The historical lane-158 consumer shape with a classical horizon strictly
longer than the cylinder horizon.

This is retained only for compatibility and negative-example documentation.
Supplying it by clamping `constructedVelocity` at `S` and choosing a horizon
`T > S` would require joint smoothness across the clamp, which is unsatisfiable
for non-stationary solutions. -/
def CarrierConstructorFullClamped {q : ℕ} (hq : 6 ≤ q) {ν S R : ℝ}
    (hν : 0 < ν) (hS : 0 < S) (a : SmoothL2Field Space)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n) : Prop :=
  ∀ (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)))
    (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2)),
      ‖u‖ ≤ R →
      u ⟨0, le_rfl, hS.le⟩ = ordinarySobolev (q + 1) a.toLp a.translation_contDiff →
      U ⟨0, le_rfl, hS.le⟩ = a.toLp →
      (∀ t, ordinaryLift (U t) = value 1 (u t)) →
      (∀ t, value 1 (u t) ∈ divergenceFreeSpace 1 1 0) →
      (∀ t, u t = quadraticDuhamel 1 ν hν hS.le le_rfl
        (coefficients 1 hq (sobolevPath F hF q))
        (ordinarySobolev (q + 1) a.toLp a.translation_contDiff) u t) →
      (∀ (θ : AddCircle (1 : ℝ)) t,
        sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t) →
      ∃ (a' : SpatialField) (f' : SpaceTimeField) (T : ℝ) (_hST : S < T)
        (w : ClassicalSolutionR ν a' f' T),
        ∀ t : Icc (0 : ℝ) S,
          (fun x : Space => w.velocity (↑t, x)) =ᵐ[volume] ⇑(U t)

set_option linter.unusedVariables false in
/-- The exact pressure field owed after lanes 192 and 190 have selected one
ordinary carrier and one jointly smooth representative.  The contextual
hypotheses are intentionally arguments of the proposition: lanes 194/195/197
need the same-carrier all-order cylinder family, the canonical solenoidal datum,
the canonical force, and the all-order ordinary paths.  Lane 180 consumes only
the resulting field and its three properties. -/
def PressureSupply {q : ℕ} (hq : 6 ≤ q) {ν S : ℝ}
    (hν : 0 < ν) (hS : 0 < S) (f : SpaceTimeField)
    (hf : NSFormalization.Section4.D01.MemForceR f) (a : SmoothL2Field Space)
    (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2))
    (hpairs : ∀ p (hp : 6 ≤ p),
      ∃ u : C(Icc (0 : ℝ) S, SobolevSpace 1 (p + 1)),
        (∀ t, ordinaryLift (U t) = value 1 (u t)) ∧
        (∀ t, value 1 (u t) ∈ divergenceFreeSpace 1 1 0) ∧
        (∀ (θ : AddCircle (1 : ℝ)) t,
          sobolevTranslation 1 (p + 1) (0, θ) (u t) = u t) ∧
        ∀ t, u t = quadraticDuhamel 1 ν hν hS.le le_rfl
          (coefficients 1 hp
            (sobolevPath (NSFormalization.Section4.C01.forcePath (S := S) hf)
              (NSFormalization.Section4.C01.forcePath_jetLp_continuous
                (S := S) hf) p))
          (ordinarySobolev (p + 1) a.toLp a.translation_contDiff) u t)
    (hpaths : ∀ j m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
      ContDiffOn ℝ j G (Icc (0 : ℝ) S) ∧
      ∀ t : Icc (0 : ℝ) S, IsSobolevDatum (m : ℝ) (⇑(U t)) (G t.1))
    (velocity : SpaceTimeField)
    (hslice : ∀ t : Icc (0 : ℝ) S,
      (fun x : Space => velocity (t.1, x)) =ᵐ[volume] ⇑(U t))
    (hc3 : ContDiffOn ℝ ∞ velocity
      (Ico (0 : ℝ) S ×ˢ (univ : Set Space))) : Prop :=
  ∃ G : SpaceTimeField,
    (∀ t ∈ Ioo (0 : ℝ) S, ∀ x : Space,
      G (t, x) = pressureGradientOfVelocity ν f velocity (t, x)) ∧
    ContDiffOn ℝ ∞ G (Ico (0 : ℝ) S ×ˢ (univ : Set Space)) ∧
    ∀ t ∈ Ico (0 : ℝ) S,
      MemLp (fun x : Space => G (t, x)) 2 volume ∧
      RadialPotential.HasSymmetricJacobian (fun x : Space => G (t, x))

/-- The full fixed-pair consumer, cut at the suppliers' landed interfaces.
The same-carrier all-order cylinder family and paths are lane 192's output, the
velocity is lane 190's selected representative, and the final hypothesis is the
scoped pressure obligation. -/
def CarrierConstructorFull {q : ℕ} (hq : 6 ≤ q) {ν S : ℝ}
    (hν : 0 < ν) (hS : 0 < S) (f : SpaceTimeField)
    (hf : NSFormalization.Section4.D01.MemForceR f) (a : SmoothL2Field Space)
    (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0) : Prop :=
  ∀ (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2))
    (hpairs : ∀ p (hp : 6 ≤ p),
      ∃ u : C(Icc (0 : ℝ) S, SobolevSpace 1 (p + 1)),
        (∀ t, ordinaryLift (U t) = value 1 (u t)) ∧
        (∀ t, value 1 (u t) ∈ divergenceFreeSpace 1 1 0) ∧
        (∀ (θ : AddCircle (1 : ℝ)) t,
          sobolevTranslation 1 (p + 1) (0, θ) (u t) = u t) ∧
        ∀ t, u t = quadraticDuhamel 1 ν hν hS.le le_rfl
          (coefficients 1 hp
            (sobolevPath (NSFormalization.Section4.C01.forcePath (S := S) hf)
              (NSFormalization.Section4.C01.forcePath_jetLp_continuous
                (S := S) hf) p))
          (ordinarySobolev (p + 1) a.toLp a.translation_contDiff) u t)
    (hpaths : ∀ j m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
      ContDiffOn ℝ j G (Icc (0 : ℝ) S) ∧
      ∀ t : Icc (0 : ℝ) S, IsSobolevDatum (m : ℝ) (⇑(U t)) (G t.1))
    (velocity : SpaceTimeField)
    (hslice : ∀ t : Icc (0 : ℝ) S,
      (fun x : Space => velocity (t.1, x)) =ᵐ[volume] ⇑(U t))
    (hc3 : ContDiffOn ℝ ∞ velocity
      (Ico (0 : ℝ) S ×ˢ (univ : Set Space))),
    PressureSupply hq hν hS f hf a ha U hpairs hpaths velocity hslice hc3 →
    ∃ w : ClassicalSolutionR ν (fun x : Space => velocity (0, x)) f S,
      w.velocity = velocity ∧
      ∀ t : Icc (0 : ℝ) S,
        (fun x : Space => w.velocity (↑t, x)) =ᵐ[volume] ⇑(U t)

/-- The fixed-pair constructor consumes the scoped pressure supply without
adding any supplier quantifier of its own. -/
theorem carrierConstructorFull_of_hyps {q : ℕ} (hq : 6 ≤ q) {ν S : ℝ}
    (hν : 0 < ν) (hS : 0 < S) (f : SpaceTimeField)
    (hf : NSFormalization.Section4.D01.MemForceR f) (a : SmoothL2Field Space)
    (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0) :
    CarrierConstructorFull hq hν hS f hf a ha := by
  intro U hpairs hpaths velocity hslice hc3 hpressure
  obtain ⟨u, hU, hdiv, _hinv, _hduh⟩ := hpairs q hq
  obtain ⟨G, hG_int, hG_smooth, hG_slices⟩ := hpressure
  exact carrierConstructor_of_localTheory hS u U hU hdiv f velocity hslice
    (hpaths 0) hc3 G hG_int ⟨hG_smooth, hG_slices⟩

/-- Both lane-157 norm-comparison rows when the classical and cylinder
horizons are the same.  The forward row is already an a.e./datum statement on
the closed interval.  For the converse row, the usual smooth-slice argument is
applied on `[0,S)`; at `S`, lane 149's endpoint argument is run on the
continuous cylinder norm and on the continuous order-`q+1` datum path supplied
by `exists_continuous_datumPath`. -/
theorem apriori_rows_of_hslice_same_horizon {q : ℕ} {ν : ℝ} {a : SpatialField}
    {f : SpaceTimeField} {S : ℝ} (hS : 0 < S) (hq : 4 ≤ q)
    (w : ClassicalSolutionR ν a f S)
    (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)))
    (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2))
    (hu : ∀ (θ : AddCircle (1 : ℝ)) t,
      sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t)
    (hU : ∀ t, ordinaryLift (U t) = value 1 (u t))
    (hslice : ∀ t : Icc (0 : ℝ) S,
      (fun x : Space => w.velocity (↑t, x)) =ᵐ[volume] ⇑(U t)) :
    (∀ t : Icc (0 : ℝ) S,
      NSFormalization.Section4.A04.sobolevNormAt (2 : ℝ) w.velocity ↑t ≤ 16 * ‖u t‖) ∧
      (∀ t : Icc (0 : ℝ) S,
        ‖u t‖ ≤ NSFormalization.Section4.D01.jetSobolevConst (q + 1) *
          NSFormalization.Section4.A04.sobolevNormAt ((q + 1 : ℕ) : ℝ)
            w.velocity ↑t) := by
  refine ⟨sobolevNormAt_two_le_of_cylinder u U hu hU hq w.velocity hslice, ?_⟩
  have hinterior : ∀ t : Icc (0 : ℝ) S, (t : ℝ) < S →
      ‖u t‖ ≤ jetSobolevConst (q + 1) *
        NSFormalization.Section4.A04.sobolevNormAt ((q + 1 : ℕ) : ℝ)
          w.velocity ↑t := by
    intro t htS
    have ht : (t : ℝ) ∈ Ico (0 : ℝ) S := ⟨t.2.1, htS⟩
    have hZ := NSFormalization.Section4.C01.velocity_slice_smoothL2 w ht
    let Z : SmoothL2Field Space :=
      { field := fun x : Space => w.velocity (↑t, x)
        smooth := hZ.1
        integrable := hZ.2 }
    apply sobolevSpace_norm_le_sobolevENorm (u t)
      (NSFormalization.Section4.D01.contDiff_slice w.velocity_smooth ht)
      (sobolevENorm_slice_ne_top w ht)
    intro n hn word
    exact hword_jet_full (u t) (fun θ => hu θ t) (U t) (hU t) Z
      (hslice t).symm n hn word
  obtain ⟨A, hAdatum, hAcont⟩ :=
    exists_continuous_datumPath u U hu hU (q + 1) (le_refl (q + 1))
  have hAw (t : Icc (0 : ℝ) S) : IsSobolevDatum ((q + 1 : ℕ) : ℝ)
      (fun x : Space => w.velocity (↑t, x)) (A t) :=
    IsSobolevDatum.congr_field (hAdatum t) (hslice t).symm
  intro t
  rcases lt_or_eq_of_le t.2.2 with htS | htS
  · exact hinterior t htS
  · have hmemS : (S : ℝ) ∈ Icc (0 : ℝ) S := ⟨hS.le, le_rfl⟩
    have hteq : t = (⟨S, hmemS⟩ : Icc (0 : ℝ) S) := Subtype.ext htS
    subst t
    let x : ℕ → ℝ := fun n => S - S / (n + 2)
    have hxmem : ∀ n, x n ∈ Icc (0 : ℝ) S := by
      intro n
      constructor
      · have hle : S / (n + 2) ≤ S := by
          rw [div_le_iff₀ (by positivity)]
          nlinarith [hS.le, Nat.cast_nonneg (α := ℝ) n]
        simpa [x] using hle
      · have : 0 ≤ S / (n + 2) := by positivity
        simpa [x] using this
    have hxlt : ∀ n, x n < S := by
      intro n
      have : 0 < S / (n + 2) := by positivity
      simpa [x] using this
    have hxtend : Filter.Tendsto x Filter.atTop (𝓝 S) := by
      have hd : Filter.Tendsto (fun n : ℕ => (n : ℝ) + 2) Filter.atTop Filter.atTop :=
        tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
      have hzero : Filter.Tendsto (fun n : ℕ => S / ((n : ℝ) + 2))
          Filter.atTop (𝓝 0) := hd.const_div_atTop S
      have hsub : Filter.Tendsto (fun n : ℕ => S - S / ((n : ℝ) + 2))
          Filter.atTop (𝓝 (S - 0)) :=
        (tendsto_const_nhds (x := S) (f := Filter.atTop)).sub hzero
      simpa [x] using hsub
    have hsub : Filter.Tendsto (fun n => (⟨x n, hxmem n⟩ : Icc (0 : ℝ) S))
        Filter.atTop (𝓝 (⟨S, hmemS⟩ : Icc (0 : ℝ) S)) :=
      tendsto_subtype_rng.mpr hxtend
    have hleft : Filter.Tendsto (fun n => ‖u ⟨x n, hxmem n⟩‖) Filter.atTop
        (𝓝 ‖u ⟨S, hmemS⟩‖) :=
      ((continuous_norm.comp u.continuous).tendsto _).comp hsub
    have hright : Filter.Tendsto
        (fun n => jetSobolevConst (q + 1) * ‖A ⟨x n, hxmem n⟩‖) Filter.atTop
        (𝓝 (jetSobolevConst (q + 1) * ‖A ⟨S, hmemS⟩‖)) :=
      ((continuous_const.mul (continuous_norm.comp hAcont)).tendsto _).comp hsub
    rw [NSFormalization.Section4.A04.sobolevNormAt_eq (hAw ⟨S, hmemS⟩)]
    apply le_of_tendsto_of_tendsto hleft hright
    exact Filter.Eventually.of_forall fun n => by
      have hi := hinterior ⟨x n, hxmem n⟩ (hxlt n)
      rw [NSFormalization.Section4.A04.sobolevNormAt_eq
        (hAw ⟨x n, hxmem n⟩)] at hi
      exact hi

/-- The audited 192 → 190 → pressure → 180 consumer loop.  Lane 192's
family-returning theorem is invoked with `hb`; its selected all-order paths are
passed to lane 190; and the pressure supplier receives that same carrier's
complete cylinder family. -/
theorem rows_from_constructor_full {q : ℕ} (hq : 6 ≤ q)
    {f : SpaceTimeField} (hf : NSFormalization.Section4.D01.MemForceR f)
    {ν S : ℝ} (hν : 0 < ν) (hS : 0 < S)
    (a : SmoothL2Field Space) (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (R : ℕ → ℝ)
    (hb : ∀ p (hp : 6 ≤ p), HasAprioriBound hp hν a
      (NSFormalization.Section4.C01.forcePath (S := S) hf)
      (NSFormalization.Section4.C01.forcePath_jetLp_continuous (S := S) hf) (R p))
    (hpressure : ∀
      (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2))
      (hpairs : ∀ p (hp : 6 ≤ p),
        ∃ u : C(Icc (0 : ℝ) S, SobolevSpace 1 (p + 1)),
          (∀ t, ordinaryLift (U t) = value 1 (u t)) ∧
          (∀ t, value 1 (u t) ∈ divergenceFreeSpace 1 1 0) ∧
          (∀ (θ : AddCircle (1 : ℝ)) t,
            sobolevTranslation 1 (p + 1) (0, θ) (u t) = u t) ∧
          ∀ t, u t = quadraticDuhamel 1 ν hν hS.le le_rfl
            (coefficients 1 hp
              (sobolevPath (NSFormalization.Section4.C01.forcePath (S := S) hf)
                (NSFormalization.Section4.C01.forcePath_jetLp_continuous
                  (S := S) hf) p))
            (ordinarySobolev (p + 1) a.toLp a.translation_contDiff) u t)
      (hpaths : ∀ j m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
        ContDiffOn ℝ j G (Icc (0 : ℝ) S) ∧
        ∀ t : Icc (0 : ℝ) S, IsSobolevDatum (m : ℝ) (⇑(U t)) (G t.1))
      (velocity : SpaceTimeField)
      (hslice : ∀ t : Icc (0 : ℝ) S,
        (fun x : Space => velocity (t.1, x)) =ᵐ[volume] ⇑(U t))
      (hc3 : ContDiffOn ℝ ∞ velocity
        (Ico (0 : ℝ) S ×ˢ (univ : Set Space))),
      PressureSupply hq hν hS f hf a ha U hpairs hpaths velocity hslice hc3) :
    ∃ (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)))
      (a' : SpatialField) (f' : SpaceTimeField)
      (w : ClassicalSolutionR ν a' f' S),
      ‖u‖ ≤ R q ∧
      (∀ t : Icc (0 : ℝ) S,
        NSFormalization.Section4.A04.sobolevNormAt (2 : ℝ) w.velocity ↑t ≤ 16 * ‖u t‖) ∧
      (∀ t : Icc (0 : ℝ) S,
        ‖u t‖ ≤ NSFormalization.Section4.D01.jetSobolevConst (q + 1) *
          NSFormalization.Section4.A04.sobolevNormAt ((q + 1 : ℕ) : ℝ)
            w.velocity ↑t) := by
  obtain ⟨U, _hU0, hpairs, hpaths⟩ :=
    cylinderPair_of_bounds hf hν hS a ha R hb
  obtain ⟨velocity, hslice, hc3⟩ :=
    exists_joint_smooth_representative hS U hpaths
  have hpressure' := hpressure U hpairs hpaths velocity hslice hc3
  obtain ⟨w, _hw, hslice'⟩ :=
    carrierConstructorFull_of_hyps hq hν hS f hf a ha
      U hpairs hpaths velocity hslice hc3 hpressure'
  obtain ⟨u, hU, _hdiv, hu, hduh⟩ := hpairs q hq
  have hR' : ‖u‖ ≤ R q := hb q hq S hS.le le_rfl u hduh
  obtain ⟨hfwd, hconv⟩ :=
    apriori_rows_of_hslice_same_horizon hS (by omega) w u U hu hU hslice'
  exact ⟨u, fun x : Space => velocity (0, x), f, w, hR', hfwd, hconv⟩

end NSFormalization.Section4.A01
