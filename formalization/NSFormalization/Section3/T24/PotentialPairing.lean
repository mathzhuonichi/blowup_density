import NSFormalization.Section3.T10.PeriodicData
import NavierStokes.PeriodicUniqueness

/-!
# T24c unit Uc2 — the conservative-force potential pairing vanishes

This module proves `potential_pairing`, the first field of the reconciled
`ConservativeForcingAPI` (`research/T24/Spec.lean:1391-1406`,
`paper/sections/03-torus.tex:729-731`): for every viscosity `ν`, every positive
horizon `T`, every smooth unit-periodic potential `φ` and every classical torus
solution `S` from rest with conservative force `-∇φ`, the Haar pairing of `-∇φ`
against the divergence-free periodic velocity vanishes at every time of the
classical lifespan `[0, T)`:

`∫_{T³} ⟪-∇φ(t), S.velocity(t)⟫ ∂(Haar) = 0`.

The statement holds for *every* real `ν` (no positivity is used): it is a pure
torus integration-by-parts fact, not a uniqueness/energy consequence.  The proof
is: transport the Haar integral to the fundamental cube (`integral_torusLift`,
`Paper1/TorusCube.lean:40`), rewrite `⟪-∇φ, u⟫ = -⟪u, ∇φ⟫` (real inner-product
symmetry), and discharge `∫_{cube} ⟪u, ∇φ⟫ = 0` for the divergence-free periodic
`u` with the already-formalized periodic integration-by-parts lemma
`NavierStokes.PeriodicUniqueness.cubeIntegral_pressure_energy_zero`
(`vendor/NavierStokesAndEuler/NavierStokes/PeriodicUniqueness.lean:435`).

## Lane note (deduplication)

`PeriodicPotentialT` and `conservativeForceT` are the T24c vocabulary
(`research/T24/Spec.lean:1367-1372`).  Their canonical module
`Section3/T24/Conservative.lean` (lane 392) had not landed on this lane's base,
so both are restated here **verbatim** under the intended
`NSFormalization.Section3.T24` namespace.  The assembly lane (Uc3) should dedupe
against lane 392's copy.
-/

noncomputable section

namespace NSFormalization.Section3.T24

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NavierStokes.PeriodicIntegration (cubeIntegral cubeIntegral_neg UnitPeriods)
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField SpaceTimeScalar)
open NSFormalization.Section3.T10
open scoped ContDiff ENNReal BigOperators RealInnerProductSpace

/-- `03-torus.tex:723-726` (`research/T24/Spec.lean:1367-1369`, verbatim): the
conservative potential class — a globally defined smooth scalar `φ` on
spacetime, unit-periodic in every spatial coordinate. -/
def PeriodicPotentialT (φ : SpaceTimeScalar) : Prop :=
  ContDiff ℝ ∞ φ ∧ IsPeriodicOn univ φ

/-- `03-torus.tex:723-726` (`research/T24/Spec.lean:1371-1372`, verbatim): the
conservative force `f = -∇φ`, in the registered pressure-gradient token. -/
def conservativeForceT (φ : SpaceTimeScalar) : SpaceTimeField :=
  fun z ↦ -pressureGradient φ z.1 z.2

/-- `03-torus.tex:729-731` (`research/T24/Spec.lean:1391-1406`): the displayed
pairing `∫_{T³} f·u = -∫∇φ·u = 0` at every time of the classical lifespan, for
every smooth periodic `φ` and every solution `S` from rest with force `-∇φ`.

The conclusion holds for every real `ν`; only incompressibility and spatial
periodicity of `u` are used, via the torus integration-by-parts identity
`cubeIntegral_pressure_energy_zero`. -/
theorem potential_pairing :
    ∀ (ν : ℝ) (T : ℝ), 0 < T → ∀ φ : SpaceTimeScalar, PeriodicPotentialT φ →
      ∀ S : ClassicalSolutionT ν (0 : SpatialField) (conservativeForceT φ) T,
        ∀ t ∈ Ico (0 : ℝ) T,
          ∫ y : PeriodicTorus,
              torusLift (fun x : Space ↦
                (inner ℝ (conservativeForceT φ (t, x)) (S.velocity (t, x)) : ℝ))
                y ∂periodicTorusMeasure = 0 := by
  intro ν T _hT φ hφ S t ht
  -- Transport the Haar integral to the fundamental cube.
  rw [NSFormalization.Paper1.integral_torusLift]
  -- Spatial smoothness of the velocity slice at time `t`, from the slab regularity.
  have hw : ContDiff ℝ ∞ (fun x : Space ↦ S.velocity (t, x)) :=
    S.velocity_smooth.comp_contDiff (contDiff_const.prodMk contDiff_id)
      (fun x ↦ ⟨ht, mem_univ x⟩)
  -- Spatial smoothness of the potential slice at time `t`, from global smoothness.
  have hφx : ContDiff ℝ ∞ (fun x : Space ↦ φ (t, x)) :=
    hφ.1.comp (contDiff_const.prodMk contDiff_id)
  -- Unit spatial periods of both slices at time `t`.
  have hpw : UnitPeriods (fun x : Space ↦ S.velocity (t, x)) :=
    fun x i ↦ S.velocity_periodic t ht x i
  have hpφ : UnitPeriods (fun x : Space ↦ φ (t, x)) :=
    fun x i ↦ hφ.2 t (mem_univ t) x i
  -- Incompressibility of the velocity at time `t`.
  have hdiv : ∀ x : Space, spatialDivergence S.velocity t x = 0 := S.divergence t ht
  -- The pressure-pairing integration-by-parts identity: `∫_{cube} ⟪u, ∇φ⟫ = 0`.
  have key :
      cubeIntegral (fun x : Space ↦ (inner ℝ (S.velocity (t, x)) (pressureGradient φ t x) : ℝ)) = 0 :=
    NavierStokes.PeriodicUniqueness.cubeIntegral_pressure_energy_zero hw hφx hpw hpφ hdiv
  -- Rewrite `⟪-∇φ, u⟫ = -⟪u, ∇φ⟫`, then discharge the cube integral with `key`.
  have hfun :
      (fun x : Space ↦ (inner ℝ (conservativeForceT φ (t, x)) (S.velocity (t, x)) : ℝ)) =
        (fun x : Space ↦ -(inner ℝ (S.velocity (t, x)) (pressureGradient φ t x) : ℝ)) := by
    funext x
    have h1 : conservativeForceT φ (t, x) = -pressureGradient φ t x := rfl
    rw [h1, inner_neg_left, real_inner_comm (S.velocity (t, x)) (pressureGradient φ t x)]
  rw [hfun, cubeIntegral_neg, key, neg_zero]

end NSFormalization.Section3.T24
