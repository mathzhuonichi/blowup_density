import NSFormalization.Section4.C01.Vocabulary
import NSFormalization.Section4.C01.Evolution
import NSFormalization.Section4.D01.PressureJets

/-!
# C01 units Ep / E3 (/ E4): the carrier-B inputs of the ordinary energy identity eq:RL2

Lane `143-C01-e3-e4-momentum`, rows **Ep**, **E3**, **E4** of
`research/C01/ENERGY_SPLIT.md`.  Companion of `Section4/C01/Vocabulary.lean` (row
E2, lane 136), whose `energyIdentity_of_carrierB` reduces the ordinary energy
identity (the unlabeled identity from which the `L²` bound eq:RL2,
`paper/sections/04-whole-space.tex:118-119`, follows) to five carrier-B inputs.
This module produces those inputs *for an actual classical whole-space solution*
`w : ClassicalSolutionR ν a f T` at an interior time `t ∈ Ioo 0 T`.

## What is packaged (row Ep)

Each of the four fields eq:RL2 pairs — the velocity `u`, its time derivative `∂ₜu`,
the pressure gradient `∇p` and the force `f` — is packaged, *at the fixed interior
time* `t`, as a `EulerLpTranslation.SmoothL2Field Space` (carrier B):

* `velocitySliceField` — `u(t,·)`, from `velocity_slice_smoothL2` (unit U1).
* `temporalSliceField` — `∂ₜu(t,·)`, from D01 P2
  `temporalDerivative_slice_smoothSquareIntegrableJets_of_memForceR`.
* `pressureGradientField` — `∇p(t,·)`, from D01 P2 (unit L9(c) = SL8)
  `pressureGradient_slice_smoothSquareIntegrableJets_of_memForceR` (**row Ep**).
* `forceSliceField` — `f(t,·)`, from `forceSlice_smoothL2_of_memForceR`.

All four `_field` lemmas are `rfl`.  With them come the exact hypotheses
`energyIdentity_of_carrierB` consumes: `hp`/`hgrad` (the pressure is a smooth
gradient, `pressureGradientField_eq_gradient` + `contDiff_pressureSlice`) and
`hdiv` (`u` is divergence free, `velocitySliceField_divergence`).

## The momentum split in `Lp` (row E3)

`momentum_split_toLp` pushes `ClassicalSolutionR.momentum` (eq:NS pointwise,
rearranged by `D01.temporalDerivative_slice_eq` to `∂ₜu = f − (u·∇)u + νΔu − ∇p`)
through `toLp` into the exact `hmom` shape

  `(∂ₜu).toLp = ν • (Δu).toLp − ((u·∇)u).toLp − (∇p).toLp + f.toLp`,

where `Δu`/`(u·∇)u` are the vendor carrier-B fields `laplacianField`/`advectionField`
of `u`.  The identification of those vendor fields with the manuscript operators
`spatialLaplacian`/`advection` is `advectionField_of_velocitySlice` (`rfl`) and
`laplacianField_of_velocitySlice` (`vector_laplacian_eq_sum`); the pushforward is a
`Lp.ext` a.e. computation.

## The energy-identity payoff (rows E4 / energyIdentity)

`energyIdentity_classical` assembles Ep + E3 + `hdiv`/`hgrad`/`hp` and reduces the
classical energy identity to the single derivative-value fact `d = 2⟪u, ∂ₜu⟫_{L²}`
(**row E4**): given that fact it yields eq:RL2's asserted derivative value
`d = −2ν·gradientSq(u) + 2·pairing(u,f)` (raw-integral form: `pairing` is definitionally
the spec's, `gradientSq` needs the one-line `PiLp.norm_sq_eq_of_L2` bridge — see
`Vocabulary.lean` and `research/C01/REVIEW_E3E4.md`).

**Row E4 (the derivative-value fact) is not closed here — see the module footer and
`research/C01/ATTEMPTS_E3E4.md`.**  The clean route
(`EulerOrdinarySobolev.wordEnergy_hasDerivWithinAt` at order `0`) requires its
derivative-path hypothesis `hB : ∀ n, Continuous (fun s => (B s).jetLp n)`, the
**time-continuity of the `∂ₜu(s,·)` `L²` jets**.  That reduces (via the momentum
split) to the **time-continuity of the `∇p(s,·)` `L²` jets**, which the class does
**not** provide: `ClassicalSolutionR.sobolev` gives a continuous-in-time datum path
for the *velocity* (this is `Evolution.velocityField_jetLp_continuous`, the `hA`),
and `MemForceR` gives one for the *force*, but the pressure carries only the
pointwise `pressure_gradient : ∀ t, MemLp (∇p(t,·)) 2`.  D01 **P2** is
pointwise-in-time (`SmoothSquareIntegrableJets (∇p(t,·))` at each fixed interior
`t`), so it does **not** supply the missing continuity.  This corrects the
`ENERGY_SPLIT.md` E4 note "B's jetLp continuity (routine) … the `∂ₜu` packaging is
P2": the packaging is P2 but the *time-continuity* is a separate, unmet obligation.
-/

noncomputable section

open Set MeasureTheory
open EulerLpTranslation EulerLpTranslation.SmoothL2Field EulerOrdinarySobolev EulerSmoothLimit
open NSFormalization.Source.OrdinaryViscousStability
open NavierStokes.ProblemStatement (temporalDerivative advection spatialLaplacian
  pressureGradient coordinateVector spatialDivergence spatialDerivative VelocityField
  PressureField)
open scoped RealInnerProductSpace ContDiff

namespace NSFormalization.Section4.C01

open NSFormalization.Section4.A02 (ClassicalSolutionR MemForceR)

variable {ν : ℝ} {a : A02.SpatialField} {f : A02.SpaceTimeField} {T : ℝ}

/-! ## Row Ep — the four carrier-B slice fields at an interior time -/

/-- **U1 packaging.**  The velocity slice `u(t,·)` as a carrier-B `SmoothL2Field`,
from `velocity_slice_smoothL2`. -/
def velocitySliceField (w : ClassicalSolutionR ν a f T) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) :
    SmoothL2Field Space where
  field := fun x => w.velocity (t, x)
  smooth := (velocity_slice_smoothL2 w ht).1
  integrable := (velocity_slice_smoothL2 w ht).2

@[simp] theorem velocitySliceField_field (w : ClassicalSolutionR ν a f T) {t : ℝ}
    (ht : t ∈ Ico (0 : ℝ) T) :
    (velocitySliceField w ht).field = fun x => w.velocity (t, x) := rfl

/-- **Row Ep.**  The pressure-gradient slice `∇p(t,·)` as a carrier-B `SmoothL2Field`,
from D01 unit L9(c) = P2
(`pressureGradient_slice_smoothSquareIntegrableJets_of_memForceR`), unconditional at
`t ∈ Ioo 0 T`. -/
def pressureGradientField (w : ClassicalSolutionR ν a f T) (hf : MemForceR f)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) : SmoothL2Field Space where
  field := fun x => pressureGradient w.pressure t x
  smooth := (D01.pressureGradient_slice_smoothSquareIntegrableJets_of_memForceR w hf ht).1
  integrable := (D01.pressureGradient_slice_smoothSquareIntegrableJets_of_memForceR w hf ht).2

@[simp] theorem pressureGradientField_field (w : ClassicalSolutionR ν a f T) (hf : MemForceR f)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    (pressureGradientField w hf ht).field = fun x => pressureGradient w.pressure t x := rfl

/-- **Corollary of P2.**  The time-derivative slice `∂ₜu(t,·)` as a carrier-B
`SmoothL2Field`, from `temporalDerivative_slice_smoothSquareIntegrableJets_of_memForceR`. -/
def temporalSliceField (w : ClassicalSolutionR ν a f T) (hf : MemForceR f)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) : SmoothL2Field Space where
  field := fun x => temporalDerivative w.velocity t x
  smooth := (D01.temporalDerivative_slice_smoothSquareIntegrableJets_of_memForceR w hf ht).1
  integrable := (D01.temporalDerivative_slice_smoothSquareIntegrableJets_of_memForceR w hf ht).2

@[simp] theorem temporalSliceField_field (w : ClassicalSolutionR ν a f T) (hf : MemForceR f)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    (temporalSliceField w hf ht).field = fun x => temporalDerivative w.velocity t x := rfl

/-- The force slice `f(t,·)` as a carrier-B `SmoothL2Field`, from
`forceSlice_smoothL2_of_memForceR`. -/
def forceSliceField (hf : MemForceR f) {t : ℝ} (ht : (0 : ℝ) ≤ t) : SmoothL2Field Space where
  field := fun x => f (t, x)
  smooth := (D01.forceSlice_smoothL2_of_memForceR hf ht).1
  integrable := (D01.forceSlice_smoothL2_of_memForceR hf ht).2

@[simp] theorem forceSliceField_field (hf : MemForceR f) {t : ℝ} (ht : (0 : ℝ) ≤ t) :
    (forceSliceField (f := f) hf ht).field = fun x => f (t, x) := rfl

/-! ## Row Ep — the `gradient_pairing_zero`-ready facts (`hp`, `hgrad`) and `hdiv` -/

/-- `hp`.  The scalar pressure slice `p(t,·)` is `C^∞`. -/
theorem contDiff_pressureSlice (w : ClassicalSolutionR ν a f T) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    ContDiff ℝ ∞ (fun z : Space => w.pressure (t, z)) :=
  D01.contDiff_slice_scalar w.pressure_smooth ⟨le_of_lt ht.1, ht.2⟩

/-- `hgrad`.  The packaged `∇p(t,·)` is pointwise the Euclidean `gradient` of the
scalar pressure slice: `(pressureGradientField …).field x = gradient (p(t,·)) x`.
Coordinatewise, `pressureGradient_apply` gives the left side as
`fderiv (p(t,·)) x (eᵢ)` and `gradient_coordinate` the right, and both are
`partialDerivative`. -/
theorem pressureGradientField_eq_gradient (w : ClassicalSolutionR ν a f T) (hf : MemForceR f)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) (x : Space) :
    (pressureGradientField w hf ht).field x = gradient (fun z : Space => w.pressure (t, z)) x := by
  rw [pressureGradientField_field]
  apply PiLp.ext
  intro i
  rw [D01.pressureGradient_apply w.pressure t x i, EulerMeanHarmonic.gradient_coordinate]
  rfl

/-- `hdiv`.  The velocity slice `u(t,·)` is divergence free, from
`ClassicalSolutionR.divergence`.  Mirrors the internal `hdiv` of
`Evolution.velocityField_solenoidal`. -/
theorem velocitySliceField_divergence (w : ClassicalSolutionR ν a f T) {t : ℝ}
    (ht : t ∈ Ico (0 : ℝ) T) (x : Space) :
    divergence (velocitySliceField w ht).field x = 0 := by
  rw [velocitySliceField_field, EulerSmoothLimit.divergence_eq_coordinate_sum]
  simpa [spatialDivergence, spatialDerivative, coordinateVector] using w.divergence t ht x

/-! ## Row E3 — the vendor carrier-B fields of `u` are the manuscript operators -/

/-- The vendor advection field `(u·∇)u` of the velocity slice is the manuscript
`advection`: `(advectionField u u).field x = advection u t x`.  `rfl` after
`advectionField_field` (both are `fderiv u(t,·) x (u(t,x))`). -/
theorem advectionField_velocitySlice_field (w : ClassicalSolutionR ν a f T) {t : ℝ}
    (ht : t ∈ Ico (0 : ℝ) T) (x : Space) :
    (advectionField (velocitySliceField w ht) (velocitySliceField w ht)).field x
      = advection w.velocity t x := by
  rw [advectionField_field]
  rfl

/-- The vendor Laplacian field `Δu` of the velocity slice is the manuscript
`spatialLaplacian`: `(laplacianField u).field x = spatialLaplacian u t x`.  From
`laplacianField_field` (`= Δ u.field`) and `vector_laplacian_eq_sum`, both being the
coordinate sum `∑ᵢ ∂ᵢ∂ᵢ`. -/
theorem laplacianField_velocitySlice_field (w : ClassicalSolutionR ν a f T) {t : ℝ}
    (ht : t ∈ Ico (0 : ℝ) T) (x : Space) :
    (laplacianField (velocitySliceField w ht)).field x = spatialLaplacian w.velocity t x := by
  have hcd : ContDiff ℝ ∞ (velocitySliceField w ht).field := (velocitySliceField w ht).smooth
  rw [laplacianField_field,
    congrFun (EulerMeanVectorIdentities.vector_laplacian_eq_sum (velocitySliceField w ht).field hcd) x]
  rfl

/-- **Row E3.**  The momentum equation of `w` at the interior time `t`, pushed to
`Lp`: the time-derivative slice equals the carrier-B combination
`ν • Δu − (u·∇)u − ∇p + f`.  From `ClassicalSolutionR.momentum` (rearranged to
`∂ₜu = f − (u·∇)u + νΔu − ∇p` by `D01.temporalDerivative_slice_eq`) pushed through
`toLp` by `Lp.ext` and the `coeFn` `Lp`-arithmetic lemmas, with the two field
bridges above. -/
theorem momentum_split_toLp (w : ClassicalSolutionR ν a f T) (hf : MemForceR f)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    (temporalSliceField w hf ht).toLp
      = ν • (laplacianField (velocitySliceField w (Ioo_subset_Ico_self ht))).toLp
          - (advectionField (velocitySliceField w (Ioo_subset_Ico_self ht))
              (velocitySliceField w (Ioo_subset_Ico_self ht))).toLp
          - (pressureGradientField w hf ht).toLp
          + (forceSliceField hf (le_of_lt ht.1)).toLp := by
  apply Lp.ext
  filter_upwards [(temporalSliceField w hf ht).toLp_ae,
    Lp.coeFn_add (ν • (laplacianField (velocitySliceField w (Ioo_subset_Ico_self ht))).toLp
        - (advectionField (velocitySliceField w (Ioo_subset_Ico_self ht))
            (velocitySliceField w (Ioo_subset_Ico_self ht))).toLp
        - (pressureGradientField w hf ht).toLp) (forceSliceField hf (le_of_lt ht.1)).toLp,
    Lp.coeFn_sub (ν • (laplacianField (velocitySliceField w (Ioo_subset_Ico_self ht))).toLp
        - (advectionField (velocitySliceField w (Ioo_subset_Ico_self ht))
            (velocitySliceField w (Ioo_subset_Ico_self ht))).toLp)
      (pressureGradientField w hf ht).toLp,
    Lp.coeFn_sub (ν • (laplacianField (velocitySliceField w (Ioo_subset_Ico_self ht))).toLp)
      (advectionField (velocitySliceField w (Ioo_subset_Ico_self ht))
        (velocitySliceField w (Ioo_subset_Ico_self ht))).toLp,
    Lp.coeFn_smul ν (laplacianField (velocitySliceField w (Ioo_subset_Ico_self ht))).toLp,
    (laplacianField (velocitySliceField w (Ioo_subset_Ico_self ht))).toLp_ae,
    (advectionField (velocitySliceField w (Ioo_subset_Ico_self ht))
      (velocitySliceField w (Ioo_subset_Ico_self ht))).toLp_ae,
    (pressureGradientField w hf ht).toLp_ae,
    (forceSliceField hf (le_of_lt ht.1)).toLp_ae]
    with x htemp hadd hsub2 hsub1 hsmul hlap hadv hpr hforce
  rw [htemp, hadd, Pi.add_apply, hsub2, Pi.sub_apply, hsub1, Pi.sub_apply, hsmul,
    Pi.smul_apply, hlap, hadv, hpr, hforce,
    laplacianField_velocitySlice_field w (Ioo_subset_Ico_self ht) x,
    advectionField_velocitySlice_field w (Ioo_subset_Ico_self ht) x]
  simp only [temporalSliceField_field, pressureGradientField_field, forceSliceField_field]
  rw [D01.temporalDerivative_slice_eq w ht x]
  abel

/-! ## The eq:RL2 payoff (row `energyIdentity`), modulo row E4 -/

/-- **eq:RL2's asserted derivative value for a classical solution, modulo row E4.**
For `w : ClassicalSolutionR ν a f T`, real admissible force `hf`, and interior time
`t ∈ Ioo 0 T`, *given the row-E4 derivative-value fact*
`hd : d = 2⟪u(t,·), ∂ₜu(t,·)⟫_{L²}`, the value `d` is the ordinary energy identity's
asserted derivative

  `d = −2ν · gradientSq(u(t,·)) + 2 · pairing(u(t,·), f(t,·))`

written in the raw-integral vocabulary (`pairing` is definitionally the spec's on the
carrier's `.field`; `gradientSq` differs by `PiLp.norm_sq_eq_of_L2`; see `Vocabulary.lean`).  This assembles the row-Ep facts
(`pressureGradientField_eq_gradient`, `contDiff_pressureSlice`), the row-E3 momentum
split (`momentum_split_toLp`) and `hdiv` (`velocitySliceField_divergence`) into
`energyIdentity_of_carrierB`.

Row E4 — that the energy `s ↦ ‖u(s,·)‖²_{L²}` is differentiable at `t` with derivative
`2⟪u,∂ₜu⟫` — is the **single remaining input** and is **not** closed in tree; see the
module footer for the precise blocker (time-continuity of the `∂ₜu` `L²` jets). -/
theorem energyIdentity_classical (w : ClassicalSolutionR ν a f T) (hf : MemForceR f)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) {d : ℝ}
    (hd : d = 2 * ⟪(velocitySliceField w (Ioo_subset_Ico_self ht)).toLp,
                  (temporalSliceField w hf ht).toLp⟫) :
    d = -2 * ν * (∫ x, ∑ i : Fin 3,
            ‖fderiv ℝ (velocitySliceField w (Ioo_subset_Ico_self ht)).field x (axis i)‖ ^ 2)
          + 2 * (∫ x, ⟪(velocitySliceField w (Ioo_subset_Ico_self ht)).field x,
                       (forceSliceField hf (le_of_lt ht.1)).field x⟫) :=
  energyIdentity_of_carrierB
    (velocitySliceField w (Ioo_subset_Ico_self ht))
    (forceSliceField hf (le_of_lt ht.1))
    (temporalSliceField w hf ht)
    (pressureGradientField w hf ht)
    (fun z => w.pressure (t, z))
    (contDiff_pressureSlice w ht)
    (pressureGradientField_eq_gradient w hf ht)
    (velocitySliceField_divergence w (Ioo_subset_Ico_self ht))
    hd
    (momentum_split_toLp w hf ht)

end NSFormalization.Section4.C01
