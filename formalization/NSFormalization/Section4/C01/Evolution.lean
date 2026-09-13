import NSFormalization.Section4.C01.VelocityJets
import Euler.LpSmoothField
import Euler.MeanSolenoidalSpace
import Euler.OrdinaryPressureCancellation

/-!
# C01 unit U3 — evolution packaging of a classical solution as an `SmoothL2Field` path

Task `collaboration/tasks/C01.md`, node `C01`; this is unit **U3** of
`research/C01/COMPARISON.md:173`, the infrastructure U4 (`energyIdentity`,
`energyDifferentialBound`) and U7 (`enstrophyIdentity`) consume.

## Goal

Turn a classical whole-space solution `u : ClassicalSolutionR ν a f T`
(`Section4/A02/SolutionClass.lean:100`), restricted to a compact time slab
`[0,S] ⊂ [0,T)` (`S < T`), into a path

  `velocityField : Icc 0 S → EulerLpTranslation.SmoothL2Field Space`

(`vendor/NavierStokesAndEuler/Euler/LpSmoothField.lean:31`) together with the
lemmas the vendor energy machinery consumes.  **C01's actual U4/U7 consumers are
`EulerOrdinarySobolev.wordEnergy_hasDerivWithinAt` and `ordinaryWord_hasDerivWithinAt`
(`Euler/OrdinaryWordTime.lean:86,78`)**, whose hypothesis package is *only* jetLp
continuity of the path (`hA`), jetLp continuity of the derivative path (`hB`) and
the pointwise `HasDerivAt` in time (`hd`) — no `hK`, `hdiv`, `hW`, `hP`.
`OrdinaryViscousStability.difference_energy_bound` (`OrdinaryViscousStability.lean:71`)
is used only as a *shape witness* that this package is consumable; its extra
hypotheses (`hK`, `hdiv`, `hW`, `hP`, `hD`) are not what U4/U7 owe, and its `hD` is
the *unforced* estimate (see the time-derivative note below).

## What is proved here

* `velocityField` — the path, built slice-by-slice from unit **U1**
  (`velocity_slice_smoothL2`), well-defined because `t ≤ S < T` puts every
  `t ∈ [0,S]` in `[0,T)`.
* `velocityField_field` — its representative is literally the velocity slice.
* `velocityField_solenoidal` — `u(t)` lies in `EulerMeanSolenoidal.solenoidalSpace`
  (`Euler/MeanSolenoidalSpace.lean:58`), from the classical divergence-free clause
  `ClassicalSolutionR.divergence` via `smooth_mem_solenoidal`
  (`Euler/MeanSolenoidalSpace.lean:187`) and the divergence bridge
  `EulerSmoothLimit.divergence_eq_coordinate_sum`.
* `jetOfDatum_continuous` — the datum ⟹ jet reconstruction `D01.jetOfDatum m j hj`
  (`DatumToJets.lean:196`) is continuous in the datum (a composition of the CLM/CLE
  factors `Source.physicalJetLp`, `Paper3.sobolevOrderLowering`,
  `(Paper3.cyclesToAngular).symm`, the `L²`-subspace coercion and the `PiLp` component).
* `velocityField_jetLp_continuous` — **the jetLp-continuity clause `hA`/`hWc`**:
  `∀ n, Continuous (fun t : Icc 0 S => (velocityField t).jetLp n)`, from `sobolev`'s
  `ContinuousOn G_n (Ico 0 T)` conjunct (this is the first use in tree of that
  conjunct, which D01's contract discards) and `D01.jetOfDatum_ae` + `Lp.ext`.

So the two path-side hypotheses of the real consumer — `hW` (solenoidal) and `hA`
(jetLp continuity) — are closed here for the velocity.

## What is *not* closed here: one root gap (all-order jets of `∇p(t,·)`)

There is a **single** root gap, and the time-derivative clause reduces to it.

* **All-order jets of `∇p(t,·)`.**  Both `EulerOrdinarySobolev.gradient_mem`
  (`Euler/OrdinaryPressureCancellation.lean:84`, the `gradientSpace` consumer of the
  pressure inside the U4/U7 pressure cancellation) and the derivative field below need
  `∇p(t,·)` to be a full `SmoothL2Field` — all its Fréchet jets in `L²`, equivalently
  `SmoothSquareIntegrableJets (∇p(t,·))`.  The class carries only order-zero `MemLp` of
  `∇p` (`pressure_gradient`, `Data.lean:647`) and spatial smoothness of the slice
  (`D01.contDiff_pressureGradient_slice`), so `∇p(t,·)` is **not** *proved here* to be an
  `SmoothL2Field`.  This is **not** a hypothesis to add: it is a *theorem of the paper's
  class*, eq:Rpressure `∇p = (I−P)(f − ∇·(u⊗u))` (`02-preliminaries.tex:89-91`,
  elliptic form `Δp = div f − ∂ᵢ∂ⱼ(uᵢuⱼ)`), which `Data.lean:621-623` deliberately omits
  as a field and books as **D01 unit L9(c)** (`research/D01/RECONCILIATION.md:160`,
  `COMPARISON_A.md:105`): the Leray projection is bounded on every `H^m` and `u⊗u ∈ H^∞`
  by the `H^m` algebra (tame products, `Contracts/V1/TameProduct.lean`), so `∇p(t,·) ∈ H^∞`,
  hence the jets by `memHInfty_iff_smoothJets`.  L9(c) is **blocked on toolchain task U05**
  (its `L²`-level witnesses `MNS2.r3HelmholtzPressure_gradient` /`r3LerayComplementL2`,
  `vendor/HeliCorgi/Formal/R3HelmholtzPressure.lean:259,228`, are Lean 4.32.1).  Adding a
  V2 pressure-datum *class field* is rejected: it would make the Lean `ClassicalSolutionR`
  strictly stronger than the paper's class and move the burden onto whoever constructs a
  solution (prop:local).

* **Pointwise time-derivative `hTime`/`hd` (and the derivative path).**  *Not* an
  independent gap.  `ClassicalSolutionR.momentum` (`Data.lean:640`) pins the time derivative
  algebraically on `Ioo 0 T`: `∂_t u = f − (u·∇)u + νΔu − ∇p`; the `HasDerivAt` in time comes
  from `velocity_smooth`'s `ContDiffOn ℝ ∞ u (Ico 0 T ×ˢ univ)` (with `projIcc` bookkeeping),
  and jet-continuity of the summands `f`, `(u·∇)u`, `Δu` is within reach of `sobolev`'s
  `ContinuousOn` conjunct (now usable via `velocityField_jetLp_continuous`) plus tame products.
  The only summand not yet all-order `L²` is `∇p` — i.e. this clause reduces to the root gap
  above plus routine work.  **Force caveat for U4:** in the shape witness
  `difference_energy_bound`, `hD` with `U := 0`, `P := ∇p` forces
  `D = −(u·∇)u − ∇p + νΔu = ∂_t u − f` (by `momentum`), i.e. that estimate is the *unforced*
  one; a forced solution's derivative field is `∂_t u`, off by `f`.  Recorded so U4 does not
  inherit a `D` that drops the force.

Full detail, including the rejected approaches, is in `research/C01/ATTEMPTS_U1U3.md`.
-/

noncomputable section

namespace NSFormalization.Section4.C01

open Set MeasureTheory
open NavierStokes.ProblemStatement
open EulerLpTranslation EulerMeanSolenoidal
open NSFormalization.Paper3 NSFormalization.Source.FourierPhysicalJets
open scoped ContDiff ENNReal

variable {ν : ℝ} {a : A02.SpatialField} {f : A02.SpaceTimeField} {S T : ℝ}

/-- Every time of the compact slab `[0,S]` lies in the half-open lifespan `[0,T)`
when `S < T`. -/
theorem mem_Ico_of_mem_Icc (hST : S < T) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) S) :
    t ∈ Ico (0 : ℝ) T :=
  ⟨ht.1, lt_of_le_of_lt ht.2 hST⟩

/-- **C01 unit U3, the path.**  The velocity of a classical solution, over the
compact slab `[0,S] ⊂ [0,T)`, as a path of `EulerLpTranslation.SmoothL2Field Space`
(`Euler/LpSmoothField.lean:31`).  Each slice is an `SmoothL2Field` by unit U1. -/
def velocityField (u : A02.ClassicalSolutionR ν a f T) (hST : S < T)
    (t : Icc (0 : ℝ) S) : SmoothL2Field Space where
  field := fun x => u.velocity (t.1, x)
  smooth := (velocity_slice_smoothL2 u (mem_Ico_of_mem_Icc hST t.2)).1
  integrable := (velocity_slice_smoothL2 u (mem_Ico_of_mem_Icc hST t.2)).2

@[simp] theorem velocityField_field (u : A02.ClassicalSolutionR ν a f T) (hST : S < T)
    (t : Icc (0 : ℝ) S) :
    (velocityField u hST t).field = fun x => u.velocity (t.1, x) := rfl

/-- **C01 unit U3, the solenoidal clause `hW` of `difference_energy_bound`.**
Each velocity slice lies in the ordinary closed solenoidal `L²` subspace
(`Euler/MeanSolenoidalSpace.lean:58`), from `ClassicalSolutionR.divergence`. -/
theorem velocityField_solenoidal (u : A02.ClassicalSolutionR ν a f T) (hST : S < T)
    (t : Icc (0 : ℝ) S) :
    (velocityField u hST t).toLp ∈ solenoidalSpace := by
  have ht_ico : t.1 ∈ Ico (0 : ℝ) T := mem_Ico_of_mem_Icc hST t.2
  have hdiv : ∀ x, EulerSmoothLimit.divergence (velocityField u hST t).field x = 0 := by
    intro x
    rw [velocityField_field, EulerSmoothLimit.divergence_eq_coordinate_sum]
    simpa [spatialDivergence, spatialDerivative, coordinateVector]
      using u.divergence t.1 ht_ico x
  exact smooth_mem_solenoidal (velocityField u hST t).field
    (velocityField u hST t).smooth (velocityField u hST t).memLp hdiv

/-- The datum ⟹ jet reconstruction `D01.jetOfDatum m j hj` (`DatumToJets.lean:196`)
is continuous in the datum: it is `Source.physicalJetLp j` (a `ContinuousLinearMap`)
applied componentwise to `Paper3.sobolevOrderLowering` (a `→L[ℂ]`) of
`(Paper3.cyclesToAngular m).symm` (a `≃L[ℂ]`) of the `L²`-subspace coercion of the
`PiLp` component of the datum — every stage continuous. -/
theorem jetOfDatum_continuous (m j : ℕ) (hj : j ≤ m) :
    Continuous (fun A : RealVectorSobolev (m : ℝ) => D01.jetOfDatum m j hj A) := by
  simp only [D01.jetOfDatum, D01.loweredComponent, D01.cyclesComponentOfAngular]
  refine (physicalJetLp j).continuous.comp (continuous_pi fun i => ?_)
  exact (sobolevOrderLowering (m : ℝ) (j : ℝ) (by exact_mod_cast hj)).continuous.comp
    ((cyclesToAngular (m : ℝ)).symm.continuous.comp
      (continuous_subtype_val.comp (PiLp.continuous_apply 2 _ i)))

/-- **C01 unit U3, the `jetLp` continuity clause `hA`/`hWc`** (of
`wordEnergy_hasDerivWithinAt`, and of `difference_energy_bound` as shape witness).
Each order-`n` `L²` jet of the velocity path is continuous in time.

The order-`n` datum path `G_n` of `ClassicalSolutionR.sobolev` is `ContinuousOn`
on `[0,T)`; `jetOfDatum n n` reconstructs the order-`n` jet from it continuously
(`jetOfDatum_continuous`) and equals `jetLp n` as an `Lp` element by
`D01.jetOfDatum_ae`.  This closes the clause for the *velocity*; the pressure jets
(and, through them, the time-derivative field) remain — see the module header. -/
theorem velocityField_jetLp_continuous (u : A02.ClassicalSolutionR ν a f T)
    (hST : S < T) (n : ℕ) :
    Continuous (fun t : Icc (0 : ℝ) S => (velocityField u hST t).jetLp n) := by
  obtain ⟨G, hGc, hGd⟩ := u.sobolev n
  have hkey : (fun t : Icc (0 : ℝ) S => (velocityField u hST t).jetLp n)
      = fun t : Icc (0 : ℝ) S => D01.jetOfDatum n n (le_refl n) (G t.1) := by
    funext t
    have ht_ico : t.1 ∈ Ico (0 : ℝ) T := mem_Ico_of_mem_Icc hST t.2
    apply Lp.ext
    exact (((velocityField u hST t).integrable n).coeFn_toLp).trans
      (D01.jetOfDatum_ae (le_refl n) (velocityField u hST t).smooth (hGd t.1 ht_ico)).symm
  rw [hkey]
  exact (jetOfDatum_continuous n n (le_refl n)).comp
    (hGc.comp_continuous continuous_subtype_val fun t => mem_Ico_of_mem_Icc hST t.2)

end NSFormalization.Section4.C01
