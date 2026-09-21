import NSFormalization.Section4.C01.EnergyIdentity
import NSFormalization.Source.OrdinaryViscousStability
import Euler.OrdinaryTransportCancellation
import Euler.OrdinaryPressureCancellation

/-!
# C01 unit E2: the carrier-B vocabulary bridge for the ordinary energy identity eq:RL2

Lane `136-C01-e2-vocabulary`, row **E2** of `research/C01/ENERGY_SPLIT.md`, graph
node `C01` (`formalization/blueprint/DEPENDENCY_GRAPH.md:275-281`).  The ordinary
energy identity eq:RL2 (`paper/sections/04-whole-space.tex:117`, spec field
`research/C01/Spec.lean:344` `energyIdentity`) is proved on **carrier B**, the
vendor jet carrier `EulerLpTranslation.SmoothL2Field` (physical `Lp`), whose inner
product is the Bochner integral `⟪A.toLp, B.toLp⟫ = ∫ x, ⟪A.field x, B.field x⟫`
(`EulerOrdinarySobolev.field_inner`, `Euler/OrdinaryL2Integration.lean:26`).  This
module is the **vocabulary bridge** between the spec's physical squared quantities
and that inner product, so that the arithmetic core `inner_energy_identity_deriv`
(`Section4/C01/EnergyIdentity.lean`) can be instantiated on carrier B and its
conclusion read as the spec's asserted derivative value.

## The three spec quantities (`research/C01/Spec.lean:167-196`)

For a spatial field `z : Space → Space` the draft spec defines, as plain Bochner
integrals,

* `l2Sq z      := ∫ x, ‖z x‖ ^ 2`                          (`Spec.lean:172`)
* `gradientSq z := ∫ x, ‖gradientTensor z x‖ ^ 2`          (`Spec.lean:185`)
* `pairing w z  := ∫ x, (inner ℝ (w x) (z x) : ℝ)`         (`Spec.lean:196`)

with `gradientTensor z x : WithLp 2 (Fin 3 → Space)` the Frobenius assembly of the
three coordinate derivatives (`Contracts/V1/GradientL6.lean:89`,
`Contracts/V1/Data.lean:453`, `coordinateVector i = axis i = EuclideanSpace.single i 1`).

## Why the statements are spelled with raw integrals, not the spec's names

`l2Sq`, `gradientSq`, `pairing` and `gradientTensor` all live in
`verification/Contracts/V1/*` (the `BlowupDensity.Contracts.V1` namespace).  This
module is a **`formalization/` module**, and `verification` *depends on*
`formalization` (`verification/lakefile.toml`), not the other way round — so those
names are **not importable here**.  The bridges below are therefore stated with the
raw integrands `∫ x, ‖A.field x‖ ^ 2`, `∫ x, ∑ i, ‖fderiv ℝ A.field x (axis i)‖ ^ 2`
and `∫ x, ⟪A.field x, B.field x⟫`, which are **definitionally** `l2Sq A.field`,
`gradientSq A.field` (see the next paragraph) and `pairing A.field B.field` when
`A.field = slice u t`.  Closing the last `= gradientSq` step requires the single
`PiLp.norm_sq_eq_of_L2` identity
`‖gradientTensor z x‖ ^ 2 = ∑ i, ‖fderiv ℝ z x (coordinateVector i)‖ ^ 2`
together with `coordinateVector = axis` and the `Data.spatialGradient = fderiv`
`rfl`-facts; every one of those is a `Contracts.V1` object, so that final rewrite is
a **one-line `verification`-side binding**, not provable here.  What this module
delivers is the entire carrier-B analysis (`field_inner`, the Frobenius reindex, the
`Real.sqrt` adapter and the E0 assembly); no Plancherel, no order hypothesis.

## What this module proves

* `l2Sq_eq_inner`  — `(E2a)` `∫ x, ‖A.field x‖ ^ 2 = ⟪A.toLp, A.toLp⟫`
  (`field_inner` + `real_inner_self_eq_norm_sq`).
* `norm_toLp_sq_eq_l2Sq` — the norm form `‖A.toLp‖ ^ 2 = ∫ x, ‖A.field x‖ ^ 2`
  that `energyDifferentialBound` needs (finding 8 of `research/C01/REVIEW_ENERGY.md`).
* `gradientSq_eq_sum` — `(E2b)`
  `∑ i, ‖(A.directionalField (axis i)).toLp‖ ^ 2 = ∫ x, ∑ i, ‖fderiv ℝ A.field x (axis i)‖ ^ 2`,
  the exact shape `laplacian_pairing` produces on the left.
* `sqrt_dirSum_sq` — the two-line `Real.sqrt` adapter (finding 4), so E0's `grad`
  can be `Real.sqrt (∑ …)` with `grad ^ 2 = ∑ …`.
* `pairing_eq_inner` — `(E2c)` `∫ x, ⟪A.field x, B.field x⟫ = ⟪A.toLp, B.toLp⟫`
  (verbatim `field_inner`).
* `energyIdentity_of_carrierB` — the demonstration that, from the five carrier-B
  inputs in their native shapes (`laplacian_pairing`, `advection_inner_zero`,
  `gradient_pairing_zero` with a packaged `∇p`, the derivative fact `d = 2⟪G, Gt⟫`
  and the momentum split), `inner_energy_identity_deriv` yields exactly the spec's
  asserted derivative value `-2ν·gradientSq + 2·pairing` (in raw-integral form) after
  rewriting with the three bridges.  The algebra closes.

No analysis obligation is left open: every ingredient is `#check`ed carrier-B lemma
plus real-inner-product arithmetic.
-/

noncomputable section

open MeasureTheory
open EulerLpTranslation EulerLpTranslation.SmoothL2Field EulerOrdinarySobolev EulerSmoothLimit
open NSFormalization.Source.OrdinaryViscousStability
open scoped RealInnerProductSpace ContDiff

namespace NSFormalization.Section4.C01

/-- The pointwise squared norm of a smooth `L²` field's representative is
integrable.  A `real_inner_self_eq_norm_sq` recast of
`EulerOrdinarySobolev.field_inner_integrable A A`. -/
theorem field_normSq_integrable (A : SmoothL2Field Space) :
    Integrable (fun x => ‖A.field x‖ ^ 2) volume :=
  (field_inner_integrable A A).congr
    (Filter.Eventually.of_forall fun x => real_inner_self_eq_norm_sq (A.field x))

/-- **E2a.** The spec's `l2Sq A.field = ∫ x, ‖A.field x‖ ^ 2` (`Spec.lean:172`) is the
carrier-B self inner product `⟪A.toLp, A.toLp⟫`.  Bridges the physical `L²` energy
to `field_inner` via `real_inner_self_eq_norm_sq`; no Plancherel. -/
theorem l2Sq_eq_inner (A : SmoothL2Field Space) :
    (∫ x, ‖A.field x‖ ^ 2) = ⟪A.toLp, A.toLp⟫ :=
  (integral_congr_ae
      (Filter.Eventually.of_forall fun x => (real_inner_self_eq_norm_sq (A.field x)).symm)).trans
    (field_inner A A).symm

/-- The norm form of `l2Sq_eq_inner`: `‖A.toLp‖ ^ 2 = ∫ x, ‖A.field x‖ ^ 2`, i.e.
`l2Norm (slice u t) = ‖(velocityField … t).toLp‖`.  This is the form
`energyDifferentialBound` consumes before Cauchy–Schwarz (finding 8 of
`research/C01/REVIEW_ENERGY.md`). -/
theorem norm_toLp_sq_eq_l2Sq (A : SmoothL2Field Space) :
    ‖A.toLp‖ ^ 2 = ∫ x, ‖A.field x‖ ^ 2 :=
  (real_inner_self_eq_norm_sq A.toLp).symm.trans (l2Sq_eq_inner A).symm

/-- **E2b.** The spec's `gradientSq A.field` (`Spec.lean:185`), in the Frobenius form
`∫ x, ∑ i, ‖∂ᵢ (A.field) x‖ ^ 2`, equals the sum of carrier-B directional `Lp`
norms — the **exact left-hand shape `laplacian_pairing` produces**
(`Source/OrdinaryViscousStability.lean:32`).  The identification of the integrand
`∑ i, ‖fderiv ℝ A.field x (axis i)‖ ^ 2` with `‖gradientTensor A.field x‖ ^ 2` (the
literal `Spec.gradientSq`) is the one remaining `PiLp.norm_sq_eq_of_L2` step, a
`verification`-side binding (`gradientTensor` is a `Contracts.V1` object; see the
module header). -/
theorem gradientSq_eq_sum (A : SmoothL2Field Space) :
    ∑ i : Fin 3, ‖(A.directionalField (axis i)).toLp‖ ^ 2
      = ∫ x, ∑ i : Fin 3, ‖fderiv ℝ A.field x (axis i)‖ ^ 2 := by
  have hterm : ∀ i : Fin 3,
      ‖(A.directionalField (axis i)).toLp‖ ^ 2
        = ∫ x, ‖fderiv ℝ A.field x (axis i)‖ ^ 2 := by
    intro i
    have h := norm_toLp_sq_eq_l2Sq (A.directionalField (axis i))
    simpa only [directionalField_field] using h
  have hInt : ∀ i : Fin 3, Integrable (fun x => ‖fderiv ℝ A.field x (axis i)‖ ^ 2) volume := by
    intro i
    have h := field_normSq_integrable (A.directionalField (axis i))
    simpa only [directionalField_field] using h
  rw [integral_finsetSum (Finset.univ : Finset (Fin 3)) (fun i _ => hInt i)]
  exact Finset.sum_congr rfl (fun i _ => hterm i)

/-- **The `Real.sqrt` adapter (finding 4).**  `laplacian_pairing` returns a *sum* of
squares `-∑ i, ‖(W.directionalField (axis i)).toLp‖ ^ 2`, whereas E0's dissipation
slot is `-grad ^ 2` for a single real `grad`.  Setting
`grad := Real.sqrt (∑ i, ‖…‖ ^ 2)` closes the gap: `grad ^ 2 = ∑ i, ‖…‖ ^ 2`. -/
theorem sqrt_dirSum_sq (A : SmoothL2Field Space) :
    Real.sqrt (∑ i : Fin 3, ‖(A.directionalField (axis i)).toLp‖ ^ 2) ^ 2
      = ∑ i : Fin 3, ‖(A.directionalField (axis i)).toLp‖ ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)

/-- **E2c.** The spec's `pairing A.field B.field = ∫ x, ⟪A.field x, B.field x⟫`
(`Spec.lean:196`) is verbatim the carrier-B inner product `⟪A.toLp, B.toLp⟫`
(`field_inner`, `Euler/OrdinaryL2Integration.lean:26`). -/
theorem pairing_eq_inner (A B : SmoothL2Field Space) :
    (∫ x, ⟪A.field x, B.field x⟫) = ⟪A.toLp, B.toLp⟫ :=
  (field_inner A B).symm

/-- **E2, the demonstration that the vocabulary bridge closes the eq:RL2 algebra.**

Given the five carrier-B inputs in their native shapes for the velocity `u`, force
`f`, time-derivative field `Gt` and packaged pressure gradient `P = ∇p(t,·)`:

* `hp`/`hgrad` : `P.field = ∇p` for a smooth potential `p` — the packaged `∇p`
  (row Ep of `ENERGY_SPLIT.md`, supplied by D01 P2);
* `hdiv`       : `u` is divergence free (`ClassicalSolutionR.divergence`,
  `Evolution.velocityField_solenoidal`);
* `hd`         : the D1 derivative `d = 2⟪u.toLp, Gt.toLp⟫` (row E4);
* `hmom`       : the momentum split `Gt = ν • Δu − (u·∇)u − ∇p + f` in `Lp` (row E3),

`inner_energy_identity_deriv` (`Section4/C01/EnergyIdentity.lean`) yields **exactly**
the spec's asserted derivative value (`energyIdentity`, `Spec.lean:348-350`),

`d = -2ν · gradientSq(u) + 2 · pairing(u, f)`,

written here in the raw-integral vocabulary (definitionally `gradientSq`/`pairing`;
see the module header).  The three cancellations are discharged by
`laplacian_pairing` (dissipation, through the `Real.sqrt` adapter),
`advection_inner_zero` (nonlinear, `⟪G, N⟫ = 0`) and `gradient_pairing_zero`
(pressure, `⟪G, P⟫ = 0`); the Frobenius reindex and the pairing are the E2 bridges. -/
theorem energyIdentity_of_carrierB
    {ν d : ℝ} (u f Gt P : SmoothL2Field Space) (p : Space → ℝ)
    (hp : ContDiff ℝ ∞ p) (hgrad : ∀ x, P.field x = gradient p x)
    (hdiv : ∀ x, divergence u.field x = 0)
    (hd : d = 2 * ⟪u.toLp, Gt.toLp⟫)
    (hmom : Gt.toLp
        = ν • (laplacianField u).toLp - (advectionField u u).toLp - P.toLp + f.toLp) :
    d = -2 * ν * (∫ x, ∑ i : Fin 3, ‖fderiv ℝ u.field x (axis i)‖ ^ 2)
          + 2 * (∫ x, ⟪u.field x, f.field x⟫) := by
  -- the dissipation slot, via the `Real.sqrt` adapter
  have hlap : ⟪u.toLp, (laplacianField u).toLp⟫
      = - Real.sqrt (∑ i : Fin 3, ‖(u.directionalField (axis i)).toLp‖ ^ 2) ^ 2 := by
    rw [sqrt_dirSum_sq u]; exact laplacian_pairing u
  -- the nonlinear cancellation `⟪G, N⟫ = 0`
  have hnl : ⟪u.toLp, (advectionField u u).toLp⟫ = 0 := by
    rw [real_inner_comm]; exact advection_inner_zero u u hdiv
  -- the pressure cancellation `⟪G, P⟫ = 0`
  have hpr : ⟪u.toLp, P.toLp⟫ = 0 := by
    rw [real_inner_comm]; exact gradient_pairing_zero P u p hp hgrad hdiv
  -- the E0 arithmetic core, with `grad := Real.sqrt (∑ …)`
  have hE := inner_energy_identity_deriv hd hmom hlap hpr hnl
  rw [hE, sqrt_dirSum_sq u, gradientSq_eq_sum u, ← pairing_eq_inner u f]

end NSFormalization.Section4.C01
