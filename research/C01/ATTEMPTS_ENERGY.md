# ATTEMPTS — C01 energy/enstrophy split (lane 131)

> Revised after lane-131 review (`research/C01/REVIEW_ENERGY.md`) and the
> coordinator's correction (D01 P2 = L9(c) is proved+registered).

## What was proved

`formalization/NSFormalization/Section4/C01/EnergyIdentity.lean`, unit **E0**:
the exact-identity arithmetic core of eq:RL2, on a generic real inner product
space, the exact analogue of `A04.inner_energy_assembly` (`HighEnergy.lean:100`)
with the three pairing hypotheses entered as **equalities** so the conclusion is
the manuscript's exact identity rather than an inequality:

* `inner_energy_identity … : ½·d + ν·grad² = ⟪G,F⟫`
* `inner_energy_identity_deriv … : d = −2ν·grad² + 2·⟪G,F⟫`

from `hd : d = 2⟪G,Gt⟫`, `hmom : Gt = ν•L−N−P+F`, `hlap : ⟪G,L⟫ = −grad²`,
`hpr : ⟪G,P⟫ = 0`, `hnl : ⟪G,N⟫ = 0`.  Standard 3 axioms.  The review confirmed it
is **not** derivable from `inner_energy_assembly` (that lemma folds the force term
into `≤` by Cauchy–Schwarz), so it is a genuinely new lemma, and confirmed the
signs against concrete numbers (`/tmp/rev131/sign.lean`).

`inner_energy_identity_deriv`'s conclusion is exactly the derivative value of the
spec field `energyIdentity` (`Spec.lean:348-350`) once `grad² = gradientSq` and
`⟪G,F⟫ = pairing u f` are supplied (row E2 of `ENERGY_SPLIT.md`).  Generic over
`E`, it instantiates at the vendor jet carrier `Lp` (route B, recommended).

## Why E0 and not the full field / the nonlinear lemma / the bridge

The brief offered three candidates for the first S unit; the decision:

1. **Exact `m=0` energy identity in datum vocabulary** — the arithmetic core is
   provable and safe; the *full* field is not one S unit.  So I proved the
   arithmetic core E0, exactly as lane 128 proved `inner_energy_assembly` as the S
   core of eq:Rhigh and left the analytic inputs as hypotheses.
2. **The nonlinear-vanishing lemma `⟨(u·∇)u,u⟩=0`** — already exists:
   `advection_inner_zero` (`vendor/.../Euler/OrdinaryTransportCancellation.lean:42`),
   so proving it would duplicate the tree.
3. **The vocabulary bridge** — cheap only on carrier B (`Lp` inner = Bochner
   integral, `field_inner`, `OrdinaryL2Integration.lean:26`); it is a full **S–M**
   (row E2), not an S unit, and it depends on E1.  On carrier A it is itself a hard
   open item (order-0 Parseval, `OrderZeroDatum.lean:40-53`).

E0 unblocks the most because it is the one algebra step **both** the energy and
(with the nonlinear term kept, sibling E7) the enstrophy assemblies pass through,
and it is carrier-agnostic.

## Paths considered and rejected (decided from the tree)

* **Route A (datum carrier) for the energy identity.**  Rejected as the primary
  route.  The binding reason — **corrected after review** — is **not** the `2 ≤ m`
  on `A04.momentum_datum` (`MomentumDatum.lean:138`) / `timeDeriv_isSobolevDatum`:
  lane 124's `orderZeroDatumCLM` (`A01/DatumPathContinuity.lean:103`) commutes with
  differentiation, so a `2≤m`-free order-0 datum time-derivative route exists in
  principle.  The real block is the **order-0 Plancherel/Parseval bridge** between
  the datum norms and the spec's physical `l2Sq`/`gradientSq`/`pairing`, documented
  **open** in `D01/OrderZeroDatum.lean:40-53` (`orderZeroDatum` gives datum
  existence only).  `inner_datum_laplacian` (`:306`, exact) and `pressure_drop`
  (`:216`, with `exists_isSobolevDatum_zero_of_memLp`, **unconditional at `m=0`**)
  *are* available — but useless without the bridge.
* **Route B (vendor jet `SmoothL2Field`).**  Selected (matches `COMPARISON.md:31,37`
  U4/U7=**M**).  Every analytic input exists; the `Lp` inner product is a Bochner
  integral (`field_inner`, `OrdinaryL2Integration.lean:26`), so the bridge to the
  spec quantities needs **no Plancherel**.  Inputs: `advection_inner_zero`
  (nonlinear vanishing), `Source.OrdinaryViscousStability.laplacian_pairing:32`
  (exact dissipation, a **sum** of squares → 2-line `Real.sqrt` adapter),
  `field_directional_ibp` (`:33`), `wordEnergy_hasDerivWithinAt`
  (`OrdinaryWordTime.lean:87`, support-free time derivative), and the pressure
  lemma below.  Template: `OrdinaryEulerKineticEnergy.lean:17,26`.
* **Pressure on carrier B — corrected.**  The right lemma is
  `EulerOrdinarySobolev.gradient_pairing_zero` (`OrdinaryPressureCancellation.lean:98`,
  the exact `hpr` shape), **not** the `gradient_mem` (`:84`) my first draft cited.
  Its first argument needs `∇p(t,·)` as a full `SmoothL2Field` (all-order `L²`
  jets) = D01 unit **L9(c)**.  The review treated L9(c) as an open blocker; the
  coordinator corrected this: **L9(c) is P2, and P2 is PROVED and registered** —
  `D01.pressureGradient_slice_smoothSquareIntegrableJets_of_memForceR`
  (`PressureJets.lean:128`, registered `D01.datum_lemmas_v3`), which is
  field-for-field the `smooth`+`integrable` fields of `SmoothL2Field`, so `∇p(t,·)`
  packages in ≤10 lines (row Ep).  So `hpr` **is deliverable on carrier B today**;
  the recommended "parallel L9(c) lane" is unnecessary.
* **E4's derivative path — same P2 supply.**  `wordEnergy_hasDerivWithinAt`'s `hA`
  jet-continuity is `Evolution.velocityField_jetLp_continuous` (`:164`, done); its
  derivative path `B = ∂ₜu(r,·)` packages as `SmoothL2Field` via P2
  `D01.temporalDerivative_slice_smoothSquareIntegrableJets_of_memForceR`
  (`PressureJets.lean:150`), the pointwise `HasDerivAt` from `velocity_smooth`
  (unconditional), plus `B`'s jetLp continuity (routine).  So E4 has no open input
  either.
* **STALE NOTE flagged (do not edit).**  `Section4/C01/Evolution.lean:60-76` (and
  its `velocityField_jetLp_continuous` docstring `:160-163`) still describes the
  all-order jets of `∇p` / the time-derivative field as "a **single** root gap …
  blocked on toolchain task U05".  This is **out of date**: U05 is done
  (lanes 004/010, PR #8/#11) and P2 was proved 2026-09-14 (`PressureJets.lean`).
  Left unedited per the brief (frozen-adjacent, and outside this lane's scope);
  **flag for the next C01 simplifier pass** to refresh that header.
* **`linarith` for `inner_energy_identity_deriv` — my earlier negative example was
  WRONG; removed.**  A prior draft of this file claimed `linarith` fails because it
  "does not recognise `ν*grad^2` and `-2*ν*grad^2` as the same atom".  The reviewer
  refuted this (`/tmp/rev131/linarith.lean`, `linarith2.lean`, all `EXIT=0`):
  `linarith`'s preprocessing ring-normalizes, so those *are* the same monomial to
  it, and all three phrasings (`have h := …; linarith`, from-scratch
  `rw [hd, hexpand, hlap, hnl]; linarith`, and `linarith [h]`) close the goal.  The
  committed proof uses `linear_combination (2:ℝ) * inner_energy_identity …`, which
  is equally fine; the choice is stylistic, not a `linarith` blocker.  (Lesson: per
  `logs/LESSONS.md` 2026-09-14, a claimed compile-level blocker must be reproduced
  with a probe before it goes in the record — I recorded one that did not.)
* **Namespaces (confirmed correct by review `#check`).**  `laplacian_pairing` is
  `NSFormalization.Source.OrdinaryViscousStability.laplacian_pairing`;
  `field_directional_ibp` / `gradient_pairing_zero` / `wordEnergy_hasDerivWithinAt`
  are in `EulerOrdinarySobolev`, not `EulerLpTranslation`.

## Commands run

* `lake build NSFormalization.Section4.C01.EnergyIdentity` → `Built … (1945 jobs)`,
  success.
* `lake env lean …/C01/EnergyIdentity.lean` → exit 0, silent.
* `lake env lean research/C01/axioms_energy.lean` → both theorems
  `[propext, Classical.choice, Quot.sound]`.
* forbidden-token scan → none in the Lean module.
* `make check` → all four checks pass.

## What the next C01 contract version should register

**V2 of `EnergyAbsorptionAPI` need not change** (the statements are correct and
route-B-provable); the work is discharging fields, then registering them.  When
the assembly lands, register in this order (all on carrier B):

1. `energyIdentity`, `energyDifferentialBound`, `l2Bound` (eq:RL2 block) — need
   only the registered `velocityJets`, `Evolution.velocityField`, the P2 `∇p`
   packaging (`D01.datum_lemmas_v3`), E0, the E2 vocabulary bridge, and the small
   `sqrt_energy_le_primitive` generalization.
2. `enstrophyIdentity`, `enstrophyDifferentialBound`, `enstrophyIntegralBound`
   (eq:RH1 block) — reuse the **already-registered** `trilinearAbsorbed` and
   `laplacianSqENorm` in `enstrophyDifferentialBound` (its first consumer).
3. `sobolevTwoFourier`, then `h2TimeIntegral`, `h2TimeIntegralZeroDatum`.

`sobolevTwoFourier` is the one field forcing a **carrier crossing** (identify
`Source.vectorAngularSobolevNorm` with D01's `sobolevENorm 2`, the order-2 sibling
of the open order-0 Plancherel item) + de-compactification of
`vectorAngularSobolev_succ`.  Do **not** register any field until its discharging
theorem compiles with the standard 3 axioms and no `sorry`; E0 is the only piece
ready today.  Add a binding-layer `rfl`/`exact` bridge for E0's generic statement
only when it is consumed by a concrete carrier instance.

**Immediate next lane (reviewer recommendation): row E2** (`Section4/C01/Vocabulary.lean`,
S–M, ≈60–90 lines, no open input).  The recommended parallel D01 L9(c) lane is
**unnecessary** — P2 is done and registered.
