# C01 energy/enstrophy split — from the A04 assembly to the four remaining C01 fields

Lane `131-C01-energy-split`.  Target: the four `EnergyAbsorptionAPI`
(`research/C01/Spec.lean`) fields still out of scope of the registered
`Contracts/V1/EnergyAbsorptionPartial.lean` — `energyIdentity` (:344),
`energyDifferentialBound` (:364), `l2Bound` (:383), `enstrophyIdentity` (:487)
— and, following them, `enstrophyDifferentialBound` (:510),
`enstrophyIntegralBound` (:532), `sobolevTwoFourier` (:555), `h2TimeIntegral`
(:576), `h2TimeIntegralZeroDatum` (:599).

> Revised after lane-131 review (`research/C01/REVIEW_ENERGY.md`,
> ACCEPT-WITH-NOTES) and the coordinator's correction that **D01 unit L9(c) = P2
> is proved and registered** — the review's finding 5 (which treated the
> all-order jets of `∇p` as an open blocker) is itself out of date.

## 0. The central finding: two carriers, and the SPEC lives on the second

The paper obtains eq:RL2 (energy) and eq:RH1 (enstrophy) as the `m=0`/`m=1`
cousins of eq:Rhigh (`m≥3`, proved in `Section4/A04/EnergyIdentityHigh.lean`):
pair the momentum equation with `u` in `L²`/`H¹`, drop the pressure by
solenoidality, get `−ν‖∇u‖²` (`−ν‖Δu‖²`) from the Laplacian, kill (energy) or
bound (enstrophy) the nonlinear term.  Two Lean carriers can run this; the choice
is the whole story.

**Carrier A — the A04 datum carrier `RealVectorSobolev (m:ℝ)`** (Fourier model),
the carrier eq:Rhigh uses.  Several of its assembly lemmas work at order 0/1:
* `A04.inner_datum_laplacian` (`LaplacianAssembly.lean:306`) — the dissipation is
  an **exact equality** `⟪G, L⟫ = −∑ⱼ‖DⱼA'‖²`, `#check`ed with **no order
  hypothesis** (data at `m`, `m+1`, `m+2`; at `m=0` that is 0,1,2); `_le'` (`:353`)
  is its `≤` consumer form (already in E0's `−grad²` shape, cf. row E2/finding 4).
* `A04.pressure_drop` (`PressureDrop.lean:216`) — `⟪G, P⟫ = 0`, `#check`ed with
  **no order hypothesis**; with `D01.exists_isSobolevDatum_zero_of_memLp` (needs
  only `MemLp z 2`, supplied by `ClassicalSolutionR.pressure_gradient`) the
  **pressure term on carrier A is unconditional at `m=0`**.

**Why carrier A is nonetheless not the route — corrected reason.**  The block is
**not** the `2 ≤ m` on `A04.momentum_datum` (`MomentumDatum.lean:138`) /
`timeDeriv_isSobolevDatum`.  Lane 124's `orderZeroDatumCLM`
(`A01/DatumPathContinuity.lean:103`, a CLM `L² →L[ℝ] RealVectorSobolev 0`)
commutes with differentiation, so the order-0 datum time-derivative needs no
bounded representative — what it needs instead is `HasDerivAt` of the velocity
path **in `L²`**, a different but equally real analytic obligation.  The true,
structural block is the **order-0 Plancherel/Parseval bridge** between the datum
norms and the spec's physical quantities: `sobolevENorm 0 z ↔ l2Sq z`,
`⟪·,·⟫_{H⁰} ↔ pairing`, and `gradientSobolevNormAt 0 ↔ gradientSq`, all
**documented open** in `D01/OrderZeroDatum.lean:40-53` ("The Plancherel **norm
identity** `‖orderZeroDatum hz‖ = ‖z‖_{L²}` … is deliberately **not** proved here
… needing two pieces absent from the tree").  `orderZeroDatum` /
`exists_isSobolevDatum_zero_of_memLp` give datum **existence** only.  So the
conclusion (carrier A is not the route) stands, but a later lane must **not**
"unblock `momentum_datum` at `m=0`" and think carrier A has opened — the missing
piece is the Plancherel/Parseval bridge, not the order hypothesis.

**Carrier B — the vendor jet carrier `EulerLpTranslation.SmoothL2Field`**
(physical `Lp`).  `research/C01/COMPARISON.md:31,37` already selected this route
(U4/U7=**M**).  Its inner product is a **Bochner integral**, not a Fourier norm:
`⟪A.toLp, B.toLp⟫_ℝ = ∫ x, ⟪A.field x, B.field x⟫_ℝ`
(`EulerOrdinarySobolev.field_inner`, `vendor/.../Euler/OrdinaryL2Integration.lean:26`).
So it matches the spec's `pairing`/`l2Sq`/`gradientSq` **up to
`real_inner_self_eq_norm_sq` and a Frobenius `ℓ²` reindex — no Plancherel** (row
E2).  Every analytic ingredient exists on carrier B, and **the pressure ingredient
that the review thought was blocked is in fact supplied by the registered D01 P2**:

* nonlinear vanishing `⟨(u·∇)u, u⟩ = 0`:
  `advection_inner_zero (A B : SmoothL2Field) (hdiv : divergence A = 0) :
  ⟪(advectionField A B).toLp, B.toLp⟫_ℝ = 0`
  (`vendor/.../Euler/OrdinaryTransportCancellation.lean:42`), applied at `A=B=u`;
  `hdiv` = `Evolution.velocityField_solenoidal` — verified.
* exact dissipation `⟨u, Δu⟩ = −∑ᵢ‖∂ᵢu‖²`:
  `OrdinaryViscousStability.laplacian_pairing`
  (`formalization/NSFormalization/Source/OrdinaryViscousStability.lean:32`) — a
  **sum** of squares, so E0's `−grad²` slot needs `grad := Real.sqrt (∑ᵢ‖…‖²)`
  and a 2-line `Real.sq_sqrt`/`sq_sqrt` adapter (finding 4).
* spatial IBP `∫⟨∂ᵢA, B⟩ = −∫⟨A, ∂ᵢB⟩`:
  `EulerOrdinarySobolev.field_directional_ibp` (`OrdinaryL2Integration.lean:33`).
* time derivative `d/dt ∑_{n≤s}∑_w‖∂^w u‖² = 2∑⟨∂^w u, ∂^w ∂ₜu⟩`:
  `EulerOrdinarySobolev.wordEnergy_hasDerivWithinAt` (`OrdinaryWordTime.lean:87`),
  jet, support-free (takes a **value/derivative path pair** + jet-continuity +
  pointwise `HasDerivAt`; see E4).
* **pressure `⟨u, ∇p⟩ = 0`** — `EulerOrdinarySobolev.gradient_pairing_zero`
  (`OrdinaryPressureCancellation.lean:98`, `#check`ed), the exact `hpr` shape:
  `(A U : SmoothL2Field) (p) (hp : ContDiff ⊤ p) (hgrad : A.field = gradient p)
  (hdiv : divergence U = 0) : ⟪A.toLp, U.toLp⟫_ℝ = 0`.  **Its first argument needs
  `∇p(t,·)` as a full `SmoothL2Field` (all-order `L²` jets) = D01 unit L9(c) — and
  that is P2, which is PROVED and registered** (row Ep below); the review's "root
  gap" is closed.  The vendor's own kinetic-energy identity assembles exactly this
  way for the unforced inviscid case (template
  `OrdinaryEulerKineticEnergy.velocity_derivative_inner_zero:17`,
  `kineticEnergy_hasDerivWithinAt:26`).

**Consequence.**  The energy fields are assemblable **entirely on carrier B with
no open input** now that P2 supplies the `∇p` packaging; carrier A is a dead end
at order 0/1 (open Plancherel/Parseval bridge).  The spec's
`l2Sq`/`gradientSq`/`pairing` are physical Bochner integrals **by design**
(`Spec.lean:98-113`), so carrier B is the natural fit.

## 1. Bounded sub-lemmas (all on carrier B unless noted)

Sizes: **S** ≤ ~40 lines, no open input; **M** ~40–120 lines or one new IBP;
**L** a genuine analysis obligation.  `file:line` inputs are `#check`ed unless
marked (paper-only).

| # | lemma (Lean-ready shape) | size | inputs (`file:line`) | status / blocker |
|---|---|---|---|---|
| **E0** | `inner_energy_identity {E} … : ½·d + ν·grad² = ⟪G,F⟫` and `_deriv : d = −2ν·grad² + 2⟪G,F⟫`, from `hd:d=2⟪G,Gt⟫`, `hmom:Gt=ν•L−N−P+F`, `hlap:⟪G,L⟫=−grad²`, `hpr:⟪G,P⟫=0`, `hnl:⟪G,N⟫=0` | **S** | pure inner-product algebra (mirror of `A04.inner_energy_assembly`, `HighEnergy.lean:100`) | **PROVED this lane** (`Section4/C01/EnergyIdentity.lean`, standard 3 axioms). Carrier-agnostic; instantiates at `E = Lp` (carrier B). Cannot be derived *from* `inner_energy_assembly` (that folds the force term with Cauchy–Schwarz into `≤`), so it is a genuinely new lemma. |
| E1 | consume `Evolution.velocityField` as the `SmoothL2Field` **path** `Icc 0 S → SmoothL2Field` | **done** | `C01.Evolution.velocityField` (`:115`), `velocityField_field` (`:123`, `@[simp]`), `velocityField_solenoidal` (`:130`, the `hdiv` of `advection_inner_zero`/`gradient_pairing_zero`) | **essentially done** — U3 (`Section4/C01/Evolution.lean`, on integration) already proves the path and its representative/solenoidal facts. No new work beyond `#check`. |
| **Ep** | package `∇p(t,·) : SmoothL2Field` (`⟨fun x => pressureGradient p t x, ·, ·⟩`) | **S** (≤10 lines) | **P2**: `D01.pressureGradient_slice_smoothSquareIntegrableJets_of_memForceR` (`PressureJets.lean:128`, registered `D01.datum_lemmas_v3`), which is field-for-field the `smooth`+`integrable` fields of `SmoothL2Field`; plus `pressureGradient p t = gradient (p t)` for `gradient_pairing_zero`'s `hgrad` | **DONE (lane 143, `Section4/C01/MomentumCarrierB.lean`, std 3 axioms).** `pressureGradientField` (`+_field` `rfl`), with `pressureGradientField_eq_gradient` (`hgrad`, via `pressureGradient_apply`+`gradient_coordinate`) and `contDiff_pressureSlice` (`hp`); the sibling packagings `velocitySliceField`/`temporalSliceField`/`forceSliceField` land alongside. `hdiv` = `velocitySliceField_divergence`. Feeds `hpr` via `gradient_pairing_zero`. |
| E2 | Lp↔spec vocabulary (three eqns): (E2a) `‖A.toLp‖² = l2Sq A.field` (for `s` in a nbhd of `t`); (E2b) `∑ᵢ‖(A.directionalField (axis i)).toLp‖² = gradientSq A.field`; (E2c) `⟪A.toLp,B.toLp⟫ = pairing A.field B.field` | **S–M** | `field_inner` (`OrdinaryL2Integration.lean:26`); `real_inner_self_eq_norm_sq`; `PiLp.norm_sq_eq_of_L2` on `WithLp 2 (Fin 3 → Space)`; `directionalField_field … = fderiv ℝ A.field x v` (`LpSmoothFieldAlgebra.lean:97-98`, `rfl`); `coordinateVector i = axis i = EuclideanSpace.single i 1` (`ProblemStatement.lean:39`, `OrdinarySmoothWords.lean:17`); `gradientTensor = Data.spatialGradient ∘ lift` (`GradientL6.lean:89`, `Data.lean:453`) | **PROVED (lane 136, `Section4/C01/Vocabulary.lean`, std 3 axioms).** `l2Sq_eq_inner` (E2a, `∫‖A.field‖²=⟪A.toLp,A.toLp⟫`), `norm_toLp_sq_eq_l2Sq` (its `‖A.toLp‖²=∫‖A.field‖²` form for finding 8), `gradientSq_eq_sum` (E2b, `∑ᵢ‖(A.dir(axis i)).toLp‖²=∫∑ᵢ‖fderiv A.field x (axis i)‖²`), `sqrt_dirSum_sq` (the `Real.sqrt` adapter of finding 4), `pairing_eq_inner` (E2c, `∫⟪A.field,B.field⟫=⟪A.toLp,B.toLp⟫`), and the assembly demo `energyIdentity_of_carrierB`. **Dependency-direction caveat:** `formalization/` cannot import `Contracts.V1` (`verification`→`formalization`, one-way), so the RHS is spelled with raw integrands (`∫‖·‖²`, `∫∑‖fderiv·‖²`, `∫⟪·,·⟫`) that are **definitionally** `l2Sq`/`gradientSq`/`pairing` on `A.field`. The single `= ‖gradientTensor·‖²` step (E2b) — `PiLp.norm_sq_eq_of_L2` + `coordinateVector=axis` + `spatialDerivative=fderiv` — is a one-line **verification-side binding**, since `gradientTensor` is a `Contracts.V1` object. No Plancherel, no order hypothesis. |
| E3 | momentum in `Lp`: `(∂ₜu).toLp = ν•(Δu).toLp − (adv).toLp − (∇p).toLp + f.toLp` | S–M | `D01.temporalDerivative_slice_eq` (`D01/Pressure.lean`, `∂ₜu = f−(u·∇)u+νΔu−∇p`); `toLp_addField`/`toLp_fieldNeg`/`toLp`-smul (vendor) | **DONE (lane 143, `momentum_split_toLp`, std 3 axioms).** `Lp.ext` + `coeFn_{add,sub,smul}` a.e. pushforward of `D01.temporalDerivative_slice_eq`; the vendor fields `Δu`/`(u·∇)u` are the manuscript `spatialLaplacian`/`advection` via `laplacianField_velocitySlice_field` (`vector_laplacian_eq_sum`) and `advectionField_velocitySlice_field` (`rfl`). |
| E4 | derivative path + time derivative at `s=0`: `HasDerivAt (fun r => ‖(velocity r).toLp‖²) (2⟪u,∂ₜu⟫) t` on `Ioo 0 T` | **M** | `wordEnergy_hasDerivWithinAt` at `s=0` (template `kineticEnergy_hasDerivWithinAt`, `OrdinaryEulerKineticEnergy.lean:26`); the **`hA` jet-continuity is `Evolution.velocityField_jetLp_continuous`** (`:164`, done); the **derivative path `B`** = `∂ₜu(r,·)` packages as `SmoothL2Field` via P2 `D01.temporalDerivative_slice_smoothSquareIntegrableJets_of_memForceR` (`PressureJets.lean:150`); pointwise `HasDerivAt (fun r => u(r,x)) (∂ₜu x) t` from `velocity_smooth` (unconditional — the existence half of `timeDeriv_isSobolevDatum`, no `2≤m`); `B`'s jetLp continuity (routine) | **BLOCKED (lane 143) — this note was wrong.** `wordEnergy_hasDerivWithinAt`'s hypothesis `hB : ∀ n, Continuous (fun s => (B s).jetLp n)` forces the **time-continuity of the `∂ₜu(s,·)` `L²` jets** (its `hd` pins `B = ∂ₜu`). Via the momentum split that reduces to the **time-continuity of the `∇p(s,·)` `L²` jets**, which the class does NOT provide (`sobolev` = continuous datum path for the *velocity* only; `MemForceR` for the *force*; pressure carries only the pointwise `pressure_gradient`). **P2 is pointwise-in-time**, so it does NOT supply it — closing it needs a *continuous-in-time* momentum-residual datum path pushed through `Leray.lerayComplement` (a new time-regularity unit, ≈L). The direct "differentiate under `∫`" route needs the same `∂ₜu` `L²` control uniform in time. See `research/C01/ATTEMPTS_E3E4.md` §3. **Review 143 (09-14)**: route (a) re-estimated M–L concentrated in one unit (continuous-in-time order-m datum path of the momentum residual `f − (u·∇)u + νΔu`); blocks already present: `(u·∇)u` jet continuity (`SmoothEulerEvolution.lean:29`), `Δu`/`ν•` via `continuous_jetLp_directionalField` + `addField`/`mapField`, force path mirrors `velocityField_jetLp_continuous`, `lerayComplement` is a CLM (`LerayDatum.lean:255`). Route (b) via A02 uniqueness is dearer: no `ClassicalSolutionR` constructor in tree yet and the vendor assumes `hB`. Value identity `2⟪u,∂ₜu⟫ = −2ν(∫∑‖∂ᵢu‖²) + 2(∫⟨u,f⟩)` already unconditional (`rev143_hd_not_escape.lean`). **Update (lane 148, E4b DONE):** the `hB` clause is supplied — `C01.temporalSlicePath_jetLp_continuous w hf hc hST` gives `∀ n, Continuous (fun t : Icc c S => (temporalSliceField w hf _).jetLp n)` on any `[c,S] ⊂ (0,T)`, with `∇p` half `pressureGradientPath_jetLp_continuous` (`PressureJetPath.lean`, std 3 axioms; both signatures are `(w hf) (hc:0<c) (hST:S<T) (n)` — `hcS` dropped per review 148 N1). **Exact target the E4 lane must prove** (the `hd` slot of `energyIdentity_classical`, `MomentumCarrierB.lean:254-258`): `energyDerivative_hasDerivAt (w hf) (hc:0<c) (hcS:c≤S) (hST:S<T) {r} (hr : r ∈ Ioo 0 (S−c)) : HasDerivAt (fun ρ => ‖(velocityField w hST ⟨(projIcc 0 (S−c) _ ρ).1 + c, _⟩).toLp‖²) (2*⟪(velocitySliceField w _).toLp, (temporalSliceField w hf _).toLp⟫_ℝ) r`. Assembly (review 148 §4): translate the `Icc c S` paths to the vendor `Icc 0 T'` (`T':=S−c`, `σ r := ⟨r+c,_⟩`); `hA`=`velocityField_jetLp_continuous`∘σ, `hB`=`temporalSlicePath_jetLp_continuous`∘σ; `hd` (**N4: NOT exported** — its only copy is inline in `A04.timeDeriv_isSobolevDatum`, `TimeDerivative.lean:182-206`, under `2≤m` + `ContDiffOn G`, so re-prove ≈7 lines from `velocity_smooth`, then the `+c` chain rule + `projIcc`/`congr_of_eventuallyEq`); feed `wordEnergy_hasDerivWithinAt` at `s=0` (**N3: no `wordEnergy_zero` lemma** — it yields `wordEnergy 0 X` and `2*(∑ n∈range 1, ∑ w:Fin n→Fin 3, ⟪…⟫)`, collapse via `wordField_zero` + the singleton `Fin 0→Fin 3`); then `HasDerivWithinAt.hasDerivAt` at interior `r` (`Icc_mem_nhds`). Full statement in `research/C01/ATTEMPTS_E4B.md`. |
| E4a | the three time-continuous carrier-B jet paths of the momentum residual `h = f − (u·∇)u + νΔu`, on `Icc 0 S` (`S<T`) | **S–M** | vendor `advection_jet_continuous` (`SmoothEulerEvolution.lean:29`); `continuous_jetLp_directionalField`/`addField`/`mapField`; force path mirrors `velocityField_jetLp_continuous`; `D01.temporalDerivative_slice_eq` | **DONE (lane 146, `Section4/C01/JetPaths.lean`, std 3 axioms).** `forcePath`/`advectionPath`/`laplacianPath`/`viscousPath`/`residualPath` with `_jetLp_continuous` each, `residualPath_field` = `f − advection + ν•spatialLaplacian` (token-for-token `pin_pressureGradient_datum`'s `hAm`), and `temporalDerivative_eq_residual_sub_pressureGradient`: `∂ₜu = residualPath − ∇p`. Reusable by E5. |
| E4b | jet-continuity in time of `∇p(s,·)` = `(I−P) h`, hence of `∂ₜu(s,·)` (the `hB` of `wordEnergy_hasDerivWithinAt`) | **M** | E4a `residualPath_jetLp_continuous`; `Leray.lerayComplement` CLM (`LerayDatum.lean:255`); `pin_pressureGradient_datum` (`PressureJets.lean:112`); `jetOfDatum_continuous` (`Evolution.lean:147`) | **DONE (lane 148, `Section4/C01/PressureJetPath.lean`, std 3 axioms).** The *jets ⟹ order-m datum* direction is closed at **every** order (no order-1 hole): `smoothAngularDatum_path_continuous` squeezes `‖A_{P t} − A_{P s}‖² ≤ 16^m·∑_{k≤m}‖(P t).jetLp k − (P s).jetLp k‖²` (`norm_smoothAngularDatum_sub_sq_le`), whose datum-difference-is-a-datum-of-the-field-difference step uses `D01.isSobolevDatum_sub` (the `SchwartzPairable` order-0-algebra version — valid at all orders, so the `2≤s` gap of `A03.isSobolevDatum_sub` is avoided) and whose quantitative bound is `D01.norm_isSobolevDatum_le_of_memLp_derivs` fed glue (a) `hasWeakDerivsL2Bound_of_jetLp_sq_le` (M written through the jets). Then `Leray.lerayComplement`∘it + `isSobolevDatum_pressureGradient_lerayComplement` pins `∇p`s order-n datum, and `jetOfDatum_continuous`∘that gives `pressureGradientPath_jetLp_continuous` on `Icc c S ⊂ (0,T)` (0<c≤S<T); `temporalSlicePath_jetLp_continuous` is the `hB` (`∂ₜu = residual − ∇p`). See `research/C01/ATTEMPTS_E4B.md`. |
| **energyIdentity** (:344) | `HasDerivAt (fun s => l2Sq (slice u s)) (−2ν·gradientSq(slice u t)+2·pairing(slice u t)(slice f t)) t` | **M** (assembly) | E0(`_deriv`)+E1+Ep+E2+E3+E4; `advection_inner_zero`, `laplacian_pairing`, `gradient_pairing_zero` for E0's `hnl`/`hlap`/`hpr` | **payoff DONE modulo E4 (lane 143, `energyIdentity_classical`, std 3 axioms).** Given the E4 value fact `hd : d = 2⟪u,∂ₜu⟫`, `energyIdentity_of_carrierB` yields `d = −2ν·gradientSq(u) + 2·pairing(u,f)` (raw-integral form) from Ep+E3+`hdiv`/`hgrad`/`hp`. **E4 is the single remaining input and is blocked** (see E4 row). Bindings lane: bridge the raw integrals to spec `l2Sq`/`gradientSq`/`pairing` (the `verification`-side `PiLp.norm_sq_eq_of_L2` step, `Vocabulary.lean` header), and — once E4 lands — wrap in the `HasDerivAt`. |
| **energyDifferentialBound** (:364) | `∀E', HasDerivAt … E' t → E'+2ν·gradientSq ≤ 2·l2Norm(f)·l2Norm(u)` | **S** (after E2) | `energyIdentity` (`HasDerivAt.unique`); **E2a in the form `l2Norm (slice z t) = ‖(Z t).toLp‖`** (finding 8); Cauchy–Schwarz `real_inner_le_norm` | **S once E2a lands** (not in parallel with it). `E'` pinned to the identity's value; nonlinear/pressure already gone. |
| **l2Bound** (**eq:RL2**, :383) | `l2Norm (slice u t) ≤ energyBudget a f t` | **M** | `energyDifferentialBound` (dissipation discarded); generalize `Paper1.sqrt_energy_le_primitive` (`ScalarEnergy.lean:22`, currently needs `E 0 = 0 ∧ N 0 = 0`) to `√(E 0) ≤ N 0` | **M**. Scalar regularized-division argument exists; `l2Norm(u 0)=l2Norm a` via `ClassicalSolutionR.initial`. |
| E5 | enstrophy time derivative: `d/dt ∑ᵢ‖∂ᵢu‖²_{Lp} = 2∑ᵢ⟪∂ᵢu,∂ᵢ∂ₜu⟫` then `= −2⟪Δu,∂ₜu⟫` | **M** | `wordEnergy_hasDerivWithinAt` at `s=1` minus `s=0`; `field_directional_ibp` | **M**. `wordEnergy 1 − wordEnergy 0 = ∑ᵢ‖∂ᵢu‖²`; IBP moves one `∂ᵢ`. Same derivative-path input as E4 (P2-supplied). |
| E6 | enstrophy pressure drop `⟨Δu, ∇p⟩ = 0` (physical) | **M** | `field_directional_ibp` twice + solenoidality, or `gradient_pairing_zero` at the higher jet with `∇p`'s P2 packaging | **M**, `COMPARISON.md` item 2(b)2 "new". Not `advection_inner_zero` (that is the `m=0` term). |
| E7 | enstrophy arithmetic core `½·d_grad + ν·‖Δu‖² = ⟪N,L⟫ − ⟪F,L⟫`, from `d_grad = −2⟪L,Gt⟫`, `hmom`, `⟪L,L⟫=‖Δu‖²`, `⟪P,L⟫=0` | **S** | pure algebra (pair the equation against `L=Δu`, nonlinear **kept**) | **S**, a sibling of E0 with the nonlinear term retained; **not** done this lane (scope). |
| **enstrophyIdentity** (:487) | `HasDerivAt (fun s => gradientSq (slice u s)) (2·advectionWork(u t) − 2ν·laplacianSq(u t) − 2·pairing(f t)(laplacian(u t))) t` | **M** (assembly) | E5+E6+E7+E3+E2 (extended to `laplacianSq`, `advectionWork`) | **assembly**, all inputs exist; nonlinear term `advectionWork` survives. |
| **enstrophyDifferentialBound** (:510) | with `C₁·criticalL3(u t) ≤ ν/4`: `E'+ν·laplacianSq ≤ CRH1·ν⁻¹·l2Sq(f)` | **M** | `enstrophyIdentity` (`E'` unique); registered `trilinearAbsorbed` + `laplacianSqENorm` (EnergyAbsorptionPartial); Young | **M**. First consumer of the registered trilinear fields. |
| **enstrophyIntegralBound** (:532) | integrate eq:RH1 on `[0,t]` + `IntervalIntegrable (laplacianSq∘slice u)` | **M–L** | `enstrophyDifferentialBound`; FTC; continuity of `laplacianSq∘slice` (mirror `A04.intervalIntegrable_highContinuationIntegrand`, in physical vocabulary) | **M–L**. |
| **sobolevTwoFourier** (:555) | `sobolevENorm 2 z ^2 ≤ ENNReal.ofReal (CH2·(l2Sq z + laplacianSq z))` | **L** | `Source.AngularGradientIdentity.vectorAngularSobolev_succ` (`:92`, **requires `HasCompactSupport`**); registered `hessianLaplacianIdentity`; interpolation `∑‖∂ᵢu‖₂² ≤ ‖u‖₂‖Δu‖₂` | **L**, `COMPARISON.md:40`. Crosses carrier A↔B (identify `Source.vectorAngularSobolevNorm` with D01's `sobolevENorm 2`, **the order-2 sibling of the open order-0 Plancherel item**) + de-compactify. Hardest remaining row. |
| **h2TimeIntegral** (:576), **…ZeroDatum** (:599) | `∫⁻₀^S ‖u(t)‖²_{H²} ≤ ENNReal.ofReal (CSK² + Cν⁻¹‖∇a‖₂² + Cν⁻²∫‖f‖₂²)` | **M** (assembly) | `l2Bound` + `enstrophyIntegralBound` + `sobolevTwoFourier` + `forceTimeRegularity` (registered); zero-datum sets `a=0` | **M assembly**, gated on the four above. `∫⁻` needs no integrability side condition. |

### Sub-question answers demanded by the brief

* **(a) `m=0` instance of `inner_energy_assembly`'s inputs — exact vs inequality.**
  On carrier A `⟪G,L⟫` is **exact** (`inner_datum_laplacian`), `⟪G,P⟫=0`
  **unconditional at `m=0`** (`pressure_drop` + `exists_isSobolevDatum_zero_of_memLp`),
  and only `hmom` is gated (`2≤m` in the existing lemma). On carrier B all three
  are exact/unconditional: `laplacian_pairing` (a **sum** of squares → `Real.sqrt`
  adapter), `gradient_pairing_zero` (via the P2 `∇p` packaging, row Ep), and the
  momentum equation is the pointwise `temporalDerivative_slice_eq` pushed through
  `toLp`. The **energy** identity wants *equalities*, not the `≤` of
  `inner_energy_assembly` — hence the new **E0** (proved this lane).
* **(b) The missing exact nonlinear vanishing at `m=0`.**  Not missing:
  `advection_inner_zero` (`OrdinaryTransportCancellation.lean:42`) is `⟨(A·∇)B,B⟩=0`
  for divergence-free `A`, applied at `A=B=u` (the vendor's own energy identity,
  `OrdinaryEulerKineticEnergy.lean:19-21`). Wiring into `hnl`: **S** (one
  application + `real_inner_comm` + `Evolution.velocityField_solenoidal`).
* **(c) The bridge from datum vocabulary to `l2Sq`/`gradientSq`/`pairing`.**  The
  spec's `pairing w z = ∫⟨w,z⟩` **is** the physical `L²` inner product; on carrier
  B it equals `⟪·.toLp, ·.toLp⟫` by `field_inner` (`OrdinaryL2Integration.lean:26`,
  up to `real_inner_self_eq_norm_sq`) — a light **S–M** bridge (row E2),
  **no Plancherel**. On carrier A the same bridge is the order-0 datum inner
  product, resting on the **absent** order-0 Parseval identity (polarization of the
  open `OrderZeroDatum.lean:40-53` norm identity); 124's `orderZeroDatumCLM` gives
  the CLM but not the norm/inner-product identity. **So the vocabulary bridge is
  cheap only on carrier B; on carrier A it is itself the hard open item.** This —
  not `2≤m` — is why the route goes through carrier B.
* **(d) Bookkeeping rows.**  E1 (done — consume `Evolution.velocityField`), Ep
  (package `∇p`, S), E3 (linear `toLp` pushforward), and the assembly rows
  `energyIdentity`, `enstrophyIdentity`, `h2TimeIntegral(ZeroDatum)`;
  `energyDifferentialBound` is **S** bookkeeping (derivative uniqueness + E2a +
  Cauchy–Schwarz).

## 2. Recommended next lane and order

**Primary next lane: row E2 — the carrier-B vocabulary bridge**
(module `Section4/C01/Vocabulary.lean`, S–M, ≈60–90 lines, **no open input**):
```lean
theorem toLp_inner_eq_pairing (A B : SmoothL2Field Space) :
    ⟪A.toLp, B.toLp⟫_ℝ = ∫ x, ⟪A.field x, B.field x⟫_ℝ            -- = field_inner
theorem toLp_norm_sq_eq_l2Sq (A : SmoothL2Field Space) :
    ‖A.toLp‖ ^ 2 = ∫ x, ‖A.field x‖ ^ 2
theorem sum_directional_norm_sq_eq_gradientSq (A : SmoothL2Field Space) :
    ∑ i : Fin 3, ‖(A.directionalField (EulerOrdinarySobolev.axis i)).toLp‖ ^ 2
      = ∫ x, ‖Contracts.V1.gradientTensor A.field x‖ ^ 2
```
Deliver with the `Real.sqrt` adapter (finding 4) so `laplacian_pairing`'s sum
feeds `inner_energy_identity_deriv`.

**The D01 L9(c) "parallel lane" the review recommends is UNNECESSARY: P2 is done.**
`D01.pressureGradient_slice_smoothSquareIntegrableJets_of_memForceR`
(`PressureJets.lean:128`, registered `D01.datum_lemmas_v3`) already gives
`SmoothSquareIntegrableJets (∇p(t,·))` = all-order `L²` jets + smoothness = a
`SmoothL2Field`, unconditionally for `t ∈ Ioo 0 T`; and
`temporalDerivative_slice_smoothSquareIntegrableJets_of_memForceR`
(`PressureJets.lean:150`) does the same for `∂ₜu`. So `hpr` (row Ep) and E4's
derivative path have their inputs in tree.

**Order:** E2 (done next) → E1(done)/Ep/E3/E4 → `energyIdentity` →
`energyDifferentialBound` → `l2Bound`. Then E5/E6/E7 → `enstrophyIdentity` →
`enstrophyDifferentialBound` → `enstrophyIntegralBound`. `sobolevTwoFourier`
(**L**, the one carrier-crossing) and the two `h2TimeIntegral` assemblies last.
