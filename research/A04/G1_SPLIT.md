# A04 unit G1 — split of eq:Rhigh on the datum carrier

Lane 056, task A04 (shared with A01 unit A2). Target: field `energyIdentityHigh`
(`research/A04/Spec.lean:424-434`), the manuscript's **eq:Rhigh**
(`paper/sections/appendix-a-local-theory.tex:129-138`):

```
½ (d/dt)‖u‖²_{H^m} + ν‖∇u‖²_{H^m}
   ≤ C_m ‖u‖_{H²} ‖u‖_{H^m} ‖∇u‖_{H^m} + ‖f‖_{H^m} ‖u‖_{H^m}   (m ≥ 3, t ∈ (0,T))
```

The Lean shape is `∃ d, HasDerivAt (fun r => sobolevNormAt (m:ℝ) w.velocity r ^ 2) d t ∧
(1/2)*d + ν*gradientSobolevNormAt (m:ℝ) w.velocity t ^ 2 ≤ Chigh m * sobolevNormAt 2 … *
sobolevNormAt (m:ℝ) … * gradientSobolevNormAt (m:ℝ) … + sobolevNormAt (m:ℝ) f t *
sobolevNormAt (m:ℝ) w.velocity t`.

## Carrier and objects

Work on the **D01 datum carrier**, `E := RealVectorSobolev (m:ℝ)` (Paper3), the
real Hilbert space of order-`m` angular Sobolev data.

* `G : ℝ → E` — the D1 datum path of `u` from `HasSmoothSobolevPath T u`
  (`DerivNorm.exists_hasDerivAt_sobolevNormAt_sq`, lane 053, in PR). `G t` is the
  datum of `u(t,·)`; `Gt := deriv G t`.
* `L N P F : E` — the order-`m` data of `Δu(t,·)`, `(u·∇)u(t,·)`, `∇p(t,·)`,
  `f(t,·)`.
* `sobolevNormAt (m:ℝ) u t = (D01.sobolevENorm (m:ℝ) (u t·)).toReal` (`Forcing.lean:74`);
  on a solution it equals `‖G t‖` (`Continuity.sobolevNormAt_eq` + D1).
* Inner product `⟪·,·⟫` on `E`: lane 053's `Paper3.realSobolevInnerProductSpace`
  — **in PR, not yet on `erenup/integration`**; every step that uses `⟪·,·⟫` on
  the concrete carrier is blocked on lane 053 merging (the arithmetic lemmas
  below dodge this by being generic in `E`).

The chain is: pair the projected momentum equation `∂ₜu = νΔu − (u·∇)u − ∇p + f`
(with `div u = 0`) against `u` in `H^m`, i.e. read
`⟪G, Gt⟫ = ν⟪G,L⟫ − ⟪G,N⟫ − ⟪G,P⟫ + ⟪G,F⟫`, bound each term, and feed
`d = 2⟪G, Gt⟫` (D1) into the arithmetic.

## Sub-lemma table

| # | statement (informal) | size | status | blocker |
|---|---|---|---|---|
| SL0 | D1: `d = 2⟪G t, deriv G t⟫`, `sobolevNormAt = ‖G·‖` | M | **DONE (lane 053, in PR)** | — |
| SL1 | **D2**: `deriv G t` is the datum of `∂ₜu(t,·)` (+ existence of `∂ₜu`) | S/M | **DONE** (`TimeDerivative.timeDeriv_isSobolevDatum`) | — |
| SL2 | momentum eq in datum form: `Gt = ν•L − N − P + F` | M | **DONE** (`momentum_datum`, `A04/MomentumDatum.lean:140`) | — |
| SL3 | Laplacian identity: `⟪G t, L⟫ = −(‖∇u‖_{H^m})²` | L | **DONE** (`inner_datum_laplacian` / `inner_datum_laplacian_le'`, `A04/LaplacianAssembly.lean:330,354`) | — |
| SL4 | pressure drop: `⟪G t, P⟫ = 0` | **S** (Leray self-adjoint route) | **DONE** (lane 121, `A04/PressureDrop.lean` `pressure_drop`) | — |
| SL5 | nonlinear IBP + Cauchy–Schwarz: `−⟪G t, N⟫ ≤ ‖∇u‖_{H^m}·‖u⊗u‖_{H^m}` | L | **DONE** (`inner_advection_bound_slice`, `A04/NonlinearBound.lean:186`; see `SL5_SPLIT.md`) | — |
| SL6 | outer tame transport: `‖u⊗u‖_{H^m} ≤ Ctame m · ‖u‖_{H²}‖u‖_{H^m}` (reals) | **S** | **DONE** (`outerNormAt_le`) | — |
| SL7 | force CS + norm identifications: `⟪G,F⟫ ≤ ‖G‖‖F‖`, `‖G t‖=sobolevNormAt`, `‖F‖=sobolevNormAt f` | **S** | generic CS **DONE** (in SL8); carrier identifications need lane 053 | lane 053 instance for `⟪⟫`↔`sobolevNormAt` |
| SL8 | assembly to eq:Rhigh's RHS | **S** | **DONE** (`inner_energy_assembly`/`inner_energy_Rhigh`) | — |
| assembly | `energyIdentityHigh` (Spec.lean:424-434) | **S** | **DONE (lane 128, `Section4/A04/EnergyIdentityHigh.lean`)**: `def Chigh m := A03.outerTameConst m` + `Chigh_pos`, `energyIdentityHigh_core` (probe promoted verbatim, credit lane-121 reviewer), and `energyIdentityHigh` = spec field token-for-token (∀-prefix, `a ∈ initialClassR` unused). Std axioms; conformance `example` in `research/A04/axioms_energy_identity_high.lean`. Contract V1 field + binding + test not yet registered | — |

`Chigh m := Ctame m = A03.outerTameConst m`; `Chigh_pos` from
`A03.outerTameConst_pos`. Registered clause used: `A03.outerProductTame`
(local theorem `A03/OuterTameProduct.lean:157`; contract field
`TameProductAPI.outerProductTame`, `Bindings/TameProduct.lean:122`, constant
`Ctame := A03.outerTameConst`).

## Exact Lean-ready statements

Notation: `open scoped RealInnerProductSpace` (`⟪·,·⟫` = real inner product);
`z t := fun x : Space => u (t, x)`; `sobolevENorm = D01.sobolevENorm`.

### SL0 (D1, done in lane 053 — input)
```
DerivNorm.exists_hasDerivAt_sobolevNormAt_sq (h : HasSmoothSobolevPath T u) (m : ℕ) :
  ∃ G : ℝ → RealVectorSobolev (m:ℝ),
    (∀ r ∈ Ico 0 T, sobolevNormAt (m:ℝ) u r = ‖G r‖) ∧
    ∀ t ∈ Ioo 0 T, HasDerivAt (fun r => sobolevNormAt (m:ℝ) u r ^ 2) (2 * ⟪G t, deriv G t⟫) t
```
Supplies `hd : d = 2 * ⟪G t, deriv G t⟫` with `d` existentially chosen, and the
`sobolevNormAt = ‖G r‖` identification (feeds SL7's `hG`).

### SL1 — D2 (**S/M, DONE here**, `formalization/…/A04/TimeDerivative.lean`)
```
theorem timeDeriv_isSobolevDatum
    (w : ClassicalSolutionR ν a f T) {m : ℕ} (hm : 2 ≤ m)
    {G : ℝ → RealVectorSobolev (m:ℝ)}
    (hGd : ∀ t ∈ Ico 0 T, IsSobolevDatum (m:ℝ) (fun x => w.velocity (t, x)) (G t))
    (hGc : ContDiffOn ℝ ∞ G (Ico 0 T)) {t : ℝ} (ht : t ∈ Ioo 0 T) :
    (∀ x : Space, HasDerivAt (fun r => w.velocity (r, x))
        (deriv (fun r => w.velocity (r, x)) t) t) ∧
      IsSobolevDatum (m:ℝ)
        (fun x => deriv (fun r => w.velocity (r, x)) t) (deriv G t)
```
i.e. the pointwise time derivative `∂ₜu(t,x)` **exists** for every `x` (first
conjunct) and `deriv G t` **is** the order-`m` datum of `x ↦ ∂ₜu(t,x)` (second).

**The earlier "L, unowned, needs A01" verdict was wrong** (`REVIEW_G1.md`
finding 2). The difference-quotient route (which would need a limit inside the
Schwartz-pairing integral, hence A01 `C^∞_{t,x}`) is *not* the route. The
**bounded representative** `Paper3.angularBoundedRepresentative s hs`
(`AngularTameProduct.lean:141`, a CLM `Lp ℂ 2 →L[ℝ] BoundedContinuousFunction`,
`2 ≤ s`, which `3 ≤ m` gives) turns the Hilbert-space derivative into a
**pointwise** one via `HasFDerivAt.comp_hasDerivAt`; `A03.representative_ae` +
`Continuous.ae_eq_iff_eq` pin it to the physical field; the imaginary part is the
derivative of the constant `0` (`HasDerivAt.unique`);
`Paper3.angularRealization_boundedRepresentative` converts back to
`IsSobolevDatum`. The **existence** conjunct comes straight from the joint
time–space smoothness `velocity_smooth` (a `ClassicalSolutionR` field). The
regularity actually used — each slice continuous and in `L²` — is delivered by
`D01.contDiff_slice w.velocity_smooth` and `D01.memLp_of_isSobolevDatum`, both on
integration. **No dominated convergence, no difference quotients, no
`isSobolevDatum_smul`, no new A01 clause.** The datum-side derivative field is
`fun x => deriv (fun r => u(r,x)) t`, whose `i`-th component is
`deriv (fun r => u(r,x) i) t` (vector slice differentiable), which is how the
componentwise scalar data (`d2_scalar`) reassemble via `isSobolevDatum_iff`
(`Iff.rfl`) and the `PiLp` projection CLM. This equals the manuscript's
`temporalDerivative w.velocity t x = fderiv (fun s => u(s,x)) t 1`.

### SL2 — momentum equation in datum form (M, A02 + datum linearity)
```
theorem momentum_datum {…} (ht : t ∈ Ioo 0 T) :
    deriv G t = ν • L − N − P + F      -- in RealVectorSobolev (m:ℝ)
```
From SL1 (`deriv G t` = datum of `∂ₜu`, now closed) plus the residual equation
`ClassicalSolutionR.momentum` (`νΔu − (u·∇)u − ∇p + f = ∂ₜu` pointwise, already a
field), datum linearity (`isSobolevDatum_add`, and a still-absent scalar-mul
companion `isSobolevDatum_smul` for the `ν•` term) and uniqueness (L1). Supplies
`hmom`. **The "pin-the-representative" technique of SL1** — `A03.representative_ae`
+ `angularRealization_boundedRepresentative`, exactly how
`A03.isScalarSobolevDatum_{add,sub,mul}` (`ScalarTameProduct.lean:168-220`) are
proved — turns each datum identity here into a *pointwise* identity of continuous
functions and should shorten this considerably; the pressure/Laplacian data are
the remaining inputs (SL3, SL4).

### SL3 — Laplacian / dissipation identity (L; **use the datum carrier**)
```
theorem lap_datum {…} : ⟪G t, L⟫ = − (gradientSobolevNormAt (m:ℝ) u t) ^ 2
```
`⟪a, Δb⟫_{H^m} = −⟪∇a, ∇b⟫_{H^m}`, diagonal `= −‖∇u‖²_{H^m}`. Needs the datum of
`∂ᵢu` at order `m` and the **datum-side** order shift. `SmoothDatum.lean:388`
(`angularRealization_smoothAngularDatum_directional`) realises directional
derivatives but on the **jet** carrier (`SmoothL2Field`), and its docstring
records U1b(ii) — the datum-carrier order shift `‖∇v‖ ≤ ‖v‖_{+1}` — as *untouched*.
**Decision: prove the identity on the datum carrier**, not the jet carrier: the
energy inequality's `⟪G t, deriv G t⟫` and `gradientSobolevNormAt` both live
datum-side, so a jet-side identity would need an extra D01 **L2** carrier
transport (whose `⟸` direction is the recorded gap). Prerequisite: a
formalization def of `gradientSobolevNormAt` (currently only in `Spec.lean:190`;
add it as N1-style bookkeeping over `A03.gradientSobolevENorm`). The
"pin-the-representative" technique (as in SL1/SL2) applies to the pairing
identity `⟪a, ∂ᵢb⟫ = −⟪∂ᵢa, b⟫`, reducing it to a pointwise integration by parts
of continuous representatives once the order-`m` datum of `∂ᵢu` is available.

### SL4 — pressure drop (**S**, DONE lane 121, `A04/PressureDrop.lean`)
```
theorem pressure_drop (u : ClassicalSolutionR ν a f T) (hf : MemForceR f)
    {m : ℕ} {t : ℝ} (ht : t ∈ Ioo 0 T) {G P : RealVectorSobolev (m:ℝ)}
    (hG : IsSobolevDatum (m:ℝ) (fun x => u.velocity (t,x)) G)
    (hP : IsSobolevDatum (m:ℝ) (fun x => pressureGradient u.pressure t x) P) :
    ⟪G, P⟫ = 0
```
Proved by the **cheap operator-algebra route** of `research/D01/REVIEW_SL8_ASSEMBLY.md` §7,
NOT the pin-the-representative IBP. Three recorded theorems:
* `lerayComplement_selfAdjoint` — `Leray.lerayComplement s` is self-adjoint on the real datum
  carrier (restriction of `lerayComplementAmbient`, which is `coordinates∘lerayComplementL2∘assemble`
  with `lerayComplementL2` fibrewise self-adjoint via `isSelfAdjoint_starProjection`);
  `inner_lerayComplement_eq_zero_of_eq_zero` is its `(I−P)G=0 ⟹ ⟪G,(I−P)B⟫=0` consequence.
* `velocity_datum_lerayComplement_eq_zero` — `(I−P)ₘG = 0` for any order-`m` datum `G` of the
  solenoidal velocity slice (lane-117 bootstrap: order-0 transversality lifted via `lowerVectorL`).
* `pressure_drop` — pins `P = (I−P)ₘAm` (lane 117 `pin_pressureGradient_datum`), then combines the
  two. The `hP` slot input (`∇p`'s order-`m` datum, D01 P2) is now unconditional (lane 117).
Binder shapes match `momentum_datum`'s `hGd`/`hP` and `inner_energy_assembly`'s `hpr`; a fit
`example` in the module feeds `pressure_drop` into the assembly verbatim.

### SL5 — nonlinear IBP + Cauchy–Schwarz (L)
```
theorem nonlinear_pairing_le {…} :
    − ⟪G t, N⟫ ≤ gradientSobolevNormAt (m:ℝ) u t *
                  (outerSobolevENorm (m:ℝ) (u t·) (u t·)).toReal
```
`(u·∇)u = ∇·(u⊗u)` (solenoidal), `⟪G, datum(∇·(u⊗u))⟫_{H^m} = −⟪∇-datum, u⊗u datum⟫_{H^m}`
(H^m integration by parts), then `abs_real_inner_le_norm`. The `‖∇u‖_{H^m}` factor
is the same `gradientSobolevNormAt` as SL3. Supplies the first half of `hnl`.

### SL6 — outer tame transport (**S, done**, `formalization/…/A04/HighEnergy.lean`)
```
theorem outerSobolevNormAt_le {m : ℕ} (hm : 2 ≤ m) {z : Space → Space}
    (hz : MemHmVector m z) (h2 : sobolevENorm 2 z ≠ ⊤) (hmz : sobolevENorm (m:ℝ) z ≠ ⊤) :
    (outerSobolevENorm (m:ℝ) z z).toReal
      ≤ outerTameConst m * ((sobolevENorm 2 z).toReal * (sobolevENorm (m:ℝ) z).toReal)

theorem outerNormAt_le {m : ℕ} (hm : 2 ≤ m) {u : SpaceTimeField} {t : ℝ}
    (hz : MemHmVector m (u t·)) (h2 : sobolevENorm 2 (u t·) ≠ ⊤) (hmz : sobolevENorm (m:ℝ) (u t·) ≠ ⊤) :
    (outerSobolevENorm (m:ℝ) (u t·) (u t·)).toReal
      ≤ outerTameConst m * (sobolevNormAt 2 u t * sobolevNormAt (m:ℝ) u t)
```
`toReal` of `A03.outerProductTame`; RHS finite by N1. Combined with SL5:
`−⟪G,N⟫ ≤ Ctame m · ‖u‖_{H²}‖u‖_{H^m}‖∇u‖_{H^m}` — the exact `hnl` shape below,
`C = Ctame m`. Finiteness inputs `h2`, `hmz` are `Continuity.sobolevENorm_velocity_ne_top`.
`MemHmVector m z = MemLp z 2 volume ∧ sobolevENorm (m:ℝ) z ≠ ⊤`
(`A03/VectorTameProduct.lean:48`): the second conjunct is
`sobolevENorm_velocity_ne_top` (from `.sobolev`), but the **`MemLp` conjunct needs
`velocity_smooth` too** (`REVIEW_G1.md` finding 3) — not `.sobolev` alone. The
one-liner is
`⟨memLp_of_isSobolevDatum (D01.contDiff_slice w.velocity_smooth ht) (hGd t ht),
sobolevENorm_velocity_ne_top w m ht⟩`.

### SL7 — force CS + norm identifications (**S**; generic CS done, carrier link on lane 053)
Generic Cauchy–Schwarz `⟪G, F⟫ ≤ ‖G‖·‖F‖` is folded into SL8 via
`real_inner_le_norm`. Remaining bookkeeping: `hG : ‖G t‖ = sobolevNormAt (m:ℝ) u t`
(from SL0/`sobolevNormAt_eq`), `hF : ‖F‖ = sobolevNormAt (m:ℝ) f t` (`sobolevNormAt_eq`
on an order-`m` datum of `f(t,·)`, which `MemForceR` supplies). Both are S once
lane 053's `Inner ℝ (RealVectorSobolev m)` instance is on integration (so `‖·‖`
is the inner-product norm `sobolevNormAt_eq` already uses — checked defeq in
`DerivNorm.lean`'s docstring).

### SL8 — assembly (**S, done**, `formalization/…/A04/HighEnergy.lean`)
```
theorem inner_energy_assembly {E} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {G Gt N P L F : E} {ν grad NLbound uNorm fNorm d : ℝ} (hν : 0 ≤ ν)
    (hd : d = 2 * ⟪G, Gt⟫) (hmom : Gt = ν • L - N - P + F)
    (hlap : ⟪G, L⟫ ≤ - grad ^ 2) (hpr : ⟪G, P⟫ = 0) (hnl : - ⟪G, N⟫ ≤ NLbound)
    (hG : ‖G‖ = uNorm) (hF : ‖F‖ = fNorm) :
    (1 / 2) * d + ν * grad ^ 2 ≤ NLbound + fNorm * uNorm

theorem inner_energy_Rhigh … (hν : 0 ≤ ν) …  (hnl : - ⟪G, N⟫ ≤ C * u2 * uNorm * grad) … :
    (1 / 2) * d + ν * grad ^ 2 ≤ C * u2 * uNorm * grad + fNorm * uNorm
```
(`hlap` weakened to `≤` with `0 ≤ ν`, `REVIEW_G1.md` finding 4, so an SL3 that
only proves the order shift as an inequality still feeds it.)
Generic in `E`, so it compiles today and is reused verbatim at
`E = RealVectorSobolev (m:ℝ)` once lane 053 lands. `inner_energy_Rhigh` is
already in eq:Rhigh's literal displayed shape: instantiate `C = Chigh m`,
`u2 = sobolevNormAt 2 u t`, `uNorm = sobolevNormAt (m:ℝ) u t`,
`grad = gradientSobolevNormAt (m:ℝ) u t`, `fNorm = sobolevNormAt (m:ℝ) f t`,
`d` from SL0; then `energyIdentityHigh` packages `⟨d, hderiv, inner_energy_Rhigh …⟩`.

## Assembly dependency order
`SL0(done), SL1(done)→SL2(done), SL3(done), SL4(done, lane 121), SL5(done)+SL6(done), SL7(partly done) ⟶ SL8(done) ⟶ assembly (probe compiled, lane 121 reviewer)`.
**All SL rows are now DONE in the tree** (as of lane 121): SL0/SL1 (D1/D2), SL2
(`momentum_datum`), SL3 (`inner_datum_laplacian_le'`), SL4 (`pressure_drop`, this lane),
SL5 (`inner_advection_bound_slice`), SL6 (`outerNormAt_le`), SL7 (carrier identifications via
lane 053's instance, on integration), SL8 (`inner_energy_Rhigh`).  With SL4's `hpr` in place the
**whole eq:Rhigh (`energyIdentityHigh`) assembles**, and lane 128 landed it as
`Section4/A04/EnergyIdentityHigh.lean`: `Chigh`/`Chigh_pos`, `energyIdentityHigh_core`
(the 121 reviewer's probe promoted verbatim), and `energyIdentityHigh` = the spec field
(`Spec.lean:424-434`) token-for-token (std axioms).  Remaining for the contract lane:
register the A04 V1 field + binding + test (the field statement is contract-ready — it is
token-identical to the spec).

## Unit G2 — eq:highcontinuation before the limit (lane 135, DONE)

Module `formalization/NSFormalization/Section4/A04/HighContinuation.lean`
(`appendix-a-local-theory.tex:139-145`, spec field `Spec.lean:459-470`
`regularizedNormDerivative`; `COMPARISON.md` §4 unit **G2**). Consumes G1
(`energyIdentityHigh`) and Z1 (`Regularized.lean`'s `regularized_sqrt_bound`).
Details and load-bearing hypotheses in `ATTEMPTS_HIGH_CONTINUATION.md`.

Declarations (all std axioms `[propext, Classical.choice, Quot.sound]`):
* `Cgron (m : ℕ) (ν : ℝ) : ℝ := Chigh m ^ 2 / (4 * ν)` — the constant Young's
  inequality produces; **`Cgron m ν = (Chigh m)²/(4ν)`**, the value `Spec.lean`
  leaves free.
* `Cgron_pos : ∀ m ν, 0 < ν → 0 < Cgron m ν`.
* `young_high_real` — pure real-arithmetic Young step
  `(½ d + ν g² ≤ C·a·n·g + F·n) → ½ d ≤ (C²/4ν)·a²·n² + F·n`.
* `young_absorption_high` — the same at `C = Chigh m`, folded into `Cgron`.
* `deriv_normSq_absorbed` (**review finding (a) hoist**) — the absorbed
  squared-norm derivative bound, `∃ d, HasDerivAt (‖u‖²_{H^m}) d t ∧ ½ d ≤
  Cgron·‖u‖²_{H²}·‖u‖²_{H^m} + ‖f‖_{H^m}·‖u‖_{H^m}` (`energyIdentityHigh` then
  `young_absorption_high`), and `deriv_normSq_absorbed_deriv` its `HasDerivAt.deriv`
  form. `regularizedNormDerivative` now consumes `deriv_normSq_absorbed`.
* `regularizedNormDerivative` — the spec field token-for-token (two-sided
  `HasDerivAt`, so `HasDerivAt.sqrt` is used directly, not Z1's one-sided
  `regularized_sqrt_hasDerivWithinAt`; only Z1's inequality `regularized_sqrt_bound`
  is consumed).

Conformance: `research/A04/axioms_high_continuation.lean` (`#print axioms` for all
six + a spec-shape `example` discharged by `regularizedNormDerivative`).

### Naming: unit G2b, not "G3"

The `ζ↓0` integral field `highContinuationIntegral` (`Spec.lean:471-494`) is
**unit G2b**, distinct from `COMPARISON.md` §4's **G3** = the variable-coefficient
Grönwall, which is **already done in tree** (`Gronwall.lean`, lane 041:
`gronwall_integral:70`, `gronwall_deriv:172`, `gronwall_integral_mul:202`). Calling
`highContinuationIntegral` "G3" clashes; use **G2b**.

### G2b recipe (size **S**, per the reviewer — every ingredient is proved) — **DONE (lane 138)**

Module `formalization/NSFormalization/Section4/A04/HighContinuationIntegral.lean`,
theorem **`highContinuationIntegral`** = `Spec.lean:471-494` token-for-token
(std axioms `[propext, Classical.choice, Quot.sound]`; conformance
`research/A04/axioms_high_continuation_integral.lean`). Recipe followed verbatim;
the two calc-shape and one nonnegativity subtlety are in `ATTEMPTS_G2B.md`.

`highContinuationIntegral`'s two conjuncts, both on `[t₀,t] ⊆ [0,T)`:

1. **The bound** `‖u(t)‖_{H^m} ≤ ‖u(t₀)‖_{H^m} + ∫_{t₀}^t (Cgron m ν ‖u‖²_{H²}‖u‖_{H^m} + ‖f‖_{H^m})`
   is `Regularized.lean:134` `sqrt_le_primitive_linear` with
   `E := fun r => sobolevNormAt m w.velocity r ^ 2` (so `√E = ‖u‖_{H^m}` by
   `Real.sqrt_sq`), `K := fun s => Cgron m ν * sobolevNormAt 2 w.velocity s ^ 2`,
   `b := fun s => sobolevNormAt m f s`. Its `hineq` is exactly
   **`deriv_normSq_absorbed_deriv`** doubled and `Real.sqrt_sq`-rewritten
   (`deriv E t ≤ 2(K·E + b·√E)`); its `ContinuousOn (Icc t₀ t₁)` hypotheses are
   `continuousOn_sobolevNormAt_velocity` (`Continuity.lean:105`) and
   `continuousOn_sobolevNormAt_force` (`:114`) mono'd along `Icc t₀ t ⊆ Ico 0 T`;
   the `hdE` interior-derivative family is `deriv_normSq_absorbed`'s `HasDerivAt`.
2. **`IntervalIntegrable` of the integrand** is `Continuity.lean:132`
   `intervalIntegrable_highContinuationIntegrand`, stated in the spec's own
   spelling with a `Cgron` parameter — **free**, one application. **Pass
   `A04.Cgron` explicitly** (finding 4: a local `Cgron` binder shadows the def
   inside that theorem and inside `Gronwall.lean:202`).

The `t₀ = 0` endpoint is fine: `energyIdentityHigh` gives derivatives on `Ioo 0 T`
and `sqrt_le_primitive_linear` needs them only on `Ioo t₀ t ⊆ Ioo 0 T`, with
continuity on `Icc t₀ t ⊆ Ico 0 T`; the field's `0 ≤ t₀` is exactly right.

### Next A04 contract = **V2** (not a fresh V1)

**Correction (coordinator):** A04's V1 contract `A04.energy_high_partial` was
merged as **PR #134**. The next registration is a **V2** adding `Cgron`
(→ `A04.Cgron`), `Cgron_pos` (→ `A04.Cgron_pos`), `regularizedNormDerivative`
(→ `A04.regularizedNormDerivative`), and `highContinuationIntegral` — opened
**after G2b lands** (so `regularizedNormDerivative`'s only consumer exists before
CI freezes its spelling). Carry `Cgron` as the spec's **opaque** `ℕ → ℝ → ℝ` field
plus `Cgron_pos`; the value `(Chigh m)²/(4ν)` lives only in the binding.

**G2b has now landed (lane 138)**, so the A04 **V2** contract can be opened: it
should register `Cgron` (→ `A04.Cgron`, opaque field + `Cgron_pos` →
`A04.Cgron_pos`), `regularizedNormDerivative` (→ `A04.regularizedNormDerivative`),
and `highContinuationIntegral` (→ `A04.highContinuationIntegral`,
`HighContinuationIntegral.lean`). The value `(Chigh m)²/(4ν)` stays in the
binding only. `regularizedNormDerivative`'s consumer (`highContinuationIntegral`)
now exists, as the plan required before freezing the spelling.

> Correction (138 review, finding 4): `regularizedNormDerivative` (G2) has **no consumer** tree-wide — G2b bypasses it via `deriv_normSq_absorbed` + `sqrt_le_primitive_linear`. Any sentence above claiming a consumer now exists is wrong; register it in V2 only with that disclosure.
