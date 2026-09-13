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
| SL2 | momentum eq in datum form: `Gt = ν•L − N − P + F` | M | open | SL1(done) + `ClassicalSolutionR.momentum` + datum linearity (`isSobolevDatum_smul`) |
| SL3 | Laplacian identity: `⟪G t, L⟫ = −(‖∇u‖_{H^m})²` | L | open | datum-side order shift (`SmoothDatum.lean:388` is jet-side) |
| SL4 | pressure drop: `⟪G t, P⟫ = 0` | L | open | `∇p` datum at order m (D01 **L9(c)**, other lane) |
| SL5 | nonlinear IBP + Cauchy–Schwarz: `−⟪G t, N⟫ ≤ ‖∇u‖_{H^m}·‖u⊗u‖_{H^m}` | L | open | H^m IBP of `∇·(u⊗u)` on datum carrier |
| SL6 | outer tame transport: `‖u⊗u‖_{H^m} ≤ Ctame m · ‖u‖_{H²}‖u‖_{H^m}` (reals) | **S** | **DONE** (`outerNormAt_le`) | — |
| SL7 | force CS + norm identifications: `⟪G,F⟫ ≤ ‖G‖‖F‖`, `‖G t‖=sobolevNormAt`, `‖F‖=sobolevNormAt f` | **S** | generic CS **DONE** (in SL8); carrier identifications need lane 053 | lane 053 instance for `⟪⟫`↔`sobolevNormAt` |
| SL8 | assembly to eq:Rhigh's RHS | **S** | **DONE** (`inner_energy_assembly`/`inner_energy_Rhigh`) | — |

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

### SL4 — pressure drop (L; D01 L9(c) gap, worked in another lane)
```
theorem pressure_datum {…} (hdiv : div-free u) : ⟪G t, P⟫ = 0
```
`⟪u, ∇p⟫_{H^m} = −⟪div u, p⟫_{H^m} = 0`. Needs `∇p(t,·)` present in the datum
carrier at order `m` — the L9(c) obligation currently being closed elsewhere.
State as a dependency; do not reprove here. Supplies `hpr`. As for SL2/SL3, the
"pin-the-representative" technique (`representative_ae` +
`angularRealization_boundedRepresentative`) reduces the datum identity to a
pointwise one and is the recommended route once `∇p`'s order-`m` datum is in hand.

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
`SL0(done), SL1(done)→SL2, SL3, SL4, SL5+SL6(SL6 done), SL7(partly done) ⟶ SL8(done)`.
Closed today: **SL1 (D2)**, **SL6**, **SL8**, and the SL7 arithmetic. The
remaining **frontier** is SL2 (momentum eq in datum form — needs the residual
equation transported to datums plus `isSobolevDatum_smul`), SL3 (datum-side order
shift, open), SL4 (D01 **L9(c)** pressure gap, another lane), SL5 (H^m
integration by parts of `∇·(u⊗u)`), and the SL7 carrier link (lane 053's
inner-product instance in PR). D2 is **no longer** on that list, and none of the
remaining items is blocked on an unowned A01 clause; SL2–SL4 should each shorten
via the "pin-the-representative" technique SL1 uses.
