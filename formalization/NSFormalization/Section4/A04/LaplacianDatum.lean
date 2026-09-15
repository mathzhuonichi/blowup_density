import NSFormalization.Section4.A04.HighEnergy
import NSFormalization.Section4.D01.DerivativeDatum

/-!
# A04 unit G1, sub-lemma SL3: the dissipation norm on the datum carrier

`research/A04/G1_SPLIT.md` §SL3.  The energy inequality **eq:Rhigh** is assembled by
`A04.inner_energy_assembly` (`HighEnergy.lean`) from, among others, the dissipation
hypothesis

`hlap : ⟪G, L⟫_{H^m} ≤ - grad ^ 2`

with `E = RealVectorSobolev (m:ℝ)`, `G` = the order-`m` datum of `u(t,·)`, `L` = the
order-`m` datum of `Δu(t,·)`, and `grad = gradientSobolevNormAt (m:ℝ) u t`.  The manuscript
identity behind it is `⟪G, datum Δu⟫_{H^m} = -‖∇u‖²_{H^m}`
(`appendix-a-local-theory.tex:134`), i.e. on the angular Fourier side
`⟪Ĝ, (-|ξ|²) Ĝ⟫_{H^m} = -∑ⱼ ‖iξⱼ Ĝ‖²_{H^m}`.

This module supplies the two pieces of SL3 that close on the datum carrier:

* `gradientSobolevNormAt` — the N1-style real form of the dissipation norm, restating
  `research/A04/Spec.lean:190` over the local `A03.gradientSobolevENorm` (the `NSFormalization`
  package cannot import `Contracts.V1.TameProduct.gradientSobolevENorm`, which is defined by
  the identical `columnsSobolevENorm s (fun j => partialDeriv j v)`).
* `gradientSobolevNormAt_sq_eq_sum` / `gradientSobolevENorm_toReal_sq_eq_datum_sum` — the
  **gradient identification**: `grad² = ∑ⱼ ‖order-m datum of ∂ⱼu‖²`, and the exact `∂ⱼ`
  datum is the one produced by the shared derivative-datum multiplier
  `Paper3.angularDirectionalDerivativeReal` (`D01/DerivativeDatum.lean`,
  `isSobolevDatum_partialDeriv`).  This turns the right-hand side of the dissipation
  identity into the displayed `∑ⱼ ‖D_j (datum_{m+1} u)‖²`.

## What remains (the SL3 gap, unproved here, no `sorry`)

The full `hlap` needs the **pairing identity** `⟪G, L⟫ = -∑ⱼ ‖D_j (datum_{m+1} u)‖²`.
Componentwise it is the scalar integration-by-parts `⟪a, ∂ⱼ∂ⱼ a⟫_{H^m} = -‖∂ⱼ a‖²_{H^m}`.
Write `angularDirectionalDerivative s a = U ∘ M_s ∘ U⁻¹` with `U = angularFrequencyDilation` a
`LinearIsometryEquiv` (unitary) and `M_s = W_{s-1} ∘ σ_a ∘ W_{-s}` a product of three
multiplication operators.  The remaining work (all inputs on `erenup/integration`, overall
size **S–M**) is:

1. **Skew-adjointness of `angularDirectionalDerivative`** w.r.t. the `L²` inner product:
   `⟪a, D_j b⟫ = -⟪D_j a, b⟫`.  Do it on the *middle* operator `M_s` only — its a.e.
   coefficient function is the three-way product of `angularWeightMap_coeFn (s-1)`,
   `sobolevDirectionalDerivative_coeFn s a`, `angularWeightMap_coeFn (-s)` (all three lemmas
   already exist); the middle symbol is purely imaginary by
   `Paper3.mid_symbol_imaginary` (proved in `D01/DerivativeDatum.lean`), so
   `MeasureTheory.L2.inner_def` + `integral_congr_ae` give skew-adjointness of `M_s`.  Then
   transport across the unitary `U` with `LinearIsometryEquiv.inner_map_map` — **no dilation
   coefficient function is needed** (there is none in tree, and it would be an awkward
   change-of-variables).
2. **Self-adjointness of `angularOrderLowering`** (real middle symbol,
   `Paper3.lowering_symbol_real`), the same way.
3. The **Laplacian datum** `datum_m(Δu) = ∑ⱼ D_j (D_j (datum_{m+2} u))`, from
   `isSobolevDatum_partialDeriv` (twice, using `partialDeriv j Z.field =
   (Z.directionalField eⱼ).field`) and datum additivity `D01.isSobolevDatum_add` over the
   three directions.  There is **no order bookkeeping**: `Paper3.mid_symbol_order_independent`
   shows all `angularDirectionalDerivative s a` are the *same* map, so orders `m`, `m+1`, `m+2`
   never diverge.

Template: `Source/OrdinaryViscousStability.lean:32` already proves the **order-0** identity in
exactly this shape (`laplacian_pairing`, `laplacian_pairing_nonpos` — the `≤` form) on the jet
carrier, from a physical integration by parts; it does not transport to order `m` (the
datum-carrier norm is the `H^m` norm, not `L²`), but it is the sanity target for step 3.
`A04.inner_energy_assembly` already weakens `hlap` to `≤` (with `0 ≤ ν`), so the identity
proved as `≤` suffices.
-/

noncomputable section

open NavierStokes.ProblemStatement

namespace NSFormalization.Section4.A04

open NSFormalization.Section4.A02 (SpaceTimeField)
open NSFormalization.Section4.D01 (sobolevENorm IsSobolevDatum isSobolevDatum_partialDeriv)
open NSFormalization.Section4.A03 (gradientSobolevENorm partialDeriv)
open NSFormalization.Paper3 (RealVectorSobolev angularDirectionalDerivativeReal)
open EulerLpTranslation (SmoothL2Field)

/-! ## 1. The dissipation norm on the datum carrier -/

/-- `‖∇u(t)‖_{H^s}` as a real number, restating `research/A04/Spec.lean:190` over the local
`A03.gradientSobolevENorm` (definitionally `Contracts.V1.TameProduct.gradientSobolevENorm`,
`columnsSobolevENorm s (fun j => partialDeriv j v)`).  Same fail-safe `.toReal` remark as
`sobolevNormAt`. -/
def gradientSobolevNormAt (s : ℝ) (u : SpaceTimeField) (t : ℝ) : ℝ :=
  (gradientSobolevENorm s (fun x : Space => u (t, x))).toReal

/-! ## 2. The gradient identification -/

/-- The squared gradient norm of a field is the sum of the squared order-`s` datum norms of
its three partial derivatives, whenever those are finite: `‖∇z‖²_{H^s} = ∑ⱼ ‖∂ⱼz‖²_{H^s}`.
This is pure `ENNReal.toReal` arithmetic on the `columnsSobolevENorm` definition (`ℓ²`
assembly). -/
theorem gradientSobolevENorm_toReal_sq_eq_sum {s : ℝ} {z : Space → Space}
    (hfin : ∀ j : Fin 3, sobolevENorm s (partialDeriv j z) ≠ ⊤) :
    (gradientSobolevENorm s z).toReal ^ 2 =
      ∑ j : Fin 3, (sobolevENorm s (partialDeriv j z)).toReal ^ 2 :=
  -- one-line corollary of the promoted general lemma (lane 109); `gradientSobolevENorm s z`
  -- is `columnsSobolevENorm s (fun j => partialDeriv j z)` by `rfl`
  NSFormalization.Section4.A03.columnsSobolevENorm_toReal_sq_eq_sum hfin

/-- The `gradientSobolevNormAt` form of the same identity, on the time-`t` slice. -/
theorem gradientSobolevNormAt_sq_eq_sum {s : ℝ} {u : SpaceTimeField} {t : ℝ}
    (hfin : ∀ j : Fin 3, sobolevENorm s (partialDeriv j (fun x : Space => u (t, x))) ≠ ⊤) :
    gradientSobolevNormAt s u t ^ 2 =
      ∑ j : Fin 3, (sobolevENorm s (partialDeriv j (fun x : Space => u (t, x)))).toReal ^ 2 :=
  gradientSobolevENorm_toReal_sq_eq_sum hfin

/-- **Gradient identification in operator terms.**  For a smooth square-integrable field `Z`
with an order-`(m+1)` angular datum `A`, the squared gradient norm is the sum over the three
directions of the squared norms of the *shared derivative-datum multiplier*
`Paper3.angularDirectionalDerivativeReal` applied to `A`:

`‖∇Z‖²_{H^m} = ∑ⱼ ‖D_j (A)‖²`.

This is exactly the right-hand side of the SL3 dissipation identity `⟪G, datum Δu⟫ = -‖∇u‖²`
expressed through the `∂ⱼ` datum of `D01/DerivativeDatum.lean`.  Combined with the pairing
identity (the remaining gap; see the module docstring) it delivers `hlap`.  The finiteness of
each `∂ⱼ` norm is free from `hA` (a datum norm is never `⊤`), so it is derived internally
rather than assumed. -/
theorem gradientSobolevENorm_toReal_sq_eq_datum_sum {Z : SmoothL2Field Space} (m : ℕ)
    {A : RealVectorSobolev ((m : ℝ) + 1)} (hA : IsSobolevDatum ((m : ℝ) + 1) Z.field A) :
    (gradientSobolevENorm (m : ℝ) Z.field).toReal ^ 2 =
      ∑ j : Fin 3, ‖((WithLp.toLp 2 fun i =>
          angularDirectionalDerivativeReal ((m : ℝ) + 1) (coordinateVector j) (A i)) :
          RealVectorSobolev (m : ℝ))‖ ^ 2 := by
  have hfin : ∀ j : Fin 3, sobolevENorm (m : ℝ) (partialDeriv j Z.field) ≠ ⊤ := by
    intro j
    rw [sobolevENorm_eq (isSobolevDatum_partialDeriv j m hA)]
    exact enorm_ne_top
  rw [gradientSobolevENorm_toReal_sq_eq_sum hfin]
  apply Finset.sum_congr rfl
  intro j _
  rw [sobolevENorm_eq (isSobolevDatum_partialDeriv j m hA), toReal_enorm]

end NSFormalization.Section4.A04
