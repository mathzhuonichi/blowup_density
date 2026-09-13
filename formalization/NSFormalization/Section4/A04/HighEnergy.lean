import NSFormalization.Section4.A04.Continuity
import NSFormalization.Section4.A03.OuterTameProduct
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# A04 unit G1: the S-level core of eq:Rhigh on the datum carrier

`research/A04/COMPARISON.md` §4 unit **G1**, `research/A04/G1_SPLIT.md`.  The
target is the all-order energy inequality **eq:Rhigh**
(`paper/sections/appendix-a-local-theory.tex:132-137`,
`research/A04/Spec.lean:424-434` field `energyIdentityHigh`):

`½ (d/dt)‖u‖²_{H^m} + ν‖∇u‖²_{H^m}
   ≤ C_m‖u‖_{H²}‖u‖_{H^m}‖∇u‖_{H^m} + ‖f‖_{H^m}‖u‖_{H^m}`.

G1 is rated **L**: the full statement pairs a *forced viscous* momentum equation
with `u` in `H^m` on the D01 datum carrier, which needs (i) the identification of
`deriv G t` with the datum of `∂ₜu(t)` (unit **D2**, **closed** in
`Section4/A04/TimeDerivative.lean` `timeDeriv_isSobolevDatum`), (ii) the
momentum equation in datum form (A01), (iii) the Laplacian identity
`⟪G, datum Δu⟫ = -‖∇u‖²_{H^m}` (datum-side order shift, `D01/SmoothDatum.lean:388`
open), (iv) the pressure drop `⟪G, datum ∇p⟫ = 0` (needs `∇p` in the carrier at
order `m`, the D01 L9(c) gap), and (v) the inner product on `RealVectorSobolev m`
(lane 053's `Paper3.realSobolevInnerProductSpace`, in PR, not yet on integration).
Those are the **L** sub-lemmas listed in `G1_SPLIT.md` and are *not* proved here.

This module proves the **S** sub-steps that need nothing open:

* `inner_energy_assembly` / `inner_energy_Rhigh` — the Cauchy–Schwarz/pairing
  arithmetic that turns the datum-form pairing (`d = 2⟪G, Gt⟫` from D1, the
  momentum decomposition, the Laplacian identity and the pressure drop) into
  eq:Rhigh's displayed right-hand side.  Stated on a **generic** real inner
  product space `E`, so it compiles without lane 053's carrier instance and is
  reused verbatim by the L-lemma at `E = RealVectorSobolev m`.  The dissipation
  is absorbed exactly (this is eq:Rhigh, *before* Young — unit G2 does Young),
  the pressure term is folded by `⟪G, P⟫ = 0`, and the force term is discharged
  by genuine Cauchy–Schwarz (`real_inner_le_norm`).
* `outerSobolevNormAt_le` / `outerNormAt_le` — the transport of the registered
  tame bound `A03.outerProductTame`
  (`‖u ⊗ u‖_{H^m} ≤ Ctame m · ‖u‖_{H²}‖u‖_{H^m}`, `A03/OuterTameProduct.lean:157`)
  from `ℝ≥0∞` to the real datum norms `sobolevNormAt`, given the finiteness the
  smooth class supplies (unit **N1**, `Continuity.lean`).  This is the `‖u⊗u‖`
  factor of the nonlinear pairing after the integration by parts of `∇·(u⊗u)`
  (an L sub-lemma) and Cauchy–Schwarz.  The registered constant is
  `A03.outerTameConst m`, which the contract exposes as `TameProductAPI.Ctame`
  (`Bindings/TameProduct.lean:102`); the implementation may take
  `Chigh m = Ctame m` (`Spec.lean:332`), and `A03.outerTameConst_pos` gives
  `Chigh_pos`.

`NSFormalization` cannot import `Contracts.*`, so the tame bound is consumed
through the *local* `NSFormalization.Section4.A03.outerProductTame`, the theorem
the binding `Bindings/TameProduct.lean:122` points `TameProductAPI.outerProductTame`
at, not through the contract field.

Template for the full assembly: `EulerOrdinarySobolev.integer_energy_tame`
(`vendor/NavierStokesAndEuler/Euler/OrdinaryTameEnergy.lean:123`), same
`abs_real_inner_le_norm` + tame-product shape, on the jet carrier with no
dissipation and no force.
-/

noncomputable section

open NavierStokes.ProblemStatement
open scoped RealInnerProductSpace

namespace NSFormalization.Section4.A04

open NSFormalization.Section4.A02 (SpaceTimeField)
open NSFormalization.Section4.D01 (sobolevENorm)
open NSFormalization.Section4.A03
  (MemHmVector outerSobolevENorm outerTameConst outerTameConst_pos outerProductTame)

/-! ## 1. The pairing arithmetic (pure inner-product space)

These are the last algebraic step of eq:Rhigh: given the datum-form pairing of
the momentum equation, they produce the displayed bound.  They are stated on an
arbitrary real inner product space `E`, so they carry no dependency on the
still-open carrier instance and are reusable by the L-lemma at
`E = RealVectorSobolev m`.  The named hypotheses are exactly the interfaces the L
sub-lemmas of `G1_SPLIT.md` supply. -/

/-- **G1, arithmetic core.**  On a real inner product space, from
* `hν`   : `0 ≤ ν` (`energyIdentityHigh` has `0 < ν`);
* `hd`   : the D1 derivative, `d = 2⟪G, Gt⟫`;
* `hmom` : the momentum equation in datum form, `Gt = ν•L - N - P + F`
  (`L` = datum of `Δu`, `N` = datum of the nonlinearity `(u·∇)u`, `P` = datum of
  `∇p`, `F` = datum of `f`);
* `hlap` : the Laplacian/dissipation bound `⟪G, L⟫ ≤ -grad²`
  (`grad = ‖∇u‖_{H^m}`);
* `hpr`  : the pressure drop `⟪G, P⟫ = 0` (solenoidality);
* `hnl`  : the nonlinear pairing bound `-⟪G, N⟫ ≤ NLbound`;
* `hG`   : `‖G‖ = uNorm`;   `hF` : `‖F‖ = fNorm`,

the energy inequality `½ d + ν grad² ≤ NLbound + fNorm·uNorm` holds.  The force
term is the only pairing bounded *inside* this lemma, by Cauchy–Schwarz
(`real_inner_le_norm`); the dissipation is absorbed exactly (no Young), matching
eq:Rhigh before the G2 step.  `hlap` is stated as `≤` (not `=`) so the lemma
absorbs an SL3 that only proves the datum-carrier order shift as an inequality
(`REVIEW_G1.md` finding 4); the exact manuscript identity is a special case. -/
theorem inner_energy_assembly {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {G Gt N P L F : E} {ν grad NLbound uNorm fNorm d : ℝ} (hν : 0 ≤ ν)
    (hd : d = 2 * ⟪G, Gt⟫)
    (hmom : Gt = ν • L - N - P + F)
    (hlap : ⟪G, L⟫ ≤ - grad ^ 2)
    (hpr : ⟪G, P⟫ = 0)
    (hnl : - ⟪G, N⟫ ≤ NLbound)
    (hG : ‖G‖ = uNorm)
    (hF : ‖F‖ = fNorm) :
    (1 / 2) * d + ν * grad ^ 2 ≤ NLbound + fNorm * uNorm := by
  have hexpand : ⟪G, Gt⟫ = ν * ⟪G, L⟫ - ⟪G, N⟫ + ⟪G, F⟫ := by
    rw [hmom]
    simp only [inner_add_right, inner_sub_right, real_inner_smul_right, hpr]
    ring
  have hcs : ⟪G, F⟫ ≤ fNorm * uNorm := by
    have h := real_inner_le_norm G F
    rw [hG, hF, mul_comm uNorm fNorm] at h
    exact h
  have hlap' : ν * ⟪G, L⟫ ≤ - (ν * grad ^ 2) := by
    have h := mul_le_mul_of_nonneg_left hlap hν
    nlinarith [h]
  have hsum : (1 / 2) * d + ν * grad ^ 2 = ν * ⟪G, L⟫ - ⟪G, N⟫ + ⟪G, F⟫ + ν * grad ^ 2 := by
    rw [hd, hexpand]; ring
  rw [hsum]; nlinarith [hnl, hcs, hlap']

/-- **G1, eq:Rhigh's displayed right-hand side.**  Specialising
`inner_energy_assembly` at `NLbound = C · u2 · uNorm · grad` gives the literal
shape of `energyIdentityHigh` (`Spec.lean:429-434`): with `C = Chigh m`,
`u2 = ‖u‖_{H²}`, `uNorm = ‖u‖_{H^m}`, `grad = ‖∇u‖_{H^m}`, `fNorm = ‖f‖_{H^m}`,

`½ d + ν grad² ≤ C·u2·uNorm·grad + fNorm·uNorm`.

The nonlinear bound `hnl : -⟪G, N⟫ ≤ C·u2·uNorm·grad` is what the outer-product
integration by parts, Cauchy–Schwarz, and `outerNormAt_le` below deliver (the L
sub-lemma); every other input is D1 (`hd`), D2, N1 (`hG`, `hF`) or the momentum
equation. -/
theorem inner_energy_Rhigh {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {G Gt N P L F : E} {ν grad C u2 uNorm fNorm d : ℝ} (hν : 0 ≤ ν)
    (hd : d = 2 * ⟪G, Gt⟫)
    (hmom : Gt = ν • L - N - P + F)
    (hlap : ⟪G, L⟫ ≤ - grad ^ 2)
    (hpr : ⟪G, P⟫ = 0)
    (hnl : - ⟪G, N⟫ ≤ C * u2 * uNorm * grad)
    (hG : ‖G‖ = uNorm)
    (hF : ‖F‖ = fNorm) :
    (1 / 2) * d + ν * grad ^ 2 ≤ C * u2 * uNorm * grad + fNorm * uNorm :=
  inner_energy_assembly hν hd hmom hlap hpr hnl hG hF

/-! ## 2. The tame product bound on the real datum norms

`A03.outerProductTame` is an inequality in `ℝ≥0∞`; the energy estimate needs it on
the real numbers `sobolevNormAt` measures the solution with.  The transport is
pure `ENNReal.toReal` monotonicity, valid because the two factor norms are finite
on the smooth class (unit **N1**, `sobolevENorm_velocity_ne_top` in
`Continuity.lean`) — the outer norm's finiteness is then automatic from the
bound. -/

/-- **G1, tame transport.**  The real form of `A03.outerProductTame`: for a field
`z` in `MemHmVector m` with finite order-`2` and order-`m` norms,

`‖z ⊗ z‖_{H^m} ≤ Ctame m · (‖z‖_{H²} · ‖z‖_{H^m})`   (all `.toReal`),

with `Ctame m = A03.outerTameConst m`.  No new analytic content: `toReal` of the
registered `ℝ≥0∞` inequality, whose right side is finite by hypothesis. -/
theorem outerSobolevNormAt_le {m : ℕ} (hm : 2 ≤ m) {z : Space → Space}
    (hz : MemHmVector m z)
    (h2 : sobolevENorm 2 z ≠ ⊤) (hmz : sobolevENorm (m : ℝ) z ≠ ⊤) :
    (outerSobolevENorm (m : ℝ) z z).toReal
      ≤ outerTameConst m * ((sobolevENorm 2 z).toReal * (sobolevENorm (m : ℝ) z).toReal) := by
  have hb := outerProductTame m hm hz
  have hfin : ENNReal.ofReal (outerTameConst m) *
      (sobolevENorm 2 z * sobolevENorm (m : ℝ) z) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top h2 hmz)
  calc (outerSobolevENorm (m : ℝ) z z).toReal
      ≤ (ENNReal.ofReal (outerTameConst m) *
          (sobolevENorm 2 z * sobolevENorm (m : ℝ) z)).toReal :=
        ENNReal.toReal_mono hfin hb
    _ = outerTameConst m * ((sobolevENorm 2 z).toReal * (sobolevENorm (m : ℝ) z).toReal) := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (outerTameConst_pos m).le,
          ENNReal.toReal_mul]

/-- **G1, tame transport on `sobolevNormAt`.**  `outerSobolevNormAt_le` on a
spacetime slice `x ↦ u(t,x)`, with the right side written in the real solution
norm `sobolevNormAt` the differential fields use (definitional unfolding of
`sobolevNormAt s u t = (sobolevENorm s (u t·)).toReal`):

`‖u(t) ⊗ u(t)‖_{H^m} ≤ Ctame m · (sobolevNormAt 2 u t · sobolevNormAt m u t)`. -/
theorem outerNormAt_le {m : ℕ} (hm : 2 ≤ m) {u : SpaceTimeField} {t : ℝ}
    (hz : MemHmVector m (fun x : Space => u (t, x)))
    (h2 : sobolevENorm 2 (fun x : Space => u (t, x)) ≠ ⊤)
    (hmz : sobolevENorm (m : ℝ) (fun x : Space => u (t, x)) ≠ ⊤) :
    (outerSobolevENorm (m : ℝ) (fun x => u (t, x)) (fun x => u (t, x))).toReal
      ≤ outerTameConst m * (sobolevNormAt 2 u t * sobolevNormAt (m : ℝ) u t) :=
  outerSobolevNormAt_le hm hz h2 hmz

end NSFormalization.Section4.A04
