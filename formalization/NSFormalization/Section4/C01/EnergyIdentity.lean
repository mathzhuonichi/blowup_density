import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# C01 unit E0: the arithmetic core of the ordinary energy identity eq:RL2 (`m = 0`)

Lane `131-C01-energy-split`, graph node `C01`
(`formalization/blueprint/DEPENDENCY_GRAPH.md:275-281`).  The ordinary energy
identity eq:RL2 (`paper/sections/04-whole-space.tex:117`, spec field
`research/C01/Spec.lean:344` `energyIdentity`) is the `m = 0` cousin of eq:Rhigh
(`appendix-a-local-theory.tex:132`, proved for `m ≥ 3` in
`Section4/A04/EnergyIdentityHigh.lean`): the projected momentum equation paired
with `u` in `L² = H⁰`.  At order `0` the manuscript's estimate is an **exact
identity**, not an inequality, because two of the three pairings cancel *exactly*
rather than being bounded:

* the pressure term drops by solenoidality, `⟪G, P⟫ = 0`
  (`Section4/A04/PressureDrop.lean:216` `pressure_drop`, which carries no
  `2 ≤ m` hypothesis and so is available at order `0`);
* the nonlinear transport term **vanishes exactly**, `⟪G, N⟫ = 0`
  (`⟨(u·∇)u, u⟩ = 0`, solenoidal skew-symmetry), rather than being bounded as in
  eq:Rhigh; and
* the Laplacian pairing is the **exact** dissipation `⟪G, L⟫ = -‖∇u‖²`
  (`Section4/A04/LaplacianAssembly.lean:306` `inner_datum_laplacian`, an equality
  and, like `pressure_drop`, free of any `2 ≤ m` hypothesis), whereas eq:Rhigh
  uses only the inequality half `inner_datum_laplacian_le`.

## What this module proves

The **arithmetic step** of eq:RL2, on a generic real inner product space `E`,
exactly as `Section4/A04/HighEnergy.lean:100` `inner_energy_assembly` proves the
arithmetic step of eq:Rhigh — but with the three cancellations entered as
*equalities* so the conclusion is the manuscript's exact identity:

`½ d + ν · grad² = ⟪G, F⟫`   (`inner_energy_identity`), and its derivative form

`d = -2ν · grad² + 2 · ⟪G, F⟫`   (`inner_energy_identity_deriv`),

from
* `hd`   : the D1 derivative `d = 2⟪G, Gt⟫`;
* `hmom` : the momentum equation in datum form `Gt = ν • L - N - P + F`;
* `hlap` : the **exact** dissipation `⟪G, L⟫ = -grad²`;
* `hpr`  : the pressure drop `⟪G, P⟫ = 0`;
* `hnl`  : the **exact** nonlinear vanishing `⟪G, N⟫ = 0`.

`inner_energy_identity_deriv`'s conclusion `d = -2ν grad² + 2⟪G, F⟫` is precisely
the derivative value of `energyIdentity` (`Spec.lean:348-350`,
`(‖u‖²)' = -2ν‖∇u‖² + 2⟨u, f⟩`) once the datum-carrier quantities are read through
the order-0 Plancherel/Parseval bridges (`grad² = gradientSq`,
`⟪G, F⟫ = pairing u f`).  Those bridges, the exact nonlinear vanishing `hnl`, and
the order-0 momentum equation `hmom` (`Section4/A04/MomentumDatum.lean`'s
`momentum_datum` needs `2 ≤ m`) are the still-open inputs recorded in
`research/C01/ENERGY_SPLIT.md`; this lemma is the algebra that consumes them,
carrier-agnostic and reusable verbatim at `E = RealVectorSobolev 0`, matching the
generic-`E` device of `inner_energy_assembly`.

No analysis, no `2 ≤ m`, no open lemma: the two theorems below are pure
inner-product algebra, the exact analogue of `inner_energy_assembly` with `≤`
replaced by `=` in the three pairing hypotheses.
-/

noncomputable section

open scoped RealInnerProductSpace

namespace NSFormalization.Section4.C01

/-- **E0, the exact energy-identity arithmetic core.**  On a real inner product
space, from
* `hd`   : `d = 2⟪G, Gt⟫` (the D1 derivative of `‖u‖²_{H⁰}`);
* `hmom` : `Gt = ν • L - N - P + F` (the momentum equation in datum form, with
  `L` = datum of `Δu`, `N` = datum of `(u·∇)u`, `P` = datum of `∇p`, `F` = datum
  of `f`);
* `hlap` : `⟪G, L⟫ = -grad²` (the **exact** dissipation, `inner_datum_laplacian`);
* `hpr`  : `⟪G, P⟫ = 0` (the pressure drop, `pressure_drop`);
* `hnl`  : `⟪G, N⟫ = 0` (the **exact** nonlinear vanishing, `⟨(u·∇)u, u⟩ = 0`),

the exact ordinary energy identity `½ d + ν grad² = ⟪G, F⟫` holds
(`04-whole-space.tex:117`, `½(‖u‖₂²)' + ν‖∇u‖₂² = ⟨f, u⟩`).  This is the exact
analogue of `A04.inner_energy_assembly`: same expansion of `⟪G, Gt⟫`, but the
dissipation and nonlinear pairings are entered as equalities, so the force term
is *not* bounded by Cauchy–Schwarz and the conclusion is an identity. -/
theorem inner_energy_identity {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {G Gt N P L F : E} {ν grad d : ℝ}
    (hd : d = 2 * ⟪G, Gt⟫)
    (hmom : Gt = ν • L - N - P + F)
    (hlap : ⟪G, L⟫ = - grad ^ 2)
    (hpr : ⟪G, P⟫ = 0)
    (hnl : ⟪G, N⟫ = 0) :
    (1 / 2) * d + ν * grad ^ 2 = ⟪G, F⟫ := by
  have hexpand : ⟪G, Gt⟫ = ν * ⟪G, L⟫ - ⟪G, N⟫ + ⟪G, F⟫ := by
    rw [hmom]
    simp only [inner_add_right, inner_sub_right, real_inner_smul_right, hpr]
    ring
  rw [hd, hexpand, hlap, hnl]; ring

/-- **E0, derivative form.**  The same hypotheses as `inner_energy_identity` give
the derivative value `energyIdentity` (`research/C01/Spec.lean:348-350`) asserts:

`d = -2ν · grad² + 2 · ⟪G, F⟫`,

i.e. `(‖u‖²_{H⁰})' = -2ν‖∇u‖²_{H⁰} + 2⟪G, F⟫`.  A one-line rearrangement of
`inner_energy_identity`. -/
theorem inner_energy_identity_deriv {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {G Gt N P L F : E} {ν grad d : ℝ}
    (hd : d = 2 * ⟪G, Gt⟫)
    (hmom : Gt = ν • L - N - P + F)
    (hlap : ⟪G, L⟫ = - grad ^ 2)
    (hpr : ⟪G, P⟫ = 0)
    (hnl : ⟪G, N⟫ = 0) :
    d = -2 * ν * grad ^ 2 + 2 * ⟪G, F⟫ := by
  linear_combination (2 : ℝ) * inner_energy_identity hd hmom hlap hpr hnl

end NSFormalization.Section4.C01
