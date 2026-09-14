import Contracts.V1.Data
import Contracts.V1.TameProduct
import Mathlib

/-!
# Blind writer B — the high-order energy inequality `eq:Rhigh`

Lane `130-SPEC-A04-rhigh-blind`, blind writer **B**.  This file states, from the
paper and the frozen contract vocabulary alone, the display labelled `eq:Rhigh`
in `paper/sections/appendix-a-local-theory.tex:132-137`:

```
½ d/dt ‖u‖²_{H^m} + ν ‖∇u‖²_{H^m}
    ≤ C_m ‖u‖_{H²} ‖u‖_{H^m} ‖∇u‖_{H^m} + ‖f‖_{H^m} ‖u‖_{H^m}.
```

The surrounding paragraph (`:127-137`) reads: "We retain the short energy
argument that yields precisely `eq:criterion`.  For every integer `m ≥ 3`,
pairing the equation with `u` in `H^m`, integrating by parts, and using
`eq:Rproduct` gives [`eq:Rhigh`].  The pressure term vanishes by solenoidality.
These identities are justified by Fourier approximation on compact intervals of
smooth existence."

## Sources actually read (blindness discipline)

* `paper/sections/appendix-a-local-theory.tex:120-150` — the display `eq:Rhigh`
  and its paragraph; the range `m ≥ 3`; "compact intervals of smooth existence";
  the `L²` energy identity `:119-120` for orientation on the `½ (·)' + ν ‖∇·‖²`
  shape.
* `paper/sections/02-preliminaries.tex` — the solution/force/data classes
  (`eq:Rinitial :12`, `eq:Rclasses :17`, `prop:local :105-120`, the lifespan and
  the continuation criterion `eq:criterion :111-114`), and the `L²` energy
  identity `lem:packetenergy :138-139` `½(‖U‖₂²)' + ν‖∇U‖₂² = ⟨F,U⟩`, whose shape
  `eq:Rhigh` generalises to order `H^m`.
* `paper/sections/01-introduction.tex:81-152` — the norm conventions:
  `‖z‖²_{H^s(R³)} = ∫ (1+|ξ|²)^s |ẑ|²`, "for vectors and tensors we sum the
  squared component norms", the `Ḣ^s` weights, `eq:time-norms` and `eq:Enorm`.
* `verification/Contracts/V1/Data.lean` — `SpatialField`, `SpaceTimeField`,
  `sobolevENorm`, `ClassicalSolutionR`, `initialClassR`, `MemForceR`.
* `verification/Contracts/V1/TameProduct.lean` — `gradientSobolevENorm` (`:192`),
  the literal `‖∇v‖_{H^s}` tensor norm `(∑_j ‖∂_jv‖²_{H^s})^{1/2}`.

## Modelling decisions (each with the alternative rejected)

* **Spatial norms are `ENNReal.toReal` of the contract's `ℝ≥0∞` norms.**  Every
  norm the contract exposes (`sobolevENorm`, `gradientSobolevENorm`) is
  `ℝ≥0∞`-valued; `eq:Rhigh` is an inequality between *real* numbers with a real
  time-derivative on the left, so each factor is taken to `ℝ` by `.toReal`.
  *Caveat (`⊤ ↦ 0`):* `ENNReal.toReal ⊤ = 0`, so a `⊤`-valued norm would collapse
  to a junk `0`.  This never happens on the classes quantified here: a
  `ClassicalSolutionR` velocity belongs to `C([0,S];H^m)` for every `m`
  (`ClassicalSolutionR.sobolev`, `02-preliminaries.tex:29`) and `f ∈ F_R` has an
  `H^m` datum at every `t ≥ 0` (`MemForceR`), so every slice has a finite `H^m`
  and `‖∇·‖_{H^m}` norm and `.toReal` is faithful.  *Rejected:* keeping the whole
  inequality in `ℝ≥0∞`.  That cannot carry `d/dt` (there is no derivative of an
  `ℝ≥0∞`-valued path in the sense needed), so the left side would be
  inexpressible.

* **`½ d/dt ‖u‖²_{H^m}` is `deriv` of the real squared-norm, gated by an explicit
  `DifferentiableAt` hypothesis.**  I set `g(t) = (‖u(t)‖_{H^m})² ∈ ℝ`
  (`hmNormSq`) and write the left side as `½ · deriv g t`.  Because `deriv`
  returns `0` for a non-differentiable function — which would make the bound
  vacuously satisfiable — the differentiability of `g` at the interior time `t`
  is stated as an **explicit antecedent** `DifferentiableAt ℝ g t`.  This is the
  time-regularity the display needs: the paper *earns* it through
  `u ∈ C^1_t H^m` ("repeated time differentiation gives `C^j_tH^k_x` regularity
  for all `j,k`", `appendix-a-local-theory.tex:71-76`), but the frozen
  `ClassicalSolutionR` only carries a *continuous* `H^m` datum path
  (`ClassicalSolutionR.sobolev`), so differentiability of `g` is not free from
  the contract and is surfaced as a hypothesis rather than silently assumed.
  *Rejected #1:* `∃ d, HasDerivAt g d t ∧ (½ d + … ≤ …)`, which folds
  differentiability into the conclusion.  It is a fine, slightly stronger
  statement, but the task asks for the regularity as an *explicit hypothesis*, so
  I keep it separate and legible.  *Rejected #2:* differentiating the
  `H^m`-valued datum path in the Hilbert space `RealVectorSobolev m` and taking
  the derivative of `t ↦ ‖G t‖²`; that is the deeper mechanism, but it forces the
  norm through `‖G t‖` (an *upper bound* for `sobolevENorm` until datum
  uniqueness is proved, D01 unit L1), whereas `eq:Rhigh` should speak about the
  canonical `sobolevENorm`.

* **`‖∇u‖_{H^m}` is the gradient's Sobolev norm, `gradientSobolevENorm`, not
  `‖u‖_{H^{m+1}}`.**  The paper writes `‖∇u‖_{H^m}` literally, and the contract
  provides exactly this object at `TameProduct.lean:192`
  (`(∑_j ‖∂_jv‖²_{H^m})^{1/2}`).  *Rejected:* replacing it by `‖u‖_{H^{m+1}}`.
  The two are equivalent up to a constant and lower-order terms but *not equal*,
  and `TameProduct.lean` explicitly lists "the order shift `‖∇v‖_{H^s} ≤
  ‖v‖_{H^{s+1}}`" as out of scope, i.e. a separate fact — so using `H^{m+1}`
  would silently prove a *different* inequality.

* **`C_m` is a single positive family `C : ℕ → ℝ`, existentially quantified
  outside everything.**  `eq:Rhigh`'s `C_m` descends from `eq:Rproduct`'s `C_m`,
  a constant depending only on `m` (and dimension), never on `ν, a, f, T` or the
  solution.  Placing `∃ C, (∀ m, 0 < C m) ∧ …` at the very outside makes this
  independence explicit and matches `TameProductAPI.C : ℕ → ℝ` /
  `TameProductAPI.C_pos`.  *Rejected:* an inner `∃ C > 0` under the `∀`s (a
  constant re-chosen per solution and per `m`); that is strictly weaker and
  misrepresents `C_m` as data-dependent.

* **Range `m ≥ 3`.**  The paragraph says "For every integer `m ≥ 3`"
  (`:129`).  *Rejected:* `m ≥ 2`.  `eq:Rproduct` holds for `m ≥ 2`, but `eq:Rhigh`
  itself is asserted only for `m ≥ 3` (the continuation argument runs on `H³`;
  `eq:tame` and `eq:algebra` used in the paragraph are `k ≥ 3` clauses).

* **Time set: interior times `Ioo 0 T`.**  The identity is justified "on compact
  intervals of smooth existence" and involves the momentum equation, which the
  contract imposes only at interior times (`ClassicalSolutionR.momentum` on
  `Ioo 0 T`).  So the inequality is stated for `t ∈ Set.Ioo 0 T`.  *Rejected:*
  `Ico 0 T`.  The `½(·)'` term needs a two-sided derivative and the equation is
  not imposed at `t = 0`, so the endpoint is excluded.

## Ambiguities in the paper

* The paper never repeats the norm definition inside `eq:Rhigh`; `‖·‖_{H^m}`
  there is the fixed-time spatial `H^m(R³)` norm of `01-introduction.tex:81`, and
  `‖f‖_{H^m}` is the spatial norm of the force *slice* `f(t,·)` (not a time
  Bochner norm), since the whole display is a pointwise-in-time ODE inequality.
* The exact analytic hypothesis that legitimises `d/dt ‖u‖²_{H^m}` is left to the
  appendix's "Fourier approximation on compact intervals of smooth existence"
  and the `C^1_t H^m` claim; I make the display-level consequence
  (differentiability of the scalar `t ↦ ‖u(t)‖²_{H^m}`) an explicit antecedent.
* `C_m` is not shown to be the same symbol as `eq:Rproduct`'s; I take it as a
  positive family, agnostic to its provenance, which is all the display uses.

No `sorry`, no `axiom`; this file is definitions plus one `Prop`.
-/

noncomputable section

namespace BlowupDensity.Research.A04.RhighB

open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.TameProduct
open scoped ENNReal

/-- The fixed-time spatial slice `x ↦ u(t,x)` of a spacetime field, the same
device as `Data.IsSobolevPath` (`fun x => f (t, x)`).  Time is the first
coordinate, matching the contract. -/
def slice (u : SpaceTimeField) (t : ℝ) : SpatialField := fun x => u (t, x)

/-- The real number `‖u(t)‖²_{H^m}`: the square of `Data.sobolevENorm` of the
slice, taken to `ℝ` by `.toReal`.  This is the function whose time derivative is
the left-most term of `eq:Rhigh`.  `⊤ ↦ 0` caveat as in the module docstring;
faithful on `ClassicalSolutionR` velocities, which lie in every `H^m`. -/
def hmNormSq (m : ℕ) (u : SpaceTimeField) (t : ℝ) : ℝ :=
  (sobolevENorm (m : ℝ) (slice u t)).toReal ^ 2

/-- The real number `‖u(t)‖_{H^m}`. -/
def hmNorm (m : ℕ) (u : SpaceTimeField) (t : ℝ) : ℝ :=
  (sobolevENorm (m : ℝ) (slice u t)).toReal

/-- The real number `‖u(t)‖_{H²}`, the low-order factor of the tame nonlinearity
(`eq:tame`, `eq:Rhigh`). -/
def h2Norm (u : SpaceTimeField) (t : ℝ) : ℝ :=
  (sobolevENorm (2 : ℝ) (slice u t)).toReal

/-- The real number `‖∇u(t)‖_{H^m}`, the literal gradient Sobolev norm
`TameProduct.gradientSobolevENorm` (`= (∑_j ‖∂_ju‖²_{H^m})^{1/2}`), **not**
`‖u‖_{H^{m+1}}`. -/
def gradHmNorm (m : ℕ) (u : SpaceTimeField) (t : ℝ) : ℝ :=
  (gradientSobolevENorm (m : ℝ) (slice u t)).toReal

/-- The real number `‖∇u(t)‖²_{H^m}`, the dissipation term of `eq:Rhigh`. -/
def gradHmNormSq (m : ℕ) (u : SpaceTimeField) (t : ℝ) : ℝ :=
  (gradientSobolevENorm (m : ℝ) (slice u t)).toReal ^ 2

/-- The real number `‖f(t)‖_{H^m}`, the spatial `H^m` norm of the force slice at
the fixed time `t` (a pointwise-in-time factor, not a Bochner time norm). -/
def fHmNorm (m : ℕ) (f : SpaceTimeField) (t : ℝ) : ℝ :=
  (sobolevENorm (m : ℝ) (slice f t)).toReal

/-- **`eq:Rhigh`** (`paper/sections/appendix-a-local-theory.tex:132-137`).

For a universal positive family of constants `C_m`, every viscosity `ν > 0`,
initial datum `a ∈ X_R = initialClassR`, force `f ∈ F_R = MemForceR`, classical
solution `w : ClassicalSolutionR ν a f T`, every integer `m ≥ 3`, and every
interior time `t ∈ (0,T)` at which the real map `τ ↦ ‖u(τ)‖²_{H^m}` is
differentiable (the display-level time regularity, earned in the paper by
`u ∈ C^1_t H^m`), the high-order energy inequality

`½ d/dt ‖u‖²_{H^m} + ν ‖∇u‖²_{H^m}`
`  ≤ C_m ‖u‖_{H²} ‖u‖_{H^m} ‖∇u‖_{H^m} + ‖f‖_{H^m} ‖u‖_{H^m}`

holds, with all norms the real (`.toReal`) values of the frozen contract norms,
`‖∇u‖_{H^m}` the gradient Sobolev norm, and `d/dt` the `deriv` of `hmNormSq`. -/
def eqRhigh_B : Prop :=
  ∃ C : ℕ → ℝ, (∀ m : ℕ, 0 < C m) ∧
    ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassR →
    ∀ (f : SpaceTimeField), MemForceR f →
    ∀ (T : ℝ) (w : ClassicalSolutionR ν a f T),
    ∀ m : ℕ, 3 ≤ m →
    ∀ t ∈ Set.Ioo (0 : ℝ) T,
      DifferentiableAt ℝ (hmNormSq m w.velocity) t →
        (1 / 2 : ℝ) * deriv (hmNormSq m w.velocity) t
            + ν * gradHmNormSq m w.velocity t
          ≤ C m * h2Norm w.velocity t * hmNorm m w.velocity t
                * gradHmNorm m w.velocity t
            + fHmNorm m f t * hmNorm m w.velocity t

#check eqRhigh_B

end BlowupDensity.Research.A04.RhighB
