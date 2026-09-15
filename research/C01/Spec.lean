import Contracts.V1.Data
import Contracts.V1.GradientL6

/-!
# C01 draft specification: ordinary energy and `H¹` absorption on `R³`

Task `collaboration/tasks/C01.md`, graph node `C01` in
`formalization/blueprint/DEPENDENCY_GRAPH.md:275-281` (`C01 ← A02, A05`;
consumers `C01 → R43`, `C01 → R44`).

This file is a **specification draft only**.  It contains `def`s and one
`structure` of obligations.  It proves nothing with mathematical content,
assumes nothing, and introduces no `axiom`, no `sorry` and no abstract `Prop`
placeholder field: every propositional field is a fully spelled-out statement
about explicitly named objects.

## What is specified

The two *a priori* estimates that Propositions 4.3 and 4.4 quote by name, plus
the assembly they both finish with:

* **eq:RL2** (`paper/sections/04-whole-space.tex:117-121`), "The separate
  ordinary energy identity, with regularized norm division, supplies
  `‖u(t)‖₂ ≤ ‖a‖₂ + ∫₀^t‖f(s)‖₂ ds =: K(t)`".  This is the low-frequency
  control that eq:RH1 explicitly does **not** provide (`:116`, "It does not
  control low frequencies by itself"); on `R³` there is no Poincaré inequality
  and no spectral gap to recover it from the dissipation
  (`04-whole-space.tex:4-5`).  Stated below in three pieces: the exact energy
  identity `energyIdentity`, its Cauchy-Schwarz differential form
  `energyDifferentialBound`, and the integrated display `l2Bound`.
* **eq:RH1** (`paper/sections/04-whole-space.tex:113-116`),
  `(‖∇u‖₂²)' + ν‖Δu‖₂² ≤ Cν^{-1}‖f‖₂²`, valid once the critical norm is small
  enough to absorb the nonlinearity.  Stated below as the enstrophy identity
  `enstrophyIdentity`, the two nonlinear steps `trilinearHolder` and
  `trilinearAbsorbed` (`:107-112`), the differential display
  `enstrophyDifferentialBound`, and the integrated form
  `enstrophyIntegralBound`.
* **the continuation assembly** (`04-whole-space.tex:121-131`): the `H²`
  Fourier inequality `‖u‖²_{H²} ≤ C(‖u‖₂² + ‖Δu‖₂²)` (`:123`) and the resulting
  `∫₀^S‖u(t)‖²_{H²}dt ≤ CSK(S)² + Cν^{-1}‖∇a‖₂² + Cν^{-2}∫₀^S‖f(t)‖₂²dt < ∞`
  (`:127-130`).  `h2TimeIntegral` is the general-`a` form that
  `research/section4/STATEMENTS.md:494-497` books as C01 item 3 for R43;
  `h2TimeIntegralZeroDatum` is its `a = 0` instance, which is the shape
  `STATEMENTS.md:604-606` records for R44 ("here with `a = 0`, so
  `K(S) = ∫₀^S‖f‖₂` and `‖∇a‖₂ = 0`").

## Out of scope, and asserted nowhere below

* **eq:Rcritical1** (`04-whole-space.tex:97-99`, `½(y²)'+(ν−C₀y)z² ≤ by`) and
  **eq:Rcritical2** (`:161-164`, `(Y²)'+νZ² ≤ C₂νY²+C₃ν^{-1}B²`).  These are the
  *critical* `Ḣ^{1/2}` / `H^{1/2}` estimates obtained by testing against `Λu`
  and `Ju`; `STATEMENTS.md:449-455` and `:576-582` book them inside R43's and
  R44's own proofs, not as C01 items.  Everything C01 exports is stated in
  `L²`, `Ḣ¹` and `H²` quantities of the physical field, with the critical norm
  entering **only** as the scalar smallness hypothesis `C₁‖u‖₃ ≤ ν/4` that
  `STATEMENTS.md:604` records verbatim.
* The Grönwall step of Proposition 4.4 (`04-whole-space.tex:165-170`) and its
  first-crossing argument; the continuity bootstrap of Proposition 4.3
  (`:103`).  Both are consequences of the critical estimates just excluded.
* The continuation criterion `eq:criterion` itself — **A04**
  (`02-preliminaries.tex:108`).  C01 stops at the finiteness of
  `∫₀^S‖u‖²_{H²}`; that this forces an extension is A04's clause.
* Every torus statement, every `Λ`, `J`, `Ḣ^{1/2}`, `Ḣ^{3/2}` and `H^{-1/2}`
  quantity, and the Leray projection.

## Why no Leray projection appears

`04-whole-space.tex:96` and `:107` test *the projected equation*.  Every field
below is instead a `Data.ClassicalSolutionR`, which carries the unprojected
`02-preliminaries.tex` eq:NS momentum balance together with a pressure
(`Data.lean:624-648`).  The two tests differ by the pressure terms
`⟨∇p, u⟩` and `⟨∇p, Δu⟩`, both of which vanish for a divergence-free field with
`∇p ∈ L²` (`ClassicalSolutionR.divergence`, `.pressure_gradient`).  Writing the
estimates on the unprojected solution therefore loses nothing and keeps C01
free of an unregistered `⟪D01:Leray⟫`; the two vanishing pairings are proof
obligations of the identity clauses, not separate fields.

## Conventions

* Every object quantified over is the canonical one of
  `verification/Contracts/V1/Data.lean`: `initialClassR` is `X_R`, `MemForceR`
  is `F_R`, `ClassicalSolutionR ν a f T` is the classical solution on `[0,T)`,
  `sobolevENorm` is `‖·‖_{H^s}`, `MemHInfty` is `H^∞`.  Nothing here redefines
  a D01 object.
* `gradientTensor`, `laplacian` and `SmoothSquareIntegrableJets` are the
  **registered** `Contracts.V1.GradientL6` objects
  (`verification/Contracts/V1/GradientL6.lean:89,94,106`), so that the
  registered clause `GradientL6API.gradientLSix` applies verbatim to the
  velocity slices appearing below, with no restatement and no conversion.  The
  whole registered API is carried as the field `gradientL6`, the same device
  `research/A02/Spec.lean:336` uses for `UniquenessAPI`.
* `gradientTensor (slice u t)` unfolds to `Data.spatialGradient u t`, and
  `laplacian (slice u t)` to `spatialLaplacian u t`, because
  `Contracts.V1.lift ∘ slice` is the identity on a fixed time slab; so the
  gradient quantity below is literally the one `Data.energyGradient`
  (`Data.lean:459`) integrates in `E_T`, in the Frobenius assembly of
  `01-introduction.tex:103`.
* **Which norms are real and which are `ℝ≥0∞`.**  The manuscript's estimates
  are *differential*, so the squared `L²` quantities must be real-valued for
  `HasDerivAt` to apply to them.  They are written as plain Bochner integrals
  of nonnegative functions, the same form the registered
  `GradientL6API.hessianLaplacianIdentity` (`GradientL6.lean:130-135`) uses.
  Mathlib returns `0` for a non-integrable Bochner integral, so the clause
  `velocityJets` — which puts every velocity slice in
  `SmoothSquareIntegrableJets` — is what makes each of them honest, and it is
  listed first for that reason.  Where a quantity is only ever *compared*, and
  never differentiated, it stays `ℝ≥0∞` and is never routed through `.toReal`:
  the critical `L³` norm (hypothesis side, so `⊤` makes a clause vacuous, the
  fail-safe direction), the `H²` datum norm `sobolevENorm`, and the `L⁶`
  gradient norm of the registered clause.  Exactly two statements cross between
  the two systems, and both are explicit fields: `sobolevTwoFourier` (the
  paper's own `H²` inequality) and `laplacianSqENorm` (an equality for
  `‖Δz‖₂²`).  Neither uses `.toReal`.

## The four bridges C01 owns

Four clauses below are *not* Section 4 displays but the conversions the
displays need.  They are named here so a reviewer can find them:

1. `velocityJets` — a classical velocity slice is an `H^∞` field in both the
   datum sense (`Data.MemHInfty`) and the jet sense
   (`Contracts.V1.SmoothSquareIntegrableJets`).  `ClassicalSolutionR.sobolev`
   (`Data.lean:643`) gives only the datum form, and the equivalence of the two
   forms is D01 unit L2, booked at `Data.lean:487-491` and recorded as **open
   in the datum ⟹ jet direction** by
   `verification/Contracts/V1/BoundedRepresentative.lean:71-74`.  Without this
   clause the registered `gradientLSix` cannot be applied to a velocity slice
   at all.
2. `forceTimeRegularity` — the `L¹_t` and `L²_t` finiteness that
   `02-preliminaries.tex:18` eq:Rclasses puts on `F_R`, transported from the
   Bochner datum path of `MemForceR` to the interval integrals of eq:RL2 and
   eq:RH1.  `04-whole-space.tex:171` leans on exactly this ("its `L^1_tL^2_x`
   and `L^2_tL^2_x` norms are finite, even though they are not required to be
   small").
3. `sobolevTwoFourier` — the Fourier inequality of `04-whole-space.tex:123`.
   `STATEMENTS.md:478-479` books it as a D01 need, but `Data.lean` contains
   definitions only, so C01 states it as the ingredient of its own assembly.
4. `laplacianSqENorm` — the `ℝ≥0∞ ↔ ℝ` conversion for `‖Δz‖₂²`, without which
   the two trilinear fields (`ℝ≥0∞`) cannot be combined with the three
   enstrophy fields (`ℝ`).  It carries no analysis; it is here because a
   contract that cannot be composed with itself is a contract that only
   documents.
-/

noncomputable section

namespace BlowupDensity.C01.Draft

open Set MeasureTheory
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1
  (lift gradientTensor laplacian SmoothSquareIntegrableJets GradientL6API)
open BlowupDensity.Contracts.V1.Data
open scoped ContDiff ENNReal

/-! ## 1. Time slices and the real-valued squared quantities

`04-whole-space.tex:107-131` writes every quantity as a function of time, of a
spatial norm of the slice `u(t)`.  These are those functions.  Each is a plain
Bochner integral of a nonnegative (or, for the two work integrals, integrable)
function; `EnergyAbsorptionAPI.velocityJets` is what supplies the integrability
that makes them faithful. -/

/-- The spatial slice `z(t) = z(t,·)` of a spacetime field.  Time is the first
spacetime coordinate (`Data.lean:38-40`), and this is the same slicing
`Data.energyEssSup` (`Data.lean:444`) and `Data.IsSobolevPath` (`:174`) use. -/
def slice (z : SpaceTimeField) (t : ℝ) : SpatialField := fun x => z (t, x)

/-- `04-whole-space.tex:119` eq:RL2, the square of `‖z‖₂`: the ordinary squared
`L²(R³)` norm of a spatial field, `∫|z|²`.  Real-valued, because eq:RL2 is
derived from a differential inequality for it. -/
def l2Sq (z : SpatialField) : ℝ := ∫ x : Space, ‖z x‖ ^ 2

/-- `04-whole-space.tex:119` eq:RL2, `‖z‖₂` itself.  The square root is taken
of `l2Sq`, so this is the quantity whose regularized division by
`(y²+ζ²)^{1/2}` (`:100`) produces eq:RL2. -/
def l2Norm (z : SpatialField) : ℝ := Real.sqrt (l2Sq z)

/-- `04-whole-space.tex:114` eq:RH1, `‖∇z‖₂²`: the squared `L²` norm of the
gradient **tensor**, in the Frobenius assembly `(∑_{i,j}|∂_iz_j|²)^{1/2}` of
`01-introduction.tex:103`.  `gradientTensor` is the registered
`Contracts/V1/GradientL6.lean:89` object, which is `Data.spatialGradient`
(`Data.lean:453`) on the time-independent lift; so this is also the integrand
of `Data.energyGradient` (`Data.lean:459`), the second summand of `E_T`. -/
def gradientSq (z : SpatialField) : ℝ := ∫ x : Space, ‖gradientTensor z x‖ ^ 2

/-- `04-whole-space.tex:109,115`, `‖Δz‖₂²`: the squared `L²` norm of the
componentwise Euclidean Laplacian `∑ᵢ∂ᵢ∂ᵢz`.  `laplacian` is the registered
`Contracts/V1/GradientL6.lean:94` object, so this is literally the right-hand
side of the registered `GradientL6API.gradientLSix`. -/
def laplacianSq (z : SpatialField) : ℝ := ∫ x : Space, ‖laplacian z x‖ ^ 2

/-- `04-whole-space.tex:108`, `⟨w, z⟩`: the real `L²(R³;R³)` pairing,
`⟪D01:pairing⟫` of `research/section4/STATEMENTS.md:482`.  Used for the forcing
work `⟨f,u⟩` of the energy identity and for `⟨f,Δu⟩` in eq:RH1. -/
def pairing (w z : SpatialField) : ℝ := ∫ x : Space, (inner ℝ (w x) (z x) : ℝ)

/-- `04-whole-space.tex:108`, `⟨(u·∇)u, Δu⟩`: the nonlinear work against the
Laplacian, the single term eq:RH1 has to absorb.  `advection` is the pinned
upstream `(u·∇)u` (`vendor/NavierStokesAndEuler/NavierStokes/ProblemStatement.lean:63`)
on the time-independent lift, matching `laplacian` and `gradientTensor`. -/
def advectionWork (z : SpatialField) : ℝ :=
  ∫ x : Space, (inner ℝ (advection (lift z) 0 x) (laplacian z x) : ℝ)

/-- `04-whole-space.tex:109,171`, `‖z‖₃`: the critical Lebesgue norm in which
the absorption hypothesis is stated.  Kept in `ℝ≥0∞` and never differentiated:
it appears only on the hypothesis side, where the fail-safe value `⊤` makes a
clause vacuous rather than satisfiable.  This is the left-hand side of A05's
`velocityCriticalL3` (`research/A05/Spec.lean`, `‖u‖₃ ≤ Cy`) and of the `‖u‖₃ ≤ CY`
of `04-whole-space.tex:171`, which is how R43 and R44 respectively discharge
it. -/
def criticalL3 (z : SpatialField) : ℝ≥0∞ := eLpNorm z 3 volume

/-- `04-whole-space.tex:119` eq:RL2, `∫₀^t‖f(s)‖₂ ds`: the forcing primitive.
The time integral is the ordinary interval integral, so `t ≥ 0` is intended
throughout; `EnergyAbsorptionAPI.forceTimeRegularity` supplies the interval
integrability that keeps it from being Mathlib's junk `0`. -/
def forcePrimitive (f : SpaceTimeField) (t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, l2Norm (slice f s)

/-- `04-whole-space.tex:119` eq:RL2, `K(t) = ‖a‖₂ + ∫₀^t‖f(s)‖₂ ds`: the entire
right-hand side of eq:RL2, named as the manuscript names it, so that R43's and
R44's assembly can quote `K(S)` directly (`:127-128`). -/
def energyBudget (a : SpatialField) (f : SpaceTimeField) (t : ℝ) : ℝ :=
  l2Norm a + forcePrimitive f t

/-! ## 2. The contract

All constants are structure fields, hence quantified **outside** every
viscosity, every datum and every solution.  This is the universal-constant
discipline of `research/section4/STATEMENTS.md:483-485`: `C₁` must be `ν`-free,
because the smallness threshold `ν/(4C₁)` is what R43 turns into the `cν`-ball
of Theorem 4.1's converse. -/

/-- **Ordinary energy and `H¹` absorption on `R³`** — eq:RL2, eq:RH1 and the
squared-`H²` time integrability they combine to give
(`paper/sections/04-whole-space.tex:96-131`, reused at `:171`).

The hypotheses are, uniformly: a viscosity `ν > 0`, an initial velocity in
`X_R`, a force in `F_R`, and a classical solution of that datum on `[0,T)`.
No smallness is assumed anywhere except in the single scalar hypothesis
`C₁‖u(t)‖₃ ≤ ν/4` of the `H¹` clauses, which is the manuscript's own
(`04-whole-space.tex:112`, "Decrease `c` so that `C₁y ≤ ν/4`") in the form
`research/section4/STATEMENTS.md:604` records for both consumers. -/
structure EnergyAbsorptionAPI where
  /-- `appendix-b-embeddings.tex:32` and `04-whole-space.tex:110-112`: the
  **registered** gradient-`L⁶` contract
  (`verification/Contracts/V1/GradientL6.lean:118`), carried whole rather than
  restated, so that `trilinearAbsorbed` below is the manuscript's own
  derivation of `≤ C₁y‖Δu‖₂²` from `≤ ‖u‖₃‖∇u‖₆‖Δu‖₂` and not an independent
  assumption.  Same device as `research/A02/Spec.lean:336`. -/
  gradientL6 : GradientL6API
  /-- `04-whole-space.tex:110`, the constant of `‖u‖₃‖∇u‖₆‖Δu‖₂ ≤ C₁y‖Δu‖₂²`,
  read through `‖u‖₃` rather than through `y = ‖Λ^{1/2}u‖₂` as
  `research/section4/STATEMENTS.md:604` does ("`H¹` absorption once
  `C₁‖u‖₃ ≤ ν/4`").  Reading it through `‖u‖₃` is what makes one clause serve
  both consumers: R43 reaches the hypothesis by `‖u‖₃ ≤ Cy` (`:93`) and R44 by
  `‖u‖₃ ≤ CY ≤ Cθν` (`:171`).  The proof may take `C₁ = gradientL6.Csix`; the
  contract does not fix that, only that one `ν`-free constant serves. -/
  C₁ : ℝ
  /-- Positivity of `C₁`; it is a divisor in the threshold `ν/(4C₁)`. -/
  C₁_pos : 0 < C₁
  /-- `04-whole-space.tex:115`, the `C` of eq:RH1's right-hand side
  `Cν^{-1}‖f‖₂²`.  Universal: independent of `ν`, of the datum and of the
  solution. -/
  CRH1 : ℝ
  /-- Positivity of `CRH1`. -/
  CRH1_pos : 0 < CRH1
  /-- `04-whole-space.tex:123`, the `C` of the Fourier inequality
  `‖u‖²_{H²} ≤ C(‖u‖₂² + ‖Δu‖₂²)`. -/
  CH2 : ℝ
  /-- Positivity of `CH2`. -/
  CH2_pos : 0 < CH2
  /-- `04-whole-space.tex:127-130`, the single `C` of the three summands of the
  assembly `CSK(S)² + Cν^{-1}‖∇a‖₂² + Cν^{-2}∫₀^S‖f‖₂²`.  The manuscript writes
  one letter for all three; so does this field. -/
  Cassembly : ℝ
  /-- Positivity of `Cassembly`. -/
  Cassembly_pos : 0 < Cassembly

  /-- **Bridge 1.**  `02-preliminaries.tex:29-30`, "a classical velocity belongs
  to `C([0,S];H^m)` for every integer `m ≥ 0`": every presingular velocity slice
  is an `H^∞` field, in the datum form `Data.MemHInfty` (`Data.lean:495`) and in
  the jet form `Contracts.V1.SmoothSquareIntegrableJets`
  (`GradientL6.lean:106`).

  `ClassicalSolutionR.sobolev` (`Data.lean:643`) supplies only the datum form.
  The equivalence of the two forms is D01 unit L2 (`Data.lean:487-491`), whose
  datum ⟹ jet direction `BoundedRepresentative.lean:71-74` records as **open**.
  This clause is where C01 takes that obligation on, and it is load-bearing
  twice over: the jet form is the hypothesis of the registered
  `gradientL6.gradientLSix`, and both forms together are what make every
  Bochner integral of Section 1 above a finite number rather than Mathlib's
  junk `0`. -/
  velocityJets :
    ∀ (ν : ℝ), 0 < ν → ∀ a : SpatialField, a ∈ initialClassR →
      ∀ f : SpaceTimeField, MemForceR f →
        ∀ (T : ℝ) (w : ClassicalSolutionR ν a f T), ∀ t ∈ Ico (0 : ℝ) T,
          MemHInfty (slice w.velocity t) ∧
            SmoothSquareIntegrableJets (slice w.velocity t)

  /-- **Bridge 2.**  `02-preliminaries.tex:17-19` eq:Rclasses, the two
  finiteness requirements defining `F_R`, in the slicewise form eq:RL2 and
  eq:RH1 integrate: the force slice is square integrable at every future time,
  and `t ↦ ‖f(t)‖₂` is continuous on `[0,∞)`.

  Interval integrability of `s ↦ ‖f(s)‖₂` and of `s ↦ ‖f(s)‖₂²` on each `[0,t]`
  — which is what makes `forcePrimitive` and the third summand of the assembly
  honest interval integrals rather than Mathlib's junk `0` — is a *consequence*
  of the second conjunct and is deliberately not restated: a function continuous
  on `Ici 0` is continuous on the compact `[0,t]`, hence interval integrable
  there, and `l2Sq = l2Norm ^ 2` pointwise because `l2Sq` is an integral of
  squares.

  **Local, not global.**  This field says nothing about `(0,∞)`.  The
  manuscript's own sentence at `04-whole-space.tex:171` — "Because `f ∈ F_R`,
  its `L^1_tL^2_x` and `L^2_tL^2_x` norms are finite, even though they are not
  required to be small" — is about *global* finiteness on the whole half line,
  and that is `MemForceR`'s own content (`Data.lean:549-551`,
  `MemLp G 1`/`MemLp G 2` over `positiveTimeMeasure`) for the Bochner **datum
  path**, not for the physical slices.  Every consumer below evaluates the force
  integrals at a *finite* horizon `S`, so the local form is all that is needed
  and all that is claimed; transporting the global datum-path finiteness to the
  physical slices would be a strictly larger obligation and is left to whoever
  needs it. -/
  forceTimeRegularity :
    ∀ f : SpaceTimeField, MemForceR f →
      (∀ t : ℝ, 0 ≤ t → MemLp (slice f t) 2 volume) ∧
        ContinuousOn (fun s => l2Norm (slice f s)) (Ici (0 : ℝ))

  /-- **The ordinary energy identity** (`04-whole-space.tex:117`, "The separate
  ordinary energy identity"), the exact form before any inequality:

    `(‖u(t)‖₂²)' = −2ν‖∇u(t)‖₂² + 2⟨u(t), f(t)⟩`.

  Equivalently `½(‖u‖₂²)' + ν‖∇u‖₂² = ⟨f,u⟩`.  Two cancellations are folded in
  and are proof obligations, not hypotheses: the transport term
  `⟨(u·∇)u, u⟩` vanishes because `u` is divergence free
  (`ClassicalSolutionR.divergence`), and the pressure term `⟨∇p, u⟩` vanishes
  for the same reason together with `∇p ∈ L²`
  (`ClassicalSolutionR.pressure_gradient`).  Asserting `HasDerivAt` also
  asserts that the squared energy is differentiable at every interior time,
  which is what the differential displays below quantify over. -/
  energyIdentity :
    ∀ (ν : ℝ), 0 < ν → ∀ a : SpatialField, a ∈ initialClassR →
      ∀ f : SpaceTimeField, MemForceR f →
        ∀ (T : ℝ) (w : ClassicalSolutionR ν a f T), ∀ t ∈ Ioo (0 : ℝ) T,
          HasDerivAt (fun s => l2Sq (slice w.velocity s))
            (-2 * ν * gradientSq (slice w.velocity t) +
              2 * pairing (slice w.velocity t) (slice f t)) t

  /-- **The ordinary energy inequality**, the Cauchy-Schwarz form of the
  identity and the differential input of eq:RL2
  (`04-whole-space.tex:117-121`):

    `(‖u(t)‖₂²)' + 2ν‖∇u(t)‖₂² ≤ 2‖f(t)‖₂‖u(t)‖₂`.

  Quantified over any real `E'` that is the derivative at `t`, rather than over
  `deriv`, so that a consumer may feed in the derivative from `energyIdentity`
  or from its own differentiability proof; derivatives are unique, so this is
  the same statement.  It is the inequality whose regularized division by
  `(‖u‖₂² + ζ²)^{1/2}`, `ζ ↓ 0` (`:100`) yields the next clause, including at
  times where `‖u(t)‖₂ = 0` (`:103`). -/
  energyDifferentialBound :
    ∀ (ν : ℝ), 0 < ν → ∀ a : SpatialField, a ∈ initialClassR →
      ∀ f : SpaceTimeField, MemForceR f →
        ∀ (T : ℝ) (w : ClassicalSolutionR ν a f T), ∀ t ∈ Ioo (0 : ℝ) T,
          ∀ E' : ℝ, HasDerivAt (fun s => l2Sq (slice w.velocity s)) E' t →
            E' + 2 * ν * gradientSq (slice w.velocity t) ≤
              2 * l2Norm (slice f t) * l2Norm (slice w.velocity t)

  /-- **eq:RL2** (`04-whole-space.tex:118-121`), the display verbatim:

    `‖u(t)‖₂ ≤ ‖a‖₂ + ∫₀^t‖f(s)‖₂ ds =: K(t)`,

  for every presingular time, with `K` spelled `energyBudget a f t`.  No
  smallness hypothesis and no absorption: this is the *ordinary* energy
  estimate, which is the whole point of keeping it separate from eq:RH1 —
  `04-whole-space.tex:117` "It does not control low frequencies by itself", and
  `:132` "The low frequencies have been controlled directly by the ordinary
  energy estimate".  On `R³` there is no spectral gap to obtain this from the
  dissipation term instead (`04-whole-space.tex:4-5`). -/
  l2Bound :
    ∀ (ν : ℝ), 0 < ν → ∀ a : SpatialField, a ∈ initialClassR →
      ∀ f : SpaceTimeField, MemForceR f →
        ∀ (T : ℝ) (w : ClassicalSolutionR ν a f T), ∀ t ∈ Ico (0 : ℝ) T,
          l2Norm (slice w.velocity t) ≤ energyBudget a f t

  /-- `04-whole-space.tex:107-109`, the first of the two nonlinear steps:

    `|⟨(u·∇)u, Δu⟩| ≤ ‖u‖₃‖∇u‖₆‖Δu‖₂`,

  a three-factor Hölder inequality with exponents `1/3 + 1/6 + 1/2 = 1`.
  Stated in `ℝ≥0∞` because two of its three factors — the critical `L³` norm and
  the `L⁶` norm of the gradient tensor, the latter being exactly the left-hand
  side of the registered `gradientL6.gradientLSix` — are `eLpNorm`s that are
  never differentiated.  The left-hand side is the absolute value of the real
  work integral, injected by `ENNReal.ofReal`, so the bound is an honest bound
  on a real number by a possibly infinite quantity.

  **The hypothesis is the jet form, not `MemHInfty`.**  The registered clause
  this field feeds, `gradientL6.gradientLSix`, runs on
  `SmoothSquareIntegrableJets` (`GradientL6.lean:138-139`), and the datum ⟹ jet
  direction is open (`BoundedRepresentative.lean:71-74`).  Stating these two
  fields over all `H^∞` *data* would therefore need D01 unit L2 at full
  generality, which no field of this contract supplies — `velocityJets` gives it
  only for velocity slices.  The jet form costs consumers nothing: the only
  fields either trilinear clause is ever applied to are velocity slices, and
  `velocityJets` hands out **both** forms for those. -/
  trilinearHolder :
    ∀ z : SpatialField, SmoothSquareIntegrableJets z →
      ENNReal.ofReal |advectionWork z| ≤
        criticalL3 z * eLpNorm (gradientTensor z) 6 volume *
          eLpNorm (laplacian z) 2 volume

  /-- `04-whole-space.tex:109-112`, the second nonlinear step, obtained from the
  first by the registered `gradientL6.gradientLSix`
  (`GradientL6.lean:138-142`, `‖∇v‖₆ ≤ C‖Δv‖₂`, itself resting on
  `hessianLaplacianIdentity`, "since Plancherel gives `‖D²u‖₂ = ‖Δu‖₂`"):

    `|⟨(u·∇)u, Δu⟩| ≤ C₁‖u‖₃‖Δu‖₂²`.

  The manuscript writes `C₁y‖Δu‖₂²` with `y = ‖Λ^{1/2}u‖₂`; the form here keeps
  `‖u‖₃`, which is the factor Hölder actually produces and the one
  `research/section4/STATEMENTS.md:604` quotes.  Converting `‖u‖₃` to `Cy`
  (R43) or to `CY` (R44) is A05's `velocityCriticalL3`, not C01's business.

  Same jet hypothesis as `trilinearHolder`, and for the same reason: with it the
  derivation from that field closes using **only** the registered clause, with
  no unregistered general-purpose datum ⟹ jet bridge smuggled in.  The
  right-hand side is `‖Δz‖₂²` as an `ℝ≥0∞` square; `laplacianSqENorm` below is
  what converts it to the real `laplacianSq` that the enstrophy fields use, so
  that this field can actually be fed into the absorption step rather than only
  document it. -/
  trilinearAbsorbed :
    ∀ z : SpatialField, SmoothSquareIntegrableJets z →
      ENNReal.ofReal |advectionWork z| ≤
        ENNReal.ofReal C₁ * criticalL3 z *
          eLpNorm (laplacian z) 2 volume ^ (2 : ℝ)

  /-- **Bridge 4.**  The one conversion the contract needs between its two
  number systems on the Laplacian term:

    `eLpNorm (Δz) 2 volume ^ 2 = ENNReal.ofReal (∫ |Δz|²)`,

  i.e. `‖Δz‖₂²` computed in `ℝ≥0∞` and `‖Δz‖₂²` computed as a real Bochner
  integral are the same number.

  `trilinearHolder` and `trilinearAbsorbed` bound the nonlinear work by
  `eLpNorm (laplacian z) 2 volume ^ 2`, while `enstrophyIdentity`,
  `enstrophyDifferentialBound` and `enstrophyIntegralBound` all speak of the
  real `laplacianSq z`.  Without this field a holder of `EnergyAbsorptionAPI`
  could not feed `trilinearAbsorbed` into the absorption step and would have to
  reprove the conversion, which would leave the two trilinear fields
  documentary rather than load-bearing.

  It is an **equality**, not a bound, and it is `.toReal`-free in the same style
  as `sobolevTwoFourier`: the left side is `⊤` exactly when `Δz ∉ L²`, and on
  the jet class it never is, so the equality is the honest statement.  Both
  sides are `eLpNorm`/Bochner objects of the *same* field `laplacian z`, so this
  is bookkeeping, not analysis: the `L²` case is already done in tree as
  `NSFormalization.Section4.I02.Energy.eLpNorm_two_eq_ofReal_sqrt`
  (`formalization/NSFormalization/Section4/I02/Energy.lean:87`,
  `eLpNorm f 2 volume = ENNReal.ofReal (Real.sqrt (∫ ‖f‖²))` for an integrable
  square), and squaring it gives this field.

  No analogue is stated for `eLpNorm (gradientTensor z) 6 volume`: the `L⁶`
  factor is an intermediate that `gradientL6.gradientLSix` eliminates on the way
  from `trilinearHolder` to `trilinearAbsorbed`, and it appears in no real-valued
  field, so it never has to cross. -/
  laplacianSqENorm :
    ∀ z : SpatialField, SmoothSquareIntegrableJets z →
      eLpNorm (laplacian z) 2 volume ^ (2 : ℝ) = ENNReal.ofReal (laplacianSq z)

  /-- **The enstrophy identity**, the exact form of the `−Δu` test
  (`04-whole-space.tex:106`, "testing against `−Δu`"; the display itself is
  `:107-110`), before any inequality:

    `(‖∇u(t)‖₂²)' = 2⟨(u·∇)u(t), Δu(t)⟩ − 2ν‖Δu(t)‖₂² − 2⟨f(t), Δu(t)⟩`.

  Equivalently `½(‖∇u‖₂²)' + ν‖Δu‖₂² = ⟨(u·∇)u, Δu⟩ − ⟨f, Δu⟩`.  Two steps are
  folded in as proof obligations: the integration by parts
  `⟨∂_tu, −Δu⟩ = ½(‖∇u‖₂²)'`, which needs differentiation under the spatial
  integral, and the vanishing of `⟨∇p, Δu⟩` for a divergence-free field.  As in
  `energyIdentity`, asserting `HasDerivAt` also asserts differentiability of
  the squared gradient norm at every interior time. -/
  enstrophyIdentity :
    ∀ (ν : ℝ), 0 < ν → ∀ a : SpatialField, a ∈ initialClassR →
      ∀ f : SpaceTimeField, MemForceR f →
        ∀ (T : ℝ) (w : ClassicalSolutionR ν a f T), ∀ t ∈ Ioo (0 : ℝ) T,
          HasDerivAt (fun s => gradientSq (slice w.velocity s))
            (2 * advectionWork (slice w.velocity t) -
              2 * ν * laplacianSq (slice w.velocity t) -
              2 * pairing (slice f t) (laplacian (slice w.velocity t))) t

  /-- **eq:RH1** (`04-whole-space.tex:113-116`), the display verbatim:

    `(‖∇u‖₂²)' + ν‖Δu‖₂² ≤ Cν^{-1}‖f‖₂²`,

  valid at every interior time at which the critical norm is small enough to
  absorb the nonlinearity, `C₁‖u(t)‖₃ ≤ ν/4` (`:112`, and
  `research/section4/STATEMENTS.md:604`).  The hypothesis is stated in `ℝ≥0∞`,
  so a slice with `‖u(t)‖₃ = ⊤` cannot satisfy it and the clause is vacuous
  there — the fail-safe direction.

  Between `trilinearAbsorbed` and this display the manuscript performs one
  Young inequality, `‖f‖₂‖Δu‖₂ ≤ (ν/4)‖Δu‖₂² + ν^{-1}‖f‖₂²`; that is why `ν/4`
  and not `ν/2` is the absorption threshold, the other quarter of the
  dissipation being spent on the forcing term. -/
  enstrophyDifferentialBound :
    ∀ (ν : ℝ), 0 < ν → ∀ a : SpatialField, a ∈ initialClassR →
      ∀ f : SpaceTimeField, MemForceR f →
        ∀ (T : ℝ) (w : ClassicalSolutionR ν a f T), ∀ t ∈ Ioo (0 : ℝ) T,
          ENNReal.ofReal C₁ * criticalL3 (slice w.velocity t) ≤
              ENNReal.ofReal (ν / 4) →
            ∀ E' : ℝ, HasDerivAt (fun s => gradientSq (slice w.velocity s)) E' t →
              E' + ν * laplacianSq (slice w.velocity t) ≤
                CRH1 * ν⁻¹ * l2Sq (slice f t)

  /-- eq:RH1 integrated from `0` to `t`, the form the assembly uses
  (`04-whole-space.tex:116`, "This controls the gradient and the integral of
  the squared Laplacian"):

    `‖∇u(t)‖₂² + ν∫₀^t‖Δu(s)‖₂²ds ≤ ‖∇a‖₂² + Cν^{-1}∫₀^t‖f(s)‖₂²ds`,

  together with the interval integrability of `s ↦ ‖Δu(s)‖₂²` that makes the
  left-hand integral an honest one rather than Mathlib's junk `0`.  The initial
  term is `‖∇a‖₂²` because `ClassicalSolutionR.initial` gives
  `u(0,·) = a`.  The absorption hypothesis is required on the whole of `[0,t]`,
  as in the manuscript, where it holds throughout the lifespan by the
  continuity bootstrap of `:103` — that bootstrap is R43's, not C01's. -/
  enstrophyIntegralBound :
    ∀ (ν : ℝ), 0 < ν → ∀ a : SpatialField, a ∈ initialClassR →
      ∀ f : SpaceTimeField, MemForceR f →
        ∀ (T : ℝ) (w : ClassicalSolutionR ν a f T), ∀ t ∈ Ico (0 : ℝ) T,
          (∀ s ∈ Ico (0 : ℝ) t, ENNReal.ofReal C₁ * criticalL3 (slice w.velocity s) ≤
              ENNReal.ofReal (ν / 4)) →
            IntervalIntegrable (fun s => laplacianSq (slice w.velocity s)) volume 0 t ∧
              gradientSq (slice w.velocity t) +
                  ν * ∫ s in (0 : ℝ)..t, laplacianSq (slice w.velocity s) ≤
                gradientSq a + CRH1 * ν⁻¹ * ∫ s in (0 : ℝ)..t, l2Sq (slice f s)

  /-- **Bridge 3.**  `04-whole-space.tex:122-124`, the Fourier inequality

    `‖z‖²_{H²} ≤ C(‖z‖₂² + ‖Δz‖₂²)`,

  which is what turns eq:RL2 and eq:RH1 — an `L²` bound and a squared-Laplacian
  time integral — into a bound on the `H²` norm that
  `02-preliminaries.tex:108` eq:criterion asks for.  The left-hand side is
  D01's datum norm `sobolevENorm 2` (`Data.lean:189`), kept in `ℝ≥0∞`; the
  right-hand side is the two real squared quantities of Section 1.
  `research/section4/STATEMENTS.md:478-479` books this as a D01 need, but
  `Data.lean` is definitions only, so C01 states it here as the ingredient of
  its own assembly. -/
  sobolevTwoFourier :
    ∀ z : SpatialField, MemHInfty z →
      sobolevENorm 2 z ^ (2 : ℝ) ≤
        ENNReal.ofReal (CH2 * (l2Sq z + laplacianSq z))

  /-- **The assembly** (`04-whole-space.tex:125-131`), the single consequence
  R43 extracts (`research/section4/STATEMENTS.md:494-497`, C01 item 3):

    `∫₀^S‖u(t)‖²_{H²}dt ≤ CSK(S)² + Cν^{-1}‖∇a‖₂² + Cν^{-2}∫₀^S‖f(t)‖₂²dt < ∞`

  for every `S` "within or at the maximal lifespan" (`:125`), i.e. every
  `0 < S ≤ T` for a classical solution on `[0,T)`; the time integral runs over
  the open interval, so no value at `S` is used.  The hypothesis is the same
  absorption smallness as eq:RH1, assumed on `[0,S)`, which R43 obtains from
  its continuity bootstrap and R44 from `‖u‖₃ ≤ CY ≤ Cθν` (`:171`).

  The left-hand side is a lower Lebesgue integral in `ℝ≥0∞`, the shape
  `Data.energyGradient` (`Data.lean:459`) already uses, so there is no
  integrability side condition and the conclusion is literally a finite bound:
  `≤ ENNReal.ofReal _` is the `< ∞` of `:130`, which is what A04's
  continuation clause consumes. -/
  h2TimeIntegral :
    ∀ (ν : ℝ), 0 < ν → ∀ a : SpatialField, a ∈ initialClassR →
      ∀ f : SpaceTimeField, MemForceR f →
        ∀ (T : ℝ) (w : ClassicalSolutionR ν a f T) (S : ℝ), 0 < S → S ≤ T →
          (∀ t ∈ Ico (0 : ℝ) S, ENNReal.ofReal C₁ * criticalL3 (slice w.velocity t) ≤
              ENNReal.ofReal (ν / 4)) →
            ∫⁻ t in Ioo (0 : ℝ) S, sobolevENorm 2 (slice w.velocity t) ^ (2 : ℝ) ≤
              ENNReal.ofReal
                (Cassembly * S * energyBudget a f S ^ 2 +
                  Cassembly * ν⁻¹ * gradientSq a +
                  Cassembly * (ν⁻¹) ^ 2 * ∫ s in (0 : ℝ)..S, l2Sq (slice f s))

  /-- The `a = 0` instance of `h2TimeIntegral`, which is the shape Proposition
  4.4 consumes: `research/section4/STATEMENTS.md:604-606`, "the
  `∫₀^S‖u‖²_{H²} < ∞` assembly — here with `a = 0`, so `K(S) = ∫₀^S‖f‖₂` and
  `‖∇a‖₂ = 0`".  Proposition 4.4 fixes the initial velocity to be exactly zero
  (`04-whole-space.tex:141`, and `STATEMENTS.md:631-633`, "`a = 0` is
  essential"), so the first summand loses `‖a‖₂` and the second vanishes.

  Kept as a separate field, rather than left to be derived, for the same reason
  `research/A05/Spec.lean` keeps `velocityCriticalL3` separate from
  `embeddingPair`: so that R44 needs no arithmetic rewriting of the constant
  term.  It is the *same* constant `Cassembly`. -/
  h2TimeIntegralZeroDatum :
    ∀ (ν : ℝ), 0 < ν → ∀ f : SpaceTimeField, MemForceR f →
      ∀ (T : ℝ) (w : ClassicalSolutionR ν (fun _ => 0) f T) (S : ℝ), 0 < S → S ≤ T →
        (∀ t ∈ Ico (0 : ℝ) S, ENNReal.ofReal C₁ * criticalL3 (slice w.velocity t) ≤
            ENNReal.ofReal (ν / 4)) →
          ∫⁻ t in Ioo (0 : ℝ) S, sobolevENorm 2 (slice w.velocity t) ^ (2 : ℝ) ≤
            ENNReal.ofReal
              (Cassembly * S * forcePrimitive f S ^ 2 +
                Cassembly * (ν⁻¹) ^ 2 * ∫ s in (0 : ℝ)..S, l2Sq (slice f s))

end BlowupDensity.C01.Draft
