import NSFormalization.Section4.A02.SolutionClass
import NSFormalization.Section4.D01.DatumToJets
import NSFormalization.Section4.D01.ForceClass
import NSFormalization.Section4.A03.OuterTameProduct
import NSFormalization.Section4.A05.SmoothJets

/-!
# The pressure package (unit D01/L9(c)-partial): `∇p` regularity from `momentum`

`research/D01/RECONCILIATION.md:160`, `COMPARISON_A.md:108`.  The booked
obligation **L9(c)** is eq:Rpressure `∇p = (I−P)(f − ∇·(u⊗u))` — the Leray
complement identity, even at the `L²` (order-zero) level — together with the
regularity of the pressure gradient of a classical solution, whose exact consumer
is C01's energy identities (units U3/U7, `research/C01/COMPARISON.md:220`,
`REVIEW.md:209-237`): for `u : ClassicalSolutionR ν a f T` and `t ∈ Ioo 0 T`, the
slice `∇p(t,·)` must be in `Contracts.V1.SmoothSquareIntegrableJets` (smooth, with
every Fréchet jet square integrable).

**This lane is L9(c)-partial.**  No form of eq:Rpressure `∇p = (I−P)(f − ∇·(u⊗u))`
is proved here — not the `(I−P)` identity, not even its order-zero `L²` version;
the Leray complement `(I−P)` on whole-space physical fields is unavailable in the
main tree (see the gap section).  What is discharged is the part that does not
need the projection: the momentum rearrangement, the `H^∞` regularity of the
nonlinear/viscous/force slices, and the conditional equivalence below.  L9(c)
stays open in `RECONCILIATION.md` and the work queue; the follow-up unit is
named at the end of this docstring.

## What is proved

1. **The algebraic identities (unconditional).**  On the interior times
   `Ioo 0 T`, `pressureGradient_slice_eq` gives `∇p = f − ∂ₜu − (u·∇)u + νΔu`
   pointwise, and `temporalDerivative_slice_eq` gives `∂ₜu = f − (u·∇)u + νΔu − ∇p`
   — the residual of `NavierStokesR3.ProblemStatement.navierStokesResidual`
   rearranged (one `abel` each).  This is the identity C01 re-derives at
   `REVIEW.md:209`.

2. **The nonlinear and viscous slices are `H^∞` (discharged from the class).**
   `laplacian_slice_smoothL2` and `advection_slice_smoothL2` show that
   `νΔu(t,·)` and `(u·∇)u(t,·)` are in `SmoothSquareIntegrableJets`, using only
   `velocity_smooth` + `sobolev` of the class (through
   `DatumToJets.smoothSquareIntegrableJets_slice`), derivative closure of the jet
   class (`A05.SmoothL2.dir`), and the registered tame product
   `A03.advectionTame`.  Neither touches `divergence`, `momentum` or
   `pressure_gradient`.

3. **The conditional equivalence, and the single root gap.**
   `pressureGradient_slice_smoothL2_iff_temporalDerivative`:  for `MemForceR f`,
   `SmoothSquareIntegrableJets (∂ₜu(t,·)) ↔ SmoothSquareIntegrableJets (∇p(t,·))`.
   This is a **repackaging** of the pressure-regularity obligation C01 books as
   **P2**, *not a reduction of the gap*: given `MemForceR f` and the module's own
   pieces the two sides are interderivable in one line each way through
   `momentum`, so the net new content is the three `H^∞`-slice lemmas.  The one
   forward direction (`pressureGradient_slice_smoothSquareIntegrableJets`) is kept
   as a corollary for consumers that want it.

### Why `∂ₜu(t,·) ∈ H^∞` is a genuine gap, and what closing it needs

`ClassicalSolutionR` (`A02/SolutionClass.lean:114-138`) carries a spatial
`H^m`-datum for **`u`** at every order (`sobolev`), smoothness on the slab,
`div u = 0`, and `∇p(t,·) ∈ L²` at order **zero only** (`pressure_gradient`).  It
carries no Sobolev datum for `∂ₜu` or for `∇p` at any positive order.
Consequently the unconditional statement "`SmoothSquareIntegrableJets (∇p(t,·))`
for every `ClassicalSolutionR ν a f T`" is **false**: take a smooth
divergence-free `u` with all slices `H^∞`, a scalar `p` whose gradient is smooth
and `L²` but not `H¹`, and *define* `f` by the momentum equation; every field of
the structure holds, yet `∇p(t,·) ∉ SmoothSquareIntegrableJets`.  A force
hypothesis is therefore mandatory, and
`DatumToJets.contDiff_pressureGradient_slice:504` already records that only
spatial smoothness of `∇p(t,·)` is cheap.

With `MemForceR f` the statement becomes true, but its proof is exactly the
Leray/Helmholtz splitting.  From `momentum`,
`∂ₜu + ∇p = f − (u·∇)u + νΔu =: h ∈ H^∞`.  Here `∂ₜu` is solenoidal
(`div ∂ₜu = ∂ₜ div u = 0`) and `∇p` is a gradient (curl-free), so
`∂ₜu = P h` and `∇p = (I−P)h` by uniqueness of the Helmholtz decomposition, and
`∇p ∈ H^∞` because `(I−P)` is bounded on every `H^m`.  This is eq:Rpressure
`∇p = (I−P)(f − ∇·(u⊗u))` (`(u·∇)u = ∇·(u⊗u)` when `div u = 0`).  Closing the gap
— i.e. proving eq:Rpressure and discharging the `∂ₜu(t,·) ∈ H^∞` hypothesis —
needs, on `Space → Space` in the manuscript's **angular** convention:
* (i) the `L²` Helmholtz/Leray **decomposition itself**, `L² = L²_σ ⊕ G` with its
  projection `P` (absent in tree for whole-space angular fields);
* (ii) placing the pointwise-solenoidal `∂ₜu(t,·) ∈ L²` into the *closed*
  solenoidal subspace, which is D01 unit **L3** (`RECONCILIATION.md` L3 row,
  booked separately and open), and needs
* (iii) `div ∂ₜu = ∂ₜ div u` (routine from `velocity_smooth`, but unproved in
  tree); together with
* (iv) `(I−P)` bounded on every `H^m` for the `H^∞` upgrade.

The `∂ₜu(t,·) ∈ H^∞` hypothesis and `∇p(t,·) ∈ H^∞` are interderivable given the
identities above (both follow from (i)–(iv)); the `Iff` names this precisely.

### The in-tree Leray inventory

There **are** Leray projections in tree, but only periodic ones, which do not
transfer to the whole-space angular target:
`NSFormalization.Source.ForcedCylinderLocal.leray` (`ForcedCylinderLocal.lean:26`)
is a continuous linear map `SobolevSpace period q →L[ℝ] SobolevSpace period q`
(so it *does* carry an "`(I−P)` bounded on `H^q`" for the periodic scale), and
`NSFormalization.Paper1.PeriodicLeray{CoeffCore,Divergence,WeightedNorm,…}` carry
the periodic Fourier Leray correction.  Both are periodic / cylinder
constructions.  The **only whole-space-`ℝ³` Leray construction in tree is
HeliCorgi's**, exposed through the U05 port (`Section4/HeliCorgiPort.lean`, which
compiles at this pin, Lean 4.34.0-rc2):
`MNS2.r3LerayComplementL2` (`vendor/HeliCorgi/Formal/R3HelmholtzPressure.lean:228`)
and `MNS2.r3HelmholtzPressure_gradient` (`:259`), the latter giving
`∇p = −(I−P)F` componentwise **in `𝓢'`** for an arbitrary `L²` source
(`r3HelmholtzPressure`, `:223`).  It is stated for the distributional gradient in
the cycles convention `e^{-2πi⟨x,ξ⟩}` over the complex HeliCorgi field types,
whereas the target here is the classical pointwise `pressureGradient` in the
angular convention on real `EuclideanSpace ℝ (Fin 3)`.  Bridging the two — a
real-linear/convention bridge plus a distributional-to-classical identification
plus the `L² → H^m` upgrade, on top of (i)–(iv) above — is a separate follow-up
unit and is the exact missing lemma; see `research/D01/ATTEMPTS_L9C.md`.

`SmoothSquareIntegrableJets`, `IsSobolevDatum`, `sobolevENorm`, `MemForceR` and
`ClassicalSolutionR` are *definitionally* the corresponding declarations of
`Contracts/V1/Data.lean`, `GradientL6.lean`; they are reached through the A02/D01
restatements because the `NSFormalization` package cannot import `Contracts`.
-/

noncomputable section

namespace NSFormalization.Section4.D01

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Paper3
open NSFormalization.Section4.A02 (ClassicalSolutionR MemForceR)
open scoped ContDiff ENNReal

/-! ## 0. Closure of the smooth square-integrable jet class

`A05.SmoothL2` is the jet form used throughout the analytic lanes; on
`Space → Space` it is definitionally `SmoothSquareIntegrableJets`.  The
datum-facing lanes never needed additive/scalar closure of it (only derivative
closure, `A05.SmoothL2.dir`); the pressure identity does, because `∇p` is a sum
of four fields.  These are `MemLp`/`iteratedFDeriv` bookkeeping, no Fourier
analysis. -/

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The sum of two smooth square-integrable jet fields is one. -/
theorem smoothL2_add {f g : Space → F} (hf : A05.SmoothL2 f) (hg : A05.SmoothL2 g) :
    A05.SmoothL2 (fun x => f x + g x) := by
  refine ⟨hf.1.add hg.1, fun n => ?_⟩
  have hle : ((n : ℕ) : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) := by exact_mod_cast le_top
  have heq : iteratedFDeriv ℝ n (fun x => f x + g x)
      = iteratedFDeriv ℝ n f + iteratedFDeriv ℝ n g := by
    have hsum : (fun x => f x + g x) = f + g := rfl
    rw [hsum]
    exact iteratedFDeriv_add (hf.1.of_le hle) (hg.1.of_le hle)
  rw [heq]
  exact (hf.2 n).add (hg.2 n)

/-- Post-composition with a scalar multiple preserves the jet class. -/
theorem smoothL2_const_smul {f : Space → F} (h : A05.SmoothL2 f) (c : ℝ) :
    A05.SmoothL2 (fun x => c • f x) := by
  have hcl := h.clm (c • ContinuousLinearMap.id ℝ F)
  have heq : (fun x => (c • ContinuousLinearMap.id ℝ F) (f x)) = fun x => c • f x := by
    funext x; simp
  rwa [heq] at hcl

/-- Negation preserves the jet class. -/
theorem smoothL2_neg {f : Space → F} (h : A05.SmoothL2 f) :
    A05.SmoothL2 (fun x => - f x) := by
  have hcl := h.clm (-ContinuousLinearMap.id ℝ F)
  have heq : (fun x => (-ContinuousLinearMap.id ℝ F) (f x)) = fun x => - f x := by
    funext x; simp
  rwa [heq] at hcl

/-- The difference of two smooth square-integrable jet fields is one. -/
theorem smoothL2_sub {f g : Space → F} (hf : A05.SmoothL2 f) (hg : A05.SmoothL2 g) :
    A05.SmoothL2 (fun x => f x - g x) := by
  have h := smoothL2_add hf (smoothL2_neg hg)
  have heq : (fun x => f x + - g x) = fun x => f x - g x := by
    funext x; rw [sub_eq_add_neg]
  rwa [heq] at h

/-! ## 1. The algebraic identities from `momentum` -/

/-- **The algebraic identity.**  On the interior times `Ioo 0 T`, the pressure
gradient of a classical solution is the momentum residual rearranged:
`∇p = f − ∂ₜu − (u·∇)u + νΔu` pointwise.  This is `ClassicalSolutionR.momentum`
with `NavierStokesR3.ProblemStatement.navierStokesResidual` unfolded. -/
theorem pressureGradient_slice_eq {ν : ℝ} {a : Space → Space} {f : VelocityField} {T : ℝ}
    (u : ClassicalSolutionR ν a f T) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) (x : Space) :
    pressureGradient u.pressure t x
      = f (t, x) - temporalDerivative u.velocity t x - advection u.velocity t x
          + ν • spatialLaplacian u.velocity t x := by
  have h := u.momentum t ht x
  rw [NavierStokesR3.ProblemStatement.navierStokesResidual] at h
  rw [← h]; abel

/-- The companion rearrangement isolating the time derivative:
`∂ₜu = f − (u·∇)u + νΔu − ∇p` pointwise on `Ioo 0 T`. -/
theorem temporalDerivative_slice_eq {ν : ℝ} {a : Space → Space} {f : VelocityField} {T : ℝ}
    (u : ClassicalSolutionR ν a f T) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) (x : Space) :
    temporalDerivative u.velocity t x
      = f (t, x) - advection u.velocity t x + ν • spatialLaplacian u.velocity t x
          - pressureGradient u.pressure t x := by
  have h := u.momentum t ht x
  rw [NavierStokesR3.ProblemStatement.navierStokesResidual] at h
  rw [← h]; abel

/-! ## 2. The velocity, viscous, nonlinear and force slices are `H^∞` -/

/-- The velocity slice of a classical solution is smooth with square-integrable
jets, at every interior time.  This is
`DatumToJets.smoothSquareIntegrableJets_slice` fed with the two fields
`velocity_smooth` and `sobolev`. -/
theorem velocity_slice_smoothL2 {ν : ℝ} {a : Space → Space} {f : VelocityField} {T : ℝ}
    (u : ClassicalSolutionR ν a f T) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    SmoothSquareIntegrableJets (fun x : Space => u.velocity (t, x)) := by
  have htIco : t ∈ Ico (0 : ℝ) T := ⟨le_of_lt ht.1, ht.2⟩
  have hsob : ∀ m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
      ∀ s ∈ Ico (0 : ℝ) T, IsSobolevDatum (m : ℝ) (fun x => u.velocity (s, x)) (G s) :=
    fun m => by obtain ⟨G, _, hG⟩ := u.sobolev m; exact ⟨G, hG⟩
  exact smoothSquareIntegrableJets_slice u.velocity_smooth hsob htIco

/-- The Laplacian slice `Δu(t,·) = ∑ᵢ ∂ᵢ∂ᵢu(t,·)` of a classical solution is in
the jet class: each `∂ᵢ∂ᵢu(t,·)` is by two applications of `A05.SmoothL2.dir`,
and the three-term sum by `smoothL2_add`. -/
theorem laplacian_slice_smoothL2 {ν : ℝ} {a : Space → Space} {f : VelocityField} {T : ℝ}
    (u : ClassicalSolutionR ν a f T) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    SmoothSquareIntegrableJets (fun x : Space => spatialLaplacian u.velocity t x) := by
  set us : Space → Space := fun x => u.velocity (t, x) with hus_def
  have hus : SmoothSquareIntegrableJets us := velocity_slice_smoothL2 u ht
  have hgi : ∀ i : Fin 3, A05.SmoothL2 (A05.dirDeriv i (A05.dirDeriv i us)) :=
    fun i => A05.SmoothL2.dir (A05.SmoothL2.dir hus i) i
  have hsum : A05.SmoothL2 (fun x => A05.dirDeriv 0 (A05.dirDeriv 0 us) x
      + A05.dirDeriv 1 (A05.dirDeriv 1 us) x + A05.dirDeriv 2 (A05.dirDeriv 2 us) x) :=
    smoothL2_add (smoothL2_add (hgi 0) (hgi 1)) (hgi 2)
  have heq : (fun x : Space => spatialLaplacian u.velocity t x)
      = fun x => A05.dirDeriv 0 (A05.dirDeriv 0 us) x
          + A05.dirDeriv 1 (A05.dirDeriv 1 us) x + A05.dirDeriv 2 (A05.dirDeriv 2 us) x := by
    funext x
    simp only [spatialLaplacian, Fin.sum_univ_three]
    rfl
  rw [heq]; exact hsum

/-- A datum exists at order `s` whenever the manuscript norm is finite: the
`Data.lean` infimum is not the empty infimum `⊤`. -/
theorem exists_isSobolevDatum_of_sobolevENorm_ne_top {s : ℝ} {z : Space → Space}
    (h : sobolevENorm s z ≠ ⊤) : ∃ A : RealVectorSobolev s, IsSobolevDatum s z A := by
  by_contra hc
  have hempty : IsEmpty {A : RealVectorSobolev s // IsSobolevDatum s z A} :=
    ⟨fun A => hc ⟨A.1, A.2⟩⟩
  rw [sobolevENorm] at h
  exact h (iInf_of_empty _)

/-- The advection `advectionOf us us = (us·∇)us` of a smooth square-integrable jet
field is in the jet class.  Smoothness is `ContDiff.clm_apply`; each jet is
square integrable because the registered tame product `A03.advectionTame` bounds
the manuscript `H^m` norm by a finite quantity at every `m ≥ 2`, which yields an
order-`m` datum, and `DatumToJets.memLp_iteratedFDeriv_of_isSobolevDatum` turns
that into the order-`j` jet for every `j ≤ m` (take `m = max n 2`). -/
theorem advectionOf_smoothL2 {us : Space → Space} (hus : SmoothSquareIntegrableJets us) :
    SmoothSquareIntegrableJets (A03.advectionOf us us) := by
  have hfd : ContDiff ℝ ∞ (fderiv ℝ us) := hus.1.fderiv_right (m := ∞) (by simp)
  have hcd : ContDiff ℝ ∞ (A03.advectionOf us us) := ContDiff.clm_apply hfd hus.1
  refine ⟨hcd, fun n => ?_⟩
  set m := max n 2 with hm_def
  have hm2 : 2 ≤ m := le_max_right n 2
  have hnm : n ≤ m := le_max_left n 2
  -- Each factor of the tame-product right-hand side is finite.
  have hpart : ∀ (s : ℝ) (j : Fin 3), sobolevENorm s (A03.partialDeriv j us) ≠ ⊤ := by
    intro s j
    have hpj : A05.SmoothL2 (A03.partialDeriv j us) := by
      rw [A03.partialDeriv_eq_dirDeriv]; exact A05.SmoothL2.dir hus j
    exact sobolevENorm_ne_top_of_contDiff_memLp hpj.1 hpj.2 s
  have hgrad : ∀ s : ℝ, A03.gradientSobolevENorm s us ≠ ⊤ := by
    intro s
    refine ne_top_of_le_ne_top ?_
      (A03.columnsSobolevENorm_le_sum s (fun j => A03.partialDeriv j us))
    exact ENNReal.sum_ne_top.mpr (fun j _ => hpart s j)
  have hsob2 : sobolevENorm 2 us ≠ ⊤ := sobolevENorm_ne_top_of_contDiff_memLp hus.1 hus.2 2
  have hsobm : sobolevENorm (m : ℝ) us ≠ ⊤ := sobolevENorm_ne_top_of_contDiff_memLp hus.1 hus.2 _
  have hrhs : ENNReal.ofReal (A03.advectionConst m) *
      (sobolevENorm 2 us * A03.gradientSobolevENorm (m : ℝ) us +
        A03.gradientSobolevENorm 2 us * sobolevENorm (m : ℝ) us) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.add_ne_top.mpr
        ⟨ENNReal.mul_ne_top hsob2 (hgrad _), ENNReal.mul_ne_top (hgrad _) hsobm⟩)
  have hne : sobolevENorm (m : ℝ) (A03.advectionOf us us) ≠ ⊤ :=
    ne_top_of_le_ne_top hrhs (A03.advectionTame m hm2 hus hus)
  obtain ⟨A, hA⟩ := exists_isSobolevDatum_of_sobolevENorm_ne_top hne
  exact memLp_iteratedFDeriv_of_isSobolevDatum hnm hcd hA

/-- The advection slice of a classical solution, phrased on the velocity field:
`(u·∇)u(t,·) ∈ SmoothSquareIntegrableJets`. -/
theorem advection_slice_smoothL2 {ν : ℝ} {a : Space → Space} {f : VelocityField} {T : ℝ}
    (u : ClassicalSolutionR ν a f T) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    SmoothSquareIntegrableJets (fun x : Space => advection u.velocity t x) := by
  have hus : SmoothSquareIntegrableJets (fun x : Space => u.velocity (t, x)) :=
    velocity_slice_smoothL2 u ht
  have h := advectionOf_smoothL2 hus
  have heq : A03.advectionOf (fun x => u.velocity (t, x)) (fun x => u.velocity (t, x))
      = fun x : Space => advection u.velocity t x := rfl
  rwa [heq] at h

/-- The force slice `f(t,·)` of a real admissible force is in the jet class: at
every order `m` the datum path of `MemForceR` gives an order-`m` datum, and
`f(t,·)` is smooth by `D01.contDiff_futureSlice` (`ForceClass.lean:301`). -/
theorem forceSlice_smoothL2_of_memForceR {f : VelocityField} (hf : MemForceR f)
    {t : ℝ} (ht : 0 ≤ t) : SmoothSquareIntegrableJets (fun x : Space => f (t, x)) := by
  have hcd : ContDiff ℝ ∞ (fun x : Space => f (t, x)) := contDiff_futureSlice hf.1 ht
  refine ⟨hcd, memHInfty_jets hcd (fun m => ?_)⟩
  obtain ⟨G, hpath, _⟩ := hf.2 m
  exact ⟨G t, hpath t ht⟩

/-! ## 3. The conditional equivalence and its corollary -/

/-- The pressure-gradient slice is in the jet class once the force slice and the
time-derivative slice are, with the nonlinear and viscous terms discharged from
the class. -/
theorem pressureGradient_slice_smoothL2_of {ν : ℝ} {a : Space → Space} {f : VelocityField}
    {T : ℝ} (u : ClassicalSolutionR ν a f T) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T)
    (hf : SmoothSquareIntegrableJets (fun x : Space => f (t, x)))
    (hut : SmoothSquareIntegrableJets (fun x : Space => temporalDerivative u.velocity t x)) :
    SmoothSquareIntegrableJets (fun x : Space => pressureGradient u.pressure t x) := by
  have hadv := advection_slice_smoothL2 u ht
  have hlap := smoothL2_const_smul (laplacian_slice_smoothL2 u ht) ν
  have hrhs : A05.SmoothL2 (fun x : Space => f (t, x) - temporalDerivative u.velocity t x
      - advection u.velocity t x + ν • spatialLaplacian u.velocity t x) :=
    smoothL2_add (smoothL2_sub (smoothL2_sub hf hut) hadv) hlap
  have heq : (fun x : Space => pressureGradient u.pressure t x)
      = fun x : Space => f (t, x) - temporalDerivative u.velocity t x
          - advection u.velocity t x + ν • spatialLaplacian u.velocity t x := by
    funext x; exact pressureGradient_slice_eq u ht x
  rw [heq]; exact hrhs

/-- The converse packaging: the time-derivative slice is in the jet class once
the force slice and the pressure-gradient slice are.  Symmetric to
`pressureGradient_slice_smoothL2_of` through `temporalDerivative_slice_eq`. -/
theorem temporalDerivative_slice_smoothL2_of {ν : ℝ} {a : Space → Space} {f : VelocityField}
    {T : ℝ} (u : ClassicalSolutionR ν a f T) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T)
    (hf : SmoothSquareIntegrableJets (fun x : Space => f (t, x)))
    (hp : SmoothSquareIntegrableJets (fun x : Space => pressureGradient u.pressure t x)) :
    SmoothSquareIntegrableJets (fun x : Space => temporalDerivative u.velocity t x) := by
  have hadv := advection_slice_smoothL2 u ht
  have hlap := smoothL2_const_smul (laplacian_slice_smoothL2 u ht) ν
  have hrhs : A05.SmoothL2 (fun x : Space => f (t, x) - advection u.velocity t x
      + ν • spatialLaplacian u.velocity t x - pressureGradient u.pressure t x) :=
    smoothL2_sub (smoothL2_add (smoothL2_sub hf hadv) hlap) hp
  have heq : (fun x : Space => temporalDerivative u.velocity t x)
      = fun x : Space => f (t, x) - advection u.velocity t x
          + ν • spatialLaplacian u.velocity t x - pressureGradient u.pressure t x := by
    funext x; exact temporalDerivative_slice_eq u ht x
  rw [heq]; exact hrhs

/-- **The conditional equivalence.**  For a classical solution with a real
admissible force, the pressure-gradient slice being in
`Contracts.V1.SmoothSquareIntegrableJets` is equivalent to the time-derivative
slice being so.

This is a **repackaging** of the pressure-regularity obligation C01 books as
**P2**, not a reduction of the Leray gap: given `MemForceR f` and the module's
own `H^∞`-slice lemmas, the two sides are interderivable in one line each way
through `momentum` (`temporalDerivative_slice_eq` / `pressureGradient_slice_eq`).
The remaining analytic content — obtaining either side outright — is the Leray
projection on `H^m` (see the module docstring), which is not proved here. -/
theorem pressureGradient_slice_smoothL2_iff_temporalDerivative {ν : ℝ} {a : Space → Space}
    {f : VelocityField} {T : ℝ} (u : ClassicalSolutionR ν a f T) (hf : MemForceR f)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    SmoothSquareIntegrableJets (fun x : Space => temporalDerivative u.velocity t x)
      ↔ SmoothSquareIntegrableJets (fun x : Space => pressureGradient u.pressure t x) := by
  have hfs := forceSlice_smoothL2_of_memForceR hf (le_of_lt ht.1)
  constructor
  · intro hut; exact pressureGradient_slice_smoothL2_of u ht hfs hut
  · intro hp; exact temporalDerivative_slice_smoothL2_of u ht hfs hp

/-- **The forward corollary.**  For a classical solution with a real admissible
force, the pressure-gradient slice is in `Contracts.V1.SmoothSquareIntegrableJets`
once `∂ₜu(t,·)` is — the single root gap, equivalent to the Leray regularity of
the pressure (see the module docstring). -/
theorem pressureGradient_slice_smoothSquareIntegrableJets {ν : ℝ} {a : Space → Space}
    {f : VelocityField} {T : ℝ} (u : ClassicalSolutionR ν a f T) (hf : MemForceR f)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T)
    (hut : SmoothSquareIntegrableJets (fun x : Space => temporalDerivative u.velocity t x)) :
    SmoothSquareIntegrableJets (fun x : Space => pressureGradient u.pressure t x) :=
  (pressureGradient_slice_smoothL2_iff_temporalDerivative u hf ht).mp hut

end NSFormalization.Section4.D01
