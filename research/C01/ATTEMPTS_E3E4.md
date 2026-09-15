# ATTEMPTS — lane 143-C01-e3-e4-momentum (rows Ep, E3, E4, energyIdentity)

Module delivered: `formalization/NSFormalization/Section4/C01/MomentumCarrierB.lean`
(namespace `NSFormalization.Section4.C01`).  Axiom audit:
`research/C01/axioms_e3e4.lean` (all 12 declarations `[propext, Classical.choice,
Quot.sound]`).

## Result summary

* **Ep — DONE.**  `velocitySliceField`, `pressureGradientField`, `temporalSliceField`,
  `forceSliceField` package `u(t,·)`, `∇p(t,·)`, `∂ₜu(t,·)`, `f(t,·)` as carrier-B
  `EulerLpTranslation.SmoothL2Field Space` at an interior time `t ∈ Ioo 0 T`, all four
  `_field` lemmas `rfl`.  `pressureGradientField` is row Ep proper (D01 P2).  With them:
  `contDiff_pressureSlice` (`hp`), `pressureGradientField_eq_gradient` (`hgrad`),
  `velocitySliceField_divergence` (`hdiv`).
* **E3 — DONE.**  `momentum_split_toLp`: `(∂ₜu).toLp = ν•(Δu).toLp − ((u·∇)u).toLp −
  (∇p).toLp + f.toLp`, the exact `hmom` shape of `energyIdentity_of_carrierB`.  Uses the
  two vendor-field bridges `advectionField_velocitySlice_field` (`rfl`) and
  `laplacianField_velocitySlice_field` (`vector_laplacian_eq_sum`).
* **Payoff — DONE modulo E4.**  `energyIdentity_classical`: given the E4 value fact
  `hd : d = 2⟪u,∂ₜu⟫_{L²}`, `d = −2ν·(∫∑ᵢ‖∂ᵢu‖²) + 2·(∫⟨u,f⟩)` (spec's asserted value,
  raw-integral form), by feeding Ep+E3+hdiv+hgrad+hp into `energyIdentity_of_carrierB`.
* **E4 — NOT CLOSED.**  The derivative-value fact
  `HasDerivAt (fun s => ‖u(s,·)‖²_{L²}) (2⟪u,∂ₜu⟫) t` is blocked; see §3.

## 1. Ep — packaging (no obstruction)

`SmoothL2Field` (`vendor/.../Euler/LpSmoothField.lean:31`) is
`⟨field, smooth : ContDiff ℝ ∞ field, integrable : ∀ n, MemLp (iteratedFDeriv ℝ n field) 2 volume⟩`.
`D01.SmoothSquareIntegrableJets` / `A05.SmoothL2` are **both** the plain `And`
`ContDiff ℝ ∞ v ∧ ∀ n, MemLp (iteratedFDeriv ℝ n v) 2 volume`, so `.1`/`.2` fill the
structure directly (exactly as `Evolution.velocityField` does).  Sources:
`velocity_slice_smoothL2`, D01 P2
`pressureGradient_slice_smoothSquareIntegrableJets_of_memForceR` /
`temporalDerivative_slice_smoothSquareIntegrableJets_of_memForceR`,
`forceSlice_smoothL2_of_memForceR`.  All `_field` lemmas `rfl`.

`hgrad` (`pressureGradientField_eq_gradient`): coordinatewise via `PiLp.ext`,
`D01.pressureGradient_apply` (LHS `.ofLp i = fderiv (p(t,·)) x (eᵢ)`) and
`EulerMeanHarmonic.gradient_coordinate` (RHS `(gradient (p(t,·)) x).ofLp i =
partialDerivative …`), then `rfl` (`partialDerivative f i x = fderiv ℝ f x (single i 1)`,
`coordinateVector i = single i 1`).  `gradient` here is Mathlib `_root_.gradient`
(`#check @gradient` ⇒ the `RCLike`/`InnerProductSpace` one), the same one
`energyIdentity_of_carrierB`/`gradient_pairing_zero` use.

`hdiv` (`velocitySliceField_divergence`): the internal `hdiv` of
`Evolution.velocityField_solenoidal`, copied — `divergence_eq_coordinate_sum` +
`simpa [spatialDivergence, spatialDerivative, coordinateVector] using w.divergence`.

## 2. E3 — the vendor-field bridges and the `Lp` pushforward

* `advectionField_velocitySlice_field`: `advectionField_field A B x = fderiv B.field x (A.field x)`
  (`OrdinaryFieldAlgebra.lean:132`, `@[simp]`); with `A=B=u=velocitySliceField`,
  `u.field = fun x => w.velocity(t,x)`, this **is** `advection w.velocity t x =
  spatialDerivative … (u(t,x)) = fderiv (u(t,·)) x (u(t,x))` — closes by `rw [advectionField_field]; rfl`.
* `laplacianField_velocitySlice_field`: `laplacianField_field W : (laplacianField W).field
  = Δ W.field` (`Source/OrdinaryViscousStability.lean:19`, `Δ = Laplacian.laplacian`); then
  `congrFun (EulerMeanVectorIdentities.vector_laplacian_eq_sum u.field u.smooth) x` turns
  `Δ u.field x` into `∑ᵢ vectorPartial (vectorPartial u.field i) i x`, which is term-for-term
  `spatialLaplacian w.velocity t x` (`= ∑ᵢ fderiv (fun y => fderiv (u(t,·)) y (eᵢ)) x (eᵢ)`):
  closes by `rfl`.
* `momentum_split_toLp`: `apply Lp.ext`, then one `filter_upwards` with the four
  `Lp.coeFn_{add,sub,sub,smul}` for the RHS `Lp`-arithmetic and the five `toLp_ae`.  The
  `rw` chain interleaves the `coeFn` lemmas with `Pi.{add,sub,smul}_apply` (see §4.3),
  then the two bridges, `temporalSliceField_field`/`pressureGradientField_field`/
  `forceSliceField_field` (via `simp only` for the beta redex), `D01.temporalDerivative_slice_eq`
  (`∂ₜu = f − (u·∇)u + νΔu − ∇p`) and `abel` (the single `ν•Δu` summand is an atom).

## 3. E4 — BLOCKED on the time-continuity of the `∂ₜu` (equivalently `∇p`) `L²` jets

**Intended route (brief / `ENERGY_SPLIT.md` E4):** `EulerOrdinarySobolev.wordEnergy_hasDerivWithinAt`
(`vendor/.../Euler/OrdinaryWordTime.lean:87`) at order `s=0` (there `wordEnergy 0 A = ‖A.toLp‖²`),
with the velocity path `A := Evolution.velocityField`, then upgrade `HasDerivWithinAt (Icc …)`
to `HasDerivAt` at interior `t`.

**Why it does not close.**  That lemma's hypothesis package (verified by reading
`OrdinaryWordTime.lean:87` and the underlying `EulerSmoothFieldSobolevTime.sobolevPath_hasDerivWithinAt`,
`SmoothFieldSobolevTime.lean`) is

```
(A B : Icc 0 T' → SmoothL2Field Space)
(hA : ∀ n, Continuous (fun s => (A s).jetLp n))     -- velocity path jet continuity
(hB : ∀ n, Continuous (fun s => (B s).jetLp n))     -- DERIVATIVE path jet continuity
(hd : ∀ t (ht : t ∈ Ioo 0 T') x,
      HasDerivAt (fun r => (A (projIcc 0 T' _ r)).field x) ((B ⟨t,…⟩).field x) t)
```

* `hA` = `Evolution.velocityField_jetLp_continuous` (done, from `ClassicalSolutionR.sobolev`'s
  continuous-in-time velocity datum path).
* `hd` (pointwise) = the time-`HasDerivAt` of the velocity from `velocity_smooth` — reachable.
* **`hB`** forces `B = ∂ₜu` path (`hd` + uniqueness of derivative pins `(B t).field = ∂ₜu(t,·)`
  at interior `t`) to have **jets continuous in time**.  Via the momentum split this reduces to the
  **time-continuity of the `∇p(s,·)` `L²` jets**.  The class provides NO such object:
  `ClassicalSolutionR.sobolev` is a continuous-in-time datum path for the *velocity* only,
  `MemForceR` gives one for the *force*, and the pressure carries only the **pointwise**
  `pressure_gradient : ∀ t, MemLp (∇p(t,·)) 2` (no continuity in `t`, no higher jets in `t`).
* **D01 P2 does not supply it.**  `pressureGradient_slice_smoothSquareIntegrableJets_of_memForceR`
  gives `SmoothSquareIntegrableJets (∇p(t,·))` at each **fixed** interior `t`; it says nothing
  about continuity as `t` varies.  Getting the `t`-continuity would mean building a
  *continuous-in-time* datum path for the momentum residual `h = f − (u·∇)u + νΔu` **and** pushing
  it through `Leray.lerayComplement` as a continuous composition — a genuine new analysis
  obligation (the time-regularity analogue of P2), not present in tree.  This **corrects** the
  `ENERGY_SPLIT.md` E4 note "B's jetLp continuity (routine) … the `∂ₜu` packaging is P2": the
  *packaging* is P2, but the *time-continuity* is a separate, unmet obligation.

**Alternative route also blocked.**  A direct "differentiate under the integral" proof of
`d/dt ∫‖u(t,x)‖² = 2∫⟨u,∂ₜu⟩` (Mathlib `hasDerivAt_integral_of_dominated_…`) needs an integrable
dominating function for `2⟨u(s,x),∂ₜu(s,x)⟩` uniform in `s` near `t`, i.e. uniform-in-time `L²`
control of `∂ₜu` — the same missing `∇p` time-regularity.  So E4 is blocked independently of the
vendor machinery, on `∇p`'s (equivalently `∂ₜu`'s) `L²` time-regularity.

**Delivered instead:** `energyIdentity_classical` takes the E4 value fact `hd : d = 2⟪u,∂ₜu⟫` as a
hypothesis and discharges everything else, so a later lane that establishes the `∂ₜu` time-regularity
(a new D01/C01 unit) plugs straight in.

## 4. Errors hit and fixed (verbatim)

4.1 **Ambiguous `Space`** — opening both `EulerSmoothLimit` (needed for `divergence`/`gradient`)
and `NavierStokes.ProblemStatement` (needed for the operators) both export `Space`:
`error: Ambiguous term  Space  Possible interpretations: NavierStokes.ProblemStatement.Space …
EulerSmoothLimit.Space`.  Fix: **selective** `open NavierStokes.ProblemStatement (temporalDerivative
advection spatialLaplacian pressureGradient coordinateVector spatialDivergence spatialDerivative
VelocityField PressureField)` — brings the operators, not `Space` (which stays `EulerSmoothLimit.Space`,
matching `Vocabulary.lean`).

4.2 **`Unknown identifier gradient_coordinate`** — it is `EulerMeanHarmonic.gradient_coordinate`
(`MeanHarmonicLaplacian.lean:13`), not opened; and its statement is already the `.ofLp i` form
`(gradient f x).ofLp i = partialDerivative f i x`, which matches the `PiLp.ext` goal.  Fix: qualify;
then `rfl`.

4.3 **`rw` chain "Did not find … ↑↑(ν•L−N−P) x"** — after `rw [hadd]` the RHS is
`(⇑(ν•L−N−P) + ⇑F) x`, i.e. `HAdd.hAdd (⇑…) (⇑…) x`, so `⇑(ν•L−N−P)` is not yet applied to `x` and the
next `coeFn` `rw` cannot match.  Fix: interleave `Pi.add_apply` / `Pi.sub_apply` / `Pi.smul_apply`
between the `coeFn` rewrites:
`rw [htemp, hadd, Pi.add_apply, hsub2, Pi.sub_apply, hsub1, Pi.sub_apply, hsmul, Pi.smul_apply, …]`.

4.4 **Laplacian bridge — inner `vectorPartial` not unfolded by `simp only`** — `simp only
[vectorPartial]` left `fderiv ℝ (vectorPartial u.field i) x …` (the inner `vectorPartial u.field i`
is an eta-function argument).  Fix: don't `simp`; after
`rw [laplacianField_field, congrFun (vector_laplacian_eq_sum u.field u.smooth) x]` the two sides are
definitionally the same coordinate sum, so plain `rfl` closes it.
