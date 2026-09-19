# T15 U8 — attempts, lane 446

## Route that closes

1. Read `CLAUDE.md`, `T15_SPLIT.md` §0/U8, reports 376/384/421,
   lane 439's report via `git show`, the paper's scaling proposition, and
   the first 40 lesson lines. Read the 13 canonical `ClassicalSolutionT`
   fields in `T10/PeriodicData.lean` (T11 consumes that canonical structure).
2. Build `SingleCopy` before elaborating this module. Reuse
   `Source.parabolic_equation`, `dilate_divergence`, and the raw extension
   equation. The binding's source-time calculation is reproduced locally;
   `formalization/` imports no `Bindings`.
3. For a closed spatial carrier `C` strictly inside the cube, apply vendor
   `locallyFinite_support_translate` to the time-independent indicator of C.
   Each translated support is closed. `LocallyFinite.iInter_compl_mem_nhds`
   simultaneously excludes every nonzero translate near a closed-cube point.
   Intersect with the open time condition `t<T` and collapse the lattice sum.
4. Choose the coordinate-floor lattice vector at the original point, then
   hold it fixed on the entire neighbourhood. Periodicity transports the
   neighbourhood equality to any spatial point. This avoids differentiating
   a discontinuous representative map. Two applications of local derivative
   congruence handle the Laplacian; value and first-derivative congruence
   handle advection. The generic dilation identities at scale one supply
   translation invariance.
5. Subtracting the pressure mean leaves the gradient unchanged, by
   `fderiv_sub_const`. Search found the same proof already in
   `Section3/T18/Momentum.lean`; it is re-proved here to avoid the inverse
   T15-to-T18 dependency. The initial slice uses `eps_time` and zero-past.

No analytic residual remains, no additional named input, and no placeholder.
The smooth raw extension clauses are unnecessary for these identities because
Fréchet derivative congruence and the existing dilation formulas also hold
for totalized derivatives. This is a strengthening of the requested premises.

## Probe choice / lane 439 observation

Lane 439's `torusChart` observation is that its representative has coordinates
in `Ioc 0 1`, hence in the closed fundamental cube; single-copy equality
therefore gives pointwise equality after torus lift. We read and describe
this, and do not import that branch. It is insufficient by itself for PDE
transport: derivative equality needs local equality, proved here even on the
closed-cube boundary.

`energy_mixed_closes.lean` is not present in this checkout (checked by file
search and the lane-439 branch report). Its energy/mixed-norm assumptions
are not the raw PDE clauses. The fallback placement bump has spatial field
`bump x • coordinateVector 0`, scalar pressure `bump x`, and zero force;
it supplies geometry, not a divergence-free forced NS packet. Rather than
assume missing PDE clauses on that bump, the probe constructs an actual
`PlacementData` for `Bindings.packet 1`, using the same cube centre and ball
radius 3/8. Its threshold is `min (1/2) (1/(8*(R+1)))`, with R a positive
bound for the compact union of the velocity carrier and the force projection.
All three theorems are instantiated with discharged hypotheses; the source
and the periodized velocity are proved nonzero at active times.

## Failed elaborations (verbatim diagnostics)

Logs below include warnings accompanying failed attempts. Repeated diagnostics
are retained so that each actual unsuccessful run is recorded.

### F1: indicator support needs a membership split; nonmembership is a double negation; inferred composition-shaped germs do not rewrite lambda derivatives.

```text
../formalization/NSFormalization/Section3/T15/Equation.lean:84:38: error: unsolved goals
V : Type u_1
inst✝ : NormedAddCommGroup V
v : SpaceTime → V
C : Set Space
hC : IsClosed C
hCQ : C ⊆ interior fundamentalCube
T : ℝ
hv : ∀ t < T, (Function.support fun x => v (t, x)) ⊆ C
t : ℝ
ht : t < T
x : Space
hx : x ∈ fundamentalCube
g : Space → ℝ := C.indicator fun x => 1
⊢ C ⊆ Function.support fun x => 1
../formalization/NSFormalization/Section3/T15/Equation.lean:112:6: error: Type mismatch
  lattice_term_eq_zero_of_mem_cube hgs hx hnzero
has type
  g (x - latticeVector n) = 0
but is expected to have type
  (t, x) ∉ Function.support (NavierStokes.PeriodicLocalization.translate G n)
../formalization/NSFormalization/Section3/T15/Equation.lean:128:72: error: unsolved goals
u v : VelocityField
p q : PressureField
t : ℝ
x : Space
hu : u =ᶠ[𝓝 (t, x)] v
hp : p =ᶠ[𝓝 (t, x)] q
ν : ℝ
hs : (u ∘ fun x => (t, id x)) =ᶠ[𝓝 x] v ∘ fun x => (t, id x)
hp' : (p ∘ fun x => (t, id x)) =ᶠ[𝓝 x] q ∘ fun x => (t, id x)
ht : (u ∘ fun x_1 => (id x_1, x)) =ᶠ[𝓝 t] v ∘ fun x_1 => (id x_1, x)
hd : spatialDerivative u t x = spatialDerivative v t x
hl : spatialLaplacian u t x = spatialLaplacian v t x
⊢ (fderiv ℝ (fun s => u (s, x)) t) 1 + (spatialDerivative v t x) (v (t, x)) - ν • spatialLaplacian v t x +
      ∑ i, (fderiv ℝ (fun y => p (t, y)) x) (coordinateVector i) • coordinateVector i =
    (fderiv ℝ (fun s => v (s, x)) t) 1 + (spatialDerivative v t x) (v (t, x)) - ν • spatialLaplacian v t x +
      ∑ i, (fderiv ℝ (fun y => q (t, y)) x) (coordinateVector i) • coordinateVector i
../formalization/NSFormalization/Section3/T15/Equation.lean:142:24: warning: This simp argument is unused:
  ht.fderiv_eq

Hint: Omit it from the simp argument list.
  [apply] simp only [NavierStokesR3.ProblemStatement.navierStokesResidual, temporalDerivative, advection, hd,
    hu.eq_of_nhds, hl, pressureGradient, hp'.fderiv_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
../formalization/NSFormalization/Section3/T15/Equation.lean:143:26: warning: This simp argument is unused:
  hp'.fderiv_eq

Hint: Omit it from the simp argument list.
  [apply] simp only [NavierStokesR3.ProblemStatement.navierStokesResidual, temporalDerivative, ht.fderiv_eq, advection,
    hd, hu.eq_of_nhds, hl, pressureGradient]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
../formalization/NSFormalization/Section3/T15/Equation.lean:147:83: error: unsolved goals
u v : VelocityField
t : ℝ
x : Space
hu : u =ᶠ[𝓝 (t, x)] v
hs : (u ∘ fun x => (t, id x)) =ᶠ[𝓝 x] v ∘ fun x => (t, id x)
⊢ ∑ i, ((fderiv ℝ (fun y => u (t, y)) x) (coordinateVector i)).ofLp i =
    ∑ i, ((fderiv ℝ (fun y => v (t, y)) x) (coordinateVector i)).ofLp i
../formalization/NSFormalization/Section3/T15/Equation.lean:149:51: warning: This simp argument is unused:
  hs.fderiv_eq

Hint: Omit it from the simp argument list.
  [apply] simp only [spatialDivergence, spatialDerivative]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
```

### F2: floor arithmetic has the opposite addition order; lattice spellings need a typed change; simplification does not unfold a partially applied dilation under the residual.

```text
../formalization/NSFormalization/Section3/T15/Equation.lean:159:65: error: Application type mismatch: The argument
  Int.lt_floor_add_one ?m.74
has type
  ?m.74 < ↑⌊?m.74⌋ + 1
but is expected to have type
  x.ofLp i < 1 + ↑⌊x.ofLp i⌋
in the application
  sub_lt_iff_lt_add.mpr (Int.lt_floor_add_one ?m.74)
../formalization/NSFormalization/Section3/T15/Equation.lean:168:2: error: Type mismatch: After simplification, term
  Eq.symm h
 has type
  NavierStokes.PeriodicLocalization.periodize v (t, x - latticeVector n) =
    NavierStokes.PeriodicLocalization.periodize v (t, x - latticeVector n + NavierStokes.PeriodicLocalization.lattice n)
but is expected to have type
  NavierStokes.PeriodicLocalization.periodize v (t, x - latticeVector n) =
    NavierStokes.PeriodicLocalization.periodize v (t, x)
../formalization/NSFormalization/Section3/T15/Equation.lean:196:2: error: Type mismatch: After simplification, term
  parabolic_residual ν 1 0 a u p t x
 has type
  Source.residual ν (dilateField 1 1 1 0 a u) (dilateField 1 1 1 0 a p) t x = Source.residual ν u p t (x - a)
but is expected to have type
  NavierStokesR3.ProblemStatement.navierStokesResidual ν (fun z => u (z.1, z.2 - a)) (fun z => p (z.1, z.2 - a)) t x =
    NavierStokesR3.ProblemStatement.navierStokesResidual ν u p t (x - a)
../formalization/NSFormalization/Section3/T15/Equation.lean:203:2: error: Type mismatch: After simplification, term
  dilate_divergence 1 1 1 0 a u t x
 has type
  spatialDivergence (dilateField 1 1 1 0 a u) t x = spatialDivergence u t (x - a)
but is expected to have type
  spatialDivergence (fun z => u (z.1, z.2 - a)) t x = spatialDivergence u t (x - a)
```

### F3: F2 repeated while adding the field wrappers; their implicit field cannot be inferred through the periodizer. Specify `(v := scaledVelocity …)` / `(v := scaledPressure …)`.

```text
../formalization/NSFormalization/Section3/T15/Equation.lean:159:65: error: Application type mismatch: The argument
  Int.lt_floor_add_one ?m.74
has type
  ?m.74 < ↑⌊?m.74⌋ + 1
but is expected to have type
  x.ofLp i < 1 + ↑⌊x.ofLp i⌋
in the application
  sub_lt_iff_lt_add.mpr (Int.lt_floor_add_one ?m.74)
../formalization/NSFormalization/Section3/T15/Equation.lean:168:2: error: Type mismatch: After simplification, term
  Eq.symm h
 has type
  NavierStokes.PeriodicLocalization.periodize v (t, x - latticeVector n) =
    NavierStokes.PeriodicLocalization.periodize v (t, x - latticeVector n + NavierStokes.PeriodicLocalization.lattice n)
but is expected to have type
  NavierStokes.PeriodicLocalization.periodize v (t, x - latticeVector n) =
    NavierStokes.PeriodicLocalization.periodize v (t, x)
../formalization/NSFormalization/Section3/T15/Equation.lean:196:2: error: Type mismatch: After simplification, term
  parabolic_residual ν 1 0 a u p t x
 has type
  Source.residual ν (dilateField 1 1 1 0 a u) (dilateField 1 1 1 0 a p) t x = Source.residual ν u p t (x - a)
but is expected to have type
  NavierStokesR3.ProblemStatement.navierStokesResidual ν (fun z => u (z.1, z.2 - a)) (fun z => p (z.1, z.2 - a)) t x =
    NavierStokesR3.ProblemStatement.navierStokesResidual ν u p t (x - a)
../formalization/NSFormalization/Section3/T15/Equation.lean:203:2: error: Type mismatch: After simplification, term
  dilate_divergence 1 1 1 0 a u t x
 has type
  spatialDivergence (dilateField 1 1 1 0 a u) t x = spatialDivergence u t (x - a)
but is expected to have type
  spatialDivergence (fun z => u (z.1, z.2 - a)) t x = spatialDivergence u t (x - a)
../formalization/NSFormalization/Section3/T15/Equation.lean:216:2: error: Tactic `apply` failed: could not unify the type of `periodize_eventuallyEq_translate
  (IsCompact.isClosed (affineImage_compact place.Kstar_compact))
  (LE.le.trans (affineImage_subset_ball hε place.eps_space) (ball_subset_interior_cube place.chartBall_in_cube)) ?m.118
  ht x`
  NavierStokes.PeriodicLocalization.periodize ?m.80 =ᶠ[𝓝 (t, x)] fun z =>
    ?m.80 (z.1, z.2 - latticeVector fun i => ⌊x.ofLp i⌋)
with the goal
  periodizedScaledVelocity u place.x₀ place.T ε =ᶠ[𝓝 (t, x)] fun z =>
    scaledVelocity u place.x₀ place.T ε (z.1, z.2 - latticeVector fun i => ⌊x.ofLp i⌋)

u f : VelocityField
p : PressureField
K : Set Space
hK : IsCompact K
hu : ∀ t ∈ Ico 0 1, (tsupport fun x => u (t, x)) ⊆ K
place : PlacementData u p f K
ε : ℝ
hε : ε ∈ Ioc 0 place.ε₀
t : ℝ
ht : t < place.T
x : Space
⊢ periodizedScaledVelocity u place.x₀ place.T ε =ᶠ[𝓝 (t, x)] fun z =>
    scaledVelocity u place.x₀ place.T ε (z.1, z.2 - latticeVector fun i => ⌊x.ofLp i⌋)
../formalization/NSFormalization/Section3/T15/Equation.lean:234:2: error: Tactic `apply` failed: could not unify the type of `periodize_eventuallyEq_translate
  (IsCompact.isClosed (affineImage_compact place.Kstar_compact))
  (LE.le.trans (affineImage_subset_ball hε place.eps_space) (ball_subset_interior_cube place.chartBall_in_cube)) ?m.118
  ht x`
  NavierStokes.PeriodicLocalization.periodize ?m.80 =ᶠ[𝓝 (t, x)] fun z =>
    ?m.80 (z.1, z.2 - latticeVector fun i => ⌊x.ofLp i⌋)
with the goal
  periodizedScaledPressure p place.x₀ place.T ε =ᶠ[𝓝 (t, x)] fun z =>
    scaledPressure p place.x₀ place.T ε (z.1, z.2 - latticeVector fun i => ⌊x.ofLp i⌋)

u f : VelocityField
p : PressureField
K : Set Space
hK : IsCompact K
hp : ∀ t ∈ Ico 0 1, (tsupport fun x => p (t, x)) ⊆ K
place : PlacementData u p f K
ε : ℝ
hε : ε ∈ Ioc 0 place.ε₀
t : ℝ
ht : t < place.T
x : Space
⊢ periodizedScaledPressure p place.x₀ place.T ε =ᶠ[𝓝 (t, x)] fun z =>
    scaledPressure p place.x₀ place.T ε (z.1, z.2 - latticeVector fun i => ⌊x.ofLp i⌋)
```

### F4: explicit dilation function equalities fix the unfolding, but the copied residual requires a typed `change Source.residual …`; wrapper inference was still unresolved.

```text
../formalization/NSFormalization/Section3/T15/Equation.lean:203:2: error: Type mismatch: After simplification, term
  h
 has type
  @Eq Space (Source.residual ν (fun z => u (z.1, z.2 - a)) (fun z => p (z.1, z.2 - a)) t x)
    (Source.residual ν u p t (x - a))
but is expected to have type
  @Eq NavierStokesR3.ProblemStatement.Space
    (NavierStokesR3.ProblemStatement.navierStokesResidual ν (fun z => u (z.1, z.2 - a)) (fun z => p (z.1, z.2 - a)) t x)
    (NavierStokesR3.ProblemStatement.navierStokesResidual ν u p t (x - a))
../formalization/NSFormalization/Section3/T15/Equation.lean:225:2: error: Tactic `apply` failed: could not unify the type of `periodize_eventuallyEq_translate
  (IsCompact.isClosed (affineImage_compact place.Kstar_compact))
  (LE.le.trans (affineImage_subset_ball hε place.eps_space) (ball_subset_interior_cube place.chartBall_in_cube)) ?m.118
  ht x`
  NavierStokes.PeriodicLocalization.periodize ?m.80 =ᶠ[𝓝 (t, x)] fun z =>
    ?m.80 (z.1, z.2 - latticeVector fun i => ⌊x.ofLp i⌋)
with the goal
  periodizedScaledVelocity u place.x₀ place.T ε =ᶠ[𝓝 (t, x)] fun z =>
    scaledVelocity u place.x₀ place.T ε (z.1, z.2 - latticeVector fun i => ⌊x.ofLp i⌋)

u f : VelocityField
p : PressureField
K : Set Space
hK : IsCompact K
hu : ∀ t ∈ Ico 0 1, (tsupport fun x => u (t, x)) ⊆ K
place : PlacementData u p f K
ε : ℝ
hε : ε ∈ Ioc 0 place.ε₀
t : ℝ
ht : t < place.T
x : Space
⊢ periodizedScaledVelocity u place.x₀ place.T ε =ᶠ[𝓝 (t, x)] fun z =>
    scaledVelocity u place.x₀ place.T ε (z.1, z.2 - latticeVector fun i => ⌊x.ofLp i⌋)
../formalization/NSFormalization/Section3/T15/Equation.lean:243:2: error: Tactic `apply` failed: could not unify the type of `periodize_eventuallyEq_translate
  (IsCompact.isClosed (affineImage_compact place.Kstar_compact))
  (LE.le.trans (affineImage_subset_ball hε place.eps_space) (ball_subset_interior_cube place.chartBall_in_cube)) ?m.118
  ht x`
  NavierStokes.PeriodicLocalization.periodize ?m.80 =ᶠ[𝓝 (t, x)] fun z =>
    ?m.80 (z.1, z.2 - latticeVector fun i => ⌊x.ofLp i⌋)
with the goal
  periodizedScaledPressure p place.x₀ place.T ε =ᶠ[𝓝 (t, x)] fun z =>
    scaledPressure p place.x₀ place.T ε (z.1, z.2 - latticeVector fun i => ⌊x.ofLp i⌋)

u f : VelocityField
p : PressureField
K : Set Space
hK : IsCompact K
hp : ∀ t ∈ Ico 0 1, (tsupport fun x => p (t, x)) ⊆ K
place : PlacementData u p f K
ε : ℝ
hε : ε ∈ Ioc 0 place.ε₀
t : ℝ
ht : t < place.T
x : Space
⊢ periodizedScaledPressure p place.x₀ place.T ε =ᶠ[𝓝 (t, x)] fun z =>
    scaledPressure p place.x₀ place.T ε (z.1, z.2 - latticeVector fun i => ⌊x.ofLp i⌋)
```

### F5: wrapper inference fixed; the copied-residual spelling remains. A typed `change` resolves the definitional equality before `simpa`.

```text
../formalization/NSFormalization/Section3/T15/Equation.lean:203:2: error: Type mismatch: After simplification, term
  h
 has type
  @Eq Space (Source.residual ν (fun z => u (z.1, z.2 - a)) (fun z => p (z.1, z.2 - a)) t x)
    (Source.residual ν u p t (x - a))
but is expected to have type
  @Eq NavierStokesR3.ProblemStatement.Space
    (NavierStokesR3.ProblemStatement.navierStokesResidual ν (fun z => u (z.1, z.2 - a)) (fun z => p (z.1, z.2 - a)) t x)
    (NavierStokesR3.ProblemStatement.navierStokesResidual ν u p t (x - a))
```

### P1: nlinarith does not unfold interval membership to extract positivity; provide `hε.1` and the nonnegative product `(1/2-ε)*(1/2+ε)`.

```text
../research/T15/probes/equation_closes.lean:71:4: error: linarith failed to find a contradiction
ε : ℝ
hε : ε ∈ Ioc 0 threshold
he : ε ≤ 1 / 2
a✝ : 1 ≤ 2 * ε ^ 2
⊢ False
failed
../research/T15/probes/equation_closes.lean:81:4: error: linarith failed to find a contradiction
ε : ℝ
hε : ε ∈ Ioc 0 threshold
y : Space
hy : y ∈ carrier
heq : center + ε • y - center = ε • y
hden : 0 < 8 * (radius + 1)
he : ε * (8 * (radius + 1)) ≤ 1
hn : ε * ‖y‖ ≤ ε * radius
a✝ : 3 / 8 ≤ ε * ‖y‖
⊢ False
failed
```

### P2: active-time bound needs the explicit positive product `ε²*(1-s)`; field_simp needs the explicit proof `ε ≠ 0`.

```text
../research/T15/probes/equation_closes.lean:126:20: error: linarith failed to find a contradiction
case right
s : ℝ
hs : s ∈ Ioo 0 1
y : Space
hy : packet.velocity (s, y) ≠ 0
ε : ℝ := place.ε₀
hε : ε ∈ Ioc 0 place.ε₀
he2 : 0 < ε ^ 2
t : ℝ := place.T - ε ^ 2 + ε ^ 2 * s
x : Space := place.x₀ + ε • y
a✝ : place.T ≤ place.T - ε ^ 2 + ε ^ 2 * s
⊢ False
failed
Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
../research/T15/probes/equation_closes.lean:135:4: error: unsolved goals
case fst
s : ℝ
hs : s ∈ Ioo 0 1
y : Space
hy : packet.velocity (s, y) ≠ 0
ε : ℝ := place.ε₀
hε : ε ∈ Ioc 0 place.ε₀
he2 : 0 < ε ^ 2
t : ℝ := place.T - ε ^ 2 + ε ^ 2 * s
x : Space := place.x₀ + ε • y
ht : t ∈ Ioo 0 place.T
hyK : y ∈ packet.carrier
hx : x ∈ fundamentalCube
⊢ ε ^ 2 * s * ε⁻¹ ^ 2 = s
```

### P3: the completed nonzero proof emitted an unnecessary `<;>` warning; replace it by sequential tactics for a silent gate.

```text
../research/T15/probes/equation_closes.lean:138:6: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
```

## Discovery corrections

The guessed branch name was wrong:

```text
fatal: invalid object name 'erenup/439-T15-U4-energy'.
```

`git branch -a --list '*439*'` found
`erenup/439-T15-U4-U5-energy-mixed`; its report was then read with `git show`.
The R3 source path is `NavierStokes/R3/ProblemStatement.lean`, found with
`rg -n 'def navierStokesResidual' vendor formalization`, after this diagnostic:

```text
rg: vendor/NavierStokesAndEuler/NavierStokesR3/ProblemStatement.lean: No such file or directory (os error 2)
```

A search using guessed T14 filenames also failed; the actual registered
constructor is `verification/Bindings/Packet.lean`:

```text
rg: formalization/NSFormalization/Section3/T14/Packet.lean: No such file or directory (os error 2)
rg: formalization/NSFormalization/Section3/T14/Assembly.lean: No such file or directory (os error 2)
zsh:1: no matches found: research/T15/probes/*energy*
```

## Final checks

The Equation build, silent direct elaboration, silent concrete probe,
18-declaration standard-axiom audit, `make check`, `lake test`, and contract
mutation checks all pass. No heartbeat override was needed.
