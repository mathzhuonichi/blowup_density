# ATTEMPTS — lane 335, T11 unit U12a (the periodic `H^m` energy identity)

Non-generated file. Route decisions, paths rejected, exact error text, residual.

## 0. Target

Lane 322's **missing fact A** (`ATTEMPTS_HIGH_ORDER.md` §3.1): for a genuine
`ClassicalSolutionT ν a f T`, at every `t ∈ Ioo 0 T`,

```
d/dt ‖u(t)‖²_{H^m} = −2ν‖∇u(t)‖²_{H^m} − 2⟪(u·∇)u, u⟫_{H^m} + 2⟪f, u⟫_{H^m}
```

delivered in exactly the shape `hRhigh` consumes for its
`HasDerivAt (fun r ↦ torusSobolevNormAt (m : ℝ) w.velocity r ^ 2) d t` component,
plus the corollary that U12b's pairing estimate turns it into `hRhigh`.

## 1. Route decision — what was **not** done, and why

### 1.1 Rejected: the `ℓ²`-datum-path route (Section 4's SL1/SL2 shape)

`ATTEMPTS_HIGH_ORDER.md` §3.1 proposed proving `ContDiffOn ℝ ∞ G` for the datum
path `G : ℝ → PeriodicSobolev m` and then `HasDerivAt (fun r ↦ ‖G r‖²) (2⟪G t, G' t⟫) t`,
i.e. Section 4's `A04.classical_hasSmoothSobolevPath` + `A04/TimeDerivative.lean`
+ `A04/MomentumDatum.lean`.  On this branch that route is blocked on lane 321's
`regularity` field, hence on the still-open `PeriodicQuantitativeLocalInput'`.

**It was not needed.**  `ClassicalSolutionT` already carries, for *every* natural
order, a datum path that is merely `ContinuousOn` — and continuity at one higher
order is exactly the domination the scalar route needs.  So this lane never
differentiates an `ℓ²`-valued path: it differentiates each scalar coefficient and
re-sums.  Consequence: the energy identity is **unconditional on a
`ClassicalSolutionT`**, with no named input at all, and does not wait for 311/313/321.

### 1.2 Rejected: rapid decay of `Q̂` and `p̂` for the domination

The first domination plan was to substitute the momentum equation into
`d/dt û` and then bound each of `f̂`, `Q̂ = ((u·∇)u)^`, `2πikᵢp̂` by a rapidly
decaying majorant.  `Q̂` would have needed the periodic convolution theorem plus
lane 327's `convolution_norm_bound`/`norm_convectionDatum_coeff_le`, and `p̂`
would have needed a decay estimate on the pressure (or the Leray complement).
Both are avoidable: the *trivial* bound

```
|(∂ₜuᵢ)^(r,k)| ≤ ∫_{T³} |∂ₜuᵢ(r,·)| ≤ sup_{[a,b]×cube} ‖∂ₜu‖ =: D      (no decay in k at all)
```

combined with `|û ᵢ(r,k)| ≤ M·W(k)^{−(m+2)}` from the order-`2m+4` datum path
already gives `|φ'ₖ(r)| ≤ 6MD·W(k)^{−2}`, which is summable
(`summable_inverse_periodicFrequencyWeight`).  Choosing the auxiliary order
`2m+4` instead of `m+3` is what removes every decay estimate on the source terms.
`exists_temporalDerivative_cube_bound` is then the only compactness argument in
the lane, and it uses vendor's `ResidualRegularity.contDiffOn_temporalDerivative`
for the joint continuity of `(r,x) ↦ ∂ₜu(r,x)` on the open slab.

### 1.3 Rejected: a Leray-projected statement of the coefficient momentum equation

The brief's spelling is `d/dt û(t)(k) = −ν4π²|k|²û(t)(k) + (P̂(f̂(t) − Q̂(t)))(k)`.
Proving the `P̂` form needs the extra step "the left-hand side is solenoidal,
therefore `P̂` acts as the identity on it, therefore the gradient term is the
Leray complement".  For the **energy identity** that step is dead weight: the
pressure term `∑ᵢ conj(û ᵢ(k))·2πikᵢp̂(k)` is annihilated at every single
frequency by coefficient-side solenoidality (lane 322's `torusPressureSymbol_drop`,
reproved here without the weight as `torusPressureSymbol_drop_raw`).  So the
module states the momentum equation in the **unprojected** form
`velocityDerivCoeffT_momentum`, which carries the explicit `2πikᵢ p̂(k)` term, and
drops it at the pairing step.  Equivalent content, one fewer construction; the
Leray projector is never invoked.

## 2. Paths tried, and the exact error text

### 2.1 `rw` through the T10 abbreviation of `periodicFourierCoeff`

```
rw [NSFormalization.Paper1.periodicFourierCoeff_eq_cube]
```
```
error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  Paper1.periodicFourierCoeff ?f ?k
in the target expression
  HasDerivAt (velocityCoeffT u i k) (periodicFourierCoeff (fun x => ↑((temporalDerivative u t x).ofLp i)) k) t
```
`Section3.T10.periodicFourierCoeff` is an eta-reduced `abbrev` of the *function*,
so the head constant in the goal is the T10 one and `rw` (syntactic) never
matches.  Fix: state the instance with a full type ascription first and then
rewrite with it —
`have heq : periodicFourierCoeff (fun x ↦ …) k = cubeIntegral (fun x ↦ …) := Paper1.periodicFourierCoeff_eq_cube _ k`.
The same trick is needed anywhere a `Paper1.*` coefficient lemma meets a T10-spelled goal.

### 2.2 `HasDerivAt.sum` is the sum-of-functions version

```
exact HasDerivAt.sum fun i _ ↦ hasDerivAt_norm_sq_complex …
```
```
error: Type mismatch … has type
  HasDerivAt (∑ i ∈ ?s, fun s => ‖velocityCoeffT u i k s‖ ^ 2) (…) t
but is expected to have type
  HasDerivAt (fun r => ∑ i, ‖velocityCoeffT u i k r‖ ^ 2) (…) t
```
At this pin the pointwise-lambda version is **`HasDerivAt.fun_sum`**
(`Mathlib/Analysis/Calculus/Deriv/Add.lean:218`); `HasDerivAt.sum` (`:222`) is
about `∑ i, A i` as a function-valued sum.

### 2.3 `Continuous.sub` feeds `Pi.sub` into higher-order unification

```
rw [periodicFourierCoeff_sub_real (hcf.sub hcadv) (hcgrad.sub hclap) k, …]
```
```
error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  periodicFourierCoeff (fun x => ↑(((fun x => (f (t, x)).ofLp i) - fun x => (advection w.velocity t x).ofLp i) x - …)) k
```
The implicit `{g h : Space → ℝ}` were solved from the `Continuous` arguments as
`Pi.sub` terms, not as the two summands.  Fix: pass them by name,
`periodicFourierCoeff_sub_real (g := fun x ↦ …) (h := fun x ↦ …) (hcf.sub hcadv) (hcgrad.sub hclap) k`.

### 2.4 `rw` with an `IsPeriodicSpatial` hypothesis

```
rw [hp x l, NavierStokes.PeriodicUniqueness.periodic_fderiv …]
```
```
error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  (fun x => v (t, x)) (x + coordinateVector l)
```
`hp x l` carries the un-beta-reduced application.  Fix: re-type it first,
`have h1 : v (t, x + coordinateVector l) = v (t, x) := hp x l`, then `rw [h1]`.

### 2.5 `λ` is not an identifier

`have hλ : … ` →
```
error: unexpected token 'λ'; expected command
```
Renamed to `hlam`.  (Cheap, but it costs a compile round.)

### 2.6 A `def` in a `have` makes `ring` fail on a goal stated without it

`hlapc` was first stated with `velocityCoeffT w.velocity i k t` while the
surrounding goal (after `simp only [velocityCoeffT, …]`) carried the unfolded
`periodicFourierCoeff (fun x ↦ ↑((w.velocity (t, x)).ofLp i)) k`:
```
The `ring` tactic failed to close the goal.
⊢ … + ↑(-(ν * periodicAngularFrequencySq k)) * velocityCoeffT w.velocity i k t
  = … + ↑(-(ν * periodicAngularFrequencySq k)) * periodicFourierCoeff (fun x => ↑((w.velocity (t, x)).ofLp i)) k
```
`ring` sees two distinct atoms.  Rule used throughout this module: inside a proof
that has already unfolded a coefficient `def`, every auxiliary `have` is stated
in the **same** (unfolded) vocabulary.

### 2.7 Wrong names / small surprises

* `Complex.sq_abs_eq_normSq_of_norm` — `error: Unknown constant`.  The pair at
  this pin is `Complex.sq_norm : ‖z‖^2 = normSq z` and
  `Complex.normSq_apply : normSq z = z.re*z.re + z.im*z.im`.
* The real-part lemmas actually used: `Complex.re_sum`, `Complex.re_ofReal_mul`,
  `Complex.ofReal_re`.  A bare `simp` on `(↑r * z).re` leaves
  `… ∨ ν = 0 ∨ periodicAngularFrequencySq k = 0` (it tries `mul_eq_mul_left_iff`);
  `simp only [Complex.sub_re, Complex.add_re, Complex.re_ofReal_mul, Complex.ofReal_re]`
  is the deterministic form.
* `lp.single_apply_self 2 0 x` does not unify against
  `(torusConstantDatum s c).1 i 0` — the subtype/`WithLp` coercions are in the
  way; a `change (lp.single 2 (0 : PeriodicFrequency) ((c i : ℝ) : ℂ) : PeriodicScalarData) 0 = _`
  first (the idiom of `torusConstantDatum_isDatum`) then `simp`.
* `IsCompact.exists_bound_of_continuousOn` applied to a
  `PeriodicSobolev`-valued path returns `∀ x ∈ s, ‖G x‖ ≤ M` directly — no outer
  `‖·‖` to strip (a `rwa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]` fails).
* Writing `_` for a bound variable inside a lambda body gives
  `error: don't know how to synthesize placeholder for argument 'x'`; name it.
* `HasSum.congr_fun h` expects `∀ b, <target function> b = <h's function> b`
  (not the reverse).
* `push_neg` is deprecated at this pin (warning only); replaced by an explicit
  `by_contra` + `not_not.mp`.

## 3. What is proved, what is not

**Proved unconditionally on a `ClassicalSolutionT`** (no named input, no
`def … : Prop`): `hasDerivAt_velocityCoeffT`, `velocityDerivCoeffT_momentum`,
`solenoidal_velocityCoeffT`, `torusPressureSymbol_drop_raw`,
`hasDerivAt_torusSobolevNormAt_sq`, `freqEnergyDerivT_split`,
`energyIdentity_of_classical`.

**Not proved here** — lane 322's **missing fact B**, U12b's tame pairing bound

```
|torusRealPairing Gm Nm| ≤ Chigh m * torusSobolevNormAt 2 w.velocity t *
    torusSobolevNormAt (m : ℝ) w.velocity t * torusGradientNormAt (m : ℝ) w.velocity t
```

for `Gm` the order-`m` datum of `u(t)` and `Nm` the order-`m` datum of
`(u·∇)u(t)` (= `convectionFieldT w.velocity`).  It enters
`hRhigh_of_pairingBound` / `higherOrderBound_of_pairingBound` as an **explicit
theorem argument**, spelled out in the binder; it is *not* a `def … : Prop`, and
it is not the target restated (it is a pointwise-in-`t` product estimate, while
the target is a uniform bound over `[0,S)` for the glued field of `SolvesBelowT`).
Satisfiability: the data are unique (`T10.datum_unique`), both sides are finite
real numbers at every classical solution, and the bound is the torus analogue of
`Section4.A03.outerProductTame` / the `research/A04/SL5_SPLIT.md` campaign;
lane 328's real-order projected convection CLM `H^r × H^r → H^{r-1}` is the
natural starting point.  With it, `PeriodicContinuationAPI.higherOrderBound`
closes (`higherOrderBound_of_pairingBound`).

## 4. Commands

```
cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T11.EnergyIdentity
cd verification && LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section3/T11/EnergyIdentity.lean
cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/T11/probes/energy_identity_closes.lean
cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/T11/axioms_energy_identity.lean
make check
make test
```
All clean, no warnings, no `sorry`/`admit`/`axiom`/`native_decide`, no
`set_option maxHeartbeats`; 51 `#guard_msgs`-checked axiom prints, each exactly
`[propext, Classical.choice, Quot.sound]`.
