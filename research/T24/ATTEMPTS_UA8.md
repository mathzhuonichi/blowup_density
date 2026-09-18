# ATTEMPTS — lane 424, T24a unit **Ua8** (`AffineVariationAPI.nonisolated`, `research/T24/Spec.lean:1104-1111`)

Positive and negative record for the non-isolation field of `prop:affine`
(`paper/sections/03-torus.tex:692-696`).  Closed; no residual goal.

## 1. Route that landed

Target (raw packet fields, `formalization/NSFormalization/Section3/T24/AffineNonisolated.lean`):

```
theorem nonisolated {ν : ℝ} {U F : VelocityField} (c : Space) (r τ₀ τ₁ : ℝ)
    (hτ₀ : 0 < τ₀) (hτ₁ : τ₁ < 1)
    (hvelocity_smooth : ContDiffOn ℝ ∞ U preSingularDomain) :
    ∀ b : VelocityField, AffineAdmissible c r τ₀ τ₁ b → b ≠ 0 → ∀ m : ℕ,
      Tendsto (fun lam : ℝ => affineCkSeminorm (tsupport b) m
          (fun z => affineVelocity U (lam • b) z - U z)) (𝓝 0) (𝓝 0) ∧
      Tendsto (fun lam : ℝ => affineCkSeminorm (tsupport b) m
          (fun z => affineForce ν U F (lam • b) z - F z)) (𝓝 0) (𝓝 0)
```

Three steps:

1. **Seminorm algebra** (§1 of the module).  `affineCkSeminorm` (lane 392,
   `AffineBasics.lean:50`) is an `ℝ≥0∞`-valued `∑_{k≤m} ⨆_{z∈K}` so all three facts
   are elementary but none were in the tree:
   `affineCkSeminorm_const_smul` (exact homogeneity, via
   `iteratedFDeriv_const_smul_apply'` + `enorm_smul` + `ENNReal.mul_iSup` pushed
   through **both** binders of `⨆ z ∈ K`), `affineCkSeminorm_add_le`
   (`fun_iteratedFDeriv_add_apply` + `enorm_add_le` + `iSup₂_le`/`le_iSup₂`), and
   `affineCkSeminorm_lt_top` (`ContDiff.continuous_iteratedFDeriv` +
   `IsCompact.exists_bound_of_continuousOn` + `ENNReal.ofReal_lt_top`).
   The brief's fallback name `ckSeminorm_lt_top_of_contDiff_compact` was not needed
   as a separate general helper — `affineCkSeminorm_lt_top` *is* that statement for
   the registered seminorm.
2. **Scaling identity** (§2).  Velocity: `Ũ_{λb} − U = λ b` exactly
   (`affineVelocity_smul_sub`).  Force: the paper's
   `F̃_{λb} − F = λ L_U b + λ²(b·∇)b` is **regrouped** as
   `λ · (affineForce ν U 0 b) + (λ²−λ) · (b·∇)b` (`affineForce_smul_sub`), using the
   vendored `spatialDerivative_const_smul` / `spatialLaplacian_const_smul`
   (`NavierStokes.ResidualCalculus:178,203`), `fderiv_fun_const_smul` for `∂ₜ`, and
   `map_smul` for the `(b·∇)U` term (which needs **no** differentiability of `U`).
   Closed by `module` after the five operator rewrites.
3. **Limits** (§3).  `‖b‖_{C^m}`, `‖affineForce ν U 0 b‖_{C^m}`, `‖(b·∇)b‖_{C^m}` are
   all `< ⊤` on the compact `tsupport b`; velocity gives the *equality*
   `‖λ‖ₑ · ‖b‖_{C^m}`, force the *bound*
   `≤ ‖λ‖ₑ·C_m + ‖λ²−λ‖ₑ·C_m'`; `ENNReal.Tendsto.mul_const` +
   `tendsto_of_tendsto_of_tendsto_of_le_of_le` between `0` and that bound.

**Hypotheses actually consumed:** `velocity_smooth`, `0 < τ₀`, `τ₁ < 1`.
**Not** consumed: the packet's `force_smooth` / `force_support`, `0 < ν`, the
pressure, and the `b ≠ 0` clause (it is part of the Spec statement and is carried,
but the proof does not use it).  No named input.

## 2. Design decision, with the reason

The paper's literal grouping `λ L_U b + λ²(b·∇)b` was **not** used.
`L_U b = ∂ₜb − νΔb + (U·∇)b + (b·∇)U` is *not globally* `ContDiff` — `U` is only known
smooth on `preSingularDomain`, so `L_U b` is undefined/nonsmooth for `t ≥ 1` — while
`fun_iteratedFDeriv_add_apply` and `iteratedFDeriv_const_smul_apply'` in the form used
here want `ContDiffAt` of each summand.  Making the literal split work would have
required a pointwise (`ContDiffAt`-on-`tsupport b`) variant of the two seminorm lemmas.
Regrouping to `λ·(F̃_b − F) + (λ²−λ)·(b·∇)b` avoids that entirely: **both** coefficient
fields are globally smooth —
`F̃_b − F = affineForce ν U (fun _ => 0) b` is lane 414's `force_smooth` applied at
the **zero** force (which is why `force_smooth` on the packet's `F` is not needed), and
`(b·∇)b = advection b` is globally smooth by the vendored `contDiffOn_advection` on
`univ`.  The resulting bound `C_m|λ| + C_m'|λ²−λ|` differs from the paper's
`C_m|λ| + C_m'λ²` only by absorbing a `|λ|` into the first constant; the Spec asserts
the `Tendsto`, not the constants, so nothing is weakened.

## 3. Things that failed / cost time (negative record)

* `htend0.mul_const (Or.inr h.ne)` resolves to the **generic** `Filter.Tendsto.mul_const`,
  which asks for `SeparatelyContinuousMul ℝ≥0∞` (no instance) and then reports
  `Application type mismatch: Or.inr … of sort Prop but is expected to have type ℝ≥0∞`.
  Dot notation must be abandoned: write `ENNReal.Tendsto.mul_const htend0 (Or.inr h.ne)`.
* `ContDiff.differentiable` takes `(hn : n ≠ 0)`, not `1 ≤ n`.  `(by exact_mod_cast le_top)`
  fails with `mod_cast has type ?m ≤ ⊤ but is expected to have type ¬⊤ = 0`; `(by simp)` works.
* Casting `∞` down: `hf.of_le (by exact_mod_cast le_top)` works when the target index is a
  **variable** `(k : ℕ)`, but fails for the numeral in `ContDiff ℝ 2 _`
  (`mod_cast has type ?m ≤ ⊤ but is expected to have type 2 ≤ ∞`).  There the repo's existing
  spelling `(WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))` (lane 398) is required.
* `enorm_add_le _ _` leaves the normed group a metavariable
  (`typeclass instance problem is stuck: ESeminormedAddMonoid ?m`); both arguments must be given
  explicitly.
* `zero_le _` — in this context `zero_le` already has its argument implicit, so `zero_le _` gives
  `Function expected at zero_le`.
* Writing `∞` in a bare `(k : WithTop ℕ∞) ≤ ∞` goal under `open scoped ContDiff ENNReal` is
  ambiguous (`∞ : ℝ≥0∞` vs `∞ : ℕ∞ω`); only write it where elaboration fixes the type.
* **Probe, worst time sink:** `Contracts.V1.Packet` does **not** import `Contracts.V1.Data`, so the
  Spec's `SpaceTimeField` is an unknown identifier — `autoImplicit` silently turned it into a fresh
  type variable and produced eight misleading errors of the form
  `b has type SpaceTimeField but is expected to have type VelocityField`.  Fixed by importing
  `Contracts.V1.Data` and restating over `VelocityField`, with the alias recorded as the `rfl`
  bridge `SpaceTimeField_eq` (`Contracts/V1/Data.lean:104`).  `open BlowupDensity.Contracts.V1.Data`
  alone is not enough (the namespace is unknown without the import).

## 4. Non-vacuity

`research/T24/probes/affine_nonisolated_closes.lean`:

* the six `rfl` bridges Spec-vocabulary → canonical, including
  `ckSeminormE ≡ affineCkSeminorm`;
* `nonisolated_on_canonical` — the registered field on `Bindings.packet ν hν`, fed only the
  packet's `velocity_smooth`;
* lane 398's nonzero witness `bWitness = ∇×(θ·φ·e₁)` rebuilt (lane 417's shared
  `Section3/T24/AffineWitness.lean` is not on this base), both limits instantiated at it;
* `nonisolated_nontrivial` — at `λ = 1`, `m = 0` the velocity seminorm of the nonzero witness is
  **nonzero**, so the two `Tendsto` statements are limits of a not-identically-zero function.  This
  is the check that the `ℝ≥0∞` `⨆` choice was made for: with a real `sSup` the junk value would make
  the limits hold for the wrong reason.

## 5. Gates

* `cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T24.AffineNonisolated`
  → `Build completed successfully (3009 jobs).`
* `lake env lean ../formalization/NSFormalization/Section3/T24/AffineNonisolated.lean` → no output.
* `lake env lean ../research/T24/probes/affine_nonisolated_closes.lean` → 8 `#print axioms` lines,
  all `[propext, Classical.choice, Quot.sound]`.
* `lake env lean ../research/T24/axioms_ua8.lean` → 8 lines, all `[propext, Classical.choice, Quot.sound]`.
* `make check` → EXIT 0.
