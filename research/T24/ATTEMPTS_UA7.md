# T24a Ua7 — `infinite_dimensional` (lane 417): attempts, decisions, negatives

Target (`research/T24/Spec.lean:1085-1087`, `paper/sections/03-torus.tex:688-691`):

```
infinite_dimensional : ∃ b : ℕ → SpaceTimeField,
  (∀ n : ℕ, AffineAdmissible c r τ₀ τ₁ (b n)) ∧ LinearIndependent ℝ b
```

Delivered (`formalization/NSFormalization/Section3/T24/AffineFamily.lean`):

```
theorem infinite_dimensional (c : Space) (r τ₀ τ₁ : ℝ) (hr : 0 < r) (hτ : τ₀ < τ₁) :
    ∃ b : ℕ → VelocityField,
      (∀ n : ℕ, AffineAdmissible c r τ₀ τ₁ (b n)) ∧ LinearIndependent ℝ b
```

`SpaceTimeField` is literally `VelocityField` (`Contracts/V1/Data.lean:104`, `abbrev`); the probe
records the `rfl` and states the field in both spellings.

## Decisions

1. **Promoted the lane 398 witness into a library, as the brief asked.**
   `research/T24/probes/affine_momentum_nonzero.lean` builds exactly one witness on the fixed
   cylinder `ball 0 1 × (1/4,3/4)`.  Ua7 needs a whole sequence, so the construction was lifted
   verbatim into a new module `Section3/T24/AffineWitness.lean`, parameterised by an arbitrary
   time bump `θ : ContDiffBump t₀` and spatial bump `φ : ContDiffBump x₀`.  The 398 probe file was
   **not** edited (ground rule: no edits to existing modules); it is now the instance
   `t₀ = 1/2`, `x₀ = 0`, `θ = ⟨1/16,1/8⟩`, `φ = ⟨1/2,3/4⟩` of `AffineWitness.curlBump`.

2. **Geometry: geometric shrinking along one axis, not an accumulating segment with
   hand-chosen radii.**  Centres `center c r n = c + (r·2⁻ⁿ/2) • e₁`, radii
   `ballRadius r n = r·2⁻ⁿ/16`.  Two facts:
   * inside: `r·2⁻ⁿ/2 + r·2⁻ⁿ/16 = 9/16 · r·2⁻ⁿ ≤ 9r/16 < r`;
   * disjoint, `n < m`: `2⁻ᵐ ≤ 2⁻ⁿ/2`, so radii sum `≤ 3/32 · r·2⁻ⁿ` while the centre gap is
     `≥ 1/4 · r·2⁻ⁿ = 8/32 · r·2⁻ⁿ`.
   Both are linear in the two atoms `r·2⁻ⁿ`, `r·2⁻ᵐ`, so `linarith` closes them after one
   `mul_le_mul_of_nonneg_left`.  This was chosen over `ℤ`-power or `1/(n+1)`-style spacings
   precisely because it keeps every inequality linear.

3. **`scale` is `(2:ℝ)⁻¹ ^ n` with its three facts proved by hand**
   (`scale_pos`, `scale_le_one` by induction, `scale_succ`, and `scale_antitone` via
   `antitone_nat_of_succ_le`) rather than hunting for the current Mathlib name of
   "`a ≤ 1 → n ≤ m → a^m ≤ a^n`" on ℝ (`pow_le_pow_right_of_le_one'` in the file found by grep is
   the ordered-monoid `'`-primed version).  Four short proofs beat one fragile name.

4. **Linear independence without a "nonzero at a *named* point" lemma.**
   `AffineWitness.curlBump_ne_zero` only says `b n ≠ 0`, i.e. `∃ z, b n z ≠ 0` — but that `z` is
   automatically inside the carrier (a point where a function is nonzero is in its support, hence
   in its `tsupport`).  So no extra "the bump is `1` at the centre and the curl is nonzero *there*"
   analysis was needed: `linearIndependent_iff'`, evaluate the vanishing combination at that `z`,
   `Finset.sum_eq_single_of_mem` kills every other term by disjointness of the balls, then
   `smul_eq_zero`.

## Negatives / things that failed on the way

* `positivity` cannot prove `0 < r * scale n` (twice: in `ballRadius_pos` and in
  `closedBall_subset_ball`), because `scale` is an ordinary `def` and `positivity` does not look at
  the hypothesis `0 < scale n` in context.  Exact error:
  `error: NSFormalization/Section3/T24/AffineFamily.lean:102:36: failed to prove
  positivity/nonnegativity/nonzeroness`.  Replaced by `mul_pos hr (scale_pos n)`.
* First draft put `open Set` / `open NavierStokes.ProblemStatement` **inside**
  `namespace AffineFamily`, so the top-level `infinite_dimensional` (stated after
  `end AffineFamily`) lost `Space` and `VelocityField` and Lean auto-bound `Space` as a universe
  variable:
  `error: Application type mismatch: The argument c has type Space but is expected to have type
  NavierStokes.ProblemStatement.Space` and
  `error: failed to synthesize instance of type class AddCommMonoid VelocityField`.
  Fixed by hoisting the `open`s to the outer namespace.
* `push_neg` is deprecated in this toolchain (`warning: push_neg has been deprecated. Prefer using
  push Not`).  The `by_contra` branch was rewritten with `push Not at hcon`.
* `Contracts.V1.SpaceTimeField` does not exist at that path:
  `error(lean.unknownIdentifier): Unknown identifier BlowupDensity.Contracts.V1.SpaceTimeField`.
  It lives in `BlowupDensity.Contracts.V1.Data` (`Data.lean:104`).

## Mutation check (arithmetic is load-bearing)

Copying `AffineFamily.lean` with `ballRadius r n := r * scale n / 2` (balls as wide as the centre
offsets) and running `lake env lean` on the copy fails exactly where it should:

```
../tmp/mut/AffineFamilyMut.lean:113:2: error: linarith failed to find a contradiction   -- closedBall_subset_ball
../tmp/mut/AffineFamilyMut.lean:127:2: error: linarith failed to find a contradiction   -- radius_add_lt_of_lt
```

(The other errors in that run are an artefact of renaming the namespace in the throwaway copy.)

## Hypothesis audit

Only `0 < r` and `τ₀ < τ₁`.  `AffineBasics.window` shows the canonical parameter package also
carries `0 < τ₀` and `τ₁ < 1`; neither is used, and no packet clause is used (the admissible class
depends only on the cylinder).  Both hypotheses are necessary and the probe proves it: with `r = 0`
or `τ₁ ≤ τ₀` the cylinder is empty, every admissible `b` is `0`, and no linearly independent
admissible sequence can exist.

## Gates

* `lake build NSFormalization.Section3.T24.AffineWitness` — 0 errors.
* `lake build NSFormalization.Section3.T24.AffineFamily` — 0 errors.
* `lake env lean` on both modules — no output (no warnings).
* `lake env lean ../research/T24/probes/affine_family_closes.lean` — only the intended
  `#print axioms` line.
* `lake env lean ../research/T24/axioms_ua7.lean` — 42 declarations, all
  `[propext, Classical.choice, Quot.sound]`.
