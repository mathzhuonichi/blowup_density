# Lane 504 — P21 Route B, B1

Status: **B1 analytic estimate closed, conditional only on explicit B0 norm
bridges. P6 / L21_H1 remains Partial.** No critical smallness, new axiom, admitted
proof, or assumed differential/nonlinear inequality is used.

## 1. Statements

`Section4/A04/EnstrophyInequality.lean` proves 16 named lemmas.

- `inhomogeneousEnergyIdentity` adds the proved ordinary L² identity to
  `C01.enstrophyIdentity_gradientSq`. The latter gives exactly
  `(gradientSq u)' = 2 advectionWork u - 2ν laplacianSq u - 2 pairing f (lap u)`;
  it does not itself differentiate the registered inhomogeneous H¹ norm.
  `weightedEnergyIdentity` also proves the sum with any fixed gradient weight κ.
- `lintegral_convection_holder_632`, `eLpNorm_three_interpolation`, and
  `velocity_six_le_gradient_two` prove the L⁶·L³·L² Hölder step, the half-power
  interpolation, and support-free velocity Sobolev estimate. Combined with A05's
  proved gradient L⁶ estimate, `convection_interpolation` gives
  `ofReal |advectionWork z| ≤ (ofReal C₀)^(3/2) G^(3/2) L^(3/2)` for smooth
  L² jets, where G=‖∇z‖₂, L=‖Δz‖₂, C₀=A05.gradientL6Const.
  `convection_sobolev` gives the requested H¹/H² bound from the two explicitly
  stated norm bridges, with constant
  `C₀^(3/2) (2π)^(3/2) ((2π)^2)^(3/2)`.
- `young_quartic`, `young_three_quarters`, `young_two_factors`, and
  `weighted_cubic_assembly` prove absorption, including all ordinary energy and
  low-frequency terms. Cauchy–Schwarz for both force pairings is supplied by
  `abs_pairing_carrier_le`, not assumed in the classical theorem.
- `enstrophy_differential` and `enstrophy_differential_on_Icc` prove, with
  `Y=(sobolevENorm 1 u).toReal²`, `Z=(sobolevENorm 2 u).toReal²`,
  `Y' + νZ ≤ Cν(1+Y)³ + Cν l2Sq(f)` on every closed interval strictly inside
  `(0,T)`. The coefficient c is 1. With κ=(2π)⁻²,
  `Cν=(2κ C₀^(3/2))⁴/(κν/2)³/κ³ + (1+ν) + (1+2κ/ν)`.
  Constants depend only on ν and fixed dimension/norm conventions.

The classical theorem uses A02's canonical restatement of `ClassicalSolutionR`
and `MemForceR`. Admissible initial-class membership is unnecessary for this
estimate once the classical solution is supplied, so the theorem is stronger in
that argument. Physical l2Sq(f) is exactly the squared L² force norm.

## 2. Files

- New proof module `formalization/NSFormalization/Section4/A04/EnstrophyInequality.lean`.
- `research/P21/probes/b1_closes.lean`: probes every named step and instantiates
  both Young APIs; `research/P21/axioms_b1.lean`: prints and checks all 16 axiom sets.
- `research/P21/ATTEMPTS_B1.md`: proof attempts, fixed compilation errors, scope.
- `research/P21/P6_SPLIT.md`: exact B0 interface and B1 handoff.
- `formalization/blueprint/entrypoints.json`: new module in proof_modules.
- `formalization/blueprint/AXIOM_AUDIT.json`: refreshed source hash after the
  required article audit. The article target list and coverage stay unchanged.

No B0 module, contract, binding, test registry entry, or article Closed marker
was created. The common full-contract closure procedure is not applicable to
this internal B1 unit while P6 is still Partial.

## 3. Remaining bridges and limits

The final theorem has exactly these B0 hypotheses, with z the current velocity
slice and κ=(2π)⁻²:

```lean
-- For all interior times (equality on a neighborhood transfers the derivative):
(D01.sobolevENorm 1 z).toReal ^ 2 = l2Sq z + κ * gradientSq z
-- At the current time / each time in the chosen compact interval:
(D01.sobolevENorm 2 z).toReal ^ 2 ≤
  l2Sq z + 2 * κ * gradientSq z + κ ^ 2 * laplacianSq z
eLpNorm (A05.gradTensor z) 2 volume ≤ ENNReal.ofReal (Real.sqrt (gradientSq z))
```

The physical Laplacian norm identity is already discharged using C01/I02.
The separate `convection_sobolev` consumes the two bounds stated in its signature:
G≤2π H¹ and L≤(2π)² H². No unproved analytic inequality is hidden in a structure
or a named input. Norm bridge proofs are intentionally delegated to lane 503 by
the lane brief, not replaced with new modules here.

There is no remaining Lean error in steps 1–3. Representative transient error:
`don't know how to synthesize placeholder for argument f'` in HasDerivAt assembly;
fixed by spelling out the already-proved derivative value. The earlier rpow
attempt generated `‖g x‖ₑ ≠ 0` and `‖g x‖ₑ ≠ ∞` goals; replaced by the correct
nonnegative-exponent identity. These are resolved errors, not residual claims.

The ODE barrier, δ-before-datum/restart quantifiers, endpoint monotone limit,
and maximality contradiction remain B3–B5 work. This module proves neither an
initial-time derivative nor finite dissipation at the maximal endpoint. The
revised proposition has no displayed H¹-uniform clause; this work serves the
separate blueprint obligation.

## 4. Commands and results

All Lean commands used `. scripts/lean-env.sh`, the verification Lake environment,
and `LEAN_NUM_THREADS=6`.

- Built C01.EnstrophyIdentityRaw (10324 jobs) and the new module (10325 jobs): passed.
- Direct `lake env lean` probes and axiom checks: passed. All 16 declarations print
  exactly `[propext, Classical.choice, Quot.sound]`; TestSupport checks also pass.
- `python3 experiments/audit_article_axioms.py --build --output-dir tmp/article-audit --workers 2`:
  passed, 56 declarations / 27 article entries / zero forbidden-axiom results.
  Reviewed and copied report.json to AXIOM_AUDIT.json.
- `python3 experiments/check_formalization_plan.py`: passed; regenerated graph unchanged.
- `make check`: passed, 29 registered contracts and 11 contract-policy tests.
- `make test`: passed (11000 build/test jobs, registered contract axiom checks).
- `make test-mutations`: passed; implementation refactor accepted and admitted
  proof, extra axiom, and weakened hypothesis rejected for the expected reasons.
- `make paper`: passed; both PDF logs clean and reader-document checks passed.
- `git diff --check`: passed. Logs are under ignored `tmp/b1-*.log`; article
  per-environment logs and report are under `tmp/article-audit/`.

Closed steps were committed separately. No push, merge, rebase, or external
message was performed. The pre-existing untracked lane brief was left untouched.
