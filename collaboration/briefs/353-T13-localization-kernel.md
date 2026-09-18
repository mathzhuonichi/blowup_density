# Lane 353-T13-localization-kernel — T13 `localization`, part 1: the kernel estimates (uniform lattice-tail bound; `ITorus s (periodize f) ≤ IReal s f + tailConst · ‖f‖₂²`; inhomogeneous ≤ L² + homogeneous on T³)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/353-T13-localization-kernel` (git branch `erenup/353-T13-localization-kernel`, based on
lane 345's branch merged with lane 344's branch and `origin/erenup/integration-section3`: canonical modules `Section3/T10/*.lean`,
`Section3/T12/{MeanZeroCalculus,SpectralGap,FourierEmbeddings,TameProduct}.lean`, `Section3/T13/Localization.lean` (vocabulary),
`Section3/T13/ConstantEndpoints.lean` (lane 344: `constant_pos_finite`, `periodize_eq_of_mem_cube`, `interior_fundamentalCube`,
`tsupport_subset_cube`, `eq_zero_of_mem_cube`, …), `Section3/T13/TorusIdentity.lean` (lane 345: `torus_identity`, `periodicKernel_unfold`,
`lintegral_eq_tsum_halfOpenCube`, `fundamentalCube_ae_eq_halfOpenCube`, `exists_homogeneous_datum`, `periodicHomogeneousENorm_sq_smooth`, …)).
Read `CLAUDE.md` (hard rules), **`research/T13/RECONCILIATION.md`, `research/T13/COMPARISON.md` ("Proof dependencies" item on the
inhomogeneous estimate), `research/T13/REPORT_344.md`, `research/T13/REPORT_345.md`, `research/T13/ATTEMPTS_TORUS_IDENTITY.md`**,
`paper/sections/03-torus.tex:73-98` (the proof of `eq:localization`), and the top 40 lines of `logs/LESSONS.md` (**name every instance
explicitly**; no anonymous `local instance`).

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented.
  No edits to existing modules; new files only.
- **No named inputs, no placeholders, no goal repackaging** (hard analytic unit). Honest partial with exact residual statements and error
  text beats a stub; a `def X : Prop := <goal>` or a hypothesis equal to a target will be discarded without review.
- Before claiming a lemma is "not in the tree", `grep -rn` `Section3/T13/*.lean`, `Section3/T12/*.lean`, `Section3/T10/*.lean`.
  Before citing a paper line, `sed -n` it. Every declaration must print exactly `[propext, Classical.choice, Quot.sound]`.

## Context: the target field (NOT this lane's deliverable — lane 354 assembles it once lane 348's `wholeSpace_identity` lands)
```
localization : ∀ (s : ℝ), 0 < s → s < 1 → ∀ (c : Space) (r : ℝ), 0 < r → closure (Metric.ball c r) ⊆ interior fundamentalCube →
  ∃ C : ℝ, 0 < C ∧ ∀ f : SpatialField, (ContDiff ℝ ∞ f ∧ SupportedInBall c r f) →
    periodicSobolevENorm s (periodize f) ≤ ENNReal.ofReal C * (eLpNorm f 2 volume + dotHomogeneousENorm s f)
```
Paper route (`03-torus.tex:73-98`): `‖periodize f‖²_{H^s(T³)} ≲ ‖periodize f‖²_{L²(T³)} + ‖·‖²_{Ḣ^s(T³)}`; the `L²` part is `‖f‖₂²`
(`endpoint_zero`, lane 344); the homogeneous part is `ITorus s (periodize f) / c_s` (`torus_identity`, lane 345); on the cube
`periodize f = f` and `periodicKernel s h = |h|^{-3-2s} + latticeTail s h`, so `ITorus s (periodize f) ≤ IReal s f + (sup of the tail on the
support-difference set) · ∫∫|f(x)−f(y)|² ≤ IReal s f + 4·tailConst·‖f‖₂²`; and `IReal s f = c_s ‖f‖²_{Ḣ^s(ℝ³)}` (lane 348, whole-space).

## Goal — this lane: the three concrete estimates, each a standalone theorem
1. **Uniform tail bound.** For `0 < s`, `0 < ρ < 1` (the support-difference radius; in the application `ρ = 2r < 1` because
   `closure (ball c r) ⊆ interior fundamentalCube` forces `2r < 1` — prove that implication too, `two_r_lt_one_of_closure_ball_subset`):
   `∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ h : Space, ‖h‖ ≤ ρ → latticeTail s h ≤ C`. Route: for `n ≠ 0`, `‖h + n‖ ≥ ‖n‖ − ρ ≥ (1 − ρ)‖n‖` (since `‖n‖ ≥ 1`), so
   `latticeTail s h ≤ (1−ρ)^{-(3+2s)} ∑_{n ≠ 0} ‖n‖^{-(3+2s)}`, and `∑_{n ∈ ℤ³∖0} ‖n‖^{-(3+2s)} < ⊤` (exponent `> 3`; compare with the
   `ℓ^p` / `Summable` results for `ℤ^d` — grep Mathlib for `summable_one_div_norm_rpow` / `Real.summable_one_div_int_pow` / T12's lattice
   sums `∑ₖ (1+4π²|k|²)⁻²` in `FourierEmbeddings.lean`/`TameProduct.lean` (`linftyConst`) which already establish a convergent lattice sum —
   reuse their summability lemma with the exponent shifted). Name the constant `tailConst s ρ`.
2. **Kernel comparison on the cube.** For `0 < s < 1`, `0 < r`, `closure (ball c r) ⊆ interior fundamentalCube`, and `f` smooth with
   `SupportedInBall c r f`:
   `ITorus s (periodize f) ≤ IReal s f + 4 * tailConst s (2r) * (eLpNorm f 2 volume)^2` (in `ℝ≥0∞`; state the `‖f‖₂²` factor as
   `(eLpNorm f 2 volume) ^ 2` or `∫⁻ ‖f‖²` — pick the spelling that lane 354 can convert, and prove the conversion lemma if you pick the
   latter). Route: `periodize f = f` on `fundamentalCube` (344), `periodicKernel_unfold`/definition split `periodicKernel = fractionalRadialKernel + latticeTail`
   (the `n = 0` term separated: `tsum_eq_add_tsum_ite` or the `{n // n ≠ 0}` subtype sum — check how `latticeTail` is defined in
   `Localization.lean:66` and match it), monotonicity of `lintegral` over `cube ×ˢ cube ⊆ ℝ³ × ℝ³` for the singular part (giving `≤ IReal s f`),
   and for the tail part `‖x − y‖ ≤ 2r` whenever both `f x ≠ 0`-relevant points lie in the ball (outside the ball both `f x = f y = 0`, so the
   integrand vanishes: split the double integral by `x ∈ ball ∨ y ∈ ball`), then `‖f x − f y‖² ≤ 2‖f x‖² + 2‖f y‖²` and integrate.
3. **Inhomogeneous ≤ L² + homogeneous on T³.** For `0 ≤ s ≤ 1` (or `0 < s < 1`) and `g` smooth periodic:
   `periodicSobolevENorm s g ≤ eLpNorm g 2 periodicTorusMeasure + periodicHomogeneousENorm s (meanZeroPartT g)` — check the exact T10 norm
   spellings (`Section3/T10/PeriodicData.lean:119,181`, whether the homogeneous norm already ignores the zero mode so `meanZeroPartT` is
   unnecessary, and which `L²` spelling `endpoint_zero` (344) produces — match it). Route: coefficientwise `(1+4π²|k|²)^{s/2} ≤ 1 + (2π|k|)^s`
   for `0 ≤ s ≤ 1` (`Real.rpow_add_le_add_rpow`-type subadditivity of `t ↦ t^{s/2}`... careful: `(a+b)^{s/2} ≤ a^{s/2} + b^{s/2}` holds for
   `0 ≤ s/2 ≤ 1`), then the `ℓ²` triangle inequality on the datum side (T10 `Parseval`/datum lemmas, T12 `SpectralGap.lean`'s reweighting
   machinery `reweightDatum`, and `homogeneous_le_sobolev` for the reverse direction as a model).

## Deliverables
1. New module `formalization/NSFormalization/Section3/T13/LocalizationKernel.lean` (namespace `NSFormalization.Section3.T13`) with
   `tailConst`, `tailConst_lt_top`, `latticeTail_le_tailConst`, `two_r_lt_one_of_closure_ball_subset`, `iTorus_periodize_le`, and
   `periodicSobolevENorm_le_l2_add_homogeneous` (exact statements as above; if a hypothesis must be strengthened, say exactly why).
2. Probe `research/T13/probes/localization_kernel_closes.lean`: the three theorems instantiated on the `ContDiffBump` field of
   `research/T13/probes/constant_endpoints_closes.lean` (non-vacuity), plus an `example` sketching how lane 354 will combine them with
   `torus_identity`, `endpoint_zero`, `constant_pos_finite` and a `wholeSpace_identity`-shaped hypothesis **inside the example only**
   (an `example (hW : ∀ …) : …` is fine in a probe as a consumer check; it is NOT allowed in the module).
3. Records: `research/T13/ATTEMPTS_LOCALIZATION_KERNEL.md`, conformance `research/T13/axioms_localization_kernel.lean`, status line in
   `research/T13/COMPARISON.md`, report `research/T13/REPORT_353.md`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T13.LocalizationKernel` (0 errors), `lake env lean` on the module,
probe and axioms file; `make check` from the worktree root.

## Report
Commit on your branch; end with four parts (theorems with exact statements and constants / files / gaps with exact error text / commands and
results). Also write it to `research/T13/REPORT_353.md`.
