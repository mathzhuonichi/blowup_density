# Lane 452-T20-U5-transport-commutes-lambda — T20 U5: `constantTransportCommutesLambda` verbatim (constant transport commutes with the Fourier multiplier Λ)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/452-T20-U5-transport-commutes-lambda` (git branch `erenup/452-T20-U5-transport-commutes-lambda`, = lane 441's branch + `origin/erenup/integration-section3`:
all T20 modules `Section3/T20/{CriticalRegularity,MeanReduction,BIntegral,ConstantTransport,CriticalTrilinear,CriticalEnergy,YBound,H1Trilinear,H1Energy,Continuation,GlobalRegularity}.lean`). U5 is the
**only** field of `CriticalRegularityTAPI` without a proof: no earlier unit needed it (U8/U10b ran on the Fourier side). Read `CLAUDE.md`, **`research/T20/T20_SPLIT.md` §0 and unit U5**, the canonical
field `constantTransportCommutesLambda` (`Section3/T20/CriticalRegularity.lean:268-282` — read its exact text: which fields `v`, `Lv`, the constant vector `m`, which premises `SmoothPeriodicT`/`IsPeriodicLambda`,
and what "commutes" means there: `IsPeriodicLambda (fun x ↦ (m·∇)v x) (fun x ↦ (m·∇)Lv x)` or an equality of fields — copy verbatim), `paper/sections/03-torus.tex:407-411` (constant transport commutes
with Fourier multipliers and is skew-adjoint), lane 390's `Section3/T20/ConstantTransport.lean` (U4 `constantTransportSkew` — the same operator, its spelling and helper lemmas), lane 415's
`Section3/T20/CriticalEnergy.lean` (`periodicFourierCoeff_fderiv_dir`: the Fourier coefficient of the directional derivative `∂_m v` is `2πi (m·k)` times the coefficient — the constant-transport symbol),
`Section3/T12/FourierEmbeddings.lean` (`IsPeriodicLambda :289`, `lambdaField_component`, `lambdaCoeff :225`, `lambda_exists`), lane 405's `Section3/T12/GradientLambdaL3.lean` (`cxReweight`, `derivShift`,
`contDiff_dirDeriv`, `isMeanZeroT_dirDeriv` — the complex multiplier machinery), and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed. `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`. Build the closure first.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only.
- **No named inputs, no placeholders, no goal repackaging.** An honest partial with the exact residual statement and error text beats a stub.
- Every declaration prints exactly `[propext, Classical.choice, Quot.sound]`. `grep -rn` before claiming "not in the tree"; `sed -n` before citing a line.

## Goal
New module `formalization/NSFormalization/Section3/T20/TransportLambda.lean` (namespace `NSFormalization.Section3.T20`): `theorem constantTransportCommutesLambda` whose type is literally the canonical field
(probe `example : constantTransportCommutesLambdaFieldType := constantTransportCommutesLambda` in the style of lanes 415/428). Route (Fourier side): if `IsPeriodicLambda v Lv` pins `Lv`'s coefficients as
`2π|k|·v̂(k)` (`lambdaCoeff`), then the transport `(m·∇)v` has coefficients `2πi(m·k)·v̂(k)` (`periodicFourierCoeff_fderiv_dir`), and both operators are diagonal Fourier multipliers, so `Λ((m·∇)v)` and
`(m·∇)(Λv)` have the same coefficients `2πi(m·k)·2π|k|·v̂(k)`; conclude through the coefficient characterisation of `IsPeriodicLambda` (uniqueness of a smooth periodic field with given coefficients —
`T10.datum_unique`/Fourier injectivity on smooth periodic fields; grep `periodicFourierCoeff_injective`/`eq_of_periodicFourierCoeff_eq`) and smoothness/periodicity/mean-zero of `(m·∇)v`, `(m·∇)Lv`
(`contDiff_dirDeriv`, `isPeriodicSpatial_dirDeriv`, `isMeanZeroT_dirDeriv`; `Lv` is smooth periodic mean-zero by `IsPeriodicLambda`'s conjuncts). Deliverables: the module,
`research/T20/probes/transport_lambda_closes.lean` (field-type match + non-vacuity on `meanZeroPartT (x ↦ cos(2π x₀)·e₀)` with `Lv` from `lambda_exists`), `research/T20/axioms_u5.lean`,
`research/T20/ATTEMPTS_U5.md`, U5 status line in `T20_SPLIT.md`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T20.TransportLambda` (0 errors), `lake env lean` on the module (0 output), the probe, the axioms file, `make check`.

## Report
Commit on your branch; end with four parts (theorem with exact statement / files / gaps with error text / commands and results). Also write it to `research/T20/REPORT_452.md`.
