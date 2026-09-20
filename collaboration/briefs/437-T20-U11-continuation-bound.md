# Lane 437-T20-U11-continuation-bound — T20 U11: `continuationBound` verbatim (orthogonal mode decomposition + the `H²` time-integral budget)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/437-T20-U11-continuation-bound` (git branch `erenup/437-T20-U11-continuation-bound`, = lane 432's branch + `origin/erenup/integration-section3`:
`Section3/T20/{CriticalRegularity,MeanReduction,BIntegral,ConstantTransport,CriticalTrilinear,CriticalEnergy,YBound,H1Trilinear,H1Energy}.lean` — lane 432's `hOneEnergy` (at `criticalSmallnessH1`,
`CH1 = 2`) with its reusable pieces (`periodicLpENorm_two_laplacian_eq_homogeneous` — the order-2 Parseval, `gradientSqT_meanFreeVelocity_eq_tsum`, `laplacianSqT_meanFreeVelocity_eq_tsum`,
`hasDerivAt_tsum_h1FreqEnergy`), lane 428's `YBound.lean` (`yBound_of_le`, `criticalForcePrimitiveT`, `criticalY_ne_top`), lane 389's mean-reduction fields (U2: `meanBound` `∫|m|² ≤ Sρ²`-type — read
`MeanReduction.lean` and the U2 field name in the canonical structure), and the T11/T12 modules (`hTwo_le_laplacian` `FourierEmbeddings.lean:165`, `hTwoConst`)). Read `CLAUDE.md`,
**`research/T20/T20_SPLIT.md` §0 and unit U11** (`:247-255`), the canonical field `continuationBound` and the definitions `squaredHTwoIntegralT`, `meanModeCriterionIntegral`, `Ccriterion` in
`Section3/T20/CriticalRegularity.lean` (grep; read exactly what the three conjuncts say: the identity `squaredHTwoIntegralT S w.velocity = meanModeCriterionIntegral S g w.velocity`, the bound
`≤ S·ρ² + Ccriterion·ν⁻²·∫₀^∞ ‖h‖²₂`, and `≠ ⊤`), `paper/sections/03-torus.tex:485-500` (`eq:H2budget`/the continuation criterion), `research/T20/REPORT_{389,428,432}.md`, the R³ analogue
`Section4/R44/Endpoint.lean` (`maximal_h2TimeIntegral`, S4 budget transport), and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed. `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only.
- **No named inputs, no placeholders, no goal repackaging.** An honest partial with the exact residual statement and error text beats a stub.
- Every declaration prints exactly `[propext, Classical.choice, Quot.sound]`. `grep -rn` before claiming "not in the tree"; `sed -n` before citing a line.

## Goal
New module `formalization/NSFormalization/Section3/T20/Continuation.lean` (namespace `NSFormalization.Section3.T20`): `def Ccriterion : ℝ` (explicit, positive) and `theorem continuationBound` whose type is
literally the canonical field at `c := criticalSmallnessH1` (432) and this `Ccriterion` (probe: `example : continuationBoundFieldType criticalSmallnessH1 Ccriterion := continuationBound` mirroring
lanes 415/428/432). Route: (i) the orthogonal constant/mean-zero decomposition on the torus, `‖u(t)‖²_{H²} = |m(t)|² + ‖v(t)‖²_{H²}` (the `k = 0` weight is `1`; `u = m + v` with `v = meanFreeVelocity`,
`m = meanT u` — prove it from the datum/coefficient description, `meanZeroPartT`, the `k=0` coefficient = mean, and the `H²` weight); integrate in time to get the identity conjunct (`squaredHTwoIntegralT S u
= ∫₀ˢ |m|² + ∫₀ˢ ‖v‖²_{H²}` — match `meanModeCriterionIntegral`'s exact definition); (ii) `‖v(t)‖²_{H²} ≤ hTwoConst²·‖Δv(t)‖²₂` (`hTwo_le_laplacian`), and integrating U10b's inequality
`E' + ν‖Δv‖²₂ ≤ CH1·ν⁻¹‖h‖²₂` over `(0, S)` with `‖∇v(0)‖₂ = 0` (zero initial datum) gives `ν∫₀ˢ‖Δv‖²₂ ≤ CH1·ν⁻¹∫₀^∞‖h‖²₂` (FTC for the derivative witness — an `intervalIntegral`/`integral_eq_sub_of_hasDerivAt`
argument with the `E'` from U10b as a function of `s`; handle measurability/integrability via the smooth solution's continuity), hence `∫₀ˢ‖v‖²_{H²} ≤ hTwoConst²·CH1·ν⁻²·∫₀^∞‖h‖²₂`; (iii) `∫₀ˢ|m|² ≤ S·ρ²` from U2
(`meanBound`, `|m(t)| ≤ ρ`); (iv) `∫₀^∞ ‖h‖²₂ < ∞` from `g ∈ forceClassT` (compact time support + continuity; `MemForceT`), so the bound is `≠ ⊤`. Set `Ccriterion := hTwoConst² · CH1` (or what you get).
Deliverables: the module, `research/T20/probes/continuation_closes.lean` (field-type match; non-vacuity at the zero-force zero-solution instance with the satisfiable smallness hypothesis, as 428/432),
`research/T20/axioms_u11.lean`, `research/T20/ATTEMPTS_U11.md`, U11 status line in `T20_SPLIT.md`, one `logs/LESSONS.md` line if pin-specific.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T20.Continuation` (0 errors), `lake env lean` on the module (0 output), the probe, the axioms file, `make check`.

## Report
Commit on your branch; end with four parts (theorem with exact statement and constant / files / gaps with error text / commands and results). Try `research/T20/REPORT_437.md`; if the report-file guard
blocks it, put the full report in your final message.
