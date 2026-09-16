# Lane 199-A01-envelope — prove `ForcingFamilyBound` and `EnvelopeConversion` (the dissipative envelope), closing `FiniteMildEnergy`

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/199-A01-envelope` (git branch `erenup/199-A01-envelope`, based on `origin/erenup/integration`, which
contains lane 198's `Section4/A01/MildEnergyPremises.lean` (`mild_energy_estimate_of_cylinder`, `def ForcingFamilyBound`, `def EnvelopeConversion`,
`finiteMildEnergy_of_estimate`), lane 196's `MildGronwall.lean` (`def FiniteMildEnergy`, `mildGronwall`, word-norm comparisons), lane 193's `AprioriFamily.lean`).
Read `CLAUDE.md`, `collaboration/HANDOFF.md` §0 and §2 P7, `research/A01/REPORT_198.md`, `research/A01/REVIEW_198-A01-energy-premises.md` §3 (the
lead's lane-199 paragraph — your route, verbatim below), `research/A01/ATTEMPTS_ENERGY_PREMISES.md`, `research/A01/ATTEMPTS_MILD_GRONWALL.md`, the vendor's
`regularized_word_hasDerivAt_clamped`, `family_energy_hasDerivAt`, `metric_second_derivative_identity` (grep `vendor/NavierStokesAndEuler/Euler` — the
signed regularized energy identities that retain the exact `−ν` gradient-square pairing), `WeightedForcingTime.lean:29-49`, `RegularizedForcingWord.lean:82-94`
(what `Z` is: the norm of word(source) + transport(word state) + word(pressure)), `Section4/A03/OuterTameProduct.lean:150-185` (`outerProductTame`),
`Section4/A04/HighEnergy.lean:120-185` (`outerSobolevNormAt_le`, `inner_energy_Rhigh`), and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing
  modules; new files only. Every declaration must print exactly `[propext, Classical.choice, Quot.sound]`; non-vacuity `example` on zero data.
- **Satisfiability rule:** if one genuinely missing analytic fact remains, isolate it as ONE named hypothesis with the exact statement; never route
  through the all-order constructor; never use `ClassicalSolutionR`-level lemmas on a mild path.

## Route (reviewer 198, verbatim)
Start from `regularized_word_hasDerivAt_clamped`, apply `family_energy_hasDerivAt` with identity metric and full words, and sum
`metric_second_derivative_identity` to retain the exact `−ν` gradient-square pairing. Establish the physical/cylinder word and tensor pairing bridges,
then use `outerProductTame` → `outerSobolevNormAt_le` (with finiteness) → `inner_energy_Rhigh`, plus lane-196 norm comparisons. Independently prove a
commutator family-norm bound if preserving `ForcingFamilyBound` verbatim. Pass the signed regularized inequalities to the limit before Young absorption.
An appropriate everywhere-differentiable envelope is `x = y²`, where `y` solves the scalar comparison ODE `y' = α(t)·y + b`, `y(0) = E‖u₀‖`,
`α = A²(16·low(t))²/(4ν)`, `b = E‖forcePath‖`; prove the limiting root is `≤ y`, then choose `g = A(16·low)·y/(2ν)`, `d = 2yy'` (an algebraic witness
permitted by the target, not the physical gradient). Merely setting `x = root²` does not give everywhere differentiability from `TimeLp` regularity.

## Goal
`theorem forcingFamilyBound_of_cylinder : ForcingFamilyBound …` and `theorem envelopeConversion_of_cylinder : EnvelopeConversion …` (token-for-token the
`def`s of lane 198, with explicit constants `E, A` depending only on `q, ν`), hence `finiteMildEnergy : FiniteMildEnergy hq hν a ha F hF (E q) (A q)` and the
unconditional `mildGronwall'`, `hb_of_base''` (compose with 196/193). If only one of the two closes, deliver it and isolate the other's exact residual.

## Deliverables
1. New module `formalization/NSFormalization/Section4/A01/MildEnergyEnvelope.lean` (namespace `NSFormalization.Section4.A01`).
2. Records `research/A01/ATTEMPTS_ENVELOPE.md` (negative examples), update `research/A01/A3_SPLIT.md` A3-M2 sub-rows, conformance `research/A01/axioms_envelope.lean`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.A01.MildEnergyEnvelope` (silent), `lake env lean` on the module (0 output), the
axioms file, `make check` from the worktree root.

## Report
Commit on your branch; end with four parts (theorems with exact statements and constants / files / gaps with error text / commands). Also write it to
`research/A01/REPORT_199.md`.
