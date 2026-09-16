# Lane 222-R44-s1b-energy-identity — R44 row S1b: differentiate `Y² = ‖u(t)‖²_{H^{1/2}}` along a classical solution, identify `(Y²)' = 2⟪∂ₜu, Ju⟫`, kill the pressure by solenoidality, and evaluate the dissipation `⟪νΔu, Ju⟫ = −ν Z²`

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/222-R44-s1b-energy-identity` (git branch `erenup/222-R44-s1b-energy-identity`, based on `origin/erenup/integration`, which contains lane 218's
`Section4/R44/JWeight.lean` (`Jmul`, `JWeightDatum`, `Y`, `Z`, `B`, `forceJPairing`, `weight_identity`, `force_pairing_le`), lane 215's `Section4/A04/RestartFixedForce.lean`
(`classical_hasSmoothSobolevPath`: every integer-order datum path of an arbitrary classical solution is `C^∞` in time on `Ico 0 T`; the local-carrier covering pattern `:146-186`),
A04's `DerivNorm.lean` (`hasDerivAt_datumNormSq_of_contDiffOn`: `(‖G t‖²)' = 2⟪G t, deriv G t⟫`), A04's `momentum_datum` (grep `Section4/A04` — the order-two datum-level derivative identity
`deriv G₂ t = datum of (νΔu − (u·∇)u − ∇p + f)`; lane 219's report says it is the exact identity, used with D01's pressure-gradient jets), D01's `lowerVectorL s r` (`HalfOrder.lean:79-110`,
continuous linear order lowering — commutes with `deriv`), D01's `LerayDatum.lean` (order-`s` Leray projector/complement on `RealVectorSobolev s`; divergence-free ⇔ complement `= 0`;
gradient fields are in the complement), lane 216's `Section4/R43/CriticalDatumPath.lean` (`criticalVelocity_transverse`, `criticalPressure_longitudinal`, `criticalLaplacian_symbol` — the
homogeneous-scale versions of exactly the three facts this lane needs in the inhomogeneous scale; copy their proofs' structure), lane 219's branch `erenup/219-R43-critical-momentum`
`Section4/R43/CriticalMomentum.lean` (**read-only reference, not on your base**: how it transported `momentum_datum` through `lowerVectorL` — `git show erenup/219-R43-critical-momentum:formalization/NSFormalization/Section4/R43/CriticalMomentum.lean`),
`research/R44/R44_SPLIT.md:53-81` (row S1b; the clean PDE-level target of S1 at `:56-64`), `research/R44/Spec.lean`, `research/R44/REPORT_218.md`, the paper `04-whole-space.tex:145-158`
("Testing the equation against `Ju` yields an energy identity with dissipation `νZ²`"), `CLAUDE.md`, `collaboration/HANDOFF.md` §0 and §2 P6, and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only.
  Every declaration must print exactly `[propext, Classical.choice, Quot.sound]`; non-vacuity `example` (`A04.zeroSol`, `f = 0`).
- **Satisfiability rule:** if one fact remains open, isolate it as ONE named hypothesis with the exact statement, satisfiable by nonzero classical solutions; consumers copy your binders.

## Goal
For `0 < ν`, `hf : MemForceR f`, `w : ClassicalSolutionR ν a f T`:
1. `def jWeightDatumPath w hf : ℝ → JWeightDatum (u(t,·)) (f(t,·))` (or the existence version): the canonical order-`1/2`, `3/2`, gradient, and `H^{-1/2}` force data of each slice, obtained by
   lowering the smooth integer-order paths of 215 (`lowerVectorL 2 (1/2)`, `lowerVectorL 2 (3/2)`, force from `MemForceR`'s order-6 path lowered to `-1/2`), with `ContDiffOn ℝ ∞` in time of the
   velocity path on `Ico 0 T` (CLM ∘ smooth), and `Y w t = Y (u(t,·))`, `Z w t`, `B f t` as real functions of time (218's spellings).
2. `hasDerivAt_Y_sq : ∀ t ∈ Ioo 0 T, HasDerivAt (fun s => Y s ^ 2) (2 * ⟪G t, deriv G t⟫) t` (DerivNorm) and the identification `⟪G t, deriv G t⟫_{H^{1/2}} = ⟪∂ₜu, Ju⟫` — i.e. the
   `H^{1/2}` inner product of the datum with the lowered momentum datum equals 218's real pairing of the momentum datum with `Jmul` of the velocity datum (this is the definition of the
   `H^{1/2}` inner product on the stored carrier; prove it as a lemma `inner_eq_jPairing`).
3. Momentum at order `1/2`: `deriv G t = lowerVectorL … (ν • L t − A t − P t + F t)` from `momentum_datum` (order two) pushed through `lowerVectorL` (CLM commutes with `deriv`, additive).
4. Three evaluations at datum level, all for `t ∈ Ioo 0 T`:
   - dissipation: `⟪νΔu, Ju⟫ = −ν · Z t ^ 2` (symbol `−|ξ|²` under the `(1+|ξ|²)^{1/2}` weight: `∫ (1+|ξ|²)^{1/2} |ξ|² |û|² = Z²` by 218's `Z_sq_eq_sum_norm` and the gradient symbol);
   - pressure: `⟪∇p, Ju⟫ = 0` (the gradient datum is in the Leray complement, `Ju` is divergence-free — `LerayDatum`; homogeneous twin: 216's two lemmas);
   - hence `energy_identity : ∀ t ∈ Ioo 0 T, HasDerivAt (fun s => Y s ^ 2) (−2 ν (Z t)^2 − 2 ⟪(u·∇)u, Ju⟫ + 2 forceJPairing) t` with the advection pairing spelled exactly as lane 220's
     `AdvectionJDatum`/`advectionJPairing` (branch `erenup/220-R44-s1c-trilinear`, read-only via `git show`; if 220 has not fixed a name yet, define `advectionJPairing` here in the
     obvious way — the real pairing of the advection datum with `Jmul` of the velocity datum — and note it so 220/S1d can align).
5. Sanity: at `A04.zeroSol` all terms vanish.

## Deliverables
1. New module `formalization/NSFormalization/Section4/R44/EnergyIdentity.lean` (namespace `NSFormalization.Section4.R44`).
2. Records `research/R44/ATTEMPTS_S1B.md`, update `R44_SPLIT.md` row S1b (and G2 status), conformance `research/R44/axioms_s1b.lean`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.R44.EnergyIdentity` (silent), `lake env lean` on the module (0 output), the axioms file, `make check`.

## Report
Commit on your branch; end with four parts. Also write it to `research/R44/REPORT_222.md`.
