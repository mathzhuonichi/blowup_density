# Lane 250-I03-homogeneous-scaling — the two absent I03 fields: homogeneous negative-order bounds `‖F_ε‖_{L^q_tḢ^s} ≤ C ε^β` for the rescaled packet force and for the correction force (the `L²_tḢ⁻¹_x` term of Prop. 4.6 / Thm 4.7)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/250-I03-homogeneous-scaling` (git branch `erenup/250-I03-homogeneous-scaling`, based on `origin/erenup/integration`). Read `CLAUDE.md`,
`collaboration/HANDOFF.md` §0, the top 40 lines of `logs/LESSONS.md`, then the target: `research/I03/Spec.lean` fields `packetNegativeHomogeneous` and `correctionNegativeHomogeneous` (copy their
statements token for token; read the whole `ScalingAPI` draft and its docstrings), `research/I03/COMPARISON.md` rows 46-48 (the gap: "the homogeneous norm is only ever used on the profile";
the inhomogeneous halves are **present**: `Source/TimeNormScaling.lean:133` `TimeNormScaling.force_eLpNorm_negative_epsilon` (packet) and `Paper1/CorrectionVectorNorms.lean`
`vectorPhysicalForce_uniform_negative_time` (correction) — read both statements and proofs: the scaling computation is the same, only the Fourier weight changes from `(1+|ξ|²)^{s/2}` to `|ξ|^s`),
`research/I03/ATTEMPTS.md`, the paper `04-whole-space.tex:64-80` (eq:RnegativeScale and the homogeneous variant, the exponent `β`) and `:264-275` (its use at `q = 2`, `s = −1` in Prop. 4.6),
the registered vocabulary `verification/Contracts/V1/Data.lean:375-410` (`IsHomogeneousPath`, `IsHomogeneousDatum` `ĥ = |ξ|^{-s} G`, `forceHomogeneousENorm`; note `:404-409` "must not be used on a
general H^∞ slice" — the norm is an infimum over datum paths, so the bound is proved by exhibiting a path), `Contracts/V1/Scaling.lean` (registered `ScalingAPI` fields — which of the two
are registered already? grep), `Bindings/ScalingNorms.lean` (`cycles_packet_negative`, `cycles_packet_mono` — the inhomogeneous binding route), D01's homogeneous data machinery
(`Section4/D01/HomogeneousWitness.lean`, `HomogeneousNorm.lean`, lane 216's `R43/CriticalDatumPath.lean` `ofSobolevVector` — the Bessel-to-homogeneous conversion is contractive only for
`s ≥ 0`; for `s = −1` the homogeneous norm is **larger**, so a genuine Fourier scaling computation is needed), `Source/FourierScaling.lean`, `Source/TimeNormScaling.lean:65-68`
(`fourierSobolevNorm`, `homogeneousFourierNorm`), `Paper3/HomogeneousTime.lean`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only.
  Every declaration must print exactly `[propext, Classical.choice, Quot.sound]`; non-vacuity `example`s (the zero force; and the actual packet if a witness is cheap).
- **Satisfiability rule:** if one analytic fact remains open (e.g. the homogeneous Fourier scaling identity for the parabolic rescaling), isolate it as ONE named hypothesis with the exact statement.

## Goal
1. Homogeneous parabolic scaling identity: for a compactly supported smooth force `F` and the rescaling used by `TimeNormScaling`/`Scaling` (`F_ε(t,x) = ε^{a} F(ε^{-2} t, ε^{-1}(x − x₀))` —
   read the exact convention), `‖F_ε(t)‖_{Ḣ^s} = ε^{c(s)} ‖F(ε^{-2}t)‖_{Ḣ^s}` at datum level (`|ξ|^s` weight; Fourier dilation), hence `‖F_ε‖_{L^q_tḢ^s} = ε^{β(q,s)} ‖F‖_{L^q_tḢ^s}` with the paper's
   `β` (`:70-76`); state it for the registered `forceHomogeneousENorm q s` by exhibiting the rescaled datum path (`IsHomogeneousPath`).
2. `packetNegativeHomogeneous` and `correctionNegativeHomogeneous` in the I03 spec's exact shapes (constants explicit; the profile's finite homogeneous norm as the constant — check
   `research/I03/COMPARISON.md` for where the profile's `Ḣ^s` finiteness lives).
3. Non-vacuity examples; audit `research/I03/axioms_homogeneous_scaling.lean`; records `research/I03/ATTEMPTS_HOMOGENEOUS.md`; update `research/I03/COMPARISON.md` rows 46/48.

## Deliverables
New module `formalization/NSFormalization/Section4/I03/HomogeneousScaling.lean` (create the directory; namespace `NSFormalization.Section4.I03`) — or `verification/Bindings/ScalingHomogeneous.lean`
if the statement must use `Contracts` vocabulary directly (say why).

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build <module>` (silent), `lake env lean` on the module (0 output), the audit, `make check`.

## Report
Commit on your branch; end with four parts. Also write it to `research/I03/REPORT_250.md`.
