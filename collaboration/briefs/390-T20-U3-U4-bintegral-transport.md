# Lane 390-T20-U3-U4-bintegral-transport — T20 wave 1 (Opus units): U3 `bIntegral` (eq:bintegral) and U4 `constantTransportSkew` (:411) of `research/T20/T20_SPLIT.md`

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/390-T20-U3-U4-bintegral-transport` (git branch `erenup/390-T20-U3-U4-bintegral-transport`, based on `origin/erenup/integration-section3`
merged with lane 381's branch `erenup/381-T20-canonical` (the canonical `Section3/T20/CriticalRegularity.lean` with `CriticalRegularityTAPI` and its field spellings; in review)).
Read `CLAUDE.md`, **`research/T20/T20_SPLIT.md` §0 and units U3, U4 (targets verbatim, inputs with file:line, routes)**, `research/T20/Spec.lean`, `research/T20/probes/api_on_canonical.lean`,
the whole-space mirror `Section4/R43/ForcePath.lean` (`forceHomogeneousENorm_le_forceSobolevENormL1`), the T10 datum layer (`Section3/T10/{PeriodicData,DatumBasics,Parseval,ForcePaths}.lean`:
`meanZeroPartT`, the inhomogeneous `H^{1/2}` datum path, `torusLift`, `periodicTorusMeasure`), T11's `MeanIdentity.lean`/`GalileanClasses.lean` (constant transport `(m·∇)`), and the top
40 lines of `logs/LESSONS.md` (**name every instance explicitly**).

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only.
- **No named inputs, no placeholders, no goal repackaging.** An honest partial with the exact residual statement and error text beats a stub.
- Every declaration must print exactly `[propext, Classical.choice, Quot.sound]`.

## Goal
1. `Section3/T20/BIntegral.lean`: `bIntegral` verbatim — `criticalBIntegral (meanFreeForce g) ≤ criticalRho g` for `g ∈ forceClassT` (`eq:bintegral`, `03-torus.tex:442-444`): removing the
   zero mode is contractive on the inhomogeneous `H^{1/2}` datum path (`k = 0` weight `1`), with a strongly measurable centred datum witness ⇒ `∫₀^∞ ‖h(t)‖_{Ḣ^{1/2}} ≤ ∫₀^∞ ‖g(t)‖_{H^{1/2}} = ρ`;
   mirror R43's `forceHomogeneousENorm_le_forceSobolevENormL1` on the torus datum.
2. `Section3/T20/ConstantTransport.lean`: `constantTransportSkew` verbatim — for smooth periodic `v, w`, `⟪(m·∇)v, w⟫_{L²(T³)} = −⟪v, (m·∇)w⟫`: periodic integration by parts on the
   probability torus (constant-coefficient first-order transport with `div m = 0` is skew on `L²(T³)`); the two `Integrable` premises the field carries follow from `torusLift` boundedness.

## Deliverables
1. The two modules (namespace `NSFormalization.Section3.T20`); 2. probe `research/T20/probes/bintegral_transport_closes.lean` (the canonical fields closed by `exact`; non-vacuity on a
nonzero smooth periodic mode); 3. `research/T20/ATTEMPTS_U3_U4.md`, `research/T20/axioms_u3_u4.lean`, status in `research/T20/T20_SPLIT.md`, report `research/T20/REPORT_390.md` (if a
guard blocks the write, put the full report in your final message).

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T20.BIntegral NSFormalization.Section3.T20.ConstantTransport` (0 errors), `lake env lean` on modules / probe /
axioms file; `make check`.

## Report
Commit on your branch; end with four parts (theorems with exact statements / files / gaps with exact error text / commands and results).
