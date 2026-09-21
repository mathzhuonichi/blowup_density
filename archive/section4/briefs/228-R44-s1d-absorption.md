# Lane 228-R44-s1d-absorption — R44 row S1d: Young absorption under `Y ≤ θν`, producing the S1 differential inequality eq:Rcritical2 `(Y²)' + νZ² ≤ C₂νY² + C₃ν⁻¹B²` along classical solutions (the exact S1 target, one integrable `E'`)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/228-R44-s1d-absorption` (git branch `erenup/228-R44-s1d-absorption`, based on `origin/erenup/integration`, which contains all of S1a–S1c:
lane 218 `Section4/R44/JWeight.lean` (`Y`, `Z`, `B`, `JWeightDatum`, `forceJPairing`, `force_pairing_le : abs (forceJPairing h) ≤ B f * sqrt (Y u ^ 2 + Z u ^ 2)`), lane 220
`R44/TrilinearJ.lean` (`AdvectionJDatum h`, `advectionJPairing h ha`, `advection_pairing_le : abs (advectionJPairing h ha) ≤ trilinearConstJ * Y u * (Y u ^ 2 + Z u ^ 2)`), lane 222
`R44/EnergyIdentity.lean` (`jWeightDatumPath w hf t ht`, `energy_identity : HasDerivAt (fun r => Y (u r) ^ 2) (−2ν·Z(u t)² − 2·energyAdvectionJPairing h N + 2·forceJPairing h) t` for
`t ∈ Ioo 0 T`, with `N` the canonical order-`-1/2` advection datum), lane 166 `R44/Pieces.lean` (`:153-170`: the consumer shape — `∃ E' : ℝ → ℝ, IntervalIntegrable E' volume 0 S ∧ ∀ t ∈ Ioo 0 S,
HasDerivAt (Y²) (E' t) t ∧ (Y t ≤ theta·ν → E' t + ν Z t² ≤ C₂ ν Y t² + C₃ ν⁻¹ B t²)` — read it and `R44_SPLIT.md:53-64` (the clean S1 target; copy it token for token), `:73` (row S1d)).
Also read `research/R44/REPORT_222.md` §3 and `REVIEW_222-R44-s1b-energy-identity.md` (the deferred fix: the datum-uniqueness bridge `energyAdvectionJPairing h N = advectionJPairing h ha`
when `N = ha.advectionNegHalf` — **do it here**), `REPORT_220.md`, `research/R44/Spec.lean:169-230`, the paper `04-whole-space.tex:150-164` ("Thus, while `Y ≤ θν` for a sufficiently small
universal `θ > 0`, Young's inequality gives constants `C₂, C₃` with `(Y²)' + νZ² ≤ C₂νY² + C₃ν⁻¹B²`. For instance absorb the `C₀YZ²` and `BZ` terms into dissipation, use `C₀Y³ ≤ C₀θνY²`, and
bound `BY` by a multiple of `νY² + ν⁻¹B²`"), `CLAUDE.md`, `collaboration/HANDOFF.md` §0 and §2 P6, and the top 40 lines of `logs/LESSONS.md`. Lane 227 (running in parallel, worktree
`.claude/worktrees/227-R44-endpoint`, read-only) is assembling S2→S6 conditional on exactly this S1 target as a named input `RCritical2Differential`; if its
`formalization/NSFormalization/Section4/R44/Endpoint.lean` already exists when you finish, match its field names/binder shapes exactly and add the instance; otherwise state your theorem
precisely in the split's `:56-64` form so it can be instantiated by `⟨…⟩`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree (reading 227's file is allowed); never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only.
  Every declaration must print exactly `[propext, Classical.choice, Quot.sound]`; non-vacuity `example` (`A04.zeroSol`, `f = 0`).
- **Satisfiability rule:** if one fact remains open, isolate it as ONE named hypothesis with the exact statement, satisfiable by nonzero classical solutions.

## Goal (for `0 < ν`, `hf : MemForceR f`, `w : ClassicalSolutionR ν a f T`)
1. `advectionJDatumPath`: the `AdvectionJDatum (jWeightDatumPath w hf t ht)` for every slice (the advection slice is smooth `L²` with an order-`-1/2` datum — 222 built the canonical one),
   and the bridge `energyAdvectionJPairing_eq : energyAdvectionJPairing h N = advectionJPairing h ha` by datum uniqueness.
2. Universal constants `theta`, `C₂`, `C₃ : ℝ` (`def`s, `0 < theta`, `0 ≤ C₂`, `0 < C₃`, explicit in `trilinearConstJ`) and the pointwise absorption lemma: from `energy_identity`,
   `advection_pairing_le`, `force_pairing_le`, and `Y t ≤ theta·ν`: `E' t + ν Z t² ≤ C₂ ν Y t² + C₃ ν⁻¹ B t²` where `E' t` is 222's derivative value (Young: `2·C₀·Y·Z² ≤ ν/2·Z²` needs
   `2C₀θ ≤ 1/2`; `2·B·Z ≤ ν/2·Z² + 2ν⁻¹B²`; `2C₀Y³ ≤ 2C₀θ·νY²`; `2BY ≤ νY² + ν⁻¹B²`).
3. Integrability: `E'` (as a function of `t`, defined by 222's formula, extended by `0` outside `Ioo 0 S`) is `IntervalIntegrable` on `[0,S]` for `S < T` — continuity of the datum paths in
   time (222's smooth paths; `Z`, `B` continuous — for `B` use 221/222's force path continuity) suffices; for `S = T` (if the consumer needs it) say what is available.
4. `rcritical2_differential : <the exact S1 target of R44_SPLIT.md:56-64 / Pieces.lean:153-170>` and, if 227's structure exists, `instance`/`def rcritical2Differential_of_classical : RCritical2Differential w hf`.

## Deliverables
1. New module `formalization/NSFormalization/Section4/R44/Absorption.lean` (namespace `NSFormalization.Section4.R44`).
2. Records `research/R44/ATTEMPTS_S1D.md`, update `R44_SPLIT.md` rows S1d/S1 (G2 closed), conformance `research/R44/axioms_s1d.lean`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.R44.Absorption` (silent), `lake env lean` on the module (0 output), the axioms file, `make check`.

## Report
Commit on your branch; end with four parts. Also write it to `research/R44/REPORT_228.md`.
