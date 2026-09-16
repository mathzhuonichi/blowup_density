# Lane 177-C01-v4-contract — register the enstrophy identity as C01 V4 (28th contract)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) contract-registration worker on the repository checked out at your
working directory `/data_8T/ping/blowup_density/.claude/worktrees/177-C01-v4-contract` (git branch
`erenup/177-C01-v4-contract`, based on `origin/erenup/integration`, which contains lanes 163/170's
`Section4/C01/Enstrophy.lean` and `EnstrophyIdentity.lean`). Read `CLAUDE.md` (contract import rules, the
`ClassicalSolutionR` structure exception, `Tests` warningAsError, `ensure_ascii=False`),
`collaboration/HANDOFF.md` §0, the top 40 lines of `logs/LESSONS.md`, then the V3 trio as the template:
`verification/Contracts/V3/EnergyAbsorptionPartial.lean`, `verification/Bindings/EnergyAbsorptionPartialV3.lean`,
`verification/Tests/EnergyAbsorptionPartialV3.lean`, the registry entry `C01.energy_absorption_partial_v3`
in `verification/contracts.json`, and the reviews `research/C01/REVIEW_V3_CONTRACT.md`,
`research/C01/REVIEW_170-C01-e6-e7-enstrophy-identity.md` (which confirms the exact E6 contract shape compiles).

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/placeholder `Prop` fields. Do not modify `Contracts/V1`, `V2`, `V3` or existing
  `Tests/*`. `Contracts/*` import only `Mathlib`/`Contracts.*` (+ the whitelist in `experiments/check_contracts.py`);
  restated definitions need `rfl` bridges in `Bindings/`.

## Deliverables
1. `verification/Contracts/V4/EnergyAbsorptionPartial.lean` (check `experiments/check_contracts.py` accepts a
   `/V4/` path — lane 120 registered a V3; if the path rule needs a one-line extension, do NOT change the
   checker: report it and fall back to `Contracts/V3/EnergyAbsorptionPartialV4.lean`? No — the versioned
   directory is the convention; read the checker first and follow what it enforces). Structure
   `EnergyAbsorptionPartialV4API extends EnergyAbsorptionPartialV3API` adding, **token-for-token from
   `research/C01/Spec.lean`**: the spec-local defs it needs (`advectionWork`, `laplacianSq`, `lap`/gradient
   objects — check what V1–V3 already restate and inherit them) and the field `enstrophyIdentity`
   (`Spec.lean:487`, eq:RH1's derivation `04-whole-space.tex:105-113`). Do NOT add `h2TimeIntegral`
   (lane 170 only proved the strict-interior version; record that as excluded in the scope).
2. `verification/Bindings/EnergyAbsorptionPartialV4.lean`: `{ energyAbsorptionPartialV3 with enstrophyIdentity := … }`
   via `uniqueness_toA02`, from `C01.enstrophyIdentity_gradientSq` (`Section4/C01/EnstrophyIdentity.lean`);
   `rfl` bridges for the restated defs, or the single non-`rfl` bridge if `laplacianSq`/`advectionWork` need
   a `PiLp`-type identity like V2's `gradientSq` did (say which); `energyAbsorptionPartialV3_of_v4 := rfl`.
3. `verification/Tests/EnergyAbsorptionPartialV4.lean` (`checkedEnergyAbsorptionPartialV4`,
   `run_cmd TestSupport.checkAxioms`, a conformance `example` restating the field against `Spec.lean`).
4. Registry entry `C01.energy_absorption_partial_v4` (`version: 4`, `parent_task: C01`, honest scope listing
   what is included and that `h2TimeIntegral`/`enstrophyIntegralBound`/`sobolevTwoFourier` remain excluded),
   written with `ensure_ascii=False, indent=2`, additions only; `work_items.json` + `python3 experiments/tasks.py render`.
5. Records `research/C01/ATTEMPTS_V4_CONTRACT.md`, conformance `research/C01/axioms_v4_contract.lean`; update
   `ENERGY_SPLIT.md` (enstrophyIdentity: registered V4).

## Gates (paste outputs)
`scripts/gates.sh` from the worktree root (`make check`, `make test`, `make test-mutations`);
`python3 experiments/check_contracts.py --base-ref origin/erenup/integration` (exit 0, `registered_contracts: 28`,
`base_compatibility_checked: true`); the axioms file (exactly `[propext, Classical.choice, Quot.sound]`);
`git diff --stat verification/contracts.json` (additions only).

## Report
Commit on your branch; end with four parts (fields registered with exact statements / files / gaps / commands).
Also write it to `research/C01/REPORT_177.md`.
