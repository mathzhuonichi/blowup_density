# Lane 198-A01-energy-premises — build the premises of the vendor's mild energy theorem for the cylinder Navier–Stokes solution and apply it (first half of `FiniteMildEnergy`)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/198-A01-energy-premises` (git branch `erenup/198-A01-energy-premises`, based on branch
`erenup/196-A01-mild-gronwall` = `origin/erenup/integration` + lane 196's `Section4/A01/MildGronwall.lean` (with the solenoidal re-cut: `def FiniteMildEnergy hq hν a ha F hF E A`
— read its exact statement first) and lane 193's `AprioriFamily.lean`). Read `CLAUDE.md`, `collaboration/HANDOFF.md` §0 and §2 P7,
`research/A01/REPORT_196.md`, `research/A01/REVIEW_196-A01-mild-gronwall.md:203-240` (the route, verbatim below), `research/A01/ATTEMPTS_MILD_GRONWALL.md`,
`vendor/NavierStokesAndEuler/Euler/MildMajorantEnergy.lean:24-65` (`EulerMildMajorantEnergy.mild_majorized_energy_subinterval`: its premises `hu`, `hz`, `hp`
(divergence-free velocity/transport paths, gradient pressure, `:43-46`), the maximal-regularity state `U : TimeLp T (SobolevSpace 1 (q+2))` and source/pressure
representatives `F, P : TimeLp T (SobolevSpace 1 (q+1))` with approximation/truncation identities (`:47-50`), and its conclusion containing the limiting
forcing-family norm `Z` (`:54-65`)), `Section4/A01/ForcedMaximalRegularity.lean:28-42` (owner's `forced_mild_maximal_regularity`: the first Bochner state),
`Section4/A01/ForcedSourceUpgrade.lean` (`TimeLp` source), the vendor's `sourceTime_restriction` / `signedPressureTime_restriction` (grep; Euler-specific — you need
Navier–Stokes analogues), `Section4/A01/CommonHorizon.lean` (186) and `MildUniqueness.lean` (188), and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules;
  new files only. Every declaration must print exactly `[propext, Classical.choice, Quot.sound]`; non-vacuity `example` on zero data.
- **Satisfiability rule:** every named input a restriction of a standard property (one sentence each). Do not route through the all-order constructor.

## Goal (this lane = premises + application; the forcing bound and the envelope conversion are lane 199)
For an order-`q` mild solution `u` of the forced cylinder equation with solenoidal datum (`ha`) and canonical force `F := C01.forcePath hf`
(the competitor quantified in `FiniteMildEnergy`), on a subwindow `[0,T] ⊆ [0,S]`:
1. Construct the premises of `mild_majorized_energy_subinterval` specialized to the **identity metric** and the **full word family through order `q+1`**
   (external order `N = q − 5`, so `N + 6 = q + 1`; the vendor's correction-system wrapper is *not* usable — it is specific to `CorrectionData`/`SpatialBudget`):
   divergence-free velocity/transport paths (`hdiv` from 192's export / `spatialDivergence_eq_zero_of_cylinder`), a gradient pressure representative (the
   cylinder Leray complement of the residual — lane 194/197's objects at cylinder level, or the vendor's cylinder gradient projection directly), the
   maximal-regularity state `U : TimeLp T (SobolevSpace 1 (q+2))` (owner's `forced_mild_maximal_regularity`), the source/pressure representatives
   `F, P : TimeLp T (SobolevSpace 1 (q+1))` with the required approximation and truncation identities (Navier–Stokes analogues of the vendor's
   `sourceTime_restriction` / `signedPressureTime_restriction` — prove them).
2. Apply the vendor theorem and export the **integrated root-energy estimate** it yields, with the limiting forcing-family norm `Z` left explicit:
   `theorem mild_energy_estimate_of_cylinder … : <the vendor conclusion instantiated>`; then isolate what lane 199 must do as **two** named
   statements (not hypotheses of your theorem — just `def`s with docstrings): `ForcingFamilyBound` (a quantitative bound of `Z` by the tame pairing:
   `A·16·‖u|₆‖·√x·g`-shaped, via A03 `outerProductTame` → A04 `outerSobolevNormAt_le` → `inner_energy_Rhigh`) and `EnvelopeConversion` (from the
   integrated estimate to an everywhere-interior differentiable majorant `x` as `FiniteMildEnergy` demands). Prove `FiniteMildEnergy` from your
   estimate **plus** those two `def`s as explicit hypotheses (`finiteMildEnergy_of_estimate`), so lane 199 has a token-exact target.
3. If a premise cannot be built for the Navier–Stokes cylinder solution with the tree (say which, with the error), isolate it as ONE additional named
   input with the exact statement and prove the rest; record negative examples.

## Deliverables
1. New module `formalization/NSFormalization/Section4/A01/MildEnergyPremises.lean` (namespace `NSFormalization.Section4.A01`).
2. Records `research/A01/ATTEMPTS_ENERGY_PREMISES.md`, update `research/A01/A3_SPLIT.md` row A3-M2 (sub-rows: premises / forcing bound / envelope),
   conformance `research/A01/axioms_energy_premises.lean`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.A01.MildEnergyPremises` (silent), `lake env lean` on the module (0 output),
the axioms file, `make check` from the worktree root.

## Report
Commit on your branch; end with four parts (theorems with exact statements and named inputs / files / gaps with error text / commands). Also write it
to `research/A01/REPORT_198.md`.
