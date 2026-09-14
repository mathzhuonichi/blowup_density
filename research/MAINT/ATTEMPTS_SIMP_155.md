# ATTEMPTS — lane 155-SIMP-d01-c01-dedup (simplifier/tester pass)

Base `origin/erenup/integration` at `86bf360` (lanes 144–153).  Worker edits only; lead commits.
All six review items were executed (none skipped).  Hard rules held: no `sorry`/`admit`/`axiom`/
`native_decide`; no consumed statement was changed or weakened (all changes are dedup/layering, plus
**additive** new lemmas for F2; the `16^m`/`256` theorems are byte-identical).

## Dependent set (recorded before editing; `grep -rln import … formalization verification research`)

Direct importers of the four review-target modules (source `.lean` only):

* `D01.FiniteOrderNorm` ← `C01.PressureJetPath`, `A01.OrderTwoCap`
* `D01.FiniteOrderConstructor` ← `D01.FiniteOrderNorm`, `A01.EulerPairing`
* `C01.JetPaths` ← `C01.PressureJetPath`
* `A04.ZeroSolution` ← (none)
* `A04.PressureDrop` ← `A04.EnergyIdentityHigh`, `A04.ZeroSolution` (the latter dropped by item 4)
* `D01.SmoothDatum` ← `A04.GradientFiniteness`, `D01.ForceClass`, `D01.OrderZeroDatum`,
  `A03.RealAngularProduct`, `D01.DatumToJets`, `D01.DerivativeDatum` (+ transitive)
* `A01.CarrierWords` ← `A01.L2Descent`

All of the above were rebuilt green (see gates).

## Per-item table

| item | files touched | removed / added | consumers rebuilt |
|---|---|---|---|
| 1 · F3 hoist | `D01/FiniteOrderConstructor.lean` (+48/−36), `D01/FiniteOrderNorm.lean` (dup deleted) | ~+55 (hoisted lemma) / −55 (duplicate) net ≈ 0, one canonical copy | `FiniteOrderNorm`, `OrderTwoCap`, `PressureJetPath`, `EulerPairing` |
| 2 · F2 sharp | `D01/FiniteOrderNorm.lean` (+184/−61) | +~150 new (identity + `4^m` constructor); `16^m`/`256` unchanged | same as item 1 |
| 3 · C01 N1 | `C01/JetPaths.lean` (+7/−5) | rename `continuous_jetLp_sumField`→`sumField_jetLp_continuous` | `PressureJetPath` |
| 4 · A04→D01 | `D01/SmoothDatum.lean` (+9), `A04/PressureDrop.lean`, `A04/ZeroSolution.lean` | `isSobolevDatum_zero` sunk to `SmoothDatum`; `PressureDrop` import dropped from `ZeroSolution` | `PressureDrop`, `EnergyIdentityHigh`, `ZeroSolution`, 6 `SmoothDatum` importers |
| 5 · A01 N3 | `A01/CarrierWords.lean` (−94 net) | 3 subsumed theorems retired (`word_descent_ae`, `_partial`, `hword_jet_of_descent`); helpers kept | `L2Descent` |
| 6 · tester | research axioms/probe files | conformance + negative probes updated for the above | — |

## Item details / decisions

**1 · F3 hoist.**  `coord_smul_deriv_ae` (the a.e. Fourier identity `(2πi)(ξⱼ·Aᵢ) =ᵐ frequencyUnit·Cⱼᵢ`)
was a verbatim ~50-line duplicate of the inline `heq` inside `memLp_coord_smul_datum`.  Hoisted the
lemma into `FiniteOrderConstructor.lean` (same statement as before) placed just before
`memLp_coord_smul_datum`, rewrote `memLp_coord_smul_datum` to consume it (deleting the inline block),
and deleted the copy from `FiniteOrderNorm.lean` — it now resolves via the existing import (same
`D01` namespace).  `eLpNorm_coord_smul_eq` is unchanged.

**2 · F2 sharp constant.**  Added, all in `FiniteOrderNorm.lean`, all axiom-clean:
`eLpNorm_raiseIntegrand_sq_eq` (the Plancherel identity `∫⁻‖(1+‖ξ‖²)^{1/2}Aᵢ‖ₑ² =
∫⁻‖Aᵢ‖ₑ² + ∑ⱼ∫⁻‖ξⱼAᵢ‖ₑ²` via `‖ξ‖² = ∑ⱼξⱼ²`, modelled on §0's `eLpNorm_component_sq_sum`),
`norm_raiseHilbert_sq_eq` (`‖raiseHilbert Aᵢ‖² = ‖Aᵢ‖² + ∑ⱼ‖Cⱼᵢ‖²`), `norm_raise_sq_eq`
(`‖raise A‖² = ‖A‖² + ∑ⱼ‖Cⱼ‖²`), and the sharp constructor `exists_isSobolevDatum_norm_le_sharp`
(`c_m = 4^m`) with its transfer `norm_isSobolevDatum_le_of_memLp_derivs_sharp` and the `m=2` instance
`norm_isSobolevDatum_le_two_sharp` (`c₂ = 16`, not `256`).  The existing `exists_isSobolevDatum_norm_le`
/ `norm_isSobolevDatum_le_of_memLp_derivs` / `norm_isSobolevDatum_le_two` (`16^m`/`256`, consumed by
lanes 147/148) are **byte-identical** — the sharp ones are strictly stronger (`4^m ≤ 16^m`) and left
separate rather than re-deriving the old ones (re-derivation would have been longer, not shorter).

**3 · C01 N1 — chose the rename (Option B), zero edits to `Source/`.**  The brief's tie-breaker is
"fewer edits to `Source/`".  Investigation showed the generalize-in-place option is also *partly
infeasible*: `Source.PhysicalBesselSobolev.continuous_jetLp_laplacianField` is about a **different**
`laplacianField` (the `ℂ` one at `PhysicalBesselSobolev.lean:16`, using `basis`) than
`C01.laplacianField_jetLp_continuous` (the `Space` one at `OrdinaryViscousStability.lean:12`, using
`axis`), so the C01 laplacian copy is not a Source duplicate and cannot be deleted.  Only
`continuous_jetLp_sumField` genuinely name-collides.  Renamed the C01 copy to `sumField_jetLp_continuous`
(matches the file's `X_jetLp_continuous` convention; no bare-name clash with the `ℂ` Source version
under simultaneous `open` — the LESSONS-109 hazard N1 cited).  Confirmed no module `open`s
`Section4.C01` (so no live ambiguity today) and `PressureJetPath` uses neither name.

**4 · A04→D01 layering.**  `isSobolevDatum_zero` moved from `A04/PressureDrop.lean:170` into
`D01/SmoothDatum.lean` (next to `IsSobolevDatum`, D01 namespace, proof `intro i ψ; simp` ports
unchanged).  `PressureDrop`'s own uses (`velocity_datum_lerayComplement_eq_zero`) resolve via its
existing `open …D01`; **no A04 alias was added** — an alias would be ambiguous, since both A04
consumers (`PressureDrop`, `ZeroSolution`) `open …D01` (LESSONS-109).  `ZeroSolution` had to add
`isSobolevDatum_zero` to its *selective* `open …D01 (…)` list and dropped `import …A04.PressureDrop`.
**Import-closure (transitive `NSFormalization.*`) of `A04.ZeroSolution`: 109 → 89** (−20 modules: the
whole Leray/pressure stack — `LerayMultiplier`, `LeraySymbol`, `LerayDatum`, `LerayLowering`,
`Longitudinal`, `Transverse`, `OrderZero{Datum,Symbol,Curl,Algebra}`, `RealPairing`,
`LaplacianPairing`, `MomentumSlice`, `Pressure`, `PressureJets`, `DivergenceTime`, `HalfOrder`,
`A04.{MomentumDatum,TimeDerivative,PressureDrop}`).  Research consumers updated:
`axioms_hpr.lean` (`#print axioms` qualified to `D01.isSobolevDatum_zero`),
`rev144_mutation.lean` (`open …A04 (isSobolevDatum_zero)` → `…D01 (…)`).

**5 · A01 N3 retirement.**  `word_descent_ae`, `word_descent_ae_partial`, `hword_jet_of_descent`
(all order-restricted, `n+3 ≤ q+1`) were retired from `CarrierWords.lean`.  Grep confirmed **no
non-research term-level consumer**: `L2Descent` references them only in docstrings and is built on the
*helpers* (`wordField`, `wordField_field`, `descent_step_ae`, `word_eq_zero_of_mem_zero`,
`eLpNorm_jet_component_le`, `locInt_component_*`), all of which are kept and — verified — remain
reachable (none orphaned).  Updated `axioms_carrier_words.lean` (dropped the three `#print`s and the
`hword_jet_of_descent` non-vacuity example) and `rev153_subsumes.lean` prose (that probe never
referenced the retired names at term level — it re-proves their statements from the `L2Descent` full
versions, so it still compiles).

**6 · tester.**  Conformance files re-run — every declaration prints exactly
`[propext, Classical.choice, Quot.sound]`: `axioms_finite_order_norm` (now 21 lines incl. the 6 new
F2 lemmas), `axioms_finite_order_close` (9, incl. hoisted `coord_smul_deriv_ae`), `axioms_jet_paths`
(18, incl. renamed `sumField_jetLp_continuous`), `axioms_144` (11), `axioms_hpr` (10),
`axioms_carrier_words` (8).  Negative probes fail for their **intended** mutation reason (verified the
error line): `rev145_mutA` `:312`, `rev145_mutB` `:410`, `rev145_mutC` `:426` (their local
`coord_smul_deriv_ae` copy was renamed `…_local` to avoid clashing with the now-imported hoisted one),
`rev146_mutation` `:33/:40`, `rev144_mutation` `:27/:34/:41`, `rev153_mut1_slice` `:56`.

## Skipped

None.  All six items executed.

## Gates and results

* `lake build` — every touched module + the whole dependent set (18 modules): **Build completed
  successfully (10335 jobs)**, exit 0.  Each touched module also byte-clean under `lake env lean`
  (zero warnings).
* `scripts/gates.sh <7 touched modules>`:
  * `make check` — exit 0.
  * `make test` — every registered contract "checked; standard logical axioms only".
  * `make test-mutations` — `implementation_refactor` accepted; `admitted_proof`/`extra_axiom`/
    `weakened_hypothesis` rejected as required; "Mutation suite passed".
* `python3 experiments/check_contracts.py` (no `--base-ref`, == `make check`): exit 0.
* `python3 experiments/check_contracts.py --base-ref origin/erenup/integration`: **fails with
  `AssertionError: Removed stable specification: verification/Contracts/V3/EnergyAbsorptionPartial.lean`
  — STALE-BASE noise, not a regression from this lane.**  This branch's merge-base is `86bf360`; the
  live `origin/erenup/integration` tip is `f40bbf3`, which has since gained
  `Contracts/V3/EnergyAbsorptionPartial.lean` (absent on this branch).  This lane changes **no**
  `Contracts/` file (`git diff --name-only origin/erenup/integration...HEAD | grep Contract` is empty).
  Against the true merge-base — `check_contracts.py --base-ref 86bf360` — it passes with
  `base_compatibility_checked: true`, exit 0.  Fix (lead): rebase onto `origin/erenup/integration`,
  then re-run.  (LESSONS 2026-09-14/123: after rebasing, `grep` for any stale import paths — none
  expected here.)
