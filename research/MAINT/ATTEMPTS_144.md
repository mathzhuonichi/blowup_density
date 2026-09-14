# Lane 144 (MAINT) — zero classical solution, landed once

New module `formalization/NSFormalization/Section4/A04/ZeroSolution.lean`
(namespace `NSFormalization.Section4.A04`) that lands the zero velocity/pressure
classical solution and its witnesses once, so the conformance / probe files stop
rebuilding it.

## Deliverables (all `#print axioms` = `[propext, Classical.choice, Quot.sound]`)

* `memForceR_zero : MemForceR (0 : SpaceTimeField)` (D01.MemForceR, direct)
* `zero_mem_initialClassR : (0 : SpatialField) ∈ initialClassR`
* `zeroSol (ν T : ℝ) (_hν : 0 < ν) (hT : 0 < T) : ClassicalSolutionR ν 0 0 T`
  (all ten fields), `zeroSol_velocity`/`zeroSol_pressure` = `0` (`@[simp]`, `rfl`)
* `sobolevNormAt_zero (s t) = 0`, `gradientSobolevNormAt_zero (s t) = 0`
* `hasSmoothSobolevPath_zero (T) : HasSmoothSobolevPath T (0 : SpaceTimeField)`
  and its `zeroSol`-specialisation `path_zero (ν T _hν hT)`
* `jets_zero`  (the zero field IS in `SmoothSquareIntegrableJets`) and
  `const_not_jets` (a nonzero constant field is `C^∞` but NOT in the jet class)

`datum_zero` was **not** re-created: `A04.PressureDrop:170 isSobolevDatum_zero`
(the "zero datum at every order") already exists and is reused verbatim
(brief bullet 1 — reuse, do not duplicate).

## Sources consolidated (best copy taken, sources credited in the module header)

| declaration | primary source | notes |
|---|---|---|
| `zeroSol` (fields) | `research/A01/axioms_a3_m2.lean` (lane 142) §0 = `research/D01/REVIEW_SL8_ASSEMBLY.md` app. A (lane 117) | byte-identical field proofs in both; generalised the horizon from the hard-coded `1` to `T` with `hT`. |
| `memForceR_zero` | lane 142 / SL8 app. A (identical) | proved directly against `D01.MemForceR`. |
| `zero_mem_initialClassR` | lane 142 | `datum_zero` call swapped for `isSobolevDatum_zero`. |
| `sobolevNormAt_zero` | lane 142 | `datum_zero` → `isSobolevDatum_zero`. |
| `path_zero` / `HasSmoothSobolevPath` witness | `research/A04/REVIEW_ENERGY_HIGH.md` app. (lane 128) | same `⟨fun _ => 0, …, contDiffOn_const⟩`; split into a zero-field lemma `hasSmoothSobolevPath_zero T` + the `zeroSol`-specialised `path_zero`. |
| `const_not_jets`, `jets_zero` | `research/D01/REVIEW_SL8_ASSEMBLY.md` app. A (lane 117) | copied verbatim. |
| contract-level `zeroSol` | `research/A04/REVIEW_CONTRACT{,_V2}.md` probes | those are `Contracts.V1.Data.ClassicalSolutionR` restatements; the same construction over the A02 restatement is what this module lands. |

## Decisions

* **Layer = A04.**  Deliverables span A02 (`ClassicalSolutionR`, `initialClassR`),
  D01 (`MemForceR`, `SmoothSquareIntegrableJets`) and A04
  (`HasSmoothSobolevPath`, `sobolevNormAt`, `gradientSobolevNormAt`,
  `isSobolevDatum_zero`).  A04 is the first layer above both A02 and D01, so it is
  the lowest layer whose imports suffice.  Imports:
  `A04.DerivNorm` (HasSmoothSobolevPath, + Continuity/Forcing for sobolevNormAt),
  `A04.LaplacianDatum` (gradientSobolevNormAt + `gradientSobolevNormAt_sq_eq_sum`),
  `A04.PressureDrop` (isSobolevDatum_zero), `D01.DatumToJets`
  (SmoothSquareIntegrableJets — not in `PressureDrop`'s closure, imported directly).
* **`MemForceR` from D01, opened explicitly (not from A02).**  A02 and D01 both
  carry a byte-identical `MemForceR` restatement (LESSONS: the "MemForceR note").
  Opening both makes the bare name ambiguous, so A02 is opened *without*
  `MemForceR` and D01 *with* it, exactly as lane 142 did.  `GronwallInstance`
  (the consumer in the retarget) opens `D01.MemForceR`, so the witness drops in.
* **`memForceR_zero` proved directly, not via `memForceR_of_memForceCompact`.**
  The compact route would need a `CompactPositiveTimeSupport 0` proof for no gain;
  the direct proof is four lines (`contDiffOn_const` + the zero datum path, `L¹`
  and `L²` by `MemLp.zero`).
* **`_hν : 0 < ν` is unused.**  The zero solution is a `ClassicalSolutionR ν 0 0 T`
  for *any* `ν` — no structure field constrains its sign (`ν • Δu = ν • 0 = 0`).
  The binder is kept to match the briefed interface and every consumer's own
  `0 < ν` hypothesis, but named `_hν` so the module is lint-clean (no
  `set_option` needed).  `hT` **is** used (`horizon_pos := hT`).
* **`gradientSobolevNormAt_zero` route.**  `partialDeriv j (fun x => 0) = 0`
  (`simp [partialDeriv, lift, spatialDerivative]`), each column enorm is
  `sobolevENorm_eq (isSobolevDatum_zero s)` = `0`, so
  `gradientSobolevNormAt_sq_eq_sum` gives `‖·‖² = ∑ 0 = 0`, then
  `pow_eq_zero_iff`.  This avoids unfolding the A03 `columnsSobolevENorm` `ℓ²`
  definition.
* **Two path names on purpose.**  `hasSmoothSobolevPath_zero` is stated on the
  *field* `(0 : SpaceTimeField)` (reusable, horizon-general, no `ν`); `path_zero`
  is the `zeroSol.velocity` specialisation (lane 142 name), a one-liner because
  `zeroSol.velocity = 0` by `rfl`.

## Retarget done (brief bullet 5)

`research/A01/axioms_a3_m2.lean`: §0 inline reconstruction deleted, replaced by
`import NSFormalization.Section4.A04.ZeroSolution` + `open` of the new names.
`zeroSol 1` → `zeroSol 1 1 one_pos one_pos`, `path_zero 1` →
`path_zero 1 1 one_pos one_pos`; the audit-specific `kbnd_zero` and the two
`nonvac_*` theorems stay, and `#print axioms` still reports the standard three
for all four printed names (`highOrder_bddAbove_of_kbnd`,
`highOrder_bddAbove_all_orders_of_kbnd`, and the two `nonvac_*`).

## Other places that could be retargeted later (NOT edited this lane)

Compiled `.lean` files that rebuild our zero objects inline:

1. `research/A01/probes/rev142_probe4_spatialfield.lean` — full rebuild
   (`datum_zero`, `zeroSol`, `memForceR_zero`, `zero_mem_initialClassR`,
   `path_zero`, `sobolevNormAt_zero`); near-identical to the old §0 here.
2. `research/D01/negative_simp_p2.lean` — `datum_zero`, `jets_zero`, `zeroSol`,
   `memForceR_zero`, `const_not_jets`.
3. `research/A01/axioms_a3_force.lean` — `memForceR_zero` only (feeds `forceCap`
   probes); could import just `memForceR_zero`.

Review `.md` appendices that carry the same inline reconstruction (records, not
compiled — retarget N/A, but they are duplicate sources of the code):

4. `research/D01/REVIEW_SL8_ASSEMBLY.md` app. A (the canonical source copy)
5. `research/A04/REVIEW_ENERGY_HIGH.md` app. (`path_zero`, `rhigh_on_zeroSol`)
6. `research/A04/REVIEW_CONTRACT.md` / `REVIEW_CONTRACT_V2.md` (contract-level)
7. `research/D01/REVIEW_CONTRACT_V3.md`, `REVIEW_SIMP_P2.md`, `REVIEW_HPR.md`,
   `REVIEW_G2B.md`, `REVIEW_HIGH_CONTINUATION.md`, `REVIEW_SL8_PREP.md`
   (reference `zeroSol` in prose/appendices).

**Out of scope — different object.**  `research/A01/axioms_a2b.lean`,
`axioms_a2b_inv.lean`, `axioms_a3_l2.lean`, `research/C01/axioms_e2.lean`,
`research/D01/probes/rev125_nonvac.lean` use the Euler
`EulerLpTranslation.SmoothL2Field.zeroField` (a Euler-carrier witness), **not**
our `ClassicalSolutionR`/`MemForceR` zero, so this module does not apply to them.
`research/A04/negative_simp_sl3.lean`'s `datum_zero_of_weakenedNoHL` is a datum of
a *weakened* hypothesis, also unrelated.

## Nothing left un-unified

Every inline copy of the zero classical solution, zero force, zero datum, zero
slice norms, zero smooth path, and the two jet-class witnesses now has a single
authoritative home in `A04.ZeroSolution`.  The audit-only `kbnd_zero` (order-2
cap = 0) is genuinely specific to the A3-M2 Grönwall audit and stays in
`axioms_a3_m2.lean`.

## Base note (for the lead)

The `144-MAINT-zero-solution` worktree was created from a stale local integration
(`cff1d20`, before lanes 139/142 merged), so `research/A01/axioms_a3_m2.lean` and
`Section4/A01/GronwallInstance.lean` were absent.  `cff1d20` is a clean ancestor
of `origin/erenup/integration` with zero local commits, so the worktree was
fast-forwarded to the integration tip `ed22b2f` (a pure ref advance, no new
commit) to match the brief's stated base.  No state-changing git beyond that
fast-forward; the lead commits the deliverables.

## Commands run

* `lake build NSFormalization.Section4.A04.ZeroSolution` — success (9942 jobs),
  only upstream HeliCorgi vendor warnings.
* `lake env lean ../formalization/NSFormalization/Section4/A04/ZeroSolution.lean`
  — silent, EXIT 0.
* `lake env lean ../research/MAINT/axioms_144.lean` — EXIT 0, all 11 declarations
  `[propext, Classical.choice, Quot.sound]`.
* `lake env lean ../research/A01/axioms_a3_m2.lean` — EXIT 0, no warnings, all
  four printed names standard three axioms.
* `make check` — EXIT 0 (architecture / contract-policy / work-queue checks pass).
