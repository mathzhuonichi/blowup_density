# Lane 387-T22-UA4-orderzero-isometry — T22 U-A4: the order-0 vector Plancherel isometry `‖D01.orderZeroDatum hz‖ₑ = eLpNorm z 2 volume`

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/387-T22-UA4-orderzero-isometry` (git branch `erenup/387-T22-UA4-orderzero-isometry`, based on `origin/erenup/integration-section3`).
Read `CLAUDE.md`, **`research/T22/T22_SPLIT.md` §0 and unit U-A4 (and U-A5 `orderZero` for how it is consumed)**, `Section4/D01/OrderZeroDatum.lean` (`orderZeroDatum`, the docstring
"the norm identity is NOT proved here", `fourier_componentLp_mem :89`), `Section4/D01/HomogeneousWitness.lean` (`enorm_sq_piLp :405`, the `WithLp 2` vector carrier `RealVectorSobolev`),
`Paper3/AngularRealSobolev.lean` (`cyclesToAngularReal_symm_norm_le :84` — scalar; build the vector isometry `cyclesToAngularRealVector_symm_norm`), Mathlib's scalar Plancherel on
`Lp` (`MeasureTheory.Lp.norm_fourier_eq` / `fourierIntegral` isometry on `L²(ℝⁿ)` — grep the exact name under this pin), and the top 40 lines of `logs/LESSONS.md` (**name every instance
explicitly**).

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only.
- **No named inputs, no placeholders, no goal repackaging** (hard analytic unit). An honest partial with the exact residual statement and error text beats a stub.
- Every declaration must print exactly `[propext, Classical.choice, Quot.sound]`.

## Goal
New module `formalization/NSFormalization/Section3/T22/OrderZeroIsometry.lean` (namespace `NSFormalization.Section3.T22`): `theorem norm_orderZeroDatum_eq {z : SpatialField} (hz : MemLp z 2 volume) :
‖D01.orderZeroDatum hz‖ₑ = eLpNorm z 2 volume` (exact D01 spellings). Route: the Euclidean Pythagorean `L²` identity `eLpNorm z 2 volume ^ 2 = ∑ i, eLpNorm (fun x => z x i) 2 volume ^ 2`
(`PiLp`/`WithLp 2` norm, `lintegral` of a finite sum), the componentwise scalar Plancherel (the angular/unitary transform D01 uses — check whether `orderZeroDatum` is built from
`angularFourier`/`cyclesToAngularReal`, and use the matching isometry: Mathlib's `fourierIntegral` `L²` isometry composed with the fixed dilation/scaling that D01 applies), and
`enorm_sq_piLp` to reassemble the vector datum norm. Deliver the vector isometry `cyclesToAngularRealVector_symm_norm` as its own lemma if that is the missing piece.

## Deliverables
1. `Section3/T22/OrderZeroIsometry.lean`; 2. probe `research/T22/probes/orderzero_isometry_closes.lean` (a nonzero `ContDiffBump` field `z` with both sides finite and equal);
3. `research/T22/ATTEMPTS_UA4.md`, `research/T22/axioms_ua4.lean`, status in `research/T22/T22_SPLIT.md` U-A4, report `research/T22/REPORT_387.md` (if a guard blocks the write, put the full
report in your final message).

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T22.OrderZeroIsometry` (0 errors), `lake env lean` on module / probe / axioms file; `make check`.

## Report
Commit on your branch; end with four parts (theorems with exact statements / files / gaps with exact error text / commands and results).
