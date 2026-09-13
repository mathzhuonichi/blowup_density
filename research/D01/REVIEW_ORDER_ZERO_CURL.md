# Review — lane 108 (D01, P2 SL7b-β): order-0 longitudinal / curl-free identity

Reviewer: opus, 2026-09-13.  Under review: commit `c91c163` on `erenup/108-D01-p2-sl7b-curl`
(`formalization/NSFormalization/Section4/D01/OrderZeroCurl.lean`, 517 lines / 14 declarations;
`research/D01/ATTEMPTS_ORDER_ZERO_CURL.md`; `research/D01/axioms_order_zero_curl.lean`).
Base `fe05a28`.  Everything below was re-run by the reviewer in this worktree.

## Verdict: **ACCEPT**

The mathematics is right, the statement is the paper's, the hypotheses are exactly the three
claimed (no hidden integrability), the corollary is the promised one-liner, the two re-proved
helpers and the pairwise transport are genuinely not available from 094, and both recorded
failures reproduce verbatim.  All findings below are cosmetic or SIMP/scheduling debt; none of
them blocks the merge.

---

## 1. Compiles / hygiene  (check 1)

| command (from the worktree, `. scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`) | result |
|---|---|
| `cd verification && lake build NSFormalization.Section4.D01.OrderZeroCurl` | `Build completed successfully (9916 jobs).` |
| `cd verification && lake env lean ../formalization/NSFormalization/Section4/D01/OrderZeroCurl.lean` | **no output**, exit 0 (no warnings, no linter hits) |
| `cd verification && lake env lean ../research/D01/axioms_order_zero_curl.lean` | 14 declarations, **each** `[propext, Classical.choice, Quot.sound]` |
| `grep -nE 'sorry\|admit\|axiom\|native_decide\|maxHeartbeats\|set_option'` on the module | one hit, line 46, inside the module docstring prose ("No `sorry`, no `axiom`") — **no code hit** |
| `make check` | exit 0 (contract policy 13/13, work queue 30 items consistent) |
| `bash scripts/gates.sh NSFormalization.Section4.D01.OrderZeroCurl` | `== gates OK` (exit 0): `make check`, build, `make test` = 18 contracts "standard logical axioms only", `make test-mutations` = `extra_axiom` and `weakened_hypothesis` both rejected, `check_contracts --base-ref origin/erenup/integration` `base_compatibility_checked: true` |

The axiom audit covers all 14 public declarations, including the `def wAnti`.  The lane adds no
contract and touches no frozen file; the diff is 3 files / +694 lines, all new.

## 2. Statement fidelity  (check 2)

**(a) Hypotheses are exactly the three claimed.**  `#check` output:

```
@orderZeroDatum_longitudinal_of_curl_free :
  ∀ {z : Space → Space} (hz : MemLp z 2 volume),
    ContDiff ℝ ↑⊤ z →
      (∀ (i j : Fin 3) (x : Space), (partialDeriv i z x).ofLp j = (partialDeriv j z x).ofLp i) →
        ∀ᵐ ξ, ∀ i j, ↑(ξ.ofLp i) * ↑↑↑((orderZeroDatum hz).ofLp j) ξ
                   = ↑(ξ.ofLp j) * ↑↑↑((orderZeroDatum hz).ofLp i) ξ
```

No fourth argument, so nothing can be hidden.  Grepping the module for
`SmoothL2Field | MemLp (fderiv | Integrable (partialDeriv | HasCompactSupport z | MemHmVector |
SmoothL2` returns **zero hits**.  The `z`-side inputs used inside are only `memLp_component hz j`
(from `MemLp z 2`) and `zc_smooth hsmooth j` / `hasFDeriv_zc` (from `ContDiff ∞ z`); every
integration by parts is against the compactly supported cutoff `χ_R ψ`, never against `z`'s
derivatives.  This is the point of the lane (non-circular order-0 seed) and it holds.

Also checked: `partialDeriv i z x j` unfolds through `A03.lift` + upstream `spatialDerivative` to
`(fderiv ℝ z x (coordinateVector i)) j` **by `rfl`** (verified, see (f)), so the time-lift in
`partialDeriv` introduces no hidden time dependence.

**(b) The conclusion is literally 089's `hlong`.**  `#check` of
`Leray.lerayComplement_eq_self_of_longitudinal` prints the same `∀ᵐ ξ, ∀ i j, ↑(ξ.ofLp i) *
↑↑↑(h.ofLp j) ξ = ↑(ξ.ofLp j) * ↑↑↑(h.ofLp i) ξ` shape, at a general real order `s`.  The
corollary (`:510`) is the promised one-liner — a term, not a tactic block:

```lean
lerayComplement_eq_self_of_longitudinal 0 (orderZeroDatum hz)
  (orderZeroDatum_longitudinal_of_curl_free hz hsmooth hcurl)
```

Confirmed: 089's own `lerayComplement_eq_self_of_curl_free` is stuck at order `(m:ℝ)+1 ≥ 1` and
requires a `SmoothL2Field` plus an `IsSobolevDatum` hypothesis; it cannot reach order 0.  108
bypasses that correctly by going through Lemma C at `s = 0`.

**(c) The weight-matrix lemma.**  Hypothesis is exactly `∀ x, ∑ i, ∑ j, w i j * ((partialDeriv i z
x j : ℝ) : ℂ) = 0`, i.e. `∑ᵢⱼ wᵢⱼ ∂ᵢz_j(x) = 0`, with `w` a *constant* matrix (stated as such in
the docstring).  Conclusion `∑ᵢⱼ wᵢⱼ ∫ (∂ᵢψ) z_j = 0`.

*δ instance → 094.*  I wrote `/tmp/rev108/delta.lean`: 094's `Cut.physical_pairing_zero` is
recovered from `physical_weighted_pairing_zero` at `w i j = if i = j then 1 else 0` in a
**3-line proof** (compiles, exit 0):

```lean
  have h := physical_weighted_pairing_zero hz hsmooth (fun i j => if i = j then (1 : ℂ) else 0)
    (fun x => by simpa [Finset.sum_ite_eq, ← Complex.ofReal_sum] using hdiv x) ψ
  simpa using h
```

So the generalization is real (094 is strictly an instance), and the SIMP factoring is cheap.

*Antisymmetric instance / sign check.*  `wAnti p q i j = [i=p ∧ j=q] − [i=q ∧ j=p]`, so the
pointwise hypothesis is `∂ₚz_q − ∂_qz_p = 0`, which is exactly `hcurl p q x`, and the conclusion
is `∫ (∂ₚψ) z_q − ∫ (∂_qψ) z_p = 0`.  **No sign slip:** the underlying identity is
`∫ (∂ₚψ) z_q = −∫ ψ ∂ₚz_q` and `∫ (∂_qψ) z_p = −∫ ψ ∂_qz_p`, whose difference is
`−∫ ψ (∂ₚz_q − ∂_qz_p) = 0`; the two minus signs cancel and the orientation of `wAnti` matches
the orientation of `hcurl`.  Degenerate case `p = q` gives `wAnti p p = 0` and the statement
`0 = 0` — harmless, and `sum_wAntisym_mul p p a = a p p − a p p` is consistent.

The sign survives downstream unchanged: `tempered_antisym_eq` uses `hstep d c : (∂_d z_c)(ψ) =
−∫ (∂_dψ) z_c` on both sides, and `fourier_antisym` multiplies both sides by the same `2πi`, so
the Fourier sign convention of `𝓕` is irrelevant to the identity.

**(d) The cutoff/DCT argument is 094's, index-generalized.**  I diffed
`OrderZeroSymbol.lean:198–300` against `OrderZeroCurl.lean:148–285`.  The two proofs agree
line-for-line on: `exists_deriv_bound`/`C`, `cn n = (n+1)⁻¹`, `chic n = ↑(χ n)`, `‖chic‖ ≤ 1`,
`chic → 1`, `‖∇chic‖ ≤ C·cn n` (094's `chi_deriv_bound`), the Leibniz split `hterm`, the
dominating function `‖(∂ᵢψ) z_j‖` (Schwartz × L², integrable by `memLp_component hz j` ⊗
`(∂ᵢψ).memLp 2`), `tendsto_integral_of_dominated_convergence` for the B-part, and
`squeeze_zero_norm` with bound `C·cn n·∫‖ψ z_j‖` for the A-part (the `C/R` boundary term).  The
only change is `j ↦ i` in the derivative index plus per-`(i,j)` limits (`hBlim_ij`, `hAlim_ij`)
assembled by a double `tendsto_finsetSum` against the constant weights.  That is a mechanical
generalization, exactly as claimed.

The fundamental-lemma side condition **is** discharged: Mathlib's
`ae_eq_zero_of_integral_contDiff_smul_eq_zero` wants `LocallyIntegrable f`, supplied by
`(hloc p q).sub (hloc q p)` where `hloc d c` is built from
`(Lp.memLp (𝓕 (componentLp hz c))).locallyIntegrable (by norm_num)` (L²_loc ⊂ L¹_loc, i.e.
`1 ≤ 2`) times a continuous coordinate, via `LocallyIntegrableOn.continuousOn_mul`.  The "for all
smooth compactly supported `g`" side is `hpair` evaluated at `hg1.toSchwartzMap hg2`, the same
Schwartz-packaging trick as 094.

**(e) Non-vacuity — machine-checked.**  `/tmp/rev108/nonvac.lean` (compiles, exit 0):

* the zero field satisfies all three hypotheses (trivially);
* `zb := ∇(bump)` with `bump = Cut.bump : ContDiffBump (0 : Space)` (`rIn = 1`, `rOut = 2`)
  satisfies `MemLp zb 2 volume` (continuous + compact support), `ContDiff ℝ ∞ zb`, and
  `hcurl` (Clairaut, `ContDiffAt.isSymmSndFDerivAt`), and
  `Leray.lerayComplement_zero_orderZeroDatum_eq_self zb_memLp zb_smooth zb_curl` typechecks;
* `zb ≠ 0`: `¬ (∀ x, zb x = 0)` is proved (`is_const_of_fderiv_eq_zero` + `bump 0 = 1` vs
  `bump (3•e₀) = 0` by `ContDiffBump.zero_of_le_dist`).

So the hypothesis class is **not** forced to `z = 0`, and the datum of such a `z` is not `0`
either: `isSobolevDatum_orderZeroDatum` realizes `z`, so a zero datum would force
`∫ψ z_i = 0` for every Schwartz `ψ`, hence `z = 0` a.e., hence `z = 0` by continuity.  (Only the
last sentence is a pen-and-paper step; the Lean part above is the substance.)

**(f) The `HasSymmetricJacobian` bridge is one line.**  `/tmp/rev108/bridge.lean` (compiles,
exit 0) with lane 106's `A01/RadialPotential.lean:101` definition copied verbatim:

```lean
theorem hcurl_of_hasSymmetricJacobian {G : Space → Space} (hG : HasSymmetricJacobian' G) :
    ∀ (i j : Fin 3) (x : Space), partialDeriv i G x j = partialDeriv j G x i :=
  fun i j x => hG.2 x i j                       -- one line, no unfolding

example (G : Space → Space) (i j : Fin 3) (x : Space) :
    partialDeriv i G x j = (fderiv ℝ G x (coordinateVector i)) j := rfl
```

i.e. the two scalar shapes are **defeq (`rfl`)** — the `lift`/`spatialDerivative`/eta layers all
reduce — and the only work is reordering `∀ x i j` into `∀ i j x` and dropping the
`Differentiable` conjunct.  SL8 can feed 106's `hasSymmetricJacobian_pressureGradient hp ht` into
this lemma with `fun i j x => (hasSymmetricJacobian_pressureGradient hp ht).2 x i j`.
(Note: `PressureGauge.lean` is not in this worktree — 108 branched before #109 merged — so the
bridge was checked against the verbatim definition read out of `origin/erenup/integration`.)

## 3. Consistency  (check 3)

Imports are the two canonical upstream modules (`D01.OrderZeroSymbol`, `D01.Longitudinal`); no
`Contracts` import, no restated upstream definition, no local re-statement of `Space`,
`partialDeriv`, `orderZeroDatum` or `lerayComplement`.  The contract import policy does not apply
(the file lives in `formalization/`), and `check_contracts.py` is green.

The four duplicated units are all justified — I re-read 094 to confirm each:

1. `Cut.fderiv_zc_eq'` (:61) vs 094's `fderiv_zc_eq` (`OrderZeroSymbol.lean:142`): 094 is stated
   only at `k = j`.  Verified in `/tmp/rev108/super.lean` that 094's statement is **exactly** the
   instance `fderiv_zc_eq' hsmooth j j x` (one-line term, compiles).
2. `Cut.cs_ibp` (:68) vs the `hibp` block inlined in 094's `cs_pairing_zero` (:170–181): 094 never
   exposes it, and inlines it only at `k = j`.  Confirmed by reading.
3. `fourier_lineDeriv_apply` (:332) vs the `hterm` block inlined in 094's `fourier_transverse`
   (:405–420): again only the diagonal `d = c`, and again inlined, not named.  Confirmed.
4. `longitudinal_of_longitudinal_symm` (:443) vs 094's `transverse_of_transverse_symm` (:491):
   094's is stated **only** for the divergence *sum* `∑ⱼ ξⱼ gⱼ = 0`, a single scalar identity, so
   it cannot produce the pairwise shape `ξᵢ g_j = ξⱼ g_i`.  ATTEMPTS' claim is correct.  I diffed
   108's body against 089's `longitudinal_of_curl_free` §2 (`Longitudinal.lean:182–215`) after
   substituting `(A k : FourierData) ↦ g k`: identical except for collapsing two `refine
   ae_all_iff.2` lines into one.  So it is a faithful abstraction of an existing body, not new
   mathematics.

**SIMP factoring plan** (for lane 109 or a follow-up MAINT lane; 094/089 are frozen so 108
correctly does not touch them):

* Promote `fderiv_zc_eq'` into `OrderZeroSymbol` and replace `fderiv_zc_eq` by the `j j` instance
  (verified one-liner); promote `cs_ibp` and rewrite 094's `cs_pairing_zero` `hibp` to use it.
* Promote `physical_weighted_pairing_zero` and re-derive 094's `physical_pairing_zero` from it at
  `w = δ` (verified 3-line proof).  This removes ~90 duplicated lines of cutoff/DCT machinery.
* Promote `fourier_lineDeriv_apply` and shrink 094's `fourier_transverse` `hterm` to it.
* Promote **both** transports — 094's `transverse_of_transverse_symm` *and* 108's
  `longitudinal_of_longitudinal_symm` — plus `angularFrequencyDilation_coeFn` to
  `Paper3/AngularFourierDilation.lean`, then rewrite 079/089/094/108 to consume them.
  **Scheduling note for the lead:** lane 109 (MAINT-promotions, in flight) already has the
  transverse one and `angularFrequencyDilation_coeFn` in scope; 108 adds a second copy of the same
  pattern, so 109 should pick the pairwise form up too (or the follow-up should).  108's base has
  **no drift** against current `origin/erenup/integration` in `Section4/D01`, `Paper3` or
  `Section4/A03` (`git log fe05a28..origin/erenup/integration -- …` is empty), so a rebase before
  merge is mechanical; only a re-build is needed.

## 4. Honesty of ATTEMPTS  (check 4)

Three cited declarations opened and checked (above): 094's `fderiv_zc_eq`/`cs_pairing_zero`
(diagonal only), 094's `transverse_of_transverse_symm` (divergence-sum only), 089's
`lerayComplement_eq_self_of_longitudinal` (real order `s`, matching shape).  The "Reused (not
re-proved)" list is accurate — everything named there is public in 094/089 or Mathlib.

Two recorded failures reproduced verbatim:

* `/tmp/rev108/fail1.lean` — `fin_cases p <;> fin_cases q <;> simp [Fin.sum_univ_three,
  Fin.ext_iff] <;> ring` on `sum_wAntisym_mul` →
  `error: Tactic 'simp' failed with a nested error: maximum recursion depth has been reached`.
  Exactly as recorded.
* `/tmp/rev108/fail2.lean` — the `calc` step justified by
  `(sum_wAntisym_mul p q (fun i j => ∫ …)).symm` →
  `error: (deterministic) timeout at 'whnf', maximum number of heartbeats (200000) has been
  reached` at the calc line.  Exactly as recorded, including the mechanism (beta-defeq on an
  integral-valued lambda).

I did not re-run the other two entries (the "`rw` did not find the pattern" and the
`Pi.sub_apply`/`smul_sub` shape issue); both are consistent with the shipped code, which uses
`rw [sum_wAntisym_mul] at hmain` with `a` inferred and `simp only [Pi.sub_apply, smul_sub]` before
`integral_sub`.

## 5. Findings

| # | severity | location | finding | fix |
|---|---|---|---|---|
| 1 | low (SIMP debt, already documented) | `OrderZeroCurl.lean:61,68,332,443` | four units duplicate diagonal/inlined content of 094 (~90 lines of cutoff machinery among them). Justified (094 frozen, exposes only diagonals), and ATTEMPTS says so. | the promotion list in §3, for lane 109 / a MAINT lane. Nothing to change here. |
| 2 | low | `OrderZeroCurl.lean:288,293` | naming: the `def` is `wAnti`, the contraction lemma is `sum_wAntisym_mul`. | rename to `sum_wAnti_mul` when promoting; not worth a churn commit now. |
| 3 | low | `:302, :352, :374` | `physical_antisym_pairing_zero`, `tempered_antisym_eq`, `fourier_antisym` each take the full `hcurl : ∀ i j x` but use only `hcurl p q x`. | weaken to the single-pair hypothesis when promoting, for reusability. The headline theorem genuinely needs all pairs. |
| 4 | low (systemic, not this lane) | — | `Section4/D01/OrderZeroCurl` is in no registered contract's Tests closure, so CI covers it only through `build_changed_lean.py`. | same as the rest of `Section4/*`; will be pulled in when P2's contract lands. |
| 5 | informational | `:302` | the docstring states the conclusion as `∫(∂ₚψ)z_q = ∫(∂_qψ)z_p` while the Lean statement is the difference `= 0`. Equivalent; the difference form is the one `sum_wAntisym_mul` produces and `sub_eq_zero` consumes. | none. |
| 6 | housekeeping | branch base `fe05a28` | 108 predates #109 (106 `PressureGauge`) and #111; needs a rebase onto current `erenup/integration` before merge. | verified there is **no** drift in the directories 108 depends on, so rebase + rebuild only. |

## 6. What remains for SL8 (`SmoothSquareIntegrableJets (∇p(t,·))`)

With 094 (order-0 transverse ⇒ `lerayComplement 0 (datum⁰ z) = 0` for solenoidal `z`), 108 (order-0
longitudinal ⇒ `lerayComplement 0 (datum⁰ z) = datum⁰ z` for curl-free `z`), 085
(`LerayLowering.lean`: `lerayComplement_lowerVectorL`, `isSobolevDatum_lower`,
`isSobolevDatum_lower_iff`, `leray_datum_lower`) and 111 (running: `orderZeroDatum` additivity,
slice regularity, the assembly table), **no analysis is left — only assembly**, in this order.
(i) At a fixed interior `t`, split the `H^∞` residual `h = f − (u·∇)u + νΔu` (SL0/055) as
`h = ∂ₜu(t,·) + ∇p(t,·)` (`D01/Pressure.lean`), and apply `lerayComplement 0` to
`orderZeroDatum h_t`: additivity of `orderZeroDatum` (111, cheapest via `isSobolevDatum_unique`
/ `Paper3.angularRealization_injective` on `isSobolevDatum_orderZeroDatum`) plus `map_add` of the
bundled `lerayComplement 0 : RVS 0 →L[ℝ] RVS 0` reduce it to the two halves; 094 +
`lerayComplement_eq_zero_of_transverse` (`LerayDatum.lean:316`) kills the `∂ₜu` half using 074's
`spatialDivergence_temporalDerivative_eq_zero` (by `rfl`), and **this lane** fixes the `∇p` half
using 106's `hasSymmetricJacobian_pressureGradient` through the one-line bridge verified in §2(f).
Result: `lerayComplement 0 (orderZeroDatum h_t) = orderZeroDatum (∇p(t,·))`, which
`isSobolevDatum_orderZeroDatum` immediately turns into `IsSobolevDatum 0 (∇p(t,·)) (…)`.
(ii) Bootstrap to every natural order `m`: take `A_m` the order-`m` datum of `h_t` (exists because
`h_t ∈ H^∞`), use 085's `lerayComplement_lowerVectorL` to move the complement through the lowering,
order-0 datum uniqueness to identify `lowerVectorL m 0 A_m` with `orderZeroDatum h_t`, and then
085's `isSobolevDatum_lower_iff` to lift the order-0 identity of step (i) back up to
`IsSobolevDatum m (∇p(t,·)) (lerayComplement m A_m)`.  This is precisely the missing "transport
lemma" listed as SL8's blocker in `P2_SPLIT.md:77`, now obtainable at order 0 only.
(iii) Convert data to jets: `DatumToJets.memLp_iteratedFDeriv_of_isSobolevDatum` for every `j ≤ m`
and every `m`, with smoothness from `DatumToJets.contDiff_slice_scalar` /
`contDiff_pressureGradient_slice` (106's `contDiff_gradSlice` is the same fact), giving
`SmoothSquareIntegrableJets (fun x => pressureGradient u.pressure t x)` through
`memHInfty_iff_smoothSquareIntegrableJets`.
**The only genuine plumbing still owed** is lane 111's item 3: `MemLp 2` and `ContDiff ∞` of
`∂ₜu(t,·)` and `∇p(t,·)` at interior times under `MemForceR f` (from `A02/SolutionClass` and
`ClassicalSolutionR.pressure_gradient`), which is what both 094's and 108's `hz`/`hsmooth` slots
consume.  Everything else above is `map_add`, uniqueness and rewriting.  Note that the order-0
**Plancherel norm identity** deliberately left out of `OrderZeroDatum.lean` is *not* needed for
SL8 — only the *realization* `isSobolevDatum_orderZeroDatum` is, and that is already proved.

## 7. Reviewer scratch files

`/tmp/rev108/{delta,bridge,nonvac,super,fail1,fail2,sig}.lean`, `/tmp/rev108/gates.log`.
The first four compile with exit 0; `fail1`/`fail2` are the intentional reproductions of the
recorded dead ends.
