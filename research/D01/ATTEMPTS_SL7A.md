# SL7a — order-0 Plancherel seed: `MemLp z 2 volume → ∃ A : RealVectorSobolev 0, IsSobolevDatum 0 z A`

Lane 067, task D01, sub-lemma SL7a. Goal: the missing non-circular entry point that
manufactures an order-0 angular Sobolev datum from a *raw* square-integrable real
vector field (no jets, no L¹, no compact support).

## Route chosen (clean, fully general — no L¹, no jets)

The existing `SmoothDatum.exists_isSobolevDatum_of_contDiff_memLp` demands ALL jets
(`SmoothL2Field`), so it cannot seed order 0. Instead, at order 0 the Sobolev weight is
trivial and the datum is just the L² Fourier transform of each real component:

1. Component L² elements. `EuclideanSpace.proj i` then `Complex.ofRealCLM`, pushed through
   `ContinuousLinearMap.comp_memLp'`, gives `MemLp (fun x => ((z x i:ℝ):ℂ)) 2 volume`;
   `zc i := (·).toLp` is the L² element.
2. Cycles order-0 datum = the L² Fourier transform `𝓕 (zc i)` (Mathlib `Lp.instFourierTransform`,
   `Lp.fourierTransformₗᵢ`). Key: `Paper3.sobolevRealization_zero` says at order 0
   `sobolevRealization 0 h = ((𝓕⁻ h : Lp) : 𝓢')`, so `sobolevRealization 0 (𝓕 (zc i)) = (zc i : 𝓢')`
   via `fourierInv_fourier_eq`. No L¹, no pointwise Fourier integral.
3. Reality. `𝓕 (zc i) ∈ realSubspace 0` because the L² Fourier transform of a REAL function is
   conjugate-symmetric. This is exactly `SmoothDatum.fourier_conjugation`
   (`𝓕 (conjugation u) = realSymmetry (𝓕 u)`, proved by density from `RealSobolev.fourier_conjugate`,
   NO L¹) combined with `conjugation (zc i) = zc i` (a real function is its own conjugate a.e.).
   Then `realProjection (𝓕 (zc i)) = 𝓕 (zc i)` by `realProjection_eq_self`, so
   `realProjectionTo 0 (𝓕 (zc i))` realizes the same distribution.
4. Angular transport + assembly. `cyclesToAngularReal 0` moves cycles→angular preserving the
   realized distribution (`angularRealization_cyclesToAngularReal`) and the real subspace;
   `cyclesToAngularRealVector 0 (WithLp.toLp 2 (fun i => realProjectionTo 0 (𝓕 (zc i))))` assembles
   the three components, with `angularRealization_cyclesToAngularRealVector` giving the componentwise
   realization directly.
5. Pairing. `Lp.toTemperedDistribution_apply` unfolds `(zc i : 𝓢') ψ = ∫ ψ x • zc i x`, and
   `zc i =ᵐ (fun x => ((z x i:ℝ):ℂ))` closes `IsSobolevDatum` after `smul_eq_mul`.

## Why NOT the B02/LowHigh pointwise route
The task suggested lane 059's `coeFn_l2Fourier_ae` (pointwise `fourierIntegral` on L¹∩L²).
That would need `z ∈ L¹`, which `∇p` of a classical solution is NOT known to satisfy — it is
only L². `sobolevRealization_zero` gives the abstract-isometry realization with no L¹ hypothesis,
so the pointwise bridge is unnecessary and would be strictly weaker. `Lp.norm_fourier_eq`
(Plancherel, constant 1) is the only Mathlib isometry fact used, for the norm identity.

## Attempts / pitfalls log
(appended as they occur)

## Outcome — PROVED (first attempt compiled)

`formalization/NSFormalization/Section4/D01/OrderZeroDatum.lean`
`exists_isSobolevDatum_zero_of_memLp` builds clean, sorry/axiom-free.
`lake -d ../formalization build NSFormalization.Section4.D01.OrderZeroDatum` → `✔ Built ... (4.3s)`.
`lake env lean ../research/D01/axioms_sl7a.lean` → axioms `[propext, Classical.choice, Quot.sound]`,
and the `Contracts.V1.Data.IsSobolevDatum` example typechecks (defeq bridge from the
`Section4.D01` restatement).

### Design points that made it a one-shot
- `Paper3.sobolevRealization_zero` was the load-bearing lemma: at order 0 the realization is
  literally Mathlib's `L²` inverse Fourier (`(𝓕⁻ h : Lp) : 𝓢'`), so no `L¹`/pointwise integral.
- kept the component `L²` class `zc i` as a `let` (definitionally transparent) so the coercion
  `(realProjectionTo 0 (𝓕 (zc i)) : FourierData)` reduces to `realProjection (𝓕 (zc i))` under
  a single `show`; a `set` would have made `zc i` opaque and broken the `change`.
- reused `angularRealization_cyclesToAngularRealVector` (vector form) directly, so no manual
  `WithLp.toLp` index reduction was needed on the LHS.
- `SmoothDatum.fourier_conjugation` + `Complex.conj_ofReal` closed reality with no new work.

### Not done (out of scope for the seed)
- Full norm identity `‖A‖ = ‖z‖_{L²}`. It holds *componentwise* for free
  (`Lp.norm_fourier_eq` = Plancherel constant 1, and reality preserves the norm since the
  transform already lies in `realSubspace`), but the vector-to-physical bridge
  `‖A‖² = Σ_i ‖A i‖²` (`PiLp.norm_sq_eq_of_L2`) `= eLpNorm z 2 volume` needs the Pythagorean
  identity for `EuclideanSpace`-valued `L²`, a separate chunk. Left as a documented gap to keep
  SL7a tight; existence is what P2/I03 U7c need.

## Review fixes (ACCEPT-WITH-NOTES, `REVIEW_SL7A.md` findings F2, F3)

- **F2 — expose the datum.** Refactored the single `∃` theorem into named pieces so the norm
  identity can be *stated* against the datum later:
  - `def orderZeroDatum (hz : MemLp z 2 volume) : RealVectorSobolev 0` — the explicit datum
    (componentwise `L²` Fourier transform, real-projected, angular-transported).
  - `theorem isSobolevDatum_orderZeroDatum : IsSobolevDatum 0 z (orderZeroDatum hz)` — the
    realization (same proof as before, now stated against the named datum via `unfold`).
  - `theorem exists_isSobolevDatum_zero_of_memLp` retained as the `⟨orderZeroDatum hz, _⟩`
    corollary — nothing downstream breaks.
  - Also factored `memLp_component`, `componentLp`, `componentLp_ae`, `conjugation_componentLp`,
    `fourier_componentLp_mem` as reusable helpers (the previous `let zc`/`have`s hoisted to
    top level; `def componentLp` replaces the `let`, and the `show`-based defeq reduction of
    `WithLp.toLp` + coercion still goes through since `componentLp hz i` is the same subterm on
    both sides — no `cyclesToAngularReal` unfolding, so no heartbeat cost; build 3.4s).
- **F3 — module header.** Replaced the misleading line "The Plancherel norm identity is
  `Lp.norm_fourier_eq` (constant 1 …)" with an explicit "Scope: the norm identity is NOT proved
  here" paragraph: it is a separate ~25-50-line `Paper3` item needing the order-0 vector
  isometry `cyclesToAngularRealVector_symm_norm_le` (only the scalar exists; `ofSubmodules`
  unification is heartbeat-heavy) plus the Euclidean Pythagorean `L²` identity. Notes that
  `orderZeroDatum` is exposed precisely so that identity can be stated later.
- F1/F4/F5 were LOW/NOTE only and require no code change (F1 is the norm identity now documented
  in the header; F4 leaf-module CI entry lands with P2's binding; F5 process note — this touch
  used the canonical `verification$ lake build`).

### Commands (review fixes)
- `verification$ lake build NSFormalization.Section4.D01.OrderZeroDatum` → `✔ Built … (3.4s)`,
  `Build completed successfully`. No warnings from `D01/OrderZeroDatum`.
- `verification$ lake env lean ../research/D01/axioms_sl7a.lean` → both `Contracts.V1.Data`
  examples typecheck (defeq bridge); `#print axioms` for `orderZeroDatum`,
  `isSobolevDatum_orderZeroDatum`, `exists_isSobolevDatum_zero_of_memLp` all
  `[propext, Classical.choice, Quot.sound]`.
- `make check` → exit 0 (architecture checks, 13 policy tests OK, 30 work items consistent).
