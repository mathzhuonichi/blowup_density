# Review — lane 056, A04 unit G1 (split of eq:Rhigh + the S sub-lemmas)

Reviewer run in worktree `.claude/worktrees/056-A04-g1-split`, commit `2bc9c2b`.
Scope: `research/A04/G1_SPLIT.md`, `research/A04/ATTEMPTS_G1.md`,
`research/A04/axioms_g1.lean`, `formalization/NSFormalization/Section4/A04/HighEnergy.lean`.

## Verdict

**ACCEPT-WITH-NOTES.**

The Lean is clean: both proved lemmas are correct, axiom-clean, warning-free, and
`inner_energy_Rhigh` is in eq:Rhigh's *literal* displayed shape — factor `½`,
dissipation on the left with a `+`, force term `‖f‖_{H^m}‖u‖_{H^m}` — matching
`paper/sections/appendix-a-local-theory.tex:129-138` and
`research/A04/Spec.lean:424-434` term for term.  Nothing is overclaimed: the
"done" column of the split table is accurate and the rejected approach recorded
in `ATTEMPTS_G1.md` is a real dead end.

The notes are about the **split document**, whose job is to route the follow-up
lanes.  Its headline analytic claim — that SL1 (unit **D2**) is an **L** lemma
blocked on an unowned A01 `C^∞_{t,x}` clause because "passing the limit inside
the integral is genuinely analytic" — is **wrong**, and wrong in a way that would
send a follow-up lane down a much harder road (or leave the frontier parked).
D2 is closable today in about 35 lines from machinery that is already on
`erenup/integration`; I compiled the scalar case end to end during this review
(finding 2).  That is a documentation defect, not a proof defect, so it does not
block the merge — but the split should be corrected before it is used as a work
plan.

## Findings

### 1. (INFO) Everything mechanical passes

See "Commands and results" below.  Build exit 0; no warning originates in
`HighEnergy.lean` (`lake env lean` on the file alone prints nothing); all four
`#print axioms` are exactly `[propext, Classical.choice, Quot.sound]`; no
`sorry` / `admit` / `native_decide` / `axiom` / `maxHeartbeats` / `set_option`
anywhere in the file (the only grep hit in `axioms_g1.lean` is the word "axiom"
inside its docstring); `make check` exit 0.

### 2. (MAJOR — document, not code) `G1_SPLIT.md:76-97`, SL1 / unit **D2**: the blocker is not real

`G1_SPLIT.md` marks SL1 **L, unowned**, and argues (lines 84-96) that the datum
uniqueness + difference-quotient route stalls because the Schwartz pairing
`lim_h ∫ ψ·q_h` needs dominated convergence, hence A01's `sobolev_smooth`.

Two things are wrong with that.

**(a) The difference-quotient route is not the cheap route, and the route my
brief suggested ("realization is a continuous linear map into distributions, so
`deriv` commutes with it") cannot even be *stated*.**  `𝓢'(Space, ℂ)` is
`𝓢(Space, ℂ) →L[ℂ] ℂ`, which carries no `NormedAddCommGroup` instance —
`HasDerivAt` does not typecheck into it.  I checked:

```
example : NormedAddCommGroup (SchwartzMap Space ℂ →L[ℂ] ℂ) := by infer_instance
-- failed to synthesize instance ... NormedAddCommGroup (𝓢(Space, ℂ) →L[ℂ] ℂ)
```

**(b) The *bounded representative* fixes exactly that, and then the whole of D2
falls out with no analysis at all.**  `Paper3.angularBoundedRepresentative s hs`
(`formalization/NSFormalization/Paper3/AngularTameProduct.lean:141`) is a
continuous linear map

```
Lp ℂ 2 volume →L[ℝ] BoundedContinuousFunction Space ℂ      (needs 2 ≤ s)
```

into a genuine **normed** space (sup norm).  Composing it with the submodule
inclusion `(RealSobolevHilbert s).subtypeL` and with
`BoundedContinuousFunction.evalCLM ℝ x` gives a CLM
`RealSobolevHilbert s →L[ℝ] ℂ`, and `HasFDerivAt.comp_hasDerivAt` then transports
the **Hilbert-space** derivative of the datum path to a **pointwise** derivative
at every `x`, for free.  The remaining three steps are all bookkeeping:

* pin the a.e. representative to the actual field — `A03.representative_ae`
  (`Section4/A03/ScalarTameProduct.lean:156`) plus `Continuous.ae_eq_iff_eq`,
  using that both sides are continuous;
* show the limit is real — its imaginary part is the derivative of the constant
  `0`, so `HasDerivAt.unique` kills it;
* convert back to `IsSobolevDatum` — `Paper3.angularRealization_boundedRepresentative`
  (`AngularTameProduct.lean:146`) says the realization pairs as
  `∫ ψ · representative`.

I proved the scalar component case in a throwaway file during this review; it
compiles `sorry`-free against the worktree as it stands.  Reproduced here so the
follow-up lane can lift it verbatim (the vector case is componentwise —
`A03.isSobolevDatum_iff` is `Iff.rfl` — plus the `PiLp` projection CLM to get
`HasDerivAt (fun r => G r i) (G' i) t`):

```lean
noncomputable def evalRep (s : ℝ) (hs : 2 ≤ s) (x : Space) : RealSobolevHilbert s →L[ℝ] ℂ :=
  (BoundedContinuousFunction.evalCLM ℝ x).comp
    ((angularBoundedRepresentative s hs).comp (RealSobolevHilbert s).subtypeL)

theorem hasDerivAt_rep (s : ℝ) (hs : 2 ≤ s) {G : ℝ → RealSobolevHilbert s}
    {G' : RealSobolevHilbert s} {t : ℝ} (h : HasDerivAt G G' t) (x : Space) :
    HasDerivAt (fun r => angularBoundedRepresentative s hs ((G r : FourierData)) x)
      (angularBoundedRepresentative s hs ((G' : FourierData)) x) t :=
  (evalRep s hs x).hasFDerivAt.comp_hasDerivAt t h

theorem representative_eq {s : ℝ} (hs : 2 ≤ s) {a : Space → ℝ}
    (hcont : Continuous a) (hmem : MemLp a 2 volume)
    {A : RealSobolevHilbert s} (hA : IsScalarSobolevDatum s a A) (x : Space) :
    angularBoundedRepresentative s hs (A : FourierData) x = ((a x : ℝ) : ℂ) :=
  congrFun (((map_continuous (angularBoundedRepresentative s hs (A : FourierData))).ae_eq_iff_eq
    volume (Complex.continuous_ofReal.comp hcont)).mp
      (representative_ae hs (locallyIntegrable_ofReal hmem) hA)) x

theorem d2_scalar {s : ℝ} (hs : 2 ≤ s) {T : ℝ} {u : ℝ × Space → ℝ}
    (hu : ∀ r ∈ Ico (0 : ℝ) T, Continuous fun x : Space => u (r, x))
    (hmem : ∀ r ∈ Ico (0 : ℝ) T, MemLp (fun x : Space => u (r, x)) 2 volume)
    {G : ℝ → RealSobolevHilbert s}
    (hG : ∀ r ∈ Ico (0 : ℝ) T, IsScalarSobolevDatum s (fun x => u (r, x)) (G r))
    {G' : RealSobolevHilbert s} {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T)
    (h : HasDerivAt G G' t) :
    (∀ x : Space, HasDerivAt (fun r => u (r, x))
        (angularBoundedRepresentative s hs (G' : FourierData) x).re t) ∧
      IsScalarSobolevDatum s (fun x => deriv (fun r => u (r, x)) t) G' := by
  have hnb : Ico (0 : ℝ) T ∈ 𝓝 t := Ico_mem_nhds ht.1 ht.2
  have hd : ∀ x : Space, HasDerivAt (fun r => ((u (r, x) : ℝ) : ℂ))
      (angularBoundedRepresentative s hs (G' : FourierData) x) t := by
    intro x
    refine (hasDerivAt_rep s hs h x).congr_of_eventuallyEq ?_
    filter_upwards [hnb] with r hr
    exact (representative_eq hs (hu r hr) (hmem r hr) (hG r hr) x).symm
  have him : ∀ x : Space, (angularBoundedRepresentative s hs (G' : FourierData) x).im = 0 := by
    intro x
    have h1 := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t (hd x)
    simp only [Function.comp_def, Complex.imCLM_apply, Complex.ofReal_im] at h1
    exact ((hasDerivAt_const t (0 : ℝ)).unique h1).symm
  have hre : ∀ x : Space,
      (((angularBoundedRepresentative s hs (G' : FourierData) x).re : ℝ) : ℂ)
        = angularBoundedRepresentative s hs (G' : FourierData) x := by
    intro x; exact Complex.ext (by simp) (by simp [him x])
  have hreal : ∀ x : Space, HasDerivAt (fun r => u (r, x))
      (angularBoundedRepresentative s hs (G' : FourierData) x).re t := by
    intro x
    have h1 := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (hd x)
    simpa [Function.comp_def] using h1
  refine ⟨hreal, ?_⟩
  intro ψ
  rw [angularRealization_boundedRepresentative s hs (G' : FourierData) ψ]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show ψ x * angularBoundedRepresentative s hs (G' : FourierData) x
      = ψ x * (((deriv (fun r => u (r, x)) t : ℝ) : ℂ))
  rw [(hreal x).deriv, hre x]
```

What this costs, and what it does **not** cost:

* `2 ≤ s` — free, `energyIdentityHigh` has `3 ≤ m`;
* each slice continuous — `D01.contDiff_slice w.velocity_smooth`
  (`Section4/D01/DatumToJets.lean:366`), from a field `ClassicalSolutionR`
  **already carries** (`velocity_smooth`, `A02/SolutionClass.lean:121`);
* each slice in `L²` — `D01.memLp_of_isSobolevDatum`
  (`DatumToJets.lean:267`) from the same smoothness plus `w.sobolev`;
* **no** dominated convergence, **no** difference quotients, **no**
  `isSobolevDatum_smul` (which really is absent, as the split says — but is not
  needed for D2), **no** new A01 clause.

Two further corrections follow:

* SL1 does **not** need `∂ₜu` to exist as a hypothesis; the route *produces* it
  (`hreal`).  The statement in `G1_SPLIT.md:76-82`, which gestures at "the field
  `x ↦ ∂ₜu(t,x)`" with a `has-time-deriv at t …` placeholder, should be restated
  as the conjunction above.
* Because the joint `C^∞_{t,x}` regularity is a **field of `ClassicalSolutionR`**
  and not an A01 obligation, the sentence "must come from A01's `sobolev_smooth`
  (or a dedicated D2 lane fed by it)" is doubly wrong: the regularity is already
  in hand, and the lemma does not need it in that strength anyway (continuity in
  `x` of each slice suffices).

**Fix:** rewrite SL1's entry as **S/M, closable now**, with the route above; move
it out of the "L frontier" list at the end of both `G1_SPLIT.md` and
`ATTEMPTS_G1.md`; drop the `isSobolevDatum_smul` prerequisite from SL1 (SL2 may
still want it).  Worth noting for SL2/SL3/SL4 as well: the same
"pin-the-representative" technique (`representative_ae` +
`angularRealization_boundedRepresentative`, which is exactly how
`A03.isScalarSobolevDatum_add/sub/mul` are proved at
`ScalarTameProduct.lean:168-220`) is likely to shorten those too, since it turns
datum identities into *pointwise* identities of continuous functions.

### 3. (MINOR — document) `G1_SPLIT.md`, SL6 paragraph: `MemHmVector` is not supplied by `ClassicalSolutionR.sobolev` alone

The SL6 entry says "`MemHmVector` of the slice comes from
`ClassicalSolutionR.sobolev` (N1)".  But
`MemHmVector m z = MemLp z 2 volume ∧ sobolevENorm (m:ℝ) z ≠ ⊤`
(`A03/VectorTameProduct.lean:48`), and `.sobolev` gives only a datum, i.e. only
the second conjunct (through `sobolevENorm_velocity_ne_top`).  The `MemLp` half
needs `velocity_smooth` as well.  The correct one-liner, which I compiled:

```lean
obtain ⟨G, -, hGd⟩ := w.sobolev m
exact ⟨memLp_of_isSobolevDatum (contDiff_slice w.velocity_smooth ht) (hGd t ht),
  sobolevENorm_velocity_ne_top w m ht⟩
```

**Fix:** one clause in the SL6 paragraph naming `velocity_smooth` and
`D01.memLp_of_isSobolevDatum`.  No code change.

### 4. (MINOR — optional hardening) `HighEnergy.lean:101`, `inner_energy_assembly`: `hlap` as an equality

`hlap : ⟪G, L⟫ = - grad ^ 2` is an equality, so the eventual SL3 must deliver the
dissipation identity exactly.  That matches the manuscript ("pairing … and
integrating by parts"), so it is not wrong.  But if SL3 on the datum carrier ends
up only proving `⟪G, L⟫ ≤ - grad ^ 2` (the usual outcome when the order shift is
proved as an inequality), the assembly would have to be restated.  Weakening
`hlap` to `≤` costs one extra hypothesis `0 ≤ ν` — which `energyIdentityHigh`
has (`0 < ν`) — and makes the lemma strictly more reusable.  Consider it; not
required for this lane.

### 5. (MINOR — risk to check at lane 053's merge) `hG : ‖G‖ = uNorm` and the inner-product norm

`inner_energy_assembly` bounds the force term with `real_inner_le_norm`, so the
`‖·‖` in `hG`/`hF` is the norm **induced by the `InnerProductSpace ℝ E`
instance**.  `A04.sobolevNormAt_eq` (`Continuity.lean:85`) is stated with the
existing `RealVectorSobolev s` norm.  Those coincide only if lane 053's
`Paper3.realSobolevInnerProductSpace` is built so that its induced norm is the
existing one (`InnerProductSpace.ofCore`-style instances create a *new*
`NormedAddCommGroup` and will not unify).  `RealVectorSobolev s` is
`PiLp 2 (Fin 3) (RealSobolevHilbert s)` over a closed `ℝ`-submodule of
`Lp ℂ 2 volume`, so the natural `⟪·,·⟫_ℝ = re ⟪·,·⟫_ℂ` does induce the existing
norm — but this should be *checked* (not assumed) when 053 lands, since
`G1_SPLIT.md`'s SL7 entry currently asserts it on the strength of a docstring.

### 6. (INFO) Honesty spot-check of `ATTEMPTS_G1.md`: the rejected approach is genuinely rejected

`ATTEMPTS_G1.md` "Approaches tried" bullet 1 claims that bounding `-⟪G, N⟫` by
`‖G‖·‖N‖` plus the advection tame bound produces two terms, not eq:Rhigh's one.
Confirmed twice over at `A03/OuterTameProduct.lean:306-311`:

```
sobolevENorm m (advectionOf u v) ≤ ofReal (advectionConst m) *
  (sobolevENorm 2 u * gradientSobolevENorm m v + gradientSobolevENorm 2 v * sobolevENorm m u)
```

— the right side is a two-term sum whose second term carries `‖∇v‖_{H²}`, which
is not `‖u‖_{H²}`, so it cannot collapse to eq:Rhigh's single
`C‖u‖_{H²}‖u‖_{H^m}‖∇u‖_{H^m}`; and its hypotheses are `SmoothL2` (the **jet**
carrier), not the datum carrier, so it would not even apply where the split needs
it.  Keeping `-⟪G,N⟫ ≤ NLbound` abstract was the right call.

Bullet 2 (`ENNReal.toReal_mono` rather than `toReal_le_toReal`, so the outer
norm's finiteness is never needed) is also accurate: `outerSobolevNormAt_le`'s
`calc` uses only `hfin` on the right-hand side.

### 7. (INFO) SL8 sanity instantiation

Requested check, run and then deleted.  With `N = P = 0`, `F = 0`, `L = -G` (so
`grad = ‖G‖`), `C = u2 = fNorm = 0`, the instantiation of `inner_energy_Rhigh`
typechecks and both sides of the conclusion evaluate to `0` — the bound is
**attained**, which is what pins the factor `½` and the sign of the dissipation
(with `d = -2ν‖G‖²` the two terms cancel exactly; a flipped dissipation sign
would give `-2ν‖G‖² ≤ 0`, false for `ν < 0`, and the lemma has no sign hypothesis
on `ν`).

### 8. (INFO) Hidden assumptions in SL8: none

`inner_energy_assembly` assumes no positivity of `ν`, `grad`, `C`, `u2`, and does
not secretly require `uNorm = ‖G‖` beyond the explicit `hG`.  `grad` occurs only
inside `grad ^ 2` and in `hlap`, so instantiating it at
`gradientSobolevNormAt (m:ℝ) u t` (a `toReal`, hence `≥ 0`) is unconstrained.
`uNorm`/`fNorm` are pinned by the equations `hG`/`hF`, which is consistent with
both being `toReal` values.  The five named hypotheses are exactly D1 (`hd`), the
momentum decomposition (`hmom`), the Laplacian identity (`hlap`), the pressure
drop (`hpr`) and the nonlinear bound (`hnl`), plus the two norm identifications —
i.e. exactly the interfaces SL0-SL5/SL7 are declared to supply.  Nothing in the
assembly is unsuppliable.

### 9. (INFO) SL6 is correctly wired to the registered constant

`outerProductTame` is consumed as the local `A03.outerProductTame`
(`A03/OuterTameProduct.lean:157`), which is exactly what the binding
`verification/Bindings/TameProduct.lean:122` assigns to the contract field
`TameProductAPI.outerProductTame`, with `Ctame := A03.outerTameConst` at
`Bindings/TameProduct.lean:102`.  The docstring's citations (`:102`, `:122`,
`:157`) are correct line for line.  The `ℝ≥0∞ → ℝ` step uses only the two
`≠ ⊤` facts, both of which are lane 039's N1
`A04.sobolevENorm_velocity_ne_top` (`Continuity.lean:65`) — I verified a consumer
can discharge them directly, with no cast friction between `sobolevENorm 2` and
`sobolevENorm ((2:ℕ):ℝ)`:

```lean
outerNormAt_le hm hz (sobolevENorm_velocity_ne_top w 2 ht)
  (sobolevENorm_velocity_ne_top w m ht)   -- typechecks as written
```

No new finiteness assumption is introduced.

### 10. (INFO) The split is honest about what is *not* done

Nine sub-lemmas (SL0-SL8), of which exactly SL6, SL8 and half of SL7 are claimed
done and are in fact done; SL2-SL5 and the SL7 carrier link are correctly left
open with their real blockers named (D01 L9(c) for the pressure, the datum-side
order shift for the Laplacian, lane 053's instance for the inner product).  None
of the open items is dressed up as closed.  Only SL1's blocker (finding 2) and
SL6's sourcing (finding 3) are inaccurate.

## Commands and results

All run from `verification/` after `. ../scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`,
no `-j`, one lake at a time.

| command | result |
|---|---|
| `bash scripts/lean-install.sh` | `== OK` (full build) |
| `lake build NSFormalization.Section4.A04.HighEnergy` | **rc=0**, `Build completed successfully (9889 jobs).` |
| `lake env lean ../formalization/NSFormalization/Section4/A04/HighEnergy.lean` | **rc=0, no output** (no warning originates in the file; the `ring`/deprecation warnings in the full build come from replayed `Source/`, `Paper3/` modules) |
| `lake env lean ../research/A04/axioms_g1.lean` | **rc=0**; all four of `inner_energy_assembly`, `inner_energy_Rhigh`, `outerSobolevNormAt_le`, `outerNormAt_le` → `[propext, Classical.choice, Quot.sound]` |
| `grep -E "sorry\|admit\|native_decide\|axiom\|maxHeartbeats\|set_option" …/HighEnergy.lean` | no match |
| same grep on `research/A04/axioms_g1.lean` | one hit, the word "axiom" inside the module docstring |
| `make check` (from the worktree root) | **rc=0** — plan check, contract check, 13 policy tests OK, `30 work items: ownership, contract registration and task cards consistent.` |
| scratch: SL8 heat-case instantiation + tightness | compiles, both sides `0` (deleted) |
| scratch: SL6 consumer chain from `ClassicalSolutionR` with no leftover hypothesis | compiles (deleted) |
| scratch: full D2 scalar route (finding 2) | compiles `sorry`-free (deleted; reproduced above) |
| scratch: `NormedAddCommGroup (𝓢(Space,ℂ) →L[ℂ] ℂ)` | instance synthesis **fails**, as expected |

## Paper conformance

`appendix-a-local-theory.tex:129-138`:

```
½ d/dt ‖u‖²_{H^m} + ν‖∇u‖²_{H^m} ≤ C_m‖u‖_{H²}‖u‖_{H^m}‖∇u‖_{H^m} + ‖f‖_{H^m}‖u‖_{H^m}
```

`inner_energy_Rhigh` conclusion:

```
(1/2) * d + ν * grad ^ 2 ≤ C * u2 * uNorm * grad + fNorm * uNorm
```

Factor `½` ✓; dissipation added on the left with `+ν` (absorbed exactly, no
Young — correctly deferred to unit G2) ✓; nonlinear term in the order
`C·‖u‖_{H²}·‖u‖_{H^m}·‖∇u‖_{H^m}` ✓; force term `‖f‖_{H^m}‖u‖_{H^m}` ✓.  Matches
`Spec.lean:424-434`'s `energyIdentityHigh` associativity and factor order
term for term, so the eventual `⟨d, hderiv, inner_energy_Rhigh …⟩` packaging will
not need any `ring_nf` massaging.
