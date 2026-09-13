# R42 — attempts, dead ends and decisions (lane 027)

Positive and negative record for `R42.insertion_family` v1. Companion:
`research/R42/COMPARISON.md` (clause-by-clause map).

## 1. Architecture: where the composition can live

`formalization/` is an upstream Lake package of `verification/`, so a module under
`NSFormalization/Section4/R42/` **cannot** import `Contracts.V1.*`. The first plan — "put the
composition in `Section4/R42/Assembly.lean`" — is therefore impossible as literally stated. The
split actually used is the one `I02`/`I03` already use:

* `formalization/NSFormalization/Section4/R42/Assembly.lean` — contract-free lemmas about the
  *Source* notions (`residual`, `spatialDivergence`, `parabolicForce`, `scaledSupport`);
* `verification/Bindings/InsertionFamily.lean` — the composition proper, feeding the `I01`,
  `I02`, `I03` and `D01` fields into those lemmas.

## 2. The reference: `ClassicalSolutionR` or the bare smooth field?

The task allowed either. `Data.ClassicalSolutionR ν a g (T+δ)` was chosen and **works**: all four
hypotheses `CorrectionAPI` imposes on `(v,π,g)` are consequences of it —
`velocity_smooth`/`pressure_smooth` restricted along `Ioo 0 (T+δ) ⊆ Ico 0 (T+δ)`, `divergence`
likewise, and `momentum` is literally the same statement on `Ioo 0 (T+δ)`. The converse fails, so
this is the only possible direction.

**Four** conclusions are only reachable this way and would have been lost with the bare smooth
field: `initial` (`u_ε(·,0) = a`); `incompressible` **at `t = 0`**
(`CorrectionAPI.reference_divergence_free` starts at `Ioo`, `ClassicalSolutionR.divergence` at
`Ico`); `velocity_smooth`/`pressure_smooth` on `Ico 0 T`, i.e. smoothness up to and including the
initial time — `CorrectionAPI.reference_smooth` and `reference_pressure_smooth` are on the *open*
slab `Ioo 0 (T+δ)` and reach no initial time, and the binding uses `R.velocity_smooth` and
`R.pressure_smooth` for exactly this; and naming `a` at all — without which neither lifespan
clause can even be *stated*.

Not done: deriving `CorrectionAPI` *from* the `ClassicalSolutionR` inside the binding. The
contract takes the `ScalingAPI` as a hypothesis field and the reference as another, with two
equations `reference.velocity = v`, `reference.pressure = π` pinning them together.

*Correction to the reason first recorded here* (reviewer issue 3): `correctionStatement`
(`Correction.lean:542-552`) takes `x₀` and `r` as **arguments** and concludes
`… ∧ A.x₀ = x₀ ∧ A.r = r`, so calling it would **not** have cost R42 the ball `B` as a parameter;
the only thing it binds existentially is `θRadius` — which is precisely the `K → K_*` gap of §3.
The decision stands, on the correct grounds: R42 must be composable with *any* already-registered
`I03` record for the packet (that is what `A.scaling = S` in `insertionFamilyStatement` asserts,
and what "the same family of inserted solutions", `04-whole-space.tex:43`, means), and R47 needs
`B` to be a parameter chosen by G01 (`research/section4/STATEMENTS.md:1276`). Rebuilding the
`CorrectionAPI` inside R42 would produce a *different* record from the caller's and break the
same-family identity.

## 3. `K → K_*`: three routes tried, one taken

The problem (diagnosed in `research/I03/REVIEW_CONTRACT.md` §5.1 item 4): nothing registered
relates `CorrectionAPI.θRadius` to `supp F`, so `ScalingAPI.eps_space : ε·θRadius < r` does not
place `F_ε` inside `B`, and clause 5 of Theorem 4.2 (`g_ε - g ∈ C_c^∞(B×(0,∞))`) is not
derivable from `I03` alone.

1. **Rejected — weaken the clause.** Drop the ball and state only
   `MemForceCompact (g_ε - g)`. This *is* provable, but it silently deletes the `B` of
   `04-whole-space.tex:38` and would break Theorem 4.7, which needs the force perturbation inside
   the grid cell. Not done.
2. **Rejected — add a hypothesis field** `∀ z ∈ tsupport P.force, z.2 ∈ ball 0 θRadius` to
   `InsertionFamilyAPI`. This is the premise `Source.insertion_at_scale` takes (`hfR`), and it is
   true by construction of the concrete binding — but a consumer that gets its `CorrectionAPI`
   from `checkedCorrection` can never discharge it, so the contract would be uninhabitable
   through the registered interface. That is exactly the inert-field problem the I03 review
   flagged; repeating it one level up would have made it worse.
3. **Taken — R42 recovers the enlargement itself.** `PacketAPI.force_support.1` gives
   `HasCompactSupport P.force`; its spatial projection is compact, hence bounded
   (`R42.exists_spatial_radius` → `R_F > 0`). `Bindings.threshold S := min S.ε₀ (r/(R_F+1))`
   makes `ε·R_F < r` on the whole `R42` range, and `R42.parabolicForce_ball` puts
   `tsupport F_ε` inside `ball x₀ r`. No new hypothesis, no weakened clause; the only price is
   `ε₀ < S.ε₀`, recorded as the field `eps_le_scaling`.

The right long-term fix is still an `I02` V2 letting the caller pin `θRadius` above a prescribed
compact set; see `research/R42/COMPARISON.md` §4.2.

## 4. Reusing `Source/InsertionFamily.lean`

`NSFormalization.Source.InsertionFamily.insertion_at_scale` already assembles almost exactly this
theorem, and `exists_insertion_family` even builds `Kall = K ∪ Prod.snd '' tsupport f`. It was
**not** reused, for two reasons:

* it requires `hv : ContDiff ℝ ∞ v` and `hvdiv : ∀ t x, div v = 0` **globally on spacetime** — a
  `ClassicalSolutionR` is smooth only on `[0,T+δ)×R³`; and
* it builds its own `physicalCorrection`/`correctionForce` rather than consuming `I02`'s
  `w_ε`/`H_ε`, so the result would not be about the registered family and `A.scaling = S` would
  be unprovable.

What *was* reused, unchanged: `Source.exact_insertion` (the cross-advection cancellation),
`Source.inserted_speed`, `PacketScaling.delayed_full_support`, `delayed_pressure_support`,
`parabolicForce_support`, `parabolicForce_positive_support`, `parabolicForce_smooth`,
`zeroPast_dilate_early`, `dilate_smoothOn`. The two slab lemmas in
`Section4/R42/Assembly.lean` are `Source.inserted_equation`/`inserted_divergence` with the
reference hypothesis weakened from `ContDiff` to `ContDiffOn` on `Ico 0 Tref ×ˢ univ`; their
proofs are the original ones with `ContDiffOn.contDiffAt` at interior points.

`Source/InsertionBreakdown.lean` (lifespan equality) was read and **not** used: it is stated
against `SmoothLifespan.Flow`, not `Data.ClassicalSolutionR`/`Data.maximalLifespanR`, and the
bridge between the two lifespan notions does not exist. Recorded in COMPARISON §3.

## 5. Not attempted, and why

* **`Data.MemForceR g_ε` and `Data.ClassicalSolutionR ν a g_ε T`.** Both need an order-`m`
  angular Sobolev datum path that is *smooth (resp. continuous) in time*.
  `Section4/I03/Angular.lean` builds the path and its `MemLp`, but not its time regularity, and
  there is no additivity lemma for `IsSobolevPath`. This is a D01 unit
  (`F_R + C_c^∞ ⊆ F_R`, `research/section4/STATEMENTS.md:270`), not an R42 one. Consequence
  recorded in COMPARISON §4.3: even the *easy* half `ofReal T ≤ maximalLifespanR ν a g_ε` of
  Theorem 4.2's lifespan clause is blocked here, not on A02. Note the precise status — that
  inequality **is a statable, well-formed `Prop`**; what fails is that it is *undischargeable*,
  because `maximalLifespanR` is a supremum over `Nonempty (ClassicalSolutionR ν a g_ε S)` and
  nothing produces an inhabitant.
* **`limsup_{t↑T}‖u_ε(t)‖_∞ = ⊤`.** `Data.lean` defines no spatial `L^∞` norm and no left
  limsup, and the pointwise `SpeedUnboundedAt` is what `I01` and `I03` produce, so that is the
  form registered. It is *not* a strengthening: in isolation it is the **weaker** reading
  (`esssup > M` ⇒ positive measure ⇒ `∃ x`, not conversely). The two are equivalent for every
  inhabitant of `InsertionFamilyAPI`, because `velocity_smooth` is co-carried and a continuous
  slice turns one witness point into a positive-measure set. Missing for the literal display:
  a spatial `L^∞` e-norm, `limsup … (𝓝[<] T) = ⊤`, and the continuity ⇒ `essSup` bridge.
  COMPARISON §4.1.

## 5b. Follow-ups filed by the reviewer

Two items that belong to other lanes, recorded here so they are not lost.

1. **I02 V2 — let the caller pin `θRadius` above a prescribed compact set.** `correctionStatement`
   existentially binds `θRadius`, so nobody reaching a `CorrectionAPI` through `checkedCorrection`
   can relate it to `supp F`, and every consumer that touches `F_ε`'s support repeats the shrink
   of §3 and acquires its own threshold. The fix is an `I02` V2 whose statement takes a compact
   set — for `R42` it is `P.carrier ∪ Prod.snd '' tsupport P.force` — and guarantees
   `θRadius` above it. After that, `ScalingAPI.eps_space` alone places all five rescaled fields
   `w_ε, H_ε, U_ε, P_ε, F_ε` inside `B`, and `R42` can take `ε₀ = S.ε₀` instead of a `min`.
   The reviewer is explicit that `R42` v1 must **not** be held for this.
2. **An `R42` V2 asserting `memF` must add a hypothesis field `hg : Data.MemForceR g`.**
   `InsertionFamilyAPI` currently carries **no** hypothesis that the reference force is in `F_R`
   (§5 above explains why none is needed for the registered clauses). `g_ε = g + H_ε + F_ε`, so
   `g_ε ∈ F_R` cannot follow from `g_ε - g ∈ C_c^∞` alone: the D01 unit
   `F_R + C_c^∞ ⊆ F_R` closes the gap only once `g ∈ F_R` is available. So the D01 unit by itself
   does not close the `≥ T` half of the lifespan clause at `R42`; a V2 of this contract must
   assume `hg` as well.

## 6. Lean frictions worth recording

1. **Metavariable leakage through `refine`.** `refine inserted_divergence_slab (by linarith …) ?_ …`
   elaborates the `by linarith` before the slab endpoint `Tref` is determined, and `linarith`
   then "proves" `T ≤ T` by assigning `?Tref := T`. Fixed by passing `(Tref := …)` explicitly and
   by `have`-ing the rewritten reference smoothness before the application.
2. **Higher-order unification on `?g (t, x)`.** `inserted_equation_slab`'s conclusion mentions
   `g (t, x)` where `(t,x)` is a pair, not a Miller pattern, so Lean cannot solve
   `?g (t,x) =?= g (t,x) + H (t,x)`. All of `ν, v, w, U, g, F, p, P` are now passed by name.
3. **`whnf` timeout in `blowup`.** Unifying `Contracts.V1.SpeedUnboundedAt T (insertedVelocity S ε)`
   against `PacketScaling.SpeedUnboundedAt T (fun z => ?b z + ?U z)` with both predicates and
   both fields as metavariables exceeds 200000 heartbeats. Fixed by an intermediate `have` with
   the fully concrete type; no `set_option maxHeartbeats` was needed.
4. `NavierStokes.SpatialCurl.contDiff_spatialSlice` is typed for `VelocityField`; pressure slices
   need `ContDiffOn.comp_contDiff (contDiff_const.prodMk contDiff_id) …` written out.

## 7. Gates

All from the worktree root after `. scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`, no `-j`.

| command | result |
|---|---|
| `bash scripts/lean-install.sh` | `== OK` |
| `make check` | pass — plan check, `check_contracts` (7 contracts), 13 policy tests, 30 work items |
| `make test` | pass — all seven contracts print `checked; standard logical axioms only` |
| `make test-mutations` | pass — `implementation_refactor` accepted; the other three rejected as required |
| `python3 experiments/check_contracts.py --base-ref erenup/integration` | `registered_contracts: 7`, `base_compatibility_checked: true` |
| `python3 experiments/build_changed_lean.py --base-ref erenup/integration --dry-run` | exactly four: `Bindings.InsertionFamily`, `Contracts.V1.InsertionFamily`, `NSFormalization.Section4.R42.Assembly`, `Tests.InsertionFamily`; the same command without `--dry-run` builds them (`Build completed successfully`) |
| `#print axioms` over 42 new declarations | every one `[propext, Classical.choice, Quot.sound]` |

No `sorry`, `axiom`, `native_decide`, `admit` or placeholder field in any of the four new files.
