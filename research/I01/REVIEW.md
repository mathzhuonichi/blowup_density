# I01 review — Packet energy and early vanishing

**ACCEPT-WITH-NOTES.** `research/I01/Spec.lean` typechecks with zero diagnostics, is
axiom/`sorry`-free and theorem-free, and every field of `PacketAPI`,
`packetStatement` and `PacketFamily` encodes the claim at the paper location its
doc comment cites. No field is stronger or weaker than the manuscript in a way
that affects Section 4. The findings below are all minor: two imprecise
citations in `COMPARISON.md`, three interval/redundancy notes on `Spec.lean`, and
three cosmetic line-range slips. Nothing blocks I02/I03.

## Issues, ranked

| # | Sev | Field / row | Paper or source location | What differs | Suggested fix |
|---|---|---|---|---|---|
| 1 | minor | `COMPARISON.md`, `energy_isLUB` row | `PEP:152-166` | Row says the existing bound is "the sharper form `l2Sq u t ≤ B²` with `B = sup_{t∈[0,1]}‖F(t)‖₂`". The statement at `PEP:154-155` is `∃ B, 0 ≤ B ∧ … ∧ l2Sq u t ≤ B`, with `B` existentially bound and tied to `PEP.uniform_force_norm` only inside the proof, not in the statement. | Reword to "`∃ B ≥ 0, l2Sq u t ≤ B`; the proof instantiates `B = (sup_{[0,1]}‖F‖₂)²`". |
| 2 | minor | `COMPARISON.md`, `pressure_support` row | `SPE:104-112` | Row says "Same bridge, `SPE:104-110`". `SPE:104-105` is the *velocity* bridge via `PEP.tsupport_subset_of_zero_outside`; the pressure case is inlined at `SPE:106-112` with a bare `closure_minimal`, not that lemma. | Cite `SPE:106-112` and say "same argument, inlined rather than via `PEP:142-148`". |
| 3 | minor | `force_quiet`, `velocity_quiet`, `pressure_quiet` | `02-preliminaries.tex:152` | Paper: `F = 0` on the **closed** `[0,τ]`, hence `U = 0` there. Spec uses the open `Ioo 0 quietTime`, i.e. strictly weaker. Harmless: `zero_initial_velocity` and `force_zero_nonpos` already cover `t = 0`, and every consumer lemma (`PS.zeroPastField_smoothOn` `PS:373-377`, `PS.zeroPastField_equation` `PS:471-477`, `PP.pressure_vanishes_on_quiet_interval` `PP:55-63`) takes exactly an `Ioo 0 ε` germ. | Keep as is; add one clause to the `force_quiet` doc comment noting the germ is deliberately open. |
| 4 | minor | `dissipation_eq` | `02-preliminaries.tex:131`; `R3CE:195-196` | `square_integrable` is an explicit field guaranteeing the spatial `L²` integral is honest, but there is no analogous field for the spatial integrability of `‖∂ᵢU(t)‖²`, and `dissipation` is a totalized Bochner integral too. Not vacuous — it follows from `velocity_smooth` + `velocity_support` — but the asymmetry is undocumented. | Add one sentence to the `dissipation_eq` doc comment: spatial integrability of the gradient follows from smoothness plus compact carrier. |
| 5 | minor | `quiet_lt_one` | `02-preliminaries.tex:133` | Redundant: `velocity_quiet` with `quietTime ≥ 1` would force `U ≡ 0` on `(0,1)`, contradicting `speed_unbounded`. Doc comment already says "forced by `speed_unbounded`". | Keep (it makes unit 8 pure assembly); no change needed. |
| 6 | minor | `PacketFamily` | `01-introduction.tex:36, 63-66` | The paper fixes one `ν` and then one packet; `PacketFamily.select` chooses one for **every** `ν`. Stronger than the text, but obtainable from `packetStatement` by `Classical.choice` with no new axiom, and `PacketAPI ν` keeps `M`, `D` `ν`-dependent as the manuscript requires. | Note only. |
| 7 | minor | `COMPARISON.md` line ranges | — | `PS:471-486` (actual `471-485`), `SPE:70-86` (actual `70-85`); trailing blank lines included. | Trim by one. |
| 8 | minor | `COMPARISON.md` follow-up A | `PS:260-264`, `PS:286-297` | Cited as groundwork for the `Iio 1` versions, but both are stated on `Ioo 0 1` / `Ico 0 1`, so they are not reusable verbatim on the extended interval. Explicitly out of I01 scope. | Add "restated on `Ico 0 1`; the `Iio 1` version needs a separate step". |

No blocker and no major issue. Nothing was found that is *weaker* than the paper
in a way a consumer relies on, and nothing *stronger* that would make the record
unprovable.

## Fidelity: what was confirmed correct

Objects, time domains, constants, regularity and the equation all match.
Specifically: `preSingularDomain = Ico 0 1 ×ˢ univ` (`PS0:42`) is the paper's
`ℝ³×[0,1)` with time first; the equation lives on the open `Ioo 0 1`
(`01-introduction.tex:20-23`, matching the "no derivative of an arbitrary
extension at `t=0`" convention) while the extension field
`extension_navier_stokes` covers all `t < 1` as `03-torus.tex:141` and
`04-whole-space.tex:36` need; `navierStokesResidual ν` (`R3PS:57-62`) puts `ν` on
the spatial Laplacian only, as in `eq:NS`; a single `carrier` serves `U` and `P`
per `01-introduction.tex:24-25`; `force_support = CompactPositiveTimeSupport`
(`R3PS:66-67`, `positiveTimeDomain` `R3PS:53`) is the closed-support reading of
`C_c^∞(ℝ³×(0,∞))`, and `force_zero_nonpos` is exactly clarification `C1`
(`logs/SOL_MAX_AUDIT_SYNTHESIS_20260912.md:51-73`) as inserted at
`03-torus.tex:108-109`.

The two constants are the correct ones, not kinetic energy:
`l2Sq u t = ∫‖u(t,x)‖²` (`R3CE:190`), so `Real.sqrt (l2Sq …)` is `‖U(t)‖_{L²}` and
`energy_isLUB` is literally `M := sup_{0≤t<1}‖U(t)‖₂` (`02-preliminaries.tex:130`);
`dissipation u t = Σᵢ∫‖∂ᵢu(t)‖²` (`R3CE:195-196`) is `‖∇U(t)‖₂²`, so
`dissipation_eq` is `D := ‖∇U‖_{L²((0,1)×ℝ³)}` (`02-preliminaries.tex:131`), with
no `ν` factor, as the manuscript has it. The nearby `kineticEnergy = ½∫‖u‖²`
(`R3PS:76-77`) is correctly *not* used. `speed_unbounded` (`PS0:94-96`) is the
pointwise `∀M>0 ∀δ>0 ∃t∈(1-δ,1)∩(0,1), ∃x, M<‖u(t,x)‖`, the faithful reading of
`limsup_{t↑1}‖u(t)‖_∞=∞` (`01-introduction.tex:28`) for continuous compactly
supported slices. `ν` is quantified outside (`01-introduction.tex:16`) exactly as
`packetStatement : ∀ ν, 0 < ν → Nonempty (PacketAPI ν)`.

## Consumers (check 4)

Walking `prop:scaling` (`03-torus.tex:101-159`) and `thm:Rinsert`
(`04-whole-space.tex:31-79`) term by term, **no packet property is used that is
not a field of `PacketAPI` or a direct consequence of one.** In particular:
finiteness of `‖F‖_{L^q_tL^p_x}` and of `‖F(·,σ)‖_{Ḣ^s}` (`eq:packetFscale`,
`eq:packetHs`) follows from `force_smooth` + `force_support`; `U_ε(·,0)=0`
(`prop:scaling`, "start from zero") follows from the zero past since
`(0-t_ε)/ε² < 0`; `U(t) ∈ H^∞` (`04-whole-space.tex:53`) follows from
`velocity_smooth` + `velocity_support`; the `L²` pressure gradient
(`04-whole-space.tex:51`) from `pressure_support`; `u_ε = v` for `t ≤ T-2ε²`
(`04-whole-space.tex:36`) is `σ ≤ -1` in the inactive past. `K_*`
(`03-torus.tex:101-102`) is *definable* from `carrier_compact` + `force_support`
and is correctly left to I02/I03. The only deliberate omission is the
"Consequently, no global finite-energy smooth solution" clause
(`01-introduction.tex:30-33`, Lean `¬ Nonempty GlobalFiniteEnergySolution`,
`R3PS:125-135, 150-153`), which Section 4 never invokes — confirmed: `thm:Rinsert`
derives breakdown from `SpeedUnboundedAtOne` plus `prop:local`.

## Flagged choices (check 6)

* **`energy_isLUB` vs a plain upper bound** — consistent, and in fact *required*:
  `eq:packetEscale` (`03-torus.tex:125-128`) asserts the **equality**
  `‖U_ε‖_{L^∞(0,T;L²)} = ε^{1/2}M`, which a mere upper bound cannot give. Not
  gold-plating; does not block.
* **Excluding the "Consequently" clause** — consistent. It is a corollary of
  Theorem 1.1 that Section 4 never cites; it belongs to node `U01`. Does not block.
* **`SpeedUnboundedAtOne` vs `limsup` of the sup norm** — consistent. The
  pointwise form is what both consumers use, and the `limsup` equivalence
  (asserted in the vendor docstring `R3PS:85-87`, proved nowhere) is not needed by
  Section 4. Does not block; worth closing eventually as follow-up B.
* **Two routes to the quiet interval** — consistent. The `τ = 3/8` route (`VP:135`,
  `SPE:52,78`) is an artifact of the OpenAI time switch; the faithful route is
  `PE.vanishes_before_forcing` (`PE:197-229`, already at arbitrary `ν ≥ 0`) plus
  `PP.pressure_vanishes_on_quiet_interval` (`PP:55-69`, arbitrary `ν`). Keeping both
  is fine because `PacketAPI` only asks for *some* `τ`. Does not block.
* **`K_*` deferred to I02/I03** — consistent. `03-torus.tex:101-102` defines `K_*`
  in the scaling setup, not in Theorem 1.1 or Lemma 2.2, and its two ingredients
  are already fields. Does not block.

## Check log

1. **Typecheck.** `. scripts/lean-env.sh; cd verification; LEAN_NUM_THREADS=6 lake env lean ../research/I01/Spec.lean` → **exit 0, no stdout, no stderr, zero diagnostics.**
2. **Hygiene.** `grep -nE "sorry|axiom|admit|native_decide|unsafe" research/I01/Spec.lean` → one hit, `12: axiom.  Nothing here asserts…`, inside the module docstring. `grep -nE "^\s*(theorem|lemma|example|instance)\b"` → no matches. Declarations are exactly `structure PacketAPI` (65), `def packetStatement` (210), `structure PacketFamily` (216) and five `PacketFamily` projections (221, 225, 229, 233, 237).
3. **Fidelity.** Read `01-introduction.tex:14-34, 60-67`; `02-preliminaries.tex:1-10, 122-153`; `logs/SOL_MAX_AUDIT_SYNTHESIS_20260912.md:49-73`; `03-torus.tex:95-165`. Every doc-comment line citation in `Spec.lean` resolves to the claimed text.
4. **Consumers.** Read `03-torus.tex:101-159` and `04-whole-space.tex:25-79`; result above.
5. **Reuse spot-checks (18 rows, all confirmed at the cited lines unless noted):** `PS0:30, 35-36, 42, 67-68, 94-96`; `R3PS:53, 57-62, 66-67, 71-72, 76-77, 81-83, 85-88, 92-109, 125-135, 150-153, 173-178`; `R3CE:190, 195-196, 198`; `Source/Insertion.lean:21-24, 26-28`; `PS:243-244, 246-252, 260-264, 278-282, 286-297, 373-391, 471-485, 506-523`; `VP:69-79, 81-98, 118-121, 131-151`; `SPE:47-66, 52, 70-85, 90-114, 99, 104-112`; `PEP:24-33, 38-64, 68-140, 142-148, 152-166, 171-183`; `PE:143-181, 197-229, 233-255`; `PP:17-30, 33-52, 55-69`; `PFE:15-32, 36-49, 53-65`; `R3CC:28-31, 248-252`; `R3ActualCandidate:18-21`; `ActualCandidateAssembly:1177`; `ViscosityScaling:18-22`. Discrepancies: issues 1, 2, 7, 8 above. No overclaim about `ν`-generality was found: `PE.vanishes_before_forcing` really is stated for `0 ≤ ν`, `PE.packet_dissipation` for `0 < ν`, `PP.*` for arbitrary `ν`, and `VP.selected_packet_every_viscosity` for arbitrary `0 < ν` via the `a = √ν` spatial dilation (`VP:136-142`, `ViscosityScaling:18-22`) — a spatial, not parabolic, rescaling, so the singular time stays at 1, as `COMPARISON.md` states.
6. **`residual`/`navierStokesResidual` bridge.** Scratch file `/tmp/I01_rfl_bridge.lean` (`import NSFormalization.Source.ViscosityPacket`; `example … : NSFormalization.Source.residual ν u p t x = NavierStokesR3.ProblemStatement.navierStokesResidual ν u p t x := rfl`) → `lake env lean` **exit 0**. The `COMPARISON.md` claim holds; the definitional equality closes by `rfl`. File deleted. (First attempt importing only `Source.Insertion` failed with `unknownIdentifier NavierStokesR3.ProblemStatement.navierStokesResidual` — that module does not transitively import `R3/ProblemStatement`; not a defect, only an import note for unit 5.)

No file other than this one was created or modified; no git write command was run.
