---
name: auto-loop
description: >
  One autonomous-formalisation cycle. Domain-agnostic mechanics; the current targets happen
  to be the training-dynamics seabeds (DLN / tensor-network / balancedness, SLT-flavoured),
  but the loop applies to any paper-claim formalisation. Merges the tide exploration loop with
  the Clawristotle Aristotle-critique loop, adapted to a personal GitHub setup (no org), GPT-5.5
  via the `codex` CLI (no API), and theoremsearch + leansearch for retrieval. Human-in-the-loop
  on proof deliberation; formalisation itself runs autonomously to green.
---

# auto-loop — autonomous autoformalisation cycle

This is the unified workflow that replaces the timaeus-flavoured `tide` / `tide-pick` /
`lean-formalisation` trio and the `balancedness` Clawristotle `/babysit` loop. One cycle
takes a direction → a **compiling Lean skeleton** (frozen statement + `:= by sorry` body) → a
fan-out of independent **prover subagents** that drive it to green against the compiler → an
Aristotle honesty/structure critique → a retrospective.

The loop is a plain **skeleton-first prove loop**: the unit of work is a typechecking,
`sorry`-bearing skeleton whose *statement* is frozen after human sign-off; many independent
provers Ralph-loop on it with per-turn compiler feedback; a *validator* gates admission (frozen
statement intact + sorry/axiom-clean) and a metered prover-*oracle* (here: Aristotle) is called
on stuck subgoals. There is **no evolutionary search** — no EVOLVE markers, no searchable-value
slots, no rater/Elo/population layer; the fan-out is plain parallelism (keep the first to reach
green) and the honesty gates are the arbiter.

## Environment (this setup, not timaeus)

- **Seabeds** = the user's per-paper Lean formalisation repos (separate repos under personal
  `github.com/yangdabei/`). `~/Documents/formalisation/` holds ONLY Lean seabeds:
  `ttn/` (the TTN seabed home, empty until scaffolded), and the self-contained
  `dln-dynamics-formalisation` and `balancedness` (papers live inside them). **Research repos
  live in `~/Documents/`, not here** — the TTN research repo (experiments, theory notes,
  canonical paper `ttn-research-revised.tex`) is `~/Documents/ttn-dynamics`. A seabed and its
  research repo need not be adjacent; record both paths. First/primary target: the **TTN
  seabed** at `formalisation/ttn/` (greenfield — scaffold from `../autoformalisation-template`,
  formalising the results in `~/Documents/ttn-dynamics`).
- **No monorepo, no org.** Cross-repo reuse is a lake **git dependency** on
  `yangdabei/lean-common` (shared lemmas + the `scripts/`). Combine only the local folder.
- **`laplace` is timaeus' repo — never modify it.** It is only a scaffold reference.
- **GPT-5.5 = `codex` CLI** (`~/.local/bin/codex`), NOT the API. Invoke with
  `codex exec "<prompt>"` from inside the seabed (a git repo, so no `--skip-git-repo-check`).
- **Aristotle** = `aristotlelib` 2.x in the seabed's `.venv`; used to critique complex
  finished proofs (see Stage 4), not as the primary prover.
- **Retrieval**: `scripts/theorem-search` (arXiv + restatements; see [[theoremsearch-api]])
  and `scripts/lean-search` / loogle / `lean-lsp-mcp` (Mathlib). theoremsearch is NOT a
  Mathlib search — keep both.

Per-seabed `.mcp.json` registers the Lean LSP server and (optionally) the theoremsearch MCP
server — see `mcp.json.template` next to this file.

## The cycle

```
Stage 0   Pick direction        tide-pick survey + Role-B lit lane (auto)    [human picks]
Stage 1   Skeleton the idea     Claude ↔ codex → a compiling .lean skeleton  [human freezes stmt]
          └ frozen statement + `:= by sorry` body + numeric ground-truth check on constants
Stage 2   Prior-art scan        theorem-search (Role A) + lean-search        [autonomous]
          └ negative-results ledger checked (don't re-attempt a disproven route)
Stage 3   Fan-out prover loop   N Ralph-loop subagents, one per worktree     [autonomous → green]
          └ per-turn lean-lsp · Mathlib-first escalation · lake-timed · validator (first-to-green)
Stage 4   Critique complex pf   Aristotle: honesty audit + structure         [autonomous, gated]
Stage 5   Close                 retro + constants/findings + per-cycle metrics + yaml [autonomous]
          └ green → close ✓  |  blocked → reduce to one fact + DECISION [surface to human]
─────
Review loop (async, over already-closed work): fidelity + overclaim audit, batched by family
```

Run stages in order; do not offer to stop mid-cycle (the user owns session length). Pause only
at the human gates — Stage 1 (freeze the statement), Stage 4 (Aristotle proposes a different
*strategy* → fork), a **blocked ceiling** (Stage 5 blocked-close → surface the reduced
obstruction), and a scope shock (revised line-count ≥ 2× — consult codex, surface the revised
plan, continue). Everything else runs autonomously to green.

---

## Stage 0 — Pick direction (tide-pick + Role-B)

> If the targets are the **already-proven results of a given paper** (no direction to *discover*,
> just faithful transcription + proving), this is the wrong skill — use [[auto-formalise]], which
> replaces this Stage 0 with paper target-extraction and a dependency-ordered worklist, then runs
> Stages 1 → 5 unchanged.

If the user named a direction, skip to Stage 1. Otherwise survey and recommend.

**Frontier candidates (your research, primary).** Harvest from the seabed and research repo:
- `### Suggested follow-ups` in `<seabed>/tide-log/*.md`
- `\section{Follow-ups}` in `<seabed>/retrospectives/*.tex`
- open problems in the research repo's `notes/open-questions.md` and `notes/results/`
Rank by tide-shape: single statement, closed-form expectation where possible, reachable from
existing seabed, concretely stated and checkable against the source. Tier 1 = mechanical extensions of recent work;
Tier 2 = cost-positive refactors; Tier 3 = fresh-seabed into adjacent papers.

**Role-B substrate lane (auto, codex + theoremsearch).** This finds the *literature/building
blocks* you'd reuse — NOT novel directions (those are the frontier list above). Runs every
tide-pick. Pipeline:
1. **codex expands the query.** From the seabed's headline theorems + `notes/open-questions.md`,
   `codex exec` to produce 3–4 *query variants* (theoremsearch is literal/query-sensitive — a
   single query missed Saxe in testing). E.g. for TTN dynamics: "decoupled SVD mode dynamics",
   "hierarchical tensor factorization implicit regularization", "conservation law gradient flow".
2. **theoremsearch retrieves.** Run each variant: `scripts/theorem-search "<variant>" -n 8`,
   plus `--pagerank` for graph-flavored hits and `graph <id>` on the strongest hit to pull
   dependencies + cross-paper restatements. Dedupe by arXiv id.
3. **codex judges + backfills canon.** `codex exec` with the program context (the ladder,
   open-questions) + the deduped hits: "which are genuinely promising substrate/prior-art for
   this program, and which canonical landmarks are MISSING from this list?" codex backfills the
   famous results theoremsearch structurally misses. Web-verify only the final shortlist's
   arXiv ids (keeps it honest without ~4-min full-verify every cycle — tune via the prompt).
4. **Append to survey**, tagged `[substrate · theoremsearch+codex]`, ranked *below* frontier
   follow-ups. Each item: real arXiv link, one-line why-relevant, "already formalised?" flag
   from `theorem-search --lean` / `graph` restatements.

**Present + claim.** Write the survey to `<seabed-or-automation>/log/<date>-candidates.md`
(frontier first, substrate second). In chat: numbered list + top recommendation + rationale.
Mark the chosen candidate `🟡 In progress`, commit the claim, then hand to Stage 1.
(Optional auto-proceed: `ScheduleWakeup` ~240s; on wake, follow any user redirect else proceed.)

## Stage 1 — Skeleton the idea (HUMAN-IN-THE-LOOP)

The deliberation is unchanged; what *exits* the stage changes. The deliverable is no longer a
prose statement — it is a **compiling Lean skeleton**. If you cannot make the skeleton typecheck,
the research idea is underspecified, and you learn that here, in deliberation, not 200 lines into
a proof. This is the filter that makes an idea "good enough to check in Lean".

1. Skim seabed signatures + `CLAUDE.md`/`AGENTS.md`. Draft **2–3 minimal candidate statements**
   — specific, not generalised (four `n=0,1,2,3` lemmas beat one parity framework).
2. **Consult GPT-5.5**: `codex exec "Are these statements correct? Which is minimal? Better
   candidate?  <statements + context>"`. Save the reply verbatim to `gpt_responses/<topic>.md`.
3. **Write the skeleton** for the agreed candidate to `sketches/<topic>.lean`:
   - the **target theorem**, stated to track the paper, body `:= by sorry` — this is the
     *frozen statement* (the declaration signature);
   - helper lemmas and the proof body, which the Stage-3 provers fill in;
   - any genuinely unknown constant/closed-form as an ordinary `def` the proof will pin — there
     are no EVOLVE markers and no searchable-value slots.
   The skeleton must **typecheck** (skeleton-correct, `sorry`-bearing) before the stage closes. See
   `sketches/example-sketch.lean` in the template for the layout contract.
4. **Numeric ground-truth check (required when the statement pins a constant/closed-form).**
   Before freezing, verify every numeric claim in the statement independently — `codex exec` or a
   throwaway `python`/`scipy`/`mpmath` snippet evaluating both sides at a few sample points (e.g.
   *"∫q·w_b² = e^{b²}−1 matched scipy quadrature to ten digits at b=0.3"*). This is the cheapest
   possible catch for a misformalised constant — it costs seconds and fails *before* 200 lines of
   proof chase the wrong target. Record the check (values + tolerance) in `gpt_responses/<topic>.md`
   or the tide-log. A statement whose constants can't be numerically confirmed is not ready to freeze.
   (Analytic/qualitative statements with no numeric content skip this.)
5. **Human freezes the statement.** Surface candidates + codex's view + the typechecking skeleton
   to the human and let them steer. The human approves the **statement** (the declaration
   signatures); copy it to a read-only baseline (`cp sketches/<topic>.lean sketches/<topic>.frozen.lean`)
   — that becomes the Stage-3 validator's pin. Record the skeleton path in the tide-log before
   formalising. This human statement-review (read against the primary source) is the
   misformalisation guard — there is **no** numerical or special-case test-lemma gate.

## Stage 2 — Prior-art scan (autonomous)

Before building: has this been done, and what does it need?
- `scripts/theorem-search "<the statement, in words>"` → the arXiv result(s) you're formalising
  + `graph <id>` for dependencies and any Lean restatement (don't re-prove an existing one).
- `scripts/lean-search "<goal-shaped query>"` + loogle + `lean-lsp-mcp` semantic search → the
  Mathlib lemmas to build on. `rg` through `.lake/packages/mathlib/` is the fastest first move.
  **Feed the hits into the skeleton**: name the Mathlib lemmas the scan finds in a comment
  so the Stage-3 provers reach for them first (see the Mathlib-first ladder below).
- **Check the negative-results ledger.** Read `<seabed>/notes/negative-results.md` (see Stage 3):
  if a prior cycle *disproved* the route you're about to take (a counterexample, a "det-residue
  cannot suffice" reduction, a false lemma), don't re-attempt it — pick the surviving route or
  restate. This is the persistent memory that stops the fan-out from re-deriving the same dead end
  cycle after cycle.

## Stage 3 — Fan-out prover loop (autonomous, runs to green)

Freeze the statement (the `sketches/<topic>.frozen.lean` baseline), then spawn **N prover
subagents** (Agent tool), each in its own `git worktree` (branch `auto/<topic>-p<i>`) so they do
not race on imports / `.lake` / untracked files. Each runs an independent **Ralph loop** on the
same skeleton; keep the first to reach *validated* green, else the best partial. This is plain
parallelism (independent samples), not an evolutionary search.

**Inner Ralph loop (per subagent).** Episodes of multi-turn editing:
- `lean-lsp-mcp` is the inner loop — sub-second `lean_diagnostic_messages` / `lean_goal` /
  `lean_run_code` after **every** edit; `lake build` only at module boundaries. Run module-boundary
  builds through **`lake-timed build`** (the `soundings/bin/lake-timed` wrapper) so build wall-clock
  is logged to `.metrics/lake-build.jsonl` for the observatory — build time is the one metric that
  can't be recovered after the fact. The compiler error steers the next turn.
- Edit the **proof body** only; the frozen statement (the declaration signature) stays fixed. If
  a constant in the statement is genuinely unknown, the proof pins it — there is no separate
  searchable-value slot to vary.
- Decompose a monolithic goal into **named `sorry` lemmas** (factor when your direct-proof
  estimate is < 50%), then discharge each (Mathlib-first ladder below).
- End each episode that still has `sorry` by writing a `-- lessons:` comment **into the skeleton**;
  it seeds the next episode / subagent (finer-grained than a session handoff).

**Mathlib-first escalation ladder** (cheapest tier that closes the subgoal wins; prefer a
tier-1 discharge even in the *final* proof):

| Tier | Tool | Cost |
|---|---|---|
| 1 | **Mathlib search** — `lean_loogle` / `lean_leansearch` / `lean_state_search` / `lean_hammer_premise`, local-first; `rg` `.lake/packages/mathlib/` | sub-second, free |
| 2 | standard tactics / a small custom `have` | cheap |
| 3 | `codex exec` — informal strategy / **counterexample** (cheap disproof) | metered |
| 4 | **Aristotle** formal oracle on a clean stuck subgoal (Stage-4 mechanics, oracle mode) | expensive, queued |

Always try tier 1 first; a subgoal a `loogle` hit closes never reaches the metered tiers. Guard
against the **F2 failure mode** (hallucinated "known" lemma): before relying on a Mathlib name,
confirm it resolves with that exact signature via `lean_hover_info` / `lean_declaration_file` — an
unresolved name is a hallucination, not a TODO. Prefer Mathlib in the *proof*, but never contort
the **frozen statement** to fit a Mathlib structure (that is a misformalisation the validator
catches). Prefer thin Mathlib wrappers over reproved infrastructure; factor to `lean-common` only
on a lemma's *second* real use. For **naming, style, and tactic conventions**, consult
[`skills/lean-references/`](../lean-references/README.md) (`mathlib-style.md` for any new
declaration; the tactic / proof-golfing / refactoring notes on stuck or finished proofs) —
the convention source of truth, shared across all seabeds.

**Oracle escalation (tiers 3–4).** On a stuck subgoal, ask codex for a counterexample first
(cheap, informal); if it reports the lemma false, restructure. Escalate a *clean* subgoal to the
**Aristotle oracle** (submit the isolated subgoal, not the whole proof): proof → substitute;
disproof / failure → feed the message back into the prover's prompt. Aristotle is async and
metered — call it at episode boundaries / on stuck subgoals only, never per turn — through a
**flock'd submission queue with dedup and a per-cycle budget cap** so N provers don't submit the
same subgoal N times. (Mechanics + the queue: Stage 4.)

**Record disproven routes.** When codex/Aristotle *disproves* a candidate lemma or a whole route
(a counterexample, a "this reduction can't work" argument), append one line to
`<seabed>/notes/negative-results.md`: the route, why it fails (with the counterexample/point), and
the date/cycle. This is durable negative knowledge — Stage 2 of every future cycle checks it, so a
dead end is paid for once, not once per cycle. A route disproven twice is a *strong* signal the
statement itself needs restating (see the blocked-close path below).

**Validator gate.** A candidate is *validated green* only when `scripts/validate
sketches/<topic>.frozen.lean <current>` passes: every frozen declaration **signature** is
byte-identical to the baseline (difficulty not silently offloaded by mutating the target), it
compiles, `scripts/no_sorry.sh` is clean (zero `sorry` / `axiom` / `native_decide`), and the capstone
`#print axioms` reads only `[propext, Classical.choice, Quot.sound]`. Aristotle-returned proofs
pass this same gate — the oracle never bypasses the kernel.

If no subagent reaches validated green, continue from the **best partial** (most subgoals
closed): debug it directly, or escalate its remaining stuck subgoal to the Aristotle oracle.
There is no rater/Elo reseed — that evolutionary layer is deliberately not part of this loop.

**When it's a genuine wall, reduce — don't grind.** If the remaining obstruction is a real
multi-week gap (Mathlib lacks the machinery; every route bottoms out at the same fact), the cycle
does **not** fail — it converts to a *reduction*. Land the cycle sorry-free and axiom-clean **up to
one explicitly-stated hypothesis**: factor the wall into a single named lemma/hypothesis, prove
everything else against it, and prove the bridge from that lemma to the goal. The deliverable is
the located block — the single remaining fact, stated self-contained. Take the blocked-close path
in Stage 5. (Worked example: Quillen–Suslin Lemma D reduced local Horrocks to "φ_f surjective over
S_f", landed the bridge green, and named the ceiling — far more valuable than a red half-proof.)

Lifecycle once green: bridge to paper (tag the TeX claim with `\leanref` pinned to SHA), then
integrate the validated skeleton into the production library. Quote line-counts not time.
Multi-session → write `notes/<topic>_handoff.md`.

## Stage 4 — Aristotle (oracle in Stage 3; critic here) (autonomous, gated)

Aristotle is an ATP, so it plays **two roles** in this loop:

- **Oracle (Stage 3, in-loop).** Called on a *stuck subgoal* via the escalation ladder. Submit
  the isolated subgoal; a returned proof is mechanical and kernel-checked, so **substitute it
  without human escalation** (it still passes `scripts/validate`); a disproof / failure is fed
  back into the prover's prompt. Audit returned proofs with the axiom gate — the oracle must not
  smuggle an `axiom` / `native_decide`.
- **Critic (here, post-green).** Run only for *complex* proofs (long, non-obvious, or central) —
  skip short/mechanical lemmas. Submit the finished, validated proof for:
  1. **Honesty audit** — the *semantic* failures the byte-diff validator cannot see: **F1**, did
     the proof offload the hard part into a helper that *morally restates the target*? **F2**, does
     a step lean on a lemma claimed "known from the literature" that is actually a hallucination?
  2. **Structure** — redundant or mis-ordered steps?
  3. **Simplification** — shorter / cleaner lemma / droppable hypotheses?
  4. **Interpretability** — does it track the paper's argument rather than tactic soup (including
     cleaning up Aristotle's *own* in-loop oracle output)?

**Mechanics** (per `balancedness`), shared by both roles: submission Lean files under
`aristotle/aristotle-in/`, outputs under `aristotle/aristotle-out/`, job metadata in
`aristotle/aristotle-jobs.json`. Under the Stage-3 fan-out this directory is **shared across N
worktrees**, so serialise through a flock'd queue with a per-cycle budget cap and dedup on the
subgoal hash (don't let N provers submit the same goal).
```sh
.venv/bin/python aristotle/check-aristotle.py submit aristotle/aristotle-in/<name>.lean "<note>"
.venv/bin/python aristotle/check-aristotle.py        # poll + download
```
Never print or commit the API key (local `.env`). Apply accepted suggestions, re-verify
(`scripts/validate`), and record what changed in `PROGRESS.md`. A *strategy* proposal from the
**critic** role still escalates to the human (Stage-1 fork); subgoal proofs from the **oracle**
role do not.

## Stage 5 — Close: retrospective, metrics, findings (autonomous)

- Write a LaTeX retrospective to `<seabed>/retrospectives/<date>-<topic>.tex` (sections:
  Setting, What was formalised, Proof strategy, Roadblocks+resolutions, Mathlib-vs-new, Lessons,
  Follow-ups — the Follow-ups feed the next Stage 0). Also record the **Mathlib-vs-new** accounting
  as the scorecard for the Mathlib-first rule (a recurring "new" gap is an
  upstream-to-`lean-common`-or-Mathlib candidate — flag it explicitly as an **upstreaming
  candidate**), and the Aristotle oracle/critic spend for the budget ledger.
- **Findings registry.** Any **closed form / constant / structural fact the proof pinned** is a
  genuine research output, not just a proof detail — append it to `<seabed>/notes/findings.md`
  (one line: the fact, where proved, the `\leanref` SHA) *and* log it in the research repo. This is
  the cross-seabed record of what the formalisation *discovered*, kept separate from the prose retro.
- **Per-cycle metrics record.** Append a structured line to `<seabed>/notes/metrics.md` (or the
  soundings observatory picks most of it up automatically): Lean-LOC delta, `lake-timed` build
  wall-clock, oracle/critic spend, Mathlib-vs-new tally, and the outcome (green / blocked). Tokens
  and context length come from the session transcripts via `soundings` — you don't hand-log those,
  but *do* note anything the transcript can't see (e.g. a scope shock, a rerun from scratch).
- **Overclaim / honesty lint (prose, not just proof).** Before committing, scan the docstrings,
  README "what's proved" table, and the retrospective abstract for claims stronger than the theorem
  actually delivers. The recurring trap: *"upgrades to an unconditional result"* when a hypothesis
  (a cited formula, a conditional RLCT) genuinely remains — **name which hypothesis is discharged
  and which stays**. Also state the **truth-domain / validity caveat** where the honest statement is
  narrower than it looks (e.g. one-sided-in-`a`, `0 ≤ a ≤ 1`). These prose overclaims pass every
  in-proof gate; catch them here (and again in the Review loop).
- Commit proofs + retrospective; mark the survey candidate `✓ Closed`; release every worktree
  (`tide-worktree release …`, one per fan-out branch).
- Append durable Mathlib API / tactic lessons to `CLAUDE.md`/`AGENTS.md`; propose memory updates.
- **Update `<seabed>/formalization.yaml`** (mathlib-initiative schema, v0.3): bump `status.sorry_count`
  / `axioms`, add the new capstone to `status.main_results` and `alignment.statements` (source label →
  Lean decl → module → status), and record any new `fidelity.divergences` (conditional hypotheses,
  weakened assumptions, renames). This is the machine-readable mirror of the README "what's proved"
  table — keep them in sync on every close.

### Blocked-close (the cycle hit a wall, Stage 3 reduced it)

When Stage 3 converts to a reduction instead of full green, close it as a *pinned ceiling*, which
is a first-class outcome — not a failure:

- The retrospective's headline is the **reduction**: the single remaining fact, stated
  self-contained, plus the bridge you *did* land (sorry-free, axiom-clean, up to that one hypothesis).
- Raise a **`DECISION`** on the candidate (status `blocked`) and write the located block to
  `<seabed>/decisions/<topic>-crux.tex` (or `.md`): the exact missing statement, why every route
  reduces to it (cite the negative-results ledger), and a realistic effort estimate.
- In `formalization.yaml`, mark the capstone `blocked` with the named hypothesis; add the ceiling to
  `fidelity.divergences` (proved *conditional on* X).
- **Surface the reduced obstruction to the human** (this is a gate) — a well-pinned wall is often
  the most useful output of a cycle and may itself be an upstreaming target.

---

## The Review loop (async, over already-closed work)

Stage 4's Aristotle critic audits a proof *at close time, in its own cycle*. It does **not**
re-examine the corpus later, and it looks at proofs, not prose. The Review loop is a **separate,
periodic pass over already-green work** — the fidelity/honesty audit the rlct_markov review
exemplifies. Run it on demand (`review this seabed`, `review the Theorem-1 instance files`) or when
a batch of related closes has accumulated; it is not part of a proving cycle.

- **Scope a family, not a file.** Thin instances of one abstract theorem review efficiently as a
  batch: establish the shared caveats once, then the per-file consult only checks the distinguishing
  data (a coefficient, a specific reduction). One consolidated `codex`/Aristotle consult per family.
- **What to check** (independent consult, adversarial): (1) are the **numeric coefficients/constants
  exact** vs the source? (2) is any reduction a **hidden gap** — a helper that morally restates the
  target (F1), or a "known lemma" that's a hallucination (F2)? (3) **prose overclaims** — docstrings /
  README / abstracts claiming more than the theorem's hypotheses deliver ("upgrades to unconditional"
  when a formula is still assumed); name which hypothesis is actually discharged. (4) **truth-domain
  caveats** stated honestly (one-sided domains, validity ranges). (5) do `formalization.yaml`
  `alignment`/`fidelity` entries still match the code?
- **Outputs.** Corrections are usually comment/docstring-only — apply them, re-run `scripts/validate`
  (build must stay green; **no proven mathematics touched**), and confirm with the consult. Write a
  **review retrospective** to `<seabed>/reviews/<date>-<topic>.tex` (the observatory indexes these
  separately from tides). Escalate anything that is a property of the whole construction (not one
  file) to the human. Genuine forward work the review surfaces (e.g. a `K ≍ H` comparability that
  would discharge a shared caveat) becomes a Stage-0 follow-up.

## Notes

- **Concurrency**: isolate each cycle *and each Stage-3 prover subagent* in its own `git worktree`
  (branch `auto/<topic>` for the cycle, `auto/<topic>-p<i>` per prover) so they don't race on imports
  / untracked files / `.lake`. Release every fan-out worktree at Stage 5.
- **Aristotle under fan-out**: `aristotle/aristotle-in|out/` + `aristotle-jobs.json` are shared
  across the prover worktrees. Serialise submissions through a flock'd queue with a per-cycle
  budget cap and dedup on the subgoal hash; it's the expensive tier-4 oracle, call it sparingly.
- **codex invocation**: run from inside the seabed (a git repo). If ever run from a non-repo
  dir, add `--skip-git-repo-check`. codex has web access and will verify arXiv ids (slow, ~min);
  scope web use to final shortlists.
- **Why both retrieval tools** (from a 2026-06-23 head-to-head): theoremsearch returns real,
  long-tail, exact-statement hits with zero hallucination but misses canonical landmarks on
  literal queries; the LLM names canon + judges program-fit but needs web to be id-safe. Hence
  Stage-0 Role-B does query-expansion + judge + canon-backfill, not plain search.
- **Per-seabed loop bookkeeping files** (all under `<seabed>/notes/`, plain append-only):
  `negative-results.md` (disproven routes — written Stage 3, read Stage 2), `findings.md`
  (constants/facts the proofs pinned — Stage 5), `metrics.md` (per-cycle LOC/build/oracle tally —
  Stage 5). Blocked ceilings go in `<seabed>/decisions/<topic>-crux.tex`. Add `.metrics/` to the
  seabed `.gitignore` (local build-timing telemetry, not source).
- **Observatory.** Metrics (tokens, context length, cost proxy, Lean LOC, `lake-timed` build time,
  tides/reviews, oracle spend) are aggregated by the private **soundings** dashboard at
  `~/Documents/soundings` (`make serve`). Tokens/context come from the session transcripts
  automatically; the only thing the loop must actively emit is `lake-timed` build timing and the
  `notes/` bookkeeping above.
