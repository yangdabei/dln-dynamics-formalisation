---
name: lean-formalisation
description: Principles and workflow for Lean 4 + Mathlib formalisation. Use when starting a new formalisation, adding to an existing one, tagging a primer claim in TeX with \leanref, navigating sri/lean/, deciding what belongs in lean-common, or interpreting the lean field in projects.json.
---

# Lean formalisation at Timaeus

We formalise selected paper claims in Lean 4 + Mathlib. The model and tooling were borrowed from Geoffrey Irving's [`aks`](https://github.com/girving/aks). The first end-to-end project is [`timaeus-research/laplace`](https://github.com/timaeus-research/laplace), which formalises the Laplace asymptotic expansions of the Susceptibility Primer. See `retrospective.tex` and `retrospective2.tex` in that repo for the two staged accounts.

## Why we formalise

We mainly don't go after big theorems. The intent is to close the verification loop on the kind of routine calculations that bottleneck human researcher time:

> *Write LaTeX, formalise the key claim in Lean, present both to a human reviewer who reads the Lean theorem statement to verify the LaTeX claim — taking 20 minutes rather than an afternoon.*

The formalisation is the artefact; the loop is the point. Bias toward small, clearly-stated targets that match a specific equation in a paper, not towards general-purpose libraries.

## Architecture

- **Per-paper repos.** Each paper that gets formalised has its own GitHub repo under `timaeus-research/<short-name>` (sibling to the Overleaf clones). Cloned into `sri/lean/<short-name>/` (gitignored). Independent Lake projects, independent Mathlib version pins.
- **Shared library.** Reusable infrastructure lives in [`timaeus-research/lean-common`](https://github.com/timaeus-research/lean-common). Per-paper repos depend on it via `lakefile.toml`'s `[[require]]`.
- **Manifest.** [`sri/lean/README.md`](../../../lean/README.md) is the manifest of formalisations and the onboarding doc for new contributors.
- **Project link.** `projects.json` carries an optional `lean` array on each project entry, with `[{repo, url, description}]` matching the shape of `gdocs`. Reading project context for a project that has a `lean` field should include reading the formalised theorem signatures (proofs are large and not the point).

## Discipline (aks-style)

- **Zero `sorry`, zero `axiom`, zero `native_decide`** — including in intermediate states. Audit on every commit with `scripts/sorries` (lifted from aks).
- **Skeleton correctness > filling sorries.** A `sorry` with a correct statement is valuable; a `sorry` with a wrong statement actively misleads. When auditing reveals a wrong statement, fix the statement first.
- **`CLAUDE.md` per repo** carries the project-specific Mathlib API references and tactic gotchas accumulated during the formalisation. Each new repo starts from the laplace template and grows its own.
- **Toolchain pinning.** Each repo pins an explicit Lean version in `lean-toolchain` and a matching Mathlib tag in `lakefile.toml`. Different repos may pin different versions.
- **Verify against the primary source.** The paper is the ground truth. Re-read the relevant section before committing to a proof structure.
- **Estimate before attacking a sorry.** Quick estimate of probability of direct proof (e.g. 30%, 60%, 80%). If <50%, factor into intermediate lemmas first.
- **Recognise thrashing.** After 3+ failed approaches to the same goal, stop. Signs: oscillating between approaches, growing helper count without progress, repeated restructuring. Pull in GPT (see below).

## Tagging primer claims with `\leanref`

In a paper, tag a formalised claim with a `\leanref` macro that produces a small unobtrusive marker in the right margin, hyperlinked to the Lean source at a pinned commit SHA. The reference implementation is in `papers/suscprimer/main_lean.tex` — read it for the current macro definition (a TikZ gradient disc), the `\laplaceCommit` SHA pin, and the call-site convention.

Two properties to preserve in any new paper-side adoption:

- **Margin placement** (via `marginnote`) keeps the equation visually clean. An inline superscript like `[Lean: cov_anharmonic_asymptotic]` competes with the math.
- **No link decoration** (`pdfborder={0 0 0}`, `colorlinks=false`) — the symbol shouldn't shout. The link works when clicked; a reader who wants to verify clicks through.

**Centralise the SHA in a single `\newcommand`** so future bumps are one edit. The second argument to `\leanref` (the theorem name) is purely for documentation in the source and does not render — keep it accurate so a reader of the `.tex` can see what's being tagged without compiling.

## The multi-model advice loop

Empirically: GPT-5.5 Pro contributes the strategic skeleton (which approach to take, which hypothesis was missing, which Lean idiom to use); Claude writes all the Lean. Treat the multi-model loop as a structured procedure, not an ad-hoc fallback.

### When to consult

Escalate to GPT when **any** of these hits:

- **Before substantial infrastructure**: about to commit to a generic asymptotic framework, a localisation theorem, or a multi-day Mathlib detour. Ask whether there is a lighter route.
- **Multi-stage plan written**: if you've drafted a 3+ step plan for one project, consult on the *whole plan* before starting Stage 1. Stage 1 is wasted work if Stage 2 reshapes everything.
- **Scope ratio shock**: if your revised line-count or sub-task list is ≥2× your initial assessment, stop and consult. The plan ballooning is the planning failure, not slow progress.
- **Thrashing**: the same goal has resisted 3+ tactical attempts. Almost always means the goal is in the wrong tactical class, not that the maths is hard.
- **Cross-session stuck**: a single sub-goal has burned a full session without converging. The next consult is *not* "how do I fix this step?" but "is my approach right at all?". Architectural pivots beat tactical pushing — the canonical laplace example is the bulk-block `exp(-s_t) = 1 + (exp(-s_t) - 1)` split, which closed a multi-session-stuck proof in four hours after one strategic consult.
- **Theorem statement feels wrong**: counterexample, or hypothesis list looks suspiciously short. Stress-test the statement before investing in a proof.
- **Mechanical bookkeeping pile-up**: 50+ lines of `abs_mul`/`abs_neg`/`show`/`ring`/`simp only` without new mathematical content. GPT very likely has a 3-line idiom for the same thing.

A productive Lean session has **3–5 GPT consultations**. Sessions with 0–1 consultations often have at least one wasted multi-hour detour that a 5-minute consult would have prevented. If you're past the first hour with zero consultations, that itself is a trigger — ask "what would I most benefit from sanity-checking right now?" and send a query.

### How to consult

State the **goal** (Lean syntax + plain-English gloss), the **tactics tried** with their error messages, the **surrounding lemmas** (paste relevant source), and a **specific question** — not "help me prove this", but "is this provable as stated, or do I need a stronger hypothesis?", "what tactical class is this?", "is there a 3-line idiom for this bookkeeping?", or — when an approach has failed for a session — "produce a counterexample if my current plan can't work". Counterexamples were load-bearing on laplace: an explicit witness ($\phi(w) = w\cdot|w|^3$) ruled out a multi-session proof plan in minutes by showing the existing hypothesis was insufficient. The query template:

```
Goal: <Lean statement>; in English: <one-line gloss>.
Surrounding lemmas: <paste>.
Tried: `<tactic>` → <error>; `<tactic>` → <error>.
Question: <specific question>.
```

Save the response verbatim to `gpt_responses/<topic>.md` (`strategy_*`, `bridge_*`, `debug_*`). These are not throwaway — subsequent sessions read them to recover the strategic state. The diagnosis ("this is a rational identity, not a linear combination") is the load-bearing part; the recipe Lean code is illustrative. **Never paste GPT code without compiling it locally.**

When the move works, promote any reusable Mathlib gotcha to the repo's `CLAUDE.md` so the next session inherits the playbook.

GPT access is via the `timaeus-research` skill's GPT-5.5 Pro setup (or current reasoning model).

## Multi-session continuity

A formalisation that runs for more than a day will span multiple Claude sessions, with context resets in between. Continuity is preserved by three durable artefacts, in increasing order of importance:

- **Per-repo `CLAUDE.md`** — Mathlib API references and tactic gotchas. Grows incrementally; future sessions inherit it on startup.
- **`gpt_responses/`** — strategic and tactical consults, preserved verbatim. Subsequent sessions grep these to recover strategic state.
- **Handoff documents** in `notes/<topic>_handoff.md` — written at session end when a sub-project will continue across a context reset. ~300 lines, ~30 min to write, ~10 min for the next session to read.

A handoff document covers, in this order: a one-paragraph TL;DR; what's proven (in dependency order); what remains (with proof sketches for each remaining sorry); known patterns and friction points encountered this session; the recommended attack order for the next session. The laplace project produced three handoffs (`laplace_cov_handoff.md`, `sharp_track_session_handoff.md`, `cov2_explicit_session_handoff.md`); each was the most-read document at the start of the next session. Proof bodies the handoffs describe have been rewritten or deleted; the handoffs are still accurate at the level of architecture and remaining-work.

When you reach a session boundary on a multi-session project, write the handoff before stopping. When you start a session on a project with existing handoffs, read the most recent one first. **Auto-memory complements but doesn't replace handoffs**: auto-memory captures *what state the branch is in*; handoffs capture *how to resume the actual work*. Both matter; neither is sufficient alone.

## Patterns and pitfalls

Recurring patterns observed across projects, worth flagging early on a new one.

### Resist over-engineering

Claude's defaults pull toward general infrastructure. On laplace, the 532-line `TailBound.lean` and 164-line `Localisation.lean` were built before the GPT strategy memo and turned out essentially unused. **Do a gap analysis against the target theorem first.** Build the minimum needed; factor up to `lean-common` only on a *second* use, not in anticipation of one.

### Specialise early

When a result is needed for `n = 0, 1, 2, 3`, prove four specialised lemmas. A generic parity framework for arbitrary `n` is overkill if the project never instantiates it elsewhere. Generic statements compound across many uses; for a single-target proof, they tax.

### Templates beat custom proofs

When a tactical pattern fires 3+ times in a project — e.g. "case-split on local vs tail region, build a `Glocal + Gtail` majorant, integrate Gaussian-poly envelopes" — name it, write it once carefully (with a GPT consult if needed), and copy-paste-substitute every subsequent use. On laplace, the local-plus-tail integral template was reused ~50 times across the explicit track at ~30 lines per reuse, all reliable. Custom proofs at the same junctures (the corrected-bracket bound, the symmetrisation attempt) were the ones that nearly broke the project.

### Hypothesis structures should `extend`

When a hypothesis structure may need additional fields later (a quintic remainder bound on top of a quartic one, a sixth-moment integrability on top of a fourth-moment one), set it up with the intent that future versions `extend` it: `structure FooQuintic extends FooTensor where ...`. Callers that need the weaker form use `h.toFooTensor`; callers that need the stronger form take the new structure. Without `extends`, mid-stream hypothesis bumps require chasing every callsite across the file. The laplace project bumped twice mid-stream (`PotentialJetApprox` → `PotentialQuinticApprox`, `ObservableTensorApprox` → `ObservableQuinticApprox`); both bumps were nearly painless because of `extends` discipline.

### The hypothesis is part of the theorem

A theorem with the wrong hypothesis is not "almost done". On laplace the discriminant condition $\alpha^2 < 3\lambda\gamma$ was missing from the original statement; without it the theorem is false. State the hypothesis as a known unknown at the start, and resolve it before proving anything.

### "Easy to see in papers" is a red flag

When a paper says "follows by Wick" or "easy calculation shows", expect the formalisation to surface a gap that the paper glosses over. Write out the full calculation by hand (or by GPT) before formalising.

### Don't give time estimates

**Do not quote wall-clock time, hours, or days for Lean work.** Empirically the model is bad at this — initial estimates routinely undershoot by 4–10× because they account only for the mathematical content and not for Lean idiom friction. Quote **line counts** (more accurate) and **sub-task lists** (concrete and reviewable) instead. Cost calibration: ~50% line retention rate from gross output to final (expect to write ~2× the final line count), and one strategic GPT consultation per ~1000 retained lines pays for itself many times over. If the user asks "how long will this take?", decline and offer line counts and sub-task counts instead.

This rule is structural, not a guideline to be argued with — the time estimates have a systematic underestimation bias that has burned multiple sessions.

### Don't suggest stopping for the session

**Do not offer "stop here for the session" as a multiple-choice option** to the user, and do not unilaterally pause Lean work after a clean commit because "this is a natural pause point". The user controls session length. Your job is to keep producing committed progress until interrupted, redirected, or genuinely blocked on user input.

What counts as genuinely blocked on user input:

- A **strategic fork** the user has not yet chosen between (e.g. weak vs sharp track, two equally valid hypothesis packages). Then ask the user the fork question, but **do not** also offer "stop now" as a third option.
- A **scope ratio shock** (per the consult trigger above): consult GPT first, then surface the revised plan to the user.
- An **ambiguous instruction** where guessing wrong would waste a substantial commit.

What does *not* count: "lots committed already in this session", "the next step is hard", "natural commit boundary". When you reach a genuine fork, present **only the substantive options**, not "or stop". The default after the user resolves the fork is to continue working.

This rule is also structural: empirically, offering "stop here" leaks a bias toward shorter sessions that does not match what the user wants from auto-mode formalisation work.

## Project lifecycle

A typical formalisation goes through four phases:

1. **Scaffolding** (~30 min). Bootstrap from the laplace template: lakefile, lean-toolchain, scripts, CLAUDE.md, .github/workflows. Get `lake build` green on an empty stub.
2. **Skeleton** (½–1 day). Write all the theorem **statements** with `sorry` stubs, get them to typecheck. Statement correctness is the milestone, not proof completion. *A skeleton with correct statements and only `sorry`s is far more valuable than a partial proof of the wrong statement.* (Geoffrey's aks discipline, adopted directly.)
3. **Filling** (most of the time). Replace `sorry`s with proofs, top-down or bottom-up. Run `scripts/sorries` before every commit. When stuck, the multi-model loop above.
4. **Bridge and tag** (~½ day). Connect the formal proof to the human-readable form (the bridge step is often the hardest). Tag the corresponding TeX claim with `\leanref` pinned to a SHA.

Discipline note: at every commit the file builds and `scripts/sorries` reports zero unfilled occurrences in *production* files (intermediate work-in-progress files may have stubs but should not be committed). This rule is non-negotiable per the aks playbook.

## Adding a new formalisation

1. **Create the GitHub repo** under `timaeus-research/<short-name>`. Copy the laplace scaffold:
   - `lakefile.toml` with `[[require]]` on Mathlib at a tag, and optionally on `lean-common`.
   - `lean-toolchain` matching.
   - `scripts/sorries`, `scripts/lean-search` (lifted from `lean-common/scripts/`).
   - `CLAUDE.md` from the laplace template, edited for the new project's goal.
   - `.github/workflows/lean_action_ci.yml` for CI.
2. **Clone into `sri/lean/<short-name>/`.**
3. **Add a `lean` entry** to the relevant project in `projects.json`:
   ```json
   "lean": [
     {"repo": "<short-name>",
      "url": "https://github.com/timaeus-research/<short-name>",
      "description": "Brief description of what's formalised"}
   ]
   ```
   Create a new project entry if none fits.
4. **Update `sri/lean/README.md`** with a row in the Layout table.
5. **Tag the corresponding TeX claim** with `\leanref` pinned to a SHA, once the theorem is committed.
6. **`scripts/sorries` clean** before every commit; `lake build` clean before every push.

## When to factor up to `lean-common`

A piece belongs in `lean-common` when:

- It is genuinely general (not specific to one potential or one paper's setup).
- A second project would benefit from it.
- Its statement is stable (not likely to be reshaped by an in-progress proof).

Pre-emptive factoring is its own form of over-engineering — it tends to produce general statements that don't fit either project. Better to duplicate once and factor on the second use.

## Reference material

- [`skills/lean-references/`](../lean-references/README.md) — vendored Mathlib **naming, style, tactic, and proof-technique** reference library (from `cameronfreer/lean4-skills`, MIT). Consult `mathlib-style.md` before naming any new declaration; the tactics/proof-golfing/refactoring notes on a stuck or finished proof. This is the convention source of truth — cite it, don't duplicate it.
- [`sri/lean/README.md`](../../../lean/README.md) — the operational manifest and setup instructions.
- [`sri/lean/laplace/CLAUDE.md`](../../../lean/laplace/CLAUDE.md) — the canonical per-repo `CLAUDE.md` template, with Mathlib API references and tactic gotchas accumulated during the laplace formalisation.
- [`sri/lean/laplace/retrospective.tex`](../../../lean/laplace/retrospective.tex), [`sri/lean/laplace/retrospective2.tex`](../../../lean/laplace/retrospective2.tex) — first-morning and multi-week retrospectives on the laplace project. Worth reading at the start of a new formalisation; the strategic patterns recur.
- [`sri/lean/laplace/gpt_responses/`](../../../lean/laplace/gpt_responses/) — preserved GPT consultations. Worth grepping when starting a new formalisation, since the strategic patterns recur.
- [Geoffrey Irving's `aks` repository](https://github.com/girving/aks) — the upstream model. Worth reading for the project layout and the `scripts/sorries` discipline.
