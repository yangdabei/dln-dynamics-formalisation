---
name: tide-pick
description: Survey the SRI research portfolio for Tide-loop candidates, present 5-6 ranked options with a recommendation, and (after a brief wait) auto-proceed with the top pick by handing off to the `tide` skill. Use when the user asks to pick / select / find a tide ("pick a tide", "find something to formalise", "what should I tide on next", "run the tide loop"), or when the next step is unknown and the user wants the system to choose. Do NOT use when the user has already named a direction — invoke `tide` directly with that direction.
---

# tide-pick — auto-selection of the next Tide

This skill closes a gap in the `tide` skill, which assumes the **direction** is given as input. `tide-pick` chooses the direction.

It runs in three phases:

1. **Survey** — walk the SRI portfolio (Lean repos, papers, prior tide-logs, retrospective follow-ups) and assemble 5–6 candidates that satisfy the Tide-shape heuristic.
2. **Present + recommend** — write the survey to `projects/automation/log/<YYYY-MM-DD>-tide-candidates-survey.md`, post a digest in chat, and recommend a top pick with a one-line reason.
3. **Auto-proceed** — set a timer; if the user has not picked an alternative within ~4 minutes, hand off to the `tide` skill on the top recommendation. (User redirections at any time short-circuit the timer.)

## Auto mode

If the user invokes this skill with an `auto` modifier (e.g. *"Choose a tide auto"*, *"pick a tide, auto mode"*, *"run the tide loop auto"*), the user wants the entire Tide loop to keep running across tides without stopping. **Before doing anything else**, invoke the `loop` skill exactly once:

```
/loop 15m Continue with what you think best, don't stop, it's fine if the session fills up the context
```

Then proceed with Phase 1 normally.

**The loop is a fallback heartbeat, not the driver.** In auto mode, the *default* between actions is to continue immediately to the next best action — close out the current Tide and roll straight into the next `tide-pick` → `tide` → retrospective cycle without waiting. The 15-minute `/loop` wakeup is a safety net that re-engages you if you somehow stop or stall; it is **not** a pacing signal and you should not idle for it. If you ever find yourself at a natural stopping point in auto mode (a survey written, a Tide closed, a retrospective committed), the correct next action is to *immediately* start the next step, not to wait for the loop to fire.

Only invoke `/loop` once per session. If a loop is already running, skip this step.

## When to use this skill

Trigger phrases the user might say:

- *"pick a tide"*, *"select a tide"*, *"choose a tide"*
- *"find something to formalise"*, *"what should I tide on next?"*
- *"run the tide loop"* (when no direction is named)
- *"survey for tide candidates"*

Do **not** trigger when the user has already named a direction (e.g. *"tide on the 2D pure-quartic case"*, *"let's formalise κ₃ for the harmonic Gibbs"*) — those go straight to the `tide` skill.

## The Tide-shape heuristic (unchanged)

A candidate qualifies if:

- it is a **single statement**, not a programme;
- it has a **closed-form expectation** where possible (specific potential, scalar coefficients);
- it is **reachable from existing seabed** (or with a small fresh seabed);
- it is **amenable to numerical sanity** before formalisation.

Reject candidates that are programmes ("formalise the grammar paper"), that don't pin a specific potential or observable, or that require seabed deltas larger than a single Tide step can absorb.

## Phase 1 — Survey

Pull from the following sources, in order:

1. **Reuse a recent survey if one exists.** Look for the most recent
   `projects/automation/log/<YYYY-MM-DD>-tide-candidates-survey.md`. If
   it is less than ~7 days old, **refresh** it rather than redoing the
   survey from scratch.

   The primary signals on each candidate heading are:
   - `✓ Closed` (plus a `**Closed by:** ...` line) — written by the
     `tide` skill at the end of its run when the headline statement
     was fully formalised.
   - `🟡 In progress` (plus a `**Claimed by:** ...` line) — written
     when a Tide picks the candidate, before handing off. See "Phase 3
     — Claim before handoff" below.

   Trust those annotations; they're cheaper and more authoritative
   than re-scanning every tide-log. Only re-scan tide-logs and
   retrospectives when the most recent survey is older than the most
   recent `<seabed>/retrospectives/*.tex` file (i.e., a Tide has
   landed since the survey was written and may not have been annotated
   yet).

   Treat `🟡 In progress` candidates the same as `✓ Closed` for
   recommendation purposes (don't propose them again); but surface
   them visibly in the chat digest so the user can see a parallel
   session is on it. If a `🟡 In progress` annotation is older than
   ~24 hours and no closure has appeared, treat as stale and re-rank
   into the available pool — note the staleness in the digest.

   When refreshing, open the new survey with a `## Status of the
   previous survey` table mapping each prior item to ✓ / partial /
   pending / decomposed. The 6 May survey
   (`projects/automation/log/2026-05-06-tide-candidates-survey.md`) is
   the exemplar; that table made the survey's value as a delta against
   its predecessor immediately visible to the next reader. Add new
   follow-ups surfaced by recent tide retrospectives, drop or merge
   stale ones, and re-rank.

2. **Per-project tide-log follow-ups.** For each project with a `lean`
   field in `projects.json` (currently `primer` → `laplace`,
   `patterning` → `threepoint`), harvest from two locations:
   - **New (canonical):** walk `lean/<seabed>/tide-log/*.md` — per-tide
     process logs now live alongside the proofs they cover. Open each
     and harvest its `### Suggested follow-ups` section.
   - **Legacy:** walk `projects/<project>/tide-log/*.md` — historical
     entries from before tide-logs moved into the seabed repo. Same
     harvest pattern. Stops being load-bearing as legacy entries age
     out of the ~6-month relevance window.
   - **Retrospectives:** open every retrospective in
     `lean/<seabed>/retrospectives/*.tex` and harvest its
     `\section{Follow-ups}`.
   These are explicit candidates left behind by prior tides. They are
   typically the highest-quality entries because someone has already
   thought about them.

3. **Active in-flight tide branches and worktrees.** Run
   `git -C <seabed> branch --list 'tide/*'` for each seabed, or use
   `.claude/skills/tide/tide-worktree list` to see all active Tide
   worktrees across all repos at once. Note anything unmerged. Either
   (a) a follow-up makes more sense after the in-flight branch lands,
   in which case skip it; or (b) the in-flight branch is abandoned and
   someone should pick up the thread (a candidate of its own).

4. **Other Timaeus papers without a Lean home yet.** Skim
   `papers.json` for papers whose headline calculations are
   tide-shaped — single specific computations against a specific
   measure or potential, with closed-form answers. Examples surfaced by
   the 2 May survey: `pas` (programs as singularities), `sustm`
   (susceptibilities for Turing machines), `qd` (LLC bounds), the
   grammar paper's resolution examples. These usually require a fresh
   seabed and so cost more, but they extend the formalised territory
   into a new project rather than deepening it.

5. **Don't drown in process.** If reading every retrospective and
   tide-log fully would take more than ~5 minutes, sample: the most
   recent retrospective per seabed, plus the 2-3 most recent tide-logs
   per project. Past surveys have shown that the top candidates cluster
   around recent work; old follow-ups that haven't been tackled in
   ~6 months are usually stale.

After harvesting, **rank**. Heuristic order:

1. Mechanical extensions of recent tides (smallest infrastructure
   delta, often single-day wins). *Strict-improvement candidates* left
   behind in retrospective Follow-ups are particularly valuable
   here — the deliberation has already happened, and the seabed is
   fresh in the cache. Examples: Tide 9's "affine-observable κ₃" left
   for Tide 9+1, Tide 10's "cross-susceptibility-derivative-vanishes
   for harmonic" left for Tide 10+1.
2. Refactors that have crossed the cost-positive threshold (e.g. the
   "extract separable-potential factorisation" lesson noted at the
   end of the 2D pure-quartic retrospective).
3. Fresh-seabed tides into adjacent papers (higher upfront cost,
   higher value when they land).

The survey on disk can carry **8–12 candidates organised by category**
(see the 6 May exemplar's A/B/C/D/E/F categorisation: mechanical
extensions, bounded-prior continuations, threepoint extensions, sustm
extensions, new-repo seabeds, cross-repo bridges). The chat digest in
Phase 2 distils to **3–6 highlighted picks** organised by user
appetite, not by category. The full survey is the durable record;
the chat digest is the decision aid.

## Phase 2 — Present + recommend

Write the survey to
`projects/automation/log/<YYYY-MM-DD>-tide-candidates-survey.md` using
this layout (mirroring the 2 May exemplar):

```markdown
---
date: <YYYY-MM-DD>
source: tide-pick
author: <name> (with Claude Opus 4.7)
---

# Survey of Tide-loop candidates across the SRI

<one paragraph: what's already been done since the last survey, what's
the next-step landscape>

## Candidates

### 1. <project>: <one-line statement title>
**Statement (informal).** <math statement>
**Seabed.** <repo + commit or branch>
**Why tide-shaped.** <one paragraph>
**Estimated size.** <line range>

### 2. ...

## Recommendation order (heuristic)

For a *single* immediate excursion: <#>. <one-line reason>.
For a *quick warmup*: <#>. <one-line reason>.
For *strategic mid-term*: <#>.
For *long-term ambition*: <#>.

## Items not surveyed
<bullet list of things considered and explicitly skipped, with reason>
```

Then in chat, post a digest:

- A numbered list of the candidates (one line each).
- Your top recommendation with a one-sentence rationale.
- The auto-proceed notice (see Phase 3).

Pointer to the full survey on disk: include the file path so the user
can read it before deciding.

### Structuring the digest by user appetite

When several candidates are roughly co-equal in technical merit, group
them in the digest by the *kind* of session the user might be in
rather than by category. Categories that have worked: *quick capstone*
(close out the narrative of the most recent tide; usually a
strict-improvement or follow-up theorem ~50-100 lines), *strategic
refactor* (high-yield infrastructure that pays off across many future
tides; ~300-600 lines), *new-repo expansion* (first foothold in a
research area not yet formalised; ~200-400 lines), *programme
continuation* (next step in an in-flight precursor sequence like
the grammar paper precursors), *process polish* (`\leanref` tagging,
hygiene fixes, documentation). The user picks based on what they want
that day, not on what is globally optimal.

**Lead the digest with the option that closes out today's narrative.**
The most natural-feeling next tide is often a strict-improvement or
capstone of the very last one. If today's tide left a clean follow-up
in its retrospective's Follow-ups section, surface that first; the
seabed is fresh in cache and the proof template is right there.

### Process tides as candidates

The survey may include process / hygiene work that's not strictly a
Lean tide: `\leanref`-tagging a paper with newly formalised theorems,
pushing a local-only Lean repo to GitHub, promoting a helper to
`lean-common`. List these in the survey under their own bullet but
**do not auto-proceed on them in Phase 3** — only Lean-formalisation
candidates qualify for hand-off to the `tide` skill, since process
work doesn't fit the deliberation-and-formalisation loop. If the
user picks a process candidate, do it directly without invoking
`tide`.

## Phase 3 — Claim before handoff, then auto-proceed

### Claim before handoff

Whenever a tide is about to be picked from the survey — whether by
auto-proceed timer firing on the top recommendation, by explicit user
selection, or by a follow-up session resuming work — **edit the
survey to mark the chosen candidate as `🟡 In progress` before
handing off to the `tide` skill** (or before doing the work directly
in the case of a process candidate). Annotate the heading inline:

```markdown
### G2. Cross-susceptibility derivative vanishes for harmonic 🟡 In progress
**Claimed by:** Claude Opus 4.7 (1M ctx) on 2026-05-06T20:14:00Z;
expected branch `tide/cross-susc-deriv-harmonic`.
```

Commit that survey edit immediately (a one-line commit `automation:
claim <candidate> on <date>`) before invoking `tide`. The commit makes
the claim durable and visible to other concurrent sessions reading the
survey from disk.

If two concurrent `tide-pick` runs would race on the same top
candidate, the second to commit will see the first's `🟡 In progress`
annotation on `git pull` and should re-rank to the next-best option
rather than duplicating the work. The annotation is *advisory*, not a
lock — but it is the cheapest mechanism that survives context resets,
process crashes, and worktree branch-toggling.

The `tide` skill is responsible for *replacing* the `🟡 In progress`
annotation with `✓ Closed` (or `~ Partial`, etc.) at end-of-run. Do
not stack annotations.

If a Tide is invoked from a user-named direction with no survey
ancestry (i.e. the user said "let's tide on X", not "pick a tide"),
no claim is necessary — the candidate isn't in any survey. The
`tide` skill's "Close out" step still skips because there's no survey
to update.

### Auto-proceed

Schedule a wakeup at **240 seconds** (4 minutes; just under the prompt
cache TTL so the next turn stays warm) using `ScheduleWakeup`:

- `delaySeconds: 240`
- `reason`: e.g. *"Tide-pick auto-proceed timer; will hand off to the
  `tide` skill on candidate N if no user redirection arrives."*
- `prompt`: a self-contained instruction such as *"Resume tide-pick:
  scan the conversation since the survey was posted. If the user has
  named a different candidate, invoke `tide` on that one. Otherwise
  invoke `tide` on the top recommendation from
  `<survey-file-path>`."*

When the wakeup fires, do exactly that:

- If the user has redirected (named a different candidate, asked to
  wait, asked for more candidates, or otherwise interrupted), follow
  the redirection. Do not auto-proceed against an explicit user
  instruction.
- Otherwise, invoke the `tide` skill via the `Skill` tool with `args`
  set to the verbatim direction text for the top candidate (the
  candidate's `### N.` heading plus the informal statement and seabed
  pointer is enough — the `tide` skill knows what to do with it).

If the user has clearly engaged with the candidates but has not
finalised a pick (e.g. they asked clarifying questions but haven't
selected), **do not auto-proceed** — they're in the loop, just not
done. Reschedule a single follow-up wakeup at 240s and try again.

## Logging discipline

The survey itself is the durable artefact of this skill. Per Tide
infrastructure conventions:

- Survey lives at
  `projects/automation/log/<YYYY-MM-DD>-tide-candidates-survey.md`
  (cross-project surveys live under `projects/automation/`, not under
  any single research project).
- Commit the survey to the SRI repo with a one-line commit message
  (`automation: tide-candidates survey for <date>`) before moving to
  Phase 3. This way the survey is durable even if Phase 3 stalls.

## Edge cases

- **No candidates found** (very unlikely given the size of the
  portfolio). Surface this to the user with the harvest log so they can
  point at something the survey missed. Don't fabricate candidates.

- **All top candidates are completed-since-last-survey.** Report this
  honestly — it means the previous survey did its job and the
  shoreline has advanced. Then re-run the harvest from scratch
  (skipping Phase 1 step 1's reuse path).

- **Concurrent agents.** If multiple `tide-pick` invocations have
  fired in parallel and produced overlapping surveys, reconcile by
  keeping the most recent, deleting the duplicate. (Don't push to
  remote until reconciled.)

- **User asks to pick again later.** That's fine: the survey on disk
  is the durable artefact. They re-invoke `tide-pick` and Phase 1's
  reuse path picks it up.

## What this skill is not

- **Not** a long-term planner. It picks one Tide step. The output of
  the next Tide retrospective will surface the candidates for the
  one after that.
- **Not** a deliberation engine. It does not consult GPT-5.5 Pro or
  rank candidates with multi-model voting. The deliberation happens
  inside the `tide` skill (Step 2), once the direction is fixed.
- **Not** a substitute for human direction-setting. When the user has
  a specific goal in mind, they should name it; this skill is for the
  case where they haven't.

## References

- [`tide` skill](../tide/SKILL.md) — the loop this hands off to.
- [Tide-shape heuristic](../tide/SKILL.md#what-minimal-means-here) —
  the standard for what counts as a Tide-shaped candidate.
- Two cross-project surveys to emulate:
  - `projects/automation/log/2026-05-02-tide-candidates-survey.md` —
    the original (5 candidates, no predecessor).
  - `projects/automation/log/2026-05-06-tide-candidates-survey.md` —
    the refresh-mode follow-up (12 candidates organised by category,
    with a `## Status of the May survey` table mapping each prior
    item to ✓/partial/pending).
