# lean-references — Lean 4 / Mathlib convention & technique library

Shared, read-only reference material cited by the formalisation skills
(`auto-loop`, `auto-formalise`, `lean-formalisation`) and by each project's `CLAUDE.md`. Single
source of truth — do **not** duplicate these into per-project repos; cite by
path instead, e.g.

> See `../../skills/lean-references/mathlib-style.md` for naming.

These are **conventions and technique notes**, not an orchestration engine. The
loop that drives proving lives in `auto-loop`; these docs are what a prover
subagent consults on a subgoal.

## Provenance

Vendored verbatim from [`cameronfreer/lean4-skills`](https://github.com/cameronfreer/lean4-skills)
(`plugins/lean4/skills/lean4/references/`), MIT-licensed — see
[`LICENSE.upstream`](LICENSE.upstream). Only the convention/technique/reference
subset was taken; the skill-engine, host-CLI, and orchestration docs were
deliberately left behind because `auto-loop` already covers that layer. Update by
re-cloning upstream and re-copying the files listed below.

## Index

### Conventions & style
- [`mathlib-style.md`](mathlib-style.md) — Mathlib naming conventions and coding style. **Start here for any new declaration.**
- [`mathlib-guide.md`](mathlib-guide.md) — using Mathlib: structures, typeclasses, where things live.
- [`lean-phrasebook.md`](lean-phrasebook.md) — common Lean idioms / how to say X.

### Tactics
- [`tactic-patterns.md`](tactic-patterns.md) — when to reach for which tactic.
- [`tactics-reference.md`](tactics-reference.md) — per-tactic reference.
- [`simp-reference.md`](simp-reference.md) — `simp` set discipline and lemma tagging.
- [`grind-tactic.md`](grind-tactic.md) — the `grind` tactic.
- [`calc-patterns.md`](calc-patterns.md) — `calc` block patterns.

### Proof technique
- [`proof-templates.md`](proof-templates.md) — skeleton shapes for common goals.
- [`proof-golfing.md`](proof-golfing.md) / [`proof-golfing-patterns.md`](proof-golfing-patterns.md) — condensing finished proofs.
- [`proof-refactoring.md`](proof-refactoring.md) — extracting helpers, restructuring.
- [`proof-simplification.md`](proof-simplification.md) — simplifying proof strategies.
- [`sorry-filling.md`](sorry-filling.md) — disciplined `sorry` discharge (matches our skeleton-first rule).
- [`axiom-elimination.md`](axiom-elimination.md) — removing axioms / keeping `#print axioms` trusted-only.

### Debugging & performance
- [`compilation-errors.md`](compilation-errors.md) — reading and fixing compiler errors.
- [`compiler-guided-repair.md`](compiler-guided-repair.md) — error-driven repair loop.
- [`instance-pollution.md`](instance-pollution.md) — typeclass instance conflicts.
- [`performance-optimization.md`](performance-optimization.md) — elaboration/build performance.

### Domain
- [`domain-patterns.md`](domain-patterns.md) — patterns by mathematical domain.
- [`measure-theory.md`](measure-theory.md) — measure theory specifics (analysis-heavy targets).

### LSP / MCP inner loop
- [`lean-lsp-tools-api.md`](lean-lsp-tools-api.md) — the LSP/MCP tool surface (maps to our `lean-lsp-mcp` inner loop; tool names may differ slightly).
- [`lean-lsp-server.md`](lean-lsp-server.md) — LSP server behaviour.
