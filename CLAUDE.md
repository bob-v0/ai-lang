# Project context for Claude

Design doc: https://claude.ai/artifact/K7SgF7W4pBoqM1VMtN72iT (the source of truth for decisions).

## What this is

A language where AI writes and reads implementations and humans own or review
policy and specs. Pipeline: human policy + spec → AI synthesis (untrusted) →
implementation + certificate → trusted checker → optimizer + backend.

## Decisions already made

- Implementation language of the compiler and kernel: **Zig**.
- **Stay close to Zig** wherever the language needs a choice Zig already made.
- Integer types: explicit `iN` / `uN` for any N in 0..65535, never inferred from ranges.
  Refinements state meaning; widths state representation.
- Arithmetic as in Zig: overflow on `+ - *` is a proof obligation; `+% -% *%` wrap and
  `+| -| *|` saturate with no obligation.
- Phase 1 has no pointers or references (values only, no aliasing) and one capability type, `Io`.
- Integers are encoded for the solver as mathematical integers plus a range obligation per
  operation (linear integer arithmetic, not bitvectors). Logic: AUFLIA; quantified contract
  clauses restricted to the array property fragment.
- Solvers are untrusted, reached over SMT-LIB2 text, run with `rlimit` (not wall-clock timeouts).
  cvc5 needs `mbqi` enabled to confirm counterexamples when quantified hypotheses are present;
  treat `unknown` as "no answer", not as disagreement.
- Unprovable safety obligations: lenient by default (keep a runtime check, report it), strict
  (reject) as a per-module policy flag.
- Termination (`decreases`) deferred to phase 1.5; the checker lists loops without it.
- Backend in phase 1: LLVM IR as text. MLIR later, if ever.
- Surface syntax follows Zig: `const`/`var`, `fn f(x: T) R` (no `->`), parenthesized `if`/`while`
  conditions, `while (c) : (i = i + 1)`, `[]const T` slices, `[_]T{...}` literals, `and`/`or`/`!`.
  Deviations (all listed in `docs/formal-core.md`): `@intCast(T, e)` takes the type explicitly;
  contract keywords; left-to-right evaluation; `.len` is `u64`.
- Spec mode uses unbounded mathematical integers: no overflow obligations inside contracts.
- `forall` in contracts is restricted to the array property fragment.
- Calls are A-normalized; structs are flattened (no references in phase 1).
- WP asserts are assert-then-assume: later obligations may rely on earlier ones.
- One SMT query per obligation, never one big formula.

## Key files

- `docs/formal-core.md`: grammar, typing, capability rule, expression semantics, WP rules, query format.
- `smt/max/`: hand-written reference queries; the VC generator's first test suite.

## Conventions

- `smt/max/` is the reference for what the VC generator must emit; diff generator output
  against it once the generator exists.
- A counterexample from a loop body or exit query may be spurious (weak invariant). Report it
  as "not provable from the given facts", never as "bug found".
