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

## Conventions

- `smt/max/` is the reference for what the VC generator must emit; diff generator output
  against it once the generator exists.
- A counterexample from a loop body or exit query may be spurious (weak invariant). Report it
  as "not provable from the given facts", never as "bug found".
