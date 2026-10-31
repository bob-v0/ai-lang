# AI-first programming language (working title)

A language designed for AI as both writer and reader. Humans own or review the
capability policy and the specs; they never review implementations. The AI acts
as an untrusted compiler pass, and only output that a small trusted checker
accepts reaches the backend.

Goals: fewer tokens per verified-correct change, security by construction, and
performance from precise semantics.

Design doc: https://claude.ai/artifact/K7SgF7W4pBoqM1VMtN72iT

## Status

Phase 1, step 3 done: the verification conditions for the `max` example were
hand-written in SMT-LIB2 and checked with Z3 and cvc5. All obligations prove;
every deliberately broken variant yields the expected counterexample. See
`smt/max/results.txt`.

Next: the formal core (grammar, typing rules, weakest-precondition rules), then
the Zig implementation of the kernel.

## Layout

| Path | What |
| --- | --- |
| `smt/max/gen.py` | Writes one SMT-LIB2 query per obligation for `max` and its broken variants |
| `smt/max/run.py` | Runs every query through Z3 and cvc5, then a seed/shuffle determinism check |
| `smt/max/results.txt` | Output of the last run |

## Running the SMT experiment

```sh
pip install z3-solver cvc5
cd smt/max
python3 gen.py out
python3 run.py out
```
