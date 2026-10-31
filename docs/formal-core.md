# Phase 1 formal core

Status: draft 1. Defines the phase-1 surface syntax, the static semantics, and the
verification-condition (VC) generation the kernel performs. The hand-written queries in
`smt/max/` are the reference output for the `max` example (Appendix A).

Design rule throughout: **where Zig has already made a choice, take Zig's.** Deviations are
marked *Deviation* with the reason.

---

## 1. Syntax

### 1.1 Lexical

- Identifiers: `[A-Za-z_][A-Za-z0-9_]*`, excluding keywords.
- Keywords: `fn const var if else while return and or true false void bool struct
  requires ensures invariant where forall in result Io`.
- Integer types: `i` or `u` followed by a decimal width `0..65535` (`u0`, `i7`, `u64`, `u1000`).
- Integer literals: decimal, `0x`, `0o`, `0b`, with `_` separators (as in Zig).
- Comments: none in the AI-facing form. The parser rejects them. (Intent lives in contracts.)

### 1.2 Grammar (EBNF)

```ebnf
module      = { decl } ;
decl        = struct_decl | fn_decl ;

struct_decl = "const" IDENT "=" "struct" "{" field { "," field } [ "," ] "}"
              [ "where" spec_expr ] ";" ;
field       = IDENT ":" type ;

fn_decl     = "fn" IDENT "(" [ param { "," param } ] ")" ret_type
              { "requires" spec_expr } { "ensures" spec_expr } block ;
param       = IDENT ":" type ;
ret_type    = type | "void" ;

type        = INT_TYPE | "bool" | "[]" "const" type | IDENT | "Io" ;

block       = "{" { stmt } "}" ;
stmt        = ( "const" | "var" ) IDENT ":" type "=" expr ";"
            | IDENT "=" expr ";"
            | "if" "(" expr ")" block [ "else" ( block | if_stmt ) ]
            | "while" "(" expr ")" [ ":" "(" IDENT "=" expr ")" ]
                  { "invariant" spec_expr } block
            | "return" [ expr ] ";"
            | call ";" ;
if_stmt     = "if" "(" expr ")" block [ "else" ( block | if_stmt ) ] ;

expr        = or_expr ;
or_expr     = and_expr { "or" and_expr } ;
and_expr    = cmp_expr { "and" cmp_expr } ;
cmp_expr    = add_expr [ cmp_op add_expr ] ;          (* non-associative, as in Zig *)
cmp_op      = "==" | "!=" | "<" | "<=" | ">" | ">=" ;
add_expr    = mul_expr { add_op mul_expr } ;
add_op      = "+" | "-" | "+%" | "-%" | "+|" | "-|" ;
mul_expr    = unary { mul_op unary } ;
mul_op      = "*" | "/" | "%" | "*%" | "*|" ;
unary       = ( "-" | "!" ) unary | postfix ;
postfix     = primary { "[" expr "]" | "." IDENT | "." "len" } ;
primary     = INT_LIT | "true" | "false" | IDENT | "(" expr ")"
            | call
            | IDENT "{" "." IDENT "=" expr { "," "." IDENT "=" expr } [ "," ] "}"
            | "[" "_" "]" type "{" [ expr { "," expr } [ "," ] ] "}"
            | builtin ;
call        = IDENT "(" [ expr { "," expr } ] ")"
            | IDENT "." IDENT "(" [ expr { "," expr } ] ")" ;  (* Io builtins only *)
builtin     = "@intCast" "(" type "," expr ")"
            | "@divTrunc" "(" expr "," expr ")"
            | "@rem" "(" expr "," expr ")" ;

spec_expr   = expr                                       (* plus the two spec-only forms: *)
            | "forall" IDENT "in" add_expr ".." add_expr ":" spec_expr
            | "result" ;
```

Notes:

- `const` / `var` mean what they mean in Zig. Parameters are immutable.
- `..` is half-open, as in Zig's `for (0..n)`.
- Shadowing is a compile error, as in Zig.
- *Deviation:* `@intCast(T, e)` takes the target type explicitly. Modern Zig infers it from the
  result location; an explicit type keeps typing local (one expression, one type, no context
  needed), which is the locality criterion.
- *Deviation:* Zig has no contracts; `requires`, `ensures`, `invariant`, `where`, `forall` and
  `result` are additions.

### 1.3 Example

```zig
fn max(xs: []const i32) i32
    requires xs.len > 0
    ensures forall k in 0..xs.len: xs[k] <= result
{
    var m: i32 = xs[0];
    var i: u64 = 1;
    while (i < xs.len) : (i = i + 1)
        invariant forall k in 0..i: xs[k] <= m
    {
        if (xs[i] > m) {
            m = xs[i];
        }
    }
    return m;
}

fn main(io: Io) void {
    io.print_int(max([_]i32{ 3, 1, 2 }));
}
```

The single invariant is sufficient: the `inv2_only` variant in `smt/max/` proves every
obligation without `1 <= i` or `i <= xs.len`.

---

## 2. Static semantics

### 2.1 Types

```
T ::= int(s, n)        s ∈ {signed, unsigned}, n ∈ 0..65535      (iN, uN)
    | bool | void | slice(T) | struct S | Io
    | comptime_int     type of integer literals before coercion
    | int              unbounded mathematical integer, spec mode only
```

`range(iN) = [-2^(n-1), 2^(n-1) - 1]`, `range(uN) = [0, 2^n - 1]`, `range(i0) = range(u0) = {0}`.
`.len` has type `u64`. *Deviation:* Zig uses `usize`; phase 1 has no `usize` and fixes 64 bits.

### 2.2 Coercion (as in Zig)

`T1 ⇝ T2` holds when a value of `T1` is always representable in `T2`:

- `uN ⇝ uM` if `M ≥ N`; `iN ⇝ iM` if `M ≥ N`; `uN ⇝ iM` if `M > N`.
- `comptime_int` with literal value `v` ⇝ `iN`/`uN` if `v ∈ range`, checked at compile time.
- Every type coerces to itself. Nothing else coerces; narrowing needs `@intCast`.

### 2.3 Expression typing (exec mode)

| Form | Rule | Result |
| --- | --- | --- |
| `a op b`, op ∈ `+ - * +% -% *% +\| -\| *\|` | peer type `P`: the one of `T(a)`, `T(b)` the other coerces to; error if neither | `P` |
| `a / b`, `a % b` | peer type must be unsigned (Zig rejects `/` and `%` on signed operands unless both are comptime-known positive; phase 1 always rejects) | `P` |
| `@divTrunc(a, b)`, `@rem(a, b)` | peer type, any signedness | `P` |
| `-a` | `T(a)` signed (Zig rejects `-` on unsigned; use `0 -% a`) | `T(a)` |
| `a cmp b` | both integers, any widths and signedness (Zig compares mathematically) | `bool` |
| `a and b`, `a or b`, `!a` | operands `bool` | `bool` |
| `xs[e]` | `xs: slice(T)`, `T(e) ⇝ u64` | `T` |
| `xs.len` | `xs: slice(T)` | `u64` |
| `s.f` | `s: struct S`, `f` a field of `S` | field type |
| `@intCast(T, e)` | `T(e)` and `T` integer types | `T` |
| `[_]T{ e1, …, en }` | each `T(ei) ⇝ T` | `slice(T)` |
| `S{ .f1 = e1, … }` | every field exactly once, `T(ei) ⇝` field type | `struct S` |
| `f(e1, …, en)` | `T(ei) ⇝` param type; `f` declared | return type |

### 2.4 Spec mode

Contracts (`requires`, `ensures`, `invariant`, `where`) are typed in spec mode:

- Every integer-typed subexpression is lifted to `int`. **Arithmetic in specs is mathematical:
  no overflow, no obligations.** `xs.len * 2` in a contract cannot overflow.
- Wrapping and saturating operators are rejected in specs (they describe representation).
- `result` is allowed only in `ensures`, with the function's return type.
- `forall k in a..b: P`: `k: int`, `a`, `b`, `P` in spec mode, `P: bool`.
  **Fragment restriction** (array property fragment, Bradley–Manna–Sipma 2006): inside `P`, `k`
  may appear only as a bare index `xs[k]` and in linear comparisons; no arithmetic on `k` inside
  an index (`xs[k + 1]` is rejected), no nested reads (`xs[ys[k]]`), no nested `forall` over
  the same array. *To verify during implementation:* that this restriction matches the
  decidable fragment exactly, not just approximately.
- Calls are not allowed in specs in phase 1.

### 2.5 Capability rule

1. `Io` has no constructor and no literal.
2. Only function parameters may have type `Io`. `Io` may not appear as a struct field, slice
   element, return type, or `const`/`var` type.
3. An expression of type `Io` may appear only as the receiver of an Io builtin
   (`io.print_int(e)`, `io.read_i64()`) or as a call argument.
4. Only `main` is called by the runtime, with one `Io` value.

Consequence: a function performs I/O only if it has an `Io` parameter, and only if every caller
up to `main` passed one down. The capability check is a property of signatures alone; no body
needs to be read. That is the property the token-reduction argument depends on.

### 2.6 Well-formedness

- Every non-`void` function returns on all paths (as in Zig).
- Assignment targets are `var` locals only.
- No shadowing; no unused locals or parameters (as in Zig).

---

## 3. Core language

The VC generator works on a desugared core. Desugaring is mechanical and deterministic:

1. **A-normal form for calls.** Every call is lifted into its own statement with a fresh
   `const`, in left-to-right evaluation order. `io.print_int(max(a))` becomes
   `const t1: i32 = max(a); io.print_int(t1);`. *Deviation:* Zig leaves evaluation order of some
   operands unspecified; phase 1 defines left-to-right.
2. **Continue expressions.** `while (c) : (x = e) inv I { s }` becomes
   `while (c) inv I { s; x = e; }`.
3. **Structs are flattened.** With no references, a struct value is a tuple: a variable `p: Point`
   becomes `p.x`, `p.y`; a slice of structs becomes one array per field. `where` clauses become
   obligations at every struct literal and hypotheses at every use.
4. **Array literals** become a fresh slice with its length and element values asserted.

Core statements:

```
s ::= skip | x := e | assert[k] φ | assume φ | s ; s
    | if e then s else s | while e inv I do s
    | x := call f(e…) | call f(e…) | return e | return
```

`assert[k]` carries an obligation **kind** `k` ∈ {`bounds`, `overflow`, `div`, `cast`, `requires`,
`ensures`, `inv-entry`, `inv-preserve`, `spec-wf`} and a source location. Kinds `bounds`,
`overflow`, `div` and `cast` are *safety* obligations; the rest are *contract* obligations.

---

## 4. Expression semantics

For each expression the generator produces a term `⟦e⟧` and a definedness condition `D(e)`.

### 4.1 Exec mode

Write `v1 = ⟦a⟧`, `v2 = ⟦b⟧`, `P` the peer type, `in(P, t)` for `t ∈ range(P)`.

| Expression | `⟦e⟧` | `D(e)` beyond `D(a) ∧ D(b)` | Kind |
| --- | --- | --- | --- |
| literal, variable | value, name | — | |
| `a + b`, `a - b` | `v1 ± v2` | `in(P, v1 ± v2)` | overflow |
| `a * b` | `v1 · v2` | `in(P, v1 · v2)` | overflow |
| `a +% b` etc. | `wrap_P(v1 ± v2)` | — | |
| `a +\| b` etc. | `clamp_P(v1 ± v2)` | — | |
| `a / b` (unsigned) | `div(v1, v2)` | `v2 ≠ 0` | div |
| `a % b` (unsigned) | `mod(v1, v2)` | `v2 ≠ 0` | div |
| `@divTrunc(a, b)` | `sgn(v1)·sgn(v2)·div(\|v1\|, \|v2\|)` | `v2 ≠ 0 ∧ in(P, quotient)` | div, overflow |
| `@rem(a, b)` | `v1 − v2 · ⟦@divTrunc(a, b)⟧` | `v2 ≠ 0` | div |
| `-a` | `−v1` | `in(T, −v1)` | overflow |
| `a cmp b`, `!a` | as written, mathematically | — | |
| `a and b` | `v1 ∧ v2` | `D(a) ∧ (v1 → D(b))` (short-circuit) | |
| `a or b` | `v1 ∨ v2` | `D(a) ∧ (¬v1 → D(b))` (short-circuit) | |
| `xs[e]` | `select(xs, ⟦e⟧)` | `0 ≤ ⟦e⟧ < len(xs)` | bounds |
| `xs.len` | `len(xs)` | — | |
| `@intCast(T, e)` | `⟦e⟧` | `in(T, ⟦e⟧)` | cast |

Where `wrap_uN(t) = t mod 2^n`, `wrap_iN(t) = ((t + 2^(n−1)) mod 2^n) − 2^(n−1)`,
`clamp_T(t) = min(max(t, min_T), max_T)`. Integers are mathematical integers; a value of type `T`
is never outside `range(T)` because every operation that could leave it carries an obligation.
That is why linear integer arithmetic suffices and bitvectors are not needed.

**Nonlinear terms.** `v1 · v2`, `div` and `mod` are linear only when one operand is a literal.
Otherwise the obligation is emitted in a nonlinear logic (`AUFNIA`) and may return `unknown`,
which is treated as not proven: in lenient mode a runtime check remains.

### 4.2 Spec mode

Same table without the overflow rows: arithmetic is unbounded, so `D` only contains `bounds` and
`div` conditions (kind `spec-wf`). Additionally:

- `⟦forall k in a..b: P⟧ = ∀k. ⟦a⟧ ≤ k < ⟦b⟧ → ⟦P⟧`, emitted with trigger `select(xs, k)` for each
  array read in `P`.
- `D(forall k in a..b: P) = D(a) ∧ D(b) ∧ ∀k. ⟦a⟧ ≤ k < ⟦b⟧ → D(P)`.

`A(φ) = D(φ) ∧ ⟦φ⟧` is "φ is well-defined and true". Every contract is asserted through `A`.

### 4.3 Type hypotheses

`Ty(x: T)` is the fact a variable of type `T` contributes:

- `in(T, x)` for integer types;
- for `xs: slice(T)`: `0 ≤ len(xs) ≤ 2^64 − 1 ∧ ∀k. 0 ≤ k < len(xs) → in(T, select(xs, k))`
  (the element axiom is itself in the array property fragment; measured cost: about 30% more
  solver work on `max`, results unchanged);
- flattened struct fields: the fields' facts plus the `where` clause.

---

## 5. Weakest preconditions

`wp(s, Q, R)`: `Q` is the postcondition for normal completion, `R` the postcondition on `return`
(a predicate over `result`). Asserted facts are assumed afterwards (`assert φ` contributes
`φ ∧ (φ → …)`), so later obligations may rely on earlier ones; this is also exactly right for
lenient mode, where an unproven safety obligation becomes a runtime check and execution only
continues past it when it held.

```
wp(skip, Q, R)              = Q
wp(assert[k] φ, Q, R)       = φ ∧ (φ → Q)
wp(assume φ, Q, R)          = φ → Q
wp(x := e, Q, R)            = wp(assert D(e), Q[x := ⟦e⟧], R)
wp(s1 ; s2, Q, R)           = wp(s1, wp(s2, Q, R), R)
wp(if e then s1 else s2,Q,R)= wp(assert D(e), (⟦e⟧ → wp(s1,Q,R)) ∧ (¬⟦e⟧ → wp(s2,Q,R)), R)
wp(return e, Q, R)          = wp(assert D(e), R[result := ⟦e⟧], R)
wp(return, Q, R)            = R
```

**Calls.** For `f` with parameters `p⃗`, `requires P_f`, `ensures E_f`, return type `T_f`, and
fresh `r`:

```
wp(x := call f(e⃗), Q, R) = wp(assert D(e⃗); assert[requires] P_f[p⃗ := ⟦e⃗⟧],
                              ∀r. (Ty(r: T_f) ∧ E_f[p⃗ := ⟦e⃗⟧, result := r]) → Q[x := r], R)
```

Modular: the callee's body is never inspected, only its contract. `∀r` sits in hypothesis
position after negation and becomes a fresh constant, so it adds no quantifier to the solver.

Io builtins: `call io.print_int(e)` is `assert D(e)` (output is not modelled in phase 1);
`x := call io.read_i64()` is `∀r. Ty(r: i64) → Q[x := r]`.

**Loops.** Let `M` be the variables assigned in `s` (syntactic, after desugaring), `M'` fresh
copies, and `·'` substitution of `M'` for `M`:

```
wp(while e inv I do s, Q, R) =
      A(I)                                                       [inv-entry, spec-wf]
    ∧ ∀M'. ( Ty(M') ∧ ⟦I⟧' ) →
          ( D(e)'                                                [safety of the guard]
          ∧ ( ⟦e⟧' → wp(s, A(I), R)' )                            [inv-preserve, body safety]
          ∧ ( ¬⟦e⟧' → Q' ) )                                      [exit]
```

`Ty(M')` is what made `i + 1` provable in `max`: the havocked `i` is still a `u64`. Without it the
solver could pick `i = 2^64` and report a spurious overflow.

A counterexample from inside `∀M'` describes a state that satisfies the invariant, not
necessarily a reachable state. It is reported as "not provable from the given facts".

**Function VC.** For `fn f(p⃗: T⃗) T requires P ensures E { s }`:

```
VC_wf_requires(f) = ∀p⃗. Ty(p⃗) → D(P)                                        [spec-wf]
VC_wf_ensures(f)  = ∀p⃗, r. Ty(p⃗) ∧ ⟦P⟧ ∧ Ty(r: T) → D(E)[result := r]         [spec-wf]
VC_body(f)        = ∀p⃗. Ty(p⃗) ∧ ⟦P⟧ → wp(s, Q₀, A(E))                         [ensures, …]
```

with `Q₀ = A(E)` for `void` functions (falling off the end returns) and `Q₀ = false` otherwise
(unreachable by §2.6; `false` is sound and never produces a spurious obligation).

---

## 6. From VC to queries

The VC is not sent as one formula. The generator walks the `wp` computation and emits **one query
per `assert`**: the hypotheses on the path to it (type facts, `assume`s, earlier asserts, branch
conditions, loop invariants and guard) and the negated obligation.

```
(set-logic AUFLIA)                ; AUFNIA if the obligation is nonlinear
(set-option :produce-models true)
<declarations: one Int per integer variable, (Array Int Int) + Int length per slice field>
<hypotheses>
(assert (not <obligation>))
(check-sat)
```

| Answer | Meaning | Safety obligation | Contract obligation |
| --- | --- | --- | --- |
| `unsat` | proven | no runtime check emitted | accepted |
| `sat` | counterexample (possibly spurious inside loops) | lenient: runtime check + report; strict: reject | reject, model returned to the submitter |
| `unknown` / rlimit | no answer | lenient: runtime check + report; strict: reject | reject |

Solver configuration is part of the trusted setup and is pinned:

- Z3: `rlimit` per query (not a wall-clock timeout), fixed `random_seed`.
- cvc5: `mbqi` enabled; without it cvc5 returns `unknown` on `sat` queries whose hypotheses contain
  quantifiers (observed on the `i_u8` variant of `max`).
- Cross-check: both solvers per query. `unsat` vs `sat` is a disagreement and a bug to investigate;
  `unknown` from one solver is no answer, not a disagreement.

---

## 7. What this core does not cover

- **Termination.** Partial correctness only: a loop that never ends satisfies any postcondition.
  `decreases` is phase 1.5; until then the checker lists every loop without one.
- References, aliasing, heap allocation, mutable slices, generics, closures, strings,
  information-flow types, more than one capability, specs that call functions.

---

## Appendix A. `max` against the reference queries

Applying §5 to the example in §1.3 (after desugaring: `const t1: i32 = max(…)` in `main`, the
continue expression appended to the loop body) yields these obligations. Each matches a query in
`smt/max/` (variant `inv2_only`):

| Obligation | Source | Query |
| --- | --- | --- |
| `0 ≤ 0 < len(xs)` (bounds) | `xs[0]` under `requires` | `o01_xs0_bounds` |
| `A(I)` at `i = 1, m = xs[0]` (inv-entry, spec-wf) | loop entry | `o03_inv2_entry` |
| `0 ≤ i < len(xs)` (bounds) | `xs[i]` in the `if` condition and assignment, under `⟦I⟧'` and guard | `o04_xsi_bounds` |
| `in(u64, i + 1)` (overflow) | continue expression | `o05_i_plus_1_overflow` |
| `⟦I⟧` at `i + 1, m'` (inv-preserve) | end of body | `o07_inv2_preserved` |
| `D(I)` at `i + 1` (spec-wf) | end of body | `o08_inv2_wellformed` |
| `A(E)` at exit with `result = m` (ensures) | `return m` after `¬guard` | `o09_postcondition` |
| `len = 3 > 0` (requires) | call in `main` | `o10_main_requires` |
| `D(E)` (spec-wf) | `VC_wf_ensures` | `o11_ensures_wellformed` |

Differences between the hand-written queries and §5, to resolve when the generator is diffed
against them:

1. The queries omit the slice element axiom from `Ty`; the `elem_axiom` variant adds it and all
   obligations still prove.
2. The queries check `xs[i]` once; §5 emits it twice (condition and assignment). The second has
   the first as a hypothesis, so it is trivially `unsat`. The generator may deduplicate
   syntactically identical obligations on the same path.
3. `VC_wf_requires` (`D(xs.len > 0)`, trivially true) has no query.
4. Main's own body adds `D(⟦3, 1, 2⟧)` literal facts and no other obligations.
