"""Hand-written verification conditions for the phase-1 `max` example.

Each obligation becomes one SMT-LIB2 query: hypotheses asserted, goal negated.
unsat = proven, sat = counterexample, unknown = not proven.

Encoding: fixed-width integers are mathematical Ints with explicit range
hypotheses; overflow is a separate obligation (never silent wrap).
Slices: (Array Int Int) + a length. Logic: AUFLIA.
"""
import os, sys

U64_MAX = 2**64 - 1
U8_MAX = 2**8 - 1
I32_MIN, I32_MAX = -2**31, 2**31 - 1

HDR = "(set-logic AUFLIA)\n(set-option :produce-models true)\n"

def decls(extra=""):
    return (
        "(declare-const xs (Array Int Int))\n"
        "(declare-const len Int)\n"
        f"(assert (and (<= 0 len) (<= len {U64_MAX})))  ; len : u64\n"
        + extra
    )

def forall_le(lo, hi, m):
    # forall k in lo..hi: xs[k] <= m   (array property fragment, trigger on xs[k])
    return (f"(forall ((k Int)) (! (=> (and (<= {lo} k) (< k {hi})) (<= (select xs k) {m}))"
            " :pattern ((select xs k))))")

def query(name, hyps, goal, note):
    body = HDR + f"; {name}: {note}\n" + "".join(f"(assert {h})\n" for h in hyps)
    body += f"(assert (not {goal}))\n(check-sat)\n"
    return name, body

def loop_state(i_max, with_inv1_upper=True, with_inv2=True, with_inv1_lower=True):
    """Arbitrary loop iteration: invariants + guard as hypotheses."""
    h = [f"(and (<= 0 i) (<= i {i_max}))",            # i : u64 (or u8)
         f"(and (<= {I32_MIN} m) (<= m {I32_MAX}))"]  # m : i32
    if with_inv1_lower:
        h.append("(<= 1 i)")
    if with_inv1_upper:
        h.append("(<= i len)")
    if with_inv2:
        h.append(forall_le(0, "i", "m"))
    return h

def build(variant="ok"):
    """variant: ok | no_requires | no_inv_upper | no_inv2 | i_u8 | inv2_only | elem_axiom"""
    i_max = U8_MAX if variant == "i_u8" else U64_MAX
    req = [] if variant == "no_requires" else ["(> len 0)"]
    inv1 = variant != "inv2_only"                     # drop invariant 1 entirely
    inv_upper = variant not in ("no_inv_upper", "inv2_only")
    inv2 = variant != "no_inv2"
    state = "(declare-const i Int)\n(declare-const m Int)\n"
    qs = []

    # --- before the loop -------------------------------------------------
    qs.append(query("o01_xs0_bounds", req, "(and (<= 0 0) (< 0 len))",
                    "xs[0] in bounds"))
    if inv1:
        entry_goal = "(and (<= 1 1)" + (" (<= 1 len))" if inv_upper else ")")
        qs.append(query("o02_inv1_entry", req, entry_goal, "invariant 1 holds on entry (i = 1)"))
    if inv2:
        qs.append(query("o03_inv2_entry", req, forall_le(0, 1, "(select xs 0)"),
                        "invariant 2 holds on entry (i = 1, m = xs[0])"))

    # --- one loop iteration ----------------------------------------------
    body_h = req + loop_state(i_max, inv_upper, inv2, inv1) + ["(< i len)"]   # + guard
    m2 = "(ite (> (select xs i) m) (select xs i) m)"
    qs.append(query("o04_xsi_bounds", body_h, "(and (<= 0 i) (< i len))",
                    "xs[i] in bounds (condition and assignment)"))
    qs.append(query("o05_i_plus_1_overflow", body_h, f"(<= (+ i 1) {i_max})",
                    "i + 1 does not overflow"))
    if inv1:
        pres1 = "(and (<= 1 (+ i 1))" + (" (<= (+ i 1) len))" if inv_upper else ")")
        qs.append(query("o06_inv1_preserved", body_h, pres1, "invariant 1 preserved"))
    if inv2:
        qs.append(query("o07_inv2_preserved", body_h, forall_le(0, "(+ i 1)", m2),
                        "invariant 2 preserved"))
        qs.append(query("o08_inv2_wellformed", body_h,
                        "(forall ((k Int)) (=> (and (<= 0 k) (< k (+ i 1))) (and (<= 0 k) (< k len))))",
                        "reads inside invariant 2 stay in bounds after the body"))

    # --- loop exit --------------------------------------------------------
    exit_h = req + loop_state(i_max, inv_upper, inv2, inv1) + ["(not (< i len))"]
    qs.append(query("o09_postcondition", exit_h, forall_le(0, "len", "m"),
                    "ensures forall k in 0..xs.len: xs[k] <= result"))

    # --- call site in main ------------------------------------------------
    qs.append(query("o10_main_requires", [], "(> 3 0)", "max([3,1,2]) satisfies requires"))

    # --- well-formedness of the postcondition itself (reads in bounds) ------
    qs.append(query("o11_ensures_wellformed", req,
                    "(forall ((k Int)) (=> (and (<= 0 k) (< k len)) (and (<= 0 k) (< k len))))",
                    "reads inside the postcondition are in bounds"))

    extra = ""
    if variant == "elem_axiom":   # slice element type i32 as a quantified range hypothesis
        extra = (f"(assert (forall ((k Int)) (! (=> (and (<= 0 k) (< k len)) "
                 f"(and (<= {I32_MIN} (select xs k)) (<= (select xs k) {I32_MAX}))) "
                 ":pattern ((select xs k)))))  ; elements : i32\n")
    return [(n, b.replace(HDR, HDR + decls(extra) + state, 1)) for n, b in qs]

def abs_case():
    """abs(x: i32) = if x < 0 then -x else x; obligation: -x fits i32."""
    b = (HDR + "(declare-const x Int)\n"
         f"(assert (and (<= {I32_MIN} x) (<= x {I32_MAX})))\n"
         "(assert (< x 0))\n"
         f"(assert (not (and (<= {I32_MIN} (- x)) (<= (- x) {I32_MAX}))))\n(check-sat)\n")
    return [("o01_neg_x_overflow", b)]

if __name__ == "__main__":
    out = sys.argv[1]
    variants = ["ok", "no_requires", "no_inv_upper", "no_inv2", "i_u8", "inv2_only", "elem_axiom"]
    for v in variants:
        d = os.path.join(out, v); os.makedirs(d, exist_ok=True)
        for n, b in build(v):
            open(os.path.join(d, n + ".smt2"), "w").write(b)
    d = os.path.join(out, "abs"); os.makedirs(d, exist_ok=True)
    for n, b in abs_case():
        open(os.path.join(d, n + ".smt2"), "w").write(b)
