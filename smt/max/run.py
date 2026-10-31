"""Run every obligation through Z3 and cvc5; then stress Z3 determinism.

Usage: python3 run.py out
"""
import glob, os, random, sys
import z3, cvc5

RLIMIT = 5_000_000   # deterministic resource limit, not wall-clock

def z3_check(path, seed=0, shuffle=False):
    ctx = z3.Context()                       # fresh context: per-query rlimit count
    asserts = list(z3.parse_smt2_file(path, ctx=ctx))
    if shuffle:
        random.Random(seed).shuffle(asserts)
    s = z3.Solver(ctx=ctx)
    s.set("random_seed", seed)
    s.set("smt.random_seed", seed)
    s.set("rlimit", RLIMIT)
    s.add(asserts)
    r = s.check()
    st = s.statistics()
    rl = st.get_key_value("rlimit count") if "rlimit count" in st.keys() else None
    model = None
    if r == z3.sat:
        m = s.model()
        model = {str(d): str(m[d]) for d in m.decls() if str(d) in ("len", "i", "m", "x")}
        xs = [d for d in m.decls() if str(d) == "xs"]
        if xs and "len" in model and int(model["len"]) > 0:
            arr = m[xs[0]]
            for k in range(min(int(model["len"]), 2)):
                model[f"xs[{k}]"] = str(m.eval(z3.Select(xs[0](), k), model_completion=True))
        model = dict(sorted(model.items()))
    return str(r), rl, model

def cvc5_check(path):
    tm = cvc5.TermManager()
    s = cvc5.Solver(tm)
    s.setOption("tlimit-per", "10000")
    s.setOption("mbqi", "true")   # model-based quantifier instantiation: needed to confirm sat
    sm = cvc5.SymbolManager(tm)
    p = cvc5.InputParser(s, sm)
    p.setFileInput(cvc5.InputLanguage.SMT_LIB_2_6, path)
    out = []
    while True:
        cmd = p.nextCommand()
        if cmd.isNull():
            break
        res = cmd.invoke(s, sm)
        if res and res.strip():
            out.append(res.strip())
    return out[-1] if out else "?"

def main(root):
    print(f"{'variant':<14}{'obligation':<26}{'z3':<9}{'cvc5':<9}{'rlimit':>9}  counterexample")
    for d in sorted(os.listdir(root)):
        for f in sorted(glob.glob(os.path.join(root, d, "*.smt2"))):
            name = os.path.basename(f)[:-5]
            r, rl, model = z3_check(f)
            c = cvc5_check(f)
            flag = "" if r == c else "  <-- DISAGREE"
            print(f"{d:<14}{name:<26}{r:<9}{c:<9}{rl!s:>9}  {model or ''}{flag}")

    # determinism: 20 seeds x shuffled assertion order, on the proven variant
    print("\nDeterminism (variants ok, inv2_only, elem_axiom; 20 seeds, shuffled assertions):")
    for d in ("ok", "inv2_only", "elem_axiom"):
        for f in sorted(glob.glob(os.path.join(root, d, "*.smt2"))):
            results, rls = set(), []
            for seed in range(20):
                r, rl, _ = z3_check(f, seed=seed, shuffle=True)
                results.add(r); rls.append(rl)
            name = os.path.basename(f)[:-5]
            print(f"  {d:<14}{name:<26}results={sorted(results)}  rlimit min/max={min(rls)}/{max(rls)}")

if __name__ == "__main__":
    main(sys.argv[1])
