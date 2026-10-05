"""Audit the exact epsilon seed and its finite simply-typed branches.

Small System F + native Nat/Rec checker for these annotations only.
No type-level beta conversion or F-omega certificate enumeration is claimed.
"""

import json

import dqdn


N = ("nat",)
A = ("tv", 0)


def arr(a, b):
    return ("arr", a, b)


CN = ("all", arr(arr(A, A), arr(A, A)))
V = lambda k: ("var", k)
LAM = lambda a, t: ("lam", a, t)
APP = lambda f, x: ("app", f, x)
Q0 = ("query", ("num", 0))


def shift_type(a, amount, depth=0):
    tag = a[0]
    if tag == "nat":
        return a
    if tag == "tv":
        return (tag, a[1] + amount if a[1] >= depth else a[1])
    if tag == "arr":
        return (tag, shift_type(a[1], amount, depth), shift_type(a[2], amount, depth))
    if tag == "all":
        return (tag, shift_type(a[1], amount, depth + 1))
    raise ValueError("bad type")


def subst_type(a, parameter, depth=0):
    tag = a[0]
    if tag == "nat":
        return a
    if tag == "tv":
        k = a[1]
        return (shift_type(parameter, depth) if k == depth else
                (tag, k - 1 if k > depth else k))
    if tag == "arr":
        return (tag, subst_type(a[1], parameter, depth), subst_type(a[2], parameter, depth))
    if tag == "all":
        return (tag, subst_type(a[1], parameter, depth + 1))
    raise ValueError("bad type")


def require(ok, message):
    if not ok:
        raise ValueError(message)


def valid_type(a, depth):
    if a == N:
        return
    if a[0] == "tv":
        require(type(a[1]) is int and 0 <= a[1] < depth, "unbound type variable")
    elif a[0] == "arr":
        valid_type(a[1], depth)
        valid_type(a[2], depth)
    elif a[0] == "all":
        valid_type(a[1], depth + 1)
    else:
        raise ValueError("bad type")


def infer(t, context=(), type_depth=0):
    tag = t[0]
    if tag == "var":
        require(type(t[1]) is int and 0 <= t[1] < len(context), "unbound variable")
        return context[t[1]]
    if tag == "num":
        require(type(t[1]) is int and t[1] >= 0, "bad numeral")
        return N
    if tag in ("query", "succ"):
        require(infer(t[1], context, type_depth) == N, "numeric argument required")
        return N
    if tag == "lam":
        valid_type(t[1], type_depth)
        return arr(t[1], infer(t[2], (t[1],) + context, type_depth))
    if tag == "app":
        f = infer(t[1], context, type_depth)
        require(f[0] == "arr", "function type required")
        require(infer(t[2], context, type_depth) == f[1], "argument type mismatch")
        return f[2]
    if tag == "poly":
        ctx = tuple(shift_type(a, 1) for a in context)
        return ("all", infer(t[1], ctx, type_depth + 1))
    if tag == "inst":
        f = infer(t[1], context, type_depth)
        require(f[0] == "all", "universal type required")
        valid_type(t[2], type_depth)
        return subst_type(f[1], t[2])
    if tag == "rec":
        a = infer(t[1], context, type_depth)
        require(infer(t[2], context, type_depth) == arr(N, arr(a, a)), "bad recursor step")
        require(infer(t[3], context, type_depth) == N, "bad recursor index")
        return a
    raise ValueError("bad term")


def erase(t, terms):
    tag = t[0]
    if tag in ("var", "num"):
        return terms.make("v" if tag == "var" else "n", t[1])
    if tag in ("poly", "inst"):
        return erase(t[1], terms)
    if tag == "lam":
        return terms.make("l", erase(t[2], terms))
    translated_tag = {"query": "q", "succ": "s", "rec": "r", "app": "a"}[tag]
    return terms.make(translated_tag, *(erase(x, terms) for x in t[1:]))


def f_at(a):
    step = LAM(N, LAM(a, APP(V(3), V(0))))
    return LAM(arr(a, a), LAM(a, ("rec", V(0), step, Q0)))


F = ("poly", f_at(A))
J = LAM(N, ("rec", V(0), LAM(N, LAM(N, V(0))), Q0))
Z = ("poly", LAM(arr(A, A), LAM(A, V(0))))
RIGHT_F = ("poly", APP(("inst", V(0), arr(A, A)), ("inst", F, A)))
STEP = LAM(N, LAM(CN, RIGHT_F))
EPSILON = APP(APP(("inst", ("rec", Z, STEP, Q0), N), J), ("num", 0))


def tower(height):
    if height == 0:
        return APP(J, ("num", 0))
    levels = [N]
    for _ in range(height):
        levels.append(arr(levels[-1], levels[-1]))
    result = f_at(levels[height - 1])
    for level in range(height - 2, -1, -1):
        result = APP(result, f_at(levels[level]))
    return APP(APP(result, J), ("num", 0))


def main():
    require(infer(F) == CN, "bad polymorphic iterator")
    require(infer(J) == arr(N, N), "bad query successor")
    require(infer(EPSILON) == N, "epsilon seed type mismatch")
    terms = dqdn.Terms(dqdn.Budget(seconds=3.0))
    root = erase(EPSILON, terms)
    require(root == dqdn.epsilon_seed(terms), "epsilon seed literal erasure mismatch")
    branch_results = []
    for n in range(9):
        if n:
            annotated = tower(n - 1)
            require(infer(annotated) == N, "simple branch not typed at Nat")
            target = erase(annotated, terms)
            require(target == dqdn.finite_tower(terms, n - 1), "tower erasure mismatch")
        else:
            target = terms.numeral(0)
        current = terms.computation_child(root, n * (n + 3) // 2)
        steps = 0
        while current != target and steps < 100:
            selected = terms.demand(current)
            require(selected is not None and terms.data[selected[0]][0] != "q",
                    "query appeared inside administrative prefix")
            current = terms.computation_child(current, 0)
            steps += 1
        require(current == target, "did not reach exact finite branch")
        require(steps == 3 * n + 3, "unexpected administrative step count")
        branch_results.append({"answer": n, "deterministic_steps": steps})
    raw = []
    dqdn.emit_data(root, raw, {}, terms)
    compatible = dqdn.append_program(dqdn.OMEGA, terms, root)
    print(json.dumps({"typechecks": True, "literal_erasure": True,
                      "raw_data_columns": len(raw),
                      "standalone_with_activity": len(raw) + 1,
                      "omega_compatible_columns": len(compatible),
                      "branches": branch_results}, indent=2))


if __name__ == "__main__":
    main()
