import sys
sys.setrecursionlimit(30000)

from constants import *
from parser import parse
from env import add_to_env, env_find, make_env
from pretty_printer import pretty_print


def tagged_cons(head, tail):
    return (TYPE_CONS, (head, tail))

def tagged_head(l):
    assert l[0] == TYPE_CONS, "Wrong type"
    return l[1][0]

def tagged_tail(l):
    assert l[0] == TYPE_CONS, "Wrong type"
    return l[1][1]

def tagged_cons(head, tail):
    return (TYPE_CONS, (head, tail))

def tagged_head(l):
    if l[0] == TYPE_UNKNOWN:
        return (TYPE_UNKNOWN,)
    elif l[0] == TYPE_ERROR:
        return (TYPE_ERROR,)
    assert l[0] == TYPE_CONS, l
    return l[1][0]

def tagged_tail(l):
    if l[0] == TYPE_UNKNOWN:
        return (TYPE_UNKNOWN,)
    elif l[0] == TYPE_ERROR:
        return (TYPE_ERROR,)
    assert l[0] == TYPE_CONS, l
    return l[1][1]

def make_func(env, func_def, func_code):
    for i in range(len(func_def)):
        assert func_def[i][0] == PARSED_IDENT, "Invalid function declaration"
    args = tuple([func_def[i][1] for i in range(1, len(func_def))])
    nm = func_def[0][1]
    if nm.endswith(" rec"): nm = nm[:-4]
    return (TYPE_FUNCTION, (func_code, args, env, nm))

def make_func_in_env(env, func_def, func_code):
    return add_to_env(env, func_def[0][1], make_func(env, func_def, func_code))

def is_call_to(e, f):
    return e[0] == PARSED_CALL and e[1][0][1] == f

def binding_is_func(bind_def):
    return bind_def[0] != PARSED_IDENT and not is_call_to(bind_def, "cons")

def bind(env, bind_def, value):
    if bind_def[0] == PARSED_IDENT:
        if bind_def[1] == "[]":
            assert value[0] in [TYPE_NIL, TYPE_UNKNOWN, TYPE_ERROR]
            return env
        elif bind_def[1] == "_":
            return env
        else:
            return add_to_env(env, bind_def[1], value)
    elif is_call_to(bind_def, "cons"):
        return bind(bind(env, bind_def[1][1], tagged_head(value)), bind_def[1][2], tagged_tail(value))

def make_rec(env, names, bind_def, bind_value):
    name = bind_def[1][0][1]
    return make_func(env, ((PARSED_IDENT, name + " rec"),) + tuple((PARSED_IDENT, n) for n in names),
                            (PARSED_CALL, ((PARSED_KEYWORD, "let"),
                                        (PARSED_CALL, ((PARSED_IDENT, name + " rec"),) + bind_def[1][1:]),
                                        bind_value,
                                        (PARSED_IDENT, name + " rec"))))

def make_binding(env, bind_def, bind_value, is_recursive = False):
    if is_recursive:
        assert binding_is_func(bind_def), "Incorrect recursive binding"
    if bind_def[0] == PARSED_IDENT:
        return bind(env, bind_def, eval_expr(env, bind_value))
    elif is_call_to(bind_def, "cons"):
        return bind(env, bind_def, eval_expr(env, bind_value))
    elif bind_def[0] == PARSED_CALL:
        if is_recursive:
            name = bind_def[1][0][1]
            frec = make_rec(env, [name], bind_def, bind_value)
            return add_to_env(env, name, (TYPE_FIXPOINT, (frec,), frec, name))
        return make_func_in_env(env, bind_def[1], bind_value)
    else:
        raise Exception("Incorrect binding")

def make_bindings(env, bds, is_recursive = False):
    assert bds[0] == PARSED_CALL
    bds = bds[1]
    assert all(bd[0] == PARSED_CALL and len(bd[1]) == 2 for bd in bds)
    bind_defs = tuple(bd[1][0] for bd in bds)
    bind_values = tuple(bd[1][1] for bd in bds)
    if is_recursive:
        assert all(binding_is_func(bind_def) for bind_def in bind_defs)
    if not is_recursive:
        newenv = env
        for bind_def, bind_value in zip(bind_defs, bind_values):
            if not binding_is_func(bind_def):
                newenv = bind(newenv, bind_def, eval_expr(env, bind_value))
            else:
                newenv = add_to_env(newenv, bind_def[1][0][1], make_func(env, bind_def[1], bind_value))
        return newenv
    names = [bind_def[1][0][1] for bind_def in bind_defs]
    frecs = tuple(make_rec(env, names, bind_def, bind_value) for bind_def, bind_value in zip(bind_defs, bind_values))
    for i in range(len(names)):
        env = add_to_env(env, names[i], (TYPE_FIXPOINT, frecs, frecs[i], names[i]))
    return env

def eval_keyword(env, expr):
    keyword = expr[0][1]
    if keyword == "if":
        cond = eval_expr(env, expr[1])
        assert cond[0] == TYPE_BOOL, "if needs a bool"
        if cond[1]:
            return eval_expr(env, expr[2])
        else:
            return eval_expr(env, expr[3])
    elif keyword in ["let", "letrec"]:
        return eval_expr(make_binding(env, expr[1], expr[2], keyword == "letrec"), expr[3])
    elif keyword in ["let*", "letrec*"]:
        return eval_expr(make_bindings(env, expr[1], keyword == "letrec*"), expr[2])

def eval_call(func, args):
    code = func[0]
    argnames = func[1]
    fenv = func[2]
    assert len(argnames) == len(args), "Wrong number of arguments : "+str(argnames)
    for i in range(len(argnames)):
        fenv = add_to_env(fenv, argnames[i], args[i])
    return eval_expr(fenv, code)

def pr_tu(t):
    if type(t) == type(tuple()):
        for x in t:
            pr_tu(x)
    else:
        print(t)

def eval_expr(env, expr):
    if expr[0] == PARSED_CONSTANT:
        return expr[1]
    if expr[0] == PARSED_INT:
        return (TYPE_INT, expr[1])
    elif expr[0] == PARSED_CHAR:
        return (TYPE_CHAR, expr[1])
    elif expr[0] == PARSED_IDENT:
        return env_find(env, expr[1])
    else: # expr[0] == PARSED_CALL
        if expr[1][0][0] == PARSED_KEYWORD:
            return eval_keyword(env, expr[1])
        else:
            func = eval_expr(env, expr[1][0])
            if func[0] == TYPE_BUILTIN_FUNCTION:
                args = [eval_expr(env, expr[1][i]) for i in range(1, len(expr[1]))]
                return func[1](*args)
            elif func[0] == TYPE_FIXPOINT:
                func = eval_call(func[2][1], [(TYPE_FIXPOINT, func[1], f, func[3]) for f in func[1]])
            assert func[0] == TYPE_FUNCTION, "Can only call a function"
            args = []
            for i in range(1, len(expr[1])):
                args.append(eval_expr(env, expr[1][i]))
            return eval_call(func[1], args)

def num_op(f):
    def wrap(x, y):
        assert x[0] == y[0] == TYPE_INT, "Wrong type"
        return (TYPE_INT, f(x[1], y[1]))
    return (TYPE_BUILTIN_FUNCTION, wrap)

def comp_op(f):
    def wrap(x, y):
        assert x[0] == y[0] == TYPE_INT, "Wrong type"
        return (TYPE_BOOL, f(x[1], y[1]))
    return (TYPE_BUILTIN_FUNCTION, wrap)

def bool_op(f):
    def wrap(x, y):
        assert x[0] == y[0] == TYPE_BOOL, "Wrong type"
        return (TYPE_BOOL, f(x[1], y[1]))
    return (TYPE_BUILTIN_FUNCTION, wrap)

def neg(x):
    assert x[0] == TYPE_BOOL, "Wrong type"
    return (TYPE_BOOL, not x[1])

def eq(x, y):
    if x[0] != y[0]:
        return False
    if x[0] == TYPE_INT:
        return x[1] == y[1]
    elif x[0] == TYPE_NIL:
        return True
    elif x[0] == TYPE_CONS:
        return eq(tagged_head(x), tagged_head(y)) and eq(tagged_tail(x), tagged_tail(y))
    elif x[0] == TYPE_CHAR:
        return x[1] == y[1]
    else:
        return False

def equal(x, y):
    return (TYPE_BOOL, eq(x, y))

def unequal(x, y):
    return (TYPE_BOOL, not eq(x, y))

def make_string(s):
    return make_list([(TYPE_CHAR, x) for x in s])

def get_string(s):
    u = read_list(s)
    for x in u:
        assert x[0] == TYPE_CHAR, "Wrong type"
    return "".join(x[1] for x in u)

def int_of_string(s):
    a = get_string(s)
    return (TYPE_INT, int(a))

def string_of_int(n):
    assert n[0] == TYPE_INT, "Wrong type"
    return make_string(str(n[1]))

def int_of_char(c):
    assert c[0] == TYPE_CHAR, "Wrong type"
    return (TYPE_INT, ord(c[1]))

def char_of_int(n):
    assert n[0] == TYPE_INT, "Wrong type"
    return (TYPE_CHAR, chr(n[1]))

def make_list(l):
    u = (TYPE_NIL,)
    for x in reversed(l):
        u = tagged_cons(x, u)
    return u

def is_list(u):
    while u[0] != TYPE_NIL:
        if u[0] == TYPE_CONS:
            u = tagged_tail(u)
        else:
            return False
    return True

def read_list(u):
    l = []
    while u[0] != TYPE_NIL:
        l.append(tagged_head(u))
        u = tagged_tail(u)
    return l

def error(s):
    raise Exception(get_string(s))

def concat(t1, t2):
    assert is_list(t1) and is_list(t2), "Incorrect arguments"
    return make_list(read_list(t1) + read_list(t2))

global_env = make_env([
    ("[]", (TYPE_NIL,)),
    ("true", (TYPE_BOOL, True)),
    ("false", (TYPE_BOOL, False)),
    ("cons", (TYPE_BUILTIN_FUNCTION, tagged_cons)),
    ("head", (TYPE_BUILTIN_FUNCTION, tagged_head)),
    ("tail", (TYPE_BUILTIN_FUNCTION, tagged_tail)),
    ("+", num_op(lambda x, y: x + y)),
    ("*", num_op(lambda x, y: x * y)),
    ("-", num_op(lambda x, y: x - y)),
    ("/", num_op(lambda x, y: x // y)),
    ("or", bool_op(lambda x, y: x or y)),
    ("and", bool_op(lambda x, y: x and y)),
    ("xor", bool_op(lambda x, y: x ^ y)),
    ("not", (TYPE_BUILTIN_FUNCTION, neg)),
    ("<", comp_op(lambda x, y: x < y)),
    (">", comp_op(lambda x, y: x > y)),
    ("<=", comp_op(lambda x, y: x <= y)),
    (">=", comp_op(lambda x, y: x >= y)),
    ("=", (TYPE_BUILTIN_FUNCTION, equal)),
    ("!=", (TYPE_BUILTIN_FUNCTION, unequal)),
    ("int_of_string", (TYPE_BUILTIN_FUNCTION, int_of_string)),
    ("string_of_int", (TYPE_BUILTIN_FUNCTION, string_of_int)),
    ("int_of_char", (TYPE_BUILTIN_FUNCTION, int_of_char)),
    ("char_of_int", (TYPE_BUILTIN_FUNCTION, char_of_int)),
    ("error", (TYPE_BUILTIN_FUNCTION, error)),
    ("concat", (TYPE_BUILTIN_FUNCTION, concat)),
])

def show(result):
    if result[0] == TYPE_INT:
        return str(result[1])
    elif result[0] == TYPE_CHAR:
        return "'" + result[1] + "'"
    elif result[0] == TYPE_NIL:
        return "[]"
    elif result[0] == TYPE_CONS:
        if is_list(result):
            l = read_list(result)
            if all(a[0] == TYPE_CHAR for a in l):
                return '"' + "".join(a[1] for a in l) + '"'
            else:
                return "[" + " ".join(show(a) for a in l) + "]"
        return "(cons " + show(tagged_head(result)) + " " + show(tagged_tail(result)) + ")"
    elif result[0] == TYPE_BOOL:
        return result[1] and "true" or "false"
    else:
        return "<function>"

def eval_main(env, code, args):
    for expr in code:
        if expr[0] == PARSED_CALL and expr[1][0][1] in ["let", "letrec"] and len(expr[1]) == 3:
            env = make_binding(env, expr[1][1], expr[1][2], expr[1][0][1] == "letrec")
        elif expr[0] == PARSED_CALL and expr[1][0][1] in ["let*", "letrec*"] and len(expr[1]) == 2:
            env = make_bindings(env, expr[1][1], expr[1][0][1] == "letrec*")
        else:
            print(show(eval_expr(env, expr)))
    env = add_to_env(env, "args ", make_string(args))
    print(show(eval_expr(env, (PARSED_CALL, [(PARSED_IDENT, "main"), (PARSED_IDENT, "args ")]))))

def run(code, args):
    #print(pretty_print(parse(code)))
    eval_main(global_env, parse(code), args)

def timed(code, args):
    t0 = time.time()
    run(code, args)
    return time.time() - t0

if __name__ == '__main__':
    import time
    #prog_input = "15"

    f = open("metaeval.l", "r")
    evaluator = f.read()
    f.close()

    f = open("oo.l", "r")
    partial = f.read()
    f.close()

    raw = "(letrec (fib n) (if (<= n 1) n (+ (fib (- n 2)) (fib (- n 1))))) (let (main x) (fib (int_of_string x)))"
    #print(timed(evaluator, "15"))
    #sys.exit(0)

    f = open("partial_no_opt.l", "r")
    pno = f.read()
    f.close()

    l1 = []
    l2 = []
    l3 = []
    l4 = []
    for i in range(5, 21):
        u = timed(evaluator, str(i))
        v = timed(partial, str(i))
        w = timed(raw, str(i))
        x = timed(pno, str(i))
        print(i)
        print("Metaeval:", u)
        print("Partially evaluated:", v)
        print("Partial no opt:", x)
        print("Raw:", w)
        print("Speedup:", u / v, v / w, x / v)
        l1.append(u)
        l2.append(v)
        l3.append(w)
        l4.append(x)
        print("-" * 20)
    print(l1, l2, l3, l4)

    #t0 = time.time()
    #run(evaluator, prog_input)
    #u = time.time() - t0
    #print("Metaeval:", u)

    #f = open("metameta.l", "r")
    #metameta = f.read()
    #f.close()

    #print("Metameta")
    #t0 = time.time()
    #run(metameta, prog_input)
    #print("Metameta:", time.time() - t0)

    
    #t0 = time.time()
    #run(evaluator, prog_input)
    #v = time.time() - t0
    #print("Partially evaluated:", v)
    #print("Speedup:", u / v)
