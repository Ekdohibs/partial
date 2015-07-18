import sys
sys.setrecursionlimit(20000)

from time import time

from constants import *
from parser import parse
from env import add_to_env, env_find, make_env
from pretty_printer import pretty_print
from eval import *

def tagged_cons(head, tail):
    return (TYPE_CONS, (head, tail))

def tagged_head(l):
    if l[0] == TYPE_UNKNOWN:
        return (TYPE_UNKNOWN,)
    assert l[0] == TYPE_CONS
    return l[1][0]

def tagged_tail(l):
    if l[0] == TYPE_UNKNOWN:
        return (TYPE_UNKNOWN,)
    assert l[0] == TYPE_CONS
    return l[1][1]

lph_seen = {}
def loop_hash(l, seen = None):
    if seen == None:
        seen = {}
    if id(l) in lph_seen:
        return lph_seen[id(l)][1]
    if type(l) == type(tuple()):
        res = hash(tuple(loop_hash(u, seen) for u in l))
    elif type(l) == type(""):
        if "()" in l and not l.startswith(GVPRF):
            res = hash(l.split("()")[0])
        else:
            res = hash(l)
    else:
        res = hash(l)
    lph_seen[id(l)] = (l, res)
    return res

def loop_eq(l, m, seen = None):
    if seen == None:
        seen = {}
    if id(l) in seen:
        return seen[id(l)]
    if type(l) in [type(tuple()), type(list())]:
        r = len(l) == len(m) and all(loop_eq(u, v, seen) for (u, v) in zip(l, m))
    else:
        r = l == m
    seen[id(l)] = r
    return r

globalvars = {}
GVPRF = "globalvar()"
def value_ref(var):
    if var[0] == TYPE_FUNCTION and "()" in var[1][3]:
        return(var, (PARSED_IDENT, var[1][3]))
    globalvars[loop_hash(var)] = var
    return (var, (PARSED_IDENT, GVPRF + str(loop_hash(var))))

def specialize(expr, env):
    u = (expr, env)
    z = loop_hash(u)
    if z not in specialized:
        result, code = _specialize(expr, env)
        if is_known(result):
            result, code = value_ref(result)
        specialized[z] = (u, (result, code))
    r = specialized[z][1]
    #if type(r[0][0]) != type(0):
    #    print("*" * 80)
    #    print(expr, show(r[0][0]), r[0])
    return r

def _specialize(expr, env):
    #print(expr)
    if expr[0] == PARSED_INT:
        return ((TYPE_INT, expr[1]), expr)
    elif expr[0] == PARSED_CHAR:
        return ((TYPE_CHAR, expr[1]), expr)
    elif expr[0] == PARSED_IDENT:
        if "()" in expr[1] and expr[1] != "args()":
            ll = expr[1].split("()")
            assert(len(ll) == 2)
            u = int(ll[1])
            if expr[1].startswith(GVPRF):
                return (globalvars[u], expr)
            argnames, _, code, fenv = spenames[u]
            return ((TYPE_FUNCTION, (code, argnames[1:], fenv, argnames[0])), expr)
        return (env_find(env, expr[1]), expr)
    elif expr[0] == PARSED_CONSTANT:
        return (expr[1], expr)
    #print(expr)
    if expr[1][0][0] == PARSED_KEYWORD:
        return specialize_keyword(expr, env)
    else:
        return specialize_call(expr, env)

def specialize_let(env, bind_def, bind_value, is_recursive = False):
    if is_recursive:
        assert binding_is_func(bind_def), "Incorrect recursive binding"
    if bind_def[0] == PARSED_IDENT or is_call_to(bind_def, "cons"):
        value, code = specialize(bind_value, env)
        #return specialize_bind(env, bind_def, value, code)
        return bind(env, bind_def, value), code
    elif bind_def[0] == PARSED_CALL:
        if is_recursive:
            name = bind_def[1][0][1]
            frec = make_rec(env, [name], bind_def, bind_value)
            return add_to_env(env, name, (TYPE_FIXPOINT, (frec,), frec, name)), None
        return make_func_in_env(env, bind_def[1], bind_value), None
    raise Exception("Incorrect binding")

def specialize_let_star(env, bds, is_recursive = False):
    assert bds[0] == PARSED_CALL
    bds = bds[1]
    assert all(bd[0] == PARSED_CALL and len(bd[1]) == 2 for bd in bds)
    bind_defs = tuple(bd[1][0] for bd in bds)
    bind_values = tuple(bd[1][1] for bd in bds)
    if is_recursive:
        assert all(binding_is_func(bind_def) for bind_def in bind_defs)
    if not is_recursive:
        newenv = env
        cd = []
        for bind_def, bind_value in zip(bind_defs, bind_values):
            if not binding_is_func(bind_def):
                value, code = specialize(bind_value, env)
                newenv = bind(newenv, bind_def, value)
                cd.append(code)
            else:
                newenv = add_to_env(newenv, bind_def[1][0][1], make_func(env, bind_def[1], bind_value))
                cd.append(None)
        return newenv, tuple(cd)
    names = [bind_def[1][0][1] for bind_def in bind_defs]
    frecs = tuple(make_rec(env, names, bind_def, bind_value) for bind_def, bind_value in zip(bind_defs, bind_values))
    for i in range(len(names)):
        env = add_to_env(env, names[i], (TYPE_FIXPOINT, frecs, frecs[i], names[i]))
    return env, None

def make_let(env, bind_def, let_code, is_recursive, bind_value):
    if is_recursive:
        keyword = "letrec"
    else:
        keyword = "let"
    return (PARSED_CALL, ((PARSED_KEYWORD, keyword), bind_def, let_code, bind_value))

def make_let_star(env, bind_def, let_code, is_recursive, bind_value):
    if is_recursive:
        keyword = "letrec*"
    else:
        keyword = "let*"
    bd = tuple((a[1][0], cd) for a, cd in zip(bind_def[1], let_code))
    return (PARSED_CALL, ((PARSED_KEYWORD, keyword), (PARSED_CALL, bd), bind_value))

def merge_values(val1, val2):
    if val1[0] == TYPE_ERROR:
        return val2
    if val2[0] == TYPE_ERROR:
        return val1
    if val1[0] != val2[0]:
        return (TYPE_UNKNOWN,)
    if val1[0] in [TYPE_INT, TYPE_CHAR]:
        if val1[1] == val2[1]:
            return val1
        return (TYPE_UNKNOWN,)
    if val1[0] == TYPE_NIL:
        return val1
    if val1[0] == TYPE_CONS:
        return tagged_cons(merge_values(val1[1][0], val2[1][0]),
                           merge_values(val1[1][1], val2[1][1]))
    return (TYPE_UNKNOWN,)

def specialize_keyword(expr, env):
    keyword = expr[1][0][1]
    if keyword == "if":
        cond, code = specialize(expr[1][1], env)
        if cond[0] == TYPE_BOOL:
            if cond[1]:
                return specialize(expr[1][2], env)
            else:
                return specialize(expr[1][3], env)
        else:
            assert cond[0] == TYPE_UNKNOWN
            assert len(expr[1]) == 4, expr
            val1, code1 = specialize(expr[1][2], env)
            val2, code2 = specialize(expr[1][3], env)
            #print(val1, val2, merge_values(val1, val2))
            return merge_values(val1, val2), (PARSED_CALL, ((PARSED_KEYWORD, "if"), code, code1, code2))
    elif keyword == "let" or keyword == "letrec": # TODO
        newenv, let_code = specialize_let(env, expr[1][1], expr[1][2], keyword == "letrec")
        result, code = specialize(expr[1][3], newenv)
        return result, make_let(env, expr[1][1], let_code, keyword == "letrec", code)
    elif keyword == "let*" or keyword == "letrec*": # TODO
        newenv, let_code = specialize_let_star(env, expr[1][1], keyword == "letrec*")
        result, code = specialize(expr[1][2], newenv)
        return result, make_let_star(env, expr[1][1], let_code, keyword == "letrec*", code)

SPE_LIMIT = 200
spelimits = {}
specialized = {}
spe_changed = False
def specialize_loop():
    global spe_changed
    spe_changed = False
    #return False
    #for z in specialized:
    #    expr, env = specialized[z][0]
    #    #if expr[0] != PARSED_CALL:
    #    #    continue
    #    #print(expr)
    #    #run_specialize_call(expr, env)
    #    if spe_changed:
    #        return True
    #return False
    specialized.clear()
    for u in list(spenames.keys()):
        names, args, code, fenv = spenames[u]
        func = (TYPE_FUNCTION, (code, names[1:], fenv, names[0]))
        result, _, rcode = make_call(func, (PARSED_IDENT, names[0]), args)
        if not loop_eq(code, rcode):
            #print(names, code, rcode)
            spenames[u] = (names, args, rcode, fenv)
            return True
    return False

def run_specialize_call(expr, env):
    global spe_changed
    u = (expr, env)
    result, code = _specialize_call(expr, env)
    #print(code)
    if is_known(result):
        result, code = value_ref(result)
    z = loop_hash(u)
    if z not in specialized or not loop_eq(specialized[z][1], (result, code)):
        specialized[z] = (u, (result, code))
        spe_changed = True
    return result, code

def specialize_call(expr, env):
    """global spe_changed
    u = (expr, env)
    z = loop_hash(u)
    if z not in specialized:
        return run_specialize_call(expr, env)
    return specialized[z][1]"""
    return _specialize_call(expr, env)

spenames = {}
def _specialize_call(expr, env):
    func, func_code = specialize(expr[1][0], env)
    args = [specialize(expr[1][i], env) for i in range(1, len(expr[1]))]
    if func[0] == TYPE_UNKNOWN:
        return (TYPE_UNKNOWN,), (PARSED_CALL, ((func_code,) + tuple(arg[1] for arg in args)))
    if func[0] == TYPE_BUILTIN_FUNCTION:
        try:
            return func[1](*(arg[0] for arg in args)), func[2](*(arg[1] for arg in args))
        except AssertionError:
            return (TYPE_ERROR,), (PARSED_CALL, (func_code,) + tuple(arg[1] for arg in args))
    if func[0] == TYPE_FIXPOINT:
        func = eval_call(func[2][1], [(TYPE_FIXPOINT, func[1], f, func[3]) for f in func[1]])
    assert func[0] == TYPE_FUNCTION
    return make_call(func, func_code, args)[:2]

def make_call(func, func_code, args):
    if all(is_known(arg[0]) for arg in args):
        a = value_ref(eval_call(func[1], [arg[0] for arg in args]))
        return (a[0], a[1], a[1])
    h = loop_hash(func)
    #print(h, func[1][3])
    z = spelimits.get(h, {})
    spelimits[h] = z
    #print(spelimits)
    code, argnames, fenv, fname = func[1]
    newenv = fenv
    assert len(argnames) == len(args)
    #spelimits[h] = z + 1
    for i in range(len(args)):
        newenv = add_to_env(newenv, argnames[i], args[i][0])
    change = is_known(func)
    #if "()" in fname:
    #    print(fname, env[0][0], show(env[0][1]))
    if change and "()" in fname:
        fname = fname.split("()")[0]
        #print(fname)
    if change:
        hh = loop_hash((code, newenv))
        spenames[hh] = ((fname + "()" + str(hh),) + argnames, args, code, fenv) # But will be with specialized code later
        func_code = (PARSED_IDENT, fname + "()" + str(hh))
    lh = loop_hash(tuple(arg[0] for arg in args))
    if lh in z:
        if z[lh] == None:
            return ((TYPE_UNKNOWN,), (PARSED_CALL, ((func_code,) + tuple(arg[1] for arg in args))), code)
        return z[lh][0], (PARSED_CALL, ((func_code,) + tuple(arg[1] for arg in args))), z[lh][1]
    z[lh] = None
    if len(z) >= SPE_LIMIT:
        return ((TYPE_UNKNOWN,), (PARSED_CALL, ((func_code,) + tuple(arg[1] for arg in args))), code)
    result, rcode = specialize(code, newenv)
    if change:
        spenames[hh] = ((fname + "()" + str(hh),) + argnames, args, rcode, fenv)
    z[lh] = (result, rcode)
    return (result, (PARSED_CALL, ((func_code,) + tuple(arg[1] for arg in args))), rcode)

def bound_names(bind_def):
    if binding_is_func(bind_def):
        return [bind_def[1][0][1]]
    elif bind_def[0] == PARSED_IDENT:
        return [bind_def[1]]
    else: # (cons a b)
        return bound_names(bind_def[1][1]) + bound_names(bind_def[1][2])

def bound_names_star(bd_star):
    s = []
    for e in bd_star:
        s += bound_names(e[1][0])
    return s

def var_uses(expr, var): # Returns number of times used, number of times used in function (can't be inlined there)
    if expr[0] == PARSED_INT or expr[0] == PARSED_CHAR or expr[0] == PARSED_CONSTANT:
        return (0, 0)
    elif expr[0] == PARSED_IDENT:
        return (1, 0) if expr[1] == var else (0, 0)
    elif expr[0] == PARSED_CALL:
        #if expr[1] == None or expr[1][0] == None:
        #    print(expr)
        if expr[1][0][0] == PARSED_KEYWORD:
            s, t = 0, 0
            if expr[1][0][1] == "let":
                if (var not in bound_names(expr[1][1])):
                    u, v = var_uses(expr[1][3], var)
                    s += u
                    t += v
                if binding_is_func(expr[1][1]):
                    if ((PARSED_IDENT, var) not in expr[1][1][1][1:]):
                        u, v = var_uses(expr[1][2], var)
                        t += u + v
                else:
                    u, v = var_uses(expr[1][2], var)
                    s += u
                    t += v
                return s, t
            elif expr[1][0][1] == "letrec":
                if (var not in bound_names(expr[1][1])):
                    u, v = var_uses(expr[1][3], var)
                    s += u
                    t += v
                if ((PARSED_IDENT, var) not in expr[1][1][1]):
                    u, v = var_uses(expr[1][2], var)
                    t += u + v
                return s, t
            elif expr[1][0][1] == "let*":
                if (var not in bound_names_star(expr[1][1][1])):
                    u, v = var_uses(expr[1][2], var)
                    s += u
                    t += v
                for e in expr[1][1][1]:
                    if binding_is_func(e[1][0]):
                        if (((PARSED_IDENT, var)) not in e[1][0][1][1:]):
                            u, v = var_uses(e[1][1], var)
                            t += u + v
                    else:
                        u, v = var_uses(e[1][1], var)
                        s += u
                        t += v
                return s, t
            elif expr[1][0][1] == "letrec*":
                if (var not in bound_names_star(expr[1][1][1])):
                    u, v = var_uses(expr[1][2], var)
                    s += u
                    t += v
                for e in expr[1][1][1]:
                    if (((PARSED_IDENT, var)) not in e[1][0][1]):
                        u, v = var_uses(e[1][1], var)
                        t += u + v
                return s, t
            elif expr[1][0][1] == "if":
                s, t = var_uses(expr[1][1], var)
                u1, v1 = var_uses(expr[1][2], var)
                u2, v2 = var_uses(expr[1][3], var)
                return s + max(u1, u2), t + max(v1, v2)
        else:
            s, t = 0, 0
            for e in expr[1]:
                u, v = var_uses(e, var)
                s += u
                t += v
            return s, t

def replace_var(expr, var, replacement):
    if expr[0] == PARSED_INT or expr[0] == PARSED_CHAR or expr[0] == PARSED_CONSTANT or expr[0] == PARSED_KEYWORD:
        return expr
    elif expr[0] == PARSED_IDENT:
        return replacement if expr[1] == var else expr
    elif expr[0] == PARSED_CALL:
        if expr[1][0][0] == PARSED_KEYWORD:
            if expr[1][0][1] == "let":
                if (var not in bound_names(expr[1][1])):
                    smp = replace_var(expr[1][3], var, replacement)
                else:
                    smp = expr[1][3]
                if (not binding_is_func(expr[1][1])) or ((PARSED_IDENT, var) not in expr[1][1][1][1:]):
                    bind_to = replace_var(expr[1][2], var, replacement)
                else:
                    bind_to = expr[1][2]
                return (PARSED_CALL, ((PARSED_KEYWORD, "let"), expr[1][1], bind_to, smp))
            elif expr[1][0][1] == "letrec":
                if (var not in bound_names(expr[1][1])):
                    smp = replace_var(expr[1][3], var, replacement)
                else:
                    smp = expr[1][3]
                if (PARSED_IDENT, var) not in expr[1][1][1]:
                    bind_to = replace_var(expr[1][2], var, replacement)
                else:
                    bind_to = expr[1][2]
                return (PARSED_CALL, ((PARSED_KEYWORD, "letrec"), expr[1][1], bind_to, smp))
            elif expr[1][0][1] == "let*":
                if (var not in bound_names_star(expr[1][1][1])):
                    smp = replace_var(expr[1][2], var, replacement)
                else:
                    smp = expr[1][2]
                nb = tuple((PARSED_CALL, (e[1][0],
                                replace_var(e[1][1], var, replacement) if ((not binding_is_func(e[1][0])) or ((PARSED_IDENT, var) not in e[1][0][1][1:])) else e[1][1]))
                           for e in expr[1][1][1])
                return (PARSED_CALL, ((PARSED_KEYWORD, "let*"), (PARSED_CALL, nb), smp))
            elif expr[1][0][1] == "letrec*":
                if (var not in bound_names_star(expr[1][1][1])):
                    smp = replace_var(expr[1][2], var, replacement)
                else:
                    smp = expr[1][2]
                nb = tuple((PARSED_CALL, (e[1][0],
                                replace_var(e[1][1], var, replacement) if ((PARSED_IDENT, var) not in e[1][0][1]) else e[1][1]))
                           for e in expr[1][1][1])
                return (PARSED_CALL, ((PARSED_KEYWORD, "letrec*"), (PARSED_CALL, nb), smp))
    #print(expr, var, replacement)
    return (PARSED_CALL, tuple(replace_var(e, var, replacement) for e in expr[1]))

def inline_access(expr, var, hvar, tvar):
    if expr[0] != PARSED_CALL:
        return expr
    elif expr[0] == PARSED_CALL:
        if expr[1] == ((PARSED_IDENT, "head"), (PARSED_IDENT, var)):
            return (PARSED_IDENT, hvar)
        elif expr[1] == ((PARSED_IDENT, "tail"), (PARSED_IDENT, var)):
            return (PARSED_IDENT, tvar)
        if expr[1][0][0] == PARSED_KEYWORD:
            if expr[1][0][1] == "let":
                if (var not in bound_names(expr[1][1])):
                    smp = inline_access(expr[1][3], var, hvar, tvar)
                else:
                    smp = expr[1][3]
                if (not binding_is_func(expr[1][1])) or ((PARSED_IDENT, var) not in expr[1][1][1][1:]):
                    bind_to = inline_access(expr[1][2], var, hvar, tvar)
                else:
                    bind_to = expr[1][2]
                return (PARSED_CALL, ((PARSED_KEYWORD, "let"), expr[1][1], bind_to, smp))
            elif expr[1][0][1] == "letrec":
                if (var not in bound_names(expr[1][1])):
                    smp = inline_access(expr[1][3], var, hvar, tvar)
                else:
                    smp = expr[1][3]
                if (PARSED_IDENT, var) not in expr[1][1][1]:
                    bind_to = inline_access(expr[1][2], var, hvar, tvar)
                else:
                    bind_to = expr[1][2]
                return (PARSED_CALL, ((PARSED_KEYWORD, "letrec"), expr[1][1], bind_to, smp))
            elif expr[1][0][1] == "let*":
                if (var not in bound_names_star(expr[1][1][1])):
                    smp = inline_access(expr[1][2], var, hvar, tvar)
                else:
                    smp = expr[1][2]
                nb = tuple((PARSED_CALL, (e[1][0],
                                inline_acess(e[1][1], var, hvar, tvar) if ((not binding_is_func(e[1][0])) or ((PARSED_IDENT, var) not in e[1][0][1][1:])) else e[1][1]))
                           for e in expr[1][1][1])
                return (PARSED_CALL, ((PARSED_KEYWORD, "let*"), (PARSED_CALL, nb), smp))
            elif expr[1][0][1] == "letrec*":
                if (var not in bound_names_star(expr[1][1][1])):
                    smp = inline_access(expr[1][2], var, hvar, tvar)
                else:
                    smp = expr[1][2]
                nb = tuple((PARSED_CALL, (e[1][0],
                                inline_access(e[1][1], var, hvar, tvar) if ((PARSED_IDENT, var) not in e[1][0][1]) else e[1][1]))
                           for e in expr[1][1][1])
                return (PARSED_CALL, ((PARSED_KEYWORD, "letrec*"), (PARSED_CALL, nb), smp))
    return (PARSED_CALL, tuple(inline_access(e, var, hvar, tvar) for e in expr[1]))

def is_var_used(expr, var):
    return var_uses(expr, var) != (0, 0)

"""def is_var_used(expr, var):
    if expr[0] == PARSED_INT or expr[0] == PARSED_CHAR or expr[0] == PARSED_CONSTANT:
        return False
    elif expr[0] == PARSED_IDENT:
        return expr[1] == var
    elif expr[0] == PARSED_CALL:
        if expr[1][0][0] == PARSED_KEYWORD:
            if expr[1][0][1] == "let":
                if (var not in bound_names(expr[1][1])) and is_var_used(expr[1][3], var):
                    return True
                if binding_is_func(expr[1][1]):
                    return ((PARSED_IDENT, var) not in expr[1][1][1][1:]) and is_var_used(expr[1][2], var)
                else:
                    return is_var_used(expr[1][2], var)
            elif expr[1][0][1] == "letrec":
                if (var not in bound_names(expr[1][1])) and is_var_used(expr[1][3]):
                    return True
                return ((PARSED_IDENT, var) not in expr[1][1][1]) and is_var_used(expr[1][2], var)
            elif expr[1][0][1] == "let*":
                if (var not in bound_names_star(expr[1][1][1])) and is_var_used(expr[1][2], var):
                    return True
                for e in expr[1][1][1]:
                    if binding_is_func(e[1][0]):
                        if (((PARSED_IDENT, var)) not in e[1][0][1][1:]) and is_var_used(e[1][1], var):
                            return True
                    else:
                        if is_var_used(e[1][1], var):
                            return True
                return False
            elif expr[1][0][1] == "letrec*":
                if (var not in bound_names_star(expr[1][1][1])) and is_var_used(expr[1][2], var):
                    return True
                for e in expr[1][1][1]:
                    if binding_is_func(e[1][0]):
                        if (((PARSED_IDENT, var)) not in e[1][0][1]) and is_var_used(e[1][1], var):
                            return True
                    else:
                        if is_var_used(e[1][1], var):
                            return True
                return False
            elif expr[1][0][1] == "if":
                return is_var_used(expr[1][1], var) or is_var_used(expr[1][2], var) or is_var_used(expr[1][3], var)
        else:
            return any((is_var_used(e, var) for e in expr[1]))"""

def destroy_pm(expr):
    if expr[0] != PARSED_CALL:
        return expr
    if expr[1][0][0] == PARSED_KEYWORD:
        if expr[1][0][1] == "let":
            if is_call_to(expr[1][1], "cons"):
                nm = "cons()" + str(hash(expr))
                return (PARSED_CALL, ((PARSED_KEYWORD, "let"), (PARSED_IDENT, nm), destroy_pm(expr[1][2]),
                        destroy_pm((PARSED_CALL, ((PARSED_KEYWORD, "let*"),
                                        (PARSED_CALL, ((PARSED_CALL, (expr[1][1][1][1], (PARSED_CALL, ((PARSED_IDENT, "head"), (PARSED_IDENT, nm))))),
                                                        (PARSED_CALL, (expr[1][1][1][2], (PARSED_CALL, ((PARSED_IDENT, "tail"), (PARSED_IDENT, nm))))))),
                                        expr[1][3])))))
            return (PARSED_CALL, (expr[1][0], expr[1][1], destroy_pm(expr[1][2]), destroy_pm(expr[1][3])))
        elif expr[1][0][1] == "let*":
            is_cons = []
            for e in expr[1][1][1]:
                is_cons.append(is_call_to(e[1][0], "cons"))
            if not any(is_cons):
                return (PARSED_CALL, ((PARSED_KEYWORD, "let*"),
                                      (PARSED_CALL, tuple((PARSED_CALL, (e[1][0], destroy_pm(e[1][1]))) for e in expr[1][1][1])),
                                      destroy_pm(expr[1][2])))
            names = ["cons(" + str(i) + ")" + str(hash(expr)) for i in range(len(expr[1][1][1]))]
            let1 = (PARSED_CALL, tuple((PARSED_CALL, ((PARSED_IDENT, names[i]), destroy_pm(expr[1][1][1][i][1][1]))) for i in range(len(is_cons)) if is_cons[i]))
            let2 = []
            for i in range(len(is_cons)):
                if not is_cons[i]:
                    let2.append(expr[1][1][1][i])
                else:
                    let2.append((PARSED_CALL, (expr[1][1][1][i][1][0][1][1], (PARSED_CALL, ((PARSED_IDENT, "head"), (PARSED_IDENT, names[i]))))))
                    let2.append((PARSED_CALL, (expr[1][1][1][i][1][0][1][2], (PARSED_CALL, ((PARSED_IDENT, "tail"), (PARSED_IDENT, names[i]))))))
            return (PARSED_CALL, ((PARSED_KEYWORD, "let*"), let1,
                                  destroy_pm((PARSED_CALL, ((PARSED_KEYWORD, "let*"), (PARSED_CALL, tuple(let2)), expr[1][2])))))
    return (PARSED_CALL, tuple(destroy_pm(e) for e in expr[1]))

def destroy_lets(expr):
    if expr[0] != PARSED_CALL:
        return expr
    if expr[1][0][0] == PARSED_KEYWORD:
        if expr[1][0][1] in ("let", "letrec"):
            smp = destroy_lets(expr[1][3])
            u = destroy_lets(expr[1][2])
            bd = bound_names(expr[1][1])
            if expr[1][1][0] == PARSED_IDENT and var_uses(smp, expr[1][1][1]) == (1, 0):
                return replace_var(smp, expr[1][1][1], u)
            if u[0] == PARSED_IDENT:
                return replace_var(smp, expr[1][1][1], u)
            for bn in bd:
                if is_var_used(smp, bn):
                    return (PARSED_CALL, expr[1][:2] + (u, smp))
            return smp
        elif expr[1][0][1] == "let*":
            smp = destroy_lets(expr[1][2])
            is_useful = []
            for e in expr[1][1][1]:
                iu = False
                for n in bound_names(e[1][0]):
                    if is_var_used(smp, n):
                        iu = True
                        break
                is_useful.append(iu)
            if sum(is_useful) == 0:
                return smp
            elif sum(is_useful) == 1:
                i = is_useful.index(True)
                b = expr[1][1][1][i]
                return (PARSED_CALL, ((PARSED_KEYWORD, "let"), b[1][0], b[1][1], smp))
            else:
                return (PARSED_CALL, ((PARSED_KEYWORD, "let*"), (PARSED_CALL, tuple(expr[1][1][1][i] for i in range(len(is_useful)) if is_useful[i])), smp))
        elif expr[1][0][1] == "letrec*":
            smp = destroy_lets(expr[1][2])
            is_useful = []
            for e in expr[1][1][1]:
                iu = False
                for n in bound_names(e[1][0]):
                    if is_var_used(smp, n):
                        iu = True
                        break
                is_useful.append(iu)
            if any(is_useful):
                return (PARSED_CALL, (expr[1][:2] + (smp,)))
            return smp
    return (PARSED_CALL, tuple(destroy_lets(e) for e in expr[1]))

def destroy_let_star(expr):
    if expr[0] != PARSED_CALL:
        return expr
    if expr[1][0][0] == PARSED_KEYWORD:
        if expr[1][0][1] == "let*":
            smp = destroy_let_star(expr[1][2])
            for i in range(len(expr[1][1][1])):
                e = expr[1][1][1][i]
                if e[1][0][0] != PARSED_IDENT:
                    continue
                for j in range(len(expr[1][1][1])):
                    if i == j: continue
                    if is_var_used(expr[1][1][1][j][1][1], e[1][0][1]):
                        break
                else: # It is safe to get this one out
                    return (PARSED_CALL, ((PARSED_KEYWORD, "let"), e[1][0], e[1][1],
                                destroy_let_star((PARSED_CALL, ((PARSED_KEYWORD, "let*"),
                                            (PARSED_CALL, tuple(expr[1][1][1][j] for j in range(len(expr[1][1][1])) if j != i)),
                                            smp)))))
            # No one can be extracted
            # Check if the let* was empty
            if len(expr[1][1][1]) == 0:
                return smp
            return (PARSED_CALL, ((PARSED_KEYWORD, "let*"), expr[1][1], smp))
    return (PARSED_CALL, tuple(destroy_let_star(e) for e in expr[1]))

def is_fct_used_no_call(expr, var):
    if expr[0] == PARSED_INT or expr[0] == PARSED_CHAR or expr[0] == PARSED_CONSTANT:
        return False
    elif expr[0] == PARSED_IDENT:
        return expr[1] == var
    elif expr[0] == PARSED_CALL:
        if expr[1][0][0] == PARSED_KEYWORD:
            if expr[1][0][1] == "let":
                if (var not in bound_names(expr[1][1])) and is_fct_used_no_call(expr[1][3], var):
                    return True
                if binding_is_func(expr[1][1]):
                    return ((PARSED_IDENT, var) not in expr[1][1][1][1:]) and is_fct_used_no_call(expr[1][2], var)
                else:
                    return is_fct_used_no_call(expr[1][2], var)
            elif expr[1][0][1] == "letrec":
                if (var not in bound_names(expr[1][1])) and is_fct_used_no_call(expr[1][3], var):
                    return True
                return ((PARSED_IDENT, var) not in expr[1][1][1]) and is_fct_used_no_call(expr[1][2], var)
            elif expr[1][0][1] == "let*":
                if (var not in bound_names_star(expr[1][1][1])) and is_fct_used_no_call(expr[1][2], var):
                    return True
                for e in expr[1][1][1]:
                    if binding_is_func(e[1][0]):
                        if (((PARSED_IDENT, var)) not in e[1][0][1][1:]) and is_fct_used_no_call(e[1][1], var):
                            return True
                    else:
                        if is_fct_used_no_call(e[1][1], var):
                            return True
                return False
            elif expr[1][0][1] == "letrec*":
                if (var not in bound_names_star(expr[1][1][1])) and is_fct_used_no_call(expr[1][2]):
                    return True
                for e in expr[1][1][1]:
                    if binding_is_func(e[1][0]):
                        if (((PARSED_IDENT, var)) not in e[1][0][1]) and is_fct_used_no_call(e[1][1], var):
                            return True
                    else:
                        if is_fct_used_no_call(e[1][1], var):
                            return True
                return False
            elif expr[1][0][1] == "if":
                return is_fct_used_no_call(expr[1][1], var) or is_fct_used_no_call(expr[1][2], var) or is_fct_used_no_call(expr[1][3], var)
        else:
            if expr[1][0] == (PARSED_IDENT, var):
                return any((is_fct_used_no_call(e, var) for e in expr[1][1:]))
            return any((is_fct_used_no_call(e, var) for e in expr[1]))


def keep_args(fct_name, expr, ka):
    if expr[0] != PARSED_CALL:
        return expr
    if expr[1][0] == (PARSED_IDENT, fct_name):
        e = tuple(keep_args(fct_name, expr[1][i], ka) for i in range(len(expr[1])) if ka[i])
    else:
        e = tuple(keep_args(fct_name, ee, ka) for ee in expr[1])
    return (PARSED_CALL, e)

def inline_func(fct_name, expr, fcode):
    if expr[0] != PARSED_CALL:
        return expr
    if expr[1][0] == (PARSED_IDENT, fct_name[0]):
        bd = tuple((PARSED_CALL, ((PARSED_IDENT, fct_name[i]), inline_func(fct_name, expr[1][i], fcode))) for i in range(1, len(expr[1])))
        return (PARSED_CALL, ((PARSED_KEYWORD, "let*"), (PARSED_CALL, bd), fcode))
    else:
        return (PARSED_CALL, tuple(inline_func(fct_name, ee, fcode) for ee in expr[1]))

def decons(fct_name, expr, p, keep):
    if expr[0] != PARSED_CALL:
        return expr
    #print(expr)
    if expr[1][0] == (PARSED_IDENT, fct_name):
        e1 = tuple(decons(fct_name, expr[1][i], p, keep) for i in range(p + 1))
        e3 = tuple(decons(fct_name, expr[1][i], p, keep) for i in range(p + 2, len(expr[1])))
        cn = loop_hash(expr)
        nms = ("head()" + str(cn), "tail()" + str(cn))
        e2 = tuple((PARSED_IDENT, nms[i]) for i in range(2) if keep[i])
        ee = e1 + e2 + e3
        return (PARSED_CALL, ((PARSED_KEYWORD, "let"), (PARSED_CALL, ((PARSED_IDENT, "cons"), (PARSED_IDENT, nms[0]), (PARSED_IDENT, nms[1]))),
                              decons(fct_name, expr[1][p + 1], p, keep),
                              (PARSED_CALL, ee)))
    else:
        return (PARSED_CALL, tuple(decons(fct_name, ee, p, keep) for ee in expr[1]))

def kill_globalvars(expr):
    if expr[0] == PARSED_IDENT:
        nm = expr[1]
        if nm.startswith(GVPRF):
            u = int(nm[len(GVPRF):])
            value = globalvars[u]
            if value[0] == TYPE_INT:
                return (PARSED_INT, value[1])
            elif value[0] == TYPE_CHAR:
                return (PARSED_CHAR, value[1])
            elif value[0] == TYPE_BOOL:
                return (PARSED_IDENT, "true" if value[1] else "false")
            #elif value[0] == TYPE_FUNCTION:
            #    return (PARSED_IDENT, "g()" + value[1][3])
            #elif value[0] == TYPE_FIXPOINT:
            #    return (PARSED_IDENT, "g()" + value[3])
            elif value[0] == TYPE_NIL:
                return (PARSED_IDENT, "[]")
    elif expr[0] == PARSED_CALL:
        return (PARSED_CALL, tuple(kill_globalvars(e) for e in expr[1]))
    return expr

varcount = 0
def rename_vars(expr, nd):
    global varcount
    if expr[0] == PARSED_IDENT:
        if expr[1] in nd and nd[expr[1]] != []:
            return (PARSED_IDENT, nd[expr[1]][-1])
        return expr
    if expr[0] in (PARSED_CONSTANT, PARSED_INT, PARSED_CHAR, PARSED_KEYWORD):
        return expr
    if expr[1][0][0] == PARSED_KEYWORD:
        if expr[1][0][1] == "let" or expr[1][0][1] == "letrec":
            bn = bound_names(expr[1][1])
            for var in bn:
                z = nd.get(var, [])
                nd[var] = z
                z.append(var + "()" + str(varcount))
                varcount += 1
            smp = rename_vars(expr[1][3], nd)
            bd = rename_vars(expr[1][1], nd)
            if expr[1][0][1] == "let":
                for var in bn:
                    nd[var].pop()
            if binding_is_func(expr[1][1]):
                for _, var in expr[1][1][1][1:]:
                    z = nd.get(var, [])
                    nd[var] = z
                    z.append(var + "()" + str(varcount))
                    varcount += 1
                e = rename_vars(expr[1][2], nd)
                bd = rename_vars(bd, nd)
                for _, var in expr[1][1][1][1:]:
                    nd[var].pop()
            else:
                e = rename_vars(expr[1][2], nd)
            if expr[1][0][1] == "letrec":
                for var in bn:
                    nd[var].pop()
            return (PARSED_CALL, (expr[1][0], bd, e, smp))
        elif expr[1][0][1] == "let*":
            bn = bound_names_star(expr[1][1][1])
            for var in bn:
                z = nd.get(var, [])
                nd[var] = z
                z.append(var + "()" + str(varcount))
                varcount += 1
            smp = rename_vars(expr[1][2], nd)
            bd = tuple((rename_vars(e[1][0], bd), e[1][1]) for e in expr[1][1][1])
            for var in bn:
                nd[var].pop()
            bdd = []
            for e in bd:
                if binding_is_func(e[1][0]):
                    for _, var in e[1][0][1][1:]:
                        z = nd.get(var, [])
                        nd[var] = z
                        z.append(var + "()" + str(varcount))
                        varcount += 1
                    nb = (rename_vars(e[1][0], nd), rename_vars(e[1][1], nd))
                    bdd.append(nb)
                    for _, var in e[1][0][1][1:]:
                        nd[var].pop()
                else:
                    bdd.append((e[1][0], rename_vars(e[1][1], nd)))
            return (PARSED_CALL, ((PARSED_KEYWORD, "let*"), (PARSED_CALL, tuple(bdd)), smp))
        elif expr[1][0][1] == "letrec*":
            bn = bound_names_star(expr[1][1][1])
            for var in bn:
                z = nd.get(var, [])
                nd[var] = z
                z.append(var + "()" + str(varcount))
                varcount += 1
            smp = rename_vars(expr[1][2], nd)
            bdd = []
            for e in expr[1][1][1]:
                if binding_is_func(e[1][0]):
                    for _, var in e[1][0][1][1:]:
                        z = nd.get(var, [])
                        nd[var] = z
                        z.append(var + "()" + str(varcount))
                        varcount += 1
                    nb = (rename_vars(e[1][0], nd), rename_vars(e[1][1], nd))
                    bdd.append(nb)
                    for _, var in e[1][0][1][1:]:
                        nd[var].pop()
                else:
                    bdd.append((e[1][0], rename_vars(e[1][1], nd)))
            for var in bn:
                nd[var].pop()
            return (PARSED_CALL, ((PARSED_KEYWORD, "letrec*"), (PARSED_CALL, tuple(bdd)), smp))
    return (PARSED_CALL, tuple(rename_vars(e, nd) for e in expr[1]))

def change_all_names(funcs):
    global varcount
    newfuncs = []
    nd = {}
    for fct_nm, fct_code, fct_args in funcs:
        nfn = [fct_nm[0]]
        for var in fct_nm[1:]:
            z = nd.get(var, [])
            nd[var] = z
            nn = var + "()" + str(varcount)
            z.append(nn)
            nfn.append(nn)
            varcount += 1
        newcode = rename_vars(fct_code, nd)
        for var in fct_nm[1:]:
            nd[var].pop()
        newfuncs.append((tuple(nfn), newcode, fct_args))
    return newfuncs

def is_string_int(s):
    try:
        a = int(s)
        return True
    except:
        return False

def rename_correct_var(name, d, dr):
    if name in d:
        return d[name]
    l = name.split("()")
    if len(l) == 1:
        d[name] = name
        dr[name] = name
        return name
    while is_string_int(l[-1]):
        l.pop()
    newname = "-".join(l) + "-"
    u = 1
    while newname + str(u) in dr:
        u += 1
    nn = newname + str(u)
    d[name] = nn
    dr[nn] = name
    return nn

def rename_correct(expr, d, dr):
    if expr[0] == PARSED_IDENT:
        return (PARSED_IDENT, rename_correct_var(expr[1], d, dr))
    elif expr[0] != PARSED_CALL:
        return expr
    return (PARSED_CALL, tuple(rename_correct(e, d, dr) for e in expr[1]))

def rename_correct_name(nm, d, dr):
    return tuple(rename_correct_var(n, d, dr) for n in nm)

def simpl_cons(expr, cs):
    global varcount
    if expr[0] != PARSED_CALL:
        return expr
    #print(expr)
    if expr[1][0][1] == "head":
        sp = simpl_cons(expr[1][1], cs)
        if sp[0] == PARSED_IDENT and sp[1] in cs:
            return (PARSED_IDENT, cs[sp[1]][0])
        elif sp[0] == PARSED_CALL and sp[1][0][1] == "cons":
            return sp[1][1]
        else:
            return (PARSED_CALL, ((PARSED_IDENT, "head"), sp))
    elif expr[1][0][1] == "tail":
        sp = simpl_cons(expr[1][1], cs)
        if sp[0] == PARSED_IDENT and sp[1] in cs:
            return (PARSED_IDENT, cs[sp[1]][1])
        elif sp[0] == PARSED_CALL and sp[1][0][1] == "cons":
            return sp[1][2]
        else:
            return (PARSED_CALL, ((PARSED_IDENT, "tail"), sp))
    elif expr[1][0][1] == "let":
        bv = simpl_cons(expr[1][2], cs)
        if bv[0] == PARSED_CALL and bv[1][0][1] == "cons" and expr[1][1][0] == PARSED_IDENT:
            nh = "head()" + str(varcount)
            nt = "tail()" + str(varcount)
            hb, ht = True, True
            if bv[1][1][0] == PARSED_IDENT:
                nh = bv[1][1][1]
                hb = False
            if bv[1][2][0] == PARSED_IDENT:
                nt = bv[1][2][1]
                tb = False
            if hb and ht:
                let1 = ((PARSED_KEYWORD, "let*"),
                                  (PARSED_CALL, ((PARSED_CALL, ((PARSED_IDENT, nh), bv[1][1])), (PARSED_CALL, ((PARSED_IDENT, nt), bv[1][2])))))
            elif hb and not ht:
                let1 = ((PARSED_KEYWORD, "let"), (PARSED_IDENT, nh), bv[1][1])
            elif ht and not hb:
                let1 = ((PARSED_KEYWORD, "let"), (PARSED_IDENT, nt), bv[1][2])
            else:
                let1 = None
            varcount += 1
            cs[expr[1][1][1]] = (nh, nt)
            e = simpl_cons(expr[1][3], cs)
            del cs[expr[1][1][1]]
            ee = (PARSED_CALL, ((PARSED_KEYWORD, "let"), (PARSED_IDENT, expr[1][1][1]),
                                   (PARSED_CALL, ((PARSED_IDENT, "cons"), (PARSED_IDENT, nh), (PARSED_IDENT, nt))),
                                   e))
            if let1 == None:
                return ee
            return (PARSED_CALL, let1 + (ee,))
        else:
            return (PARSED_CALL, ((PARSED_KEYWORD, "let"), expr[1][1], bv, simpl_cons(expr[1][3], cs)))
    return (PARSED_CALL, tuple(simpl_cons(e, cs) for e in expr[1]))
    

def remove_args(funcs):
    newfuncs = change_all_names(funcs)
    changed = True
    loopcount = 0
    while changed and loopcount <= 10:
        #loopcout += 1
        #print(len(newfuncs))
        changed = False
        # Step 1: remove args
        ch = []
        for fct_nm, fct_code, fct_args in newfuncs:
            if any(is_fct_used_no_call(e, fct_nm[0]) for _, e, _ in newfuncs):
                ch.append(None)
                continue
            ka = tuple(i == 0 or is_var_used(fct_code, fct_nm[i]) for i in range(len(fct_nm)))
            if all(ka):
                ch.append(None)
                continue
            ch.append(ka)
        #print(ch)
        for i in range(len(ch)):
            if ch[i] == None:
                continue
            changed = True
            for j in range(len(newfuncs)):
                fct_name, fct_code, fct_args = newfuncs[j]
                newfuncs[j] = (fct_name, keep_args(newfuncs[i][0][0], fct_code, ch[i]), fct_args)
            fct_name, fct_code, fct_args = newfuncs[i]
            newfuncs[i] = tuple(fct_name[p] for p in range(len(fct_name)) if ch[i][p]), fct_code, tuple(fct_args[p] for p in range(len(fct_args)) if ch[i][p+1])

        # Step 2: destroy pattern matching
        for i in range(len(newfuncs)):
            fct_name, fct_code, fct_args = newfuncs[i]
            e = destroy_pm(fct_code)
            changed = changed or e != fct_code
            newfuncs[i] = fct_name, e, fct_args

        # Step 3: destroy let*s that can be
        for i in range(len(newfuncs)):
            fct_name, fct_code, fct_args = newfuncs[i]
            e = destroy_let_star(fct_code)
            changed = changed or e != fct_code
            newfuncs[i] = fct_name, e, fct_args
        
        # Step 4: destroy useless lets
        for i in range(len(newfuncs)):
            fct_name, fct_code, fct_args = newfuncs[i]
            e = destroy_lets(fct_code)
            changed = changed or e != fct_code
            newfuncs[i] = fct_name, e, fct_args

        # Step 5: delete useless functions
        useful = []
        for fct_nm, _, _ in newfuncs:
            useful.append(fct_nm[0] == "main" or any(is_var_used(e, fct_nm[0]) for _, e, _ in newfuncs))
        newfuncs = [newfuncs[i] for i in range(len(newfuncs)) if useful[i]]

        # Step 6: kill globalvars
        for i in range(len(newfuncs)):
            fct_name, fct_code, fct_args = newfuncs[i]
            newfuncs[i] = fct_name, kill_globalvars(fct_code), fct_args

        # Step 7: raise arity -> if arg is always a cons, de-cons it; but only one in each function at a time (to get the delete args optimisation)
        for i in range(len(newfuncs)):
            fct_name, fct_code, fct_args = newfuncs[i]
            if any(is_fct_used_no_call(e, fct_name[0]) for _, e, _ in newfuncs):
                continue
            for p in range(len(fct_args)):
                if fct_args[p][0] == TYPE_CONS:
                    break
            else:
                continue
            if len(fct_args) >= 10:
                continue
            changed = True
            nm = fct_name[p + 1]
            argc = fct_args[p][1]
            keep = [True, True]
            names = [nm + "()h", nm + "()t"]
            for k in range(2):
                if is_known(argc[k]):
                    name = value_ref(argc[k])[1][1]
                    names[k] = name
                    keep[k] = False
            fct_name = fct_name[:p+1] + tuple(names[k] for k in range(2) if keep[k]) + fct_name[p+2:]
            fct_args = fct_args[:p] + tuple(argc[k] for k in range(2) if keep[k]) + fct_args[p+1:]
            newfuncs[i] = fct_name, (PARSED_CALL, ((PARSED_KEYWORD, "let"), (PARSED_IDENT, nm),
                                                   (PARSED_CALL, ((PARSED_IDENT, "cons"), (PARSED_IDENT, names[0]), (PARSED_IDENT, names[1]))),
                                                   inline_access(fct_code, nm, names[0], names[1]))), fct_args
            #if fct_name[0].startswith("eval_main"):
            #    print(fct_name, nm, argc)
            #    print("*"*80)
            for j in range(len(newfuncs)):
                fname, fcode, fargs = newfuncs[j]
                newfuncs[j] = fname, decons(fct_name[0], fcode, p, tuple(keep)), fargs

        # Step 8: inline some functions
        for i in range(len(newfuncs)):
            fname, fcode, fargs = newfuncs[i]
            should_inline = not is_var_used(fcode, fname[0]) # Don't inline recursive functions
            for arg in fname[1:]:
                u, v = var_uses(fcode, arg)
                #print(u, v, end = "/")
                if u + v > 1:
                    should_inline = False
                    break
            #print(fname, fcode, should_inline)
            if should_inline:
                for j in range(len(newfuncs)):
                    fct_name, fct_code, fct_args = newfuncs[j]
                    e = inline_func(fname, fct_code, fcode)
                    changed = changed or e != fct_code
                    newfuncs[j] = fct_name, e, fct_args

        # Step 9: simplify (head (cons a b)) and the like
        for i in range(len(newfuncs)):
            fct_name, fct_code, fct_args = newfuncs[i]
            e = simpl_cons(fct_code, {})
            changed = changed or e != fct_code
            newfuncs[i] = fct_name, e, fct_args

        #for nf in newfuncs:
        #    print(nf[0], print_expr(nf[1], []))
        #print("-"*80)

    d = {}
    dr = {}
    for i in range(len(newfuncs)):
        fct_name, fct_code, fct_args = newfuncs[i]
        e = rename_correct(fct_code, d, dr)
        nname = rename_correct_name(fct_name, d, dr)
        newfuncs[i] = nname, e, fct_args
    return newfuncs, d, dr

def make_func_graph(funcs):
    return [[i for i in range(len(funcs)) if is_var_used(funcs[i][1], fct_nm[0])] for fct_nm, _, _ in funcs]

def transpose(graph):
    t = [[] for i in range(len(graph))]
    for i in range(len(graph)):
        for j in graph[i]:
            t[j].append(i)
    return t

def pp(graph, seen, l, u):
    if seen[u]: return
    seen[u] = True
    for v in graph[u]:
        pp(graph, seen, l, v)
    l.append(u)

def cfc(graph):
    seen = [False] * len(graph)
    l = []
    for u in range(len(graph)):
        pp(graph, seen, l, u)
    trans = transpose(graph)
    lcfc = []
    seen = [False] * len(graph)
    for i in range(len(l) - 1, -1, -1):
        u = l[i]
        if seen[u]: continue
        ll = []
        pp(trans, seen, ll, u)
        lcfc.append(ll)
    return lcfc

def specialize_main(env, code):
    # Step 1: the core of partial evaluation
    for expr in code:
        if expr[0] == PARSED_CALL and expr[1][0][1] in ["let", "letrec"] and len(expr[1]) == 3:
            env, _ = specialize_let(env, expr[1][1], expr[1][2], expr[1][0][1] == "letrec")
        elif expr[0] == PARSED_CALL and expr[1][0][1] in ["let*", "letrec*"] and len(expr[1]) == 2:
            env, _ = specialize_let_star(env, expr[1][1], expr[1][0][1] == "letrec*")
        else:
            print(show(eval_expr(env, expr)))
        #print("#"*80, expr)
    env = add_to_env(env, "args()", (TYPE_UNKNOWN,))
    cd = (PARSED_CALL, ((PARSED_IDENT, "main"), (PARSED_IDENT, "args()")))
    #print("<"*80)
    result, code = specialize(cd, env)
    z = loop_hash((cd, env))
    #print("<"*80)
    spenames[z] = (("main", "args()"), (((TYPE_UNKNOWN,),(PARSED_IDENT, "args()")),), code, env)
    while specialize_loop():
        pass
    #result, code = specialize(cd, env)
    #
    
    funcs = []
    for k in spenames:
        #print(len(spenames[k]))
        #if specialized[k][1][1] != spenames[k][2]:
        #    print(spenames[k][0], specialized[k][1][1], spenames[k][2])
        #funcs.append((spenames[k][0], specialized[k][1][1], tuple(u[0] for u in spenames[k][1])))
        funcs.append((spenames[k][0], spenames[k][2], tuple(u[0] for u in spenames[k][1])))
        #print(spenames[k], print_expr(specialized[k][1][1], []))
    #print(list(print_expr(specialized[k][1][1], []) for k in specialized))
    '''graph = make_func_graph(funcs)
    c = cfc(graph)
    for cf in c:
        if len(cf) == 1:
            u = cf[0]
            nf = funcs[u]
            kw = "letrec" if u in graph[u] else "let"
            print("(" + kw + " (" + " ".join(nf[0]) + ") " + print_expr(nf[1], []) + ")")
        else:
            print("(letrec* (")
            for u in cf:
                nf = funcs[u]
                print("((" + " ".join(nf[0]) + ") " + print_expr(nf[1], []) + ")")
            print("))")'''
    newfuncs, d, dr = remove_args(funcs)
    #cd = []
    for v in globalvars:
        if GVPRF + str(v) in d:
            print("(let " + d[GVPRF + str(v)] + " " + show(globalvars[v]) + ")")
            #cd.append((PARSED_CALL, ((PARSED_KEYWORD, "let"), (PARSED_IDENT
    graph = make_func_graph(newfuncs)
    c = cfc(graph)
    for cf in c:
        if len(cf) == 1:
            u = cf[0]
            nf = newfuncs[u]
            kw = "letrec" if u in graph[u] else "let"
            print("(" + kw + " (" + " ".join(nf[0]) + ") " + print_expr(nf[1], []) + ")")
        else:
            print("(letrec* (")
            for u in cf:
                nf = newfuncs[u]
                print("((" + " ".join(nf[0]) + ") " + print_expr(nf[1], []) + ")")
            print("))")
    #print("-"*80)
    
    #return result, code, specialized
    """# TODO: Do the inlining now
    for k in spefuncs:
        if spefuncs[k][2] == "main":
            inline_func(k, ((PARSED_IDENT, "args"),))
    
    l = []
    for name, func in sorted([(func[2] + str(key), func) for key, func in inlined.items()]):
        if func[2] == "main":
            name = "main"
        #args = " ".join(func[1][i] + ":" + show(func[4][i]) for i in range(len(func[1])))
        args = " ".join(func[1])
        s = "(let ("+name+" "+args+") "+print_expr(func[0], l)+")" #+ ":" + show(func[3])
        print(s)
    seen = {"[]": True}
    while l != []:
        used = l.pop()
        if used in seen:
            continue
        seen[used] = True
        try:
            e = env_find(env, used)
        except:
            continue
        if e[0] in [TYPE_CHAR, TYPE_INT, TYPE_LIST, TYPE_TUPLE]:
            s = "(define " + used + " " + show(e, l) + ")"
        elif e[0] == TYPE_FUNCTION:
            s = "(define (" + used + " " + " ".join(e[1][1]) + ") " + print_expr(e[1][0], l) + ")"
        else:
            continue
        print(s)"""

######################################################################

"""
# TODO
def count_var_number(expr, name):
    pass

# TODO
def move_binding(expr, name, value_code):
    pass

# TODO
def make_let(defi, value_code, expr):
    if (value_code[0] in (PARSED_IDENT, PARSED_INT, PARSED_CHAR)) and defi[0] == PARSED_IDENT:
        return move_binding(expr, defi[1], value_code)
    if defi[0] == PARSED_IDENT:
        no = count_var_number(expr, defi[1])
        if no == 0:
            return expr
        if no == 1:
            return move_binding(expr, defi[1], value_code)
    return (PARSED_CALL, ((PARSED_KEYWORD, "let"), defi, value_code, expr))

# TODO
def simplify_binding(expr, name, value, value_code):
    return (PARSED_CALL, ((PARSED_KEYWORD, "let"), (PARSED_IDENT, name), value_code, expr))

'''
    no = count_var_number(expr, name)
    if no == 0:
        return expr
    if no == 1 or (value[0] in (TYPE_INT, TYPE_CHAR, TYPE_BOOL)):
        return move_binding(expr, name, value_code)
    else:
        if value_code[0] == PARSED_CALL and value_code[1][0][1] == "cons":
            return simplify_binding(
                simplify_binding(
                    move_binding(expr, name, (PARSED_CALL, ((PARSED_IDENT, "cons"), (PARSED_IDENT, name + "-head"), (PARSED_IDENT, name + "-tail")))),
                name + "-tail", value[1][1], value_code[1][2]),
            name + "-head", value[1][0], value_code[1][1])
        return make_let((PARSED_IDENT, name), value_code, expr)
'''

# TODO
def specialize_binding(env, bind_def, bind_value):
    if bind_def[0] == PARSED_IDENT:
        value, code = specialize(env, bind_value)
        if is_known(value):
            value, code = value_ref(value)
        return add_to_env(env, bind_def[1], value), bind_def, value, code
    elif bind_def[0] == PARSED_CALL and bind_def[1][0][1] == "{}":
        value, code = specialize(env, bind_value)
        if is_known(value):
            assert value[0] & ERRORMASK == TYPE_TUPLE
            assert len(value[1]) == len(bind_def[1]) - 1
            z = [value_ref(x) for x in value[1]]
            c = (PARSED_CALL, ((PARSED_IDENT, "{}"),) + tuple(x[1] for x in z))
            for i in range(1, len(bind_def[1])):
                u = bind_def[1][i]
                assert u[0] == PARSED_IDENT
                env = add_to_env(env, u[1], add_error(value[0], z[i - 1][0]))
            return env, bind_def, (TYPE_TUPLE | (value[0] & ERRORMASK), tuple(x[0] for x in z)), c
        if value[0] & ERRORMASK == TYPE_UNKNOWN:
            for i in range(1, len(bind_def[1])):
                u = bind_def[1][i]
                assert u[0] == PARSED_IDENT
                env = add_to_env(env, u[1], value)
            return env, bind_def, value, code
        assert value[0] & ERRORMASK == TYPE_TUPLE, str(bind_def)+str(value)
        assert len(value[1]) == len(bind_def[1]) - 1
        for i in range(1, len(bind_def[1])):
            u = bind_def[1][i]
            assert u[0] == PARSED_IDENT
            env = add_to_env(env, u[1], add_error(value[0], value[1][i - 1]))
        return env, bind_def, value, code
    elif bind_def[0] == PARSED_CALL:
        e = make_func(env, bind_def[1], bind_value)
        return e, bind_def, head(e)[1], bind_value
    else:
        raise Exception("Incorrect binding")

def simplify_let(expr, bind_def, value, value_code):
    if bind_def[0] == PARSED_IDENT:
        if is_known(value):
            value_code = value_ref(value)[1]
        return simplify_binding(expr, bind_def[1], value, value_code)
    elif is_call_to(bind_def, "cons"):
        if value[0] == TYPE_CONS:
            # TODO: check that
            return simplify_let(simplify_let(expr,
                bind_def[1][1], tagged_head(value),
                        (PARSED_CALL, ((PARSED_IDENT, "head"), value_code))),
                bind_def[1][2], tagged_tail(value),
                        (PARSED_CALL, ((PARSED_IDENT, "tail"), value_code)))
    else:
        return (PARSED_CALL, ((PARSED_KEYWORD, "let"), bind_def, value_code, expr))

# TODO
def specialize_keyword(env, expr):
    keyword = expr[0][1]
    if keyword == "if":
        cond, code = specialize(env, expr[1])
        if cond[0] == TYPE_UNKNOWN:
            val1, code1 = specialize(env, expr[2])
            val2, code2 = specialize(env, expr[3])
            if is_known(val1):
                val1, code1 = value_ref(val1)
            if is_known(val2):
                val2, code2 = value_ref(val2)
            result = merge_values(val1, val2)
            return (result, (PARSED_CALL, ((PARSED_KEYWORD, "if"), code, code1, code2)))
        if cond[0] != TYPE_BOOL:
            return ((TYPE_ERROR,), (PARSED_CALL, ((PARSED_KEYWORD, "if"), code, expr[2], expr[3])))
        if cond[1]:
            return specialize(env, expr[2])
        else:
            return specialize(env, expr[3])
    elif keyword == "let": # TODO (and others)
        try:
            newenv, newdef, val, newvalue = specialize_binding(env, expr[1], expr[2])
            result, code = specialize(newenv, expr[3])
        except AssertionError:
            return ((ERRORED | TYPE_ERROR,), (PARSED_CALL, ((PARSED_KEYWORD, "let"), expr[1], expr[2], expr[3])))
        if is_known(result):
            return value_ref(result)
        return (result, simplify_let(code, newdef, val, newvalue))

# TODO
def specialize(env, expr):
    if expr[0] == PARSED_INT or expr[0] == PARSED_CHAR:
        return (eval_expr(None, expr), expr)
    elif expr[0] == PARSED_IDENT:
        var = env_find(env, expr[1])
        return (var, expr)
    else:
        if expr[1][0][0] == PARSED_KEYWORD:
            return specialize_keyword(env, expr[1])
        else:
            func, code = specialize(env, expr[1][0])
            args = [specialize(env, expr[1][i]) for i in range(1, len(expr[1]))]
            if func[0] == TYPE_UNKNOWN:
                return ((TYPE_UNKNOWN,), (PARSED_CALL, (code,) + tuple(arg[1] for arg in args)))
            elif func[0] == TYPE_BUILTIN_FUNCTION:
                try:
                    result = func[1](*(arg[0] for arg in args))
                    c = func[2](*(arg[1] for arg in args))
                except AssertionError:
                    result, c = ERRORED, (PARSED_CALL, (code,) + tuple(arg[1] for arg in args))
                if is_known(result):
                    return value_ref(result)
                return (result, c)
            elif func[0] == TYPE_FIXPOINT: # TODO!!!!
                pass
            assert func[0] == TYPE_FUNCTION, "Can only call a function"
            return specialize_func(env, func, code, args)

# TODO
LIM = 6
def get_args_code(args):
    stack = args
    output = []
    while stack != []:
        arg = stack.pop()
        if is_known(arg[0]):
            continue
        if arg[0][0] == TYPE_LIST and len(stack) <= LIM:
            stack.append((arg[0][1][0], chead(arg[1])))
            stack.append((arg[0][1][1], ctail(arg[1])))
            continue
        if arg[0][0] == TYPE_TUPLE and len(stack) <= LIM:
            for i in range(len(arg[0][1])):
                stack.append((arg[0][1][i], cget(arg[1], (TYPE_INT, i))))
            continue
        output.append(arg[1])
    return tuple(output)

# TODO
def change_args(code, fargnames, args):
    newargs = []
    newargnames = []
    part = []
    stack = list(zip(fargnames, args))
    while stack != []:
        argname, arg = stack.pop()
        if is_known(arg[0]):
            code = simplify_let(code, (PARSED_IDENT, argname), arg[0], value_ref(arg[0])[1])
        else:
            if arg[0][0] == TYPE_LIST and len(stack) <= LIM:
                headname = argname + "-head"
                tailname = argname + "-tail"
                code = move_binding(code, argname, (PARSED_CALL, ((PARSED_IDENT, "cons"), (PARSED_IDENT, headname), (PARSED_IDENT, tailname))))
                stack.append((headname, (arg[0][1][0], chead(arg[1]))))
                stack.append((tailname, (arg[0][1][1], ctail(arg[1]))))
                continue
            if arg[0][0] == TYPE_TUPLE and len(stack) <= LIM:
                code = move_binding(code, argname, (PARSED_CALL, ((PARSED_IDENT, "{}"),) + tuple((PARSED_IDENT, argname+"-"+str(i)) for i in range(len(arg[0][1])))))
                for i in range(len(arg[0][1])):
                    nname = argname + "-"+str(i)
                    stack.append((nname, (arg[0][1][i], cget(arg[1], (TYPE_INT, i)))))
                continue
            newargs.append(arg[1])
            part.append(arg[0])
            newargnames.append(argname)
    return code, newargs, part, newargnames

# TODO
SPECIALIZING = 42
SEEN_SPECIALIZING = 43
def specialize_func(env, func, code, args):
    fcode = func[1][0]
    fargnames = func[1][1]
    #if func[1][2] == "eq":
    #    print(args)
    assert len(fargnames) == len(args), "Wrong number of arguments : "+str(fargnames)
    u = hash((func, code, fargnames, tuple(arg[0] for arg in args)))
    #print(func[1][2], fargnames, tuple(arg[0] for arg in args))
    if u in spefuncs:
        if spefuncs[u] == SEEN_SPECIALIZING or spefuncs[u] == SPECIALIZING:
            spefuncs[u] = SEEN_SPECIALIZING
            return ((TYPE_UNKNOWN,), (PARSED_CALL, ((PARSED_IDENT, func[1][2]+" "+str(u)),)+get_args_code(args)))
        result = spefuncs[u][3]
        if spefuncs[u][5]:
            z = get_args_code(args)
            code = spefuncs[u][0]
            for i in range(len(z)):
                code = simplify_let(code, (PARSED_IDENT, spefuncs[u][1][i]), spefuncs[u][4][i], z[i])
            return (result, code)
        return (result, (PARSED_CALL, ((PARSED_IDENT, func[1][2]+" "+str(u)),)+get_args_code(args)))
    sn = specialized_number.get(func[1][2], 0)
    for i in range(len(fargnames)):
        env = add_to_env(env, fargnames[i], args[i][0])
    for v, _ in args:
        if not is_known(v):
            break
    else:
        result = add_error(func[0], eval_expr(env, fcode))
        if is_known(result) and func[1][2] != "main":
            return value_ref(result)
    if sn >= 50:#SPE_LIMIT:
        return (add_error(func[0], (TYPE_UNKNOWN,)), (PARSED_CALL, ((PARSED_IDENT, func[1][2]),)+tuple(arg[1] for arg in args)))
    specialized_number[func[1][2]] = sn + 1
    spefuncs[u] = SPECIALIZING
    #spefuncs[u] = (code, newargnames, func[1][2], SPECIALIZING, part, False)
    result, code = specialize(env, fcode)
    result = add_error(func[0], result)
    code, newargs, part, newargnames = change_args(code, fargnames, args)
    #print(print_expr(code))
    if is_known(result) and func[1][2] != "main":
        spefuncs[u] = (value_ref(result)[1], newargnames, func[1][2], result, part, True)
        return value_ref(result)
    inline = False
    for narg in newargnames:
        if count_var_number(code, narg) >= 2:
            break
    else:
        if func[1][2] != "main":
            inline = True
    #if func[1][2] != "main":
    #    inline = True
    inline = False
    #if True or func[1][2] == "eval_args":
    #    inline = False
    if spefuncs[u] == SEEN_SPECIALIZING:
        inline = False
    spefuncs[u] = (code, newargnames, func[1][2], result, part, inline)
    if inline:
        for i in range(len(newargs)):
            code = simplify_let(code, (PARSED_IDENT, newargnames[i]), part[i], newargs[i])
        return (result, code)
    return (result, (PARSED_CALL, ((PARSED_IDENT, func[1][2]+" "+str(u)),)+tuple(arg for arg in newargs)))

specialized_number = {}
globalvars = {}
spefuncs = {}
"""

def num_op(f, name):
    def wrap(x, y):
        if x[0] == TYPE_UNKNOWN or y[0] == TYPE_UNKNOWN:
            return (TYPE_UNKNOWN,)
        assert x[0] == y[0] == TYPE_INT, "Wrong type"
        return (TYPE_INT, f(x[1], y[1]))
    return (TYPE_BUILTIN_FUNCTION, wrap, codewrap(name), name)

def comp_op(f, name):
    def wrap(x, y):
        if x[0] == TYPE_UNKNOWN or y[0] == TYPE_UNKNOWN:
            return (TYPE_UNKNOWN,)
        assert x[0] == y[0] == TYPE_INT, "Wrong type"
        return (TYPE_BOOL, f(x[1], y[1]))
    return (TYPE_BUILTIN_FUNCTION, wrap, codewrap(name), name)

def tagged_and(x, y):
    if (x[0] == TYPE_BOOL and not x[1]) or (y[0] == TYPE_BOOL and not y[1]):
        return (TYPE_BOOL, False)
    if (x[0] == TYPE_BOOL and x[1]) and (y[0] == TYPE_BOOL and y[1]):
        return (TYPE_BOOL, True)
    return (TYPE_UNKNOWN,)

def tagged_or(x, y):
    if (x[0] == TYPE_BOOL and x[1]) or (y[0] == TYPE_BOOL and y[1]):
        return (TYPE_BOOL, True)
    if (x[0] == TYPE_BOOL and not x[1]) and (y[0] == TYPE_BOOL and not y[1]):
        return (TYPE_BOOL, False)
    return (TYPE_UNKNOWN,)

def tagged_xor(x, y):
    if x[0] == TYPE_UNKNOWN or y[0] == TYPE_UNKNOWN:
        return (TYPE_UNKNOWN,)
    assert x[0] == y[0] == TYPE_BOOL, "Wrong type"
    return (TYPE_BOOL, x[1] ^ y[1])

def neg(x):
    if x[0] == TYPE_UNKNOWN:
        return x
    assert x[0] == TYPE_BOOL, "Wrong type"
    return (TYPE_BOOL, not x[1])

def equal(x, y):
    if x[0] == TYPE_UNKNOWN or y[0] == TYPE_UNKNOWN:
        return (TYPE_UNKNOWN,)
    if x[0] != y[0]:
        return (TYPE_BOOL, False)
    if x[0] in [TYPE_INT, TYPE_CHAR]:
        return (TYPE_BOOL, x[1] == y[1])
    elif x[0] == TYPE_NIL:
        return (TYPE_BOOL, True)
    elif x[0] == TYPE_CONS:
        return tagged_and(equal(tagged_head(x), tagged_head(y)), equal(tagged_tail(x), tagged_tail(y)))
    else:
        return (TYPE_BOOL, False)

def unequal(x, y):
    return neg(equal(x, y))

def make_string(s):
    return make_list([(TYPE_CHAR, x) for x in s])

def get_string(s):
    u = read_list(s)
    for x in u:
        assert x[0] == TYPE_CHAR, "Wrong type"
    return "".join(x[1] for x in u)

def int_of_string(s):
    if not is_known(s):
        return (TYPE_UNKNOWN,)
    a = get_string(s)
    return(TYPE_INT, int(a))

def string_of_int(n):
    if n[0] == TYPE_UNKNOWN:
        return (TYPE_UNKNOWN,)
    assert n[0] == TYPE_INT, "Wrong type"
    return make_string(str(n[1]))

def int_of_char(c):
    if c[0] == TYPE_UNKNOWN:
        return (TYPE_UNKNOWN,)
    assert c[0] == TYPE_CHAR, "Wrong type"
    return(TYPE_INT, ord(c[1]))

def char_of_int(n):
    if n[0] == TYPE_UNKNOWN:
        return (TYPE_UNKNOWN,)
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
    return (TYPE_ERROR,)

def concat(t1, t2):
    if t1[0] == TYPE_UNKNOWN:
        return (TYPE_UNKNOWN,)
    if t1[0] == TYPE_NIL:
        return t2
    assert t1[0] == TYPE_CONS, "Wrong type"
    return tagged_cons(tagged_head(t1), concat(tagged_tail(t1), t2))

def codewrap(name):
    def wrap(*a):
        return (PARSED_CALL, ((PARSED_IDENT, name),) + a)
    return wrap

def chead(l):
    if is_call_to(l, "cons"):
        return l[1][1]
    return (PARSED_CALL, ((PARSED_IDENT, "head"), l))

def ctail(l):
    if is_call_to(l, "cons"):
        return l[1][2]
    return (PARSED_CALL, ((PARSED_IDENT, "tail"), l))

def cconcat(t1, t2):
    if is_call_to(t1, "cons"):
        return (PARSED_CALL, ((PARSED_IDENT, "cons"), t1[1][1], cconcat(t1[1][2], t2)))
    return (PARSED_CALL, ((PARSED_IDENT, "concat"), t1, t2))

global_env = make_env([
    ("[]", (TYPE_NIL,)),
    ("true", (TYPE_BOOL, True)),
    ("false", (TYPE_BOOL, False)),
    ("cons", (TYPE_BUILTIN_FUNCTION, tagged_cons, codewrap("cons"), "cons")),
    ("head", (TYPE_BUILTIN_FUNCTION, tagged_head, chead, "head")),
    ("tail", (TYPE_BUILTIN_FUNCTION, tagged_tail, ctail, "tail")),
    ("+", num_op(lambda x, y: x + y, "+")),
    ("*", num_op(lambda x, y: x * y, "*")),
    ("-", num_op(lambda x, y: x - y, "-")),
    ("/", num_op(lambda x, y: x // y, "/")),
    ("or", (TYPE_BUILTIN_FUNCTION, tagged_or, codewrap("or"), "or")),
    ("and", (TYPE_BUILTIN_FUNCTION, tagged_and, codewrap("and"), "and")),
    ("xor", (TYPE_BUILTIN_FUNCTION, tagged_xor, codewrap("xor"), "xor")),
    ("not", (TYPE_BUILTIN_FUNCTION, neg, codewrap("not"), "not")),
    ("<", comp_op(lambda x, y: x < y, "<")),
    (">", comp_op(lambda x, y: x > y, ">")),
    ("<=", comp_op(lambda x, y: x <= y, "<=")),
    (">=", comp_op(lambda x, y: x >= y, ">=")),
    ("=", (TYPE_BUILTIN_FUNCTION, equal, codewrap("="), "=")),
    ("!=", (TYPE_BUILTIN_FUNCTION, unequal, codewrap("!="), "!=")),
    ("int_of_string", (TYPE_BUILTIN_FUNCTION, int_of_string, codewrap("int_of_string"), "int_of_string")),
    ("string_of_int", (TYPE_BUILTIN_FUNCTION, string_of_int, codewrap("string_of_int"), "string_of_int")),
    ("int_of_char", (TYPE_BUILTIN_FUNCTION, int_of_char, codewrap("int_of_char"), "int_of_char")),
    ("char_of_int", (TYPE_BUILTIN_FUNCTION, char_of_int, codewrap("char_of_int"), "char_of_int")),
    ("error", (TYPE_BUILTIN_FUNCTION, error, codewrap("error"), "error")),
    ("concat", (TYPE_BUILTIN_FUNCTION, concat, cconcat, "concat")),
])

def env_is_known(env):
    while env != None:
        if not is_known(env[0][1]):
            return False
        env = env[1]
    return True

ikn_d = {}
def is_known(var):
    if id(var) in ikn_d:
        return ikn_d[id(var)][1]
    ikn_d[id(var)] = (var, _is_known(var))
    return ikn_d[id(var)][1]

def _is_known(var):
    if var[0] in [TYPE_UNKNOWN, TYPE_ERROR]:
        return False
    if var[0] in [TYPE_INT, TYPE_CHAR, TYPE_NIL, TYPE_BUILTIN_FUNCTION, TYPE_BOOL]:
        return True
    if var[0] == TYPE_CONS:
        return is_known(var[1][0]) and is_known(var[1][1])
    if var[0] == TYPE_FUNCTION:
        env = var[1][2]
        while env != None:
            name, value = env[0]
            if id(value) != id(var) and (name not in var[1][1]) and is_var_used(var[1][0], name) and (not is_known(value)):
                return False
            env = env[1]
        return True
    if var[0] == TYPE_FIXPOINT:
        return all(is_known(f) for f in var[1])

"""
def show(result, z = []):
    if result[0] == TYPE_UNKNOWN:
        return "???"
    elif result[0] == TYPE_ERROR:
        return "<error>"
    elif result[0] == TYPE_INT:
        return str(result[1])
    elif result[0] == TYPE_NIL:
        return "[]"
    elif result[0] == TYPE_CHAR:
        return print_expr((PARSED_CHAR, result[1]))
    elif result[0] == TYPE_CONS: # TODO: improve this
        return "{" + show(tagged_head(result), z) + " " + show(tagged_tail(result), z) + "}"
    elif result[0] == TYPE_BOOL:
        return result[1] and "true" or "false"
    elif result[0] == TYPE_BUILTIN_FUNCTION:
        z.append(result[3])
        return result[3]
    elif result[0] == TYPE_FUNCTION:
        z.append(result[1][2])
        return result[1][2]
    elif result[0] == TYPE_FIXPOINT:
        z.append(result[2][1][2])
        return result[2][1][2]

# TODO
inlining = {}
inlined = {}
def inline_func(k, args):
    if k in inlining:
        inlining[k] = True
        return (PARSED_CALL, ((PARSED_IDENT, spefuncs[k][2]+" "+str(k)),) + tuple(args))
    else:
        inlining[k] = False
        sf = spefuncs[k]
        code = inline_all(sf[0])
        ar = sf[1]
        if inlining[k] or sf[2] == "main":
            inlined[k] = (code,) + sf[1:]
            return (PARSED_CALL, ((PARSED_IDENT, sf[2]+" "+str(k)),) + tuple(args))
        else:
            for (argname, arg) in zip(ar, args):
                code = make_let((PARSED_IDENT, argname), arg, code)
            del inlining[k]
            return code

# TODO
def inline_all(expr):
    if expr[0] == PARSED_CALL:
        if expr[1][0][0] == PARSED_IDENT and " " in expr[1][0][1]:
            k = int(expr[1][0][1].split(" ")[1])
            return inline_func(k, (inline_all(a) for a in expr[1][1:]))
        return (PARSED_CALL, tuple(inline_all(a) for a in expr[1]))
    return expr
"""

def show(result, z = None):
    if z == None:
        z = []
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
    elif result[0] == TYPE_BUILTIN_FUNCTION:
        return "\"<built-in function " + result[3] + ">\""
    elif result[0] == TYPE_FIXPOINT:
        return "\"<function " + result[3] + ">\""
    elif result[0] == TYPE_FUNCTION:
        return "\"<function " + result[1][3] + ">\""
    elif result[0] == TYPE_UNKNOWN:
        return "\"<unknown>\""

def spe_run(code):
    specialize_main(global_env, parse(code))

def print_expr(expr, u):
    if expr[0] == PARSED_INT:
        return str(expr[1])
    elif expr[0] == PARSED_CONSTANT:
        return show(expr[1])
    elif expr[0] == PARSED_CHAR:
        c = expr[1]
        if c == '\\':
            return "'\\\\'"
        elif c == '\n':
            return "'\\n'"
        elif c == '\t':
            return "'\\t'"
        elif c == '\0':
            return "'\\0'"
        elif c == "'":
            return "'\\''"
        else:
            return "'"+c+"'"
    elif expr[0] == PARSED_IDENT or expr[0] == PARSED_KEYWORD:
        #if expr[1].startswith("globalvar"):
        #    return show(globalvars[int(expr[1][9:])], u)
        u.append(expr[1])
        return expr[1]
        #return expr[1].replace(" ", "")
    else: # TODO: improve a bit that -> pretty_printer?
        return "("+print_code(expr[1], u)+")"

def print_code(code, u):
    l = []
    for expr in code:
        l.append(print_expr(expr, u))
    return " ".join(l)                                                                                  

#f = open("metaeval.l", "r")
#f = open("metameta.l", "r")
#evaluator = f.read()
#f.close()
#evaluator = """(let (u n) (+ n (* 2 3))) (let (main x) (u (int_of_string x)))"""
from sys import stdin
evaluator = stdin.read()
spe_run(evaluator)
#run(evaluator, '"'+prog.replace('"', '\\"')+'"')

