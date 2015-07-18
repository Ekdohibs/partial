from constants import *

def escape(c):
    if c == '\n':
        return '\\n'
    elif c == '\t':
        return '\\t'
    elif c == '\0':
        return '\\0'
    elif c in '\\\'\"':
        return '\\' + c
    return c

def pp_keyword(code, ind):
    keyword = code[0][1]
    #if keyword == "if":
    #
    e = ""
    if len(code) > 2:
        e = pretty_print(code[2:], ind + "\t")
    return ind + "(" + keyword + pretty_print_expr(code[1], " ") + e + ind + ")"

def code_is_list(code):
    if code[0] == PARSED_IDENT and code[1] == "[]":
        return True
    elif code[0] == PARSED_CALL and code[1][0][1] == "cons":
        return code_is_list(code[1][2])
    return False

def code_to_list(code):
    if code[0] == PARSED_IDENT and code[1] == "[]":
        return []
    elif code[0] == PARSED_CALL and code[1][0][1] == "cons":
        return [code[1][1]] + code_to_list(code[1][2])

def pp_cons(code, ind):
    if code_is_list(code):
        l = code_to_list(code)
        if all(k[0] == PARSED_CHAR for k in l):
            return ind + '"' + "".join(escape(k[1]) for k in l) + '"'
        return ind + "[" + pretty_print(l, ind + "\t") + ind + "]"
    return ind + "{" + pretty_print(code[1][1:], ind + "\t") + ind + "}"

def pretty_print_expr(code, ind = "\n"):
    if code[0] == PARSED_CALL:
        if code[1][0][0] == PARSED_KEYWORD:
            return pp_keyword(code[1], ind)
        elif code[1][0][1] == "cons":
            return pp_cons(code, ind)
        return ind + "(" + pretty_print(code[1], ind + "\t") + ind + ")"
    elif code[0] == PARSED_INT:
        return ind + str(code[1])
    elif code[0] == PARSED_IDENT or code[0] == PARSED_KEYWORD:
        return ind + code[1]
    elif code[0] == PARSED_CHAR:
        return ind + "'" + escape(code[1]) + "'"

def pretty_print(code, ind = "\n"):
    return "".join(pretty_print_expr(k, ind) for k in code)


