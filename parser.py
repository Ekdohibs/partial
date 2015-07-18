from constants import *

def escaped(c):
    if c == 'n':
        return '\n'
    elif c == 't':
        return '\t'
    elif c == '0':
        return '\0'
    return c

def _parse(s, i, enddelim):
    l = []
    while i < len(s) and s[i] not in enddelim:
        while i < len(s) and s[i] in " \t\n":
            i += 1
        if i >= len(s):
            break
        if s[i] == "(":
            parsed, i = _parse(s, i + 1, ")")
            l.append((PARSED_CALL, parsed))
            i += 1
        elif s[i] == "{":
            parsed, i = _parse(s, i + 1, "}")
            l.append((PARSED_CALL, ((PARSED_IDENT, "cons"),) + parsed))
            i += 1
        elif s[i] == "#": # Comment
            i += 1
            while i < len(s) and s[i] != "\n":
                i += 1
        elif s[i] == "[": # List
            parsed, i = _parse(s, i + 1, "]")
            i += 1
            u = (PARSED_IDENT, "[]")
            for x in reversed(parsed):
                u = (PARSED_CALL, ((PARSED_IDENT, "cons"), x, u))
            l.append(u)
        elif s[i] == "'": # Char
            i += 1
            if s[i] == "\\":
                i += 1
                c = escaped(s[i])
            else:
                c = s[i]
            l.append((PARSED_CHAR, c))
            i += 2
        elif s[i] == '"': # String
            i += 1
            u = []
            while s[i] != '"':
                if s[i] == "\\":
                    c = escaped(s[i + 1])
                    i += 2
                else:
                    c = s[i]
                    i += 1
                u.append((TYPE_CHAR, c))
            i += 1
            z = (TYPE_NIL,)
            for x in reversed(u):
                z = (TYPE_CONS, (x, z))
            l.append((PARSED_CONSTANT, z))
        else:
            a = ""
            while i < len(s) and s[i] not in " \t\n" and s[i] not in enddelim:
                a += s[i]
                i += 1
            if a != "":
                try:
                    u = (PARSED_INT, int(a))
                except:
                    if a in ["let", "let*", "letrec", "letrec*", "if"]:
                        u = (PARSED_KEYWORD, a)
                    else:
                        u = (PARSED_IDENT, a)
                l.append(u)
    return tuple(l), i

def parse(s):
        return _parse(s, 0, "\0")[0]
