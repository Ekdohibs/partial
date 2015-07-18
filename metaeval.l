##########
# Parser #
##########

(let PARSED_INT 0)
(let PARSED_CALL 1)
(let PARSED_IDENT 2)
(let PARSED_CHAR 3)
(let PARSED_KEYWORD 4)

(let (is_whitespace c)
	(or (= c ' ') (or (= c '\t') (= c '\n')))
)

(letrec (in x l)
	(if (= l [])
		false
	(if (= x (head l))
		true
		(in x (tail l))
	))
)

(let (escaped c)
	(if (= c 't') '\t'
	(if (= c 'n') '\n'
	(if (= c '0') '\0'
	c
))))

(letrec (len l)
	(if (= l [])
		0
		(+ 1 (len (tail l)))
))

(letrec (access i l)
	(if (= i 0)
		(head l)
		(access (- i 1) (tail l))
))

(letrec (_parse_word_aux s enddelim)
	(if (= s []) {[] []}
	(let c (head s)
	(if (or (= c enddelim) (is_whitespace c)) {[] s}
	(let {wd r} (_parse_word_aux (tail s) enddelim)
	{(cons c wd) r}
)))))

(let (is_keyword word)
	(in word ["if" "let" "letrec" "let*" "letrec*"])
)

(letrec (csbi s allow_minus)
	(if (= s []) true
	(let c (head s)
	(let cc (int_of_char c)
	(if (or (and allow_minus (= c '-')) (and (<= (int_of_char '0') cc) (<= cc (int_of_char '9'))))
		(csbi (tail s) false)
		false
)))))

(let (can_string_be_int s) (csbi s (> (len s) 1))) # "-" is not an int

(let (_parse_word s enddelim)
	(let {word r} (_parse_word_aux s enddelim)
	(if (can_string_be_int word) {{PARSED_INT (int_of_string word)} r}
	(let type (if (is_keyword word) PARSED_KEYWORD PARSED_IDENT)
	{{type word} r}
))))

(letrec (_parse_comment s)
	(if (= s []) []
	(let c (head s)
	(if (= c '\n') s
	(_parse_comment (tail s))
))))

(letrec (_parse_list p)
	(if (= p [])
		{PARSED_IDENT "[]"}
		{PARSED_CALL [{PARSED_IDENT "cons"} (head p) (_parse_list (tail p))]}
))

(letrec (_parse_string s)
	(if (= s []) {[] []}
	(let cc (head s)
	(if (= cc '"')
		{[] s}
	(let {c r} (if (= cc '\\')
		{(escaped (head (tail s))) (tail (tail s))}
		{cc (tail s)})
	(let {wd t} (_parse_string r)
	{{PARSED_CALL [{PARSED_IDENT "cons"} {PARSED_CHAR c} wd]} t}
))))))

(letrec (_parse_loop s enddelim)
	(if (= s []) {[] []}
	(let c (head s)
	(if (= c enddelim) {[] s}
	(if (is_whitespace c) (_parse_loop (tail s) enddelim)
	(if (= c '(')
		(let {parsed r} (_parse_loop (tail s) ')')
		(let {prs t} (_parse_loop (tail r) enddelim)
		{(cons {PARSED_CALL parsed} prs) t}
		))
	(if (= c '{') # Cons
		(let {parsed r} (_parse_loop (tail s) '}')
		(let {prs t} (_parse_loop (tail r) enddelim)
		{(cons {PARSED_CALL (cons {PARSED_IDENT "cons"} parsed)} prs) t}
		))
	(if (= c '#') # Comment
		(let r (_parse_comment (tail s))
		(_parse_loop (tail r) enddelim)
		)
	(if (= c '[') # List
		(let {parsed r} (_parse_loop (tail s) ']')
		(let {prs t} (_parse_loop (tail r) enddelim)
		{(cons (_parse_list parsed) prs) t}
		))
	(if (= c '\'') # Char
		(let cc (head (tail s))
		(let {c r} (if (= cc '\\')
			{(escaped (head (tail (tail s)))) (tail (tail (tail (tail s))))}
			{cc (tail (tail (tail s)))})
		(let {prs t} (_parse_loop r enddelim)
		{(cons {PARSED_CHAR c} prs) t}
		)))
	(if (= c '"') # String
		(let {string r} (_parse_string (tail s))
		(let {prs t} (_parse_loop (tail r) enddelim)
		{(cons string prs) t}
		))
	# Else
		(let {word r} (_parse_word s enddelim)
		(let {prs t} (_parse_loop r enddelim)
		{(cons word prs) t}
		))
)))))))))))

(let (parse s)
	(head (_parse_loop s '\0'))	
)

#############
# Evaluator #
#############

(let TYPE_INT 0)
(let TYPE_NIL 1)
(let TYPE_CONS 2)
(let TYPE_CHAR 3)
(let TYPE_BOOL 4)
(let TYPE_FUNCTION 5)
(let TYPE_BUILTIN_FUNCTION 6)
(let TYPE_FIXPOINT 7)

(let (add_to_env env name value)
	(cons {name value} env)
)

(letrec (env_find env name)
	(if (= env []) (error (concat "Name not found in env: " name))
	(let {nm value} (head env)
	(if (= name nm)
		value
		(env_find (tail env) name)
))))

(letrec (get_ident_list func_def)
	(if (= func_def []) []
	(let {type name} (head func_def)
	(if (!= type PARSED_IDENT) (error "Invalid list of identifiers")
	(cons name (get_ident_list (tail func_def)))
))))

(let (make_func env func_def func_code)
	(let args (get_ident_list func_def)
	{TYPE_FUNCTION [func_code (tail args) env]}
))

(let (make_func_in_env env func_def func_code)
	(let func (make_func env func_def func_code)
	(let name (tail (head func_def))
	(add_to_env env name func)
)))

(letrec (add_list_to_env env ident_list values)
	(if (= ident_list [])
		(if (= values [])
			env
			(error "Incorrect number of values")
		)
		(if (= values [])
			(error "Incorrect number of values")
			(add_list_to_env
				(add_to_env env (head ident_list) (head values))
				(tail ident_list)
				(tail values))
		)
))

(let (binding_is_func bind_def)
	(let {type def} bind_def
	(if (= type PARSED_IDENT)
		false
	(!= (tail (head def)) "cons")
)))

(letrec (bind env bind_def value)
	(let {type def} bind_def
	(if (= type PARSED_IDENT)
		(if (= def "[]")
			(if (!= (head value) TYPE_NIL)
				(error "Match error")
				env
			)
		(if (= def "_")
			env
		(add_to_env env def value)
	))
	(if (or (!= type PARSED_CALL) (!= (tail (head def)) "cons"))
		(error "Incorrect binding")
	(if (!= (head value) TYPE_CONS)
		(error "Match error")
	(bind (bind env (access 1 def) (head (tail value))) (access 2 def) (tail (tail value)))
)))))

(letrec (add_ident names)
	(if (= names [])
		[]
		(cons {PARSED_IDENT (head names)} (add_ident (tail names)))
))

(let (make_rec env names bind_def bind_value)
	(let name (tail (head (tail bind_def)))
	(let newname (concat name " rec")
	(make_func env
		(cons {PARSED_IDENT newname} (add_ident names))
		{PARSED_CALL [{PARSED_KEYWORD "let"}
			{PARSED_CALL (cons {PARSED_IDENT newname} (tail (tail bind_def)))}
			bind_value
			{PARSED_IDENT newname}]})
)))

(letrec (unpack_bindings bds)
	(if (= bds [])
		{[] []}
	(if (!= (head (head bds)) PARSED_CALL)
		(error "Incorrect use of let(rec)*")
	(let [def value] (tail (head bds))
	(let {defs values} (unpack_bindings (tail bds))
	{(cons def defs) (cons value values)}
)))))

(letrec* (
((make_binding env bind_def bind_value is_recursive)
	(let {type def} bind_def
	(if (and (!= type PARSED_CALL) (!= type PARSED_IDENT))
		(error "Incorrect binding")
	(let is_func (binding_is_func bind_def)
	(if (and is_recursive (not is_func))
		(error "Incorrect recursive binding")

	(if (not is_func)
		(bind env bind_def (eval_expr env bind_value))
	
	(if (not is_recursive)
		(make_func_in_env env def bind_value)
	
	(let name (tail (head (tail bind_def)))
	(let frec (make_rec env [name] bind_def bind_value)
	(add_to_env env name {TYPE_FIXPOINT {[frec] frec}})
)))))))))

# TODO
((make_bindings env bds is_recursive)
	(if (!= (head bds) PARSED_CALL)
		(error "Incorrect use of let(rec)*")
	(let {bind_defs bind_values} (unpack_bindings (tail bds))
	bind_defs
)))

((eval_keyword env expr)
	(let keyword (tail (head expr))
	(if (= keyword "if")
		(let {ct condition} (eval_expr env (access 1 expr))
		(if (!= ct TYPE_BOOL)
			(error "Condition must be a bool")
		(if condition
			(eval_expr env (access 2 expr))
			(eval_expr env (access 3 expr))
		)
	))
	(if (in keyword ["let" "letrec"])
		(eval_expr (make_binding env (access 1 expr) (access 2 expr) (= keyword "letrec")) (access 3 expr))
	# keyword = let(rec)*
		(eval_expr (make_bindings env (access 1 expr) (= keyword "letrec*")) (access 2 expr))
))))

((eval_args env args)
	(if (= args [])
		[]
		(cons (eval_expr env (head args)) (eval_args env (tail args)))
))

((eval_call func args)
	(let [code argnames fenv] func
	(eval_expr (add_list_to_env fenv argnames args) code)
))

((get_fixpoints fix l)
	(if (= l [])
		[]
		(cons {TYPE_FIXPOINT {fix (head l)}} (get_fixpoints fix (tail l)))
))

((eval_expr env expr)
	(let {type ex} expr
	(if (= type PARSED_INT)
		{TYPE_INT ex}
	(if (= type PARSED_CHAR)
		{TYPE_CHAR ex}
	(if (= type PARSED_IDENT)
		(env_find env ex)
	# type = PARSED_CALL
	(if (= (head (head ex)) PARSED_KEYWORD)
		(eval_keyword env ex)
		(let {ft func} (eval_expr env (head ex))
		(if (= ft TYPE_BUILTIN_FUNCTION)
			(let args (eval_args env (tail ex))
			(func args)
		)
		(if (= ft TYPE_FIXPOINT)
			(let {ft2 func2} (eval_call (tail (tail func)) (get_fixpoints (head func) (head func)))
			(eval_call func2 (eval_args env (tail ex))))
		(if (!= ft TYPE_FUNCTION) (error "Can only call a function")
			(eval_call func (eval_args env (tail ex)))
		)))
	))
)))))
))

(let (is_main_let expr)
	(let {type def} expr
	(if (!= type PARSED_CALL)
		false
	(and (in (tail (head def)) ["let" "letrec"]) (= (len def) 3))
)))

(letrec (eval_main env code args)
	(if (= code [])
		(let func (tail (env_find env "main"))
		(eval_call func [args]))
	(let {et expr} (head code)
	(let newenv (if (is_main_let (head code))
		(make_binding env (access 1 expr) (access 2 expr) (= (tail (head expr)) "letrec"))
		env)
	(eval_main newenv (tail code) args)
))))

######################
# Global environment #
######################

(let (tagged_cons l)
	(if (!= (len l) 2) (error "Incorrect number of arguments")
	(let u (head l)
	(let v (access 1 l)
	{TYPE_CONS (cons u v)}
))))

(let (tagged_head l)
	(if (!= (len l) 1) (error "Incorrect number of arguments")
	(let {ut u} (head l)
	(if (!= ut TYPE_CONS) (error "Invalid type")
	(head u)
))))

(let (tagged_tail l)
	(if (!= (len l) 1) (error "Incorrect number of arguments")
	(let {ut u} (head l)
	(if (!= ut TYPE_CONS) (error "Invalid type")
	(tail u)
))))

(let (tagged_+ l)
	(if (!= (len l) 2) (error "Incorrect number of arguments")
	(let {ut u} (head l)
	(let {vt v} (access 1 l)
	(if (!= ut TYPE_INT) (error "Invalid type")
	(if (!= vt TYPE_INT) (error "Invalid type")
	{TYPE_INT (+ u v)}
))))))

(let (tagged_* l)
	(if (!= (len l) 2) (error "Incorrect number of arguments")
	(let {ut u} (head l)
	(let {vt v} (access 1 l)
	(if (!= ut TYPE_INT) (error "Invalid type")
	(if (!= vt TYPE_INT) (error "Invalid type")
	{TYPE_INT (* u v)}
))))))

(let (tagged_- l)
	(if (!= (len l) 2) (error "Incorrect number of arguments")
	(let {ut u} (head l)
	(let {vt v} (access 1 l)
	(if (!= ut TYPE_INT) (error "Invalid type")
	(if (!= vt TYPE_INT) (error "Invalid type")
	{TYPE_INT (- u v)}
))))))

(let (tagged_/ l)
	(if (!= (len l) 2) (error "Incorrect number of arguments")
	(let {ut u} (head l)
	(let {vt v} (access 1 l)
	(if (!= ut TYPE_INT) (error "Invalid type")
	(if (!= vt TYPE_INT) (error "Invalid type")
	{TYPE_INT (/ u v)}
))))))

(let (tagged_or l)
	(if (!= (len l) 2) (error "Incorrect number of arguments")
	(let {ut u} (head l)
	(let {vt v} (access 1 l)
	(if (!= ut TYPE_BOOL) (error "Invalid type")
	(if (!= vt TYPE_BOOL) (error "Invalid type")
	{TYPE_BOOL (or u v)}
))))))

(let (tagged_and l)
	(if (!= (len l) 2) (error "Incorrect number of arguments")
	(let {ut u} (head l)
	(let {vt v} (access 1 l)
	(if (!= ut TYPE_BOOL) (error "Invalid type")
	(if (!= vt TYPE_BOOL) (error "Invalid type")
	{TYPE_BOOL (and u v)}
))))))

(let (tagged_xor l)
	(if (!= (len l) 2) (error "Incorrect number of arguments")
	(let {ut u} (head l)
	(let {vt v} (access 1 l)
	(if (!= ut TYPE_BOOL) (error "Invalid type")
	(if (!= vt TYPE_BOOL) (error "Invalid type")
	{TYPE_BOOL (xor u v)}
))))))

(let (tagged_not l)
	(if (!= (len l) 1) (error "Incorrect number of arguments")
	(let {ut u} (head l)
	(if (!= ut TYPE_BOOL) (error "Invalid type")
	{TYPE_BOOL (not u)}
))))

(let (tagged_< l)
	(if (!= (len l) 2) (error "Incorrect number of arguments")
	(let {ut u} (head l)
	(let {vt v} (access 1 l)
	(if (!= ut TYPE_INT) (error "Invalid type")
	(if (!= vt TYPE_INT) (error "Invalid type")
	{TYPE_BOOL (< u v)}
))))))

(let (tagged_> l)
	(if (!= (len l) 2) (error "Incorrect number of arguments")
	(let {ut u} (head l)
	(let {vt v} (access 1 l)
	(if (!= ut TYPE_INT) (error "Invalid type")
	(if (!= vt TYPE_INT) (error "Invalid type")
	{TYPE_BOOL (> u v)}
))))))

(let (tagged_<= l)
	(if (!= (len l) 2) (error "Incorrect number of arguments")
	(let {ut u} (head l)
	(let {vt v} (access 1 l)
	(if (!= ut TYPE_INT) (error "Invalid type")
	(if (!= vt TYPE_INT) (error "Invalid type")
	{TYPE_BOOL (<= u v)}
))))))

(let (tagged_>= l)
	(if (!= (len l) 2) (error "Incorrect number of arguments")
	(let {ut u} (head l)
	(let {vt v} (access 1 l)
	(if (!= ut TYPE_INT) (error "Invalid type")
	(if (!= vt TYPE_INT) (error "Invalid type")
	{TYPE_BOOL (>= u v)}
))))))

(letrec (eq a b)
	(let {ut u} a
	(let {vt v} b
	(if (!= ut vt) false
	(if (= ut TYPE_INT) (= u v)
	(if (= ut TYPE_CHAR) (= u v)
	(if (= ut TYPE_NIL) true
	(if (= ut TYPE_CONS)
		(if (eq (head u) (head v))
			(eq (tail u) (tail v))
				false
		)
	false
))))))))

(let (tagged_= l)
	(if (!= (len l) 2) (error "Incorrect number of arguments")
	(let u (head l)
	(let v (access 1 l)
	{TYPE_BOOL (eq u v)}
))))

(let (tagged_!= l)
	(if (!= (len l) 2) (error "Incorrect number of arguments")
	(let u (head l)
	(let v (access 1 l)
	{TYPE_BOOL (not (eq u v))}
))))

(let (tagged_ioc l)
	(if (!= (len l) 1) (error "Incorrect number of arguments")
	(let {ut u} (head l)
	(if (!= ut TYPE_CHAR) (error "Invalid type")
	{TYPE_INT (int_of_char u)}
))))

(let (tagged_coi l)
	(if (!= (len l) 1) (error "Incorrect number of arguments")
	(let {ut u} (head l)
	(if (!= ut TYPE_INT) (error "Invalid type")
	{TYPE_CHAR (char_of_int u)}
))))

(letrec (read_string s)
	(let {st t} s
	(if (= st TYPE_NIL)
		[]
	(if (!= st TYPE_CONS) (error "Invalid string")
	(let {ct c} (head t)
	(if (!= ct TYPE_CHAR) (error "Invalid string")
	(cons c (read_string (tail t)))
))))))

(letrec (write_string s)
	(if (= s [])
		{TYPE_NIL []}
	{TYPE_CONS (cons {TYPE_CHAR (head s)} (write_string (tail s)))}
))

(let (tagged_ios l)
	(if (!= (len l) 1) (error "Incorrect number of arguments")
	(let u (head l)
	{TYPE_INT (int_of_string (read_string u))}
)))

(let (tagged_soi l)
	(if (!= (len l) 1) (error "Incorrect number of arguments")
	(let {ut u} (head l)
	(if (!= ut TYPE_INT) (error "Invalid type")
	(write_string (string_of_int u))
))))

(let (tagged_error l)
	(if (!= (len l) 1) (error "Incorrect number of arguments")
	(let u (head l)
	(error (read_string u))
)))

# TODO
(let (tagged_concat l)
	l
)

(let global_env [
	{"[]" {TYPE_NIL []}}
	{"false" {TYPE_BOOL false}}
	{"true" {TYPE_BOOL true}}
	{"cons" {TYPE_BUILTIN_FUNCTION tagged_cons}}
	{"head" {TYPE_BUILTIN_FUNCTION tagged_head}}
	{"tail" {TYPE_BUILTIN_FUNCTION tagged_tail}}
	{"+" {TYPE_BUILTIN_FUNCTION tagged_+}}
	{"*" {TYPE_BUILTIN_FUNCTION tagged_*}}
	{"-" {TYPE_BUILTIN_FUNCTION tagged_-}}
	{"/" {TYPE_BUILTIN_FUNCTION tagged_/}}
	{"or" {TYPE_BUILTIN_FUNCTION tagged_or}}
	{"and" {TYPE_BUILTIN_FUNCTION tagged_and}}
	{"xor" {TYPE_BUILTIN_FUNCTION tagged_xor}}
	{"not" {TYPE_BUILTIN_FUNCTION tagged_not}}
	{"<" {TYPE_BUILTIN_FUNCTION tagged_<}}
	{">" {TYPE_BUILTIN_FUNCTION tagged_>}}
	{"<=" {TYPE_BUILTIN_FUNCTION tagged_<=}}
	{">=" {TYPE_BUILTIN_FUNCTION tagged_>=}}
	{"=" {TYPE_BUILTIN_FUNCTION tagged_=}}
	{"!=" {TYPE_BUILTIN_FUNCTION tagged_!=}}
	{"int_of_char" {TYPE_BUILTIN_FUNCTION tagged_ioc}}
	{"char_of_int" {TYPE_BUILTIN_FUNCTION tagged_coi}}
	{"int_of_string" {TYPE_BUILTIN_FUNCTION tagged_ios}}
	{"string_of_int" {TYPE_BUILTIN_FUNCTION tagged_soi}}
	{"error" {TYPE_BUILTIN_FUNCTION tagged_error}}
	{"concat" {TYPE_BUILTIN_FUNCTION tagged_concat}}
])

#(letrec (tuple_can_be_string r)
#	(if (= r [])
#		true
#	(let {ut _} (head r)
#	(if (= ut TYPE_CHAR)
#		(tuple_can_be_string (tail r))
#		false
#	)
#)))

#(letrec* (
#((show_spaced r)
#	(if (= r []) ""
#	(if (= (tail r) []) (show (head r))
#	(concat (concat (show (head r)) " ") (show_spaced (tail r)))
#)))

#((show_tuple r)
#	(if (tuple_can_be_string r 0)
#		(concat "\"" (concat (read_string {TYPE_TUPLE r}) "\""))
#	(concat "{" (concat (show_spaced r) "}"))
#))

#((show_list r)
#	(concat "[" (concat (show_spaced r) "]"))
#)

#((show result)
#	(let {rt r} result
#	(if (= rt TYPE_INT) (string_of_int r)
#	(if (= rt TYPE_CHAR) ['\'' r '\'']
#	(if (= rt TYPE_TUPLE) (show_tuple r)
#	(if (= rt TYPE_LIST) (show_list r)
#	(if (= rt TYPE_BOOL) (if r "true" "false")
#	"<function>"
#	#result
#)))))))
#))

(let (show result) result) # TODO


(let (run code args)
	(show (eval_main global_env (parse code) (write_string args)))
)

#(let prog "(letrec (fact n) (if (<= n 1) 1 (* n (fact (- n 1))))) (let (main x) (fact (int_of_string x)))")
(let prog "(letrec (fib n) (if (<= n 1) n (+ (fib (- n 2)) (fib (- n 1))))) (let (main x) (fib (int_of_string x)))")
#(let prog "(letrec (make n) (if (= n 0) [] (cons n (make (- n 1))))) (letrec (rev l r) (if (= l []) r (rev (tail l) (cons (head l) r)))) (let (main x) (rev (make (int_of_string x)) []))")
#(let prog "(letrec (make n) (if (= n 0) [] (cons n (make (- n 1))))) (letrec (d l) (if (= l []) [] (let u (head l) (cons u (cons u (d (tail l))))))) (let (main x) (d (make (int_of_string x))))")

(let (main x)
	(run prog x)
	#(parse x)
)
