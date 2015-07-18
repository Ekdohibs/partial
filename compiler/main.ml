let read_file f =
  let ic = open_in f in
  let n = in_channel_length ic in
  let s = String.create n in
  really_input ic s 0 n;
  close_in ic;
  s

open Parser
let parse_file f =
  parse (read_file f)

let escaped c =
  match c with
    '\n' -> "\\n"
  | '\t' -> "\\t"
  | '\\' -> "\\\\"
  | '\000' -> "\\000"
  | '\'' -> "\\'"
  | _ -> String.make 1 c

let make_char c = 
  "(C_Char '" ^ (escaped c) ^ "')"

let explode s =
  let rec exp i l =
    if i < 0 then
      l
    else
      exp (i - 1) (s.[i] :: l)
  in exp (String.length s - 1) []

let esc_underscore c =
  match c with
    '+' -> "_p"
  | '-' -> "_m"
  | '_' -> "__"
  | '*' -> "_f"
  | '/' -> "_d"
  | '%' -> "_b"
  | '^' -> "_c"
  | '!' -> "_e"
  | '&' -> "_a"
  | '|' -> "_o"
  | '.' -> "_s"
  | ',' -> "_v"
  | '[' -> "_l"
  | ']' -> "_r"
  | '=' -> "_z"
  | '<' -> "_i"
  | '>' -> "_j"
  | _ -> String.make 1 c

let builtin = "
type t =
    C_Int of int
  | C_Char of char
  | C_Nil
  | C_Cons of t * t
  | C_Bool of bool
  | C_Func of (t list -> t)


let escaped c =
  match c with
    '\\n' -> \"\\\\n\"
  | '\\t' -> \"\\\\t\"
  | '\\\\' -> \"\\\\\\\\\"
  | '\\000' -> \"\\\\000\"
  | '\\'' -> \"\\\\'\"
  | _ -> String.make 1 c

let rec show x =
  match x with
    C_Int i -> print_int i
  | C_Char c -> print_string (\"'\" ^ (escaped c) ^ \"'\")
  | C_Nil -> print_string \"[]\"
  | C_Cons (u, v) -> print_string \"{\"; show u; print_string \" \"; show v; print_string \"}\"
  | C_Bool b -> print_string (if b then \"true\" else \"false\")
  | C_Func _ -> print_string \"<func>\"
 
let explode s =
  let rec exp i l =
    if i < 0 then
      l
    else
      exp (i - 1) (s.[i] :: l)
  in exp (String.length s - 1) []
let call (C_Func f) args = f args
let __l_r = C_Nil
let _true = C_Bool true
let _false = C_Bool false
let __p = C_Func (function [(C_Int x); (C_Int y)] -> C_Int (x + y))
let __m = C_Func (function [(C_Int x); (C_Int y)] -> C_Int (x - y))
let __f = C_Func (function [(C_Int x); (C_Int y)] -> C_Int (x * y))
let __d = C_Func (function [(C_Int x); (C_Int y)] -> C_Int (x / y))
let _cons = C_Func (function [x; y] -> C_Cons (x, y))
let _head = C_Func (function [C_Cons (x, y)] -> x)
let _tail = C_Func (function [C_Cons (x, y)] -> y)
let _or = C_Func (function [(C_Bool x); (C_Bool y)] -> C_Bool (x || y))
let _and = C_Func (function [(C_Bool x); (C_Bool y)] -> C_Bool (x && y))
let _xor = C_Func (function [(C_Bool x); (C_Bool y)] -> C_Bool ((x || y) && (not (x && y))))
let _not = C_Func (function [C_Bool x] -> C_Bool (not x))
let __i = C_Func (function [(C_Int x); (C_Int y)] -> C_Bool (x < y))
let __j = C_Func (function [(C_Int x); (C_Int y)] -> C_Bool (x > y))
let __i_z = C_Func (function [(C_Int x); (C_Int y)] -> C_Bool (x <= y))
let __j_z = C_Func (function [(C_Int x); (C_Int y)] -> C_Bool (x >= y))
let __z = C_Func (function [x; y] -> C_Bool (x = y))
let __e_z = C_Func (function [x; y] -> C_Bool (x <> y))
let read_string s =
  let rec rs s =
    match s with
      C_Nil -> []
    | C_Cons (C_Char h, t) -> (String.make 1 h) :: (rs t)
  in String.concat \"\" (rs s)
let write_string s =
  List.fold_right (fun c s -> C_Cons (C_Char c, s)) (explode s) C_Nil
let _int__of__string = C_Func (function [x] -> C_Int (int_of_string (read_string x)))
let _string__of__int = C_Func (function [C_Int x] -> write_string (string_of_int x))
let _int__of__char = C_Func (function [C_Char x] -> C_Int (Char.code x))
let _char__of__int = C_Func (function [C_Int x] -> C_Char (Char.chr x))
let _error = C_Func (function [x] -> failwith (read_string x))
let _concat = C_Func (function [x; y] ->
  let rec cc u v =
    match u with
      C_Nil -> v
    | C_Cons (a, b) -> cc b (C_Cons (a, v))
  in cc (cc x C_Nil) y)
let read_bool (C_Bool x) = x
"
;;

let make_id id =
  let l = explode id in
  String.concat "" ("_" :: (List.map esc_underscore l))

let make_call c args =
  "(call " ^ c ^ " [ " ^ String.concat " ; " args ^ " ] )"

let rec make_pm_binding e =
  match e with
    P_Id id -> make_id id
  | P_Call ((P_Id "cons") :: t) ->
    "(C_Cons (" ^ (String.concat " , " (List.map make_pm_binding t)) ^ "))"

let make_binding e s =
  match e with
    P_Id id -> (make_id id) ^ " = " ^ s
  | P_Call l ->
    match l with
      (P_Id "cons") :: t -> (make_pm_binding e) ^ " = " ^ s
    | (P_Id name) :: t ->
      (make_id name) ^ " = C_Func (function [" ^
	(String.concat " ; " (List.map (function (P_Id id) -> make_id id) t)) ^
	"] -> " ^ s ^ ")"

let rec compile_expr e =
  match e with
    P_Id id -> make_id id
  | P_Int i -> "(C_Int " ^ string_of_int i ^ ")"
  | P_Char c -> make_char c
  | P_String s -> List.fold_right (fun c p ->
    "(C_Cons (" ^ make_char c ^ ", " ^ p ^ "))") s "C_Nil"
  | P_Call l ->
    match l with
      (P_Id ("let" | "letrec" as k)) :: t -> (
	match t with
	  bind_def :: bind_value :: r ->
	    let s = compile_expr bind_value in
	    let u = make_binding bind_def s in
	    let v = (if k = "let" then "let" else "let rec") ^ " " ^ u in
	    match r with
	      [] -> v
	    | [bind_in] -> "(" ^ v ^ " in " ^ (compile_expr bind_in) ^ ")"
       )
    | (P_Id ("let*" | "letrec*" as k)) :: t -> (
      match t with
	(P_Call binds) :: r ->
	  let ll = List.map
	    (function P_Call [bind_def; bind_value] ->
	      let s = compile_expr bind_value in
	      make_binding bind_def s) binds in
	  let cc = String.concat "\nand " ll in
	  let v = (if k = "let*" then "let" else "let rec") ^ " " ^ cc in
	  match r with
	    [] -> v
	  | [bind_in] -> "(" ^ v ^ " in " ^ (compile_expr bind_in) ^ ")"
    )
    | (P_Id "if") :: t -> (
      match t with
	[cond; if_true; if_false] ->
	  "(if (read_bool " ^ (compile_expr cond) ^ ") then "
	    ^ (compile_expr if_true) ^ " else " ^ (compile_expr if_false) ^ ")"
    )
    | h :: t ->
      let c = compile_expr h in
      let args = List.map compile_expr t in
      make_call c args

let compile prog =
  builtin ^ (String.concat "\n" (List.map compile_expr (parse prog))) ^
    "\nlet () = show (call _main [write_string (input_line stdin)]); print_newline ()\n"

let read_stdin () =
  let n = in_channel_length stdin in
  let s = String.create n in
  really_input stdin s 0 n;
  s

let main () =
  (*let fib =
    "(letrec (fib n) (if (<= n 1) n (+ (fib (- n 1)) (fib (- n 2)))))
     (let (main x) (fib (int_of_string x)))" in*)
  let prog = read_stdin () in
  print_string (compile prog)
;;

main ();;
