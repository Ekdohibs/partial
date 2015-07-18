type parsed =
  P_Int of int
| P_Char of char
| P_String of char list
| P_Id of string
| P_Call of parsed list

let escaped c =
  match c with
    'n' -> '\n'
  | 't' -> '\t'
  | '0' -> '\000'
  | _ -> c

let is_white c =
  match c with
    ' ' | '\t' | '\n' -> true
  | _ -> false

let is_digit c =
  '0' <= c && c <= '9'

let can_ident_be_int id =
  let n = String.length id in
  n > 0 && (is_digit id.[0] || (id.[0] = '-' && n > 1)) &&
    (let b = ref true in
     for i = 1 to n - 1 do
       b := !b && is_digit id.[i]
     done; !b)

let parse s =
  let n = String.length s in
  let rec _parse_comment i enddelim =
    if i >= n then
      [], i
    else if s.[i] = '\n' then
      _parse_loop (i + 1) enddelim
    else
      _parse_comment (i + 1) enddelim
  and _parse_string i =
    if s.[i] = '"' then
      [], i
    else if s.[i] = '\\' then
      let ss, j = _parse_string (i + 2) in
      (escaped s.[i + 1]) :: ss, j
    else
      let ss, j = _parse_string (i + 1) in
      s.[i] :: ss, j
  and _parse_loop i enddelim =
    if i >= n then
      [], i
    else if s.[i] = enddelim then
      [], i
    else if is_white s.[i] then
      _parse_loop (i + 1) enddelim
    else match s.[i] with
      '(' -> 
	let p, j = _parse_loop (i + 1) ')' in
	let pp, k = _parse_loop (j + 1) enddelim in
	(P_Call p) :: pp, k
    | '[' ->
      let p, j = _parse_loop (i + 1) ']' in
      let pp, k = _parse_loop (j + 1) enddelim in
      (List.fold_right (fun u v -> P_Call [P_Id "cons"; u; v]) p (P_Id "[]")) :: pp, k
    | '{' ->
      let p, j = _parse_loop (i + 1) '}' in
      let pp, k = _parse_loop (j + 1) enddelim in
      (P_Call ((P_Id "cons") :: p)) :: pp, k
    | '#' -> _parse_comment (i + 1) enddelim
    | '\'' ->
      if s.[i + 1] = '\\' then
	let p, j = _parse_loop (i + 4) enddelim in
	(P_Char (escaped s.[i + 2])) :: p, j
      else
	let p, j = _parse_loop (i + 3) enddelim in
	(P_Char s.[i + 1]) :: p, j
    | '"' ->
      let ss, j = _parse_string (i + 1) in
      let p, k = _parse_loop (j + 1) enddelim in
      (P_String ss) :: p, k
    | _ ->
      let u = ref i in
      while !u < n && s.[!u] <> enddelim && not (is_white s.[!u]) do
	incr u
      done;
      let id = String.sub s i (!u - i) in
      let p, j = _parse_loop !u enddelim in
      if can_ident_be_int id then
	(P_Int (int_of_string id)) :: p, j
      else
	(P_Id id) :: p, j
  in
  fst (_parse_loop 0 '\000')
;;
