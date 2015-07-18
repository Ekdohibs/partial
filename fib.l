(letrec (fib n) (if (<= n 1) n (+ (fib (- n 1)) (fib (- n 2)))))
(let (main x) (fib (int_of_string x)))