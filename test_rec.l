(letrec* (((even n) (if (= n 0) true (odd (- n 1))))
          ((odd n) (if (= n 0) false (even (- n 1))))))
(let (main x) (even (int_of_string x))) 