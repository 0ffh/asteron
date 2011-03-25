
(scope // put tests into scope to avoid pollution of base environment

  (prln "--- car/cdr")

  (prln "()" (car ()))
  (prln "()" (cdr ()))
  (prln "1" (car (list 1 2 3)))
  (prln "2" (car (cdr (list 1 2 3))))
  (prln "3" (car (cdr (cdr (list 1 2 3)))))
  (prln "()" (car (cdr (cdr (cdr (list 1 2 3))))))


  (prln "--- check scoping")

  (prln "outer: defining x = 1")
  (def x 1)
  (prln "outer: x =" x)
  (scope
    (prln "scope: defining x = 2")
    (def x 2)
    (prln "scope: x =" x)
  )
  (prln "outer: x =" x)
  (defun foo ()
    (prln "foo: setting x = x + 1")
    (= x (+ x 1))
    (prln "foo: x =" x))
  (foo)
  (prln "outer: x =" x)
  (defun bar ()
    (prln "bar: defining x = 5")
    (def x 5)
    (prln "bar: x =" x)
    (foo)
    (prln "bar: x =" x))
  (bar)
  (prln "outer: x =" x)


  (prln "--- check lambda-inside-lambda")

  (def multiply-by (fun (n) (fun (y) (* y n))))
  (def doubler (multiply-by 2))
  (def tripler (multiply-by 3))
  (prln "8 " (doubler 4))
  (prln "12" (tripler 4))


  (prln "--- check closures (1)")

  (def count-down-from (fun (n) (fun () (= n (- n 1)))))
  (def count-down-from-3 (count-down-from 3))
  (def count-down-from-4 (count-down-from 4))
  (prln "2 " (count-down-from-3))
  (prln "3 " (count-down-from-4))
  (prln "1 " (count-down-from-3))
  (prln "0 " (count-down-from-3))
  (prln "2 " (count-down-from-4))
  (prln "1 " (count-down-from-4))
  (prln "0 " (count-down-from-4))


  (prln "--- check closures (2)")

  (def set-hidden 0)
  (def get-hidden 0)
  ((fun ()
    (def hidden 0)
    (= set-hidden (fun (n) (= hidden n)))
    (= get-hidden (fun () hidden))))
  (prln "0 " (get-hidden))
  (prln "12" (set-hidden 12))
  (prln "12" (get-hidden))


  (prln "--- fib test")

  (def fibarg 24)

  (def subtract (fun (n) (fun (y) (- y n))))
  (def pred (subtract 1))
  (def ppred (subtract 2))
  (defun fib1 (n)
    (if (< n 2) n (+ (fib1 (pred n)) (fib1 (ppred n)))))
  (tic)
  (prln "fib1(" fibarg ") ="(fib1 fibarg))
  (toc)

  (defun fib2 (n)
    (if (< n 2) n (+ (fib2 (- n 1)) (fib2 (- n 2)))))
  (tic)
  (prln "fib2(" fibarg ") ="(fib2 fibarg))
  (toc)

  (defun fib3 (n)
    (defun fib-aux (n a b)
      (if (== n 0)
          a
          (fib-aux (- n 1) b (+ a b))))
    (fib-aux n 0 1))
  (tic)
  (prln "fib3(" fibarg ") ="(fib3 fibarg))
  (toc)

)
