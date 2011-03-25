
(scope // put tests into scope to avoid pollution of base environment

  (pr "--- car/cdr")

  (pr "()" (car ()))
  (pr "()" (cdr ()))
  (pr "1" (car (list 1 2 3)))
  (pr "2" (car (cdr (list 1 2 3))))
  (pr "3" (car (cdr (cdr (list 1 2 3)))))
  (pr "()" (car (cdr (cdr (cdr (list 1 2 3))))))


  (pr "--- check scoping")

  (pr "outer: defining x = 1")
  (def x 1)
  (pr "outer: x =" x)
  (scope
    (pr "scope: defining x = 2")
    (def x 2)
    (pr "scope: x =" x)
  )
  (pr "outer: x =" x)
  (defun foo ()
    (pr "foo: setting x = x + 1")
    (= x (+ x 1))
    (pr "foo: x =" x))
  (foo)
  (pr "outer: x =" x)
  (defun bar ()
    (pr "bar: defining x = 5")
    (def x 5)
    (pr "bar: x =" x)
    (foo)
    (pr "bar: x =" x))
  (bar)
  (pr "outer: x =" x)


  (pr "--- check lambda-inside-lambda")

  (def multiply-by (fun (n) (fun (y) (* y n))))
  (def doubler (multiply-by 2))
  (def tripler (multiply-by 3))
  (pr "8 " (doubler 4))
  (pr "12" (tripler 4))


  (pr "--- check closures (1)")

  (def count-down-from (fun (n) (fun () (= n (- n 1)))))
  (def count-down-from-3 (count-down-from 3))
  (def count-down-from-4 (count-down-from 4))
  (pr "2 " (count-down-from-3))
  (pr "3 " (count-down-from-4))
  (pr "1 " (count-down-from-3))
  (pr "0 " (count-down-from-3))
  (pr "2 " (count-down-from-4))
  (pr "1 " (count-down-from-4))
  (pr "0 " (count-down-from-4))


  (pr "--- check closures (2)")

  (def set-hidden 0)
  (def get-hidden 0)
  ((fun ()
    (def hidden 0)
    (= set-hidden (fun (n) (= hidden n)))
    (= get-hidden (fun () hidden))))
  (pr "0 " (get-hidden))
  (pr "12" (set-hidden 12))
  (pr "12" (get-hidden))

  (pr "--- fib test")

  (def fibarg 24)

  (def subtract (fun (n) (fun (y) (- y n))))
  (def pred (subtract 1))
  (def ppred (subtract 2))
  (defun fib1 (n)
    (if (< n 2) n (+ (fib1 (pred n)) (fib1 (ppred n)))))
  (tic)
  (pr "fib1(" fibarg ") ="(fib1 fibarg))
  (toc)

  (defun fib2 (n)
    (if (< n 2) n (+ (fib2 (- n 1)) (fib2 (- n 2)))))
  (tic)
  (pr "fib2(" fibarg ") ="(fib2 fibarg))
  (toc)

  (defun fib3 (n)
    (defun fib-aux (n a b)
      (if (== n 0)
          a
          (fib-aux (- n 1) b (+ a b))))
    (fib-aux n 0 1))
  (tic)
  (pr "fib3(" fibarg ") ="(fib3 fibarg))
  (toc)

)
