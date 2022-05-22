#|
Makayla Soh, Tarani Srikanth, Dani Lopez
File name: substArgs
Description: Interpreter that parses and then interprets. Parses an entire
   program and performs arithmetic expressions. Interpreter is based
   on a substitution method that passes through the program once
   to "insert" the correct values for each identifier. Then passes
   through the program again to execute. This program only takes
   one argument.

The Language (named JILI):

JILI = num
      | {+ JILI JILI}
      |	{- JILI JILI} 
      | {* JILI JILI}
      |	{/ JILI JILI}
      |	{id JILI}
      |	{leq0? JILI JILI JILI}
      |	id
DEFN = {def {id id} JILI}
|#

#lang typed/racket
(require typed/rackunit)



; Data types
(define-syntax tstruct
  (syntax-rules ()
    [(_ name fields)
     (struct name fields #:transparent)]))

; - ExprC represents all possible expressions
(define-type ExprC (U numC leq0C binop IdC AppC))

; - supported arithmetic operations
(tstruct numC ([n : Real]))
(tstruct leq0C ([test : ExprC] [then : ExprC] [else : ExprC]))
(tstruct binop ([operator : Symbol] [l : ExprC] [r : ExprC]))

; - functions/function parts
(tstruct FunDefC ([name : Symbol] [param : Symbol] [body : ExprC]))
(tstruct IdC ([sym : Symbol])) ; name of a variable
(tstruct AppC ([fun : Symbol] [param : ExprC])) ; fun is funct name, param is argument



;; bin-operations
; purpose: define possible binary operations
(define bin-operations (append '(+ - / *)))



;; keywords
; purpose: define reserved words that cannot be function names
(define keywords (append '(+ - / * leq0? def)))



;; legal-id?
; purpose: a predicate to determine if a symbol is a
;          legal function name
(: legal-id? (Any -> Boolean : #:+ Symbol))
(define (legal-id? s)
  (and (symbol? s)
       (not (member s keywords))))



;; lookup2
; purpose: Break down binary operations from concrete to abstract syntax.
; - input: s-expression
; - output: binop
(define (lookup2 [s : Sexp]) : (-> Real Real Real)
  (match s
    ['+ +]
    ['* *]
    ['- -]
    ['/ /]))



;; parse
; Purpose: Parses s-expression (concrete) into arithmetic components
; - input: Sexp
; - output: ExprC 
(define (parse [s : Sexp]) : ExprC
  (match s
    [(? real? n) (numC n)]
    [(list 'leq0? test then else) (leq0C (parse test) (parse then) (parse else))]
    [(list (? symbol? sym) l r) (if (member sym bin-operations) (binop sym (parse l) (parse r))
                                    (error 'parse "unimplemented JILI ~e" s))]
    [(? legal-id? sym) (IdC sym)]
    [(list (? legal-id? fun) rst) (AppC fun (parse rst))]
    [other (error 'parse "unimplemented JILI ~e" s)]))
; test
(check-exn #px"unimplemented JILI" (lambda () (parse '(hi 2 3))))



; Purpose: Breaks each function into its name, param, and body
; - input: Sexp (the program)
; - output: FunDefC 
(define (parse-fundef [sexp : Sexp]) : FunDefC
  (match sexp
    [(list 'def (list (? legal-id? name) (? symbol? param)) body) (FunDefC name param (parse body))]
    [other (error 'parse-fundef "unimplemented JILI ~e" sexp)]))
; tests
(check-exn #px"JILI" (lambda () (parse-fundef '(asfd (name param1 param2) (* 1 2)))))




;; get-fundef
; purpose: Finds the function n in the list of FunDefC
; - input: Symbol, Listof FunDefC
; - output: FunDefC
(define (get-fundef [n : Symbol] [fds : (Listof FunDefC)]) : FunDefC
  (cond
    [(empty? fds) (error 'get-fundef "unimplemented JILI ~e" n)]
    [(cons? fds)
     (cond
       [(equal? n (FunDefC-name (first fds))) (first fds)]
       [else (get-fundef n (rest fds))])]))



;; subst
; purpose: subsitute an expression (what) for a specific symbol (for) in a given expression (what)
; - input: an ExprC, a Symbol, and an ExprC
; - output: an ExprC 
(define (subst [what : ExprC] [for : Symbol] [in : ExprC]) : ExprC
  (match in 
    [(numC n) in]
    [(IdC s) (cond
               [(symbol=? s for) what]
               [else in])]
    [(AppC f a) (AppC f (subst what for a))]
    [(binop s l r) (binop s (subst what for l) (subst what for r))]
    [(leq0C test then else) (leq0C (subst what for test) (subst what for then) (subst what for else))]))



;; interp
; purpose: Evaluate the given expression. If the expression is a function (AppC),
;          find the funciton in the program and evaluate with the given argument.
; - input: an ExprC and a list of FunDefC (functions in the program)
; - output: a real number
(: interp (ExprC (Listof FunDefC) -> Real)) 
(define (interp exp fds)
  (match exp 
    [(numC n) n]
    [(binop s l r) (if (and (equal? s '/) (equal? (interp r fds) 0))
                       (error 'interp "divide by zero JILI ~e" exp)
                       ((lookup2 s) (interp l fds) (interp r fds)))]
    [(leq0C test then else) (if (<= (interp test fds) 0) (interp then fds) (interp else fds))]
    [(AppC f arg) (define num (interp arg fds))
                  (define fd (get-fundef f fds))
                  (interp (subst (numC num)
                                 (FunDefC-param fd)
                                 (FunDefC-body fd))
                          fds)]
    [(IdC _) (error 'interp "undefined variable in expression JILI ~e" exp)]))
; interp test cases
(check-equal? (interp (binop '* (numC 1) (numC 2)) '()) 2)
(check-equal? (interp (binop '+ (numC 10) (numC 2)) '()) 12)
(check-equal? (interp (binop '- (numC 8) (numC 2)) '()) 6)
(check-equal? (interp (binop '/ (numC 6) (numC 2)) '()) 3)
(check-equal? (interp (leq0C (numC 6) (numC 2) (numC 10)) '()) 10)
(check-equal? (interp (leq0C (numC -6) (numC 2) (numC 10)) '()) 2)
(check-equal? (interp (binop '* (AppC 'ignoreit (numC 2)) (numC 3))
                      (list (FunDefC 'ignoreit 'x (binop '/ (numC 4) (IdC 'x)))
                            (FunDefC 'main 'init (AppC 'ignoreit (numC 20))))) 6)
(check-exn #px"JILI" (lambda () (interp (binop '/ (numC 1) (numC 0)) '())))
(check-exn #px"JILI" (lambda () (interp (binop '/ (numC 1) (IdC 'w)) '())))
(check-exn #px"JILI" (lambda () (interp (binop '* (AppC 'ignoreit (numC 2)) (numC 3))
                      (list (FunDefC 'ignoreit 'x (binop '/ (numC 4) (IdC 'y)))
                            (FunDefC 'main 'init (AppC 'ignoreit (numC 20)))))))



;; parse-prog
; purpose: Parse the whole program into functions
; - input: Sexp
; - output: Listof FunDefC
(define (parse-prog [sexp : Sexp]) : (Listof FunDefC)
  (match sexp
    ['() '()]
    [(cons fst rst) (cons (parse-fundef fst) (parse-prog rst))]))
; parse
(check-equal? (parse-prog '{{def {ignoreit x}{/ 4 x}}{def {main init}{ignoreit 20}}})
              (list (FunDefC 'ignoreit 'x (binop '/ (numC 4) (IdC 'x)))
                    (FunDefC 'main 'init (AppC 'ignoreit (numC 20)))))
(check-equal? (parse-prog '{{def {foo x}{/ 10 x}}{def {main init}{foo -20}}})
              (list (FunDefC 'foo 'x (binop '/ (numC 10) (IdC 'x)))
                    (FunDefC 'main 'init (AppC 'foo (numC -20)))))
(check-equal? (parse-prog '{{def {foo x}{leq0? x 4 5}}{def {main init}{foo 50}}})
              (list (FunDefC 'foo 'x (leq0C (IdC 'x) (numC 4) (numC 5)))
                    (FunDefC 'main 'init (AppC 'foo (numC 50)))))
(check-equal? (parse-prog '{})
              '())
              


;; interp-fns
; purpose: Executes the main function to get the result of the program.
;          First parses the main function, then interprets the abstract language.
; - input: a list of FunDefC (functions) in the program
; - output: a real number
(define (interp-fns [fds : (Listof FunDefC)]) : Real
  (interp (parse '{main 0}) fds))
; interp-fns tests
(check-equal? (interp-fns (list (FunDefC 'foo 'x (leq0C (IdC 'x) (numC 4) (numC 5)))
                    (FunDefC 'main 'init (AppC 'foo (numC 50)))))
              5)
(check-equal? (interp-fns (list (FunDefC 'foo 'x (binop '/ (numC 10) (IdC 'x)))
                    (FunDefC 'main 'init (AppC 'foo (numC -20)))))
              -1/2)
(check-equal? (interp-fns (list (FunDefC 'ignoreit 'x (binop '* (numC 4) (IdC 'x)))
                    (FunDefC 'main 'init (AppC 'ignoreit (numC 20)))))
              80)



;; top-interp
; purpose: Takes a whole program represented as an s-expression, evaluates
;          the function by parsing (parse-prog) and interpreting (interp-fns).
; - input: an s-expression representing a program 
; - output: a real that is the result of running the program
(define (top-interp [s : Sexp]) : Real
  (interp-fns (parse-prog s)))
; top-interp tests
(check-equal? (top-interp '{{def {foo x}{+ x 3}}{def {main init}{foo 5}}})8) 
(check-equal? (top-interp '{{def {foo x}{* x 3}}{def {main init}{foo 5}}})15)
(check-equal? (top-interp '{{def {foo x}{/ x 10}}{def {main init}{foo 50}}})5)
(check-equal? (top-interp '{{def {foo x}{- x 3}}{def {main init}{foo 5}}})2)
(check-equal? (top-interp '{{def {foo x}{- x -3}}{def {main init}{foo 5}}})8)
(check-equal? (top-interp '{{def {foo x}{* x -5}}{def {main init}{foo 50}}})-250)
(check-equal? (top-interp '{{def {foo x}{/ x -5}}{def {main init}{foo 50}}})-10)
(check-equal? (top-interp '{{def {foo x}{leq0? x 4 5}}{def {main init}{foo 50}}})5)
(check-equal? (top-interp '{{def {foo x}{leq0? x 4 5}}{def {main init}{foo -20}}})4)
(check-equal? (top-interp '{{def {foo x}{leq0? 2 4 5}}{def {main init}{foo -20}}})5)
(check-equal? (top-interp '{{def {foo1 x}{/ x -5}}{def {foo2 x}{* x -5}}{def {main init}{foo2 {foo1 50}}}})50)
(check-equal? (top-interp '{{def {foo x}{/ x -5}}{def {main init}{foo 50}}})-10)
(check-equal? (top-interp '{{def {minus-five x}{+ x (* -1 5)}}{def{main init}{minus-five {+ 8 init}}}}) 3)
(check-equal? (top-interp '{{def {foo x}{+ x 1}}{def {main init}{foo{/ 10 5}}}})3)

(check-exn #px"JILI" (lambda () (top-interp '{{def {foo x}{leq0? x 4 5}}{def {main init}{foo}}})))
(check-exn #px"JILI" (lambda () (top-interp '{{def {main init}{foo}}})))
(check-exn #px"JILI" (lambda () (top-interp '{})))
(check-exn #px"JILI" (lambda () (top-interp '{{def {foo x}{* 1 y}}{def {main init}{foo -20}}})))
(check-exn #px"JILI"(lambda ()(top-interp '{{def {ignoreit x}{+ 3 4}}{def {main init}{ignoreit (/ 1 (+ 0 0))}}})))
(check-exn #px"JILI"(lambda ()(top-interp '{{def {ignoreit x}{+ 3 4}}{def {main init}{ignoreit (/ 1 0)}}})))
(check-exn #px"JILI"(lambda ()(top-interp '{{def {ignoreit x}{/ 4 x}}{def {main init}{ignoreit 0}}})))