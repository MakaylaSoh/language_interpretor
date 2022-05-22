#|
Makayla Soh, Tarani Srikanth, Dani Lopez
File name: substArgs
Description: Interpreter that parses and then interprets. Parses an entire
   program and performs arithmetic expressions. Interpreter is based
   on a substitution method that passes through the program once
   to "insert" the correct values for each identifier. Then passes
   through the program again to execute. This is done for multiple arguments.

The Language (named JILI):

JILI = num
      | {+ JILI JILI}
      |	{- JILI JILI}
      | {* JILI JILI}
      |	{/ JILI JILI}
      |	{id JILI}
      |	{leq0? JILI JILI JILI}
      |	id
DEFN = {def {id id ...} JILI}
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
(tstruct FunDefC ([name : Symbol] [param : (Listof Sexp)] [body : ExprC]))
(tstruct IdC ([sym : Symbol])) ; name of an identifier
(tstruct AppC ([fun : Symbol] [arg : (Listof ExprC)])) ; fun is funct name, arg is an argument



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
    ['/ /]
    [other (error 'lookup2 "Binary operation DNE. JILI ~e" s)]))
; lookup2 tests
(check-equal? (lookup2 '+) +)
(check-equal? (lookup2 '*) *)
(check-equal? (lookup2 '-) -)
(check-equal? (lookup2 '/) /)
(check-exn #px"JILI" (lambda () (lookup2 '=)))


;; parse
; Purpose: Parses s-expression (concrete) into arithmetic components
; - input: Sexp
; - output: ExprC
; (define-predicate sexp? Sexp)
(define (parse [s : Sexp]) : ExprC
 (match s
    [(? real? n) (numC n)]
    [(list 'leq0? test then else) (leq0C (parse test) (parse then) (parse else))]
    [(? legal-id? sym) (IdC sym)]
    [(list (? legal-id? fun) sym ...) (AppC fun (map parse sym))]
    [(list (? symbol? sym) l r)
     (member sym bin-operations) (binop sym (parse l) (parse r))]
    [other (error 'parse "not a valid s-expression JILI ~e" s)])) 
; parse test
(check-equal? (parse '(fun (* 5 2))) (AppC 'fun (list (binop '* (numC 5) (numC 2)))))
(check-equal? (parse '(fun (+ 1 x) y))
              (AppC 'fun (list (binop '+ (numC 1) (IdC 'x)) (IdC 'y))))
(check-equal? (parse '(fun x y z)) (AppC 'fun (list (IdC 'x) (IdC 'y) (IdC 'z))))
(check-equal? (parse '(leq0? -4 5 9)) (leq0C (numC -4) (numC 5) (numC 9))) 
(check-exn #px"JILI" (lambda () (parse '(3 1 2))))
(check-exn #px"JILI" (lambda () (parse '(* + 2))))



; Purpose: Breaks each function into its name, param, and body
; - input: Sexp (the program)
; - output: FunDefC 
(define (parse-fundef [sexp : Sexp]) : FunDefC
  (match sexp
    [(list 'def (list (? legal-id? name)) body) (FunDefC name '() (parse body))]
    [(list 'def (list (? legal-id? name) param ...) body)
     (FunDefC name param (parse body))]
    [other (error 'parse-fundef "unimplemented JILI ~e" sexp)]))
; parse-fundef
(check-equal? (parse-fundef '{def {fun x y} {* 1 2}})
              (FunDefC 'fun '(x y) (binop '* (numC 1) (numC 2))))
(check-equal? (parse-fundef '{def {main} {fun x}})
              (FunDefC 'main '() (AppC 'fun (list (IdC 'x)))))
(check-exn #px"JILI"
           (lambda () (parse-fundef '(asfd (name param1 param2) (* 1 2)))))



;; get-fundef
; purpose: Finds the function n in the list of FunDefC
; - input: Symbol, Listof FunDefC
; - output: FunDefC
(define (get-fundef [n : Symbol] [fds : (Listof FunDefC)]) : FunDefC
  (cond
    [(empty? fds) (error 'get-fundef "function does not exist/not defined JILI ~e" n)]
    [(cons? fds)
     (cond
       [(equal? n (FunDefC-name (first fds))) (first fds)]
       [else (get-fundef n (rest fds))])]))
; get-fundef test
(check-equal? (get-fundef 'fun
                          (list (FunDefC 'main '() (AppC 'fun (list (numC 2))))
                                (FunDefC 'fun '(x) (binop '* (numC 1) (numC 2)))))
                          (FunDefC 'fun '(x) (binop '* (numC 1) (numC 2))))
(check-equal? (get-fundef 'fun
                          (list (FunDefC 'fun '(x) (binop '* (numC 1) (numC 2)))))
                          (FunDefC 'fun '(x) (binop '* (numC 1) (numC 2))))
(check-exn #px"JILI" (lambda () (get-fundef 'fun '())))



;; subst
; purpose: subsitute an expression (what) for a specific symbol (for) in a given expression (in)
; - input: an ExprC, a Symbol, and an ExprC
; - output: an ExprC 
(define (subst [what : ExprC] [for : Sexp] [in : ExprC]) : ExprC
  (match in  
    [(numC n) in]
    [(IdC s) (cond
               [(equal? s for) what] 
               [else in])]
    [(AppC f a)
        (define subst-all (map (lambda ([one : ExprC])
                            (subst what for one)) a))
        (AppC f subst-all)]
    [(binop s l r) (binop s (subst what for l) (subst what for r))]
    [(leq0C test then else) (leq0C (subst what for test)
                                   (subst what for then)
                                   (subst what for else))]))
; subst tests
(check-equal? (subst (numC 2) 'x (binop '+ (IdC 'x) (numC 2))) (binop '+ (numC 2) (numC 2)))
(check-equal? (subst (numC 2) 'x (AppC 'fun (list (IdC 'x)))) (AppC 'fun (list (numC 2))))
(check-equal? (subst (numC 2) 'x (leq0C (binop '+ (IdC 'x) (numC 1)) (numC -2) (numC 4)))
                     (leq0C (binop '+ (numC 2) (numC 1)) (numC -2) (numC 4)))
(check-equal? (subst (numC 2) 'y (leq0C (binop '+ (IdC 'x) (IdC 'y)) (numC -2) (numC 4)))
                     (leq0C (binop '+ (IdC 'x) (numC 2)) (numC -2) (numC 4)))
  
 

;; subst-list
; purpose: substitutes a list of arguments for the correct corresponding parameters in an expression
; - input: Listof Real (arguments), Listof Symbol (parameters), ExprC (expression evaluating)
; - output: ExprC
(define (subst-list [numList : (Listof Real)] [parList : (Listof Sexp)] [body : ExprC]) : ExprC
  (match* (numList parList)
    [('() '()) body]
    [((cons numFst numRst) (cons parFst parRst)) (define upd-bdy (subst (numC numFst) parFst body))
                                                 (subst-list numRst parRst upd-bdy)]
     
    [('() anything) (error 'subst-list "number of args and parameters do not match JILI ~e" parList)]
    [(anything '()) (error 'subst-list "number of args and parameters do not match JILI ~e" body)]))
; subst-lst tests
(check-equal? (subst-list '(1 2 3) '(x y z) (binop '+ (binop '* (IdC 'x) (IdC 'y)) (IdC 'z)))
              (binop '+ (binop '* (numC 1) (numC 2)) (numC 3)))
(check-exn #px"JILI" (lambda () (subst-list '() '(x) (binop '+ (IdC 'x) (IdC 'y)))))
(check-exn #px"JILI" (lambda () (subst-list '(3 4 9) '(x) (binop '+ (IdC 'x) (IdC 'y)))))



;; interp
; purpose: Evaluate the given expression. If the expression is a function (AppC), 
;          find the funciton in the program and evaluate with the given argument.
; - input: an ExprC and a list of FunDefC (functions in the p rogram)
; - output: a real number   
(: interp (ExprC (Listof FunDefC) -> Real))  
(define (interp exp fds)
 (match exp 
    [(numC n) n]
    [(binop s l r) (if (and (equal? s '/) (equal? (interp r fds) 0))
                       (error 'interp "divide by zero JILI ~e" exp)
                       ((lookup2 s) (interp l fds) (interp r fds)))]
    [(leq0C test then else) (if (<= (interp test fds) 0) (interp then fds) (interp else fds))]
    ; go through arg list, and interp each argument (returns a list of all the numbers)
    ; based on the interpreted arg list, substitute those into the funct function
    [(AppC fun arg) (define funct (get-fundef fun fds))
                    ; each value is eval-arg
                    (define eval-arg (map (lambda ([ar : ExprC]) 
                                           (interp ar fds))
                                           arg))
                    (define new-bdy (subst-list eval-arg (FunDefC-param funct) (FunDefC-body funct)))
                    (interp new-bdy fds)] 
    [(IdC _) (error 'interp "undefined variable in expression JILI ~e" exp)]))
; interp test cases 
(check-equal? (interp (binop '* (numC 1) (numC 2)) '()) 2)
(check-equal? (interp (binop '+ (numC 10) (numC 2)) '()) 12) 
(check-equal? (interp (binop '- (numC 8) (numC 2)) '()) 6)
(check-equal? (interp (binop '/ (numC 6) (numC 2)) '()) 3)
(check-equal? (interp (leq0C (numC 6) (numC 2) (numC 10)) '()) 10)
(check-equal? (interp (leq0C (numC -6) (numC 2) (numC 10)) '()) 2)
(check-equal? (interp (AppC 'fun (list (numC 2)))
                      (list (FunDefC 'fun '(x) (binop '+ (numC 4) (IdC 'x)))
                            (FunDefC 'main '(init) (AppC 'ignoreit (list (numC 20)))))) 6)
(check-equal? (interp (binop '+ (AppC 'fun (list (numC 2) (numC 3))) (numC 3))
                      (list (FunDefC 'fun '(x y) (binop '* (binop '+ (numC 4) (IdC 'x)) (IdC 'y)))))
               21)
(check-equal? (interp (binop '+ (AppC 'fun '()) (numC 3))
                      (list (FunDefC 'fun '() (binop '* (numC 2) (numC 3)))))
              9)
(check-exn #px"JILI" (lambda () (interp (binop '/ (numC 1) (numC 0)) '())))
(check-exn #px"JILI" (lambda () (interp (binop '+ (AppC 'fun (list (numC 2))) (numC 3))
                      (list (FunDefC 'fun '(x y) (binop '* (binop '+ (numC 4) (IdC 'x)) (IdC 'y)))))))
(check-exn #px"JILI" (lambda () (interp (binop '+ (AppC 'fun (list (numC 2) (numC 5))) (numC 3))
                      (list (FunDefC 'fun '(x) (binop '* (binop '+ (numC 4) (IdC 'x)) (IdC 'y)))))))
(check-exn #px"JILI" (lambda () (interp (binop '+ (AppC 'fun (list (numC 2) (numC 5))) (numC 3))
                      (list (FunDefC 'fun '(x y) (binop '* (binop '+ (numC 4) (IdC 'x)) (IdC 'm)))))))



;; parse-prog
; purpose: Parse the whole program into functions
; - input: Sexp
; - output: Listof FunDefC
(define (parse-prog [sexp : Sexp]) : (Listof FunDefC)
  (match sexp
    ['() '()]
    [(cons fst rst) (cons (parse-fundef fst) (parse-prog rst))]))
; parse tests
(check-equal? (parse-prog '{{def {ignoreit x}{/ 4 x}}{def {main}{ignoreit 20}}})
              (list (FunDefC 'ignoreit '(x) (binop '/ (numC 4) (IdC 'x)))
                    (FunDefC 'main '() (AppC 'ignoreit (list (numC 20))))))
(check-equal? (parse-prog '{{def {foo x}{/ 10 x}}{def {main}{foo -20}}})
              (list (FunDefC 'foo '(x) (binop '/ (numC 10) (IdC 'x)))
                    (FunDefC 'main '() (AppC 'foo (list (numC -20))))))
(check-equal? (parse-prog '{{def {foo x}{leq0? x 4 5}}{def {main}{foo 50}}})
              (list (FunDefC 'foo '(x) (leq0C (IdC 'x) (numC 4) (numC 5)))
                    (FunDefC 'main '() (AppC 'foo (list (numC 50))))))
(check-equal? (parse-prog '{}) '())   



;; interp-fns
; purpose: Executes the main function to get the result of the program.
;          First parses the main function, then interprets the abstract language.
; - input: a list of FunDefC (functions) in the program
; - output: a real number
(define (interp-fns [fds : (Listof FunDefC)]) : Real
  (interp (parse '{main}) fds))
; interp-fns tests
(check-equal? (interp-fns (list (FunDefC 'foo '(x) (leq0C (IdC 'x) (numC 4) (numC 5)))
                    (FunDefC 'main '() (AppC 'foo (list (numC 50))))))
              5)
(check-equal? (interp-fns (list (FunDefC 'foo '(x) (binop '/ (numC 10) (IdC 'x)))
                    (FunDefC 'main '() (AppC 'foo (list (numC -20))))))
              -1/2)
(check-equal? (interp-fns (list (FunDefC 'ignoreit '(x) (binop '* (numC 4) (IdC 'x)))
                    (FunDefC 'main '() (AppC 'ignoreit (list (numC 20))))))
              80)



;; top-interp
; purpose: Takes a whole program represented as an s-expression, evaluates
;          the function by parsing (parse-prog) and inerpreting (interp-fns).
; - input: an s-expression representing a program 
; - output: a real that is the result of running the program
(define (top-interp [s : Sexp]): Real
  (interp-fns (parse-prog s)))
; top-interp tests
(check-equal? (top-interp '{{def {foo x}{+ x 3}}{def {main}{foo 5}}})8) 
(check-equal? (top-interp '{{def {foo x}{* x 3}}{def {main}{foo 5}}})15)
(check-equal? (top-interp '{{def {foo x}{/ x 10}}{def {main}{foo 50}}})5)
(check-equal? (top-interp '{{def {foo x}{- x 3}}{def {main}{foo 5}}})2)
(check-equal? (top-interp '{{def {foo x}{- x -3}}{def {main}{foo 5}}})8)
(check-equal? (top-interp '{{def {foo x}{* x -5}}{def {main}{foo 50}}})-250)
(check-equal? (top-interp '{{def {foo x}{/ x -5}}{def {main}{foo 50}}})-10)
(check-equal? (top-interp '{{def {foo x}{leq0? x 4 5}}{def {main}{foo 50}}})5)
(check-equal? (top-interp '{{def {foo x}{leq0? x 4 5}}{def {main}{foo -20}}})4)
(check-equal? (top-interp '{{def {foo x}{leq0? 2 4 5}}{def {main}{foo -20}}})5)
(check-equal? (top-interp '{{def {foo1 x} (* x 2)} {def {foo2 y} (+ 1 y)} {def {main} (foo1 (foo2 2))}}) 6)
(check-equal? (top-interp '{{def {foo x}{/ x -5}}{def {main}{foo 50}}}) -10)
(check-equal? (top-interp '{{def {foo x y}{+ x y}}{def {main}{foo 50 20}}}) 70)
(check-equal? (top-interp '{{def {foo x y z} (+ x (* y z))}{def {main}{foo 1 2 3}}}) 7)
(check-equal? (top-interp '((def (realtwice x) (+ x x))
                            (def (main) (twice 15)) (def (twice x) (realtwice x))))30)
(check-equal? (top-interp '((def (main) (f 9)) (def (f x) (g 3 x)) (def (g a b) (+ a b))))12)

(check-exn #px"JILI" (lambda () (top-interp '{{def {foo x}{leq0? x 4 5}}{def {main}{foo}}})))
(check-exn #px"JILI" (lambda () (top-interp '{{def {main}{foo}}})))
(check-exn #px"JILI" (lambda () (top-interp '{})))
(check-exn #px"JILI" (lambda () (top-interp '{{def {foo x}{* 1 y}}{def {main}{foo -20}}})))
(check-exn #px"JILI"(lambda ()(top-interp '{{def {ignoreit x}{+ 3 4}}{def {main}{ignoreit (/ 1 (+ 0 0))}}})))
(check-exn #px"JILI"(lambda ()(top-interp '{{def {ignoreit x}{+ 3 4}}{def {main}{ignoreit (/ 1 0)}}})))
(check-exn #px"JILI"(lambda ()(top-interp '{{def {ignoreit x}{/ 4 x}}{def {main}{ignoreit 0}}})))
