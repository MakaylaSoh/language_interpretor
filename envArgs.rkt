#|
Makayla Soh, Tarani Srikanth, Dani Lopez
File name: envArgs
Description: Interpreter that parses and then interprets. Uses an environment to
   hold the binding between arguments and identifiers. The environment keeps
   track of in scope identifiers.

The Language:
Exp = Num
    |id
    |String
    |{if Expr Expr Expr}
    |{var {[id = Expr] ...} in Expr}
    |{id ... => Expr}  
    |{Expr Expr ...} 
|#


#lang typed/racket
(require typed/rackunit)

 
; Data types
(define-syntax tstruct
  (syntax-rules ()
    [(_ name fields)
     (struct name fields #:transparent)]))


(define-type NonId (U 'if 'var 'in '=> '())) ; canot be id names

; ExprC
(define-type ExprC (U NumC IdC StrC IfC AppC LamC))
(tstruct NumC ([n : Real]))
(tstruct IdC ([sym : Symbol]))
(tstruct StrC ([s : String]))
(tstruct IfC ([conditional : ExprC] [then : ExprC][else : ExprC]))
(tstruct LamC ([id : (Listof Symbol)] [body : ExprC]))
(tstruct AppC ([fun : ExprC] [arg : (Listof ExprC)]))

; Values
(define-type Value (U Real String Boolean PrimOp CloV))
(tstruct CloV ([param : (Listof Symbol)] [body : ExprC] [e : Environment]))
(tstruct PrimOp ([operator : Symbol]))
(define-type Solid-Value (U Real String Boolean)) ; not a PrimOp or CloV

; Environment
(define-type Environment (Listof Bind))
(tstruct Bind ([name : Symbol] [val : Value]))
(define extend-env cons)
(define top-env (list (Bind '+ (PrimOp '+)) (Bind '- (PrimOp '-)) (Bind '* (PrimOp '*)) (Bind '/ (PrimOp '/))
                      (Bind '<= (PrimOp '<=)) (Bind 'equal? (PrimOp 'equal?)) (Bind 'true #t)
                      (Bind 'false #f) (Bind 'error (PrimOp 'error))))

; predicates
(define-predicate nonid? NonId)
(define-predicate solid-value? Solid-Value)



;; legal-id?
; purpose: a predicate to determine if a symbol is a
;          legal function name
;input: anything
;output: boolean (whether it is a legal id or not)
(: legal-id? (Any -> Boolean : #:+ Symbol))
(define (legal-id? s)
  (and (symbol? s)
       (not (nonid? s))))
 


;; serialize
; purpose: to convert the value to a String representation
; input: value of our language
; output: string (representation of the value)
(define (serialize [val : Value]) : String
  (match val
    [(? real? n) (~v n)]
    [(? boolean? b) (if b "true" "false")]
    [(PrimOp oper) "#<primop>"]
    [(CloV param body env) "#<procedure>"]
    [(? string? s) (~v s)]))





;; get-id
; purpose: to split a given argument and return just the identifier
; -input: s-expressions in form "id = value"
; -output: s-expression (the id)
(define (get-id [s : Sexp]) :  Sexp
  (match s
    [(list id '= val) id]
    [other (error 'get-id "invalid argument entered. user-error JILI ~e" s)]))




;; get-val
; purpose: to split a given argument and return just the value
;-input: s-expressions in form "id = value"
;-output: s-expression (the value)
(define (get-val [s : Sexp]) :  Sexp
  (match s
    [(list id '= val) val]
    [other (error 'get-id "invalid argument entered. user-error JILI ~e" s)]))




;; parse
; Purpose: Parses s-expression (concrete) into arithmetic components
; - input: Sexp
; - output: ExprC
(define (parse [s : Sexp]) : ExprC
 (match s
    [(list 'var (list args ...) 'in bdy)
     (define exp (cons (append (map get-id args) (list '=> bdy))
                  (map get-val args)))
     (parse exp)]
    [(? real? n) (NumC n)]
    [(? string? s) (StrC s)]
    [(list 'if rst ...) (match rst
                          [(list condition then else) (IfC (parse condition)(parse then)(parse else))]
                          [other (error 'lookup "Incorrect if statement. user-error JILI ~e" rst)])]
    [(? symbol? sym) (match sym
                           [(? legal-id? sym)(IdC sym)]
                           [other (error 'lookup "Incorrect if statement. user-error JILI ~e" sym)])]
                        
    [(list (? legal-id? id) ... '=> bdy) 
     (if (check-duplicates id)
         (error 'lookup "Id duplicates in lamC. user-error JILI ~e" id)
         (LamC (cast id (Listof Symbol)) (parse bdy)))]
      
    [(list s ...) (AppC (parse (first s)) (map parse (rest s)))]))




; lookup
; purpose: find an id in an environment
; -input: id (symbol), env (where to look for the symbol)
; -output: value (of id tied to the binding in the environment)
(define (lookup [id : Symbol] [env : Environment]) : Value
  (match env
    ['() (error 'lookup "Could not find identifier. user-error JILI ~e" id)]
    [(cons f r) (if (equal? (Bind-name f) id) (Bind-val f) (lookup id r))]))




; arith-lookup
; purpose: Break down binary operations from concrete to abstract syntax.
; - input: s-expression
; - output: procedure
(define (arith-lookup [s : Symbol]) : (U (Real Real * -> Real) (Real Real -> Boolean) (Any Any -> Boolean))
  (match s
    ['+ +]
    ['* *]
    ['- -]
    ['/ /]
    ['<= <=]
    ['equal? equal?]
    [other (error 'lookup2 "Binary operation DNE. user-error JILI ~e" s)]))


 


;; interp
; purpose: Evaluate the given expression. If the expression is a function (AppC), 
;          find the funciton in the program and evaluate with the given argument.
; - input: an ExprC and a list of FunDefC (functions in the p rogram)
; - output: a Value

(: interp (ExprC Environment -> Value))   
(define (interp exp env)
 (match exp 
    [(NumC n) n]
    [(StrC s) s] 
    [(LamC param body) (CloV param body env)] ; CloV
    [(IdC id) (lookup id env)] ; PrimOp or identifier
    [(IfC condition then else)  
     (define eval-cond (interp condition env))
     (cond
       [(boolean? eval-cond) (match eval-cond
                               [#t (interp then env)]
                               [other (interp else env)])]
       [else (error 'interp "conditional cannot be evaluated to true or false user-error JILI ~e" condition)])]
    [(AppC f a)
     (define eval-a (map (lambda ([arg : ExprC])
                           (interp arg env))
                            a))
     (match (interp f env)
                  [(CloV param body clov-env)
                   (cond
                     [(equal? (length param) (length a))
                      (define pairs (map (lambda ([p : Symbol] [a : Value])
                                          (Bind p a))
                                        param
                                        eval-a))
                      (define new-env (append pairs clov-env))
                      (interp body new-env)]
                     [else (error 'interp "number of args and params differ. user-error. JILI ~e ~e" param a)])]
                   [(PrimOp p)
                    (match p
                      ['error (error 'interp "user-error JILI ~e" a)]
                      ['equal? (match eval-a
                               [(list (? solid-value? val1) (? solid-value? val2)) (equal? val1 val2)]
                               [other #f])]
                      ['/ (match eval-a
                            [(list (? real? val1) (? real? val2)) (if (equal? val2 0)
                                                                      (error "division by 0. user-error JILI ~e" val2)
                                                                      ((arith-lookup p) val1 val2))]
                            [other (error 'interp "operation and values do not match JILI ~e" a)])]
                      [other (match eval-a
                               [(list (? real? val1) (? real? val2)) ((arith-lookup p) val1 val2)]
                               [other (error 'interp "operation and values do not match JILI ~e" a)])])]
                  [other (error 'interp "non-closure or primop AppC. user-error JILI ~e" exp)])]))



;; top-interp
; purpose: takes in a sexp as a expression to our language,
; returns the value of that expression
; input- sexp (expression)
; output- String (String representation of the result of the expression)
(define (top-interp [s : Sexp]) : String
  (serialize (interp (parse s) top-env)))



; TEST CASES

; serialize tests
(check-equal? (serialize (PrimOp '+)) "#<primop>")
(check-equal? (serialize "Hello") "\"Hello\"")

; get-id tests
(check-equal? (get-id '(x = 24)) 'x)
(check-exn #px"JILI" (lambda () (get-id '(hi world))))

; get-val tests
(check-equal? (get-val '(x = 24)) 24)
(check-exn #px"JILI" (lambda () (get-val '(hi world))))

; parse tests
(check-equal? (parse '{+ 1 2}) (AppC (IdC '+) (list (NumC 1) (NumC 2))))
(check-equal? (parse '{x + => {/ x +}}) (LamC '(x +) (AppC (IdC '/) (list (IdC 'x) (IdC '+)))))
(check-equal? (parse '{equal? 1 2}) (AppC (IdC 'equal?) (list (NumC 1) (NumC 2))))
(check-equal? (parse '{equal? "hello" "hello"}) (AppC (IdC 'equal?)
                                                      (list (StrC "hello") (StrC "hello"))))
(check-equal? (parse '{var {[z = {+ 9 14}]
                            [y = 98]} 
                           in
                           {+ z y}})
              (AppC (LamC '(z y) (AppC (IdC '+) (list (IdC 'z) (IdC 'y))))
                    (list (AppC (IdC '+) (list (NumC 9) (NumC 14))) (NumC 98))))
(check-equal? (parse '{x y => {+ 1 2}}) (LamC '(x y) (AppC (IdC '+) (list (NumC 1) (NumC 2)))))
(check-equal? (parse '{x y => {* {+ 1 2} {- x y}}})
              (LamC '(x y) (AppC (IdC '*) (list (AppC (IdC '+) (list (NumC 1) (NumC 2)))
                                                (AppC (IdC '-) (list (IdC 'x) (IdC 'y)))))))
  
(check-equal? (parse '{if {<= 3 4} 4 5}) (IfC (AppC (IdC '<=) (list (NumC 3) (NumC 4))) (NumC 4) (NumC 5)))
(check-equal? (parse '{var {{x = {+ 9 14}}
                {y = 98}}
               in
               {if {<= x y}4 5}})(AppC (LamC '(x y) (IfC (AppC (IdC '<=) (list (IdC 'x) (IdC 'y)))
                                                         (NumC 4) (NumC 5)))
                                       (list (AppC (IdC '+) (list (NumC 9) (NumC 14))) (NumC 98))))
(check-exn #px"JILI" (lambda () (parse '{if {<= 3 4} 4})))
(check-exn #px"JILI" (lambda () (parse '{x x => (+ x 2)})))
(check-exn #px"JILI" (lambda () (parse '{var x => (+ + 2)})))


; arith-lookup tests
(check-equal? (arith-lookup '*) *)
(check-equal? (arith-lookup '+) +)
(check-equal? (arith-lookup '/) /)
(check-equal? (arith-lookup '-) -)
(check-equal? (arith-lookup '<=) <=)
(check-equal? (arith-lookup 'equal?) equal?)
(check-exn #px"JILI" (lambda () (arith-lookup 'a)))


; interp tests
(check-equal? (interp (NumC 3) top-env) 3)
(check-equal? (interp (AppC (LamC '(x y) (AppC (IdC '/) (list (IdC 'x) (IdC 'y))))
                            (list (AppC (IdC '+) (list (NumC 9) (NumC 16))) (NumC 5))) top-env)
              5)
(check-equal? (interp (AppC (LamC '(x y) (AppC (IdC '+) (list (IdC 'x) (IdC 'y))))
                            (list (AppC (IdC '+) (list (NumC 9) (NumC 14))) (NumC 98))) top-env)
              121)
(check-equal? (interp (AppC (LamC '(x y) (AppC (IdC '<=) (list (IdC 'x) (IdC 'y))))
                            (list (AppC (IdC '+) (list (NumC 9) (NumC 14))) (NumC 98))) top-env)
               #t)
(check-equal? (interp (AppC (LamC '(x y) (AppC (IdC 'equal?) (list (IdC 'x) (IdC 'y))))
                            (list (NumC 2) (NumC 2))) top-env)
              #t)
(check-equal? (interp (AppC (LamC '(x y) (AppC (IdC 'equal?) (list (IdC 'x) (IdC 'y))))
                            (list (NumC 1) (NumC 2))) top-env)
              #f)
(check-equal? (interp (LamC '(x y) (AppC (IdC '+) (list (IdC 'x) (IdC 'y)))) top-env)
              (CloV '(x y) (AppC (IdC '+) (list (IdC 'x) (IdC 'y))) top-env))
(check-equal? (interp (StrC "Hello") '()) "Hello")
(check-equal? (interp(IfC (AppC (IdC '<=) (list (NumC 3) (NumC 4))) (NumC 4) (NumC 5)) top-env)4)

(check-equal? (interp (AppC (LamC '(x y) (IfC (AppC (IdC '<=) (list (IdC 'x) (IdC 'y))) (NumC 4) (NumC 5)))
                            (list (AppC (IdC '+) (list (NumC 9) (NumC 14))) (NumC 98))) top-env)
              4)

(check-equal? (interp (AppC (LamC '(x y) (IfC (AppC (IdC 'equal?) (list (IdC 'x) (IdC 'y))) (NumC 4) (NumC 5)))
                            (list (AppC (IdC '+) (list (NumC 9) (NumC 14))) (NumC 98))) top-env)
              5)
(check-equal? (interp (AppC (LamC '(x y) (IfC (AppC (IdC 'equal?) (list (IdC 'x) (IdC 'y))) (IdC 'x) (IdC 'y)))
                            (list (AppC (IdC '+) (list (NumC 9) (NumC 14))) (NumC 98))) top-env)
              98)
(check-exn #px"JILI" (lambda () (arith-lookup 'a)))
(check-exn #px"JILI"
           (lambda ()(interp (AppC (AppC (IdC 'var)
                                         (list
                                          (AppC (AppC (IdC 'z=) (list (AppC (IdC '+) (list (NumC 9) (NumC 14)))))
                                                               (list (AppC (IdC 'y) (list (IdC '=) (NumC 98)))
                                                                     (IdC 'in)
                                                                     (AppC (IdC '+) (list (IdC 'x) (IdC 'y))))))) '())
                             top-env)))
(check-true (interp (AppC (IdC 'equal?) (list (StrC "hello") (StrC "hello"))) top-env))
(check-false (interp (AppC (IdC 'equal?) (list (StrC "hello") (IdC '+))) top-env))
(check-exn #px"JILI" (lambda () (interp (AppC (IdC '+) (list (StrC "hello") (StrC "world"))) top-env)))
(check-exn #px"JILI" (lambda () (interp (AppC (IdC '+) (list (NumC 1) (NumC 1) (NumC 1))) top-env)))
(check-exn #px"JILI" (lambda () (interp(IfC (NumC 2) (NumC 4) (NumC 5)) top-env)))



; top-interp tests
(check-equal?(top-interp '{+ 1 2})"3")
(check-equal?(top-interp '{equal? 1 2})"false")
(check-equal?(top-interp '{equal? "hello" "hello"})"true")
(check-equal?(top-interp '{var {[z = {+ 9 14}]
                            [y = 98]}
                           in
                           {+ z y}})"121")
(check-equal?(top-interp '{x y => {+ 1 2}})"#<procedure>")
(check-equal?(top-interp '{x y => {* {+ 1 2} {- x y}}})"#<procedure>")
(check-equal?(top-interp'{if {<= 3 4} 4 5})"4")
(check-equal?(top-interp '{var {{x = {+ 9 14}} 
                {y = 98}}
               in
               {if {<= x y}4 5}})"4")
(check-exn #px"JILI" (lambda () (top-interp '{1})))
(check-exn #px"JILI" (lambda () (top-interp '(error {+ 1 4}))))
(check-exn #px"JILI" (lambda () (top-interp '(error {+ 1 {- 2 4}}))))
(check-exn #px"JILI"(lambda ()(top-interp '(+ if 4))))
(check-exn #px"JILI" (lambda ()(top-interp '((=> 9)17))))
(check-exn #px"JILI" (lambda () (top-interp '(/ 1 (- 3 3)))))
(check-exn #px"JILI" (lambda () (top-interp '(/ true (- 3 3)))))
(check-exn #px"JILI" (lambda ()(top-interp '(+ + +))))
