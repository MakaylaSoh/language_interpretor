#|
Makayla Soh, Tarani Srikanth, Dani Lopez
File name: stoArgs
Description: Interpreter that parses and then interprets. Uses an environment to
   hold the binding between arguments and and the location reference of a variable in scope.
   Uses a store that holds all the values associated with each location. This allows
   for a language with mutation.

The Language:
  expr	 	=	 	number
 	 	|	 	string
 	 	|	 	id
 	 	|	 	{id := expr}
 	 	|	 	{if expr expr expr}
 	 	|	 	{var {[id = expr] ...} in expr}
 	 	|	 	{id ... => expr}
 	 	|	 	{expr expr ...}
  top-level-constants	 	=	 	true
 	 	|	 	false
 	 	|	 	null
  top-level-functions	 	=	 	+
 	 	|	 	-
 	 	|	 	*
 	 	|	 	/
 	 	|	 	equal?
 	 	|	 	<=
 	 	|	 	array
 	 	|	 	new-array
 	 	|	 	aref
 	 	|	 	aset!
 	 	|	 	begin
 	 	|	 	substring
 	 	|	 	error
|#


#lang typed/racket
(require typed/rackunit)
  
; Data types
(define-syntax tstruct
  (syntax-rules ()
    [(_ name fields)
     (struct name fields #:transparent)]))

; illegal Id names
(define-type NonId (U 'if 'var 'in '=> '()))

; ExprC
(define-type ExprC (U NumC IdC StrC IfC AppC LamC))
(tstruct NumC ([n : Real]))
(tstruct IdC ([sym : Symbol]))
(tstruct StrC ([s : String]))
(tstruct IfC ([conditional : ExprC] [then : ExprC][else : ExprC]))
(tstruct LamC ([id : (Listof Symbol)] [body : ExprC]))
(tstruct AppC ([fun : ExprC] [arg : (Listof ExprC)]))

; Values
(tstruct NullV ([id : Symbol] [s : Store]))
(define-type Value (U Real String Boolean PrimOp CloV ArrayV ArrayOp NullV))
(tstruct CloV ([param : (Listof Symbol)] [body : ExprC] [e : Environment]))
(tstruct PrimOp ([operator : Symbol]))
(tstruct ArrayOp ([arrOp : Symbol]))
(tstruct ArrayV ([loc : Nonnegative-Integer] [len : Nonnegative-Integer]))
 
(define-type Solid-Value (U Real String Boolean))

; Environment
(define-type Environment (Listof Bind))
(tstruct Bind ([name : Symbol] [loc : Nonnegative-Integer]))
(define extend-env cons)
(define top-env (list (Bind '+ 0) (Bind '- 1) (Bind '* 2) (Bind '/ 3)
                      (Bind '<= 4) (Bind 'equal? 5) (Bind 'true 6)
                      (Bind 'false 7) (Bind 'error 8) (Bind 'array 9)
                      (Bind 'new-array 10) (Bind 'aref 11) (Bind 'aset! 12)
                      (Bind 'begin 13) (Bind 'substring 14) (Bind 'null 15)))

; Store
(tstruct Storage ([loc : Nonnegative-Integer] [val : Value]))
(define-type Store (Listof Storage))
(tstruct v*s ([v : Value] [s : Store]))
(define top-sto (list (Storage 0 (PrimOp '+)) (Storage 1 (PrimOp '-))
                      (Storage 2 (PrimOp '*)) (Storage 3 (PrimOp '/))
                      (Storage 4 (PrimOp '<=)) (Storage 5 (PrimOp 'equal?))
                      (Storage 6 #t) (Storage 7 #f) (Storage 8 (PrimOp 'error))
                      (Storage 9 (ArrayOp 'array))
                      (Storage 10 (ArrayOp 'new-array)) (Storage 11 (ArrayOp 'aref))
                      (Storage 12 (ArrayOp 'aset!)) (Storage 13 (ArrayOp 'begin))
                      (Storage 14 (ArrayOp 'substring))
                      (Storage 15 (ArrayOp 'null))))

; predicates
(define-predicate nonid? NonId)
(define-predicate solid-value? Solid-Value)
(define-predicate value? Value)
(define-predicate arrV? ArrayV)
(define-predicate id? IdC)



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
(define (serialize [val : v*s]) : String
  (match val
    [(v*s (? real? n) sto) (~v n)]
    [(v*s (? boolean? b) sto) (if b "true" "false")]
    [(v*s (PrimOp oper) sto) "#<primop>"]
    [(v*s (CloV param body env) sto) "#<procedure>"]
    [(v*s (? string? s) sto) (~v s)]
    [(v*s (ArrayV loc len) sto) "#<array>"]
    [(v*s (NullV 'null sto) sto)"#<null>"]))
    ;[other (error "invalid JILI ~e" val)]))
     


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
    [(list 'if rst ...)
     (match rst
       [(list condition then else) (IfC (parse condition)(parse then)(parse else))]
       [other (error 'lookup "Incorrect if statement. user-error JILI ~e" rst)])]
    [(? symbol? sym)
     (match sym
       [(? legal-id? sym)(IdC sym)]
       [other (error 'lookup
                     "Incorrect if statement. user-error JILI ~e" sym)])]
    [(list (? legal-id? id) ... '=> bdy) 
     (if (check-duplicates id)
         (error 'lookup "Id duplicates in lamC. user-error JILI ~e" id)
         (LamC (cast id (Listof Symbol)) (parse bdy)))] 
    [(list s rst ...)
     (if(equal? s ':=)
        (error 'lookup "mutating undefined JILI ~e" s)
        (AppC (parse s) (map parse rst)))]
    [other (error 'lookup "Incorrect if statement. user-error JILI ~e" s)]))
  



; lookup
; purpose: find an id in an environment
; -input: id (symbol), env (where to look for the symbol)
; -output: value (of id tied to the binding in the environment)
(define (lookup [id : Symbol] [env : Environment]) : Nonnegative-Integer
   (match env
    ['() (error 'lookup "Could not find identifier. user-error JILI ~e" id)]
    [(cons f r) (if (equal? (Bind-name f) id) (Bind-loc f) (lookup id r))]))



;; fetch
; purpose: find a num in store
; input: num (nonneg-int), stor (where to look for the num)
; output: value (of num to the binding in the storage)
(define (fetch [num : Nonnegative-Integer] [s : Store]) : Value
  (match s
    ['() (error 'fetch "value not in Store JILI ~e" num)]
    [(cons f r) (if (equal? (Storage-loc f) num) (Storage-val f) (fetch num r))]))



; arith-lookup
; purpose: Break down binary operations from concrete to abstract syntax.
; - input: s-expression
; - output: procedure
(define (arith-lookup [s : Symbol]) : (U (Real Real * -> Real)
                                         (Real Real -> Boolean) (Any Any -> Boolean))
  (match s
    ['+ +]
    ['* *]
    ['- -]
    ['/ /]
    ['<= <=]
    ['equal? equal?]
    [other (error 'lookup2 "Binary operation DNE. user-error JILI ~e" s)]))



;; lookup-arrop
; purpose: Break down primitive bindings
; input: s-expression, stor, env
; output: Listof Result (value and storage combined)
(define (lookup-arrop [s : Symbol][sto : Store][e : Environment])
  : (Nonnegative-Integer (Listof v*s) -> v*s)
  (lambda([loc : Nonnegative-Integer][vals : (Listof v*s)])
    (match s
      ; array
      ['array (v*s (ArrayV loc (length vals))
                   (allocate-store sto  vals (length vals)))]
      ; new- array
      ['new-array 
       (match (v*s-v(first vals))
         [(? exact-nonnegative-integer? n)
          (v*s (ArrayV loc n) (allocate-store sto (rest vals) n))]
         [other (error 'lookup-arrop "new-array parameters are incorrect. user-error JILI ~e" s)])]
      ; aref
      ['aref
       (match* ((v*s-v(first vals)) (v*s-v(second vals)))
         [((? arrV? arr)(? exact-nonnegative-integer? indx))
          (if (> (ArrayV-len arr) indx)
             (v*s (fetch (+ (ArrayV-loc arr) indx) sto) sto)
             (error 'lookup-arrop "index out of range JILI ~e" s))]
         [(_ _) (error 'lookup-arrop "aref parameters are incorrect. user-error JILI ~e ~e"
                       (v*s-v (first vals)) (v*s-v (second vals)))])]
      ; aset
      ['aset!
       (match* ((v*s-v(first vals)) (v*s-v(second vals)))
         [((? arrV? arr)(? exact-nonnegative-integer? indx))
          (if (>(ArrayV-len arr)indx)
             (v*s (NullV 'null (cons (Storage (+ (ArrayV-loc arr) indx)
                                              (v*s-v(last vals))) sto))
                  (cons (Storage (+ (ArrayV-loc arr) indx)
                                 (v*s-v(last vals))) sto))
             (error 'lookup-arrop "index too big JILI ~e" s))]
         [(_ _) (error 'lookup-arrop "aset! parameters are incorrect. user-error JILI ~e" s)])]
      ; substring
      ['substring
       (match* ((v*s-v(first vals)) (v*s-v(second vals)) (v*s-v(third vals)))
         [((? string? s) (? exact-nonnegative-integer? n) (? exact-nonnegative-integer? n2))
          (if (and (>= n 0) (>= (string-length s) n2) (< n n2))
           (v*s (substring s n n2) sto)
           (error 'lookup-arrop "index too big JILI ~e ~e" n n2))] 
         [(_ _ _)
          (error 'lookup-arrop "Substring parameters are incorrect. user-error JILI ~e" s)])]))) 


  
;; eval-args
; purpose: interp each argument and pass store into next argument
; - input: Listof ExprC to be evaluated, current environment and current store
; - output: Listof v*s
(: eval-args ((Listof ExprC) Environment Store -> (Listof v*s)))  
(define (eval-args exp env sto)
  (match exp
    ['() '()]
    [(cons f r)
     (define f-arg (interp f env sto))
     (match f-arg
       [(v*s val new-sto) (cons f-arg (eval-args r env new-sto))])]))



;; allocate
; purpose: updating environment and store, setting location as length of storage and adding to storage and env
; input: store, environment,
; output: new/updated environment and store
(: allocate (Store Environment (Listof Symbol) Real (Listof v*s)
                   -> (Pairof Environment Store)))
(define (allocate sto env syms n vals)
  (match n
    [0 (cons env sto)]
    [other (allocate (cons (Storage (length sto) (v*s-v(first vals))) sto)
                     (extend-env (Bind (first syms) (length sto)) env)
                     (rest syms) (- n 1) (rest vals))]))



;; allocate-store
; purpose: add values to the new store, does not add bindings in the environment
; - input:  current Store, Listof v*s values to add, length of current store
; - output: updated Store
(: allocate-store (Store (Listof v*s) Real -> Store))
(define (allocate-store sto vals num)
  (define find_vals (map
                     (lambda ([a : v*s]) (v*s-v a))
                     vals))
  (match num
    [0 sto]
    [other (allocate-store
            (cons (Storage (length sto) (v*s-v(first vals))) sto)
            (if (equal? (length vals) 1) (list (last vals)) (rest vals))
            (- num 1))]))



;; interp
; purpose: Evaluate the given expression. If the expression is a function (AppC), 
;          find the funciton in the program and evaluate with the given argument.
; - input: an ExprC and a list of FunDefC (functions in the p rogram)
; - output: a Valuee
(: interp (ExprC Environment Store -> v*s))   
(define (interp exp env sto)
  (match exp 
    [(NumC n) (v*s n sto)]
    [(StrC s) (v*s s sto)]
    [(IdC id) (v*s (fetch (lookup id env) sto) sto)]
    [(LamC param body) (v*s (CloV param body env) sto)]
    [(IfC condition then else)  
     (define eval-cond (interp condition env sto))     
     (match eval-cond
       [(v*s #t sto2) (interp then env sto2)]
       [(v*s #f sto2) (interp else env sto2)]
       [other (error 'interp "conditional cannot be evaluated to true or
                              false user-error JILI ~e" condition)])]
    [(AppC f a)
     (match (interp f env sto) 
       ; CloV
       [(v*s (CloV param body clov-env) a-sto)
        (cond
          [(equal? (length param) (length a))
           (define eargs (eval-args a env a-sto))
           (define new-store (if (equal? (length eargs) 0)
                                 a-sto
                                 (v*s-s (last eargs))))
           (define new-data (allocate new-store clov-env param
                                      (length eargs) eargs))
           (interp body (car new-data) (cdr new-data))]
          [else (error 'interp "number of args and params differ.
                               user-error. JILI ~e ~e" param a)]
          )]
       
       ; PrimOp 
       [(v*s (PrimOp p) a-sto)
        (define eargs (eval-args a env a-sto))
        (define new-store (v*s-s (last eargs)))
        (match p
          ['error (error 'interp "user-error JILI ~e" a)]
          ['equal? (match eargs
                     [(list (v*s (? solid-value? val1) _)
                            (v*s (? solid-value? val2) _))
                      (v*s (equal? val1 val2) new-store)] 
                     [other (v*s #f new-store)])]
          ['/ (match (first eargs)
                [(v*s (? real? val1) _)
                 (match (second eargs)
                   [(v*s (? real? val2) _)
                    (if(equal? val2 0) (error "division by 0. user-error JILI ~e" val2)
                       (v*s ((arith-lookup p)val1 val2) new-store))])]
                [other (error 'interp "operation and values do not match JILI ~e" a)])]
                   
          [other
           (if (equal? (length eargs) 2)
               (match* ((first eargs)(second eargs))
                 [((v*s (? real? val1) _) (v*s (? real? val2) _))
                  (v*s ((arith-lookup p) val1 val2) new-store)]
                 [(_ _) (error 'interp "operation and values do not match JILI ~e" a)])
               (error 'interp "operation and values do not match JILI ~e" a))])]
       ; ArrayOp
       [(v*s (ArrayOp arr) a-sto)
        (define eargs (eval-args a env a-sto))
        (define new-store (v*s-s (last eargs)))
        (match arr 
          ['begin
           (last eargs)]
          [other
           (define fun (lookup-arrop arr new-store env))
           (fun (length new-store) eargs)])]
       ; other
       [other
        (cond        
          [(and (IdC? f) (equal? (first a) (IdC ':=)))
           (v*s (NullV 'null (cons (Storage (lookup (IdC-sym f) env)
                                            (v*s-v (interp (last a) env sto)))
                                   (v*s-s (interp (last a) env sto))))
                (cons (Storage (lookup (IdC-sym f) env)
                               (v*s-v (interp (last a) env sto)))
                      (v*s-s (interp (last a) env sto))))]
          [else (error 'interp "non-closure, primop, or arrayop AppC.
                                user-error JILI ~e" a)])])]))



     
;; top-interp
; purpose: takes in a sexp as a expression to our language,
; returns the value of that expression
; input- sexp (expression)
; output- String (String representation of the result of the expression)
(define (top-interp [s : Sexp]) : String
  (serialize (interp (parse s) top-env top-sto)))



; TEST CASES
;_______________________________________________________________________________________________________
;_______________________________________________________________________________________________________

(define guard '{=> {<= 0 x}})
(define body  '{=> {x := {- x 1}}})

(define while
  `{var {[while = "placeholder"]}
   in
   {begin {while := {g b => {if {g}
                                {begin {b}
                                          {while g b}}
                                "done"}}}
          while}})



(define guard1 '{=> {<= 2 num}})
(define body1 '{=> {begin
                     {if {<= {aref arr {- num 2}} {aref arr {- num 1}}}
                         {+ 1 2}
                         {inc := 0}}
                     {num := {- num 1}}}})

(define in-order
  `{var {[in-order = "placeholder"]
         [inc = 1]} ; 1 means increase, 0 means decreasing
        in
        {begin
          {in-order := {arr num =>
                            {begin
                              {,while ,guard1 ,body1}
                              {if {equal? inc 1}
                               true
                               false}}}}
          in-order}})
 



; TEST CASES

; serialize tests
(check-equal? (serialize (v*s (PrimOp '+) top-sto)) "#<primop>")
(check-equal? (serialize (v*s "Hello" top-sto)) "\"Hello\"")

; get-id tests
(check-equal? (get-id '(x = 24)) 'x) 
(check-exn #px"JILI" (lambda () (get-id '(hi world))))

; get-val tests
(check-equal? (get-val '(x = 24)) 24)
(check-exn #px"JILI" (lambda () (get-val '(hi world))))

; fetch test
(check-equal? (fetch 0 top-sto)(PrimOp'+))
(check-exn #px"JILI" (lambda () (fetch 20 top-sto)))

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

; error checking - parse
(check-exn #px"JILI" (lambda () (parse '{if {<= 3 4} 4})))
(check-exn #px"JILI" (lambda () (parse '{x x => (+ x 2)})))
(check-exn #px"JILI" (lambda () (parse '{var x => (+ + 2)})))
(check-exn #px"JILI" (lambda () (parse '(:= true false null))))
(check-exn #px"JILI" (lambda () (parse '{})))


 
; arith-lookup tests
(check-equal? (arith-lookup '*) *)
(check-equal? (arith-lookup '+) +)
(check-equal? (arith-lookup '/) /)
(check-equal? (arith-lookup '-) -)
(check-equal? (arith-lookup '<=) <=)
(check-equal? (arith-lookup 'equal?) equal?)
(check-exn #px"JILI" (lambda () (arith-lookup 'a)))


; interp tests
(check-equal? (v*s-v(interp (NumC 3) top-env top-sto)) 3)

(check-equal? (v*s-v(interp (AppC (LamC '(x y) (AppC (IdC '/) (list (IdC 'x) (IdC 'y))))
                            (list (AppC (IdC '+) (list (NumC 9) (NumC 16))) (NumC 5))) top-env top-sto))
              5)
(check-equal? (v*s-v(interp (AppC (LamC '(x y) (AppC (IdC '+) (list (IdC 'x) (IdC 'y))))
                            (list (AppC (IdC '+) (list (NumC 9) (NumC 14))) (NumC 98))) top-env top-sto))
              121)
(check-equal? (v*s-v(interp (AppC (LamC '(x y) (AppC (IdC '<=) (list (IdC 'x) (IdC 'y))))
                            (list (AppC (IdC '+) (list (NumC 9) (NumC 14))) (NumC 98))) top-env top-sto))
               #t)
(check-equal? (v*s-v(interp (AppC (LamC '(x y) (AppC (IdC 'equal?) (list (IdC 'x) (IdC 'y))))
                            (list (NumC 2) (NumC 2))) top-env top-sto))
              #t)
(check-equal? (v*s-v(interp (AppC (LamC '(x y) (AppC (IdC 'equal?) (list (IdC 'x) (IdC 'y))))
                            (list (NumC 1) (NumC 2))) top-env top-sto))
              #f)
(check-equal? (v*s-v(interp (LamC '(x y) (AppC (IdC '+) (list (IdC 'x) (IdC 'y)))) top-env top-sto))
              (CloV '(x y) (AppC (IdC '+) (list (IdC 'x) (IdC 'y))) top-env)) 
(check-equal?(v*s-v(interp (StrC "Hello") top-env top-sto)) "Hello")
(check-equal? (v*s-v(interp(IfC (AppC (IdC '<=) (list (NumC 3) (NumC 4))) (NumC 4) (NumC 5)) top-env top-sto))4)

(check-equal? (v*s-v(interp (AppC (LamC '(x y) (IfC (AppC (IdC '<=) (list (IdC 'x) (IdC 'y))) (NumC 4) (NumC 5)))
                            (list (AppC (IdC '+) (list (NumC 9) (NumC 14))) (NumC 98))) top-env top-sto))
              4)

(check-equal? (v*s-v(interp (AppC (LamC '(x y) (IfC (AppC (IdC 'equal?) (list (IdC 'x) (IdC 'y))) (NumC 4) (NumC 5)))
                            (list (AppC (IdC '+) (list (NumC 9) (NumC 14))) (NumC 98))) top-env top-sto))
              5)
(check-equal? (v*s-v(interp (AppC (LamC '(x y) (IfC (AppC (IdC 'equal?) (list (IdC 'x) (IdC 'y))) (IdC 'x) (IdC 'y)))
                            (list (AppC (IdC '+) (list (NumC 9) (NumC 14))) (NumC 98))) top-env top-sto))
              98)

(check-true (v*s-v(interp (AppC (IdC 'equal?) (list (StrC "hello") (StrC "hello"))) top-env top-sto)))
(check-false (v*s-v(interp (AppC (IdC 'equal?) (list (StrC "hello") (IdC '+))) top-env top-sto)))

(check-equal? (v*s-v (interp (parse '{new-array 10 "hi"}) top-env top-sto)) (ArrayV 16 10))
(check-equal?(v*s-v(interp (parse '{array (* 5 3) (/ 6 3) (+ 1 2)
                                          (if true true false)}) top-env top-sto))(ArrayV 16 4))

(check-equal?(v*s-v(interp (parse '{aref (array "hi" 1 "cool") 2})
                           top-env top-sto))"cool")



(check-equal?(v*s-v(interp (parse '{aref (array "hi" 1 (new-array 10 "ten")) 2})
                           top-env top-sto))(ArrayV 16 10))
(check-equal?(list-ref (v*s-s(interp (parse '{aset! (array "hi" 1
                                                           (new-array 10 "ten")) 2 (+ 3 4)})
                                     top-env top-sto)) 0) (Storage 28 7))

(check-equal? (v*s-v(interp (parse '{var {[z = 10]
                      [y = 98]} 
                     in
                     {begin {z := 20} 
                            {+ z y}}}) top-env top-sto))118)
(check-equal?(v*s-v(interp (parse '{var {[z = "hello world"]
                      [y = 5] 
                      [x = 6]} 
                     in 
                     {begin (x := 9)
                            {substring z y x}}}) top-env top-sto))" wor")

; Error checking - interp

(check-exn #px"JILI" (lambda () (arith-lookup 'a)))
(check-exn #px"JILI"
           (lambda ()(interp (AppC (AppC (IdC 'var)
                                         (list
                                          (AppC (AppC (IdC 'z=) (list (AppC (IdC '+) (list (NumC 9) (NumC 14)))))
                                                               (list (AppC (IdC 'y) (list (IdC '=) (NumC 98)))
                                                                     (IdC 'in)
                                                                     (AppC (IdC '+) (list (IdC 'x) (IdC 'y))))))) '())
                             top-env top-sto)))


(check-exn #px"JILI" (lambda () (interp (AppC (IdC '+) (list (StrC "hello") (StrC "world"))) top-env top-sto)))

(check-exn #px"JILI" (lambda () (interp (AppC (IdC '+) (list (NumC 1) (NumC 1) (NumC 1))) top-env top-sto)))



 
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
(check-equal?(top-interp '{new-array 10 "hi"})"#<array>")
(check-equal? (top-interp '{aset! {array 1 2 3} 1 5}) "#<null>")
(check-equal? (top-interp '{{=> 9}}) "9")
(check-equal?(top-interp  '{{seven => {seven}}
          {{minus =>
                  (=> (minus 13 6))}
           (x y => (* -1 y))}})"-6")

; error checking - top interp

(check-exn #px"JILI" (lambda() (top-interp '{aref {array "hi" 1 "cool"}3})))
(check-exn #px"JILI" (lambda() (top-interp '{if {+ 2 3}3 4})))

(check-exn #px"JILI" (lambda () (top-interp '{1})))
(check-exn #px"JILI" (lambda () (top-interp '(error {+ 1 4}))))
(check-exn #px"JILI" (lambda () (top-interp '(error {+ 1 {- 2 4}}))))
(check-exn #px"JILI"(lambda ()(top-interp '(+ if 4))))
(check-exn #px"JILI" (lambda ()(top-interp '((=> 9)17)))) 
(check-exn #px"JILI" (lambda () (top-interp '(/ 1 (- 3 3)))))
(check-exn #px"JILI" (lambda () (top-interp '(/ true (- 3 3)))))
(check-exn #px"JILI" (lambda ()(top-interp '(+ + +))))
(check-exn #px"JILI" (lambda ()(top-interp '{+ 2 +})))
(check-exn #px"JILI" (lambda ()(top-interp '{substring "abcd"  0 0.45})))


(check-exn #px"JILI" (lambda ()(top-interp '(var ((f = (new-array 5 false))) in (aset! f 5 19))))) 

(check-exn #px"JILI" (lambda ()(top-interp '(var ((f = (new-array 5 false))) in (aset! f -1 19)))))


(check-exn #px"JILI" (lambda ()(top-interp '(var ((f = (new-array 2.1 false))) in (aset! f 1 19)))))


(check-exn #px"JILI" (lambda () (top-interp '{aref {array 4 0} "hello"})))
(check-exn #px"JILI" (lambda () (top-interp '{substring "hello" 0 20})))

; test cases - in order/while
(check-equal?(top-interp `{var ({while = ,while})
              in
              {var ({in-order = ,in-order})
                in
                {in-order {array 3 10 8} 3}}})"false")

(check-equal?(top-interp `{var ({while = ,while})
              in
              {var ({in-order = ,in-order})
                in
                {in-order {array 3 5 8} 3}}})"true")
(check-equal?(top-interp `{var {[while = ,while]
                     [x = 16]}
                    in
                    {begin {while ,guard ,body} x}})"-1")