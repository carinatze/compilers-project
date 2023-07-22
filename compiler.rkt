#lang racket

(require
 cpsc411/compiler-lib
 cpsc411/2c-run-time
 cpsc411/langs/v6
 cpsc411/graph-lib
 racket/trace
 rackunit
 "impose-calling-conventions.rkt"
 "select-instructions.rkt"
 "uncover-locals.rkt"
 "undead-analysis.rkt"
 "conflict-analysis.rkt"
 "allocate-frames.rkt"
 "replace-locations.rkt"
 "implement-fvars.rkt"
 "generate-x64.rkt")

(provide
 uniquify
 sequentialize-let
 normalize-bind
 assign-call-undead-variables
 assign-registers
 assign-frame-variables
 optimize-predicates
 expose-basic-blocks
 resolve-predicates
 flatten-program
 patch-instructions)

(define-values (assign-call-undead-variables
                assign-frame-variables
                optimize-predicates)
  (values
   values
   values
   values))

;; values-lang-v3 -> values-unique-lang-v3
;; Resolves all levical identifiers to abstract locations
(define (uniquify p)

  ; (Values-lang-v3 p) (Listof aloc) -> (Values-unique-lang-v3 p) 
  ; Accumulator: holds the abstract locations so far 
  ; Maps over tail in p with uniquify-ta, passing in two: a list of alocs and the tail
  ; statement to implement the assignment of lexical identifiers to abstract locations
  (define (uniquify-p p acc)
    (match p
      [`(module ,s ...) 
      `(module ,@(map (lambda (s) (uniquify-ta s acc)) s))]))  
  
  ;; (Values-lang-v3 tail) (Listof aloc) -> (Values-unique-lang-v3 tail)
  ;; acc: the list of abstract locations so far
  ;; Takes in tail statement and list of abstract locations
  ;; defines fresh abstract locations for each new lexical identifier it encouters in the statement
  ;; recursively calls on the (Values-lang-v3 values) and nested (Values-lang-v3 tail)
  (define (uniquify-ta ta acc)
    (match ta
      [`(let ([,xs ,vs] ...) ,tail) 
        (define new-acc
          (for/fold ([new-acc acc])
                    ([x xs])
            (dict-set new-acc x (fresh))))
        (let ([new-alocs
              (for/list  ([x xs]
                          [v vs])
                `(,(uniquify-v x new-acc) ,(uniquify-v v acc)))])
          `(let (,@ new-alocs) ,(uniquify-v tail new-acc)))]
      [_ (uniquify-v ta acc)]))

  ;; (Values-lang-v3 value) (Listof aloc) -> (Values-unique-lang-v3 value)
  ;; Accumulator: [ListOf aloc] 
  ;; accumulator is the list of fresh abstract locations defined so far
  ;; Takes in value statement and list of abstract locations
  ;; defines fresh abstract locations for each new lexical identifier it encouters in the value statement
  ;; recursively calls on the nested and corresponding (Values-lang-v3 values) 
  (define (uniquify-v v acc)
    (match v
      [`(let ([,xs ,vs] ...) ,value) 
         (define new-acc
          (for/fold ([new-acc acc])
                    ([x xs])
                    (dict-set new-acc x (fresh))))
           (let ([new-alocs
              (for/list  ([x xs]
                          [v vs])
                `(,(uniquify-v x new-acc) ,(uniquify-v v acc)))])
                `(let (,@ new-alocs) ,(uniquify-v value new-acc)))]
      [`(,binop ,triv_1 ,triv) 
      #:when(binop? binop) 
      `(,binop ,(uniquify-t triv_1 acc) ,(uniquify-t triv acc))]
      [triv 
      #:when(triv? triv) 
      (uniquify-t triv acc)]
      [_ v])) 

  ;; triv (Listof aloc) -> triv
  ;; Returns the value of corresponding abstract location stored in the acc if triv t is a name,
  ;; else it returns t itself if it is an int64?
  (define (uniquify-t t acc)
    (match t
      [(? int64?) 
      t]
      [(? name?) 
      (dict-ref acc t)]))

   ;; binop -> boolean
  ;; returns true if binop is a + or *
  (define (binop? b)
    (or (eq? b '+) (eq? b '*)))
  
  ;; triv -> boolean
  ;; returns true if triv is an int64? or name?
  (define (triv? t)
    (or (int64? t) (name? t)))

  (uniquify-p p `()))
#|
(module+ test
(require rackunit)
(check-equal? (interp-values-lang-v3 '(module (let ((x (let ((y 1)) y)) (y 2)) (+ x y)))) 
              (interp-values-unique-lang-v3 (uniquify '(module (let ((x (let ((y 1)) y)) (y 2)) (+ x y))))))

(check-equal? (interp-values-lang-v3 '(module (let ((x 1) (y (let ((z 5)) z)) (z (let ((y 2)) (* y y)))) (+ y z)))) 
              (interp-values-unique-lang-v3 (uniquify '(module (let ((x 1) (y (let ((z 5)) z)) (z (let ((y 2)) (* y y)))) (+ y z))))))

(check-equal? (interp-values-lang-v3  '(module (let ([x 5] [y (+ 3 1)]) x))) 
              (interp-values-unique-lang-v3 (uniquify '(module (let ([x 5] [y (+ 3 1)]) x)))))

(check-equal? (interp-values-lang-v3 '(module (let ([x 5]) (let ([y 5]) (+ x y))))) 
              (interp-values-unique-lang-v3 (uniquify '(module (let ([x 5]) (let ([y 5]) (+ x y)))))))

(check-equal? (interp-values-lang-v3 '(module (let ([x 5]) (let ([y (+ 2 3)] [x (* 7 5)]) (+ y x)))))
              (interp-values-unique-lang-v3 (uniquify '(module (let ([x 5]) (let ([y (+ 2 3)] [x (* 7 5)]) (+ y x)))))))

(check-equal? (interp-values-lang-v3 '(module (let ([z 5]) (let ([y (* 2 1)] [x 20]) (+ y z)))))
              (interp-values-unique-lang-v3 (uniquify '(module (let ([z 5]) (let ([y (* 2 1)] [x 20]) (+ y z)))))))

(check-equal? (interp-values-lang-v3 '(module (let ((v 5)) (let ((s 4)) (let ((x v)) (let ((x (+ x 7))) (let ((y x)) (let ((y (* y 2))) (let ((z x)) (let ((z (+ z s))) (let ((t y)) (let ((t (* t 1))) (let ((z (* z t))) z))))))))))))) 
              (interp-values-unique-lang-v3 (uniquify '(module (let ((v 5)) (let ((s 4)) (let ((x v)) (let ((x (+ x 7))) (let ((y x)) (let ((y (* y 2))) (let ((z x)) (let ((z (+ z s))) (let ((t y)) (let ((t (* t 1))) (let ((z (* z t))) z)))))))))))))))

(check-equal? (interp-values-lang-v3 '(module (let ((x 2)) (let ((x (* 8 x))) x)))) 
              (interp-values-unique-lang-v3 (uniquify '(module (let ((x 2)) (let ((x (* 8 x))) x)))))))
|#
#| values-unique-lang-v3:
  p ::=	(module tail)
  tail ::= value
 	 	   |	(let ([aloc value] ...) tail)
  value ::= triv
 	 	    | (binop triv triv)
 	 	    | (let ([aloc value] ...) value)
 	triv ::= int64
 	 	    | aloc
  binop ::= * | +
|#
;; values-unique-lang-v3 -> imp-mf-lang-v3
;; picks particuluar order to implement let expressions using set!
(define (sequentialize-let p)
  ;; (Values-unique-lang-v3 p) -> (imp-mf-lang-v3 p)
  ;; Takes in (Values-unique-lang-v3 p) statement and returns (imp-mf-lang-v3 p) by calling sequentialize-let-t on the tail statement
  (define (sequentialize-let-p p)
    (match p
      [`(module ,tail) 
      `(module ,(sequentialize-let-t tail))]))

  ;; (Values-unique-lang-v3 tail) -> (imp-mf-lang-v3 tail)
  ;; Takes in (Values-unique-lang-v3 tail) statement and returns (imp-mf-lang-v3 tail) 
  ;; by defining new set statements for each aloc and calling sequentilize-let-lv on the value v within the pair
  ;; and recursively calls sequentilize-let-t on the nested tail statement
  (define (sequentialize-let-t t)
    (match t
      [`(let ([,as ,vs] ...) ,tail) 
        (let ([new-effects
              (for/list  ([a as]
                          [v vs])
                `(set! ,a ,(sequentialize-let-v v)))])
          `(begin ,@new-effects ,(sequentialize-let-t tail)))]
      [_ (sequentialize-let-v t)]))

  ;;; (Values-unique-lang-v3 value) -> (imp-mf-lang-v3 value)
  ;; Takes in (Values-unique-lang-v3 value) statement and returns (imp-mf-lang-v3 value) 
  ;; by defining new set statements for each aloc and calling sequentilize-let-v on the value v within the pair
  ;; and recursively calls sequentilize-let-v on the nested tail statement
  ;; else it returns the value
  (define (sequentialize-let-v v)
     (match v
      [(? triv?) v]
      [`(,binop ,triv_1 ,triv) 
      #:when(and (binop? binop) 
                (triv? triv_1) 
                (triv? triv_1)) v]
      [`(let ([,as ,vs] ...) ,value)
        (let ([new-effects
              (for/list  ([a as]
                          [v vs])
                `(set! ,a ,(sequentialize-let-v v)))])
        `(begin ,@new-effects ,(sequentialize-let-v value)))]))

  ;; triv -> boolean
  ;; returns true if triv is an int64 or aloc
  (define (triv? t)
    (or (int64? t) (aloc? t)))

  ;; binop -> boolean
  ;; returns true if binop is a + or *
  (define (binop? b)
    (or (eq? b '+) (eq? b '*)))

  (sequentialize-let-p p))
#|
(module+ test
(require rackunit)
(check-equal? (interp-values-unique-lang-v3 '(module (let ((x.1 5) (y.1 (let ((z.1 (+ 7 8))) z.1))) (+ x.1 y.1))))
              (interp-imp-mf-lang-v3 (sequentialize-let '(module (let ((x.1 5) (y.1 (let ((z.1 (+ 7 8))) z.1))) (+ x.1 y.1))))))
(check-equal? (interp-values-unique-lang-v3 '(module (let ((x.1 2)) (let ((y.6 2)) (* x.1 y.6)))))
              (interp-imp-mf-lang-v3 (sequentialize-let '(module (let ((x.1 2)) (let ((y.6 2)) (* x.1 y.6)))))))
(check-equal? (interp-values-unique-lang-v3 '(module (let ((x.1 2) (x.4 4)) (let ((x.3 2)) (+ x.3 x.3)))))
              (interp-imp-mf-lang-v3 (sequentialize-let '(module (let ((x.1 2) (x.4 4)) (let ((x.3 2)) (+ x.3 x.3))))))))
|#

#| Asm-lang-v2/locals:
   p ::= (module info tail)
  info ::= (#:from-contract (info/c (locals (aloc ...))))
  tail ::= (halt triv)
 	 	|	 	(begin effect ... tail)
 	effect ::= (set! aloc triv)
 	 	|	 	(set! aloc_1 (binop aloc_1 triv))
 	 	|	 	(begin effect ... effect)
 	triv ::= int64
 	 	|	 	aloc
|#
;; (Asm-lang-v2/locals) -> (Asm-lang-v2/assignments)
;; assigns each abstract location from the locals info field to a fresh frame variable
(define (assign-fvars p)

  ;; (asm-lang-v2-locals p) -> (asm-lang-v2/assignments p)
  ;; Takes in (asm-lang-v2-locals p) and returns (asm-lang-v2/assignments p) by calling assign-fvars-s on all
  ;; the locals from the info field
  (define (assign-fvars-p p)
    (match p
      [`(module ((locals (,xs ...))) ,llb) 
      `(module ((locals ,xs) ,(assign-fvars-s xs)) ,llb)]))

  ;; (asm-lang-v2-locals (listof aloc)) -> (asm-lang-v2/assignments (listof fvar))
  ;; iterates through all the list of abstract locations and defines a fresh new frame variable with the same index
  (define (assign-fvars-s s)
  (if (eq? (length s) 0)
    `(assignment ())
    `(assignment (,@(for/list ([i (in-naturals 0)]
                              [f s]) 
                              `(,f ,(make-fvar i)))))))

  (assign-fvars-p p))

#|
(module+ test
  (require rackunit)

  (check-equal? 
    (interp-asm-lang-v2/assignments (assign-fvars '(module ((locals ())) (halt 5))))
     (interp-asm-lang-v2/locals '(module ((locals ())) (halt 5))))

  (check-equal? 
    (interp-asm-lang-v2/assignments (assign-fvars
    '(module
        ((locals (x.1 x.4 x.3 x.2)))
        (begin
          (set! x.1 0)
          (set! x.2 3)
          (set! x.3 0)
          (set! x.4 20)
          (halt x.4)))))
     (interp-asm-lang-v2/locals 
    '(module
        ((locals (x.1 x.4 x.3 x.2)))
        (begin
          (set! x.1 0)
          (set! x.2 3)
          (set! x.3 0)
          (set! x.4 20)
          (halt x.4))))))
|#

#| Block-pred-lang-v4:
  p	 	::=	 	(module b ... b) 	 	 
  b	 	::=	 	(define label tail)
  pred	 	::=	 	(relop loc opand)
 	 	|	 	(true)
 	 	|	 	(false)
 	 	|	 	(not pred)
 	 	 	 	 
  tail	 	::=	 	(halt opand)
 	 	|	 	(jump trg)
 	 	|	 	(begin effect ... tail)
 	 	|	 	(if pred (relop loc opand) (jump trg) (jump trg))
 	 	 	 	 
  effect	 	::=	 	(set! loc triv)
 	 	|	 	(set! loc_1 (binop loc_1 opand))
 	 	 	 	 
  opand	 	::=	 	int64
 	 	|	 	loc
 	 	 	 	 
  loc	 	::=	 	reg
 	 	|	 	fvar
|#
;; (Block-pred-lang-v4) -> (block-asm-lang-v4)
;; manipulates if statement branches to resolve branches
(define (resolve-predicates p) 
  (define (resolve-predicates-p p)
    (match p
      [`(module ,xb ... ,b)
        `(module ,@(map resolve-predicates-b xb) ,(resolve-predicates-b b))]))
  
  ; (block-pred-lang-v4 b) -> (block-asm-lang-v4 b)
  ; compiles (block-pred-lang-v4 b) to (block-asm-lang-v4 b) by calling resolve-preicates-tail on tail
  (define (resolve-predicates-b b)
    (match b
      [`(define ,label ,tail)
        `(define ,label ,(resolve-predicates-tail tail))]))

  ; (block-pred-lang-v4 pred trg trg) -> (block-asm-lang-v4 tail)
  ; compile preds into either simple (relop loc opand) or simplifly and eliminate them entirely when obviously false or true
  (define (resolve-predicates-pred pred trg_1 trg_2)
    (match pred
      [`(,relop ,loc ,opand)
      #:when (and (relop? relop)
                  (loc? loc)
                  (opand? opand))
        `(if ,pred (jump ,trg_1) (jump ,trg_2))]
      [`(true)
        `(jump ,trg_1)]
      [`(false)
        `(jump ,trg_2)]
      [`(not ,pred)
        (resolve-predicates-pred pred trg_2 trg_1)]))
  
  ; (block-pred-lang-v4 tail) -> (block-asm-lang-v4 tail)
  ; compiles tail by rewriting if statements with obvious predicates, calling on resolve-predicates-pred for all predicates
  (define (resolve-predicates-tail t)
    (match t
      [`(halt ,opand)
        #:when (opand? opand)
        t]
      [`(jump ,trg)
        t]
      [`(begin ,effect ... ,tail)
        `(begin ,@(map resolve-predicates-effect effect) 
                ,(resolve-predicates-tail tail))]
      [`(if ,pred (jump ,trg_1) (jump ,trg_2))
        (resolve-predicates-pred pred trg_1 trg_2)]))
  
  ; (block-pred-lang-v4 effect) -> (block-asm-lang-v4 effect)
  ; compiles effect by rewriting if statements with obvious predicates, calling on resolve-predicates-pred for all predicates
  (define (resolve-predicates-effect t)
    (match t
      [`(set! ,loc ,triv)
        t]
       [`(set! ,loc_1 (,binop ,loc_1 ,opand))
       #:when (and (loc? loc_1) 
                    (opand? opand) 
                    (binop? binop))
        t]))

  (define (triv? triv)
    (or (int64? triv) (opand? triv)))
  
  ;; opand -> boolean
  ;; returns true if opand t is a opand?
  (define (opand? opand)
    (or (int64? opand) (loc? opand)))

  ;; loc -> boolean
  ;; returns true if loc loc is a loc?
  (define (loc? loc)
    (and  (or (register? loc) (fvar? loc))))

  ;; binop -> boolean
  ;; returns true if binop is a + or *
  (define (binop? b)
      (or (eq? b '+) (eq? b '*)))

  ;; relop -> boolean
  ;; returns true if relop t is a relop?
  (define (relop? relop)
     (match relop
     ['< #t]
     ['<= #t]
     ['= #t]
     ['>= #t]
     ['> #t]
     ['!= #t]
     [_ #f]))

  (resolve-predicates-p p))

(module+ test
(require rackunit)
(define rp-7 
'(module 
(define L.start.1 
(if (not (false)) (jump L.start.2) (jump L.start.3))) 
(define L.start.2 (halt 0)) 
(define L.start.3 (halt 120))))
(check-equal?
(resolve-predicates rp-7)
'(module
  (define L.start.1 (jump L.start.2))
  (define L.start.2 (halt 0))
  (define L.start.3 (halt 120))))


(define rp-1
'(module
(define L.main.1
(begin 
(set! r8 10)
(set! r9 11)
(if (true) (jump r8) (jump r9))))))


(define rp-2
'(module
(define L.main.1
(begin 
(set! r8 10)
(set! r9 11)
(if (false) (jump r8) (jump r9))))))

(define rp-3
'(module
(define L.main.1
(begin 
(set! r8 10)
(set! r9 11)
(if (not (false)) (jump r8) (jump r9))))))

(define rp-4
'(module
(define L.main.1
(begin 
(set! r8 10)
(set! r9 11)
(if (not (true)) (jump r8) (jump r9))))))

(define rp-5
'(module
(define L.main.1
(begin 
(set! r8 10)
(set! r9 11)
(if (> r8 7) (jump r8) (jump r9))))))

(define rp-6
'(module
(define L.main.1
(begin 
(set! r8 10)
(set! r9 11)
(if (not (> r8 7)) (jump r8) (jump r9))))))

(check-equal?
(resolve-predicates rp-1)
'(module (define L.main.1 (begin (set! r8 10) (set! r9 11) (jump r8)))))

(check-equal?
(resolve-predicates rp-2)
'(module (define L.main.1 (begin (set! r8 10) (set! r9 11) (jump r9)))))

(check-equal?
(resolve-predicates rp-3)
'(module (define L.main.1 (begin (set! r8 10) (set! r9 11) (jump r8)))))

(check-equal?
(resolve-predicates rp-4)
'(module (define L.main.1 (begin (set! r8 10) (set! r9 11) (jump r9)))))

(check-equal?
(resolve-predicates rp-5)
'(module (define L.main.1 (begin (set! r8 10) (set! r9 11) (if (> r8 7) (jump r8) (jump r9))))))

(check-equal?
(resolve-predicates rp-6)
'(module (define L.main.1 (begin (set! r8 10) (set! r9 11) (if (> r8 7) (jump r9) (jump r8)))))))

#| nested-asm-lang-v2:
  p ::= tail
  tail ::= (halt triv)|	 	(begin effect ... tail)
  effect ::= (set! loc triv) |	 	(set! loc_1 (binop loc_1 triv))|	 	(begin effect ... effect)
  triv ::=	int64|	 	loc
  loc ::= reg|	 	fvar
  binop ::= * | +
|#
;; (nested-asm-lang-v2) -> (para-asm-lang-v2)
;; flattens nested instructions to minimize the number of begins
(define (flatten-begins p)
  
  ;; (nested-asm-lang-v2 p) -> (para-asm-lang-v2 p)
  ;; calls flatten-begins-s on the list of effects and flatten-begins-t on tail, if matches pattern
  (define (flatten-begins-p p)
    (match p
      [`(begin ,xs ... ,t) 
      (make-begin-effect `(,@(append-map flatten-begins-s xs) ,@(flatten-begins-t t)))]
      [`(begin ,xs ...) 
      (make-begin-effect `(,@(append-map flatten-begins-s xs)))]
      [_ `(begin ,p)]))

  ;; (nested-asm-lang-v2 tail) -> (para-asm-lang-v2 tail)
  ;; calls flatten-begins-s on the list of effects and recursively calls flatten-begins-t on the nested tail statement
  ;; to return (para-asm-lang-v2 tail)
  (define (flatten-begins-t t)
    (match t
      [`(halt ,triv) 
      #:when (or (int64? triv) 
                (loc? triv))
      (list t)]
      [`(begin ,xs ... ,t)
      `(,@(append-map flatten-begins-s xs) ,@(flatten-begins-t t))]))

  ;; (nested-asm-lang-v2 effect) -> (para-asm-lang-v2 effect)
  ;; appends the list of effects into a single list to flatten nested begins
  (define (flatten-begins-s s)
    (match s
      [`(set! ,loc ,triv) 
      `((set! ,loc ,triv))]
      [`(set! ,loc_1 (,binop ,loc_1 ,triv)) 
      `((set! ,loc_1 (,binop ,loc_1 ,triv)))]
      [`(begin ,xs ...) 
      `(,@(append-map flatten-begins-s xs))]))

  ;; loc? -> boolean
  ;; returns true if loc is loc?
  (define (loc? loc)
    (or (register? loc) (fvar? loc)))

  (flatten-begins-p p))
#|
(module+ test
  (require rackunit)

   (check-equal? (interp-nested-asm-lang-v2 
    '(begin (begin (halt 5))))
    (interp-para-asm-lang-v2 
    (flatten-begins 
    '(begin (begin (halt 5))))))

  (check-equal? (interp-nested-asm-lang-v2 
    '(halt 5))
    (interp-para-asm-lang-v2 
    (flatten-begins 
    '(halt 5))))

  (check-equal? (interp-nested-asm-lang-v2 
    '(halt fv0))
    (interp-para-asm-lang-v2 
    (flatten-begins 
    '(halt fv0))))

(check-equal? (interp-nested-asm-lang-v2 
    '(begin (set! fv0 0) (set! fv0 (+ fv0 1)) (halt 1)))
    (interp-para-asm-lang-v2 
    (flatten-begins 
    '(begin (set! fv0 0) (set! fv0 (+ fv0 1)) (halt 1)))))

  (check-equal? (interp-nested-asm-lang-v2 
    '(begin (begin (set! fv0 1) (set! fv1 2)) (set! fv0 (+ fv0 10)) (set! fv1 (+ fv1 fv0)) (halt fv1)))
    (interp-para-asm-lang-v2 
    (flatten-begins 
    '(begin (begin (set! fv0 1) (set! fv1 2)) (set! fv0 (+ fv0 10)) (set! fv1 (+ fv1 fv0)) (halt fv1))))))|#


#| Para-asm-lang-v4:
    p	::=	(begin s ...)
 	  s	::=	 	(halt opand)
    |   (set! loc triv)
 	 	|	 	(set! loc_1 (binop loc_1 opand))
 	 	|	 	(jump trg)
 	 	|	 	(with-label label s) ;; TODO: does this mean there can only be one effect
 	 	|	 	(compare loc opand)
 	 	|	 	(jump-if relop trg)
 	triv ::= opand | label
  trg	 	::=	 	label |	 	loc
  opand ::= int64 | loc
  loc	 ::=	 reg |	fvar
   relop	 	::=	 	<
 	 	|	 	<=
 	 	|	 	=
 	 	|	 	>=
 	 	|	 	>
 	 	|	 	!=
  binop ::= * | +
|#
;; reference: lily's office hours
;; (Para-asm-lang-v4) -> (Paren-x64-fvars-v4) 
;; patching instructions that have no x64 anaolgue into sequence of instructions using auxillary registers
(define (patch-instructions p)

  ;; (Para-asm-lang-v4 p) -> (Paren-x64-fvars-v4 p) 
  ;; maps call to patch-instructions-s to each s statement
  (define (patch-instructions-p p)
    (match p
      [`(begin ,xs ...) 
      `(begin ,@(append-map patch-instructions-s xs))])) 

  ;; (Para-asm-lang-v4 effect) -> (Paren-x64-fvars-v4 effect) 
  ;; calls patch-instruction-register on each effect that have no x64 analogue
  ;; or generates instruction with current-return-value-register for compiling halt
  (define (patch-instructions-s s)
    (match s
      [`(halt ,opand) 
      #:when(opand? opand)
      (list `(set! ,(current-return-value-register) ,opand) 
            `(jump done))]
      [`(set! ,loc ,triv) 
        #:when (and (loc? loc) 
                    (triv? triv)) 
        (if (and (fvar? loc) (fvar? triv))
          (let-values ([(x y) (patch-instruction-register s)]) `(,x ,y))
          (list s))]  
      [`(set! ,loc_1 (,binop ,loc_1 ,opand)) 
        #:when (and (loc? loc_1) 
                    (opand? opand) 
                    (binop? binop))
        (if (fvar? loc_1)
        (let-values ([(x y z) (patch-instruction-register-three s)]) `(,x ,y ,z))
        (list s))]                             
      [`(jump ,trg) 
      #:when(trg? trg) 
      (list s)]
      [`(with-label ,label ,s)
      #:when(label? label) 
      (define list-s (patch-instructions-s s))
      (cons `(with-label ,label ,(first list-s)) 
            `,(rest list-s))]
      [`(compare ,loc ,opand) 
      #:when(and (loc? loc) 
                  (opand? opand))
      (cond 
      [(and (fvar? loc)
            (int64? opand)) ;; compare curr-reg opand
      (let-values ([(x y) (patch-instruction-register s)]) `(,x ,y))]
      [(and (register? loc)
            (int64? opand))
      (list `(compare ,loc ,opand))]
      [(and (fvar? loc)
            (register? opand)) ;; compare curr-reg opand
      (let-values ([(x y) (patch-instruction-register s)]) `(,x ,y))]
      [(and (register? loc)
            (register? opand))
      (list `(compare ,loc ,opand))]
      [(and (register? loc)
            (fvar? opand)) ;; compare reg curr-reg
      (let-values ([(x y) (patch-instruction-register s)]) `(,x ,y))]
      [(and (fvar? loc)
            (fvar? opand)) ;; compare curr-reg curr-reg-1
      (let-values ([(x y z) (patch-instruction-register-three s)]) `(,x ,y ,z))])] 
      [`(jump-if ,relop ,trg) 
      #:when(and (relop? relop) 
                  (trg? trg)) 
      (if (loc? trg)
      (let-values ([(x y) (patch-instruction-register s)]) `(,x ,y))
      (list s))]
      ))
  
  ;; (Para-asm-lang-v4 value) -> (listof (Paren-x64-fvars-v4 value))
  ;; assigns auxiliary registers from current-patch-instructions-registers to generate two instruction sequences 
  (define (patch-instruction-register v)
    (match v
      [`(set! ,loc ,triv)  
      (if (or (equal? '(r11) current-patch-instructions-registers) 
          (equal? '(r10 r11) (current-patch-instructions-registers)))
      (current-patch-instructions-registers 'r10)
      (current-patch-instructions-registers 'r11))
      (let ([curr-reg (if (equal? current-patch-instructions-registers 'r11) 'r10 'r11)])
            (values `(set! ,curr-reg ,triv)
                    `(set! ,loc ,curr-reg)))]
      [`(jump-if ,relop ,trg)
      #:when(and (relop? relop)
                  (trg? trg))
        (define new-label (fresh-label))
        (if (label? trg)
        (v)
        (values  `(jump-if ,(negate-relop relop) ,new-label)
                  `(jump trg)
                  `(with-label ,new-label (set! rax rax))))]
      [`(compare ,loc ,opand)
      #:when(and (loc? loc)
                  (opand? opand))
        (cond
        [(and (fvar? loc)
              (or (register? opand)
                  (int32? opand)))
        (if (or (equal? '(r11) current-patch-instructions-registers) 
                (equal? '(r10 r11) (current-patch-instructions-registers)))
        (current-patch-instructions-registers 'r10)
        (current-patch-instructions-registers 'r11))
        (let ([curr-reg (if (equal? current-patch-instructions-registers 'r11) 'r10 'r11)])
          (values `(set! ,curr-reg ,loc)
                  `(compare ,curr-reg ,opand)))]
        [(and (register? loc)
              (fvar? opand))
          (if (or (equal? '(r11) current-patch-instructions-registers) 
                (equal? '(r10 r11) (current-patch-instructions-registers)))
        (current-patch-instructions-registers 'r10)
        (current-patch-instructions-registers 'r11))
        (let ([curr-reg (if (equal? current-patch-instructions-registers 'r11) 'r10 'r11)])
          (values `(set! ,curr-reg ,opand)
                `(compare ,loc ,curr-reg)))])]))

  ;; (Para-asm-lang-v4 value) -> (listof (Paren-x64-fvars-v4 value))
  ;; assigns auxiliary registers from current-patch-instructions-registers to generate three instruction sequences
  (define (patch-instruction-register-three v)
    (match v
      [`(set! ,loc_1 (,binop ,loc_1 ,triv))
       (if 
       (or (equal? '(r11) current-patch-instructions-registers) 
            (equal? '(r10 r11) (current-patch-instructions-registers)))
        (current-patch-instructions-registers 'r10)
        (current-patch-instructions-registers 'r11))
        (let ([loc_1_reg (if (equal? current-patch-instructions-registers 'r11) 'r10 'r11)])
              (values 
                `(set! ,loc_1_reg ,loc_1)
                `(set! ,loc_1_reg (,binop ,loc_1_reg ,triv))
                `(set! ,loc_1 ,loc_1_reg)))]
      [`(compare ,loc ,opand)
      #:when (and (fvar? loc)
                (fvar? opand))
        (current-patch-instructions-registers 'r11)
        (let ([cp_reg (current-patch-instructions-registers)]
              [cp_reg_1 (if (equal? current-patch-instructions-registers 'r10) 'r11 'r10)])
              (values `(set! ,cp_reg ,opand)
                      `(set! ,cp_reg_1 ,loc)
                      `(compare ,cp_reg_1 ,cp_reg)))]))

  ;; relop -> relop
  ;; negates relop symbol
  (define (negate-relop relop)
    (match relop
     ['< '>] 
     ['<= '>=]
     ['= '!=]
     ['>= '<=]
     ['> '<]
     ['!= '=])) 

  ;; binop -> boolean
  ;; returns true if binop is a + or *
   (define (binop? b)
      (or (eq? b '+) (eq? b '*)))

  ;; triv -> boolean
  ;; returns true if triv t is a triv?
  (define (triv? triv)
    (or (opand? triv) (label? triv)))

  ;; loc? -> boolean
  ;; returns true if loc? is an register? or fvar?
    (define (loc? loc)
      (or (register? loc) (fvar? loc))) 

  ;; trg -> boolean
  ;; returns true if trg trg is a trg?
  (define (trg? trg)
    (or (register? trg) (label? trg)))
  
  ;; opand -> boolean
  ;; returns true if opand t is a opand?
  (define (opand? opand)
    (or (int64? opand) (loc? opand)))
  
  ;; relop -> boolean
  ;; returns true if relop t is a relop?
  (define (relop? relop)
     (match relop
     ['< #t]
     ['<= #t]
     ['= #t]
     ['>= #t]
     ['> #t]
     ['!= #t]
     [_ #f]))
  
  (patch-instructions-p p))
#|
(module+ test
  (require rackunit)
(define pi6
'(begin (set! fv0 21474) (halt 12)))
(check-equal?
(interp-para-asm-lang-v4 pi6)
(interp-paren-x64-fvars-v4 (patch-instructions pi6)))
(define pi1 
'(begin (set! fv0 1) 
        (set! fv0 (+ fv0 2)) 
        (halt fv0)))
(check-equal?
(interp-para-asm-lang-v4 pi1)
(interp-paren-x64-fvars-v4 (patch-instructions pi1)))

(define pi2
'(begin 
(set! fv0 23)
(with-label L.start.1 (set! fv1 3))
(compare fv0 65)
(jump-if < L.start.1)
(halt 10)))
(check-equal? 
(patch-instructions pi2)
'(begin
  (set! fv0 23)
  (with-label L.start.1 (set! fv1 3))
  (set! r11 fv0)
  (compare r11 65)
  (jump-if < L.start.1)
  (set! rax 10)
  (jump done)))

(define pi3
'(begin 
(set! fv0 3)
(set! fv0 (+ fv0 2))
(with-label L.start.1 (halt fv0))
(jump L.start.1)))
(check-equal?
(interp-para-asm-lang-v4 pi3)
(interp-paren-x64-fvars-v4 (patch-instructions pi3)))

(define pi4
'(begin (set! fv1 7) 
        (set! fv2 0) 
        (set! r12 fv1) 
        (set! fv2 (+ fv2 4)) 
        (halt fv2)))
(check-equal?
(interp-para-asm-lang-v4 pi4)
(interp-paren-x64-fvars-v4 (patch-instructions pi4)))

(define pi5
'(begin (set! fv0 5)
        (set! fv1 10)
        (with-label L.main.1 (set! r9 29))
        (compare fv0 fv1)
        (jump-if = L.main.1)
        (halt 10)))

(check-equal? 
(interp-para-asm-lang-v4 pi5)
(interp-paren-x64-fvars-v4 (patch-instructions pi5)))
(check-equal? (interp-para-asm-lang-v2 '(begin (set! fv0 1) (set! fv0 (+ fv0 2)) (halt fv0)))
              (interp-paren-x64-fvars-v2(patch-instructions '(begin (set! fv0 1) (set! fv0 (+ fv0 2)) (halt fv0)))))

(check-equal? (interp-para-asm-lang-v2 '(begin (set! fv1 7) (set! fv2 0) (set! r8 5) (set! r12 fv1) (set! r12 (+ r12 r8)) (set! fv2 (+ fv2 4)) (halt fv2)))
              (interp-paren-x64-fvars-v2(patch-instructions '(begin (set! fv1 7) (set! fv2 0) (set! r8 5) (set! r12 fv1) (set! r12 (+ r12 r8)) (set! fv2 (+ fv2 4)) (halt fv2)))))

(check-equal? (interp-para-asm-lang-v2 '(begin (set! fv0 0) (set! fv0 (+ fv0 1)) (halt 1)))
              (interp-paren-x64-fvars-v2(patch-instructions '(begin (set! fv0 0) (set! fv0 (+ fv0 1)) (halt 1)))))

(check-equal? (interp-para-asm-lang-v2 '(begin (set! fv1 1) (set! fv2 fv1) (set! fv2 (+ fv2 1)) (set! fv0 fv2) (set! fv0 (+ fv0 1)) (halt fv0)))
              (interp-paren-x64-fvars-v2(patch-instructions '(begin (set! fv1 1) (set! fv2 fv1) (set! fv2 (+ fv2 1)) (set! fv0 fv2) (set! fv0 (+ fv0 1)) (halt fv0)))))

(check-equal? (interp-para-asm-lang-v2 '(begin (set! fv1 1) (set! fv2 1) (set! fv0 fv1) (set! fv0 (+ fv0 fv2)) (halt fv0)))
              (interp-paren-x64-fvars-v2 (patch-instructions '(begin (set! fv1 1) (set! fv2 1) (set! fv0 fv1) (set! fv0 (+ fv0 fv2)) (halt fv0)))))

(check-equal? (interp-para-asm-lang-v2 '(begin (set! fv1 7) (set! fv2 0) (set! r8 5) (set! r12 fv1) (set! r12 (+ r12 r8)) (set! fv2 (+ fv2 4)) (halt fv2)))
              (interp-paren-x64-fvars-v2 (patch-instructions '(begin (set! fv1 7) (set! fv2 0) (set! r8 5) (set! r12 fv1) (set! r12 (+ r12 r8)) (set! fv2 (+ fv2 4)) (halt fv2)))))

(check-equal? (interp-para-asm-lang-v2 '(begin (set! fv0 1) (set! fv1 fv0) (set! fv1 (+ fv1 fv0)) (halt fv1)))
              (interp-paren-x64-fvars-v2 (patch-instructions '(begin (set! fv0 1) (set! fv1 fv0) (set! fv1 (+ fv1 fv0)) (halt fv1)))))

(check-equal? (interp-para-asm-lang-v2 '(begin (set! fv2 1) (set! fv1 2) (set! fv0 fv2) (set! fv0 (+ fv0 fv1)) (halt fv0)))
              (interp-paren-x64-fvars-v2 (patch-instructions '(begin (set! fv2 1) (set! fv1 2) (set! fv0 fv2) (set! fv0 (+ fv0 fv1)) (halt fv0)))))
              
(check-equal? (interp-para-asm-lang-v2 '(begin (set! rbx 0) (set! rcx 0) (set! r9 42) (set! rbx rcx) (set! rbx (+ rbx r9)) (halt rbx)))
              (interp-paren-x64-fvars-v2 (patch-instructions '(begin (set! rbx 0) (set! rcx 0) (set! r9 42) (set! rbx rcx) (set! rbx (+ rbx r9)) (halt rbx)))))

(check-equal? (interp-para-asm-lang-v2 '(begin (set! fv0 0) (set! fv1 42) (set! fv0 (+ fv0 fv1)) (halt fv0)))
              (interp-paren-x64-fvars-v2 (patch-instructions '(begin (set! fv0 0) (set! fv1 42) (set! fv0 (+ fv0 fv1)) (halt fv0)))))

(check-equal? (interp-para-asm-lang-v2 '(begin (set! fv0 0) (set! fv1 42) (set! fv2 0) (set! fv3 42) (set! fv0 fv1) (set! fv2 fv3) (halt fv0)))
              (interp-paren-x64-fvars-v2 (patch-instructions '(begin (set! fv0 0) (set! fv1 42) (set! fv2 0) (set! fv3 42) (set! fv0 fv1) (set! fv2 fv3) (halt fv0))))))
|#
#|
  Imp-mf-lan-v3: 
  p	 	::=	 	(module tail)	 	 	 	 
  tail	 	::=	 	value
 	 	|	 	(begin effect ... tail) 	 	 
  value	 	::=	 	triv
 	 	|	 	(binop triv triv)
 	 	|	 	(begin effect ... value)	 	 
  effect	 	::=	 	(set! aloc value)
 	 	|	 	(begin effect ... effect) 	 	 
  triv	 	::=	 	int64
 	 	|	 	aloc
  binop ::= * | +
|#

;; imp-mf-lang-v4? -> imp-cmf-lang-v4?
;; Compiles Imp-mf-lang v4 to Imp-cmf-lang v4, pushing set! under begin and if 
;; so that the right-hand-side of each set! is a simple value-producing operation.
(define (normalize-bind p)

  ;; (imp-mf-lang-v4 p) -> (imp-cmf-lang-v4 p) 
  ;; calls normalize-bind-t on tail statement of (Imp-mf-lan-v3 p) to return (imp-cmf-lang-v3 p) 
  (define (normalize-bind-p p)
    (match p
      [`(module ,t) 
      #:when (tail? t) 
      `(module ,(normalize-bind-t t))]))  

  ;; (imp-mf-lang-v4 pred) -> (imp-cmf-lang-v4 pred)
  (define (normalize-bind-pred pred)
    ;;; (match pred 
      ;;; [`(if ,pred_p ,pred_t ,pred_f)
      ;;;   `(if ,pred_p ,pred_t ,pred_f)]
      ;;; [(,relop ,triv_1 ,triv_2) #:when (and (relop? relop) (triv? triv_1) (triv? triv_2))
      ;;;   pred]
      ;;; [(let ([,alocs ,values] ...) ,pred)
      ;;;   ...]
      ;;; [else pred]
    pred)

  ;; (imp-mf-lang-v4 tail) -> (imp-cmf-lang-v4 tail) 
  ;; calls normalize-bind-e on each effect statement and normalize-bind-t on nested tail statement of (Imp-mf-lan-v3 tail) to return (imp-cmf-lang-v3 tail) 
  (define (normalize-bind-t t)
    (match t 
      [value 
      #:when (value? value) 
      (normalize-bind-v value)]
      [`(begin ,xs ... ,t) 
      #:when (and (andmap effect? xs) 
                  (tail? t))
      `(begin ,@(map normalize-bind-e xs) ,(normalize-bind-t t))]
      [`(if ,pred ,tail_t ,tail_f)
        `(if ,(normalize-bind-pred pred) ,(normalize-bind-t tail_t) ,(normalize-bind-t tail_f))]))

  ;; (imp-mf-lang-v4 value) -> (imp-cmf-lang-v4 value) 
  ;; calls normalize-bind-e on each effect statement and recursively calls normalize-bind-v on nested value statement of (Imp-mf-lan-v3 value) to return (imp-cmf-lang-v3 value) 
  (define (normalize-bind-v v) 
    (match v 
      [triv 
      #:when (triv? triv) 
      triv]
      [`(,binop ,triv_1 ,triv) 
      #:when (and (binop? binop) 
                  (triv? triv_1) 
                  (triv? triv)) 
      v]
      [`(begin ,xs ... ,v) 
      #:when (and (andmap effect? xs) 
                  (value? v)) 
      `(begin ,@(map normalize-bind-e xs) ,(normalize-bind-v v))]
      [`(if ,pred ,value_t ,value_f)
        `(if ,(normalize-bind-pred pred) ,(normalize-bind-v value_t) ,(normalize-bind-v value_f))]))

  ;; (imp-mf-lang-v4 effect) -> (imp-cmf-lang-v4 effect) 
  ;; calls normalize-bind-e on each effect statement and recursively calls normalize-bind-e on nested effect statement of (imp-mf-lang-v4 effect) to return (imp-cmf-lang-v4 effect) 
  (define (normalize-bind-e effect) 
    (match effect 
      [`(set! ,aloc ,s) 
      #:when (and (aloc? aloc) 
                  (value? s)) 
      (normalize-bind-s s aloc)]
      [`(begin ,xs ... ,e) 
      #:when (and (andmap effect? xs) 
                  (effect? e)) 
      `(begin ,@(map normalize-bind-e xs) ,(normalize-bind-e e))]
      [`(if ,pred ,effect_t ,effect_f)
        `(if ,(normalize-bind-pred pred) ,(normalize-bind-e effect_t) ,(normalize-bind-e effect_f))]))

  ;; (imp-mf-lang-v4 value) aloc  -> (imp-cmf-lang-v4 value) 
  ;; calls normalize-bind-e on each nested effect statement and abstract set! statement out to return (imp-cmf-lang-v4 value) 
  ;; s ::= value from (set! aloc value)
  (define (normalize-bind-s s aloc)
    (match s 
      [triv 
      #:when (triv? triv) 
      `(set! ,aloc ,s)]
      [`(,binop ,triv_1 ,triv) 
      #:when (and (binop? binop) 
                  (triv? triv_1)
                  (triv? triv)) 
      `(set! ,aloc ,s)]
      [`(begin ,xs ... ,v) 
      #:when (and (andmap effect? xs) 
                  (value? v)) 
      `(begin ,@(map normalize-bind-e xs) (set! ,aloc ,(begin-s s)))]
      [`(if ,pred ,value_t ,value_f)
      `(if ,(normalize-bind-pred pred) (set! ,aloc ,value_t) (set! ,aloc ,value_f))]))

  ;; (imp-mf-lang-v4 value) -> (imp-cmf-lang-v4 value) 
  (define (begin-s s)
    (match s
      [`(begin ,xs ... ,v) 
      #:when (and (andmap effect? xs) 
                  (value? v)) 
      v]))
  
  ;;; (define (normalize-bind-r r p1 p2)
  ;;;   ...)

  (define (relop? r)
    (or (eq? r '<) (eq? r '<=) (eq? r '=) (eq? r '>) (eq? r '>=) (eq? r '!=)))

  ;; (imp-mf-lang-v4 tail) -> boolean
  ;; returns true if t matches pattern of (imp-mf-lang-v4 tail)
  (define (tail? t)
    (match t       
      [value 
      #:when (value? value) 
      #t]
      [`(begin ,xs ... ,t) 
      #:when (and (andmap effect? xs) 
                  (tail? t)) 
      #t]
      [`(if ,pred ,tail_t ,tail_f) 
      #:when (and (tail? tail_t) (tail? tail_f))
      #t]
      [_ #f]
      ))
  
  ;; (imp-mf-lang-v4 value) -> boolean
  ;; returns true if t matches pattern of (imp-mf-lang-v4 value)
  (define (value? v) 
    (match v
      [triv #:when (triv? triv) #t]
      [`(,binop ,triv_1 ,triv) 
      #:when (and (binop? binop) 
                  (triv? triv_1) 
                  (triv? triv)) 
      #t]
      [`(begin ,xs ... ,v) 
      #:when (and (andmap effect? xs) 
                  (value? v)) 
      #t] 
      [`(if ,pred ,value_t ,value_f)
      #:when (and (value? value_t) (value? value_f))
      #t]
      [_ #f]))

  ;; (imp-mf-lang-v4 effect) -> boolean
  ;; returns true if t matches pattern of (imp-mf-lang-v4 effect)
  (define (effect? e) 
    (match e
      [`(begin ,xs ... ,e) 
      #:when (and (andmap effect? xs) 
                  (effect? e))
      #t]
      [`(set! ,aloc ,value) 
      #:when (and (aloc? aloc) 
                  (value? value)) 
      #t]
      [`(if ,pred ,effect_t ,effect_f) #:when (and (effect? effect_t) (effect? effect_f))
      #t]
      [_ #f]))
  
  ;; triv -> boolean
  ;; returns true if t is an int64 or aloc
  (define (triv? t)
    (or (int64? t) 
        (aloc? t)))

  ;; binop -> boolean
  ;; returns true if binop is a + or *
  (define (binop? b)
    (or (eq? '* b) 
        (eq? '+ b)))
    
  (normalize-bind-p p))
#|
(module+ test
(require rackunit)
(check-equal? (interp-imp-mf-lang-v4 (normalize-bind  '(module (begin (set! x.1 (if (true) 3 4)) 2))))
              (interp-imp-cmf-lang-v4 (normalize-bind '(module (begin (if (true) (set! x.1 3) (set! x.1 4)) 2)))))

(check-equal? (interp-imp-mf-lang-v4 '(module (begin (set! tmp.1 1) (begin (set! tmp.2 2) (+ tmp.2 tmp.1)))))
              (interp-imp-cmf-lang-v4 (normalize-bind '(module (begin (set! tmp.1 1) (begin (set! tmp.2 2) (+ tmp.2 tmp.1)))))))

(check-equal? (interp-imp-mf-lang-v4 '(module (begin (set! x.1 (+ 5 6)) (set! y.1 (+ 1 x.1)) y.1)))
              (interp-imp-cmf-lang-v4 (normalize-bind '(module (begin (set! x.1 (+ 5 6)) (set! y.1 (+ 1 x.1)) y.1)))))

(check-equal? (interp-imp-mf-lang-v4  '(module (begin (set! x.3 (begin (set! y.4 (begin (set! z.4 (+ 4 5)) z.4)) y.4)) x.3)))
              (interp-imp-cmf-lang-v4 (normalize-bind  '(module (begin (set! x.3 (begin (set! y.4 (begin (set! z.4 (+ 4 5)) z.4)) y.4)) x.3)))))

(check-equal? (interp-imp-mf-lang-v4  '(module (begin (set! tmp.1 (begin 1)) 3)))
              (interp-imp-cmf-lang-v4 (normalize-bind  '(module (begin (set! tmp.1 (begin 1)) 3)))))

(check-equal? (interp-imp-mf-lang-v4  '(module (begin (set! x.1 (+ 2 2)) x.1)))
              (interp-imp-cmf-lang-v4 (normalize-bind  '(module (begin (set! x.1 (+ 2 2)) x.1))))))
|#

;;asm-lang-v2/conflicts
; p	 	::=	 	(module info tail)	 	 	 
;   info	 	::=	 	(#:from-contract (info/c (locals (aloc ...)) (conflicts ((aloc (aloc ...)) ...)))) 	 	 	 
;   tail	 	::=	 	(halt triv)
;  	 	|	 	(begin effect ... tail) 	 	 	 
;   effect	 	::=	 	(set! aloc triv)
;  	 	|	 	(set! aloc_1 (binop aloc_1 triv))
;  	 	|	 	(begin effect ... effect) 	 	 
;   triv	 	::=	 	int64
;  	 	|	 	aloc 	 
;   binop	 	::=	 	*
;  	 	|	 	+ 	 	 	 
;   aloc	 	::=	 	aloc? 	 	 
;   int64	 	::=	 	int64?


;;(assign-registers p) → asm-lang-v2/assignments?
;;p : asm-lang-v2/conflicts

(define (assign-registers p)
  
  ;; removes our selected loc from conflicts
  ;; loc conflicts -> conflicts
  (define (update-conflict loc conflicts)
    (map (lambda (x) 
    `(,(first x) ,(remove loc (second x)))) conflicts))
  
  ;; loc conflicts -> aloc 
  ;; pick the lowest degree abstraction with fewer than k conflicts
  ;; low version for now can improve on later if time
  (define (choose-aloc locs conflicts)
    (define k (length (current-assignable-registers)))

    ;; used as our filter / sorting function takes loc from locs -> number
    (define (degree loc)
      (length (second (assoc loc conflicts))))

    (cond 
      [(empty? locs) #f] 
      [else 
      (let ([aloc (argmin degree locs)]);; finds lowest conflict loc in locs 
        (if (< (degree aloc) k)
        aloc ;; we have less conflict than available registers return aloc
        #f))]))

  (define (pick-reg lowest-loc conflicts new-assignment)
    (define valid-regs (current-assignable-registers))
    (let ([conflict-of-loc (second (assoc lowest-loc conflicts))]
         )
    (begin 
      (for-each (lambda (x)
              (cond 
                [(dict-ref new-assignment x)
                    (set! valid-regs (remove (dict-ref new-assignment x) valid-regs))])) 
              conflict-of-loc)
              (last (set->list valid-regs)))))

  (define (assign-registers-s locs conflicts assignment i)
  (cond
    [(empty? locs) (set->list assignment)] ;; base case returns assignment
    [else ;; found aloc
      (let* ([lowest-loc (choose-aloc locs conflicts)] ;; this makes the order of the selection
            [rest_locs (remove lowest-loc locs)] ;; removes the lowest loc from locs
            ) 
      (cond
        [(not lowest-loc) ;; case #f we cannot find an aloc that is the lowest
          (begin ;; arbituarily assign an fvar
          (assign-registers-s (rest locs) 
                            (update-conflict (first locs) conflicts)
                            (cons (cons (first locs) (make-fvar i)) assignment)
                            (add1 i)))] 
        [else  ;; we found something something ie v.1
          (begin
          (let* (
                [updated_conflicts (update-conflict lowest-loc conflicts)]
                [new-assignment (assign-registers-s rest_locs updated_conflicts assignment i)]
                [avail-reg (pick-reg lowest-loc conflicts new-assignment)])
              (if avail-reg
              (assign-registers-s rest_locs
                              updated_conflicts
                              (cons (cons lowest-loc avail-reg) assignment)
                              i)
              (assign-registers-s rest_locs 
                              (update-conflict (first locs) conflicts)
                              (cons `(,(first locs) ,(make-fvar i)) assignment)
                              (add1 i)))))]))]))
  ;; starts function
  (match p
  [`(module ,info ,tail) #:when(info? info)
  (begin
    `(module (,(list-ref info 0) 
    ,(list-ref info 1) 
    (assignment 
    ,(map (lambda (pair) (list (car pair) (cdr pair)))
    (assign-registers-s (list-ref (list-ref info 0) 1) (list-ref (list-ref info 1) 1) `() 0))))
     ,tail) )]))

;; block-asm-lang-v4? -> para-asm-lang-v4?
;; Compile Block-asm-lang v4 to Para-asm-lang v4 by flattening basic blocks into labeled instructions.
(define (flatten-program p)
  (define env '())

  (define (flatten-p p env)
    (match p 
      [`(module ,bs ...)
        `(begin ,@(map (curryr flatten-b env) bs))]))

  (define (flatten-b b env)
    (match b
      [`(define ,label ,tail)
        (flatten-tail tail label env)]
      [else (begin (display b) (display "\n"))]))

  (define (flatten-tail tail label env)
    (append env `(with-label ,label ,tail)))

  (define (flatten-effect effect env) 
    (append env effect))

  (flatten-p p env))
#|
  (module+ test
  (require rackunit)
  
  (check-equal? (flatten-program `(module (define L.start.1 (halt 2))))
                `(begin (with-label L.start.1 (halt 2))))

  (check-equal? (flatten-program `(module (define L.start.1 (jump L.start.1)) (define L.start.2 (halt 2))))
                `(begin (with-label L.start.1 (jump L.start.1)) (with-label L.start.2 (halt 2))))
                
  (check-equal? (flatten-program `(module (define L.start.1 (begin (set! rsp 2) (set! rbp 5) (set! rsp (+ rsp rbp)) (halt rsp)))))
               `(begin (with-label L.start.1 (set! rsp 2)) (set! rbp 5) (set! rsp (+ rsp rbp)) (halt rsp))))
|#
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; nested-asm-lang-v4? -> block-pred-lang-v4? 
;; Compile the Nested-asm-lang v4 to Block-pred-lang v4, eliminating all nested 
;; expressions by generating fresh basic blocks and jumps.
(define (expose-basic-blocks p)
  (define env '()) ;; TODO: add this as accumulator 

  ;; nested-asm-lang-v4? -> block-pred-lang-v4? 
  (define (expose-p p)
    (match p 
      [`(module ,tail)
        `(module ,@(expose-tail tail))]))
    
  ;; pred -> (listof) block-pred-lang-v4?
  (define (expose-pred p)
    (match p
      [`(,relop ,loc ,triv)
        (list p)]
      [`(begin ,effects ... ,pred)
        (append (append (map expose-effect effects))
        (expose-pred pred))]
      [`(if ,pred ,pred_t ,pred_f)
        (define label_t (fresh-label))
        (define label_f (fresh-label))
        `((if ,pred (jump ,label_t) (jump ,label_f))
         (define ,label_t ,pred_t)
         (define ,label_f ,pred_f))]  
      [`(not ,pred) 
        (list p)]
      [(? false?)
        (list p)]
      [true
        (list p)]))

  ;; tail -> (listof) block-pred-lang-v4?
  (define (expose-tail tail)
    (match tail 
      [`(halt ,triv)
        `((define ,(fresh-label) ,tail))]
      [`(begin ,effects ... ,tail)
        `((define ,(fresh-label) (begin ,@(map expose-effect effects) ,tail)))]
      [`(if ,pred ,tail_t ,tail_f)
        (define label_t (fresh-label))
        (define label_f (fresh-label))
        `((define ,(fresh-label) (if ,pred (jump ,label_t) (jump ,label_f)))
          (define ,label_t ,@(expose-tail tail_t))
          (define ,label_f ,@(expose-tail tail_f)))])) 

  ;; effect -> (listof) block-pred-lang-v4?
  (define (expose-effect effect)
    (match effect 
      [`(set! ,loc ,triv)
        effect]
      [`(set! ,loc (,binop ,loc ,triv))
        effect]
      [`(begin ,effects ...)
        `(define ,(fresh-label) ,@(map expose-effect effects))]
      [`(if ,pred ,effect_t ,effect_f)
        (define label_t (fresh-label))
        (define label_f (fresh-label))
        `((if ,pred (jump ,label_t) (jump ,label_f))
          (define ,label_t ,@(expose-effect effect_t))
          (define ,label_f ,@(expose-effect effect_f)))])) 
  
  (define (triv? t)
    (or (int64? t) (loc? t)))

  (define (loc? l)
    (or (register? l) (fvar? l)))
  
  (expose-p p))
#|
(module+ test
(require rackunit)
(check-equal? (interp-nested-asm-lang-v4 (expose-basic-blocks `(module (halt 1))))
  (interp-nested-asm-lang-v4 `(module (define ,(fresh-label) (halt 1)))))

(check-equal? (interp-nested-asm-lang-v4 (expose-basic-blocks '(module (begin (set! rdi 2) (halt rdi)))))
  (interp-nested-asm-lang-v4 `(module (define ,(fresh-label) (begin (set! rdi 2) (halt rdi))))))

#;(check-equal? (interp-nested-asm-lang-v4 (expose-basic-blocks '(module (if (true) (halt 1) (halt 2)))))
  (interp-nested-asm-lang-v4 `(module
    (define ,(fresh-label) (if (true) (jump ,(fresh-label)) (jump ,(fresh-label))))
    (define ,(fresh-label) (halt 1))
    (define ,(fresh-label) (halt 2))))))
|#

;; Optional; if you choose not to complete, implement a stub that returns the input
(define (check-paren-x64-init p)
  p)

;; Optional; if you choose not to complete, implement a stub that returns the input
(define (check-paren-x64-syntax p)
  p)

(define (check-paren-x64 p)
  (check-paren-x64-init (check-paren-x64-syntax p)))

(module+ test
  (require
   rackunit
   rackunit/text-ui
   cpsc411/langs/v6
   cpsc411/test-suite/public/v6)

  (define pass-map
    (list
     (cons uniquify interp-values-lang-v6)
     (cons sequentialize-let interp-values-unique-lang-v6)
     (cons normalize-bind interp-imp-mf-lang-v6)
     (cons impose-calling-conventions interp-proc-imp-cmf-lang-v6)
     (cons select-instructions interp-imp-cmf-lang-v6)
     (cons uncover-locals interp-asm-pred-lang-v6)
     (cons undead-analysis interp-asm-pred-lang-v6/locals)
     (cons conflict-analysis interp-asm-pred-lang-v6/undead)
     (cons assign-call-undead-variables interp-asm-pred-lang-v6/conflicts)
     (cons allocate-frames interp-asm-pred-lang-v6/pre-framed)
     (cons assign-registers interp-asm-pred-lang-v6/framed)
     (cons assign-frame-variables interp-asm-pred-lang-v6/spilled)
     (cons replace-locations interp-asm-pred-lang-v6/assignments)
     (cons optimize-predicates interp-nested-asm-lang-fvars-v6)
     (cons implement-fvars interp-nested-asm-lang-fvars-v6)
     (cons expose-basic-blocks interp-nested-asm-lang-v6)
     (cons resolve-predicates interp-block-pred-lang-v6)
     (cons flatten-program interp-block-asm-lang-v6)
     (cons patch-instructions interp-para-asm-lang-v6)
     (cons generate-x64 interp-paren-x64-v6)
     (cons wrap-x64-boilerplate #f)
     (cons wrap-x64-run-time #f)))

  (current-pass-list
   (map car pass-map))

  (run-tests
   (v6-public-test-suite
    (current-pass-list)
    (map cdr pass-map))))
