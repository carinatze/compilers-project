#lang racket

(provide replace-locations)

(require
 cpsc411/compiler-lib
 cpsc411/2c-run-time
 cpsc411/langs/v6
 cpsc411/graph-lib
 racket/trace
 rackunit)

#| Asm-lang-v6/assignments:

p	 	::=	 	(module info (define label info tail) ... tail)
 	 	 	 	 
  info	 	::=	 	(#:from-contract (info/c (assignment ((aloc rloc) ...))))
 	 	 	 	 
  frame	 	::=	 	(aloc ...)
 	 	 	 	       
  pred	 	::=	 	(relop loc opand) 
 	 	|	 	(true) 
 	 	|	 	(false)
 	 	|	 	(not pred) 
 	 	|	 	(begin effect ... pred) 
 	 	|	 	(if pred pred pred) 
 	 	 	 	 
  tail	 	::=	 	(jump trg loc ...) 
 	 	|	 	(begin effect ... tail) 
 	 	|	 	(if pred tail tail) 
 	 	 	 	 
  effect	 	::=	 	(set! loc triv) 
 	 	|	 	(set! loc_1 (binop loc_1 opand)) 
 	 	|	 	(begin effect ... effect) 
 	 	|	 	(if pred effect effect) 
 	 	|	 	(return-point label tail) 
 	 	 	 	 
  opand	 	::=	 	int64
 	 	|	 	loc
 	 	 	 	 
  triv	 	::=	 	opand
 	 	|	 	label
 	 	 	 	 
  loc	 	::=	 	rloc
 	 	|	 	aloc
 	 	 	 	 
  trg	 	::=	 	label
 	 	|	 	loc
 	 	 	 	 
  binop	 	::=	 	*
 	 	|	 	+
 	 	|	 	-
 	 	 	 	 
  relop	 	::=	 	<
 	 	|	 	<=
 	 	|	 	=
 	 	|	 	>=
 	 	|	 	>
 	 	|	 	!=
|#

;; Exercise 14
;; (Asm-lang-v6/assignments) -> (nested-asm-lang-v6)
;; replaces all abstract location with assigned pysical location using assignment info field
(define (replace-locations p)

  ;; p -> p
  ;;
  ;; compiles p by replacing all abstract locations with assigned physical location using this
  ;; block's assignment info field
  (define (replace-locations-p p)
    (match p 
      [`(module ,info ,nested ... ,tail) 
      (define info-set
        (replace-locations-i (info-ref info 'assignment)))
      (define-values (new-tail _)
        (replace-locations-t tail info-set))
      `(module 
        ,@(map replace-locations-nested-p nested)
        ,new-tail)]))

  ;; nested-p -> nested-p
  ;;
  ;; nested-p ::= (define label info tail)
  ;; compiles nested-p by replacing all abstract locations with assigned physical location using this
  ;; block's assignment info field
  (define (replace-locations-nested-p p)
    (match p 
      [`(define ,label ,info ,tail) 
      (define info-set
        (replace-locations-i (info-ref info 'assignment)))
       (define-values (new-nested-p _)
        (replace-locations-t tail info-set))
      `(define 
        ,label 
        ,new-nested-p)])) 

   ;; pred [Mapof aloc loc] -> (values pred [Mapof aloc loc])
   ;;
   ;; takes in pred and mapping of aloc to phsyical locations and compiles nested-p by replacing all
   ;; abstract locations with assigned physical location and returns compiled pred and mappings
  (define (replace-locations-pred pred env) 
    (match pred
    [`(,relop ,loc ,opand)
    #:when(relop? relop) 
      (values
        `(,relop ,(find-assign loc env) ,(find-assign opand env))
        env)]
 	 	[`(true) 
    (values pred env)]
 	 	[`(false)
     (values pred env)]
 	 	[`(not ,pred)
    (define-values (new-pred _)
      (replace-locations-pred pred env))
    (values 
      `(not ,new-pred)
      env)]
 	 	[`(begin ,xs ... ,pred)
        (define new-effects
          (for/foldr ([xs-s '()])
                      ([s xs])
            (define-values (new-xs _)
              (replace-locations-s s env))
            (cons new-xs xs-s)))
        (define-values (new-pred _)
            (replace-locations-pred pred env))
        (values
          `(begin 
            ,@new-effects
            ,new-pred)
          env)]
 	 	[`(if ,pred ,pred_1 ,pred_2)
        (define-values (new-pred pred-env)
          (replace-locations-pred pred env))
        (define-values (new-pred1 pred1-env)
          (replace-locations-pred pred_1 env))
        (define-values (new-pred2 pred2-env)
          (replace-locations-pred pred_2 env))
        (values 
        `(if ,new-pred 
          ,new-pred1  
          ,new-pred2)
         env)]))

   ;; tail [Mapof aloc loc] -> (values tail [Mapof aloc loc])
   ;;
   ;; takes in tail and mapping of aloc to phsyical locations and compiles nested-p by replacing all
   ;; abstract locations with assigned physical location and returns compiled tail and mappings
  (define (replace-locations-t t env)
    (match t
      [`(begin ,xs ... ,tail) 
      (define new-effects
          (for/foldr ([xs-s '()])
                      ([s xs])
            (define-values (new-xs _)
              (replace-locations-s s env))
            (cons new-xs xs-s)))
        (define-values (new-tail _)
            (replace-locations-t tail env))
        (values
          `(begin 
            ,@new-effects
            ,new-tail)
          env)]
      [`(jump ,trg ,loc ...) 
      (values 
        `(jump ,(find-assign trg env)) 
        env)]
      [`(if ,pred ,tail ,tail1)
       (define-values (new-tail tail-env)
          (replace-locations-t tail env))
        (define-values (new-tail1 tail1-env)
          (replace-locations-t tail1 env))
        (define-values (new-pred pred-env)
          (replace-locations-pred pred env))
        (values 
        `(if ,new-pred 
          ,new-tail  
          ,new-tail1)
         env)]))

   ;; effect [Mapof aloc loc] -> (values effect [Mapof aloc loc])
   ;;
   ;; takes in effect and mapping of aloc to phsyical locations and compiles nested-p by replacing all
   ;; abstract locations with assigned physical location and returns compiled effect and mappings
  (define (replace-locations-s s env)
    (match s
      [`(set! ,loc_1 (,binop ,loc_1 ,opand))
        (values 
          `(set! ,(find-assign loc_1 env) (,binop ,(find-assign loc_1 env) ,(find-assign opand env)))
          env)]
      [`(set! ,loc ,triv) 
      #:when(triv? triv)
        (values 
          `(set! ,(find-assign loc env) ,(find-assign triv env))
          env)]
      [`(begin ,xs ... ,effect)
        (define new-effects
          (for/foldr ([xs-s '()])
                      ([s xs])
            (define-values (new-xs _)
              (replace-locations-s s env))
            (cons new-xs xs-s)))
        (define-values (new-effect _)
            (replace-locations-s effect env))
        (values
          `(begin 
            ,@new-effects
            ,new-effect)
          env)]
      [`(if ,pred ,effect ,effect1)
      (define-values (new-effect effect-env)
          (replace-locations-s effect env))
        (define-values (new-effect1 effect1-env)
          (replace-locations-s effect1 env))
        (define-values (new-pred pred-env)
          (replace-locations-pred pred env))
        (values 
        `(if ,new-pred 
          ,new-effect  
          ,new-effect1)
         env)]
      [`(return-point ,label ,tail)
       (define-values (new-tail _)
          (replace-locations-t tail env))
        (values 
          `(return-point ,label ,new-tail)
          env)]))

  ;; (listof info) -> (Mapof aloc loc)
  ;;
  ;; iterates through assignment info given and maps each abstract location to its 
  ;; corresponding assigned physical location and returns map of all abstract locations 
  ;; to its assigned physical locations
  (define (replace-locations-i i)
    (match i
      [`((,xs ,xp) ...) 
        (define env (make-hash))
        (for ([x xs]
              [p xp])
              (dict-set! env x p))
        env]))

  ;; aloc [Mapof aloc loc] -> aloc
  ;; 
  ;; takes in aloc and mappings of aloc to physical locations, and if aloc is aloc? then return its
  ;; corresponding physical location
  ;; else return itself
  (define (find-assign aloc env)
    (if (aloc? aloc)
      (dict-ref env aloc)
      aloc))

  ;; triv -> boolean
  ;; returns true if triv is opand or label
  (define (triv? triv)
    (or (opand? triv) (label? triv)))

  ;; opand -> boolean
  ;; returns true if opand is int64 or loc
  (define (opand? opand)
    (or (int64? opand) (loc? opand)))

  ;; loc -> boolean
  ;; returns true if loc is rloc or aloc
  (define (loc? loc)
    (or (rloc? loc) (aloc? loc)))

  ;; rloc -> boolean
  ;; returns true if rloc is register or fvar
  (define (rloc? rloc)
    (or (register? rloc) (fvar? rloc)))
  
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

  (replace-locations-p p))

(module+ test 
  (require
  rackunit
   rackunit/text-ui
   cpsc411/langs/v6
   cpsc411/test-suite/public/v6
   cpsc411/test-suite/utils)

; if pred pred pred
; if pred effect effect
; begin effect ... pred
; begin effect ... effect
; set loc triv
; true
; not pred
; relop loc opand
; begin effect ... tail
(define rl-v6-1
'(module
  ((locals ())
   (conflicts
    ((tmp-ra.1 (rax x.5 x.6 x.4 rbp))
     (tmp-ra.2 (rbp tmp-ra.1))
     (x.6 (x.5 rbp tmp-ra.1))
     (x.5 (rbp tmp-ra.1 x.6))
     (rbp (rax x.5 x.6 tmp-ra.2 tmp-ra.1))
     (rax (rbp tmp-ra.1))))
   (assignment ((tmp-ra.1 r15) (x.6 r14) (x.5 r13) (tmp-ra.2 r14))))
  (begin
    (set! tmp-ra.1 r15)
    (if (if (begin (set! x.6 2) (set! x.5 1) (< x.5 x.6))
          (not (true))
          (< x.6 10))
      (begin (set! tmp-ra.2 x.5) (set! tmp-ra.2 (+ tmp-ra.2 2)))
      (set! tmp-ra.2 x.6))
    (set! rax 2)
    (jump tmp-ra.1 rbp rax))))

(define rl-v6-1-compiled
 '(module
  (begin
    (set! r15 r15)
    (if (if (begin (set! r14 2) (set! r13 1) (< r13 r14))
          (not (true))
          (< r14 10))
      (begin (set! r14 r13) (set! r14 (+ r14 2)))
      (set! r14 r14))
    (set! rax 2)
    (jump r15))))
    
(check-equal? (replace-locations rl-v6-1) rl-v6-1-compiled)
(check-equal? 
  (interp-nested-asm-lang-fvars-v6 (replace-locations rl-v6-1)) 
  (interp-nested-asm-lang-fvars-v6 rl-v6-1-compiled))

; if pred tail tail
; begin effect tail
; set loc triv
; set loc (binop loc opand)
; jump trg loc
; relop loc opand
(define rl-v6-2-compiled
'(module
  (begin
    (set! r15 r15)
    (if (begin (set! r14 0) (> r14 1))
      (begin (set! rax 0) (jump r15))
      (begin (set! rax 0) (set! rax (+ rax 1)) (jump r15))))))
(define rl-v6-2
'(module
  ((locals ())
   (conflicts
    ((tmp.79 (rbp tmp-ra.74))
     (tmp-ra.74 (rbp tmp.79 rax))
     (rax (rbp tmp-ra.74))
     (rbp (tmp-ra.74 tmp.79 rax))))
   (assignment ((tmp-ra.74 r15) (tmp.79 r14))))
  (begin
    (set! tmp-ra.74 r15)
    (if (begin (set! tmp.79 0) (> tmp.79 1))
      (begin (set! rax 0) (jump tmp-ra.74 rbp rax))
      (begin (set! rax 0) (set! rax (+ rax 1)) (jump tmp-ra.74 rbp rax))))))

(check-equal? (replace-locations rl-v6-2) rl-v6-2-compiled)
(check-equal? 
  (interp-nested-asm-lang-fvars-v6 (replace-locations rl-v6-2)) 
  (interp-nested-asm-lang-fvars-v6 rl-v6-2-compiled))

(define rl-5 
'(module
  ((locals ())
   (conflicts
    ((tmp-ra.4 (fv0 fv1 rbp))
     (rbp (r15 fv0 fv1 tmp-ra.4))
     (fv1 (r15 fv0 rbp tmp-ra.4))
     (fv0 (r15 rbp fv1 tmp-ra.4))
     (r15 (rbp fv0 fv1))))
   (assignment ((tmp-ra.4 r15))))
  (define L.swap.1
    ((locals ())
     (conflicts
      ((y.2 (rbp tmp-ra.1 x.1 nfv.3))
       (x.1 (y.2 rbp tmp-ra.1 fv1))
       (tmp-ra.1 (y.2 x.1 rbp fv1 fv0 rax z.3))
       (z.3 (rbp tmp-ra.1))
       (nfv.3 (r15 nfv.2 rbp y.2))
       (nfv.2 (r15 rbp nfv.3))
       (rbp (y.2 x.1 tmp-ra.1 rax z.3 r15 nfv.2 nfv.3))
       (r15 (rbp nfv.2 nfv.3))
       (rax (rbp tmp-ra.1))
       (fv0 (tmp-ra.1))
       (fv1 (x.1 tmp-ra.1))))
     (assignment
      ((tmp-ra.1 fv2) (nfv.2 fv3) (nfv.3 fv4) (y.2 r15) (x.1 r14) (z.3 r15))))
    (begin
      (set! tmp-ra.1 r15)
      (set! x.1 fv0)
      (set! y.2 fv1)
      (if (< y.2 x.1)
        (begin (set! rax x.1) (jump tmp-ra.1 rbp rax))
        (begin
          (begin
            (set! rbp (- rbp 24))
            (return-point
             L.rp.1
             (begin
               (set! nfv.3 x.1)
               (set! nfv.2 y.2)
               (set! r15 L.rp.1)
               (jump L.swap.1 rbp r15 nfv.2 nfv.3)))
            (set! rbp (+ rbp 24)))
          (set! z.3 rax)
          (set! rax z.3)
          (jump tmp-ra.1 rbp rax)))))
  (begin
    (set! tmp-ra.4 r15)
    (set! fv1 2)
    (set! fv0 1)
    (set! r15 tmp-ra.4)
    (jump L.swap.1 rbp r15 fv0 fv1))))

(define rl-5-compiled 
'(module
  (define L.swap.1
    (begin
      (set! fv2 r15)
      (set! r14 fv0)
      (set! r15 fv1)
      (if (< r15 r14)
        (begin (set! rax r14) (jump fv2))
        (begin
          (begin
            (set! rbp (- rbp 24))
            (return-point
             L.rp.1
             (begin
               (set! fv4 r14)
               (set! fv3 r15)
               (set! r15 L.rp.1)
               (jump L.swap.1)))
            (set! rbp (+ rbp 24)))
          (set! r15 rax)
          (set! rax r15)
          (jump fv2)))))
  (begin
    (set! r15 r15)
    (set! fv1 2)
    (set! fv0 1)
    (set! r15 r15)
    (jump L.swap.1))))
(check-equal? (replace-locations rl-5) rl-5-compiled)
(check-equal? 
  (interp-nested-asm-lang-fvars-v6 (replace-locations rl-5)) 
  (interp-nested-asm-lang-fvars-v6 rl-5-compiled))

(run-tests
   (test-suite
    ""
    (test-compiler-pass replace-locations interp-asm-pred-lang-v6/assignments interp-nested-asm-lang-fvars-v6 nested-asm-lang-fvars-v6?))))

