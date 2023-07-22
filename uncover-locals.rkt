#lang racket

(provide uncover-locals)

(require
 cpsc411/compiler-lib
 cpsc411/2c-run-time
 cpsc411/langs/v6
 cpsc411/graph-lib
 racket/trace
 rackunit)


#| Asm-pred-lang-v6:
   p	 	::=	 	(module info (define label info tail) ... tail)
 	 	 	 	 
  info	 	::=	 	(#:from-contract (info/c (new-frames (frame ...))))
 	 	 	 	 
  frame	 	::=	 	(aloc ...)
 	 	 	 	 
  pred	 	::=	 	(relop loc opand) ;
 	 	|	 	(true) ;
 	 	|	 	(false)
 	 	|	 	(not pred) ;
 	 	|	 	(begin effect ... pred) ;
 	 	|	 	(if pred pred pred) ;
 	 	 	 	 
  tail	 	::=	 	(jump trg loc ...) ;
 	 	|	 	(begin effect ... tail) ;
 	 	|	 	(if pred tail tail) ;
 	 	 	 	 
  effect	 	::=	 	(set! loc triv) ;
 	 	|	 	(set! loc_1 (binop loc_1 opand)) ;
 	 	|	 	(begin effect ... effect) ;
 	 	|	 	(if pred effect effect) ;
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

;; Exercise 7
;; (Asm-pred-lang-v6) -> (Asm-pred-lang-v6/locals)
;; Compiles Asm-pred-lang v6 to Asm-pred-lang v6/locals by 
;; decorating locals info field by analyzing abstract locations used in each block 
(define (uncover-locals p)

  ;; p [SetOf aloc] ->  p
  ;;
  ;; takes in p and empty set of alocs to compile p by decorating the locals info field with the 
  ;; list of abstract locations used for the tail in this block
  (define (uncover-locals-p p acc)
    (match p
      [`(module ,info ,nested ... ,tail) 
      `(module ((new-frames ,(info-ref info 'new-frames))
                (locals ,(set->list (uncover-locals-t tail acc)))) 
              ,@(map uncover-locals-nested-p nested)
              ,tail)]))

  ;; nested-p -> nested-p
  ;; 
  ;; compiles nested-p statement by decorating locals info field with the list of abstract locations 
  ;; returned from the tail statement in this block
  (define (uncover-locals-nested-p p)
    (match p
      [`(define ,label ,info ,tail) 
      `(define ,label
        ((new-frames ,(info-ref info 'new-frames))
        (locals ,(reverse (set->list (uncover-locals-t tail '()))))) 
        ,tail)]))
  
  ;; pred [SetOf aloc] -> [Setof aloc]
  ;; 
  ;; Takes in pred statement and set of abstract locations used in the program so far
  ;; and returns set of alocs with new abstract locations added
  (define (uncover-locals-pred pred acc)
    (match pred
    [`(,relop ,aloc ,triv) 
    #:when(and (aloc? aloc) (relop? relop))
    (add-aloc (add-aloc acc aloc) triv)]
 	 	[`(true) 
    acc]
 	 	[`(false)
    acc]
 	 	[`(not ,pred)
    (uncover-locals-pred pred acc)]
 	 	[`(begin ,effects ... ,pred)
    (define effect-locals
          (for/fold ([new-acc acc])
                    ([e effects]) 
          (uncover-locals-e e new-acc)))
    (uncover-locals-pred pred effect-locals)]
 	 	[`(if ,pred ,pred_1 ,pred_2)
    (uncover-locals-pred pred_2 (uncover-locals-pred pred_1 (uncover-locals-pred pred acc)))]))
  
  ;; effect [Setof aloc] -> [Setof aloc]
  ;; 
  ;; Takes in effect statement and set of abstract locations used in the program so far 
  ;; and returns set of alocs with new abstract locations added
  (define (uncover-locals-e e acc)
    (match e 
      [`(set! ,loc ,triv) 
      #:when(triv? triv)
      (add-aloc (add-aloc acc loc) triv)]
      [`(set! ,loc_1 (,binop ,loc_1 ,opand)) 
       (add-aloc (add-aloc acc loc_1) opand)]
      [`(begin ,effects ... ,effect) 
      (define effect-locals
          (for/fold ([new-acc acc])
                    ([e effects]) 
          (uncover-locals-e e new-acc)))
      (uncover-locals-e effect effect-locals)]
      [`(if ,pred ,effect ,effect_1)
        (uncover-locals-e effect_1 (uncover-locals-e effect (uncover-locals-pred pred acc)))]
      [`(return-point ,label ,tail)
      (uncover-locals-t tail acc)]))

  ;; tail [Setof aloc] -> [Setof aloc]
  ;;
  ;; Takes in tail statement and set of abstract locations used in the program so far 
  ;; and returns set of alocs with new abstract locations added
  (define (uncover-locals-t t acc)
    (match t 
    [`(begin ,effects ... ,tail) 
      (define effect-locals
          (for/fold ([new-acc acc])
                    ([e effects]) 
          (uncover-locals-e e new-acc)))
      (uncover-locals-t tail effect-locals)]
      [`(jump ,trg ,loc ...) 
      (define alocs 
        (for/fold ([lst acc])
                ([l loc])
               (add-aloc lst l)))
        alocs]
      [`(if ,pred ,tail ,tail_1)
        (uncover-locals-t tail_1 (uncover-locals-t tail (uncover-locals-pred pred acc)))]))
  
  ;; [SetOf Aloc] aloc -> [Setof Aloc]
  ;;
  ;; adds aloc to set of aloc if given aloc is aloc?
  ;; and returns the environment: [Setof Aloc] so far
  (define (add-aloc env aloc)
    (if (aloc? aloc)
      (set-add env aloc)
      env))
    
  ;; triv -> boolean
  ;; returns true if triv is an int64 or aloc
  (define (triv? t)
    (or (opand? t) (label? t)))

  ;; binop -> boolean
  ;; returns true if binop is a + or *
  (define (binop? b)
    (or (eq? b '+) (eq? b '*) (eq? b '-)))

  ;; trg -> boolean
  ;; returns true if trg is a label or loc
  (define (trg? t)
    (or (label? t) (loc? t)))
  
  ;; loc -> boolean
  ;; returns true if loc is an rloc (register or fvar) or aloc
  (define (loc? loc)
    (or (or (register? loc) (fvar? loc)) (aloc? loc)))
  
  ;; opand -> boolean
  ;; returns true if opand is an int64 or loc
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

  (uncover-locals-p p '()))

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
; set loc value
; true
; not pred
; relop opand opand
; begin effect tail
(define ul-v6-6 
  '(module
  ((new-frames ()))
  (begin
    (set! tmp-ra.1 r15)
    (if (if (begin (set! x.6 2) (set! x.5 1) (< x.5 x.6))
          (not (true))
          (< x.6 10))
      (begin (set! x.4 x.5) (set! x.4 (+ x.4 2)))
      (set! x.4 x.6))
    (set! rax 2)
    (jump tmp-ra.1 rbp rax))))

(define ul-v6-6-compiled 
'(module
  ((new-frames ()) (locals (x.5 x.6 x.4 tmp-ra.1)))
  (begin
    (set! tmp-ra.1 r15)
    (if (if (begin (set! x.6 2) (set! x.5 1) (< x.5 x.6))
          (not (true))
          (< x.6 10))
      (begin (set! x.4 x.5) (set! x.4 (+ x.4 2)))
      (set! x.4 x.6))
    (set! rax 2)
    (jump tmp-ra.1 rbp rax))))

(check-true 
(set=? '(x.5 x.6 x.4 tmp-ra.1) 
      (info-ref (list-ref (uncover-locals ul-v6-6) 1) 'locals)))


; if pred tail tail
; begin effect tail
; set loc triv
; set loc (binop loc opand)
; jump trg loc
; relop loc opand
(define ul-v6-5 
'(module ((new-frames ())) 
  (begin (set! tmp-ra.74 r15) 
    (if (begin (set! tmp.79 0) (> tmp.79 1)) 
    (begin 
      (set! rax 0) 
      (jump tmp-ra.74 rbp rax)) 
    (begin 
      (set! rax 0) 
      (set! rax (+ rax 1)) 
      (jump tmp-ra.74 rbp rax))))))

(define ul-v6-5-compiled
'(module
  ((new-frames ()) (locals (tmp-ra.74 tmp.79)))
  (begin
    (set! tmp-ra.74 r15)
    (if (begin (set! tmp.79 0) (> tmp.79 1))
      (begin (set! rax 0) (jump tmp-ra.74 rbp rax))
      (begin (set! rax 0) (set! rax (+ rax 1)) (jump tmp-ra.74 rbp rax))))))
;(uncover-locals ul-v6-5) 
;(check-equal? (uncover-locals ul-v6-5) ul-v6-5-compiled)
(check-true (set=? '(tmp-ra.74 tmp.79) (info-ref (list-ref (uncover-locals ul-v6-5) 1) 'locals)))

(define ul-v6-4 
'(module ((new-frames ())) 
  (begin 
    (set! tmp-ra.77 r15) 
    (set! y.4 5) 
    (set! x.3 1) 
    (set! x.3 (+ x.3 2)) 
    (set! z.5 2) 
    (set! x.3 (+ x.3 y.4)) 
    (set! x.3 y.4) 
    (set! x.3 (+ x.3 z.5)) 
    (set! x.3 x.3) 
    (set! rax x.3) 
    (jump tmp-ra.77 rbp rax))))
(define ul-v6-4-compiled
'(module
  ((new-frames ()) (locals (z.5 x.3 y.4 tmp-ra.77)))
  (begin
    (set! tmp-ra.77 r15)
    (set! y.4 5)
    (set! x.3 1)
    (set! x.3 (+ x.3 2))
    (set! z.5 2)
    (set! x.3 (+ x.3 y.4))
    (set! x.3 y.4)
    (set! x.3 (+ x.3 z.5))
    (set! x.3 x.3)
    (set! rax x.3)
    (jump tmp-ra.77 rbp rax))))
;(uncover-locals ul-v6-4) 
(check-equal? (uncover-locals ul-v6-4) ul-v6-4-compiled)
(check-true (set=? '(z.5 x.3 y.4 tmp-ra.77) (info-ref (list-ref (uncover-locals ul-v6-4) 1) 'locals)))


(define ul-v6-3 
'(module ((new-frames ())) 
  (begin 
    (set! tmp-ra.78 r15) 
    (set! x.1 4) 
    (set! x.1 (+ x.1 10)) 
    (set! rax x.1) 
    (set! rax (+ rax 5)) 
    (jump tmp-ra.78 rbp rax))))
(define ul-v6-3-compiled
'(module
  ((new-frames ()) (locals (x.1 tmp-ra.78)))
  (begin
    (set! tmp-ra.78 r15)
    (set! x.1 4)
    (set! x.1 (+ x.1 10))
    (set! rax x.1)
    (set! rax (+ rax 5))
    (jump tmp-ra.78 rbp rax))))
;(uncover-locals ul-v6-3) 
;(check-equal? (uncover-locals ul-v6-3) ul-v6-3-compiled)
(check-true (set=? '(tmp-ra.78 x.1) (info-ref (list-ref (uncover-locals ul-v6-3) 1) 'locals)))

(define ul-v6-2 
'(module ((new-frames ())) 
  (begin 
    (set! tmp-ra.75 r15) 
    (set! rax 1) 
    (set! rax (+ rax 2)) 
    (jump tmp-ra.75 rbp rax))))
(define ul-v6-2-compiled
'(module
  ((new-frames ()) (locals (tmp-ra.75)))
  (begin
    (set! tmp-ra.75 r15)
    (set! rax 1)
    (set! rax (+ rax 2))
    (jump tmp-ra.75 rbp rax))))
;(check-equal? (uncover-locals ul-v6-2) ul-v6-2-compiled)
(check-true (set=? '(tmp-ra.75) (info-ref (list-ref (uncover-locals ul-v6-2) 1) 'locals)))

(define ul-v6-1 
'(module 
  ((new-frames ())) 
  (begin 
    (set! tmp-ra.131 r15) 
    (if (begin 
          (set! tmp.169 0) 
          (> tmp.169 1)) 
    (begin (set! rax 0) (jump tmp-ra.131 rbp rax)) 
    (begin (set! rax 0) (set! rax (+ rax 1)) 
    (jump tmp-ra.131 rbp rax))))))

(define ul-v6-1-compiled 
'(module
  ((new-frames ()) (locals (tmp-ra.131 tmp.169)))
  (begin
    (set! tmp-ra.131 r15)
    (if (begin (set! tmp.169 0) (> tmp.169 1))
      (begin (set! rax 0) (jump tmp-ra.131 rbp rax))
      (begin (set! rax 0) (set! rax (+ rax 1)) (jump tmp-ra.131 rbp rax))))))
;(check-equal? (uncover-locals ul-v6-1) ul-v6-1-compiled)
(check-true (set=? '(tmp-ra.131 tmp.169) (info-ref (list-ref (uncover-locals ul-v6-1) 1) 'locals)))

(module+ test
(require rackunit)

; return-point
(define ul-8-compiled
'(module
  ((new-frames ()) (locals (tmp-ra.4)))
  (define L.swap.1
    ((new-frames ((nfv.2 nfv.3))) (locals (nfv.2 nfv.3 z.3 tmp-ra.1 x.1 y.2)))
    (begin
      (set! tmp-ra.1 r15)
      (set! x.1 fv0)
      (set! y.2 fv1)
      (if (< y.2 x.1)
        (begin (set! rax x.1) (jump tmp-ra.1 rbp rax))
        (begin
          (return-point L.rp.1
            (begin
              (set! nfv.3 x.1)
              (set! nfv.2 y.2)
              (set! r15 L.rp.1)
              (jump L.swap.1 rbp r15 nfv.2 nfv.3)))
          (set! z.3 rax)
          (set! rax z.3)
          (jump tmp-ra.1 rbp rax)))))
  (begin
    (set! tmp-ra.4 r15)
    (set! fv1 2)
    (set! fv0 1)
    (set! r15 tmp-ra.4)
    (jump L.swap.1 rbp r15 fv0 fv1))))
(define ul-8
'(module
  ((new-frames ()))
  (define L.swap.1
    ((new-frames ((nfv.2 nfv.3))))
    (begin
      (set! tmp-ra.1 r15)
      (set! x.1 fv0)
      (set! y.2 fv1)
      (if (< y.2 x.1)
        (begin (set! rax x.1) (jump tmp-ra.1 rbp rax))
        (begin
          (return-point L.rp.1
            (begin
              (set! nfv.3 x.1)
              (set! nfv.2 y.2)
              (set! r15 L.rp.1)
              (jump L.swap.1 rbp r15 nfv.2 nfv.3)))
          (set! z.3 rax)
          (set! rax z.3)
          (jump tmp-ra.1 rbp rax)))))
  (begin
    (set! tmp-ra.4 r15)
    (set! fv1 2)
    (set! fv0 1)
    (set! r15 tmp-ra.4)
    (jump L.swap.1 rbp r15 fv0 fv1))))

(check-true (set=? '(tmp-ra.4) (info-ref (list-ref (uncover-locals ul-8) 1) 'locals)))
(check-true (set=? '(nfv.2 nfv.3 z.3 tmp-ra.1 x.1 y.2) 
           (info-ref (list-ref (list-ref (uncover-locals ul-8) 2) 2) 'locals))))

(run-tests
   (test-suite
   ""
    (test-compiler-pass uncover-locals interp-asm-pred-lang-v6 interp-asm-pred-lang-v6/locals asm-pred-lang-v6/locals?))))

