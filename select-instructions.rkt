#lang racket

(provide select-instructions)

(require
 cpsc411/compiler-lib
 cpsc411/2c-run-time
 cpsc411/langs/v6
 cpsc411/graph-lib
 racket/trace
 rackunit)


#|
  imp-cmf-lan-v6:
  
  p	 	::=	 	(module info (define label info tail) ... tail)
 	 	 	 	 
  info	 	::=	 	(#:from-contract (info/c (new-frames (frame ...))))
 	 	 	 	 
  frame	 	::=	 	(aloc ...)
 	 	 	 	 
  pred	 	::=	 	(relop opand opand) 
 	 	|	 	(true) 
 	 	|	 	(false)
 	 	|	 	(not pred) 
 	 	|	 	(begin effect ... pred) 
 	 	|	 	(if pred pred pred) 
 	 	 	 	 
  tail	 	::=	 	(jump trg loc ...) 
 	 	|	 	(begin effect ... tail) 
 	 	|	 	(if pred tail tail) 
 	 	 	 	 
  value	 	::=	 	triv 
 	 	|	 	(binop opand opand)
 	 	 	 	 
  effect	 	::=	 	(set! loc value) 
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

;; Exercise 6
;; Reference: went to Paulette's office hours
;; Imp-cmf-lang-v6 -> asm-pred-lang-v6
;; selects sequences of abstract assembly instructions to implement operations of source language
(define (select-instructions p)

  ;; p -> p 
  ;; 
  ;; compiles p by calling helpers to select sequences of abstract assmebly to implement operations
  (define (select-p p)
    (match p
      [`(module ,info ,nested ... ,tail) 
      `(module
        ,info  
        ,@(map select-p-nested nested)
        ,(select-tail tail))]))
  
  ;; nested-p -> nested-p
  ;; nested-p ::= (define label info tail)
  ;;
  ;; compiles nested-p by calling select-tail to select sequences of abstract assembly
  (define (select-p-nested p)
    (match p
      [`(define ,label ,info ,tail)
        `(define 
          ,label
          ,info
          ,(select-tail tail))]))

  ; (Imp-cmf-lang-v6 value) -> (List-of (Asm-pred-lang-v6 effect)) and (Asm-pred-lang-v6 aloc)
  ; Assigns the value v to a fresh temporary, returning two values: the list of
  ; statements the implement the assignment in Loc-lang, and the aloc that the
  ; value is stored in.
  #|(define (assign-tmp v)
    (define x (fresh))
    (match v
      [`(,binop ,opand ,opand1)
       #:when(and (binop? binop)
                  (opand? opand)
                  (opand? opand1))
      (values 
      (list `(set! ,x ,opand) 
            `(set! ,x (,binop ,x ,opand1))) ;; TODO: why does this not map to proper variables? :(
        x)]
      [`(set! ,aloc (,binop ,triv_1 ,triv)) 
        #:when (and (aloc? aloc) 
                    (int64? triv) 
                    (aloc? triv_1) 
                    (binop? binop))
        (values 
          (list `(set! ,aloc ,triv) 
                `(set! ,aloc (,binop ,aloc ,triv_1)))
           x)]
      ; TODO: fix this nested deep matching?
      [`(,relop ,opand ,opand1)
      #:when(and (relop? relop)
                  (opand? opand)
                  (opand? opand1))
        (if (int64? opand)
          (values 
            (list `(set! ,x ,opand)
                  `(,relop ,x ,opand1))
          x)
          (values 
            (list v)))]))|#

  ;; pred -> pred
  ;; compiles pred by un-nesting begin statements 
  (define (select-pred pred) 
    (match pred
    [`(,relop ,opand ,opand1) 
    (define tmp (fresh))
    (if (int64? opand)
      `(begin
        (set! ,tmp ,opand)
        (,relop ,tmp ,opand1))
      pred)]
 	 	[`(true) 
    pred]
 	 	[`(false)
    pred]
 	 	[`(not ,pred)
    `(not ,(select-pred pred))]
 	 	[`(begin ,effect ... ,pred)
    (make-begin 
      (map select-effect effect) 
        (select-pred pred))]
 	 	[`(if ,pred ,pred1 ,pred2)
    `(if ,(select-pred pred) 
        ,(select-pred pred1) 
        ,(select-pred pred2))]))

  ;; tail -> tail
  ;;
  ;; compiles tail by un-nesting begins and calling helpers to select nested sequences
  (define (select-tail e)
    (match e
      [`(begin ,xs ... ,t) 
        (make-begin 
          (map select-effect xs) 
          (select-tail t))]
      [`(if ,pred ,tail ,tail1)
      `(if ,(select-pred pred) 
          ,(select-tail tail) 
          ,(select-tail tail1))]
      [`(jump ,trg ,loc ...)
      e]))
  
  ;; value loc ->  value
  ;;
  ;; compiles value statements by un-nesting value statements 
  (define (select-value v loc)
    (match v
      [`(,binop ,opand ,opand1) 
        (if (equal? loc opand)
          (list '() `(set! ,loc ,v))
          (list 
            (list `(set! ,loc ,opand))
            `(set! ,loc (,binop ,loc ,opand1))))]
      [(? triv?) 
       (list '() `(set! ,loc ,v))]))

  ;; effect ->  effect
  ;; 
  ;; compiles effect statement by un-nesting value statements 
  (define (select-effect e)
    (match e 
      [`(set! ,loc ,value) 
      (make-begin 
           (first (select-value value loc))
            (last (select-value value loc)))] 
      [`(begin ,effects ... ,effect) 
      (make-begin
        (map select-effect effects) 
        (select-effect effect))]
      [`(if ,pred ,effect ,effect1)
      `(if ,(select-pred pred) 
          ,(select-effect effect) 
          ,(select-effect effect1))]
      [`(return-point ,label ,tail)
      `(return-point 
        ,label
        ,(select-tail tail))]))

  ;; binop -> boolean
  ;; returns true if binop is a + or *
  (define (binop? b)
    (or (eq? b '+) 
        (eq? b '*)))

  ;; triv -> boolean
  ;; returns true if triv is an opand? or label?
   (define (triv? triv)
    (or (opand? triv) 
        (label? triv)))
  
  ;; opand -> boolean
  ;; returns true if opand is an int64? or loc?
  (define (opand? opand)
    (or (int64? opand) 
        (loc? opand)))

  ;; loc -> boolean
  ;; returns true if loc is an rloc? or aloc?
  (define (loc? loc)
    (or (rloc? loc) (aloc? loc)))
  
  ;; rloc -> boolean
  ;; returns true if rloc is an register? or fvar?
  (define (rloc? loc)
    (or (register? loc) (fvar? loc)))

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
  
  (select-p p))

(module+ test 
  (require
  rackunit
   rackunit/text-ui
   cpsc411/langs/v6
   cpsc411/test-suite/public/v6
   cpsc411/test-suite/utils)

; jump trg loc
; begin effect ... effect
; begin effect ... tail
; binop opand opand
(define si-v6-20
'(module
  ((new-frames ()))
  (begin
    (set! tmp-ra.1 r15)
    (begin
      (set! x.6 (+ 3 2))
      (set! x.5 1)
      (begin
        (set! x.4 x.5)
        (begin (set! x.4 2) (set! x.6 x.4))
        (begin (set! rax 2) (jump tmp-ra.1 rbp rax)))))))

(define si-v6-20-compiled
  '(module
    ((new-frames ()))
    (begin
      (set! tmp-ra.1 r15)
      (set! x.6 3)
      (set! x.6 (+ x.6 2))
      (set! x.5 1)
      (set! x.4 x.5)
      (set! x.4 2)
      (set! x.6 x.4)
      (set! rax 2)
      (jump tmp-ra.1 rbp rax))))

(check-equal?
  (interp-asm-pred-lang-v6 si-v6-20-compiled)
  (interp-asm-pred-lang-v6 (select-instructions si-v6-20)))

; if pred pred pred
; if pred effect effect
; begin effect ... pred
; begin effect ... effect 
; set loc value
; true
; not pred
; relop opand opand
; begin effect tail
(define si-v6-19
'(module
  ((new-frames ()))
  (begin
    (set! tmp-ra.1 r15)
    (begin
      (if (if (begin (set! x.6 2) (set! x.5 1) (< x.5 x.6))
            (not (true))
            (< x.6 10))
        (begin (set! x.4 x.5) (set! x.4 (+ x.4 2)))
        (set! x.4 x.6))
      (begin (set! rax 2) (jump tmp-ra.1 rbp rax))))))

(define si-v6-19-compiled 
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
(check-equal?
  (interp-asm-pred-lang-v6 si-v6-19-compiled)
  (interp-asm-pred-lang-v6 (select-instructions si-v6-19)))

; if pred effect effect
; false
; not pred
; begin effect tail
(define ic-v6-18-compiled 
'(module
  ((new-frames ()))
  (begin
    (set! tmp-ra.1 r15)
    (begin
      (set! x.6 2)
      (set! x.5 1)
      (begin
        (if (not (false)) (set! x.4 x.5) (set! x.4 x.6))
        (begin (set! x.4 2) (set! x.6 x.4))
        (begin (set! rax 2) (jump tmp-ra.1 rbp rax)))))))

(define si-v6-7 
  '(module ((new-frames ())) 
  (begin (set! tmp-ra.149 r15) 
  (begin (set! x.1 10) 
  (set! y.3 7) 
  (set! x.1 (+ x.1 y.3)) 
  (set! x.1 (+ y.3 y.3)) 
  (begin (set! rax x.1) (jump tmp-ra.149 rbp rax))))))
(define si-v6-7-compiled 
'(module
  ((new-frames ()))
  (begin
    (set! tmp-ra.149 r15)
    (set! x.1 10)
    (set! y.3 7)
    (set! x.1 (+ x.1 y.3))
    (set! x.1 y.3)
    (set! x.1 (+ x.1 y.3))
    (set! rax x.1)
    (jump tmp-ra.149 rbp rax))))
(check-equal?
  (interp-asm-pred-lang-v6 si-v6-7-compiled)
  (interp-asm-pred-lang-v6 (select-instructions si-v6-7)))

(define si-v6-6 
'(module 
  ((new-frames ())) 
  (begin 
    (set! tmp-ra.126 r15)
    (begin 
      (set! x.1 1)
      (set! y.1 1) 
      (set! z.1 (+ x.1 y.1)) 
      (set! w.1 x.1) 
      (set! w.1 (+ w.1 z.1)) 
      (begin 
        (set! rax w.1) 
        (jump tmp-ra.126 rbp rax))))))

(define si-v6-6-compiled
'(module
  ((new-frames ()))
  (begin
    (set! tmp-ra.126 r15)
    (set! x.1 1)
    (set! y.1 1)
    (set! z.1 x.1)
    (set! z.1 (+ z.1 y.1))
    (set! w.1 x.1)
    (set! w.1 (+ w.1 z.1))
    (set! rax w.1)
    (jump tmp-ra.126 rbp rax))))
(check-equal? (select-instructions si-v6-6) si-v6-6-compiled)
(check-equal?
  (interp-asm-pred-lang-v6 si-v6-6-compiled)
  (interp-asm-pred-lang-v6 (select-instructions si-v6-6)))

(define si-v6-4
'(module
  ((new-frames ()))
  (begin
    (set! tmp-ra.1 r15)
    (begin
      (set! x.6 2)
      (set! x.5 1)
      (begin
        (set! x.4 x.5)
        (begin (set! x.4 2) (set! x.6 x.4))
        (begin (set! rax 2) (jump tmp-ra.1 rbp rax)))))))

(define si-v6-4-compiled
'(module
  ((new-frames ()))
  (begin
    (set! tmp-ra.1 r15)
    (set! x.6 2)
    (set! x.5 1)
    (set! x.4 x.5)
    (set! x.4 2)
    (set! x.6 x.4)
    (set! rax 2)
    (jump tmp-ra.1 rbp rax))))

(check-equal? (select-instructions si-v6-4) si-v6-4-compiled)
(check-equal?
  (interp-asm-pred-lang-v6 si-v6-4-compiled)
  (interp-asm-pred-lang-v6 (select-instructions si-v6-4)))

; nested begins
(define si-v6-2
'(module
  ((new-frames ()))
  (begin
    (set! tmp-ra.1 r15)
    (begin
      (set! tmp.100 1)
      (begin
        (set! tmp.101 (+ 1 tmp.100))
        (set! tmp.102 (+ 2 tmp.100))
        (begin 
          (set! rax (+ tmp.101 tmp.102)) 
          (jump tmp-ra.1 rbp rax)))))))

(define si-v6-2-compiled 
'(module
  ((new-frames ()))
  (begin
    (set! tmp-ra.1 r15)
    (set! tmp.100 1)
    (set! tmp.101 1)
    (set! tmp.101 (+ tmp.101 tmp.100))
    (set! tmp.102 2)
    (set! tmp.102 (+ tmp.102 tmp.100))
    (set! rax tmp.101)
    (set! rax (+ rax tmp.102))
    (jump tmp-ra.1 rbp rax))))

(check-equal? (select-instructions si-v6-2) si-v6-2-compiled)
(check-equal?
  (interp-asm-pred-lang-v6 si-v6-2-compiled)
  (interp-asm-pred-lang-v6 (select-instructions si-v6-2)))

;; return-point
; if pred tail tail
(define si-v6-1-compiled 
'(module
  ((new-frames ()))
  (define L.swap.1
    ((new-frames ((nfvar.3))))
    (begin
      (set! tmp-ra.2 r15)
      (set! x.1 rdi)
      (set! y.2 rsi)
      (set! x.3 rdx)
      (set! x.4 rcx)
      (set! x.5 r8)
      (set! x.6 r9)
      (set! x.7 fv0)
      (set! x.8 fv1)
      (set! x.9 fv2)
      (if (< y.2 x.1)
        (begin (set! rax x.1) (jump tmp-ra.2 rbp rax))
        (begin
          (return-point
           L.rp.1
           (begin
             (set! nfvar.3 x.7)
             (set! r9 x.6)
             (set! r8 x.5)
             (set! rcx x.4)
             (set! rdx x.3)
             (set! rsi x.1)
             (set! rdi y.2)
             (set! r15 L.rp.1)
             (jump L.swap.1 rbp r15 rdi rsi rdx rcx r8 r9 nfvar.3)))
          (set! z.3 rax)
          (set! z.4 2)
          (set! rax z.3)
          (jump tmp-ra.2 rbp rax)))))
  (begin
    (set! tmp-ra.1 r15)
    (set! rsi 2)
    (set! rdi 1)
    (set! r15 tmp-ra.1)
    (jump L.swap.1 rbp r15 rdi rsi))))
  
(define si-v6-1 
'(module
  ((new-frames ()))
  (define L.swap.1
    ((new-frames ((nfvar.3))))
    (begin
      (set! tmp-ra.2 r15)
      (begin
        (set! x.1 rdi)
        (set! y.2 rsi)
        (set! x.3 rdx)
        (set! x.4 rcx)
        (set! x.5 r8)
        (set! x.6 r9)
        (set! x.7 fv0)
        (set! x.8 fv1)
        (set! x.9 fv2)
        (if (< y.2 x.1)
          (begin (set! rax x.1) (jump tmp-ra.2 rbp rax))
          (begin
            (begin
              (return-point
               L.rp.1
               (begin
                 (set! nfvar.3 x.7)
                 (set! r9 x.6)
                 (set! r8 x.5)
                 (set! rcx x.4)
                 (set! rdx x.3)
                 (set! rsi x.1)
                 (set! rdi y.2)
                 (set! r15 L.rp.1)
                 (jump L.swap.1 rbp r15 rdi rsi rdx rcx r8 r9 nfvar.3)))
              (set! z.3 rax))
            (set! z.4 2)
            (begin (set! rax z.3) (jump tmp-ra.2 rbp rax)))))))
  (begin
    (set! tmp-ra.1 r15)
    (begin
      (set! rsi 2)
      (set! rdi 1)
      (set! r15 tmp-ra.1)
      (jump L.swap.1 rbp r15 rdi rsi)))))
;(select-instructions si-v6-1)
(check-equal? (select-instructions si-v6-1) si-v6-1-compiled)
(check-equal?
  (interp-asm-pred-lang-v6 si-v6-1-compiled) 
  (interp-asm-pred-lang-v6 (select-instructions si-v6-1)))

(define si-v6-3
'(module
  ((new-frames ()))
  (begin 
    (set! tmp-ra.1 r15) 
    (begin 
      (set! rax 5) 
     (jump tmp-ra.1 rbp rax)))))

(define si-v6-3-compiled 
'(module
  ((new-frames ()))
  (begin 
    (set! tmp-ra.1 r15) 
    (set! rax 5) 
    (jump tmp-ra.1 rbp rax))))

(check-equal? (select-instructions si-v6-3) si-v6-3-compiled)
(check-equal?
  (interp-asm-pred-lang-v6 si-v6-3-compiled)
  (interp-asm-pred-lang-v6 (select-instructions si-v6-3)))

; pred int comparison
(define si-v6-5
'(module
  ((new-frames ()))
  (define L.swap.1
    ((new-frames ()))
    (begin
      (set! tmp-ra.1 r15)
      (begin
        (set! x.1 rdi)
        (set! y.2 rsi)
        (set! x.3 rdx)
        (if (= 2 3)
          (begin (set! rax (+ x.1 4)) (jump tmp-ra.1 rbp rax))
          (begin
            (set! z.3 3)
            (set! z.4 (+ x.1 4))
            (begin (set! rax z.3) (jump tmp-ra.1 rbp rax)))))))
  (begin
    (set! tmp-ra.2 r15)
    (begin
      (set! rsi 2)
      (set! rdi 1)
      (set! r15 tmp-ra.2)
      (jump L.swap.1 rbp r15 rdi rsi)))))

(define si-v6-5-compiled 
'(module
  ((new-frames ()))
  (define L.swap.1
    ((new-frames ()))
    (begin
      (set! tmp-ra.1 r15)
      (set! x.1 rdi)
      (set! y.2 rsi)
      (set! x.3 rdx)
      (if (begin (set! tmp.1 2) (= tmp.1 3))
        (begin (set! rax x.1) (set! rax (+ rax 4)) (jump tmp-ra.1 rbp rax))
        (begin
          (set! z.3 3)
          (set! z.4 x.1)
          (set! z.4 (+ z.4 4))
          (set! rax z.3)
          (jump tmp-ra.1 rbp rax)))))
  (begin
    (set! tmp-ra.2 r15)
    (set! rsi 2)
    (set! rdi 1)
    (set! r15 tmp-ra.2)
    (jump L.swap.1 rbp r15 rdi rsi))))

;(check-equal? (select-instructions si-v6-5) si-v6-5-compiled)
(check-equal?
  (interp-asm-pred-lang-v6 si-v6-5-compiled)
  (interp-asm-pred-lang-v6 (select-instructions si-v6-5)))

(run-tests
   (test-suite
    ""
    (test-compiler-pass select-instructions interp-imp-cmf-lang-v6 interp-asm-pred-lang-v6 asm-pred-lang-v6?))))
