#lang racket

(provide implement-fvars)

(require
 cpsc411/compiler-lib
 cpsc411/2c-run-time
 cpsc411/langs/v6
 cpsc411/graph-lib
 racket/trace
 rackunit)


#| Nested-asm-lang-fvars-v6: 
  p	 	::=	 	(module (define label tail) ... tail)
 	 	 	 	 
  pred	 	::=	 	(relop loc opand) 
 	 	|	 	(true) 
 	 	|	 	(false)
 	 	|	 	(not pred) 
 	 	|	 	(begin effect ... pred) 
 	 	|	 	(if pred pred pred) 
 	 	 	 	 
  tail	 	::=	 	(jump trg) 
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
 	 	 	 	 
  loc	 	::=	 	reg
 	 	|	 	fvar
 	 	 	 	 
  trg	 	::=	 	label
 	 	|	 	loc
 	 	 	 	 
  reg	 	::=	 	rsp
 	 	|	 	rbp
 	 	|	 	rax
 	 	|	 	rbx
 	 	|	 	rcx
 	 	|	 	rdx
 	 	|	 	rsi
 	 	|	 	rdi
 	 	|	 	r8
 	 	|	 	r9
 	 	|	 	r12
 	 	|	 	r13
 	 	|	 	r14
 	 	|	 	r15
 	 	 	 	 
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

;; Exercise 17
;; (Nested-asm-lang-fvars-v6) -> (Nested-asm-lang-v6)
;; reifying fvars into displacement mode operands by using addrs instead of fvars
;; reference: Paulette's tutorial notes/office hours <3
(define(implement-fvars p)

  ;; p -> p
  ;;
  ;; calls implement-fvars-tail with tail and current fbp offset intialized to 0
  (define (implement-fvars-p p)
    (match p
      [`(module ,nested ... ,tail) 
      (define-values (t nb)
        (implement-fvars-tail tail 0))
      `(module 
        ,@(map implement-fvars-p-nested nested) 
          ,t)]))
  
  ;; tail -> (tail (current fbp offset))
  ;; nested-p ::= define label tail 
  ;;
  ;; calls implement-fvars-tail with tail and current fbp offset intialized to 0
  (define (implement-fvars-p-nested p)
    (match p 
    [`(define ,label ,tail)
    (define-values (t nb)
      (implement-fvars-tail tail 0))
      `(define 
        ,label
        ,t)]))
  
  ;; tail (current fbp offset) -> tail (current fbp offset)
  ;;
  ;; takes in tail and current fbp offset to compile tail by updating fvars to addresses
  ;; and updating current fbp offset for this block
  (define (implement-fvars-tail tail acc)
    (match tail 
    [`(jump ,trg)
      (if (fvar? trg)
        (values `(jump ,(fvar->addr trg acc)) acc)
        (values tail acc))]
    [`(begin ,effect ... ,tail)
      (define-values (xs entry-nb) 
        (for/fold ([lst-effects '()]
                      [s-nb acc])
                    [(s effect)]
            (define-values (e nb)
                (implement-fvars-effect s s-nb))
            (values
              (cons e lst-effects)
              nb)))
      (define-values (t tail-nb)
            (implement-fvars-tail tail entry-nb))
      (values `(begin ,@(reverse xs) ,t) tail-nb)]
    [`(if ,pred ,tail ,tail_1)
      (define-values (p pred-nb)
            (implement-fvars-pred pred acc))
      (define-values (t tail-nb)
            (implement-fvars-tail tail pred-nb))
      (define-values (t_1 tail_1-nb)
            (implement-fvars-tail tail_1 tail-nb))
      (values `(if ,p ,t ,t_1)
        tail_1-nb)]))
  
  ;; pred (current fbp offset) -> pred (current fbp offset)
  ;;
  ;; takes in pred and current fbp offset to compile pred by updating fvars to addresses
  ;; and updating current fbp offset for this block
  (define (implement-fvars-pred pred acc) 
    (match pred
      [`(,relop ,opand ,opand_1)
      (values `(,relop ,(fvar->addr opand acc) ,(fvar->addr opand_1 acc)) acc)]
    [`(true)
      (values pred acc)]
    [`(false)
      (values pred acc)]
    [`(not ,pred)
     (define-values (p pred-nb)
          (implement-fvars-pred pred acc))
      (values `(not ,p) pred-nb)]
    [`(begin ,effects ... ,pred)
      (define-values (s entry-nb) 
        (for/fold ([lst-effects '()]
                    [s-nb acc])
                  [(xs effects)]
          (define-values (e nb)
              (implement-fvars-effect xs s-nb))
          (values
            (cons e lst-effects)
            nb)))
      (define-values (p pred-nb)
            (implement-fvars-pred pred entry-nb))
      (values `(begin ,@(reverse s) ,p)
        pred-nb)]
    [`(if ,pred ,pred_1 ,pred_2)
        (define-values (p pred-nb)
            (implement-fvars-pred pred acc))
        (define-values (p_1 pred_1-nb)
            (implement-fvars-pred pred_1 pred-nb))
        (define-values (p_2 pred_2-nb)
            (implement-fvars-pred pred_2 pred_1-nb))
        (values `(if ,p ,p_1 ,p_2)
                  pred_2-nb)]))

  ;; effect (current fbp offset) -> effect (current fbp offset)
  ;;
  ;; takes in effect and current fbp offset by updating fvar with displacement mode operand 
  ;; calculated using the current fbp offset relative to the base of the frame
  (define (implement-fvars-effect s acc)
    (match s
      [`(set! ,loc ,triv)
      #:when(triv? triv)
      (values 
        `(set! ,(fvar->addr loc acc) ,(fvar->addr triv acc))
          acc)]
      [`(set! ,loc_1 (,binop ,loc_1 ,opand))
        (cond 
          [(equal? loc_1 (current-frame-base-pointer-register))
            (begin 
              (define nb 
                (if (equal? '- binop)
                  opand
                  0))
              (values s nb))] 
          [else
            (values 
              `(set! ,(fvar->addr loc_1 acc) (,binop ,(fvar->addr loc_1 acc) ,(fvar->addr opand acc)))
              acc)])]
      [`(begin ,effects ... ,effect)
        (define-values (xs entry-nb) 
          (for/fold ([lst-effects '()]
                      [s-nb acc])
                      [(s effects)]
            (define-values (e nb)
                (implement-fvars-effect s s-nb))
            (values
              (cons e lst-effects)
              nb)))
        (define-values (ss effect-nb)
          (implement-fvars-effect effect entry-nb))
        (values `(begin ,@(reverse xs) ,ss)
                  effect-nb)]
      [`(if ,pred ,effect ,effect_1)
      (define-values (p pred-nb)
            (implement-fvars-pred pred acc))
      (define-values (s effect-nb)
          (implement-fvars-effect effect pred-nb))
      (define-values (s_1 effect_1-nb)
          (implement-fvars-effect effect_1 effect-nb))
      (values 
        `(if ,p
          ,s  
          ,s_1)
      effect_1-nb)]
      [`(return-point ,label ,tail)
       (define-values (t tail-nb)
          (implement-fvars-tail tail acc))
      (values `(return-point ,label ,t)
        tail-nb)]))

  ;; trg -> boolean
  ;; returns true if trg is register or label
  (define (trg? trg)
    (or (register? trg) (label? trg)))

  ;; triv -> boolean
  ;; returns true if triv is label or opand
  (define (triv? triv)
    (or (label? triv) (opand? triv)))
  
  ;; opand -> boolean
  ;; returns true if opand t is int64 or opand
  (define (opand? opand)
    (or (int64? opand) (loc? opand)))

  ;; loc -> boolean
  ;; returns true if loc loc is a loc?
  (define (loc? loc)
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
   
  ;; fvar nb -> displacement mode operand
  ;; defines a new displacement mode operand for address f if f is fvar?
  ;; else returns f
  (define (fvar->addr f nb)
    (if (fvar? f)
      `(,(current-frame-base-pointer-register) - 
          ,(+ (* (fvar->index f) (current-word-size-bytes))
              (* -1 nb)))
      f))

  ;; binop -> boolean
  ;; returns true if binop is a + or *
  (define (binop? b)
      (or (eq? b '+) (eq? b '*) (eq? b '-)))

  (implement-fvars-p p))

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
; begin effect tail
(define if-v6-6 
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

(define if-v6-6-compiled 
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

(check-equal? (implement-fvars if-v6-6) if-v6-6-compiled)
(check-equal?
  (interp-nested-asm-lang-v6 (implement-fvars if-v6-6))
  (interp-nested-asm-lang-v6 if-v6-6-compiled))

; if pred tail tail
; begin effect tail
; set loc triv
; set loc (binop loc opand)
; jump trg loc
; relop loc opand
(define if-v6-7 
'(module
  (begin
    (set! r15 r15)
    (if (begin (set! r14 0) (> r14 1))
      (begin (set! rax 0) (jump r15))
      (begin (set! rax 0) (set! rax (+ rax 1)) (jump r15))))))

(define if-v6-7-compiled
'(module
  (begin
    (set! r15 r15)
    (if (begin (set! r14 0) (> r14 1))
      (begin (set! rax 0) (jump r15))
      (begin (set! rax 0) (set! rax (+ rax 1)) (jump r15))))))

(check-equal? (implement-fvars if-v6-7) if-v6-7-compiled)
(check-equal?
  (interp-nested-asm-lang-v6 (implement-fvars if-v6-7))
  (interp-nested-asm-lang-v6 if-v6-7-compiled))

; set loc triv
; (set! loc_1 (binop loc_1 opand))
; jump trg 
; begin effect tail
(define if-v6-5 
'(module 
  (begin 
    (set! fv0 1) 
    (set! fv1 fv0) 
    (set! fv1 (* fv1 1)) 
    (set! fv2 fv1) 
    (set! fv2 (+ fv2 1)) 
    (begin 
      (set! rax fv2) 
      (jump r15)))))
(define if-v6-5-compiled 
'(module
  (begin
    (set! (rbp - 0) 1)
    (set! (rbp - 8) (rbp - 0))
    (set! (rbp - 8) (* (rbp - 8) 1))
    (set! (rbp - 16) (rbp - 8))
    (set! (rbp - 16) (+ (rbp - 16) 1))
    (begin (set! rax (rbp - 16)) (jump r15)))))
(check-equal? (implement-fvars if-v6-5) if-v6-5-compiled)
(check-equal?
  (interp-nested-asm-lang-v6 (implement-fvars if-v6-5))
  (interp-nested-asm-lang-v6 if-v6-5-compiled))

(define if-v6-4 
'(module 
  (begin 
    (set! fv2 10) 
    (set! fv0 10) 
    (set! fv1 fv2) 
    (set! fv0 (+ fv0 fv2)) 
    (set! fv0 (- fv0 fv1)) 
    (begin 
      (set! rax fv0) 
      (jump r15)))))
(define if-v6-4-compiled 
'(module
  (begin
    (set! (rbp - 16) 10)
    (set! (rbp - 0) 10)
    (set! (rbp - 8) (rbp - 16))
    (set! (rbp - 0) (+ (rbp - 0) (rbp - 16)))
    (set! (rbp - 0) (- (rbp - 0) (rbp - 8)))
    (begin (set! rax (rbp - 0)) (jump r15)))))
(nested-asm-lang-v6? (implement-fvars if-v6-4))
(nested-asm-lang-v6? if-v6-4-compiled)
(check-equal? (implement-fvars if-v6-4) if-v6-4-compiled)
(check-equal?
  (interp-nested-asm-lang-v6 (implement-fvars if-v6-4))
  (interp-nested-asm-lang-v6 if-v6-4-compiled))

(define if-v6-3 
'(module (begin (set! fv0 5) (begin (set! rax fv0) (jump r15)))))
(define if-v6-3-compiled 
'(module (begin (set! (rbp - 0) 5) (begin (set! rax (rbp - 0)) (jump r15)))))
(nested-asm-lang-v6? (implement-fvars if-v6-3))
(nested-asm-lang-v6? if-v6-3-compiled)
(check-equal? (implement-fvars if-v6-3) if-v6-3-compiled)
(check-equal?
  (interp-nested-asm-lang-v6 (implement-fvars if-v6-3))
  (interp-nested-asm-lang-v6 if-v6-3-compiled))

(define if-v6-2 
'(module (begin (set! rax 5) (jump r15))))
(define if-v6-2-compiled 
'(module (begin (set! rax 5) (jump r15))))
(check-equal? (implement-fvars if-v6-2) if-v6-2-compiled)
(nested-asm-lang-v6? (implement-fvars if-v6-2))
(nested-asm-lang-v6? if-v6-2-compiled)
(check-equal?
  (interp-nested-asm-lang-v6 (implement-fvars if-v6-2))
  (interp-nested-asm-lang-v6 if-v6-2-compiled))

(define if-v6-1 
'(module 
  (begin 
    (set! fv16 0) 
    (set! fv0 0) 
    (set! fv8 fv16) 
    (set! fv0 (+ fv0 fv16)) 
    (set! fv0 (+ fv0 fv8)) 
    (begin 
      (set! rax fv0) 
      (jump r15)))))
(define if-v6-1-compiled 
'(module
  (begin
    (set! (rbp - 128) 0)
    (set! (rbp - 0) 0)
    (set! (rbp - 64) (rbp - 128))
    (set! (rbp - 0) (+ (rbp - 0) (rbp - 128)))
    (set! (rbp - 0) (+ (rbp - 0) (rbp - 64)))
    (begin (set! rax (rbp - 0)) (jump r15)))))
(check-equal? (implement-fvars if-v6-1) if-v6-1-compiled)

(check-equal?
  (interp-nested-asm-lang-v6 (implement-fvars if-v6-1))
  (interp-nested-asm-lang-v6 if-v6-1-compiled))

; return-point
; if pred tail tail
; nested p
(define if-5-compiled
'(module
  (define L.swap.1
    (begin
      (set! (rbp - 16) r15)
      (set! r14 (rbp - 0))
      (set! r15 (rbp - 8))
      (if (< r15 r14)
        (begin (set! rax r14) (jump (rbp - 16)))
        (begin
          (begin
            (set! rbp (- rbp 24))
            (return-point L.rp.1
              (begin
                (set! (rbp - 8) r14)
                (set! (rbp - 0) r15)
                (set! r15 L.rp.1)
                (jump L.swap.1)))
            (set! rbp (+ rbp 24)))
          (set! r15 rax)
          (set! rax r15)
          (jump (rbp - 16))))))
  (begin
    (set! r15 r15)
    (set! (rbp - 8) 2)
    (set! (rbp - 0) 1)
    (set! r15 r15)
    (jump L.swap.1))))
(define if-5
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
            (return-point L.rp.1
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
(check-equal? (implement-fvars if-5)
if-5-compiled)

(set-count (hash-ref test-prog-dict interp-nested-asm-lang-fvars-v6 '()))
(run-tests
   (test-suite
    ""
    (test-compiler-pass implement-fvars interp-nested-asm-lang-fvars-v6 interp-nested-asm-lang-v6 nested-asm-lang-v6?))))

