#lang racket

(provide impose-calling-conventions)

(require
 cpsc411/compiler-lib
 cpsc411/2c-run-time
 cpsc411/langs/v6
 cpsc411/graph-lib
 racket/trace
 rackunit)


#|
  proc-imp-cmf-lang-v6:
   p	 	::=	 	(module (define label (lambda (aloc ...) entry)) ... entry)
 	entry	 	::=	 	tail
 	 	 	 	 
  pred	 	::=	 	(relop opand opand) 
 	 	|	 	(true) 
 	 	|	 	(false) 
 	 	|	 	(not pred) 
 	 	|	 	(begin effect ... pred) 
 	 	|	 	(if pred pred pred) 
 	 	 	 	 
  tail	 	::=	 	value 
 	 	|	 	(call triv opand ...) 
 	 	|	 	(begin effect ... tail) 
 	 	|	 	(if pred tail tail) 
 	 	 	 	 
  value	 	::=	 	triv 
 	 	|	 	(binop opand opand) 
 	 	|	 	(call triv opand ...) 
 	 	 	 	 
  effect	 	::=	 	(set! aloc value) 
 	 	|	 	(begin effect ... effect) 
 	 	|	 	(if pred effect effect) 
 	 	 	 	 
  opand	 	::=	 	int64
 	 	|	 	aloc
 	 	 	 	 
  triv	 	::=	 	opand
 	 	|	 	label
 	 	 	 	 
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

;; Exercise 5
;; Compiles Proc-imp-cmf-lang-v6 to Imp-cmf-lang-v6 by imposing calling conventions on all calls 
;; and entry points
;; registers for parameters are defined by current-parameter-registers 
;; registers for returns defined by current-return-address-register and current-return-value-register
(define (impose-calling-conventions p)

  ;; p -> p
  ;; compiles p by imposing calling conventions on p and all nested-p by recording new-frames info 
  ;; field with all new frames created in p block
  (define (impose-calling-conventions-p p)
    (match p
      [`(module ,nested ... ,entry)
      (define-values (lst-entry lst-nfvars)
        (impose-calling-conventions-entry entry))
      `(module 
          ((new-frames (,@lst-nfvars)))
          ,@(map impose-calling-conventions-nested-p nested) 
          ,lst-entry)]))
  
  ;; nested-p -> nested-p
  ;; 
  ;; nested-p ::= (define label (lambda (aloc ...) entry))
  ;; compiles p by imposing calling conventions on p and all nested-p by recording new-frames info 
  ;; field with all new frames created in nested-p block for this entry
  ;; defines register set of phsyical locations by calling current-parameter-registers and 
  ;; slowly expose phsyical locations making tmp-ra fvars if needed
  (define (impose-calling-conventions-nested-p p)
    (match p
      [`(define ,label (lambda (,aloc ...) ,entry))
      (begin
        (define-values (reg-set _) 
          (for/foldr ([new-reg-set '()]
                      [counter 0])
                       ([a aloc])
            (if (>= counter (length (current-parameter-registers)))
              (values 
                (cons (make-fvar (- counter (length (current-parameter-registers)))) new-reg-set)
                (add1 counter))
              (values 
                (cons (list-ref (current-parameter-registers) counter) new-reg-set)
                (add1 counter)))))
        (define lst-rlocs
            (for/list ([reg (reverse reg-set)]
                      [a aloc])
            `(set! ,a ,reg)))
        (define ra (fresh 'tmp-ra))
        (define-values (lst-tail lst-nfvars)
          (impose-calling-conventions-tail entry ra))
          `(define 
              ,label
              ((new-frames ((,@lst-nfvars))))
              (begin
              (set! ,ra ,(current-return-address-register))
                (begin 
                  ,@lst-rlocs
                  ,lst-tail))))]))

  ;; entry -> entry [Listof nfvars]
  ;
  ;; compiles entry by imposing calling conventions on this entry and
  ;; sets up the current return address to fresh aloc
  ;; returns entry statement and list of nfvars defined for this entry block
  (define (impose-calling-conventions-entry entry)
    (begin 
        (define ra (fresh 'tmp-ra))
        (define-values (lst-tail lst-nfvars)
          (impose-calling-conventions-tail entry ra))
        (values
          `(begin
            (set! ,ra ,(current-return-address-register))
            ,lst-tail)
        lst-nfvars)))
  
  ;; pred Return-Address -> pred [Listof nfvars]
  ;;
  ;; takes in pred statement and return address to imposing calling conventions
  ;; returns list of new frame variables and return address used in corresponding block
  (define (impose-calling-conventions-pred pred ra)
    (match pred
      [`(,relop ,opand ,opand_1)
      #:when(relop? relop)
      (values pred '())]
      [`(true)
        (values pred '())]
      [`(false)
        (values pred '())]
      [`(not ,pred)
        (define-values (lst-pred lst-nfvars-pred)
            (impose-calling-conventions-pred pred ra))
        (values `(not ,lst-pred) lst-nfvars-pred)]
      [`(begin ,effects ... ,pred)
        (define-values (lst-effects lst-nfvars-effects)
          (for/fold ([xs '()]
                      [fvs '()])
                    ([s effects])
            (define-values (effect lst-nfvar-effect)
              (impose-calling-conventions-effect s ra))
          (values 
            (cons effect xs)
            (append fvs lst-nfvar-effect))))
        (define-values (lst-pred lst-nfvars)
          (impose-calling-conventions-pred pred ra))
        (values
          `(begin 
            ,@lst-effects
            ,lst-pred)
          (append lst-nfvars-effects lst-nfvars))]
      [`(if ,pred ,pred_1 ,pred_2)
      (define-values (lst-pred lst-nfvars-pred)
            (impose-calling-conventions-pred pred ra))
        (define-values (lst-pred_1 lst-nfvars-pred_1)
            (impose-calling-conventions-pred pred_1 ra))  
        (define-values (lst-pred_2 lst-nfvars-pred_2)
            (impose-calling-conventions-pred pred_2 ra))
      (values
        `(if ,lst-pred          
            ,lst-pred_1
            ,lst-pred_2)
      (append lst-nfvars-pred lst-nfvars-pred_1 lst-nfvars-pred_2))]))
  
  ;; tail Return-Address -> tail [Listof nfvars]
  ;; 
  ;; returns compiled tail statement and [Listof nfvars] that 
  ;; updates tail calls to set the return address register into the current return address
  ;; and list of new frames variables used
  (define (impose-calling-conventions-tail t ra)
    (match t
    [(? value?)  ;; ask about call inside this? which one to default to?
      (define-values (lst-value v)
        (impose-calling-conventions-tail-value t ra))
      (values lst-value '())]
    [`(call ,triv ,opand ...)
      #:when(triv? triv)
      (begin 
        (define-values (reg-set counter) 
          (for/foldr ([new-reg-set '()]
                      [counter 0])
                       ([o opand])
            (if (>= counter (length (current-parameter-registers)))
              (values 
                (cons (make-fvar (- counter (length (current-parameter-registers)))) new-reg-set)
                (add1 counter))
              (values 
                (cons (list-ref (current-parameter-registers) counter) new-reg-set)
                (add1 counter)))))
        (define lst-fvars
          (for/list ([reg (if (> counter (length (current-parameter-registers)))
                              (reverse (drop (reverse reg-set) (length (current-parameter-registers))))
                              '())]
                      [o (if (> counter (length (current-parameter-registers)))
                              (reverse (drop opand (length (current-parameter-registers))))
                              '())])
            `(set! ,reg ,o)))
        (define lst-regs
            (for/list ([reg (if (> counter (length (current-parameter-registers)))
                              (reverse (take (reverse reg-set) (length (current-parameter-registers))))
                              (reverse reg-set))]
                      [o (if (> counter (length (current-parameter-registers)))
                              (reverse (take opand (length (current-parameter-registers))))
                              opand)])
            `(set! ,reg ,o)))
      (values 
        `(begin
            ,@(reverse lst-regs)
            ,@lst-fvars
            (set! ,(current-return-address-register) ,ra)
            (jump ,triv ,(current-frame-base-pointer-register) ,(current-return-address-register) ,@(reverse reg-set)))
        '()))]
    [`(begin ,effects ... ,tail)
      (define-values (lst-effects lst-nfvars-effects)
        (for/fold ([xs '()]
                    [fvs '()])
                  ([s effects])
          (define-values (effect lst-nfvar-effect)
            (impose-calling-conventions-effect s ra))
        (values 
          (cons effect xs)
          (append fvs lst-nfvar-effect))))
      (define-values (lst-tail lst-nfvars)
        (impose-calling-conventions-tail tail ra))
      (values
        `(begin 
          ,@(reverse lst-effects)
          ,lst-tail)
        (append lst-nfvars-effects lst-nfvars))]
    [`(if ,pred ,tail ,tail_1)
    (begin 
      (define-values (lst-pred lst-nfvars-pred)
          (impose-calling-conventions-pred pred ra))
      (define-values (lst-tail lst-nfvars-tail)
          (impose-calling-conventions-tail tail ra))
      (define-values (lst-tail_1 lst-nfvars-tail_1)
          (impose-calling-conventions-tail tail_1 ra))          
      (values
        `(if ,lst-pred
            ,lst-tail
            ,lst-tail_1)
      (append lst-nfvars-pred lst-nfvars-tail lst-nfvars-tail_1)))]))
  
  ;; value return-address -> (values value return-address)
  ;;
  ;; compiles tail value statement by setting return address and returning computation using 
  ;; calling conventions and returns return address and list of new fvars used
  (define (impose-calling-conventions-tail-value v ra)
    (match v
      [(? triv?)
        (values 
            `(begin
                (set! ,(current-return-value-register) ,v)
                (jump ,ra ,(current-frame-base-pointer-register) ,(current-return-value-register)))
        ra)]
      [`(,binop ,opand ,opand_1)
        (values 
        `(begin
            (set! ,(current-return-value-register) ,v)
            (jump ,ra ,(current-frame-base-pointer-register) ,(current-return-value-register)))
        ra)]
      [`(call ,triv ,opand ...)
     (begin 
        (define-values (reg-set counter) 
          (for/foldr ([new-reg-set '()]
                      [counter 0])
                       ([o opand])
            (if (>= counter (length (current-parameter-registers)))
              (values 
                (cons (make-fvar (- counter (length (current-parameter-registers)))) new-reg-set)
                (add1 counter))
              (values 
                (cons (list-ref (current-parameter-registers) counter) new-reg-set)
                (add1 counter)))))
        (define lst-fvars
          (for/list ([reg (if (> counter (length (current-parameter-registers)))
                              (reverse (drop (reverse reg-set) (length (current-parameter-registers))))
                              '())]
                      [o (if (> counter (length (current-parameter-registers)))
                              (reverse (drop opand (length (current-parameter-registers))))
                              '())])
            `(set! ,reg ,o)))
        (define lst-regs
            (for/list ([reg (if (> counter (length (current-parameter-registers)))
                              (reverse (take (reverse reg-set) (length (current-parameter-registers))))
                              (reverse reg-set))]
                      [o (if (> counter (length (current-parameter-registers)))
                              (reverse (take opand (length (current-parameter-registers))))
                              opand)])
            `(set! ,reg ,o)))
      (values 
        `(begin
            ,@(reverse lst-regs)
            ,@lst-fvars
            (set! ,(current-return-address-register) ,ra)
            (jump ,triv ,(current-frame-base-pointer-register) ,(current-return-address-register) ,@(reverse reg-set)))
        (current-return-value-register)))]))

  ;; value return address -> (values value return address [Listof nfvars])
  ;;
  ;; compiles non-tail value statements by imposing calling conventions and returning the updated 
  ;; return address and list of nfvars initialized for this value statement
  (define (impose-calling-conventions-effect-value v aloc ra)
    (match v
      [(? triv?)
      (values `(set! ,aloc ,v) ra '())]
      [`(,binop ,opand ,opand_1)
      (values `(set! ,aloc ,v) ra '())]
      [`(call ,triv ,opand ...)
     (begin 
        (define-values (reg-set counter) 
          (for/foldr ([new-reg-set '()]
                      [counter 0])
                       ([o opand])
            (if (>= counter (length (current-parameter-registers)))
              (values 
                (cons (fresh 'nfvar) new-reg-set)
                (add1 counter))
              (values 
                (cons (list-ref (current-parameter-registers) counter) new-reg-set)
                (add1 counter)))))
        (define lst-nfvars
          (for/list ([reg (if (> counter (length (current-parameter-registers)))
                              (reverse (drop (reverse reg-set) (length (current-parameter-registers))))
                              '())]
                      [o (if (> counter (length (current-parameter-registers)))
                              (reverse (drop opand (length (current-parameter-registers))))
                              '())])
            `(set! ,reg ,o)))
        (define lst-regs
            (for/list ([reg (if (> counter (length (current-parameter-registers)))
                              (reverse (take (reverse reg-set) (length (current-parameter-registers))))
                              (reverse reg-set))]
                      [o (if (> counter (length (current-parameter-registers)))
                              (reverse (take opand (length (current-parameter-registers))))
                              opand)])
            `(set! ,reg ,o)))
        (define rp-label (fresh 'L.rp))
      (values 
        `(return-point ,rp-label
            (begin
              ,@lst-nfvars 
              ,@lst-regs
              (set! ,(current-return-address-register) ,rp-label)
              (jump ,triv ,(current-frame-base-pointer-register) ,(current-return-address-register) ,@(reverse reg-set))))
        (current-return-value-register)
        (if (> counter (length (current-parameter-registers)))
            (reverse (drop (reverse reg-set) (length (current-parameter-registers))))
            '())))]))

  ;; effect Return-Address -> (values effect [Listof nfvars])
  ;;
  ;; compiles effect by imposing calling conventions and returning return list of new frame variables 
  ;; declared in effect statement
  (define (impose-calling-conventions-effect s ra)
    (match s
      [`(set! ,aloc ,value)
        (define-values (val-statement v lst-nfvars)
           (impose-calling-conventions-effect-value value aloc ra))
          (values val-statement lst-nfvars)]
      [`(begin ,effects ... ,effect)
      (define-values (lst-effects lst-nfvars-effects)
        (for/fold ([xs '()]
                    [fvs '()])
                  ([s effects])
          (define-values (effect lst-nfvar-effect)
            (impose-calling-conventions-effect s ra))
        (values 
          (cons effect xs)
          (append lst-nfvar-effect fvs))))
      (define-values (lst-effect lst-nfvars-effect)
          (impose-calling-conventions-effect effect ra))
      (values
        `(begin  
            ,@(reverse lst-effects)
            ,lst-effect)
        (append lst-nfvars-effect lst-nfvars-effects))]
      [`(if ,pred ,effect ,effect_1)
      (define-values (lst-pred lst-nfvars-pred)
          (impose-calling-conventions-pred pred ra))
      (define-values (lst-effect lst-nfvars-effect)
          (impose-calling-conventions-effect effect ra))
      (define-values (lst-effect_1 lst-nfvars-effect_1)
          (impose-calling-conventions-effect effect_1 ra))  
      (values 
       `(if ,lst-pred
            ,lst-effect
            ,lst-effect_1)
        (append lst-nfvars-pred lst-nfvars-effect lst-nfvars-effect_1))]))
  
  ;; binop -> boolean
  ;; returns true if binop is a + or *
  (define (binop? b)
    (or (eq? b '+) 
        (eq? b '*)
        (eq? b '-)))
  
  ;; triv -> boolean
  ;; returns true if triv is an opand? or label?
   (define (triv? triv)
    (or (opand? triv) 
        (label? triv)))
  
  ;; opand -> boolean
  ;; returns true if opand is an int64? or aloc?
   (define (opand? opand)
    (or (int64? opand) 
        (aloc? opand)))

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
  
  ; value -> boolean
  ; returns true if value v is pattern matched to (proc-imp-cmf-lang-v6 value)
  (define (value? v) 
     (match v
      [(? triv?)
      #t]
      [`(,binop ,opand ,opand_1)
      #:when(and (binop? binop)
                  (opand? opand)
                  (opand? opand_1))
      #t]
      [`(call ,triv ,opand ...)
      #:when(and (triv? triv) 
                (andmap opand? opand))
      #t]
      [_ #f]))

  (impose-calling-conventions-p p))

(module+ test 
  (require
  rackunit
   rackunit/text-ui
   cpsc411/langs/v6
   cpsc411/test-suite/public/v6
   cpsc411/test-suite/utils)

; if pred pred pred
; begin effect ... pred
(define ic-v6-1
  '(module 
    (begin 
      (if (if (begin (set! x.6 2) (set! x.5 1) (< x.5 x.6)) 
              (< x.5 5) 
              (< x.6 10)) 
          (set! x.4 x.5) 
          (set! x.4 x.6))
    2)))
(define ic-v6-1-compiled
'(module
  ((new-frames ()))
  (begin
    (set! tmp-ra.1 r15)
    (begin
      (if (if (begin (set! x.6 2) (set! x.5 1) (< x.5 x.6))
            (< x.5 5)
            (< x.6 10))
        (set! x.4 x.5)
        (set! x.4 x.6))
      (begin (set! rax 2) (jump tmp-ra.1 rbp rax))))))
(check-equal?
  (interp-imp-cmf-lang-v6 (impose-calling-conventions ic-v6-1))
  (interp-imp-cmf-lang-v6 ic-v6-1-compiled))

; if pred effect effect
; false
; not pred
(define ic-v6-18
  '(module 
    (begin 
      (set! x.6 2) 
      (set! x.5 1) 
      (begin 
        (if (not (false)) (set! x.4 x.5) (set! x.4 x.6))
        (begin 
          (set! x.4 2) 
          (set! x.6 x.4)) 2))))
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
(check-equal?
  (interp-imp-cmf-lang-v6 (impose-calling-conventions ic-v6-18))
  (interp-imp-cmf-lang-v6 ic-v6-18-compiled))

(define ic-v6-9-compiled 
'(module
  ((new-frames ()))
  (begin
    (set! tmp-ra.1 r15)
    (begin
      (set! tmp.89 1)
      (begin (set! rax (+ tmp.89 tmp.89)) (jump tmp-ra.1 rbp rax))))))

(define ic-v6-9 '(module (begin (set! tmp.89 1) (+ tmp.89 tmp.89))))
;(impose-calling-conventions ic-v6-9)
(check-equal?
  (interp-imp-cmf-lang-v6 (impose-calling-conventions ic-v6-9))
  (interp-imp-cmf-lang-v6 ic-v6-9-compiled))

(define ic-v6-8-compiled 
'(module
  ((new-frames ()))
  (begin
    (set! tmp-ra.1 r15)
    (begin (set! foo.1 1) (begin (set! rax foo.1) (jump tmp-ra.1 rbp rax))))))
(define ic-v6-8 '(module (begin (set! foo.1 1) foo.1)))
;(impose-calling-conventions ic-v6-8)
;(check-equal? (impose-calling-conventions ic-v6-8) ic-v6-8-compiled)
;; temp variables failing
(check-equal?
  (interp-imp-cmf-lang-v6 (impose-calling-conventions ic-v6-8))
  (interp-imp-cmf-lang-v6 ic-v6-8-compiled))

(define ic-v6-7-compiled 
'(module
  ((new-frames ()))
  (begin
    (set! tmp-ra.1 r15)
    (begin (set! x.1 1) (begin (set! rax x.1) (jump tmp-ra.1 rbp rax))))))

(define ic-v6-7
  '(module (begin (set! x.1 1) x.1)))

;(impose-calling-conventions ic-v6-7)
; temp variables
;(check-equal? (impose-calling-conventions ic-v6-7) ic-v6-7-compiled)
(check-equal?
  (interp-imp-cmf-lang-v6 (impose-calling-conventions ic-v6-7))
  (interp-imp-cmf-lang-v6 ic-v6-7-compiled))

(define ic-v6-6-compiled 
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

; begin effect effect
(define ic-v6-6
  '(module 
    (begin 
      (set! x.6 2) 
      (set! x.5 1) 
      (begin 
        (set! x.4 x.5) 
        (begin 
          (set! x.4 2) 
          (set! x.6 x.4)) 2))))
;(impose-calling-conventions ic-v6-6)
;(check-equal? (impose-calling-conventions ic-v6-6) ic-v6-6-compiled)
;; TODO: failing due to temp variables
(check-equal?
  (interp-imp-cmf-lang-v6 (impose-calling-conventions ic-v6-6))
  (interp-imp-cmf-lang-v6 ic-v6-6-compiled))

(define ic-v6-5-compiled 
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

(define ic-v6-5
  '(module 
    (begin 
      (set! tmp.100 1) 
          (begin 
            (set! tmp.101 (+ 1 tmp.100)) 
            (set! tmp.102 (+ 2 tmp.100)) 
            (+ tmp.101 tmp.102)))))
;(check-equal? (impose-calling-conventions ic-v6-5) ic-v6-5-compiled)
;; TODO: failing due to temp variables
(check-equal?
  (interp-imp-cmf-lang-v6 (impose-calling-conventions ic-v6-5))
  (interp-imp-cmf-lang-v6 ic-v6-5-compiled))

(define ic-v6-4-compiled 
'(module
  ((new-frames ()))
  (begin 
    (set! tmp-ra.1 r15) 
    (begin 
      (set! rax 5) 
     (jump tmp-ra.1 rbp rax)))))
(define ic-v6-4
  '(module 5))
;(impose-calling-conventions ic-v6-4)
;(check-equal? (impose-calling-conventions ic-v6-4) ic-v6-4-compiled)
;; TODO: failing due to temp vaibales
(check-equal?
  (interp-imp-cmf-lang-v6 (impose-calling-conventions ic-v6-4))
  (interp-imp-cmf-lang-v6 ic-v6-4-compiled))

(define ic-v6-3 
'(module 
  (begin 
    (set! y.4 5) 
    (set! x.3 (+ 1 2)) 
    (set! z.5 2) 
    (set! x.3 (+ x.3 y.4)) 
    (set! x.3 (+ y.4 z.5)) 
    (set! x.3 x.3) x.3)))

(define ic-v6-3-compiled 
'(module
  ((new-frames ()))
  (begin
    (set! tmp-ra.1 r15)
    (begin
      (set! y.4 5)
      (set! x.3 (+ 1 2))
      (set! z.5 2)
      (set! x.3 (+ x.3 y.4))
      (set! x.3 (+ y.4 z.5))
      (set! x.3 x.3)
      (begin (set! rax x.3) (jump tmp-ra.1 rbp rax))))))
;(impose-calling-conventions ic-v6-3)
;(check-equal? (impose-calling-conventions ic-v6-3) ic-v6-3-compiled)
;; TODO: failing due to temp variables
(check-equal?
  (interp-imp-cmf-lang-v6 (impose-calling-conventions ic-v6-3))
  (interp-imp-cmf-lang-v6 ic-v6-3-compiled))

(define ic-v6-2 
'(module
  (define L.swap.1
    (lambda (x.1 y.2 x.3)
      (if (< y.2 x.1)
        (+ x.1 4)
        (begin 
          (set! z.3 3)
          (set! z.4 (+ x.1 4))
          z.3))))
  (call L.swap.1 1 2)))
(define ic-v6-2-compiled 
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
        (if (< y.2 x.1)
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

;(impose-calling-conventions ic-v6-2)
;(check-equal? (impose-calling-conventions ic-v6-2) ic-v6-2-compiled)
;; TODO: failing due to temp variables
(check-equal?
  (interp-imp-cmf-lang-v6 (impose-calling-conventions ic-v6-2))
  (interp-imp-cmf-lang-v6 ic-v6-2-compiled))

(define ic-v6-11
'(module 
  (begin (set! y.4 5) 
    (set! x.3 (+ 1 2)) 
    (set! z.5 2) 
    (set! x.3 (+ x.3 y.4)) 
    (set! x.3 (+ y.4 z.5)) 
    (set! x.3 x.3) 
  x.3)))
(define ic-v6-11-compiled 
'(module
  ((new-frames ()))
  (begin
    (set! tmp-ra.1 r15)
    (begin
      (set! y.4 5)
      (set! x.3 (+ 1 2))
      (set! z.5 2)
      (set! x.3 (+ x.3 y.4))
      (set! x.3 (+ y.4 z.5))
      (set! x.3 x.3)
      (begin (set! rax x.3) (jump tmp-ra.1 rbp rax))))))
(check-equal?
(interp-imp-cmf-lang-v6 ic-v6-11-compiled)
(interp-imp-cmf-lang-v6 (impose-calling-conventions ic-v6-11)))
;(check-equal? (impose-calling-conventions ic-v6-11) ic-v6-11-compiled)

(define ic-12
'(module (+ 1 2)))
(define ic-12-compiled 
'(module
  ((new-frames ()))
  (begin
    (set! tmp-ra.1 r15)
    (begin (set! rax (+ 1 2)) (jump tmp-ra.1 rbp rax)))))
;(impose-calling-conventions ic-12)
(check-equal?
(interp-imp-cmf-lang-v6 ic-12-compiled)
(interp-imp-cmf-lang-v6 (impose-calling-conventions ic-12)))
;(check-equal? (impose-calling-conventions ic-12) ic-12-compiled)
; TODO: failing due to temp

; if pred tail tail
; relop opand opand
(define ic-v6-10
'(module 
  (define L.start.1
    (lambda (x.1 x.2 x.3 x.4 x.5 x.6 x.7)
    (call x.1 10 2 1 2 34 5 6 8)))
  (if( > 10 2)
      20
      1)))
(define ic-v6-10-compiled 
'(module
  ((new-frames ()))
  (define L.start.1
    ((new-frames ()))
    (begin
      (set! tmp-ra.1 r15)
      (begin
        (set! x.1 rdi)
        (set! x.2 rsi)
        (set! x.3 rdx)
        (set! x.4 rcx)
        (set! x.5 r8)
        (set! x.6 r9)
        (set! x.7 fv0)
        (begin
          (set! fv1 8)
          (set! fv0 6)
          (set! r9 5)
          (set! r8 34)
          (set! rcx 2)
          (set! rdx 1)
          (set! rsi 2)
          (set! rdi 10)
          (set! r15 tmp-ra.1)
          (jump x.1 rbp r15 rdi rsi rdx rcx r8 r9 fv0 fv1)))))
  (begin
    (set! tmp-ra.2 r15)
    (if (> 10 2)
      (begin (set! rax 20) (jump tmp-ra.2 rbp rax))
      (begin (set! rax 1) (jump tmp-ra.2 rbp rax))))))
;(impose-calling-conventions ic-v6-10) ;; TODO: why dont we have new-fvars?
(check-equal?
(interp-imp-cmf-lang-v6 ic-v6-10-compiled)
(interp-imp-cmf-lang-v6 (impose-calling-conventions ic-v6-10)))
;(check-equal?(impose-calling-conventions ic-v6-10) ic-v6-10-compiled)

; call triv opand
(define ic-v6-12 
'(module 
  (define L.start.1
    (lambda (x.1 x.2)
    (call x.1 10 20)))
  10))
(define ic-v6-12-compiled 
'(module
  ((new-frames ()))
  (define L.start.1
    ((new-frames ()))
    (begin
      (set! tmp-ra.1 r15)
      (begin
        (set! x.1 rdi)
        (set! x.2 rsi)
        (begin
          (set! rsi 20)
          (set! rdi 10)
          (set! r15 tmp-ra.1)
          (jump x.1 rbp r15 rdi rsi)))))
  (begin (set! tmp-ra.2 r15) (begin (set! rax 10) (jump tmp-ra.2 rbp rax)))))
;(check-equal? (impose-calling-conventions ic-v6-12) ic-v6-12-compiled)
; TODO: failing due to temp variables
(check-equal?
(interp-imp-cmf-lang-v6 ic-v6-12-compiled)
(interp-imp-cmf-lang-v6 (impose-calling-conventions ic-v6-12)))

; nested-p
; triv
  (define ic-v6-13 
'(module 
  (define L.start.1
    (lambda (x.1 x.2)
    (begin 
      (set! x.1 10)
      (set! x.2 5)
      (+ x.1 x.2))))
  10))
  (define ic-v6-13-compiled
  '(module
  ((new-frames ()))
  (define L.start.1
    ((new-frames ()))
    (begin
      (set! tmp-ra.1 r15)
      (begin
        (set! x.1 rdi)
        (set! x.2 rsi)
        (begin
          (set! x.1 10)
          (set! x.2 5)
          (begin (set! rax (+ x.1 x.2)) (jump tmp-ra.1 rbp rax))))))
  (begin (set! tmp-ra.2 r15) (begin (set! rax 10) (jump tmp-ra.2 rbp rax)))))
;(check-equal? (impose-calling-conventions ic-v6-13) ic-v6-13-compiled)
; TODO: failing due to temp variables
(check-equal?
(interp-imp-cmf-lang-v6 ic-v6-13-compiled)
(interp-imp-cmf-lang-v6 (impose-calling-conventions ic-v6-13)))

; begin effect tail
; (set! aloc value)
; (binop opand opand)
(define ic-v6-14
'(module (begin (set! x.1 (+ 4 10)) (+ x.1 5))))
(define ic-v6-14-compiled
'(module
  ((new-frames ()))
  (begin
    (set! tmp-ra.1 r15)
    (begin
      (set! x.1 (+ 4 10))
      (begin (set! rax (+ x.1 5)) (jump tmp-ra.1 rbp rax))))))
;(check-equal? (impose-calling-conventions ic-v6-14) ic-v6-14-compiled)
; TODO: failing due to temp variables
(check-equal?
(interp-imp-cmf-lang-v6 ic-v6-14-compiled)
(interp-imp-cmf-lang-v6 (impose-calling-conventions ic-v6-14)))

(define ic-v6-15 
'(module 
  (begin (set! y.4 5) 
    (set! x.3 (+ 1 2)) 
    (set! z.5 2) 
    (set! x.3 (+ x.3 y.4)) 
    (set! x.3 (+ y.4 z.5)) 
    (set! x.3 x.3) x.3))) ;7
(define ic-v6-15-compiled
'(module
  ((new-frames ()))
  (begin
    (set! tmp-ra.1 r15)
    (begin
      (set! y.4 5)
      (set! x.3 (+ 1 2))
      (set! z.5 2)
      (set! x.3 (+ x.3 y.4))
      (set! x.3 (+ y.4 z.5))
      (set! x.3 x.3)
      (begin (set! rax x.3) (jump tmp-ra.1 rbp rax))))))
;(check-equal? (impose-calling-conventions ic-v6-15) ic-v6-15-compiled)
; TODO; failing due to temp variables
(check-equal?
(interp-imp-cmf-lang-v6 ic-v6-15-compiled)
(interp-imp-cmf-lang-v6 (impose-calling-conventions ic-v6-15)))

(define ic-v6-16 
'(module (begin (set! x.1 5) 
  (if (true) 
    (begin (set! y.2 (+ x.1 17)) (set! x.5 12)) 
    (begin (set! x.5 15))) x.5))) ;12
(define ic-v6-16-compiled 
'(module
  ((new-frames ()))
  (begin
    (set! tmp-ra.1 r15)
    (begin
      (set! x.1 5)
      (if (true)
        (begin (set! y.2 (+ x.1 17)) (set! x.5 12))
        (begin (set! x.5 15)))
      (begin (set! rax x.5) (jump tmp-ra.1 rbp rax))))))
#;(check-equal?
  (impose-calling-conventions ic-v6-16) ic-v6-16-compiled)
(check-equal?
(interp-imp-cmf-lang-v6 ic-v6-16-compiled)
(interp-imp-cmf-lang-v6 (impose-calling-conventions ic-v6-16)))

(define ic-v6-17 
'(module (begin (set! x.1 (+ 4 10)) (+ x.1 5)))) 
(define ic-v6-17-compiled 
'(module
  ((new-frames ()))
  (begin
    (set! tmp-ra.1 r15)
    (begin
      (set! x.1 (+ 4 10))
      (begin (set! rax (+ x.1 5)) (jump tmp-ra.1 rbp rax))))))
(check-equal?
(interp-imp-cmf-lang-v6 ic-v6-17-compiled)
(interp-imp-cmf-lang-v6 (impose-calling-conventions ic-v6-17)))

(run-tests
   (test-suite
    ""
    (test-compiler-pass impose-calling-conventions interp-proc-imp-cmf-lang-v6 interp-imp-cmf-lang-v6 imp-cmf-lang-v6?))))



