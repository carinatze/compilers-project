#lang racket

(provide allocate-frames)

(require
 cpsc411/compiler-lib
 cpsc411/2c-run-time
 cpsc411/langs/v6
 cpsc411/graph-lib
 racket/trace
 rackunit)

 #| asm-pred-lang-v6/pre-framed 
   p	 	::=	 	(module info (define label info tail) ... tail) 	 	 
  info	 	::=	 	(#:from-contract (info/c (new-frames (frame ...)) (locals (aloc ...)) (call-undead (loc ...)) (conflicts ((loc (loc ...)) ...)) (assignment ((aloc fvar) ...))))	 	 
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
  aloc	 	::=	 	aloc?	 	 
  label	 	::=	 	label?	 	 
  rloc	 	::=	 	register?
 	 	|	 	fvar?	 	 
  fvar	 	::=	 	fvar?	 	 
  int64	 	::=	 	int64?
|#

;; Exercise 11
;; allocates frames for each non-tail call, and assigns all new-frame variables to frame variables in the new frame
;; by compiling Asm-pred-lang-v6/pre-framed to Asm-pred-lang-v6/framed 
(define (allocate-frames p)
  (define (allocate-frames-p p)
    (match p
      [`(module ,info ,nested ... ,tail) 	 	 
      (begin
        (define-values (t _)
          (allocate-frames-tail tail (info-ref info 'assignment) 0))
        (define-values (local-lst nfvar-lst)
          (allocate-frames-frame (info-ref info 'locals) (info-ref info 'assignment)))
      `(module
        ((locals ,local-lst)
          (conflicts ,(info-ref info 'conflicts))
          (assignment ,nfvar-lst))
          ,@(map allocate-frames-nested nested)
          ,t))]))

  ;; asm-pred-lang-v6/pre-framed nested-p -> asm-pred-lang-v6/framed nested-p
  ;; nested-p ::= (define label info tail)
  ;; allocates frames for each non-tail call, and assigns all new-frame variables to frame variables in the new frame
  (define (allocate-frames-nested p)
    (match p
      [`(define ,label ,info ,tail) 
      (begin
       (define-values (t _)
          (allocate-frames-tail tail (info-ref info 'assignment) 0))
         (define-values (local-lst nfvar-lst)
          (allocate-frames-frame (info-ref info 'locals) (info-ref info 'assignment)))	 	 
        `(define
          ,label
          ((locals ,local-lst)
            (conflicts ,(info-ref info 'conflicts))
            (assignment ,nfvar-lst))
            ,t))]))

  ;; [Listof (aloc)] [Listof (aloc fvar)] -> [Listof (aloc)] [Listof (aloc fvar)]
  ;; compiles Asm-pred-lang-v6/pre-framed frame to Asm-pred-lang-v6/framed frame by:
  ;; removes nfvars from locals field in enclosing block
  ;; assigns and adds a frame variable to each new-frame variable using (make-fvar) into the assignment field in enclosing block
  (define (allocate-frames-frame f nf)
    (define i 
      (if (equal? (length nf) 0)
        0
        (add1 (fvar->index (list-ref (last nf) 1)))))
    (define-values (lst-locals lst-nfvars _)
      (for/foldr ([locals '()]
                  [nfvars nf]
                  [counter i])
                ([aloc f])
      (if (string-prefix? (symbol->string aloc) "nfv")
        (values 
          locals 
          (cons (list aloc (make-fvar counter)) nfvars) 
          (add1 counter))
        (values 
          (cons aloc locals) 
          nfvars 
          counter))))
    (values 
      (reverse lst-locals)
      (reverse lst-nfvars)))

  ;; (Asm-pred-lang-v6/pre-framed pred) [ListOf (aloc fvar)] integer -> (Asm-pred-lang-v6/framed pred) integer
  ;; Takes in pred statement, list of assignments, and current index to keep track of the current assigned fvar used to calculate nb in the enclosed block
  ;; returns the compiled tail and the new index of the current fvar
  (define (allocate-frames-pred pred acc i)
    (match pred
      [`(,relop ,loc ,opand)
      #:when(and (relop? relop) (opand? opand))
        (values pred i)]
      [`(true)
        (values pred i)]
      [`(false)
        (values pred i)]
      [`(not ,pred) 
        (define-values (pred-statement pred-counter)
           (allocate-frames-pred pred acc i))
        (values `(not ,pred-statement) pred-counter)]
       [`(begin ,effect ... ,pred)
        (begin 
          (define-values (effects effects-counter)
            (for/foldr ([lst-effects '()] ; list of effects
                        [counter i]) ; counter of fv
                          ([e effect]) ; iterate each effect
                (define-values (e-statement e-count) 
                  (allocate-frames-effect e acc counter))
            (values 
              (cons e-statement lst-effects)
              e-count)))
          (define-values (p pred-counter)
              (allocate-frames-pred pred acc effects-counter))
        (values 
          `(begin ,@(reverse effects) ,p) ;statements
          pred-counter))] ; counter
      [`(if ,pred ,pred_1 ,pred_2)
       (define-values (p pred-count) 
              (allocate-frames-pred pred acc i))
      (define-values (p1 pred1-count) 
              (allocate-frames-pred pred_1 acc pred-count))
      (define-values (p2 pred2-count) 
              (allocate-frames-pred pred_2 acc pred1-count))
      (values 
        `(if ,p ,p1 ,p2)
        pred2-count)]))
  
  ;; (Asm-pred-lang-v6/pre-framed tail) [ListOf (aloc fvar)] integer -> (Asm-pred-lang-v6/framed tail) integer
  ;; Takes in tail statement, list of assignments and current index to keep track of the current assigned fvar used to calculate nb in the enclosed block
  ;; returns tail and current index of the fvar in the assignment of the enclosed block
  (define (allocate-frames-tail t acc i) 
    (match t
      [`(jump ,trg ,loc ...) 
      (values t i)]
      [`(begin ,effect ... ,tail) 
        (begin 
          (define-values (effects effects-counter)
            (for/foldr ([lst-effects '()] ; list of effects
                        [counter i]) ; counter of fv
                        ([e effect]) ; iterate each effect
                (define-values (e-statement e-count) 
                  (allocate-frames-effect e acc counter))
            (values 
              (cons e-statement lst-effects)
              e-count)))
          (define-values (tail-statement tail-counter)
              (allocate-frames-tail tail acc effects-counter))
        (values 
          `(begin 
            ,@effects
            ,tail-statement)
          tail-counter))]
      [`(if ,pred ,tail ,tail_1) 
        (define-values (p pred-count) 
                (allocate-frames-pred pred acc i))
        (define-values (tail-statement tail-count) 
                (allocate-frames-tail tail acc pred-count))
        (define-values (tail_1-statement tail_1-count) 
                (allocate-frames-tail tail_1 acc tail-count))
        (values
          `(if ,p 
              ,tail-statement
              ,tail_1-statement)
          tail_1-count)]))
    
  ;; Asm-pred-lang-v6/pre-framed effect [ListOf (aloc fvar)] integer -> Asm-pred-lang-v6/framed effect
  ;; takes in effect statement, list of assignments, and current index 
  ;; compiles (Asm-pred-lang-v6/pre-framed effect) to (Asm-pred-lang-v6/pre-framed effect) by allocating caller's frame
  ;; transforms return-point statements with allocating number of bytes required to save n slots on the frame
  ;; returns tail and updated index of the fvar in the assignment of the enclosed block
  (define (allocate-frames-effect e acc i) 
    (match e
      [`(set! ,loc_1 (,binop ,loc_1 ,opand)) 
        (values e i)]
      [`(set! ,loc ,triv)  
      #:when(triv? triv)
      (values e i)]
      [`(begin ,xs ... ,x)
      (begin 
          (define-values (effects effects-counter)
            (for/foldr ([lst-effects '()] ; list of effects
                        [counter i]) ; counter of fv
                          ([e xs]) ; iterate each effect
                (define-values (e-statement e-count) 
                  (allocate-frames-effect e acc counter))
            (values 
              (cons e-statement lst-effects)
              e-count)))
          (define-values (effect-statement effect-counter)
              (allocate-frames-effect x acc effects-counter))
        (values 
          `(begin 
            ,@effects
            ,effect-statement)
          effect-counter))]
      [`(if ,pred ,effect ,effect_1) 
      (define-values (p pred-count) 
              (allocate-frames-pred pred acc i))
       (define-values (effect-statement effect-count) 
                (allocate-frames-effect effect acc pred-count))
        (define-values (effect_1-statement effect_1-count) 
                (allocate-frames-effect effect_1 acc effect-count))
      (values 
        `(if ,p 
            ,effect-statement  
            ,effect_1-statement)
        effect_1-count)]
      [`(return-point ,label ,tail)
      #:when(label? label)
      (begin
        (define nb
            (* (add1 (fvar->index (list-ref (list-ref acc i) 1))) 
                (current-word-size-bytes)))
        (values 
        `(begin 
          (set! ,(current-frame-base-pointer-register) (- ,(current-frame-base-pointer-register) ,nb))
          ,e
          (set! ,(current-frame-base-pointer-register) (+ ,(current-frame-base-pointer-register) ,nb)))
        (add1 i)))]))
  
  ;; binop -> x64 string
  ;; translates binop symbols into the string format of the binary operations
  (define (binop? binop)
      (or (eq? binop '*)
         (eq? binop '+)
         (eq? binop '-)))

  ;; trg -> boolean
  ;; returns true if trg trg is a trg?
  (define (trg? trg)
    (or (label? trg) (loc? trg)))

  ;; triv -> boolean
  ;; returns true if triv t is a triv?
  (define (triv? triv)
    (or (opand? triv) (label? triv)))
  
  ;; opand -> boolean
  ;; returns true if opand t is a opand?
  (define (opand? opand)
    (or (int64? opand) (loc? opand)))

  ;; loc -> boolean
  ;; returns true if loc loc is a loc?
  (define (loc? loc)
    (or  (register? loc) 
          (fvar? loc)
          (aloc? loc)))
  
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

(allocate-frames-p p))

(module+ test 
  (require
  rackunit
   rackunit/text-ui
   cpsc411/langs/v6
   cpsc411/test-suite/public/v6
   cpsc411/test-suite/utils)

(define af-5 
'(module
  ((new-frames ())
   (locals (tmp-ra.1 x.6 x.5 x.4))
   (call-undead ())
   (undead-out
    ((tmp-ra.1 rbp)
     (x.6 tmp-ra.1 rbp)
     (x.6 tmp-ra.1 rbp)
     (((tmp-ra.1 rbp) (tmp-ra.1 rbp) (tmp-ra.1 rbp))
      (tmp-ra.1 rbp)
      (tmp-ra.1 rbp))
     (x.4 tmp-ra.1 rbp)
     (tmp-ra.1 rbp)
     (tmp-ra.1 rax rbp)
     (rax rbp)))
   (conflicts
    ((tmp-ra.1 (rax x.4 x.5 x.6 rbp))
     (x.6 (x.5 rbp tmp-ra.1))
     (x.5 (rbp tmp-ra.1 x.6))
     (x.4 (rbp tmp-ra.1))
     (rbp (rax x.4 x.5 x.6 tmp-ra.1))
     (rax (rbp tmp-ra.1))))
   (assignment ()))
  (begin
    (set! tmp-ra.1 r15)
    (set! x.6 2)
    (set! x.5 1)
    (if (if (< x.6 1) (true) (false)) (set! x.6 8) (set! x.6 10))
    (set! x.4 2)
    (set! x.6 x.4)
    (set! rax 2)
    (jump tmp-ra.1 rbp rax))))

(define af-5-compiled 
'(module
  ((locals (x.4 x.5 x.6 tmp-ra.1))
   (conflicts
    ((tmp-ra.1 (rax x.4 x.5 x.6 rbp))
     (x.6 (x.5 rbp tmp-ra.1))
     (x.5 (rbp tmp-ra.1 x.6))
     (x.4 (rbp tmp-ra.1))
     (rbp (rax x.4 x.5 x.6 tmp-ra.1))
     (rax (rbp tmp-ra.1))))
   (assignment ()))
  (begin
    (set! tmp-ra.1 r15)
    (set! x.6 2)
    (set! x.5 1)
    (if (if (< x.6 1) (true) (false)) (set! x.6 8) (set! x.6 10))
    (set! x.4 2)
    (set! x.6 x.4)
    (set! rax 2)
    (jump tmp-ra.1 rbp rax))))

(check-equal? (allocate-frames af-5) af-5-compiled)
(check-equal? 
  (interp-asm-pred-lang-v6/framed (allocate-frames af-5))
  (interp-asm-pred-lang-v6/framed af-5-compiled)) 

(define af-4 
'(module
  ((new-frames ())
   (locals (tmp-ra.37 tmp.42))
   (call-undead ())
   (undead-out
    ((tmp-ra.37 rbp)
     (((tmp.42 tmp-ra.37 rbp) (tmp-ra.37 rbp))
      ((tmp-ra.37 rax rbp) (rax rbp))
      ((rax tmp-ra.37 rbp) (tmp-ra.37 rax rbp) (rax rbp)))))
   (conflicts
    ((tmp-ra.37 (rbp tmp.42 rax))
     (tmp.42 (rbp tmp-ra.37))
     (rax (rbp tmp-ra.37))
     (rbp (tmp-ra.37 tmp.42 rax))))
   (assignment ()))
  (begin
    (set! tmp-ra.37 r15)
    (if (begin (set! tmp.42 0) (> tmp.42 1))
      (begin (set! rax 0) (jump tmp-ra.37 rbp rax))
      (begin 
        (set! rax 0) 
        (set! rax (+ rax 1)) 
        (jump tmp-ra.37 rbp rax))))))
(asm-pred-lang-v6/pre-framed? af-4)
(interp-asm-pred-lang-v6/pre-framed af-4)

(define af-4-compiled 
'(module
  ((locals (tmp.42 tmp-ra.37))
   (conflicts
    ((tmp-ra.37 (rbp tmp.42 rax))
     (tmp.42 (rbp tmp-ra.37))
     (rax (rbp tmp-ra.37))
     (rbp (tmp-ra.37 tmp.42 rax))))
   (assignment ()))
  (begin
    (set! tmp-ra.37 r15)
    (if (begin (set! tmp.42 0) (> tmp.42 1))
      (begin (set! rax 0) (jump tmp-ra.37 rbp rax))
      (begin (set! rax 0) (set! rax (+ rax 1)) (jump tmp-ra.37 rbp rax))))))
(allocate-frames af-4)
(check-equal? (allocate-frames af-4) af-4-compiled)
(check-equal? 
  (interp-asm-pred-lang-v6/framed (allocate-frames af-4))
  (interp-asm-pred-lang-v6/framed af-4-compiled)) 

; set loc (binop loc opand)
; jump trg (no loc)
(define af-3 
'(module
  ((new-frames (()))
   (locals (x.1 y.1 w.1))
   (call-undead ())
   (undead-out
    ((x.1 r15)
     (x.1 w.1 r15)
     (x.1 w.1 y.1 r15)
     (y.1 w.1 r15)
     (w.1 r15)
     ((r15) ())))
   (conflicts
    ((x.1 (w.1 r15))
     (y.1 (r15 w.1))
     (w.1 (y.1 r15 x.1))
     (rax (r15))
     (r15 (y.1 w.1 x.1 rax))))
   (assignment ()))
  (begin
    (set! x.1 0)
    (set! w.1 0)
    (set! y.1 x.1)
    (set! w.1 (+ w.1 x.1))
    (set! w.1 (- w.1 y.1))
    (begin (set! rax w.1) (jump r15)))))

(define af-3-compiled 
'(module
  ((locals (w.1 y.1 x.1))
   (conflicts
    ((x.1 (w.1 r15))
     (y.1 (r15 w.1))
     (w.1 (y.1 r15 x.1))
     (rax (r15))
     (r15 (y.1 w.1 x.1 rax))))
   (assignment ()))
  (begin
    (set! x.1 0)
    (set! w.1 0)
    (set! y.1 x.1)
    (set! w.1 (+ w.1 x.1))
    (set! w.1 (- w.1 y.1))
    (begin (set! rax w.1) (jump r15)))))

(check-equal? (allocate-frames af-3) af-3-compiled)
(check-equal? 
  (interp-asm-pred-lang-v6/framed (allocate-frames af-3))
  (interp-asm-pred-lang-v6/framed af-3-compiled))

;; no nested p test
(define af-2 
'(module
  ((new-frames (()))
   (locals ())
   (call-undead ())
   (undead-out ((r15) ()))
   (conflicts ((rax (r15)) (r15 (rax))))
   (assignment ()))
  (begin (set! rax 5) (jump r15))))

(define af-2-compiled 
'(module
  ((locals ()) (conflicts ((rax (r15)) (r15 (rax)))) (assignment ()))
  (begin (set! rax 5) (jump r15))))
(allocate-frames af-2) 
(check-equal? (allocate-frames af-2) af-2-compiled)
(check-equal? 
  (interp-asm-pred-lang-v6/framed (allocate-frames af-2))
  (interp-asm-pred-lang-v6/framed af-2-compiled))

;; nested p test
;; if pred tail tail
;; relop loc opand
;; begin effect tail
;; return-point 
;; jump trg loc
(define af-1
'(module
  ((new-frames ())
   (locals (tmp-ra.4))
   (call-undead ())
   (undead-out
    ((tmp-ra.4 rbp)
     (tmp-ra.4 fv1 rbp)
     (tmp-ra.4 fv1 fv0 rbp)
     (fv1 fv0 r15 rbp)
     (fv1 fv0 r15 rbp)))
   (conflicts
    ((tmp-ra.4 (fv0 fv1 rbp))
     (rbp (r15 fv0 fv1 tmp-ra.4))
     (fv1 (r15 fv0 rbp tmp-ra.4))
     (fv0 (r15 rbp fv1 tmp-ra.4))
     (r15 (rbp fv0 fv1))))
   (assignment ()))
  (define L.swap.1
    ((new-frames ((nfv.2 nfv.3)))
     (locals (y.2 x.1 z.3 nfv.3 nfv.2))
     (undead-out
      ((fv0 fv1 tmp-ra.1 rbp)
       (fv1 x.1 tmp-ra.1 rbp)
       (y.2 x.1 tmp-ra.1 rbp)
       ((y.2 x.1 tmp-ra.1 rbp)
        ((tmp-ra.1 rax rbp) (rax rbp))
        (((rax tmp-ra.1 rbp)
          ((y.2 nfv.3 rbp)
           (nfv.3 nfv.2 rbp)
           (nfv.3 nfv.2 r15 rbp)
           (nfv.3 nfv.2 r15 rbp)))
         (z.3 tmp-ra.1 rbp)
         (tmp-ra.1 rax rbp)
         (rax rbp)))))
     (call-undead (tmp-ra.1))
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
     (assignment ((tmp-ra.1 fv2))))
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

(define af-1-compiled 
'(module
  ((locals (tmp-ra.4))
   (conflicts
    ((tmp-ra.4 (fv0 fv1 rbp))
     (rbp (r15 fv0 fv1 tmp-ra.4))
     (fv1 (r15 fv0 rbp tmp-ra.4))
     (fv0 (r15 rbp fv1 tmp-ra.4))
     (r15 (rbp fv0 fv1))))
   (assignment ()))
  (define L.swap.1
    ((locals (z.3 x.1 y.2))
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
     (assignment ((tmp-ra.1 fv2) (nfv.2 fv3) (nfv.3 fv4))))
    (begin
      (set! tmp-ra.1 r15)
      (set! x.1 fv0)
      (set! y.2 fv1)
      (if (< y.2 x.1)
        (begin (set! rax x.1) (jump tmp-ra.1 rbp rax))
        (begin
          (begin
            (set! rbp (- rbp 24))
            (return-point L.rp.1
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
    
(check-equal? (allocate-frames af-1) af-1-compiled)
(check-equal? 
  (interp-asm-pred-lang-v6/framed (allocate-frames af-1))
  (interp-asm-pred-lang-v6/framed af-1-compiled))

(define af-6-compiled 
'(module
  ((locals (tmp-ra.75))
   (conflicts
    ((tmp-ra.75 (rax rbp)) (rbp (rax tmp-ra.75)) (rax (rbp tmp-ra.75))))
   (assignment ()))
  (begin
    (set! tmp-ra.75 r15)
    (set! rax 1)
    (if (not (true)) (set! rax 2) (set! rax 3))
    (set! rax (+ rax 2))
    (jump tmp-ra.75 rbp rax))))

; not pred
; if pred effect effect
(define af-6 
'(module
  ((new-frames ())
   (locals (tmp-ra.75))
   (call-undead ())
   (undead-out
    ((tmp-ra.75 rbp)
     (tmp-ra.75 rbp)
     ((tmp-ra.75 rbp) (rax tmp-ra.75 rbp) (rax tmp-ra.75 rbp))
     (tmp-ra.75 rax rbp)
     (rax rbp)))
   (conflicts
    ((tmp-ra.75 (rax rbp)) (rbp (rax tmp-ra.75)) (rax (rbp tmp-ra.75))))
   (assignment ()))
  (begin
    (set! tmp-ra.75 r15)
    (set! rax 1)
    (if (not (true)) 
      (set! rax 2) 
      (set! rax 3))
    (set! rax (+ rax 2))
    (jump tmp-ra.75 rbp rax))))

(check-equal? (allocate-frames af-6) af-6-compiled)
(check-equal? 
  (interp-asm-pred-lang-v6/framed (allocate-frames af-6))
  (interp-asm-pred-lang-v6/framed af-6-compiled))


(run-tests
   (test-suite
   ""
    (test-compiler-pass allocate-frames interp-asm-pred-lang-v6/pre-framed interp-asm-pred-lang-v6/framed asm-pred-lang-v6/framed?))))

