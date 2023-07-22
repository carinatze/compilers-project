#lang racket

(provide conflict-analysis)

(require
 cpsc411/compiler-lib
 cpsc411/2c-run-time
 cpsc411/langs/v6
 cpsc411/graph-lib
 racket/trace
 rackunit)

#| 
  Asm-lang-v6/undead is defined as: 
  p	 	::=	 	(module info (define label info tail) ... tail)
 	 	 	 	 
  info	 	::=	 	(#:from-contract 
              (info/c (new-frames (frame ...)) 
                (locals (aloc ...)) 
                (call-undead (loc ...)) 
                (undead-out undead-set-tree/rloc?)))
 	 	 	 	 
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

; Exercise 9
; reference: Paulette's office hours :)
; (Asm-lang-v6/undead p) -> (Asm-lang-v6/conflicts p)
; reconstructs p by decorating p with conflict graph by analysing undead-out from info 
(define (conflict-analysis p)

  ; (Asm-lang-v6/undead p) -> (asm-lang-v6/conflicts p)
  ; returns (asm-lang-v6/conflicts p) by calling conflict-analysis-info passing in info and the tail
  (define (conflict-analysis-p p g)
    (match p  
      [`(module ,info ,nested ... ,tail)
        (begin 
          (define vg
            (for/fold([vertex-graph g])
                ([aloc (info-ref info 'locals)])
                (add-vertex vertex-graph aloc)))
          `(module ((new-frames ,(info-ref info 'new-frames))
                    (locals ,(info-ref info 'locals)) 
                    (call-undead ,(info-ref info 'call-undead))
                    (undead-out ,(info-ref info 'undead-out))
                    (conflicts ,(conflict-analysis-t tail (info-ref info 'undead-out) vg)))
                    ,@(map conflict-analysis-p-nested nested)
                    ,tail))]))
  
  ; (Asm-lang-v6/undead nested-p) -> (asm-lang-v6/conflicts nested-p)
  ; nested-p ::= (define label info tail)
  ; returns (asm-lang-v6/conflicts nested-p) by calling conflict-analysis-info passing in 
  ; corresponding info and tail for this nested block
  (define (conflict-analysis-p-nested p)
    (match p
    [`(define ,label ,info ,tail)
    (begin
      (define vg
              (for/fold([vertex-graph (new-graph)])
                  ([aloc (info-ref info 'locals)])
                  (add-vertex vertex-graph aloc)))
      `(define ,label 
                ((new-frames ,(info-ref info 'new-frames))
                (locals ,(info-ref info 'locals)) 
                (call-undead ,(info-ref info 'call-undead))
                (undead-out ,(info-ref info 'undead-out))
                (conflicts ,(conflict-analysis-t tail (info-ref info 'undead-out) vg)))  
                ,tail))]))
  
  ; pred undead-set-tree? conflict-graph? ->  conflict-graph?
  ; adds alocs to the conflict graph cg based on analysis of the undead set tree (ust) given that 
  ; corresponds to pred 
  (define (conflict-analysis-pred pred ust cg)
    (match (cons ust pred)
      [(cons undead-out-set
            `(,relop ,loc ,opand))
        #:when(and (relop? relop) 
                  (opand? opand) 
                  (loc? loc)) 
      (add-edges cg loc (set-remove (set-remove undead-out-set loc) opand))]
      [(cons x true) 
        cg]
      [(cons x false) 
        cg]  
      [(cons x `(not ,pred)) 
        #:when(undead-set-tree? x) 
        (conflict-analysis-pred pred ust cg)]      
      [(cons `(,ust ... ,ust_tail) `(begin ,xs ... ,pred))	
         (define effect-graph
          (for/fold ([new-acc cg])  ;; new graph with added edges
                    ([us ust] ;; undead-set
                      [s xs]) ;; effect
                    (conflict-analysis-s s us new-acc)))
         (conflict-analysis-pred pred ust_tail effect-graph)]
      [(cons `(,ust ,ust_pred ,ust_pred1) `(if ,pred ,pred1 ,pred2))	
         (define pred-graph
          (for/fold ([new-acc cg])  
                    ([us (list ust ust_pred)]
                      [p (list pred pred1)]) 
                    (conflict-analysis-pred p us new-acc)))
         (conflict-analysis-pred pred2 ust_pred1 pred-graph)]))
  
  ; tail undead-set-tree? conflict-graph? ->  conflict-graph?
  ; adds alocs to the conflict graph cg based on analysis of the undead set tree (ust) given that 
  ; corresponds to tail 
  (define (conflict-analysis-t t ust cg)
    (match (cons t ust)
      [(cons 
        `(jump ,trg ,loc ...)
        ust)
        cg]  
      [(cons `(begin ,xs ... ,tail) ust)
        (define last-uo (list-ref ust (- (length ust) 1)))
        (define lst-uo (remove last-uo ust))
         (define effect-graph
          (for/fold ([new-acc cg])  ;; new graph with added edges
                    ([us lst-uo] ;; undead-set
                      [s xs]) ;; effect
                    (conflict-analysis-s s us new-acc)))
         (conflict-analysis-t tail last-uo effect-graph)]
      [(cons `(if ,pred ,tail ,tail1) ust) 
        (define ust_pred (first ust))
        (define ust_tail (second ust))
        (define ust_tail1 (third ust))
        (define pred-graph
          (conflict-analysis-pred pred ust_pred cg))
        (define tail-graph
          (conflict-analysis-t tail ust_tail pred-graph))
        (conflict-analysis-t tail1 ust_tail1 tail-graph)]))

  ; effect undead-set-tree? conflict-graph? ->  conflict-graph?
  ; adds alocs to the conflict graph cg based on analysis of the undead set tree (ust) given that 
  ; corresponds to effect 
  (define (conflict-analysis-s s ust cg)
    (match (cons s ust)
      [(cons `(set! ,loc ,triv) 
              undead-out-set)
        (add-edges cg loc (set-remove (set-remove undead-out-set loc) triv))]
      [(cons `(set! ,loc_1 (,binop ,loc_1 ,opand))	
              undead-out-set)
        (add-edges cg loc_1 (set-remove undead-out-set loc_1))]
      [	(cons `(begin ,effects ... ,effect) ust)
        (define last-uo (list-ref ust (- (length ust) 1)))
        (define lst-uo (remove last-uo ust))
        (define effect-graph
          (for/fold ([new-acc cg])  ;; new graph with added edges
                    ([us lst-uo] ;; undead-set
                      [s effects]) ;; effect
                    (conflict-analysis-s s us new-acc)))	
        (conflict-analysis-s effect last-uo effect-graph)]
      [(cons `(if ,pred ,effect ,effect1) ust) 
        (define ust_pred (first ust))
        (define ust_effect (second ust))
        (define ust_effect1 (third ust))
        (define pred-graph
          (conflict-analysis-pred pred ust_pred cg))
        (define effect-graph 
          (conflict-analysis-s effect ust_effect pred-graph))
        (conflict-analysis-s effect1 ust_effect1 effect-graph)]
      [(cons `(return-point ,label ,tail) 
              ust)
        ;(define ust_rp (first ust))  ;;TODO: is this needed for the cg?
        (define ust_tail (second ust)) 
        (conflict-analysis-t tail ust_tail cg)]))
  
  ;; triv -> boolean
  ;; returns true if triv t is a triv?
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

  (conflict-analysis-p p (new-graph)))

(module+ test 
  (require
  rackunit
   rackunit/text-ui
   cpsc411/langs/v6
   cpsc411/test-suite/public/v6
   cpsc411/test-suite/utils)

;; conflict-graph? conflict graph? [listof aloc] -> boolean
;; returns true if every aloc in both conflict graphs contain the same values, else false
(define (check-conflict-analysis cg1 cg2 locals)
  (for/fold ([bool #t])
            ([aloc locals])
            (and (set=? (get-neighbors cg1 aloc) (get-neighbors cg2 aloc))
              bool)))

(check-equal? 
(conflict-analysis
' (module 
    ((new-frames ()) 
    (locals (z.5 x.3 y.4 tmp-ra.40))
    (call-undead ()) 
    (undead-out 
    ((tmp-ra.40 rbp) 
    (y.4 tmp-ra.40 rbp) 
    (x.3 y.4 tmp-ra.40 rbp)
    (x.3 y.4 tmp-ra.40 rbp) 
    (x.3 y.4 z.5 tmp-ra.40 rbp) 
    (y.4 z.5 tmp-ra.40 rbp) 
    (z.5 x.3 tmp-ra.40 rbp) 
    (x.3 tmp-ra.40 rbp) 
    (x.3 tmp-ra.40 rbp) 
    (tmp-ra.40 rbp rax) 
    (rax rbp)))) 
  (begin 
    (set! tmp-ra.40 r15) 
    (set! y.4 5) 
    (set! x.3 1) 
    (set! x.3 (+ x.3 2)) 
    (set! z.5 2) 
    (set! x.3 (+ x.3 y.4)) 
    (set! x.3 y.4) 
    (set! x.3 (+ x.3 z.5)) 
    (set! x.3 x.3) 
    (set! rax x.3) 
    (jump tmp-ra.40 rbp rax))))
'(module
  ((new-frames ())
   (locals (z.5 x.3 y.4 tmp-ra.40))
   (call-undead ())
   (undead-out
    ((tmp-ra.40 rbp)
     (y.4 tmp-ra.40 rbp)
     (x.3 y.4 tmp-ra.40 rbp)
     (x.3 y.4 tmp-ra.40 rbp)
     (x.3 y.4 z.5 tmp-ra.40 rbp)
     (y.4 z.5 tmp-ra.40 rbp)
     (z.5 x.3 tmp-ra.40 rbp)
     (x.3 tmp-ra.40 rbp)
     (x.3 tmp-ra.40 rbp)
     (tmp-ra.40 rbp rax)
     (rax rbp)))
   (conflicts
    ((tmp-ra.40 (rax z.5 x.3 y.4 rbp))
     (y.4 (z.5 x.3 rbp tmp-ra.40))
     (x.3 (z.5 rbp tmp-ra.40 y.4))
     (z.5 (rbp tmp-ra.40 y.4 x.3))
     (rbp (rax z.5 x.3 y.4 tmp-ra.40))
     (rax (rbp tmp-ra.40)))))
  (begin
    (set! tmp-ra.40 r15)
    (set! y.4 5)
    (set! x.3 1)
    (set! x.3 (+ x.3 2))
    (set! z.5 2)
    (set! x.3 (+ x.3 y.4))
    (set! x.3 y.4)
    (set! x.3 (+ x.3 z.5))
    (set! x.3 x.3)
    (set! rax x.3)
    (jump tmp-ra.40 rbp rax))))

; jump w/ no loc
; begin effect ... tail
; set! loc triv
; (set! loc_1 (binop loc_1 opand))
(define ca-v6-9 
'(module ((new-frames (())) (locals (w.1 y.1 x.1)) (call-undead ()) (undead-out ((x.1 r15) (x.1 w.1 r15) (x.1 w.1 y.1 r15) (y.1 w.1 r15) (w.1 r15) ((r15) ())))) (begin (set! x.1 0) (set! w.1 0) (set! y.1 x.1) (set! w.1 (+ w.1 x.1)) (set! w.1 (+ w.1 y.1)) (begin (set! rax w.1) (jump r15)))))
(define ca-v6-9-compiled 
'(module
  ((new-frames (()))
   (locals (w.1 y.1 x.1))
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
     (r15 (y.1 w.1 x.1 rax)))))
  (begin
    (set! x.1 0)
    (set! w.1 0)
    (set! y.1 x.1)
    (set! w.1 (+ w.1 x.1))
    (set! w.1 (+ w.1 y.1))
    (begin (set! rax w.1) (jump r15)))))

;(check-equal? (conflict-analysis ca-v6-9) ca-v6-9-compiled)
(check-conflict-analysis 
  (info-ref (list-ref (conflict-analysis ca-v6-9) 1) 'conflicts)
  (info-ref (list-ref (conflict-analysis ca-v6-9-compiled) 1) 'conflicts)
  '(w.1 y.1 x.1 rax r15))

(define ca-v6-8 
'(module ((new-frames ()) (locals (tmp-ra.69)) (call-undead ()) (undead-out ((tmp-ra.69 rbp) (rax tmp-ra.69 rbp) (tmp-ra.69 rbp rax) (rax rbp)))) (begin (set! tmp-ra.69 r15) (set! rax 1) (set! rax (+ rax 2)) (jump tmp-ra.69 rbp rax))))
(define ca-v6-8-compiled 
'(module
  ((new-frames ())
   (locals (tmp-ra.69))
   (call-undead ())
   (undead-out
    ((tmp-ra.69 rbp) (rax tmp-ra.69 rbp) (tmp-ra.69 rbp rax) (rax rbp)))
   (conflicts
    ((tmp-ra.69 (rax rbp)) (rbp (rax tmp-ra.69)) (rax (rbp tmp-ra.69)))))
  (begin
    (set! tmp-ra.69 r15)
    (set! rax 1)
    (set! rax (+ rax 2))
    (jump tmp-ra.69 rbp rax))))

(check-equal? (conflict-analysis ca-v6-8) ca-v6-8-compiled)
(check-conflict-analysis 
  (info-ref (list-ref (conflict-analysis ca-v6-8) 1) 'conflicts)
  (info-ref (list-ref (conflict-analysis ca-v6-8-compiled) 1) 'conflicts)
  '(tmp-ra.75 rax rbp))

(define ca-v6-6 
'(module ((new-frames (())) (locals (x.1 y.1 z.1)) (call-undead ()) (undead-out ((x.1 r15) (y.1 r15) (y.1 r15) (z.1 r15) (z.1 r15) ((r15) ())))) (begin (set! x.1 1) (set! y.1 x.1) (set! y.1 (+ y.1 1)) (set! z.1 y.1) (set! z.1 (+ z.1 1)) (begin (set! rax z.1) (jump r15)))))
(define ca-v6-6-compiled 
'(module
  ((new-frames (()))
   (locals (x.1 y.1 z.1))
   (call-undead ())
   (undead-out ((x.1 r15) (y.1 r15) (y.1 r15) (z.1 r15) (z.1 r15) ((r15) ())))
   (conflicts
    ((z.1 (r15)) (y.1 (r15)) (x.1 (r15)) (rax (r15)) (r15 (z.1 y.1 x.1 rax)))))
  (begin
    (set! x.1 1)
    (set! y.1 x.1)
    (set! y.1 (+ y.1 1))
    (set! z.1 y.1)
    (set! z.1 (+ z.1 1))
    (begin (set! rax z.1) (jump r15)))))

;(check-equal? (conflict-analysis ca-v6-6) ca-v6-6-compiled)
(check-conflict-analysis 
  (info-ref (list-ref (conflict-analysis ca-v6-6) 1) 'conflicts)
  (info-ref (list-ref (conflict-analysis ca-v6-6-compiled) 1) 'conflicts)
  '(x.1 y.1 z.1 rax r15))

; if pred effect effect 
; begin effect effect
; true
(define ca-v6-5 
'(module ((new-frames ()) 
  (locals (tmp-ra.76 x.1 y.2 x.5)) 
  (call-undead ()) 
  (undead-out 
    ((tmp-ra.76 rbp) 
    (x.1 tmp-ra.76 rbp) 
    ((x.1 tmp-ra.76 rbp) 
    ((y.2 tmp-ra.76 rbp) 
    (tmp-ra.76 rbp) 
    (x.5 tmp-ra.76 rbp)) 
    (x.5 tmp-ra.76 rbp)) 
    (tmp-ra.76 rbp rax) 
    (rax rbp)))) 
  (begin (set! tmp-ra.76 r15) (set! x.1 5) 
    (if (true) 
    (begin (set! y.2 x.1) (set! y.2 (+ y.2 17)) (set! x.5 12)) 
    (set! x.5 15)) 
    (set! rax x.5) 
    (jump tmp-ra.76 rbp rax))))
(define ca-v6-5-compiled 
'(module
  ((new-frames ())
   (locals (tmp-ra.76 x.1 y.2 x.5))
   (call-undead ())
   (undead-out
    ((tmp-ra.76 rbp)
     (x.1 tmp-ra.76 rbp)
     ((x.1 tmp-ra.76 rbp)
      ((y.2 tmp-ra.76 rbp) (tmp-ra.76 rbp) (x.5 tmp-ra.76 rbp))
      (x.5 tmp-ra.76 rbp))
     (tmp-ra.76 rbp rax)
     (rax rbp)))
   (conflicts
    ((x.5 (rbp tmp-ra.76))
     (y.2 (rbp tmp-ra.76))
     (x.1 (rbp tmp-ra.76))
     (tmp-ra.76 (rax y.2 x.5 x.1 rbp))
     (rbp (rax y.2 x.5 x.1 tmp-ra.76))
     (rax (rbp tmp-ra.76)))))
  (begin
    (set! tmp-ra.76 r15)
    (set! x.1 5)
    (if (true)
      (begin (set! y.2 x.1) (set! y.2 (+ y.2 17)) (set! x.5 12))
      (set! x.5 15))
    (set! rax x.5)
    (jump tmp-ra.76 rbp rax))))

;(check-equal? (conflict-analysis ca-v6-5) ca-v6-5-compiled)
(check-conflict-analysis 
  (info-ref (list-ref (conflict-analysis ca-v6-5) 1) 'conflicts)
  (info-ref (list-ref (conflict-analysis ca-v6-5-compiled) 1) 'conflicts)
  '(tmp-ra.76 x.1 y.2 x.5 rax rbp))

(define ca-v6-4 
' (module 
    ((new-frames ()) 
    (locals (tmp-ra.68 x.1 y.1 z.1 w.1)) 
    (call-undead ()) 
    (undead-out 
      ((tmp-ra.68 rbp) 
        (x.1 tmp-ra.68 rbp) 
        (y.1 x.1 tmp-ra.68 rbp) 
        (y.1 z.1 x.1 tmp-ra.68 rbp) 
        (x.1 z.1 tmp-ra.68 rbp) 
        (z.1 w.1 tmp-ra.68 rbp) 
        (w.1 tmp-ra.68 rbp) 
        (tmp-ra.68 rbp rax) 
        (rax rbp)))) 
    (begin
      (set! tmp-ra.68 r15) 
      (set! x.1 1) 
      (set! y.1 1) 
      (set! z.1 x.1) 
      (set! z.1 (+ z.1 y.1)) 
      (set! w.1 x.1) 
      (set! w.1 (+ w.1 z.1)) 
      (set! rax w.1) 
      (jump tmp-ra.68 rbp rax))))

(define ca-v6-4-compiled 
'(module
  ((new-frames ())
   (locals (tmp-ra.68 x.1 y.1 z.1 w.1))
   (call-undead ())
   (undead-out
    ((tmp-ra.68 rbp)
     (x.1 tmp-ra.68 rbp)
     (y.1 x.1 tmp-ra.68 rbp)
     (y.1 z.1 x.1 tmp-ra.68 rbp)
     (x.1 z.1 tmp-ra.68 rbp)
     (z.1 w.1 tmp-ra.68 rbp)
     (w.1 tmp-ra.68 rbp)
     (tmp-ra.68 rbp rax)
     (rax rbp)))
   (conflicts
    ((w.1 (rbp tmp-ra.68 z.1))
     (z.1 (w.1 x.1 rbp tmp-ra.68 y.1))
     (y.1 (z.1 rbp tmp-ra.68 x.1))
     (x.1 (z.1 y.1 rbp tmp-ra.68))
     (tmp-ra.68 (rax w.1 z.1 y.1 x.1 rbp))
     (rbp (rax w.1 z.1 y.1 x.1 tmp-ra.68))
     (rax (rbp tmp-ra.68)))))
  (begin
    (set! tmp-ra.68 r15)
    (set! x.1 1)
    (set! y.1 1)
    (set! z.1 x.1)
    (set! z.1 (+ z.1 y.1))
    (set! w.1 x.1)
    (set! w.1 (+ w.1 z.1))
    (set! rax w.1)
    (jump tmp-ra.68 rbp rax))))

;(check-equal? (conflict-analysis ca-v6-4) ca-v6-4-compiled)
(check-conflict-analysis 
  (info-ref (list-ref (conflict-analysis ca-v6-4) 1) 'conflicts)
  (info-ref (list-ref (conflict-analysis ca-v6-4-compiled) 1) 'conflicts)
  '(tmp-ra.68 x.1 y.1 z.1 w.1 rax rbp))

(define ca-v6-2 
'(module 
  ((new-frames (())) 
    (locals ()) 
    (call-undead ()) 
    (undead-out ((r15) ()))) 
  (begin (set! rax 5) (jump r15))))

(define ca-v6-2-compiled 
'(module
  ((new-frames (()))
   (locals ())
   (call-undead ())
   (undead-out ((r15) ()))
   (conflicts ((rax (r15)) (r15 (rax)))))
  (begin (set! rax 5) (jump r15))))

(check-conflict-analysis 
  (info-ref (list-ref (conflict-analysis ca-v6-2) 1) 'conflicts)
  (info-ref (list-ref (conflict-analysis ca-v6-2-compiled) 1) 'conflicts)
  '(rax r15))

(define ca-v6-1 
' (module 
    ((new-frames ()) 
      (locals (tmp-ra.153 x.1 y.2 x.5)) 
      (call-undead ()) 
      (undead-out 
        ((tmp-ra.153 rbp) 
          (x.1 tmp-ra.153 rbp) 
        ((x.1 tmp-ra.153 rbp) 
          ((y.2 tmp-ra.153 rbp) 
            (tmp-ra.153 rbp) 
            (x.5 tmp-ra.153 rbp)) 
          (x.5 tmp-ra.153 rbp)) 
        (tmp-ra.153 rbp rax) 
        (rax rbp)))) 
    (begin 
      (set! tmp-ra.153 r15) 
      (set! x.1 5) 
      (if (true) 
        (begin 
          (set! y.2 x.1) 
          (set! y.2 (+ y.2 17)) 
          (set! x.5 12)) 
        (set! x.5 15)) 
      (set! rax x.5) 
      (jump tmp-ra.153 rbp rax))))
(define ca-v6-1-compiled 
'(module
  ((new-frames ())
   (locals (tmp-ra.153 x.1 y.2 x.5))
   (call-undead ())
   (undead-out
    ((tmp-ra.153 rbp)
     (x.1 tmp-ra.153 rbp)
     ((x.1 tmp-ra.153 rbp)
      ((y.2 tmp-ra.153 rbp) (tmp-ra.153 rbp) (x.5 tmp-ra.153 rbp))
      (x.5 tmp-ra.153 rbp))
     (tmp-ra.153 rbp rax)
     (rax rbp)))
   (conflicts
    ((x.5 (rbp tmp-ra.153))
     (y.2 (rbp tmp-ra.153))
     (x.1 (rbp tmp-ra.153))
     (tmp-ra.153 (rax y.2 x.5 x.1 rbp))
     (rbp (rax y.2 x.5 x.1 tmp-ra.153))
     (rax (rbp tmp-ra.153)))))
  (begin
    (set! tmp-ra.153 r15)
    (set! x.1 5)
    (if (true)
      (begin (set! y.2 x.1) (set! y.2 (+ y.2 17)) (set! x.5 12))
      (set! x.5 15))
    (set! rax x.5)
    (jump tmp-ra.153 rbp rax))))
;(conflict-analysis ca-v6-1)
;(check-equal? (conflict-analysis ca-v6-1) ca-v6-1-compiled)
(check-conflict-analysis 
  (info-ref (list-ref (conflict-analysis ca-v6-1) 1) 'conflicts)
  (info-ref (list-ref (conflict-analysis ca-v6-1-compiled) 1) 'conflicts)
  '(tmp-ra.153 x.1 y.2 x.5 rbp rax))

; if pred tail tail
(define ca-7
'(module
  ((new-frames ())
   (locals (tmp-ra.4))
   (call-undead ())
   (undead-out
    ((tmp-ra.4 rbp)
     (tmp-ra.4 fv1 rbp)
     (tmp-ra.4 fv1 fv0 rbp)
     (fv1 fv0 r15 rbp)
     (fv1 fv0 r15 rbp))))
  (define L.swap.1
    ((new-frames ((nfv.2 nfv.3)))
     (locals (nfv.2 nfv.3 z.3 tmp-ra.1 x.1 y.2))
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
     (call-undead (tmp-ra.1)))
    (begin
      (set! tmp-ra.1 r15)
      (set! x.1 fv0)
      (set! y.2 fv1)
      (if (< y.2 x.1)
        (begin (set! rax x.1) (jump tmp-ra.1 rbp rax))
        (begin
          (return-point
           L.rp.1
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
(define ca-7-compiled
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
     (r15 (rbp fv0 fv1)))))
  (define L.swap.1
    ((new-frames ((nfv.2 nfv.3)))
     (locals (nfv.2 nfv.3 z.3 tmp-ra.1 x.1 y.2))
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
       (fv1 (x.1 tmp-ra.1)))))
    (begin
      (set! tmp-ra.1 r15)
      (set! x.1 fv0)
      (set! y.2 fv1)
      (if (< y.2 x.1)
        (begin (set! rax x.1) (jump tmp-ra.1 rbp rax))
        (begin
          (return-point
           L.rp.1
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
(check-conflict-analysis 
  (info-ref (list-ref (conflict-analysis ca-7) 1) 'conflicts)
  (info-ref (list-ref (conflict-analysis ca-7-compiled) 1) 'conflicts)
  '(tmp-ra.4 rbp fv1 fv0 r15))
(check-conflict-analysis 
  (info-ref (list-ref (list-ref (conflict-analysis ca-7) 2) 2) 'conflicts)
  (info-ref (list-ref (list-ref (conflict-analysis ca-7-compiled) 2) 2) 'conflicts)
  '(y.2 x.1 tmp-ra.1 z.3 nfv.3 nfv.2 rbp r15 rax fv0 fv1))

; return-point label tail
(define ca-8
'(module
  ((new-frames ())
   (locals (ra.12))
   (call-undead ())
   (undead-out ((ra.12 rbp) (ra.12 fv0 rbp) (fv0 r15 rbp) (fv0 r15 rbp))))
  (define L.fact.4
    ((new-frames ((nfv.16)))
     (locals (ra.13 x.9 tmp.14 tmp.15 new-n.10 nfv.16 factn-1.11 tmp.17))
     (undead-out
      ((r15 x.9 rbp)
       (x.9 ra.13 rbp)
       ((x.9 ra.13 rbp)
        ((ra.13 rax rbp) (rax rbp))
        ((tmp.14 x.9 ra.13 rbp)
         (tmp.14 tmp.15 x.9 ra.13 rbp)
         (tmp.15 x.9 ra.13 rbp)
         (new-n.10 x.9 ra.13 rbp)
         ((rax x.9 ra.13 rbp) ((nfv.16 rbp) (nfv.16 r15 rbp) (nfv.16 r15 rbp)))
         (x.9 factn-1.11 ra.13 rbp)
         (factn-1.11 tmp.17 ra.13 rbp)
         (tmp.17 ra.13 rbp)
         (ra.13 rax rbp)
         (rax rbp)))))
     (call-undead (x.9 ra.13)))
    (begin
      (set! x.9 fv0)
      (set! ra.13 r15)
      (if (= x.9 0)
        (begin (set! rax 1) (jump ra.13 rbp rax))
        (begin
          (set! tmp.14 -1)
          (set! tmp.15 x.9)
          (set! tmp.15 (+ tmp.15 tmp.14))
          (set! new-n.10 tmp.15)
          (return-point L.rp.6
            (begin
              (set! nfv.16 new-n.10)
              (set! r15 L.rp.6)
              (jump L.fact.4 rbp r15 nfv.16)))
          (set! factn-1.11 rax)
          (set! tmp.17 x.9)
          (set! tmp.17 (* tmp.17 factn-1.11))
          (set! rax tmp.17)
          (jump ra.13 rbp rax)))))
  (begin
    (set! ra.12 r15)
    (set! fv0 5)
    (set! r15 ra.12)
    (jump L.fact.4 rbp r15 fv0))))

(define ca-8-compiled
'(module
  ((new-frames ())
   (locals (ra.12))
   (call-undead ())
   (undead-out ((ra.12 rbp) (ra.12 fv0 rbp) (fv0 r15 rbp) (fv0 r15 rbp)))
   (conflicts
    ((ra.12 (fv0 rbp))
     (rbp (r15 fv0 ra.12))
     (fv0 (r15 rbp ra.12))
     (r15 (rbp fv0)))))
  (define L.fact.4
    ((new-frames ((nfv.16)))
     (locals (ra.13 x.9 tmp.14 tmp.15 new-n.10 nfv.16 factn-1.11 tmp.17))
     (undead-out
      ((r15 x.9 rbp)
       (x.9 ra.13 rbp)
       ((x.9 ra.13 rbp)
        ((ra.13 rax rbp) (rax rbp))
        ((tmp.14 x.9 ra.13 rbp)
         (tmp.14 tmp.15 x.9 ra.13 rbp)
         (tmp.15 x.9 ra.13 rbp)
         (new-n.10 x.9 ra.13 rbp)
         ((rax x.9 ra.13 rbp) ((nfv.16 rbp) (nfv.16 r15 rbp) (nfv.16 r15 rbp)))
         (x.9 factn-1.11 ra.13 rbp)
         (factn-1.11 tmp.17 ra.13 rbp)
         (tmp.17 ra.13 rbp)
         (ra.13 rax rbp)
         (rax rbp)))))
     (call-undead (x.9 ra.13))
     (conflicts
      ((tmp.17 (rbp ra.13 factn-1.11))
       (factn-1.11 (tmp.17 rbp ra.13 x.9))
       (nfv.16 (r15 rbp))
       (new-n.10 (rbp ra.13 x.9))
       (tmp.15 (x.9 rbp ra.13 tmp.14))
       (tmp.14 (tmp.15 rbp ra.13 x.9))
       (x.9 (ra.13 rbp r15 factn-1.11 new-n.10 tmp.15 tmp.14))
       (ra.13 (rbp x.9 rax tmp.17 factn-1.11 new-n.10 tmp.15 tmp.14))
       (rbp
        (ra.13 x.9 rax tmp.17 factn-1.11 r15 nfv.16 new-n.10 tmp.15 tmp.14))
       (r15 (x.9 rbp nfv.16))
       (rax (rbp ra.13)))))
    (begin
      (set! x.9 fv0)
      (set! ra.13 r15)
      (if (= x.9 0)
        (begin (set! rax 1) (jump ra.13 rbp rax))
        (begin
          (set! tmp.14 -1)
          (set! tmp.15 x.9)
          (set! tmp.15 (+ tmp.15 tmp.14))
          (set! new-n.10 tmp.15)
          (return-point
           L.rp.6
           (begin
             (set! nfv.16 new-n.10)
             (set! r15 L.rp.6)
             (jump L.fact.4 rbp r15 nfv.16)))
          (set! factn-1.11 rax)
          (set! tmp.17 x.9)
          (set! tmp.17 (* tmp.17 factn-1.11))
          (set! rax tmp.17)
          (jump ra.13 rbp rax)))))
  (begin
    (set! ra.12 r15)
    (set! fv0 5)
    (set! r15 ra.12)
    (jump L.fact.4 rbp r15 fv0))))
(check-conflict-analysis 
  (info-ref (list-ref (conflict-analysis ca-8) 1) 'conflicts)
  (info-ref (list-ref (conflict-analysis ca-8-compiled) 1) 'conflicts)
  '(ra.12 rbp fv0 r15))
(check-conflict-analysis 
  (info-ref (list-ref (list-ref (conflict-analysis ca-8) 2) 2) 'conflicts)
  (info-ref (list-ref (list-ref (conflict-analysis ca-8-compiled) 2) 2) 'conflicts)
  '(rbp fv0 r15 tmp.17 factn-1.11 nfv.16 new-n.10 tmp.15 tmp.14 x.9 ra.13))

; not pred 
; true
; false 
; if pred pred pred
(define ca-v6-3 
'(module
  ((new-frames ())
   (locals (tmp-ra.75))
   (call-undead ())
   (undead-out
    ((tmp-ra.75 rbp)
     (tmp-ra.75 rbp)
     (((tmp-ra.75 rbp) (tmp-ra.75 rbp) (tmp-ra.75 rbp))
      (rax tmp-ra.75 rbp)
      (rax tmp-ra.75 rbp))
     (tmp-ra.75 rax rbp)
     (rax rbp))))
  (begin
    (set! tmp-ra.75 r15)
    (set! rax 1)
    (if (if (false) (true) (not (true))) (set! rax 2) (set! rax 3))
    (set! rax (+ rax 2))
    (jump tmp-ra.75 rbp rax))))
(define ca-v6-3-compiled
'(module
  ((new-frames ())
   (locals (tmp-ra.75))
   (call-undead ())
   (undead-out
    ((tmp-ra.75 rbp)
     (tmp-ra.75 rbp)
     (((tmp-ra.75 rbp) (tmp-ra.75 rbp) (tmp-ra.75 rbp))
      (rax tmp-ra.75 rbp)
      (rax tmp-ra.75 rbp))
     (tmp-ra.75 rax rbp)
     (rax rbp)))
   (conflicts
    ((tmp-ra.75 (rax rbp)) (rbp (rax tmp-ra.75)) (rax (rbp tmp-ra.75)))))
  (begin
    (set! tmp-ra.75 r15)
    (set! rax 1)
    (if (if (false) 
          (true) 
          (not (true))) 
      (set! rax 2) 
      (set! rax 3))
    (set! rax (+ rax 2))
    (jump tmp-ra.75 rbp rax))))
(check-conflict-analysis 
  (info-ref (list-ref (conflict-analysis ca-v6-3) 1) 'conflicts)
  (info-ref (list-ref (conflict-analysis ca-v6-3-compiled) 1) 'conflicts)
  '(tmp-ra.75 rbp rax))

(run-tests
   (test-suite
    ""
    (test-compiler-pass conflict-analysis interp-asm-pred-lang-v6/undead interp-asm-pred-lang-v6/conflicts asm-pred-lang-v6/conflicts?))))



