#lang racket

(provide undead-analysis)

(require
 cpsc411/compiler-lib
 cpsc411/2c-run-time
 cpsc411/langs/v6
 cpsc411/graph-lib
 racket/trace
 rackunit)

#| asm-pred-lang-v6/locals:
    p	 	::=	 	(module info (define label info tail) ... tail)
 	 	 	 	 
  info	 	::=	 	(#:from-contract 
                (info/c (new-frames (frame ...)) 
                    (locals (aloc ...))))
 	 	 	 	 
  frame	 	::=	 	(aloc ...)
 	 	 	 	 
  pred	 	::=	 	(relop loc opand) ;
 	 	|	 	(true)
 	 	|	 	(false)
 	 	|	 	(not pred)
 	 	|	 	(begin effect ... pred) ;
 	 	|	 	(if pred pred pred)
 	 	 	 	 
  tail	 	::=	 	(jump trg loc ...) ;
 	 	|	 	(begin effect ... tail) ;
 	 	|	 	(if pred tail tail) ;
 	 	 	 	 
  effect	 	::=	 	(set! loc triv) ;
 	 	|	 	(set! loc_1 (binop loc_1 opand)) ;
 	 	|	 	(begin effect ... effect)
 	 	|	 	(if pred effect effect) ;
 	 	|	 	(return-point label tail) ;
 	 	 	 	 
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

;; Exercise 8
;; asm-pred-lang-v6/locals -> asm-lang-v6/undead 
;; performs undead analysis for each statement using undead-set tree (ust)
;; decorates info undead-out section with undead-set tree for p 
;; reference: paulette's office hours :)
(define (undead-analysis p) 

  ;; asm-pred-lang-v6/locals p -> asm-lang-v6/undead p
  ;; decorates undead-out with undead-set tree for p
  ;; and call-undead with every aloc or fvar in undead-out set of return-point
  (define (undead-analysis-p p)
    (match p
      [`(module ,info ,nested ... ,tail)
        (define ust '())
        (define-values (ust-tail undead-out-tail undead-out-rp) 
          (undead-analysis-tail tail '() '()))
        `(module
          ((new-frames ,(info-ref info 'new-frames))
          (locals ,(info-ref info 'locals))
          (call-undead ,undead-out-rp)
          (undead-out ,ust-tail))
          ,@(map undead-analysis-p-nested nested)
          ,tail)]))
  
  ;; asm-pred-lang-v6/locals (nested p) -> asm-pred-lang-v6/undead (nested p)
  ;;
  ;; nested p ::= (define label info tail)
  ;; performs local undead analysis using undead-set tree (ust) on nested-p
  ;; decorates local info field for the corresponding block
  ;; and call-undead with every aloc or fvar in undead-out set of return-point
  (define (undead-analysis-p-nested p)
    (match p
      [`(define ,label ,info ,tail)
      (begin
        (define ust '())
        (define-values (ust-tail undead-out-tail undead-out-rp)
          (undead-analysis-tail tail '() '()))
        `(define
          ,label
          ((new-frames ,(info-ref info 'new-frames))
            (locals ,(info-ref info 'locals))
            (undead-out ,ust-tail)
            (call-undead ,undead-out-rp))
          ,tail))]))
  
  ;; tail undead-set? undead-set-tree? -> (values undead-set-tree? undead-set?)
  ;;
  ;; the output undead-set-tree should only contain the undead-out sets for
  ;; tail and undead-out-rp should contain every aloc or fvar in undead-out set of return-point
  (define (undead-analysis-tail tail undead-out undead-out-rp) 
      (match tail
        [`(begin ,effects ... ,tail)
          (define-values (ust-tail undead-in-tail undead-out-rp-tail)
            (undead-analysis-tail tail undead-out undead-out-rp))
          (define-values (ust-effects undead-out-effects undead-out-rp-effects)
            (for/foldr ([ust '()]
                        [new-undead-out undead-in-tail]
                        [undead-out-rp-effect undead-out-rp])
                        ([new-effect effects])
              (define-values (new-ust undead-in new-uo-rp)
                (undead-analyse-effect new-effect new-undead-out undead-out-rp-effect))
              (values
                (cons new-ust ust)
                undead-in
                (set-union new-uo-rp undead-out-rp-effect))))
           (values 
            (append ust-effects (list ust-tail)) 
            undead-out-effects
            (set-union undead-out-rp-tail undead-out-rp-effects))]
        [`(jump ,trg ,loc ...)
        (define undead-in
          (if (loc? trg)
            (set-add loc trg)
            loc))
          (values (reverse loc) undead-in undead-out-rp)] 
        [`(if ,pred ,tail_t ,tail_f)
         (define-values (ust-tail_t undead-in-t uo-rp-t)
          (undead-analysis-tail tail_t undead-out undead-out-rp))
        (define-values (ust-tail_f undead-in-f uo-rp-f)
          (undead-analysis-tail tail_f undead-out uo-rp-t))
        (define-values (ust-pred undead-in-pred uo-rp-pred)
          (undead-analyse-pred pred (set-union undead-in-t undead-in-f) uo-rp-f))
        (values 
          (list ust-pred ust-tail_t ust-tail_f) 
          undead-in-pred 
          uo-rp-pred)]))
  
  ;; Effect undead-set? undead-set-tree? -> (values undead-set-tree? undead-set? undead-set?)
  ;;
  ;; the output undead-set-tree should only contain the undead-out sets for effect 
  ;; for the corresponding ust block, the undead-out set for the next effect, 
  ;; and undead-out-rp should contain every aloc or fvar in undead-out set of return-point
  (define (undead-analyse-effect effect undead-out undead-out-rp)
    (match effect
      [`(begin ,effects ...)
        (define-values (ust-effects undead-out-effect undead-out-rp-effect)
          (for/foldr ([ust '()]
                      [new-undead-out undead-out]
                      [new-undead-out-rp undead-out-rp])
                      ([new-effect effects])
            (define-values (new-ust undead-in undead-rp)
             (undead-analyse-effect new-effect new-undead-out new-undead-out-rp))
            (values
              (cons new-ust ust)
              undead-in
              (set-union undead-rp new-undead-out-rp))))
        (values ust-effects undead-out-effect undead-out-rp-effect)]
      [`(if ,pred ,effect_t ,effect_f)
        (define-values (ust-effect_t undead-in-t undead-rp-t)
          (undead-analyse-effect effect_t undead-out undead-out-rp))
        (define-values (ust-effect_f undead-in-f undead-rp-f)
          (undead-analyse-effect effect_f undead-out undead-rp-t))
        (define-values (ust-pred undead-in-pred undead-rp-pred)
          (undead-analyse-pred pred (set-union undead-in-t undead-in-f) undead-rp-f))
        (values 
          (list ust-pred ust-effect_t ust-effect_f) 
          undead-in-pred
          undead-rp-pred)] 
      [`(set! ,loc_1 (,binop ,loc_1 ,triv)) 
        (define undead-in
          (if (loc? triv) 
            (set-add (set-add (set-remove undead-out loc_1) loc_1) triv)
            (set-add (set-remove undead-out loc_1) loc_1)))
        (values undead-out undead-in undead-out-rp)]
      [`(set! ,loc ,triv) 
        (define undead-in
          (if (loc? triv)
            (set-add (set-remove undead-out loc) triv)
            (set-remove undead-out loc)))
        (values undead-out undead-in undead-out-rp)]
      [`(return-point ,label ,tail)
      (define-values (ust-tail undead-in-t uo-rp-t)
          (undead-analysis-tail tail undead-out undead-out-rp))
      (define lst-cu-rp
        (for/foldr ([lst-cu uo-rp-t])
                  ([u undead-out]) 
          (if (or (aloc? u) (fvar? u))
            (cons u lst-cu)
            lst-cu)))
        (values (cons undead-out (list ust-tail))
                (set-remove (set-union undead-in-t undead-out) (current-return-value-register))
                (reverse lst-cu-rp))]))

    ;; pred undead-set? undead-set-tree? -> (values undead-set-tree? undead-set? undead-set?)
    ;;
    ;; the output undead-set-tree should only contain the undead-out sets for
    ;; pred for the corresponding ust block, the undead-out set for the pred statement
    ;; and the undead-set-rp of a return-point contains every aloc or fvar 
    (define (undead-analyse-pred pred undead-out uo-rp)
      (match pred 
        [`(begin ,effects ... ,pred)
          (define-values (ust-pred undead-out-pred uo-rp-pred)
            (undead-analyse-pred pred undead-out uo-rp))
          (define-values (ust-effects undead-out-effects uo-rp-effects)
            (for/foldr ([ust '()]
                        [new-undead-out undead-out-pred]
                        [uo-rp-effect uo-rp])
                        ([new-effect effects])
              (define-values (new-ust undead-in uo-rp-s)
                (undead-analyse-effect new-effect new-undead-out uo-rp-effect))
                (values
                  (cons new-ust ust)
                  undead-in
                  (set-union uo-rp-s uo-rp-effect))))
           (values 
            (append ust-effects (list ust-pred)) 
            undead-out-effects 
            (set-union uo-rp-pred uo-rp-effects))]
        [`(,relop ,loc ,triv)
          (define undead-in
            (if (loc? triv)
              (set-add (set-add undead-out loc) triv) 
              (set-add undead-out loc)))
          (values undead-out undead-in uo-rp)]
         [`(true)
            (values undead-out undead-out uo-rp)]
         [`(false)
            (values undead-out undead-out uo-rp)]
          [`(not ,pred)
          (define-values (ust-pred undead-in-pred uo-rp-pred)
            (undead-analyse-pred pred undead-out uo-rp))
         (values ust-pred undead-in-pred uo-rp-pred)]
        [`(if ,pred ,pred_t ,pred_f)
          (define-values (ust-pred_t undead-in-t uo-rp-t)
            (undead-analyse-pred pred_t undead-out uo-rp))
          (define-values (ust-pred_f undead-in-f uo-rp-f)
            (undead-analyse-pred pred_f undead-out uo-rp-t))
          (define-values (ust-pred undead-in-pred uo-rp-pred)
            (undead-analyse-pred pred (set-union undead-in-t undead-in-f) uo-rp-f))
          (values 
            (list ust-pred ust-pred_t ust-pred_f) 
            undead-in-pred 
            uo-rp-pred)]))

    (define (loc? loc)
      (or (aloc? loc) (rloc? loc)))

    (define (rloc? rloc)
      (or (register? rloc) (fvar? rloc)))

    (undead-analysis-p p))
(list? (first `((tmp-ra.75 rbp) (tmp-ra.75 rbp) (tmp-ra.75 rbp))))

(module+ test 
  (require
  rackunit
   rackunit/text-ui
   cpsc411/langs/v6
   cpsc411/test-suite/public/v6
   cpsc411/test-suite/utils)
   
; undead-set tree? undead-set tree? -> boolean
; returns true if the two undead-set trees are equal to each other, calls recursively to check nested
; else returns false
(define (check-undead-analysis ua ua-c)
  (for/fold ([bool #t])
            ([uo ua]
            [uo-c ua-c])
    (if (list? (first uo))
      (and (check-undead-analysis uo uo-c) bool)
      (and (set=? uo uo-c) bool))))

; true
; false
; if pred pred pred
; not pred
; if pred effect effect
(define ua-v6-4-compiled 
'(module
  ((new-frames ())
   (locals (ra.12))
   (call-undead ())
   (undead-out
    ((ra.12 rbp)
     (ra.12 rbp)
     ((ra.12 rbp) ((fv0 ra.12 rbp) (ra.12 fv0 rbp)) (ra.12 fv0 rbp))
     (fv0 r15 rbp)
     (fv0 r15 rbp))))
  (begin
    (set! ra.12 r15)
    (set! fv0 5)
    (if (not (true)) (begin (set! fv0 4) (set! fv0 (- fv0 1))) (set! fv0 6))
    (set! r15 ra.12)
    (jump L.fact.4 rbp r15 fv0))))
(define ua-v6-4
'(module
  ((new-frames ()) 
    (locals (ra.12)))
       (begin
         (set! ra.12 r15)
         (set! fv0 5)
         (if (not (true))
          (begin (set! fv0 4) (set! fv0 (- fv0 1)))
          (set! fv0 6))
         (set! r15 ra.12)
         (jump L.fact.4 rbp r15 fv0))))

;(check-equal? (undead-analysis ua-v6-4) ua-v6-4-compiled)
(check-undead-analysis 
  (info-ref(list-ref (undead-analysis ua-v6-4) 1) 'undead-out)
  (info-ref(list-ref ua-v6-4-compiled 1) 'undead-out))

; begin effect pred 
; set loc triv
; begin effect tail
; set loc (binop loc opand)
; relop loc opand
; jump trg loc
; if pred tail tail
(define ua-v6-3
'(module ((new-frames ()) 
  (locals (tmp.42 tmp-ra.37))) 
  (begin 
    (set! tmp-ra.37 r15) 
    (if (begin (set! tmp.42 0) (> tmp.42 1)) 
        (begin (set! rax 0) (jump tmp-ra.37 rbp rax)) 
        (begin (set! rax 0) (set! rax (+ rax 1)) (jump tmp-ra.37 rbp rax))))))

(define ua-v6-3-compiled 
'(module
  ((new-frames ())
   (locals (tmp.42 tmp-ra.37))
   (call-undead ())
   (undead-out
    ((tmp-ra.37 rbp)
     (((tmp.42 tmp-ra.37 rbp) (tmp-ra.37 rbp))
      ((tmp-ra.37 rax rbp) (rax rbp))
      ((rax tmp-ra.37 rbp) (tmp-ra.37 rax rbp) (rax rbp))))))
  (begin
    (set! tmp-ra.37 r15)
    (if (begin (set! tmp.42 0) (> tmp.42 1))
      (begin (set! rax 0) (jump tmp-ra.37 rbp rax))
      (begin (set! rax 0) (set! rax (+ rax 1)) (jump tmp-ra.37 rbp rax))))))
;(check-equal? (undead-analysis ua-v6-3) ua-v6-3-compiled) 
(check-undead-analysis 
  (info-ref(list-ref (undead-analysis ua-v6-3) 1) 'undead-out)
  (info-ref(list-ref ua-v6-3-compiled 1) 'undead-out))

; if pred effect effect
(define ua-v6-2
'(module
  ((new-frames ()) 
    (locals (ra.12)))
       (begin
         (set! ra.12 r15)
         (set! fv0 5)
         (if (< fv0 5)
          (set! fv0 4)
          (set! fv0 6))
         (set! r15 ra.12)
         (jump L.fact.4 rbp r15 fv0))))

(define ua-v6-2-compiled 
'(module
  ((new-frames ())
   (locals (ra.12))
   (call-undead ())
   (undead-out
    ((ra.12 rbp)
     (fv0 ra.12 rbp)
     ((ra.12 rbp) (ra.12 fv0 rbp) (ra.12 fv0 rbp))
     (fv0 r15 rbp)
     (fv0 r15 rbp))))
  (begin
    (set! ra.12 r15)
    (set! fv0 5)
    (if (< fv0 5) (set! fv0 4) (set! fv0 6))
    (set! r15 ra.12)
    (jump L.fact.4 rbp r15 fv0))))
;(check-equal? (undead-analysis ua-v6-2) ua-v6-2-compiled) 
(check-undead-analysis 
  (info-ref(list-ref (undead-analysis ua-v6-2) 1) 'undead-out)
  (info-ref(list-ref ua-v6-2-compiled 1) 'undead-out))

; relop loc opand
; return-point
(define ua-1 
'(module
       ((new-frames ()) (locals (ra.12)))
       (define L.fact.4
         ((new-frames ((nfv.16)))
          (locals (ra.13 x.9 tmp.14 tmp.15 new-n.10 nfv.16 factn-1.11 tmp.17)))
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
(define ua-1-compiled 
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

(check-undead-analysis 
  (info-ref(list-ref (undead-analysis ua-1) 1) 'undead-out)
  (info-ref(list-ref ua-1-compiled 1) 'undead-out))

(check-undead-analysis 
  (info-ref(list-ref (list-ref (undead-analysis ua-1) 2) 2) 'undead-out)
  (info-ref(list-ref (list-ref ua-1-compiled 2) 2) 'undead-out))

(run-tests
   (test-suite
    ""
    (test-compiler-pass 
      undead-analysis 
      interp-asm-pred-lang-v6/locals 
      interp-asm-pred-lang-v6/undead 
      asm-pred-lang-v6/undead?))))
