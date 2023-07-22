#lang racket

(provide generate-x64)

(require
 cpsc411/compiler-lib
 cpsc411/2c-run-time
 cpsc411/langs/v6
 cpsc411/graph-lib
 racket/trace
 rackunit)


#| Paren-x64-v6: 
  p	 	::=	 	(begin s ...)
 	 	 	 	 
  s	 	::=	 	(set! addr int32) 
 	 	|	 	(set! addr trg) 
 	 	|	 	(set! reg loc) ;
 	 	|	 	(set! reg triv) ;
 	 	|	 	(set! reg_1 (binop reg_1 int32))  ;
 	 	|	 	(set! reg_1 (binop reg_1 loc)) ;
 	 	|	 	(with-label label s) ;
 	 	|	 	(jump trg)  ;
 	 	|	 	(compare reg opand)  ;
 	 	|	 	(jump-if relop label) ;
 	 	 	 	 
  trg	 	::=	 	reg
 	 	|	 	label
 	 	 	 	 
  triv	 	::=	 	trg
 	 	|	 	int64
 	 	 	 	 
  opand	 	::=	 	int64
 	 	|	 	reg
 	 	 	 	 
  loc	 	::=	 	reg
 	 	|	 	addr
 	 	 	 	 
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
 	 	|	 	r10
 	 	|	 	r11
 	 	|	 	r12
 	 	|	 	r13
 	 	|	 	r14
 	 	|	 	r15
 	 	 	 	 
  addr	 	::=	 	(fbp - dispoffset)
 	 	 	 	 
  fbp	 	::=	 	frame-base-pointer-register?
 	 	 	 	 
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

;; Exercise 19
;; Compile the Paren-x64 v6 into valid sequence of x64 instructions represented in its string form
;; reference: went to Paulette's office hours and tutorial for help
(define (generate-x64 p)

  ;; p -> string
  ;;
  ;; compiles p into valid sequence of x64 represented in its string form by appending all 
  ;; the compiled string sequences
  (define (program->x64 p) 
    (match p
      [`(begin ,s ...) 
      (apply string-append (map statement->x64 s))]))

  ;; s -> string
  ;;
  ;; compiles s into valid sequence of x64 represented in its string form 
  (define (statement->x64 s)
  (match s 
      [`(set! ,addr ,int32) 
      #:when (and (int32? int32) (addr? addr)) 
      (format "mov ~a, ~a\n" (loc->x64 addr) int32)]
      [`(set! ,addr ,trg)
       #:when (and (trg? trg) (addr? addr)) 
       (format "mov ~a, ~a\n" (loc->x64 addr) trg)]
      [`(set! ,reg ,loc) 
      #:when (and (loc? loc) (register? reg)) 
      (format "mov ~a, ~a\n" reg (loc->x64 loc))] 
      [`(set! ,reg ,triv) 
      #:when (and (register? reg) (triv? triv))
      (format "mov ~a, ~a\n" reg triv)]
 	 	  [`(set! ,reg_1 (,binop ,reg_1 ,int32)) 
      #:when (and (int32? int32) (register? reg_1)) 
      (format "~a ~a, ~a\n" (binop->ins binop) reg_1 int32)] 
 	 	  [`(set! ,reg_1 (,binop ,reg_1 ,loc)) 
      #:when (and (register? reg_1) (loc? loc)) 
      (format "~a ~a, ~a\n" (binop->ins binop) reg_1 (loc->x64 loc))]
      [`(with-label ,label ,s) 
      #:when(label? label) 
      (format "~a:\n~a" label (statement->x64 s))]
      [`(jump ,trg) 
      #:when(trg? trg) 
      (format "jmp ~a\n" trg)] 
      [`(compare ,reg ,opand) 
      #:when(and (register? reg) (opand? opand)) 
      (format "cmp ~a, ~a\n" reg opand)]
      [`(jump-if ,relop ,label) 
      #:when(and (relop? relop) (label? label)) 
      (format "j~a ~a\n" (relop->x64 relop) (sanitize-label label))])) 

  ;; relop -> x64 string
  ;; 
  ;; translates relop symbols into the string format of the comparison flags
  (define (relop->x64 relop)
    (match relop
     ['< "l"]
     ['<= "le"]
     ['= "e"]
     ['>= "ge"]
     ['> "g"]
     ['!= "ne"])) 

  ;; loc -> x64 string
  ;;
  ;; translates locations into the string format 
  (define (loc->x64 loc)
    (if (register? loc) 
      loc
      (format "QWORD [~a]" (string-join (map ~a loc) " "))))

  ;; binop -> x64 string
  ;;
  ;; translates binop symbols into the string format of the binary operations
  (define (binop->ins b)
    (match b
     ['+ "add"]
     ['* "imul"]
     ['- "sub"]))

  ;; trg -> boolean
  ;; returns true if trg is a register or label
  (define (trg? trg)
    (or (register? trg) (label? trg)))

  ;; triv -> boolean
  ;; returns true if triv t is a triv? or int64
  (define (triv? triv)
    (or (trg? triv) (int64? triv)))
  
  ;; opand -> boolean
  ;; returns true if opand t is an int64 or opand
  (define (opand? opand)
    (or (int64? opand) (register? opand)))

  ;; loc -> boolean
  ;; returns true if loc is a register or address
  (define (loc? loc)
    (or (register? loc) (addr? loc)))
  
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

  ;; addr -> boolean
  ;; returns true if addr is a addr?
  ;; else return false
  (define (addr? addr)
     (and (pair? addr)   
          (and  (frame-base-pointer-register? (list-ref addr 0)))
                (eq? (list-ref addr 1) '-)
                (dispoffset? (list-ref addr 2))))

  (program->x64 p))

(module+ test 
  (require
  rackunit
   rackunit/text-ui
   cpsc411/langs/v6
   cpsc411/test-suite/public/v6
   cpsc411/test-suite/utils)

; with-label
; set reg triv
; jump-if relop label
; jump
; compare reg opand
; set reg (binop reg int32)
(define g-3 
  '(begin
    (with-label L.__main.3 (set! r15 r15))
    (set! r14 0)
    (compare r14 1)
    (jump-if > L.__nested.1)
    (jump L.__nested.2)
    (with-label L.__nested.1 (set! rax 0))
    (jump r15)
    (with-label L.__nested.2 (set! rax 0))
    (set! rax (+ rax 1))
    (jump r15)))
(define g-3-compiled 
  "L.__main.3:
  mov r15, r15
  mov r14, 0
  cmp r14, 1
  jg L.__nested.1
  jmp L.__nested.2
  L.__nested.1:
  mov rax, 0
  jmp r15
  L.__nested.2:
  mov rax, 0
  add rax, 1
  jmp r15")
(check-equal?
  (parameterize 
    ([current-pass-list
        (list generate-x64
              wrap-x64-run-time
              wrap-x64-boilerplate)])
    (execute g-3))
  (parameterize 
    ([current-pass-list
       (list wrap-x64-run-time
             wrap-x64-boilerplate)])
  (execute g-3-compiled)))

; set reg (binop reg loc)
(define g-2 
'(begin
  (with-label L.__main.6 (set! r15 r15))
  (set! r14 2)
  (set! r13 1)
  (compare r13 r14)
  (jump-if < L.tmp.4)
  (jump L.tmp.5)
  (with-label L.tmp.4 (jump L.tmp.2))
  (with-label L.tmp.5 (compare r14 10))
  (jump-if < L.tmp.1)
  (jump L.tmp.2)
  (with-label L.tmp.1 (set! r14 r13))
  (set! r14 (+ r14 r13))
  (jump L.tmp.3)
  (with-label L.tmp.2 (set! r14 r14))
  (jump L.tmp.3)
  (with-label L.tmp.3 (set! rax 2))
  (jump r15)))

(define g-2-compiled 
  "L.__main.6:
  mov r15, r15
  mov r14, 2
  mov r13, 1
  cmp r13, r14
  jl L.tmp.4
  jmp L.tmp.5
  L.tmp.4:
  jmp L.tmp.2
  L.tmp.5:
  cmp r14, 10
  jl L.tmp.1
  jmp L.tmp.2
  L.tmp.1:
  mov r14, r13
  add r14, r13
  jmp L.tmp.3
  L.tmp.2:
  mov r14, r14
  jmp L.tmp.3
  L.tmp.3:
  mov rax, 2
  jmp r15")

(check-equal?
  (parameterize 
    ([current-pass-list
        (list generate-x64
              wrap-x64-run-time
              wrap-x64-boilerplate)])
    (execute g-2))
  (parameterize 
    ([current-pass-list
       (list wrap-x64-run-time
             wrap-x64-boilerplate)])
  (execute g-2-compiled)))

; set addr int32
; set adr trg
(define g-4 
  '(begin
      (with-label L.main.2 (set! r15 r15))
      (set! (rbp - 8) 10)
      (set! (rbp - 0) 3)
      (set! r15 r15)
      (jump L.swap.1)
      (with-label L.swap.1 (set! (rbp - 16) r15))
      (set! r14 (rbp - 0))
      (set! r15 (rbp - 8))
      (compare r15 r14)
      (jump-if > L.main.3)
      (jump L.main.4)
      (with-label L.rp.1 (set! rbp (+ rbp 24)))
      (set! r15 rax)
      (set! rax r15)
      (set! r10 (rbp - 16))
      (jump r10)
      (with-label L.main.3 (set! rax r14))
      (set! r10 (rbp - 16))
      (jump r10)
      (with-label L.main.4 (set! rbp (- rbp 24)))
      (set! (rbp - 8) r14)
      (set! (rbp - 0) r15)
      (set! r15 L.rp.1)
      (jump L.swap.1)))
(define g-4-compiled
  "L.main.2:
  mov r15, r15
  mov QWORD [rbp - 8], 10
  mov QWORD [rbp - 0], 3
  mov r15, r15
  jmp L.swap.1
  L.swap.1:
  mov QWORD [rbp - 16], r15
  mov r14, QWORD [rbp - 0]
  mov r15, QWORD [rbp - 8]
  cmp r15, r14
  jg L.main.3
  jmp L.main.4
  L.rp.1:
  add rbp, 24
  mov r15, rax
  mov rax, r15
  mov r10, QWORD [rbp - 16]
  jmp r10
  L.main.3:
  mov rax, r14
  mov r10, QWORD [rbp - 16]
  jmp r10
  L.main.4:
  sub rbp, 24
  mov QWORD [rbp - 8], r14
  mov QWORD [rbp - 0], r15
  lea r15, [rel L.rp.1]
  jmp L.swap.1")
  (check-equal?
    (parameterize 
      ([current-pass-list
          (list generate-x64
                wrap-x64-run-time
                wrap-x64-boilerplate)])
      (execute g-2))
    (parameterize 
      ([current-pass-list
        (list wrap-x64-run-time
              wrap-x64-boilerplate)])
    (execute g-2-compiled)))

(define g-1
'(begin
  (with-label L.__main.2 (set! r15 r15))
  (set! (rbp - 8) 2)
  (set! (rbp - 0) 1)
  (set! r15 r15)
  (jump L.swap.1)
  (with-label L.swap.1 (set! (rbp - 16) r15))
  (set! r14 (rbp - 0))
  (set! r15 (rbp - 8))
  (compare r15 r14)
  (jump-if < L.__nested.3)
  (jump L.__nested.4)
  (with-label L.rp.1 (set! rbp (+ rbp 24)))
  (set! r15 rax)
  (set! rax r15)
  (set! r10 (rbp - 16))
  (jump r10)
  (with-label L.__nested.3 (set! rax r14))
  (set! r10 (rbp - 16))
  (jump r10)
  (with-label L.__nested.4 (set! rbp (- rbp 24)))
  (set! (rbp - 8) r14)
  (set! (rbp - 0) r15)
  (set! r15 L.rp.1)
  (jump L.swap.1)))
  
(define g-1-compiled
"L.__main.2:
mov r15, r15
mov QWORD [rbp - 8], 2
mov QWORD [rbp - 0], 1
mov r15, r15
jmp L.swap.1
L.swap.1:
mov QWORD [rbp - 16], r15
mov r14, QWORD [rbp - 0]
mov r15, QWORD [rbp - 8]
cmp r15, r14
jl L.__nested.3
jmp L.__nested.4
L.rp.1:
add rbp, 24
mov r15, rax
mov rax, r15
mov r10, QWORD [rbp - 16]
jmp r10
L.__nested.3:
mov rax, r14
mov r10, QWORD [rbp - 16]
jmp r10
L.__nested.4:
sub rbp, 24
mov QWORD [rbp - 8], r14
mov QWORD [rbp - 0], r15
mov r15, L.rp.1
jmp L.swap.1
")
(check-equal? (generate-x64 g-1) g-1-compiled)

; 
(check-equal?
(parameterize ([current-pass-list
       (list generate-x64
             wrap-x64-run-time
             wrap-x64-boilerplate)])
  (execute '(begin
      (set! (rbp - 0) 10)
      (set! (rbp - 8) 37)
      (set! rax (rbp - 0))
      (set! rax (+ rax (rbp - 8))))))
  (parameterize ([current-pass-list
       (list wrap-x64-run-time
             wrap-x64-boilerplate)])
  (execute "mov QWORD [rbp - 0], 10\nmov QWORD [rbp - 8], 37\nmov rax, QWORD [rbp - 0]\nadd rax, QWORD [rbp - 8]\n")))

(check-equal?
(parameterize ([current-pass-list
       (list generate-x64
             wrap-x64-run-time
             wrap-x64-boilerplate)])
  (execute '(begin
      (set! rax 0)
      (set! rbx 0)
      (set! r9 42)
      (set! rax (+ rax r9)))))
  (parameterize ([current-pass-list
       (list wrap-x64-run-time
             wrap-x64-boilerplate)])
  (execute "mov rax, 0\nmov rbx, 0\nmov r9, 42\nadd rax, r9\n")))

(parameterize ([current-pass-list '()])
  (run-tests
   (test-suite
    ""
    (test-compiler-pass 
      (compose wrap-x64-boilerplate wrap-x64-run-time generate-x64) 
      interp-paren-x64-v6 execute 
      string?)))))

