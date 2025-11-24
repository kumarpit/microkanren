#lang racket

;; Key Insight: Depth-first search over infinite relations is an incomplete
;; search strategy

;; State is (ListOf (PairOf (AssociationListOf Variable μKanrenTerm) Integer))
;; Goal is a State -> (StreamOf State)

;; Stream is one-of:
;; - (PairOf State Stream) (mature stream)
;; - Procedure (immature stream)

(define empty-state '(() . 0))

;; Variables are just size-1 vectors
;; NOTE: Using a size-1 list instead would break unify because of confusion with
;;       pair? and other non-variable size-1 lists.

;; Integer -> Variable
(define (var c) (vector c))

;; Any -> Boolean
;; interp: Returns true iff the given argument represents a variable 
(define (var? v) (vector? v))

;; Variable Variable -> Boolean
;; interp: Returns true iff the two variables are equal, i.e have the same
;; variable index
(define (var=? v1 v2) (equal? (vector-ref v1 0) (vector-ref v2 0)))

;; μKanrenTerm is any term in the μKanren language 

;; SubstitutionList is an association list binding variables to terms in 
;; μKanren 

;; μKanrenTerm SubstitutionList -> μKanrenTerm
;; interp: Returns the resolved variable reference if `t` is a variable 
;; and it is bound (non-circularly) in the substitutiion list. Otherwise, 
;; if t is not a variable, returns it as is. Returns false in all other cases.
(define (walk t sublist)
  (let [(binding (and (var? t) (assp (λ (k) (var=? t k)) sublist)))]
    (if binding 
        (walk (cdr binding) sublist)
        t)))

;; Variable μKanrenTerm SubstitutionList -> SubstitutionList
;; interp: Extends the sublist with the (x . v) binding
;; NOTE: Does not check for circular references! 
(define (sublist/extend x v s) `((,x . ,v) . ,s))

;; μKanrenTerm μKanrenTerm -> Goal
;; interp: Goal constructor that only contributes values if the given terms 
;; unify in the given state
(define (≡ u v)
  (λ (s/c) 
    (let [(res (unify u v (car s/c)))]
      (if res 
          (stream/unit `(,res . ,(cdr s/c)))
          (stream/zero)))))

;; μKanrenTerm μKanrenTerm SubstitutionList -> SubstitutionList
;; interp: Given two terms, returns the SubstitutionList under which these 
;; terms "unify", false otherwise
(define (unify u v sublist) 
  (let [(u^ (walk u sublist))
        (v^ (walk v sublist))]
    (cond 
      [(and (var? u^)
            (var? v^)
            (var=? u^ v^))
       sublist]
      [(var? u^) (sublist/extend u^ v^ sublist)]
      [(var? v^) (sublist/extend v^ u^ sublist)]
      [(and (pair? u^)
            (pair? v^))
       (let [(sublist^ (unify (car u^) (car v^) sublist))]
         ;; Note the threaded sublist! Why is this important? -- Because
         ;; elements in the tail could be the same as those in the head?
         (if sublist^ (unify (cdr u^) (cdr v^) sublist^) #f))]
      [else (if (eqv? u^ v^) sublist #f)])))

;; Variable -> Goal -> Goal
;; interp: Binds formal parameter of f to a new logic variable and runs the 
;; body of f (which is a goal) with given substitution list and the now 
;; incremented fresh variable counter
(define (call/fresh f)
  (λ (s/c)
    (let [(index (cdr s/c))]
      ((f (var index)) `(,(car s/c) . ,(add1 index))))))

;; Goal Goal -> Goal
;; interp: Given two goals, produces a new goal that returns all states that
;; satisfy either of these goals
(define (disj g1 g2) (λ (s/c) (stream/mplus (g1 s/c) (g2 s/c))))

;; Goal Goal -> Goal
;; interp: Given two goals, produces a new goal that returns only those states
;; that satisfy both of the goals in question
(define (conj g1 g2) (λ (s/c) (stream/bind (g1 s/c) g2)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Stream Monad
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; NOTE: An interesting alternative exploration here would be to use a 
;; 2 continuation approach

;; ∀ A : A -> (StreamOf A)
(define (stream/unit v) (list v))

;; ∀ A : -> (StreamOf A)
(define (stream/zero) (list))

;; ∀ A : (StreamOf A) (StreamOf A) -> (StreamOf A)
(define (stream/mplus $1 $2)
  (cond [(null? $1) $2]
        [(procedure? $1) (λ () (stream/mplus $2 ($1)))] ; --> SUBTLE
        [else (cons (car $1) (stream/mplus (cdr $1) $2))]))

;; ∀ A : (StreamOf A) Goal -> (StreamOf A)
(define (stream/bind $ g)
  (cond [(null? $) '()]
        [(procedure? $) (λ () (stream/bind ($) g))]
        [else (cons (g (car $)) (stream/bind (cdr $) g))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Private
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; ∀ A, B : (A A -> Boolean) (AssociationListOf A B) -> (PairOf A B)
;; interp: Ports the scheme assp function to racket
(define (assp pred alist)
  (for/first ([pair alist] #:when (pred (car pair)))
    pair))

(define-syntax Zzz
  (syntax-rules ()
    ((_ g) (λ (s/c) (λ () (g s/c))))))

(define-syntax conj*
  (syntax-rules ()
    ((_ g) (Zzz g))
    ((_ g0 g ...) (conj (Zzz g0) (conj* g ...)))))

(define-syntax disj*
  (syntax-rules ()
    ((_ g) (Zzz g))
    ((_ g0 g ...) (disj (Zzz g0) (disj* g ...)))))

(define-syntax conde
  (syntax-rules ()
    ((_ [g0 g ...] ...) (disj* (conj* g0 g ...) ...))))

(define-syntax fresh
  (syntax-rules ()
    ((_ () g0 g ...) (conj* g0 g ...))
    ((_ (x0 x ...) g0 g ...)
     (call/fresh (λ (x0) (fresh (x ...) g0 g ...))))))

(define (pull $) (if (procedure? $) (pull ($)) $))

(define (take-all $)
  (let [($^ (pull $))]
    (if (null? $^)
        '()
        (cons (pull (car $^)) (take-all (cdr $^)))))) ; -> the original
; implementation didn't have a pull on the car here, not sure why?
; since *every* goal is Zzz, the cardinality of the stream is not established
; when take-all is called (i.e a single pull can "explode" into multiple
; mature results - an example of this is the a-and-b goal below).

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Examples
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define a-and-b (fresh (a b)
                       (≡ a 7)
                       (disj* (≡ b 5) (≡ b 6))))
(take-all (a-and-b empty-state))

(define (fives x) (disj* (≡ x 5) (fives x)))
(pull ((call/fresh fives) empty-state))

(define (sixes x) (disj* (≡ x 6) (sixes x)))
(pull ((call/fresh sixes) empty-state))

(define a-rather-complex-example
  (fresh (x y)
         (disj (≡ x 5) (≡ x 4))
         (disj (≡ y 4) (≡ y 3))
         (≡ `(,x ,y) `(,y ,x))))
(pull (a-rather-complex-example empty-state))

(define fives-and-sixes (fresh (x) (disj (fives x) (sixes x))))
(pull (fives-and-sixes empty-state))