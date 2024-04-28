#lang fsm
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Final
;; Due: May 13
;; Oliwia Kempinski, Tijana Minic

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Implement the constructor to build an mttm from a pda.
;; Test and proof. 

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Sample pdas

;; L = {a^n b^n | n >= 0}
;; Σ = {a b}
;; States
;; S: ci = a* = stack, start state
;; M: ci = (append (listof a) (listof b))
;;         ∧ stack = a*
;;         ∧ |ci as| = |stack| + |ci bs|
;; F: ci = (append (listof a) (listof b))
;;         ∧ |stack| = 0
;;         ∧ |ci as| = |ci bs|, final state
;; The stack is a (listof a)
(define a^nb^n (make-ndpda '(S M F)
                           '(a b)
                           '(a)
                           'S
                           '(F)
                           '(((S ε ε) (M ε))
                             ((S a ε) (S (a)))
                             ((M b (a)) (M ε))
                             ((M ε ε) (F ε)))))

;(sm-visualize a^nb^n)
(sm-graph a^nb^n)

;; Tests for a^nb^n
(check-equal? (sm-apply a^nb^n '(a)) 'reject)
(check-equal? (sm-apply a^nb^n '(b b)) 'reject)
(check-equal? (sm-apply a^nb^n '(a b b)) 'reject)
(check-equal? (sm-apply a^nb^n '(a b a a b b)) 'reject)
(check-equal? (sm-apply a^nb^n '()) 'accept)
(check-equal? (sm-apply a^nb^n '(a a b b)) 'accept)

;.................................................

;; L = {w | w has an equal number of as and bs}
;; Σ = {a b}
;; States:
;;  S: ci = number as in ci = nunber bs in ci + number bs in stack, start state, final state
;; Stack:
;;  The stack is a (listof a) or (listof b)
(define as=bs (make-ndpda '(S)
                          '(a b)
                          '(a b)
                          'S
                          '(S)
                          '(((S a ε) (S (b)))
                            ((S b ε) (S (a)))
                            ((S a (a)) (S ε))
                            ((S b (b)) (S ε)))))

;(sm-visualize as=bs)
(sm-graph as=bs)

;; Tests for as=bs
(check-equal? (sm-apply as=bs '(a)) 'reject)
(check-equal? (sm-apply as=bs '(b b)) 'reject)
(check-equal? (sm-apply as=bs '(a b b)) 'reject)
(check-equal? (sm-apply as=bs '(a b a a b b)) 'accept)
(check-equal? (sm-apply as=bs '()) 'accept)
(check-equal? (sm-apply as=bs '(a a b b)) 'accept)

;.................................................

;; L = {a^i b^j | i ≤ j ≤ 2i}
;; Σ = {a b}
;; States:
;;  S: number bs in stack = 2* number as in ci, ci = a*, stack = b*, start state
;;  X: number as in ci <= (number bs in stack + number bs in ci) <= 2* number as in ci, ci = a*b*, stack = b*, final state
;; Stack:
;;  Stack is a (listof b), max of bs that can be read
(define a^ib^j (make-ndpda '(S X)
                           '(a b)
                           '(b)
                           'S
                           '(X)
                           '(((S ε ε) (X ε))
                             ((S a ε) (S (b b)))
                             ((X b (b)) (X ε))
                             ((X b (b b)) (X ε)))))

;(sm-visualize a^ib^j)
(sm-graph a^ib^j)

;; Tests for a^ib^j
(check-equal? (sm-apply a^ib^j '(a a b)) 'reject)
(check-equal? (sm-apply a^ib^j '(b b)) 'reject)
(check-equal? (sm-apply a^ib^j '(a b b)) 'accept)
(check-equal? (sm-apply a^ib^j '(a b a a b b)) 'reject)
(check-equal? (sm-apply a^ib^j '()) 'accept)
(check-equal? (sm-apply a^ib^j '(a a b b)) 'accept)

;.................................................

;; L = {w | w is a palindrome}
;; Σ = {a b}
;; States:
;;  S: ci = w and stack = w^R, start state
;;  X: ci = uvxv^R, s = u^R, |x| = 1 if (odd? vxv^R)
;;                               = 0 if (even? vxv^R)
;; Is this condition strong enough for X to be a final state?
;;  s = EMP ==> u^R = EMP ==> u = EMP ==> ci = vxv^R ==> ci is a palindrome :-)
(define palindrome (make-ndpda '(S X)
                               '(a b)
                               '(a b)
                               'S
                               '(X)
                               '(((S ε ε) (X ε))
                                 ((S a ε) (X ε))
                                 ((S b ε) (X ε))
                                 ((S a ε) (S (a)))
                                 ((S b ε) (S (b)))
                                 ((X a (a)) (X ε))
                                 ((X b (b)) (X ε)))))

;(sm-visualize palindrome)
(sm-graph palindrome)

;; Tests for palindrome
(check-equal? (sm-apply palindrome '(a b a)) 'accept)
(check-equal? (sm-apply palindrome '(a b a b b a b a)) 'accept)
(check-equal? (sm-apply palindrome '(b)) 'accept)
(check-equal? (sm-apply palindrome '(a b)) 'reject)
(check-equal? (sm-apply palindrome '(b a b a)) 'reject)
(check-equal? (sm-apply palindrome '(a b)) 'reject)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Q: push state
;; R: pop state

(define new-anbn (make-mttm `(S M F Q R Y)
                            '(a b)
                            'S
                            '(Y)
                            `(((S (a _)) (Q (a R)))
                              ((S (a a)) (Q (a R)))
                              ((S (a b)) (Q (a R)))
                              ((Q (a _)) (M (R a)))
                              ((Q (a _)) (S (R a)))
      
                              ((M (b a)) (R (b _)))
                              ((R (b _)) (F (R L)))
                              ((R (b _)) (M (R L)))

                             ((F (_ _)) (Y (_ _))))
                            2
                            'Y))

;(gen-nt '(S M F Q R Y N))

(sm-graph a^nb^n)
(sm-graph new-anbn)
(sm-showtransitions new-anbn '(a a b b))
;(sm-visualize new-anbn)




































