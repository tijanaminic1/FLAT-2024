#lang fsm
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Quiz 8, p.313
;; Tijana Minic, Oliwia Kempinski
;; Due: Tuesday

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Implement, (cfg-ks G), a cfg constructor for L*

;; Prove:
;; Context-free languages are closed under Kleene star.
;; by showing that L* = L((cfg-ks G)), where L is an arbitrary context-free language such that L = L(G).

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Syntactic Categories
;;  S = words that start with n a and end with n b

;; L = a^nb^n
(define a2nb2n (make-cfg '(S)
                         '(a b)
                         `((S -> ,EMP)
                           (S -> aSb))
                         'S))

;; Tests for a^nb^n
(check-equal? (grammar-derive a2nb2n '(b b b))
              "(b b b) is not in L(G).")
(check-equal? (grammar-derive a2nb2n '(a b a))
              "(a b a) is not in L(G).")
(check-equal? (grammar-derive a2nb2n '(a b))
              '(S -> aSb -> ab))
(check-equal? (grammar-derive a2nb2n '(a a a b b b))
              '(S -> aSb -> aaSbb -> aaaSbbb -> aaabbb))

;.................................................

; Syntactic Categories
;;  S = words such that number of b > number of a
;;  A = words such that number of b >= number of a

;; L = w | w in (ab)* AND w has more b than a
(define numb>numa (make-cfg '(S A)
                            '(a b)
                            `((S ,ARROW b)
                              (S ,ARROW AbA)
                              (A ,ARROW AaAbA)
                              (A ,ARROW AbAaA)
                              (A ,ARROW ,EMP)
                              (A ,ARROW bA))
                            'S))

;; Tests for numb>numa
(check-equal? (grammar-derive numb>numa '(a b))
              "(a b) is not in L(G).")
(check-equal? (grammar-derive numb>numa '(a b a))
              "(a b a) is not in L(G).")
(check-equal? (grammar-derive numb>numa '(a a a a a))
              "(a a a a a) is not in L(G).")
(check-equal? (grammar-derive numb>numa '(b b b))
              '(S -> AbA -> bA -> bbA -> bbbA -> bbb))

;.................................................

; Syntactic Categories
;;  S = words such that number of a = 0 v number of a = 3
;;  B = words such that number of a = 1
;;  C = words such that number of a = 2

;; cfg for L = {w | the number of as in w is a multiple of 3}
(define MULT3-as (make-cfg '(S B C)
                           '(a b)
                           `((S ,ARROW ,EMP) 
                             (S ,ARROW aB)
                             (S ,ARROW bS)
                             (B ,ARROW aC)
                             (B ,ARROW bB)
                             (C ,ARROW aS)
                             (C ,ARROW bC))
                           'S))
;; Tests for MULT3-as
(check-equal? (grammar-derive MULT3-as '(b b a b b))
              "(b b a b b) is not in L(G).")
(check-equal? (grammar-derive MULT3-as '(b b a b b a))
              "(b b a b b a) is not in L(G).")
(check-equal? (grammar-derive MULT3-as '(b b a b a b a a b))
              "(b b a b a b a a b) is not in L(G).")
(check-equal? (grammar-derive MULT3-as '())
              "The word () is too short to test.")
(check-equal? (grammar-derive MULT3-as '(a a a))
              '(S -> aB -> aaC -> aaaS -> aaa))
(check-equal? (grammar-derive MULT3-as '(b b a a b a b b))
              '(S -> bS -> bbS -> bbaB -> bbaaC -> bbaabC ->
                  bbaabaS -> bbaababS -> bbaababbS ->  bbaababb))

;.................................................

; Syntactic Categories
;;  S: w = ε v w = a {ab}* a v w = b {ab}* b, reads a and b pairs at start and end of w
;;  A: w = a {ab}* a v w = b {ab}* b, reads singular as and bs within the palindrome

;; L = w | w is a palindrome
(define palindrome (make-cfg '(S A)
                             '(a b)
                             '((S -> ε)
                               (S -> aSa)
                               (S -> bSb)
                               (S -> aAa)
                               (S -> bAb)
                               (A -> aS)
                               (A -> bS)) 
                             'S))

;; Tests for palindrome
(check-equal? (grammar-derive palindrome '(a a))
              '(S -> aSa -> aa))
(check-equal? (grammar-derive palindrome '(b b))
              '(S -> bSb -> bb))
(check-equal? (grammar-derive palindrome '(a b a))
              '(S -> aAa -> abSa -> aba))
(check-equal? (grammar-derive palindrome '(a b b a))
              '(S -> aSa -> abSba -> abba))
(check-equal? (grammar-derive palindrome '(a b))
              "(a b) is not in L(G).")
(check-equal? (grammar-derive palindrome '(a b a b a))
              '(S -> aSa -> abAba -> abaSba -> ababa))
(check-equal? (grammar-derive palindrome '(a b a b b a))
              "(a b a b b a) is not in L(G).")
(check-equal? (grammar-derive palindrome '(a b a a a b a))
              '(S -> aSa -> abSba -> abaAaba -> abaaSaba -> abaaaba))
(check-equal? (grammar-derive palindrome '(a b a b))
              "(a b a b) is not in L(G).")
(check-equal? (grammar-derive palindrome '(b a b a b))
              '(S -> bSb -> baAab -> babSab -> babab))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; cfg -> cfg
;; Purpose: Build a cfg for the Kleene star of the given cfg
(define (cfg-ks cfg)
  (let* [(nts (grammar-nts cfg))  
         (sigma (grammar-sigma cfg))
         (rules (grammar-rules cfg)) 
         (start (grammar-start cfg))
         (new-start (generate-symbol 'S nts))
         (final-rules (filter (lambda (x) (or (equal? (third x) EMP)
                                              (member (third x) sigma))) rules))
         (final-nts (map (lambda (x) (first x)) final-rules))]
    (make-cfg (cons new-start nts)
              sigma
              (append
               (list (list new-start ARROW EMP))
               (list (list new-start ARROW (los->symbol (list start new-start))))
               rules)
              new-start)))


;; Tests for cfg-concat
(check-equal? (last (grammar-derive palindrome  '(b b a b b b a b)))  
              'bbabbbab)
(check-equal? (last (grammar-derive (cfg-ks palindrome) '(b b a b b a b a)))  
              'bbabbaba)
(check-equal? (last (grammar-derive (cfg-ks a2nb2n) '(a a b b)))  
              'aabb)
(check-equal? (last (grammar-derive (cfg-ks a2nb2n) '(a a b b a a b b)))  
              'aabbaabb)
(check-equal? (last (grammar-derive (cfg-ks a2nb2n) '(a a b b a a b b a a b b)))  
              'aabbaabbaabb)
(check-equal? (grammar-derive (cfg-ks palindrome) '(a b b b b)) "(a b b b b) is not in L(G).")
(check-equal? (grammar-derive (cfg-ks a2nb2n) '(a b b b b)) "(a b b b b) is not in L(G).")























;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
