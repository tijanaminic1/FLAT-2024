#lang fsm
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Quiz 4
;; p.120, Nr.17
;; Tijana Minic, Oliwia Kempinski
;; Due: Thursday

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#| Mr. Hacker claims to have designed his own version of EVEN-A-ODD-B.
His claim is highly suspicious because all he has done is add states that
are unreachable from the start state. Design and implement a dfa constructor
that takes as input a dfa, M, and that returns the dfa, M', obtained by removing
the unreachable states from M. Prove that L(M) = L(M'). Why is it important to
remove unreachable states? |#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Sample dfas

;; States
;; S: even number of a and even number of b, start state
;; M: odd number of a and odd number of b
;; N: even number of a and odd number of b, final state
;; P: odd number of a and even number of b

;; L = {w | w ∈ {ab}∗ ∧ w has an even number of as and an odd number of bs}
;; Name: EVEN-A-ODD-B 
;; Σ: '(a b)
(define EVEN-A-ODD-B
  (make-dfa '(S M N P X Y Z ds)
            '(a b)
            'S
            '(N)
            '((S a P)
              (S b N)
              (M a N)
              (M b P)
              (N a M)
              (N b S)
              (P a S)
              (P b M)
              (X a Y)
              (Y b Y)
              (Y a ds)
              (X b ds)
              (Z a ds)
              (Z b ds)
              (ds a ds)
              (ds b ds))
            'no-dead))

(define EVEN-A-ODD-B2
  (make-dfa '(S M N P X Y Z ds)
            '(a b)
            'S
            '(N)
            '((S a P)
              (S b N)
              ;(M a N)
              (M b P)
              (N a M)
              (N b S)
              (P a S)
              (P b M)
              (X a Y)
              (Y b Y)
              (Y a ds)
              (X b ds)
              (Z a ds)
              (Z b ds)
              (ds a ds)
              (ds b ds)
              (M a Z))
            'no-dead))

(define EVEN-A-ODD-B3
  (make-dfa '(S M N P X Y Z ds)
            '(a b)
            'S
            '(N)
            '((S a P)
              (S b N)
              ;(M a N)
              (M b P)
              (N a M)
              (N b S)
              (P a S)
              (P b M)
              (X a Y)
              (Y b Y)
              (Y a ds)
              (X b ds)
              (Z a ds)
              (Z b ds)
              (ds a ds)
              (ds b ds)
              (M a X))
            'no-dead))

;.................................................

;; Tests 
(check-equal? (sm-apply EVEN-A-ODD-B '()) 'reject)
(check-equal? (sm-apply EVEN-A-ODD-B '(a b b a)) 'reject)
(check-equal? (sm-apply EVEN-A-ODD-B '(b a b b a a)) 'reject)
(check-equal? (sm-apply EVEN-A-ODD-B '(a b)) 'reject)
(check-equal? (sm-apply EVEN-A-ODD-B '(a b b b b)) 'reject)
(check-equal? (sm-apply EVEN-A-ODD-B '(a a b)) 'accept)
(check-equal? (sm-apply EVEN-A-ODD-B '(b a b b a)) 'accept)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; dfa state (listof states) (listof states)
;; Purpose:
;; Accumulator invariants:
;;  reached-states = 
(define (reachable-from-start? M state reachable-states reached-states)
  (cond ((empty? reachable-states) #f)
        ((member state reachable-states) #t)
        (else            
         (reachable-from-start?
          M
          state
          (filter (lambda (z) (not (member z reached-states)))
                  (map (lambda (y) (caddr y))
                       (filter (lambda (x) (member (car x) reachable-states)) (sm-rules M))))
          (append reachable-states reached-states)))))

(sm-graph EVEN-A-ODD-B)
(reachable-from-start? EVEN-A-ODD-B 'N '(N P) '(S))
(reachable-from-start? EVEN-A-ODD-B 'M '(N P) '(S))
(reachable-from-start? EVEN-A-ODD-B 'K '(N P) '(S))
(reachable-from-start? EVEN-A-ODD-B 'Y '(N P) '(S))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; dfa -> dfa
;; Purpose: Take as input a dfa, M, and return the dfa, M', obtained by removing
;;          the unreachable states from M
(define (trim-dfa M)
  
  (let* ((valid-states
          (remove-duplicates
           (filter (lambda (x) (or (eq? x (sm-start M))
                                   (reachable-from-start? M
                                                          x
                                                          (map (lambda (z) (caddr z)) (filter (lambda (y) (eq? (car y) (sm-start M))) (sm-rules M)))
                                                          (list (sm-start M)))))
                   (sm-states M))))
         (new-rules
          (remove-duplicates
           (filter (lambda (x) (or (member (car x) valid-states)
                                   (member (cadr x) valid-states))) (sm-rules M))))
         (new-sigma
          (remove-duplicates (map (lambda (x) (cadr x)) new-rules)))
         (new-finals
          (remove-duplicates
           (filter (lambda (x) (member x valid-states)) (sm-finals M)))))
    (make-dfa valid-states
              new-sigma
              (sm-start M)
              new-finals
              new-rules
              'no-dead)))

(sm-graph (trim-dfa EVEN-A-ODD-B))
(sm-graph (trim-dfa EVEN-A-ODD-B2))
(sm-graph (trim-dfa EVEN-A-ODD-B3))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Proof

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;




