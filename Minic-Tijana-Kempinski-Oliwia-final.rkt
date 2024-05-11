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

#;(define new-anbn (make-mttm '(S M F Q R Y)
                              '(a b)
                              'S
                              '(Y)
                              '(((S (a _)) (Q (a R)))
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

(define new-anbn (make-mttm '(S M F Q R Y)
                            '(a b)
                            'S
                            '(Y)
                            '(((S (a _)) (Q (a R)))
                              ((S (a a)) (Q (a R)))
                              ((S (a b)) (Q (a R)))
                              ;((Q (a _)) (M (R a)))
                              ((Q (a _)) (S (R a)))

                              ((S (a a)) (M (a a)))
                              ((S (b b)) (M (b b)))
                              ((S (_ _)) (M (_ _)))
                              ((S (a b)) (M (a b)))
                              ((S (b a)) (M (b a)))
                              ((S (a _)) (M (a _)))
                              ((S (_ a)) (M (_ a)))
                              ((S (b _)) (M (b _)))
                              ((S (_ b)) (M (_ b)))
                              
      
                              ((M (b a)) (R (b _)))
                              ;((R (b _)) (F (R L)))

                              ((M (a a)) (F (a a)))
                              ((M (b b)) (F (b b)))
                              ((M (_ _)) (F (_ _)))
                              ((M (a b)) (F (a b)))
                              ((M (b a)) (F (b a)))
                              ((M (a _)) (F (a _)))
                              ((M (_ a)) (F (_ a)))
                              ((M (b _)) (F (b _)))
                              ((M (_ b)) (F (_ b)))
                              
                              ((R (b _)) (M (R L)))

                              ((F (_ _)) (Y (_ _))))
                            2
                            'Y))

;(gen-nt '(S M F Q R Y N))

(sm-graph a^nb^n)
(sm-graph new-anbn)
(sm-showtransitions new-anbn '(a a b b))
;(sm-visualize new-anbn)

(define anbn (make-ndpda '(S M F)
                           '(a b)
                           '(a c b)
                           'S
                           '(F)
                           '(((S ε ε) (M ε))
                             ((S a ε) (S (a)))
                             ((M a (b)) (M (c)))
                             ((M ε ε) (F ε)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; pda -> mttm
;; Purpose: Given a pda, make an mttm
(define (pda->mttm p)

  ;; pda-rule -> boolean
  ;; Purpose: Given a rule, determine if read is not empty
  (define (read? r)
    (not (eq? EMP (second (first r)))))
  ;; pda-rule -> boolean
  ;; Purpose: Given a rule, determine if pop is not empty
  (define (pop? r)
    (not (eq? EMP (third (first r)))))
  ;; pda-rule -> boolean
  ;; Purpose: Given a rule, determine if push is not empty
  (define (push? r)
    (not (eq? EMP (second (second r)))))

  ;; (listof mttm-rule) -> (listof state)
  ;; Purpose: Get all lists from mttm-rules 
  (define (get-states-from-mttm-rules r)
    (remove-duplicates
     (append (map (lambda (x) (first (first x))) r)
             (map (lambda (x) (first (second x))) r))))

  ;; pda-rule -> (listof mttm-rule)
  ;; Purpose: Make mttm rules for a pda rule that only pops and pushes something
  ;; Accumulator invariants:
  ;;  stateacc = keep track of which states have already been generated
  (define (new-read-pop-push-rules rule stateacc)
    (let ((fromst (first (first rule)))
          (tost (first (second rule)))
          (read (second (first rule)))
          (pop (third (first rule)))
          (push (reverse (second (second rule))))
          (sigma (cons BLANK (sm-sigma p))))
      ;; pushlist -> (listof mttm-rule)
      ;; Purpose: Traverse the push list
      ;; Accumulator invariants:
      ;;  stateacc2 = keep track of which states have already been generated
      (define (push-helper p new-fromst stateacc2)
        (cond ((= 1 (length p))
               (list `((,new-fromst (,read ,BLANK)) (,tost (R ,(car p))))))
              (else
               (let* ((newst (gen-state stateacc2))
                      (new-acc (cons newst stateacc2)))
                 (append (list `((,new-fromst (,read ,BLANK)) (,new-fromst (,read ,(car p)))))
                         (list `((,new-fromst (,read ,(car p))) (,newst (,read R))))
                         (push-helper (cdr p) newst new-acc))))))
      ;; poplist -> (listof mttm-rule)
      ;; Purpose: Traverse the pop list
      ;; Accumulator invariants:
      ;;  stateacc2 = keep track of which states have already been generated
      (define (new-read-pop-push-rules-helper p new-fromst stateacc2)
        (cond ((= 1 (length p))
               (let* ((newst (gen-state stateacc2))
                      (new-acc (cons newst stateacc2))
                      (newst2 (gen-state new-acc))
                      (new-acc2 (cons newst2 new-acc))
                      (newst3 (gen-state new-acc2))
                      (new-acc3 (cons newst3 new-acc2)))
                 (append (list `((,new-fromst (,read ,(car p))) (,newst (,read ,BLANK))))
                         (list `((,newst (,read ,BLANK)) (,newst2 (,read L))))
                         (append-map (lambda (x) (list `((,newst2 (,read ,x)) (,newst3 (,read R))))) sigma)
                         (push-helper push newst3 new-acc3))))
              (else
               (let* ((newst (gen-state stateacc2))
                      (new-acc (cons newst stateacc2)))
                 (append (list `((,new-fromst (,read ,(car p))) (,newst (,read ,BLANK))))
                         (list `((,newst (,read ,BLANK)) (,newst (,read L))))
                         (new-read-pop-push-rules-helper (cdr p) newst new-acc)))))) 
      (new-read-pop-push-rules-helper pop fromst stateacc)))
  
  ;; pda-rule -> (listof mttm-rule)
  ;; Purpose: Make mttm rules for a pda rule that reads and pops something
  ;; Accumulator invariants:
  ;;  stateacc = keep track of which states have already been generated
  (define (new-read-pop-rules rule stateacc)
    (let ((fromst (first (first rule)))
          (tost (first (second rule)))
          (read (second (first rule)))
          (pop (third (first rule))))
      ;; poplist -> (listof mttm-rule)
      ;; Purpose: Traverse the pop list
      ;; Accumulator invariants:
      ;;  stateacc2 = keep track of which states have already been generated
      (define (new-read-pop-rules-helper p new-fromst stateacc2)
        (cond ((= 1 (length p))
               (let* ((newst (gen-state stateacc2))
                      (new-acc (cons newst stateacc2)))
                 (append (list `((,new-fromst (,read ,(car p))) (,newst (,read ,BLANK))))
                         (list `((,newst (,read ,BLANK)) (,tost (R L)))))))
              (else
               (let* ((newst (gen-state stateacc2))
                      (new-acc (cons newst stateacc2)))
                 (append (list `((,new-fromst (,read ,(car p))) (,newst (,read ,BLANK))))
                         (list `((,newst (,read ,BLANK)) (,newst (,read L))))
                         (new-read-pop-rules-helper (cdr p) newst new-acc))))))             
      (new-read-pop-rules-helper pop fromst stateacc)))

  ;; pda-rule -> (listof mttm-rule)
  ;; Purpose: Make mttm rules for a pda rule that reads and pushes something
  ;; Accumulator invariants:
  ;;  stateacc = keep track of which states have already been generated
  (define (new-read-push-rules rule stateacc)
    (let ((fromst (first (first rule)))
          (tost (first (second rule)))
          (read (second (first rule)))
          (push (reverse (second (second rule))))
          (sigma (cons BLANK (sm-sigma p))))
      ;; pushlist -> (listof mttm-rule)
      ;; Purpose: Traverse the push list
      ;; Accumulator invariants:
      ;;  stateacc2 = keep track of which states have already been generated
      (define (new-read-push-rules-helper p new-fromst stateacc2)
        (cond ((= 1 (length p))
               (list `((,new-fromst (,read ,BLANK)) (,tost (R ,(car p))))))
              (else
               (let* ((newst (gen-state stateacc2))
                      (new-acc (cons newst stateacc2)))
                 (append (list `((,new-fromst (,read ,BLANK)) (,new-fromst (,read ,(car p)))))
                         (list `((,new-fromst (,read ,(car p))) (,newst (,read R))))
                         (new-read-push-rules-helper (cdr p) newst new-acc))))))
      (let ((newst (gen-state stateacc)))
        (append (append-map (lambda (x) (list `((,fromst (,read ,x)) (,newst (,read R))))) sigma)
                (new-read-push-rules-helper push newst (cons newst stateacc))))))

  ;; pda-rule -> (listof mttm-rule)
  ;; Purpose: Make mttm rules for a pda rule that only pops and pushes something
  ;; Accumulator invariants:
  ;;  stateacc = keep track of which states have already been generated
  (define (new-pop-push-rules rule stateacc)
    (let ((fromst (first (first rule)))
          (tost (first (second rule)))
          (read (if (eq? EMP (second (first rule)))
                    BLANK
                    (second (first rule))))
          (pop (third (first rule)))
          (push (reverse (second (second rule))))
          (sigma (cons BLANK (sm-sigma p))))
      ;; pushlist -> (listof mttm-rule)
      ;; Purpose: Traverse the push list
      ;; Accumulator invariants:
      ;;  stateacc2 = keep track of which states have already been generated
      (define (push-helper p new-fromst stateacc2)
        (cond ((= 1 (length p))
               (list `((,new-fromst (,read ,BLANK)) (,tost (,read ,(car p))))))
              (else
               (let* ((newst (gen-state stateacc2))
                      (new-acc (cons newst stateacc2)))
                 (append (list `((,new-fromst (,read ,BLANK)) (,new-fromst (,read ,(car p)))))
                         (list `((,new-fromst (,read ,(car p))) (,newst (,read R))))
                         (push-helper (cdr p) newst new-acc))))))
      ;; poplist -> (listof mttm-rule)
      ;; Purpose: Traverse the pop list
      ;; Accumulator invariants:
      ;;  stateacc2 = keep track of which states have already been generated
      (define (new-pop-push-rules-helper p new-fromst stateacc2)
        (cond ((= 1 (length p))
               (let* ((newst (gen-state stateacc2))
                      (new-acc (cons newst stateacc2))
                      (newst2 (gen-state new-acc))
                      (new-acc2 (cons newst2 new-acc))
                      (newst3 (gen-state new-acc2))
                      (new-acc3 (cons newst3 new-acc2)))
                 (append (list `((,new-fromst (,read ,(car p))) (,newst (,read ,BLANK))))
                         (list `((,newst (,read ,BLANK)) (,newst2 (,read L))))
                         (append-map (lambda (x) (list `((,newst2 (,read ,x)) (,newst3 (,read R))))) sigma)
                         (push-helper push newst3 new-acc3))))
              (else
               (let* ((newst (gen-state stateacc2))
                      (new-acc (cons newst stateacc2)))
                 (append (list `((,new-fromst (,read ,(car p))) (,newst (,read ,BLANK))))
                         (list `((,newst (,read ,BLANK)) (,newst (,read L))))
                         (new-pop-push-rules-helper (cdr p) newst new-acc)))))) 
      (new-pop-push-rules-helper pop fromst stateacc)))
  
  ;; pda-rule -> (listof mttm-rule)
  ;; Purpose: Make mttm rules for a pda rule that only reads something
  (define (new-read-rules rule)
    (let ((fromst (first (first rule)))
          (tost (first (second rule)))
          (read (second (first rule)))
          (sigma (cons BLANK (sm-sigma p))))
      (map (lambda (x) `((,fromst (,read ,x)) (,tost (R ,x)))) sigma)))

  ;; pda-rule -> (listof mttm-rule)
  ;; Purpose: Make mttm rules for a pda rule that only pops something
  ;; Accumulator invariants:
  ;;  stateacc = keep track of which states have already been generated
  (define (new-pop-rules rule stateacc)
    (let ((fromst (first (first rule)))
          (tost (first (second rule)))
          (read (if (eq? EMP (second (first rule)))
                    BLANK
                    (second (first rule))))
          (pop (third (first rule))))
      ;; poplist -> (listof mttm-rule)
      ;; Purpose: Traverse the pop list
      ;; Accumulator invariants:
      ;;  stateacc2 = keep track of which states have already been generated
      (define (new-pop-rules-helper p new-fromst stateacc2)
        (cond ((= 1 (length p))
               (let* ((newst (gen-state stateacc2))
                      (new-acc (cons newst stateacc2)))
                 (append (list `((,new-fromst (,read ,(car p))) (,newst (,read ,BLANK))))
                         (list `((,newst (,read ,BLANK)) (,tost (,read L)))))))
              (else
               (let* ((newst (gen-state stateacc2))
                      (new-acc (cons newst stateacc2)))
                 (append (list `((,new-fromst (,read ,(car p))) (,newst (,read ,BLANK))))
                         (list `((,newst (,read ,BLANK)) (,newst (,read L))))
                         (new-pop-rules-helper (cdr p) newst new-acc))))))             
      (new-pop-rules-helper pop fromst stateacc)))

  ;; pda-rule -> (listof mttm-rule)
  ;; Purpose: Make mttm rules for a pda rule that only pushes something
  ;; Accumulator invariants:
  ;;  stateacc = keep track of which states have already been generated
  (define (new-push-rules rule stateacc)
    (let ((fromst (first (first rule)))
          (tost (first (second rule)))
          (read (if (eq? EMP (second (first rule)))
                    BLANK
                    (second (first rule))))
          (push (reverse (second (second rule))))
          (sigma (cons BLANK (sm-sigma p))))
      ;; pushlist -> (listof mttm-rule)
      ;; Purpose: Traverse the push list
      ;; Accumulator invariants:
      ;;  stateacc2 = keep track of which states have already been generated
      (define (new-push-rules-helper p new-fromst stateacc2)
        (cond ((= 1 (length p))
               (list `((,new-fromst (,read ,BLANK)) (,tost (,read ,(car p))))))
              (else
               (let* ((newst (gen-state stateacc2))
                      (new-acc (cons newst stateacc2)))
                 (append (list `((,new-fromst (,read ,BLANK)) (,new-fromst (,read ,(car p)))))
                         (list `((,new-fromst (,read ,(car p))) (,newst (,read R))))
                         (new-push-rules-helper (cdr p) newst new-acc))))))
      (let ((newst (gen-state stateacc)))
        (append (append-map (lambda (x) (list `((,fromst (,read ,x)) (,newst (,read R))))) sigma)
                (new-push-rules-helper push newst (cons newst stateacc))))))
  
  ;; pda-rule -> (listof mttm-rule)
  ;; Purpose: Make mttm rules for a pda rule that reads, pops, and pushes nothing
  (define (new-empty-rules rule)
    (let* ((fromst (first (first rule)))
           (tost (first (second rule)))
           (sigma (cons BLANK (sm-sigma p)))
           (new-reads-actions (append (map (lambda (x) (list x x)) sigma)
                                      (append-map permutations (filter (lambda (x) (= 2 (length x))) (combinations sigma))))))
      (map (lambda (x) `((,fromst ,x) (,tost ,x))) new-reads-actions)))
  
  ;; (listof pda-rule) -> (listof mttm-rule)
  ;; Purpose: Convert pda rules to mttm rules
  ;; Accumulator invariants:
  ;;  states = keeps track of which states have already been generated
  (define (new-rules-helper rules states)
    (if (empty? rules)
        '()
        (let ((rule (first rules)))
          (cond ((and (read? rule)
                      (pop? rule)
                      (push? rule))
                 (let* ((new-rules (new-read-pop-push-rules rule states))
                        (new-states (remove-duplicates
                                     (append (get-states-from-mttm-rules new-rules)
                                             states))))
                   (append new-rules
                           (new-rules-helper (rest rules) new-states))))
                ((and (read? rule)
                      (pop? rule))
                 (let* ((new-rules (new-read-pop-rules rule states))
                        (new-states (remove-duplicates
                                     (append (get-states-from-mttm-rules new-rules)
                                             states))))
                   (append new-rules
                           (new-rules-helper (rest rules) new-states))))
                ((and (read? rule)
                      (push? rule))
                 (let* ((new-rules (new-read-push-rules rule states))
                        (new-states (remove-duplicates
                                     (append (get-states-from-mttm-rules new-rules)
                                             states))))
                   (append new-rules
                           (new-rules-helper (rest rules) new-states))))
                ((and (pop? rule)
                      (push? rule))
                 (let* ((new-rules (new-pop-push-rules rule states))
                        (new-states (remove-duplicates
                                     (append (get-states-from-mttm-rules new-rules)
                                             states))))
                   (append new-rules
                           (new-rules-helper (rest rules) new-states))))
                ((read? rule) (append (new-read-rules rule)
                                      (new-rules-helper (rest rules) states)))
                ((pop? rule)
                 (let* ((new-rules (new-pop-rules rule states))
                        (new-states (remove-duplicates
                                     (append (get-states-from-mttm-rules new-rules)
                                             states))))
                   (append new-rules
                           (new-rules-helper (rest rules) new-states)))) 
                ((push? rule)
                 (let* ((new-rules (new-push-rules rule states))
                        (new-states (remove-duplicates
                                     (append (get-states-from-mttm-rules new-rules)
                                             states))))
                   (append new-rules
                           (new-rules-helper (rest rules) new-states))))
                (else (append (new-empty-rules rule)
                              (new-rules-helper (rest rules) states)))))))
  ;(displayln (new-read-pop-push-rules '((Q c (a a)) (S (b b))) '(A C F G)))
  ;(new-rules-helper (sm-rules p) (sm-states p))
  (let* ((new-rules (new-rules-helper (sm-rules p) (sm-states p)))
         (new-states (get-states-from-mttm-rules new-rules))
         (new-final (gen-nt new-states))
         (new-rules2 (append (append-map (lambda (x) (list `((,x (,BLANK ,BLANK)) (,new-final (,BLANK ,BLANK))))) (sm-finals p)) new-rules)))
      (make-mttm (cons new-final new-states)
                 (remove-duplicates (append (sm-sigma p) (sm-gamma p)))
                 (sm-start p)
                 (list new-final)
                 new-rules2
                 2
                 new-final)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;(append-map permutations (filter (lambda (x) (= 2 (length x))) (combinations '(_ a b))))

(sm-graph a^nb^n)
(sm-graph (pda->mttm a^nb^n))

(sm-graph a^ib^j)
(sm-graph (pda->mttm a^ib^j))

(sm-graph anbn)
(sm-graph (pda->mttm anbn))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#| Proof of Equivalence

To prove that the languages of the two machines are the same, we first need to
prove that every computation possible with PDA may be carried out by MTTM.
To this end, we prove the following theorem by induction on |w|.

Let P = (make-ndpda K sig gam s F del). There exists a mttm P' that simulates P.
Let P' = (make-mttm K' sig' s F' del' a n), such that:
  K': K and
      new states needed for popping and pushing and
      a
sig': sig and
      gam
  F': (list a)
   a: new accept state
del': transitions simulating transitions in del and
      transitions reading and writing blanks on all tapes from all states in F to a
   n: 2 (tape 0 simulates w and tape 1 simulates the stack)

Assume the precondition for P' is:
tape 0 = (LM w) and t0h = 1
tape 1 = (BLANK) and t1h = 0

If a blank is read on tape 0, that means that all the input is consumed.
If the head on tape 1 is on the blank at position 0, that means the stack is empty. 

Assume the states of P are states in P'.
Prove that P' makes the same state transitions as P.

There are 8 cases for possible transitions in P:

1. Transition that reads, pops, and pushes something.
2. Transition that reads and pops something, but pushes nothing.
3. Transition that reads and pushes something, but pops nothing.
4. Transition that pops and pushes something, but reads nothing.
5. Transition that reads something, but pops and pushes nothing.
6. Transition that pops something, but reads and pushes nothing.
7. Transition that pushes something, but reads and pops nothing.
8. Transition that reads, pops, and pushes nothing.

We need to prove that P' can simulate all 8 of these transition types.

Let src = source state of a transition in P
Let dst = destination state of a transition in P
Let ui = unconsumed input

1. Assume a rule in P reads, pops, and pushes something. That means that the machine transitions from
a src to a dst reading the next element of the ui and changing the stack (by popping the pop elements and then pushing the push elements).
For P' to transition from the same src to the same dst, the machine starts in src, then transitions through a newly
created state for every element popped, then transitions through a newly created state for every element pushed, and ends in dst.
The transition from src to the first newly created state reads the element on tape 0 and writes it (it is not consumed until everything is popped and pushed).
This same transition also reads the element on tape 1 and if it is the first element of the pop list it writes a blank. Then, in that newly
created state, it reads the blank and moves the head on tape 1 left (simulating the new top of the stack). This is repeated for all elements in the pop list.
After popping the last element of the list (writing a blank on tape 1), P' transitions to some new state A and moves the head on tape 1
left. Like this, the next element in ui (tape 0) has been consumed and the elements from the pop list were removed from the stack (tape 1).
A is the last state of the pop sequence and the first state of the push sequence. Before using the list of push elements, we reverse it to push
the start of the list first. The transition from A to the first newly created state of the push sequence reads the element on tape 0 and writes it.
This same transition also reads the element on tape 1 and moves the head on tape 1 right to a blank. Then, in that newly created state, it reads the blank and
writes the first push element. This is repeated for all elements in the push list. When pushing the last element of the list (writing it
on tape 1), P' transitions to dst and moves the head on tape 0 right (consuming the next element in ui). Like this, the next element in ui (tape 0) has been consumed
and the pop elements have been removed from the stack (tape 1) and the stack was added the elements from the push list. Thus, the rule in P and the
new transitions in P' are equivalent.

2. Assume a rule in P reads and pops something, but pushes nothing. That means that the machine transitions from
a src to a dst reading the next element of the ui and changing the stack (by popping the pop elements).
For P' to transition from the same src to the same dst, the machine starts in src, then transitions through a newly
created state for every element popped, and ends in dst. The transition from src to the first newly created state
reads the element on tape 0 and writes it (it is not consumed until everything is popped). This same transition also reads the element on tape 1
and if it is the first element of the pop list it writes a blank. Then, in that newly created state, it reads the blank
and moves the head on tape 1 left (simulating the new top of the stack). This is repeated for all elements in the pop list.
After popping the last element of the list (writing a blank on tape 1), P' transitions to dst, moves the head on tape 0 right (consuming the next element of ui)
and moves the head on tape 1 left (simulating the head being on the top of the stack). Like this, the next element in ui (tape 0) has been consumed and the elements
from the pop list were removed from the stack (tape 1). Thus, the rule in P and the new transitions in P' are equivalent.

3. Assume a rule in P reads and pushes something, but pops nothing. That means that the machine transitions from
a src to a dst reading the next element of the ui and changing the stack (by adding new push elements).
For P' to transition from the same src to the same dst, the machine starts in src, then transitions through a newly
created state for every element pushed, and ends in dst. Before using the list of push elements, we reverse it to
push the start of the list first. The transition from src to the first newly created state
reads the element on tape 0 and writes it (it is not consumed until everything is pushed). This same transition also reads the element on tape 1
and moves the head on tape 1 right to a blank. Then, in that newly created state, it reads the blank and writes the first
push element. This is repeated for all elements in the push list. When pushing the last element of the list (writing it
on tape 1), P' transitions to dst, and moves the head on tape 0 right (consuming the next element of ui). Like this, the next element in ui (tape 0) has been
consumed and the stack (tape 1) was added the elements from the push list. Thus, the rule in P and the new transitions in P' are equivalent.

4. Assume a rule in P pops, and pushes something, but reads nothing. That means that the machine transitions from
a src to a dst not changing the ui and changing the stack (by popping the pop elements and then pushing the push elements).
For P' to transition from the same src to the same dst, the machine starts in src, then transitions through a newly
created state for every element popped, then transitions through a newly created state for every element pushed, and ends in dst.
The transition from src to the first newly created state reads the element on tape 0 and writes it (nothing is consumed).
This same transition also reads the element on tape 1 and if it is the first element of the pop list it writes a blank. Then, in that newly
created state, it reads the blank and moves the head on tape 1 left (simulating the new top of the stack). This is repeated for all elements in the pop list.
After popping the last element of the list (writing a blank on tape 1), P' transitions to some new state A and moves the head on tape 1
left. Like this, the next element in ui (tape 0) has been consumed and the elements from the pop list were removed from the stack (tape 1).
A is the last state of the pop sequence and the first state of the push sequence. Before using the list of push elements, we reverse it to push
the start of the list first. The transition from A to the first newly created state of the push sequence reads the element on tape 0 and writes it.
This same transition also reads the element on tape 1 and moves the head on tape 1 right to a blank. Then, in that newly created state, it reads the blank and
writes the first push element. This is repeated for all elements in the push list. When pushing the last element of the list (writing it
on tape 1), P' transitions to dst. Like this, ui (tape 0) remains unchanged and the pop elements have been removed from the stack (tape 1)
and the stack was added the elements from the push list. Thus, the rule in P and the new transitions in P' are equivalent.

5. Assume a rule in P reads something, but pushes and pops nothing. That means that the machine transitions from
a src to a dst reading the next element of ui and not changing the stack.
P' also transitions from the same src to the same dst. The transition reads P's read element on tape 0 and moves the
head on tape 0 to the right. The transition also reads the current element on tape 1 and writes it. Like this the stack
remains unchanged, and the next element in ui has been consumed. Thus, the rule in P and the new transitions in P' are equivalent.

6. Assume a rule in P pops something, but reads and pushes nothing. That means that the machine transitions from
a src to a dst without changing the ui and changing the stack (by popping the pop elements).
For P' to transition from the same src to the same dst, the machine starts in src, then transitions through a newly
created state for every element popped, and ends in dst. The transition from src to the first newly created state
reads the element on tape 0 and writes it (ui remains the same). This same transition also reads the element on tape 1
and if it is the first element of the pop list it writes a blank. Then, in that newly created state, it reads the blank
and moves the head on tape 1 left (simulating the new top of the stack). This is repeated for all elements in the pop list.
After popping the last element of the list (writing a blank on tape 1), P' transitions to dst and moves the head on tape 1
left. Like this, ui (tape 0) remains the same and the elements from the pop list were removed from the stack (tape 1). Thus, the
rule in P and the new transitions in P' are equivalent.

7. Assume a rule in P pushes something, but reads and pops nothing. That means that the machine transitions from
a src to a dst without changing the ui and changing the stack (by adding new push elements).
For P' to transition from the same src to the same dst, the machine starts in src, then transitions through a newly
created state for every element pushed, and ends in dst. Before using the list of push elements, we reverse it to
push the start of the list first. The transition from src to the first newly created state
reads the element on tape 0 and writes it (ui remains the same). This same transition also reads the element on tape 1
and moves the head on tape 1 right to a blank. Then, in that newly created state, it reads the blank and writes the first
push element. This is repeated for all elements in the push list. When pushing the last element of the list (writing it
on tape 1), P' transitions to dst. Like this, ui (tape 0) remains the same and the stack (tape 1) was added the elements
from the push list. Thus, the rule in P and the new transitions in P' are equivalent.

8. Assume a rule in P reads, pops, and pushes nothing. That means that the machine transitions from a src
to a dst without changing ui or stack.
P' transitions from the same src to the same dst by reading the elements on its 2
tapes, and writing the same elements. Like this, both tapes remain unchanged, which is equivalent to not changing
ui or stack. Thus, the rule in P and the new transitions in P' are equivalent.

Proving L(P) = L(P')

w∈L(P) <-> w∈L(P')

(->) Assume w∈L(P).
Given that transition equivalences always hold, there is a computation that has P' consume w, meaning that the head ends on tape 0 on the blank after w,
and with the head on tape 1 being at position 0 on a blank (simulating an empty stack), and reach a, its accept state. Therefore, w∈L(P').

(<-) Assume w∈L(P').
Given that transition equivalences always hold, there is a computation that has P consume w
and reach a state in F with an empty stack. Therefore, w∈L(P).

w∈/L(P) <-> w∈/L(P')

(->) Assume w∈L(P).
Given that transition equivalences always hold, there is no computation that has P' consume w, meaning that the head ends on tape 0 on the blank after w,
and with the head on tape 1 being at position 0 on a blank (simulating an empty stack), and reach a, its accept state. Therefore, w∈/L(P').

(<-) Assume w∈L(P').
Given that transition equivalences always hold, there is no computation that has P consume w
and reach a state in F with an empty stack. Therefore, w∈/L(P). |#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;










