#lang fsm

#|

12 A user is a random word generated from letters in the Roman
 alphabet and from the digits that starts with a letter. A domain
is a random word generated from letters in the Roman alphabet followed
by either .com, .edu, or .net. Consider the following definition for
the language of email addresses:
L = {u@d | u is a user ∧ d is a domain}
Define a regular expression for email addresses, and implement a
function to generate an email address.

|#

;; user concat @ concat domain concat (union com (union net (union edu)))



(define lowers '(a b c d e f g h i j k l m n o p q r s t u v w x y z))
(define digits '(0 1 2 3 4 5 6 7 8 9))
(define at (singleton-regexp "@"))


;; dot endings of the email defined separately
(define edu (concat-regexp (singleton-regexp ".") (concat-regexp (singleton-regexp "e")
                                                                 (concat-regexp (singleton-regexp "d")
                                                                                (singleton-regexp "u")))))
(define com (concat-regexp (singleton-regexp ".") (concat-regexp (singleton-regexp "c")
                                                                 (concat-regexp (singleton-regexp "o")
                                                                                (singleton-regexp "m")))))
(define net (concat-regexp (singleton-regexp ".") (concat-regexp (singleton-regexp "n")
                                                                 (concat-regexp (singleton-regexp "e")
                                                                                (singleton-regexp "t")))))
;; lists of symbols converted into a list of singleton-regexps
(define lc (map (λ (lcl) (singleton-regexp (symbol->string lcl))) lowers))
(define dig (map (λ (num) (singleton-regexp (number->string num))) digits))

;; possible dot endings of the email
(define ending (union-regexp edu (union-regexp com net)))

;; (listof regexp) → union-regexp
;; Purpose: Create a union-regexp using the given list ;; of regular expressions
(define (create-union-regexp L)
  (cond [(< (length L) 2)
         (error "create-union-regexp: list too short")]
        [(empty? (rest (rest L)))
         (union-regexp (first L) (second L))]
        [else
         (union-regexp (first L)
                       (create-union-regexp (rest L)))]))

;; union of letters and digits regular expressions
(define L (create-union-regexp lc))
(define D (create-union-regexp dig))

;; possible combinations of letter and digits
(define LD (concat-regexp L D))
(define DL (concat-regexp D L))
(define random-word-letters (concat-regexp L (kleenestar-regexp L)))

;; user
(define user (concat-regexp L (kleenestar-regexp (union-regexp LD DL))))

;; domain
(define domain (concat-regexp random-word-letters ending))

;; email-address
(define email (concat-regexp user (concat-regexp at domain)))


;; is-email?
;; los -> Boolean
;; Purpose: To determine whether a given word is an email
(define (is-email? w)
  (if (empty? w)
      #f
      (and (list? w)
           (<= 6 (length w))
           (andmap (λ (el) (or (member el lowers)
                               (member el digits)
                               (equal? el '@)
                               (equal? el '|.|)))
                   w)
           (member (first w) lowers)
           (= (length (filter (λ (el) (equal? el '@)) w)) 1)
           (or (equal? (take-right w 4) '(|.| e d u))
               (equal? (take-right w 4) '(|.| n e t))
               (equal? (take-right w 4) '(|.| c o m)))
           (not (empty? (drop (rest (member '@ w)) 4)))
           (not (empty? (rest (rest (member '@ (reverse w)))))))))



(check-equal? (is-email? '(t i j a n a @ g m a i l |.| c o m)) #t)
(check-equal? (is-email? '(@ |.| c o m)) #f)
(check-equal? (is-email? '(t i j a n a @ |.| c o m)) #f)
(check-equal? (is-email? '(t i j a n a @ g m a i l |.|)) #f)
(check-equal? (is-email? '(t i j a n a @ g m a i c o |.| m)) #f)
(check-equal? (is-email? '(t i j a n a @ g m a i l c o m)) #f)
(check-equal? (is-email? '(@ g m a i l |.| c o m)) #f)



;; [natnum>0] → word
;; Purpose: Generate the word of the given length
(define (generate . n)
  (define MAX-KS-REPS 6)
  (define MAX-LENGTH (if (null? n) 10 (first n)))
  (define (gen-word r . m)
    (cond
      [(singleton-regexp? r) (convert-singleton r)]
      [(concat-regexp? r)
       (let [(w1 (gen-word (concat-regexp-r1 r)))
             (w2 (gen-word (concat-regexp-r2 r)))]
         (append w1 w2))]
      [(union-regexp? r) (gen-word (pick-regexp r))]
      [(kleenestar-regexp? r)
       (flatten (build-list
                 (pick-reps MAX-KS-REPS)
                 (λ (i)
                   (gen-word (kleenestar-regexp-r1 r)))))]))
  (gen-word email MAX-LENGTH))































































































