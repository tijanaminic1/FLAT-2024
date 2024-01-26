#lang fsm

;; PG. 19 problem 1

;; Design and implement a recursive function to insert in the right place a number in a sorted
;; list of numbers.

;; A lon is:
;; '()
;; (cons number lon)


;; num lon -> lon
;; Purpose: To insert the num in a sorted lon
;; Assumption: The input lon has to be sorted
(define (insert-number num lon)
  (cond [(empty? lon) (cons num lon)]
        [(< num (first lon)) (cons num lon)]
        [else (cons (first lon) (insert-number num (rest lon)))]))

;; Tests
(check-equal? (insert-number 5 '()) '(5))
(check-equal? (insert-number 5 '(1 3 6 8 9)) '(1 3 5 6 8 9))
(check-equal? (insert-number -5 '(1 3 6 8 9)) '(-5 1 3 6 8 9))
(check-equal? (insert-number 100 '(1 3 6 8 9)) '(1 3 6 8 9 100))
(check-equal? (insert-number -17 '(-30 -25 -7 -1 5 7)) '(-30 -25 -17 -7 -1 5 7))


;; PG. 19 problem 2

;; Design and implement a function to find the longest string in a list of strings.

;; a los is:
;; '()
;; (cons string los)

;; los -> string
;; Purpose: To find the longest string in a los
(define (find-longest-str los)
  (cond [(empty? los) '()]
        [(empty? (filter (λ (x) (< (string-length (first los)) (string-length x))) (rest los))) (first los)]
        [else (find-longest-str (rest los))]))

;; Tests
(check-equal? (find-longest-str '()) '())
(check-equal? (find-longest-str (list "mom" "baby" "tijana")) "tijana")
(check-equal? (find-longest-str (list "mom" "mauuuu" "baby" "tijana")) "mauuuu")
(check-equal? (find-longest-str (list "mom" "mauuuu" "baby" "tijana" "idkwhattosayyy")) "idkwhattosayyy")



;; PG. 19 problem 3

;; Design and implement a function that takes as input two natural numbers greater than or equal to 2,
;; a and b, and returns the greatest common divisor of the two given numbers. 

;; natnum is either
;; 0
;; (+ 1 natnum)

;; natnum natnum -> natnum
;; Purpose: To find the greater common divisor of the given numbers
;; Assumption: Both numbers are <=2





;; PG. 19 problem 4

;; Design and implement a function that merges two sorted lists of numbers into one sorted lon

;; lon is either
;; '()
;; cons num lon

;; lon lon -> lon
;; Purpose: To merge two sorted lon into one sorted lon
;; Assumption: Input lon's are both sorted
(define (merge-sort lon1 lon2)
  (let* [(accum '())]
    (cond [(empty? lon1) lon2]
          [(empty? lon2) lon1]
          [(> (first lon1) (first lon2)) (cons (first lon2) (cons (first lon1) (merge-sort (rest lon1) (rest lon2))))]
          [else (cons (first lon1) (cons (first lon2) (merge-sort (rest lon1) (rest lon2))))])))


(check-equal? (merge-sort '(2 4 6 8) '(1 3 5 7)) '(1 2 3 4 5 6 7 8))
(check-equal? (merge-sort '(-5 -2 4 6 8) '(-2 -1 5 7)) '(-5 -2 -2 -1 4 5 6 7 8))
(check-equal? (merge-sort '() '(1 3 5 7)) '(1 3 5 7))

;; PG. 19 problem 5

;; Design and implement a function that takes as input a natnum and returns the sum of the natural
;; numbers in [0..n]

;; natnum -> natnum
;; Purpose: To return the sum of the natural
;; numbers in [0..n]
(define (sum-num num)
  (if (= 0 num)
      0
      (+ num (sum-num (- num 1)))))

(check-equal? (sum-num 0) 0)
(check-equal? (sum-num 5) 15)
(check-equal? (sum-num 3) 6)
(check-equal? (sum-num 10) 55)


;; PG. 20 problem 6

;; Design and implement a function using ormap to determine if any number in a list of numbers
;; is a prime

;; lon is either
;; '()
;; (cons number lon)

(define (is-prime? num)
  (or (= 2 num)
      (= 3 num)
      (= 5 num)
      (= 7 num)
      (and (not (and (= 0 (remainder num 2))
                     (>= num 4)))
           (not (and (= 0 (remainder num 3))
                     (>= num 9)))
           (not (and (= 0 (remainder num 5))
                     (>= num 25)))
           (not (and (= 0 (remainder num 7))
                     (>= num 49))))))

;; lon -> Boolean
;; Purpose: To determine if any number in a list of numbers
;; is a prime
(define (any-primes? lon)
  (define (is-prime? num)
    (or (= 2 num)
        (= 3 num)
        (= 5 num)
        (= 7 num)
        (and (not (and (= 0 (remainder num 2))
                       (>= num 4)))
             (not (and (= 0 (remainder num 3))
                       (>= num 9)))
             (not (and (= 0 (remainder num 5))
                       (>= num 25)))
             (not (and (= 0 (remainder num 7))
                       (>= num 49))))))
  (ormap (λ (x)(is-prime? x)) lon))
         


(check-equal? (any-primes? '(50 94 58 10)) #f)
(check-equal? (any-primes? '(2 50 13 93 58 10)) #t)
(check-equal? (any-primes? '()) #f)


;; PG. 20 problem 7

;; Design and implement a function using filter to extract the strings with a length greater than
;; 5 from a list of strings.

;; los is either
;; '()
;; cons string los


;; los -> los
;; Purpose: To extract all strings longer than 5
(define (longer-than-5 los)
  (filter (λ (x) (> (string-length x) 5)) los))


(check-equal? (longer-than-5 (list "tiksi" "Oliwia" "sena" "marco")) '("Oliwia"))
(check-equal? (longer-than-5 '()) '())
(check-equal? (longer-than-5 (list "no" "yes" "liv" "tix")) '())


;; PG. 20 problem 8

;; Design and implement a function using map to add a blank to the front of every
;; string in a list of strings

;; los is either
;; '()
;; cons string los

;; los -> los
;; Purpose: To add a blank at the front of each string in a los
(define (add-blank los)
  (if (empty? los)
      '()
      (map (λ (x) (string-append " " x)) los)))

(check-equal? (add-blank (list "tiksi" "Oliwia" "sena" "marco")) '(" tiksi" " Oliwia" " sena" " marco"))
(check-equal? (add-blank '()) '())


;; PG. 20 problem 9

;; Design and implement a function that takes as input a list of number and a number i, and that using foldr
;; extracts all the numbers in the list less than or equal to i.

;; lon is either
;; '()
;; cons num lon

;; lon num -> lon
;; Purpose: To extract all the numbers in a list that are less than or equal to i
(define (extract-i lon i)
  (foldr (λ (num result)
           (if (<= num i)
               (cons num result)
               result))
         '()
         lon))


(check-equal? (extract-i '(1 2 3 5 6 7) 4) '(1 2 3))
(check-equal? (extract-i '(2 5 6 7) 4) '(2))
(check-equal? (extract-i '() 4) '())


;; PG. 21 problem 10

;; Design and implement a nonrecursive function that takes as input a list of numbers that returns a list
;; of the even numbers in the given list doubled

;; lon is either
;; '()
;; cons num lon

;; lon -> lon
;; Purpose: To double the even numbers in the list
(define (double-evens lon)
  (append (foldr (λ (num result) (if (even? num)
                                     (cons num result)
                                     result))
                 '()
                 lon)
          lon))


(check-equal? (double-evens '(2 3 4 5 6 7 8)) '(2 4 6 8 2 3 4 5 6 7 8))
(check-equal? (double-evens '()) '())















