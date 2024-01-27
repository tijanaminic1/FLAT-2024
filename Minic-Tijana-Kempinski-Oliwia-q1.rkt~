#lang fsm
(require lang/htdp-advanced)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Quiz 1
;; Chapter 2, Nr.17
;; Tijana Minic and Oliwia Kempinski

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Design and implement a function to print the integer pairs in a 2D Cartesian plane.

;; posn dir -> posn
;; Purpose: Given a posn and a direction, determine the next posn
(define (next-posn p dir)
  (cond [(eq? dir 'right) (make-posn (add1 (posn-x p)) (posn-y p))]
        [(eq? dir 'up) (make-posn (posn-x p) (add1 (posn-y p)))]
        [(eq? dir 'left) (make-posn (sub1 (posn-x p)) (posn-y p))]
        [else (make-posn (posn-x p) (sub1 (posn-y p)))]))

;; Tests for next-posn

(check-equal? (next-posn (make-posn 0 0) 'right) (make-posn 1 0))
(check-equal? (next-posn (make-posn 1 2) 'left) (make-posn 0 2))
(check-equal? (next-posn (make-posn 0 0) 'down) (make-posn 0 -1))
(check-equal? (next-posn (make-posn 1 2) 'up) (make-posn 1 3))

;.................................................

;; dir natnum natnum -> symbol
;; Purpose: Find new direction, if direction changes 
(define (next-dir dir len counter)
  (local (;; -> symbol
          ;; Purpose: Find the new direction 
          (define (next-dir-helper)
            (cond [(eq? dir 'right) 'up]
                  [(eq? dir 'up) 'left]
                  [(eq? dir 'left) 'down]
                  [else 'right])))
    (if (= (sub1 len) counter)
        (next-dir-helper)
        dir)))

;; Tests for next-dir

(check-equal? (next-dir 'right 3 2) 'up)
(check-equal? (next-dir 'right 3 1) 'right)
(check-equal? (next-dir 'up 3 2) 'left)
(check-equal? (next-dir 'up 3 1) 'up)
(check-equal? (next-dir 'left 3 1) 'left)
(check-equal? (next-dir 'left 3 2) 'down)
(check-equal? (next-dir 'down 3 1) 'down)
(check-equal? (next-dir 'down 3 2) 'right)

;.................................................

;; natnum natnum dir Boolean -> integer
;; Purpose: Find the next length
(define (next-len len counter dir change-len?)
  (if (and change-len?
           (or (eq? (next-dir dir len counter) 'right)
               (eq? (next-dir dir len counter) 'left)))
      (add1 len)
      len))

;; Tests for next-len

(check-equal? (next-len 3 2 'right #t) 3)
(check-equal? (next-len 3 2 'up #t) 4)
(check-equal? (next-len 3 2 'up #f) 3)
(check-equal? (next-len 3 2 'down #t) 4)

;.................................................

;; natnum natnum -> natnum
;; Purpose: Set the counter
(define (next-counter len counter)
  (if (= (sub1 len) counter)
      0
      (add1 counter)))

;; Tests for next-counter

(check-equal? (next-counter 3 2) 0)
(check-equal? (next-counter 3 1) 2)
(check-equal? (next-counter 5 1) 2)
(check-equal? (next-counter 10 9) 0)

;.................................................

;; natnum natnum Boolean-> boolean
;; Purpose: Adjust change-len? boolean
(define (next-cglen len counter change-len?)
  (cond [(and (= counter (sub1 len))
              change-len?) #f]
        [(and (= counter (sub1 len))
              (not change-len?)) #t]
        [else change-len?]))
           

;; Tests for next-cglen

(check-equal? (next-cglen 3 2 #f) #t)
(check-equal? (next-cglen 3 1 #f) #f)
(check-equal? (next-cglen 3 2 #t) #f)
(check-equal? (next-cglen 3 1 #t) #t)

;.................................................

;; Data Definitions:
;; p           = posn
;; dir         = symbol representing the direction of the arrow
;; len         = length the sequential arrows pointing in the same direction
;; counter     = keeps track of traversed arrows in len
;; change-len? = if true, len will increase by 1 at next direction change

;; -> (void)
;; Purpose: Print the integer pairs in a 2D Cartesian planes
(define (print-coords)
  (local (;; posn natnum natnum natnum Boolean -> (void)
          ;; Purpose: Print the next posn, and make recursive call
          (define (printer p dir len counter change-len?)
            (if (= len +inf.0)
                (void)
                (begin
                  (displayln p)
                  (printer (next-posn p dir)
                           (next-dir dir len counter)
                           (next-len len counter dir change-len?)
                           (next-counter len counter)
                           (next-cglen len counter change-len?))))))
    (printer (make-posn 0 0) 'right 1 0 #f)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
