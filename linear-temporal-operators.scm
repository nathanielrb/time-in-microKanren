(use srfi-1)
(define (assp pred alist)
  (find (lambda (pair) (pred (car pair))) alist))

(load "temporal-microKanren.scm")
(load "miniKanren-wrappers.scm")

(define (precedes* g* h*)
  (let ((g (g*)) (h (h*)))
    (disj h
	  (conj g
		(next (precedes* g* h*))))))

(define-syntax precedes
  (syntax-rules ()
    ((_ g h) (precedes* (lambda () g) (lambda () h)))))

(define (always* g*)
  (let ((g (g*)))
    (conj g (next (always* g*))))))

(define-syntax always
  (syntax-rules ()
    ((_ g) (always* (lambda () g)))))

(define (as-long-as* g* h*)
  (let ((g (g*)) (h (h*)))
    (lambda (s/c)
      (let (($ (g s/c)))
	(if (null? $) mzero
	    (bind $ (disj h (next (as-long-as* g* h*)))))))))

(define-syntax as-long-as
  (syntax-rules ()
    ((_ g h) (as-long-as* (lambda () g) (lambda () h)))))

(define (eventually* g*)
  (let ((g (g*)))
    (disj g (next (eventually* g*)))))

(define-syntax eventually
  (syntax-rules ()
    ((_ g) (eventually* (lambda () g)))))

(define-syntax until
  (syntax-rules ()
    ((_ g h) (conj (precedes g h) (eventually h)))))
