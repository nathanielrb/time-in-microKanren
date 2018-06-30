(use srfi-1)
(define (assp pred alist)
  (find (lambda (pair) (pred (car pair))) alist))

(load "temporal-microKanren.scm")
(load "miniKanren-wrappers.scm")

(define (precedeso* g* h*)
  (let ((g (g*)) (h (h*)))
    (disj h
	  (conj g
		(next (precedeso* g* h*))))))

(define-syntax precedeso
  (syntax-rules ()
    ((_ g h) (precedeso* (lambda () g) (lambda () h)))))

(define (alwayso* g*)
  (let ((g (g*)))
    (conj g (next (alwayso* g*))))))

(define-syntax alwayso
  (syntax-rules ()
    ((_ g) (alwayso* (lambda () g)))))

(define (as-long-aso* g* h*)
  (let ((g (g*)) (h (h*)))
    (lambda (s/c)
      (let (($ (g s/c)))
	(if (null? $) mzero
	    (bind $ (disj h (next (as-long-aso* g* h*)))))))))

(define-syntax as-long-as
  (syntax-rules ()
    ((_ g h) (as-long-aso* (lambda () g) (lambda () h)))))

(define (eventuallyo* g*)
  (let ((g (g*)))
    (disj g (next (eventuallyo* g*)))))

(define-syntax eventuallyo
  (syntax-rules ()
    ((_ g) (eventuallyo* (lambda () g)))))

(define-syntax untilo
  (syntax-rules ()
    ((_ g h) (conj (precedeso g h) (eventuallyo h)))))
