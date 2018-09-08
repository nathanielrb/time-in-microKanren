(use srfi-1 persistent-hash-map matchable)

(define (assp pred alist)
  (find (lambda (pair) (pred (car pair))) alist))

(include "temporal-microKanren.scm")
(include "miniKanren-wrappers.scm")

(define-syntax project
  (syntax-rules ()
    ((_ (x ...) g)
     (lambda (s/c)
       (let ((x (walk x (car s/c))) ...)
	 (g s/c))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Database
(define-record db null s sp p po o os spo)

(define-record incrementals map list)

(define (empty-incrementals)
  (make-incrementals (persistent-map) '()))

(define (empty-db)
  (apply make-db
	 (make-list 8 (persistent-map))))

(define (update-incrementals table key val)
  (let ((incrementals (map-ref table key (empty-incrementals))))
    (map-add table key
	     (if (map-ref (incrementals-map incrementals) val)
		 incrementals
		 (make-incrementals
		  (map-add (incrementals-map incrementals) val #t)
		  (cons val (incrementals-list incrementals)))))))

(define (update-triple table triple val)
  (map-add table triple val))

(define latest-db (make-parameter (empty-db)))

(define (latest-incrementals accessor key)
  (incrementals-list
   (map-ref (accessor (latest-db)) key (empty-incrementals))))

(define (latest-triple s p o)
  (map-ref (db-spo (latest-db))
	   (list s p o)))

(define (update-triples DB triples val)
  (let loop ((triples triples)
	     (i/null (db-null DB))
	     (i/s (db-s DB))
	     (i/sp (db-sp DB))
	     (i/p (db-p DB))
	     (i/po (db-po DB))
	     (i/o (db-o DB))
	     (i/os (db-os DB))
	     (i/spo (db-spo DB)))
    (if (null? triples)
	(make-db i/null i/s i/sp i/p i/po i/o i/os i/spo)
	(match (car triples)
	  ((s p o)
	   (loop (cdr triples)
		 (update-incrementals i/null #f s) 
		 (update-incrementals i/s s p)
		 (update-incrementals i/sp (list s p) o)
		 (update-incrementals i/p p o)
		 (update-incrementals i/po (list p o) s)
		 (update-incrementals i/o o s)
		 (update-incrementals i/os (list o s) p)
		 (update-triple i/spo (list s p o) val)))))))

(define (add-triples DB triples) (update-triples DB triples #t))

(define (delete-triples DB triples) (update-triples DB triples #f))

(define (add-triple s p o)
  (add-triples `((,s ,p ,o))))

(define (delete-triple s p o)
  (delete-triples `((,s ,p ,o))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Goal Constructors
(define (tripleo s p o)
  (let ((mkstrm (lambda (var accessor key)
		  (let ((get-incrementals (lambda ()
					    (latest-incrementals accessor key))))
		    (let stream ((indexes (get-incrementals)))
		      (if (null? indexes) (lambda (s/c) mzero)
			  (disj
			   (conj (== var (car indexes))
				 (project (s p o)
                                   (tripleo s p o)))
			   (stream (cdr indexes)))))))))
    (cond ((and (var? s) (var? p) (var? o)) (mkstrm s db-null #f))
	  ((and (var? s) (var? p))          (mkstrm s db-o o))
	  ((and (var? s) (var? o))          (mkstrm o db-p p))
	  ((and (var? p) (var? o))          (mkstrm p db-s s))
	  ((var? s)                         (mkstrm s db-po (list p o)))
	  ((var? p)                         (mkstrm p db-os (list o s)))
	  ((var? o)                         (mkstrm o db-sp (list s p)))
	  (else (== #t (latest-triple s p o))))))

(define (triple-nolo delta s p o)
  (let ((mkstrm (lambda (var accessor key)
		  (let* ((get-incrementals (lambda ()
					    (latest-incrementals accessor key)))
			(initial-indexes (get-incrementals)))
		    (let stream ((indexes initial-indexes) 
                                 (ref '()) (next-ref initial-indexes))
		      (if (equal? indexes ref)
			  (next
			   (let ((vals (get-incrementals)))
			     (stream vals next-ref vals)))
			  (disj
			   (conj (== var (car indexes))
				 (project (delta s p o) (triple-nolo delta s p o)))
			   (stream (cdr indexes) ref next-ref))))))))
    (cond ((and (var? s) (var? p) (var? o)) (mkstrm s db-null #f))
	  ((and (var? s) (var? p))          (mkstrm s db-o o))
	  ((and (var? s) (var? o))          (mkstrm o db-p p))
	  ((and (var? p) (var? o))          (mkstrm p db-s s))
	  ((var? s)                         (mkstrm s db-po (list p o)))
	  ((var? p)                         (mkstrm p db-os (list o s)))
	  ((var? o)                         (mkstrm o db-sp (list s p)))
	  (else
           (let leaf ((ref #f))
             (let ((v (latest-triple s p o)))
               (cond ((eq? v ref) (next (leaf v)))
		     (v (disj (== delta '+) (next (leaf v))))
                     (else (disj (== delta '-) (next (leaf v)))))))))))

