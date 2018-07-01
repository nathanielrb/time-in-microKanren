---
title: Temporal Logic, µKanren, and a Time-Traveling RDF Database
author:
- Nathaniel Rudavsky-Brody
abstract: By adding a temporal primitive to the µKanren language and adapting its interleaving search to preserve simultaneity in linear time, we show how a system of temporal relational programming can be implemented. This system is then applied to a practical problem in distributed systems and linked data.
---

# Introduction

When using logical programming to model or interact with stateful resources, it is convenient to have a way to reason about time. To this end, temporal logic, and in particular linear temporal logic, has been formalized as a modal extension to predicate logic, and a number of implementations have been proposed as extensions to logical languages such as Prolog.

Adding a temporal primitive to the miniKanren family of languages and adapting the interleaving search to account for the concepts of 'now' (simultaneity) and 'later' allows us to build tools for temporal reasoning that turn out to integrate quite well with the basic methods of relational programming. In addition to providing a way of controlling simultaneity and goal construction in miniKanren programs, they can be used to construct time-aware accessors to stateful data structures leveraging miniKanren's interleaving search.

In the first two sections we show how such a system can be implemented, and sketch out some ideas on how it might be extended to support a more complete linear temporal logic. In the final section, we turn to a real-world application in the domain of distributed systems and linked data. For clarity, we use µKanren^[Jason Hemann, Daniel P. Friedman. µKanren: A Minimal Functional Core for Relational Programming.] and in particular the original implementation^[https://github.com/jasonhemann/microKanren] which has the advantage of using procedures to represent immature streams, leaving us free to use Scheme promises for time. In what follows, we assume a familiarity with its implementation, and only note modifications to the original code. The full code is presented in the Appendixes.^[Code and examples at https://github.com/nathanielrb/temporal-microKanren]

# Time in µKanren

µKanren defines two types of streams, mature (represented as a pair of a state and a stream) and immature (represented as a lambda expression). A third type, delayed streams, is introduced to represent goals that are delayed until a later point in time. We can represent delayed streams by Scheme promises, and construct them using a single temporal primitive `next`.

```
(define-syntax next
  (syntax-rules ()
    ((_ g) (lambda (s/c) (delay (g s/c)))))) 
```

A complex program might have many levels of delays representing different future points in time. It is important that the temporal order of these goals be preserved during interleaving search, both with regards to the ordering of solutions and also to guaranty that a goal (which might refer to a stateful resource) is constructed at the right time. We accomplish this by adapting the interleaving search so that promises are shunted right and all promises at the same nested level are recombined together. This is done by adding two cases to the definition of `mplus`.

```
(define (mplus $1 $2)
  (cond
    ((null? $1) $2)
    ((procedure? $1) (lambda () (mplus $2 ($1))))
    ((and (promise? $1) (promise? $2))          ; recombine
     (delay (mplus (force $1) (force $2))))
    ((promise? $1) (mplus $2 $1))    	        ; shunt right
    (else (cons (car $1) (mplus (cdr $1) $2)))))
```

`bind` also needs to be modified by adding an additional case to delay the binding of delayed streams with a goal. The utility function `forward` is used to 'fast-forward' through the enclosing delayed stream.

```
(define (forward g)
  (lambda (s/c)
    (let rec (($ (g s/c)))
      (cond ((null? $) '())
            ((promise? $) (force $))
            ((procedure? $) (lambda () (rec ($))))
            (else (cons (car $) (rec (cdr $))))))))

(define (bind $ g)
   (cond
     ((null? $) mzero)
     ((procedure? $) (lambda () (bind ($) g)))
     ((promise? $) (delay (bind (force $) (forward g))))
     (else (mplus (g (car $)) (bind (cdr $) g)))))
```

The resulting 53 lines of code make up the functional core of our temporal µKanren. To keep the subsequent code simple, we also define a few convenience functions for accessing delayed streams.

```
(use srfi-1)

(define (promised $)
  (take-right $ 0))

(define (current $)
  (drop-right $ 0))

(define (advance $)
  (let ((p (promised $)))
    (and p (force p))))
```

Here is a simple example that demonstrates its internal workings.

```
(define *db* 1)

(define r
 ((call/fresh 
  (lambda (q)
   (disj (== q *db*) 
         (next (== q *db*)))))
  empty-state))
;; => ((((#(0) . 1)) . 1) . #<promise>)

(set! *db* 2)

(advance r)
;; => ((((#(0) . 2)) . 1))
```

The shunt-right mechanism turns out to have interesting properties for interleaving search, even without referring to a stateful resource, for instance in ordering and grouping solutions as the following contrived example shows. Here and in what follows, will use the miniKanren wrappers from the original paper, likewise extended to handle delayed streams.^[https://github.com/nathanielrb/time-in-microKanren/blob/master/miniKanren-wrappers.scm]

```
(define (inco x)
  (let r ((n 0))
    (disj (== x n) (next (r (+ n 1))))))

(define s
  (run* (q)
    (fresh (a b)
      (== q (list a b))
      (conj (inco a) (inco b)))))

(current s)
;; => ((0 0)))

(current (advance s))
;; => ((0 1) (1 0) (1 1)))

(current (advance (advance s)))
;; => ((1 2) (2 0) (2 1) (2 2) (0 2)))

(current (advance (advance (advance  s))))
;; => ((0 3) (2 3) (3 0) (3 1) (3 2) (3 3) (1 3)))
```


# Towards a Temporal Relational Programming

Linear temporal logic extends predicate logic with temporal modal operators referring to linear time. Two operators, Next (`X`) and Until (`U`), are generally defined as primitives and then used to construct a larger set of operators for conveniently reasoning about time. Several of these operators can be usefully recovered in temporal µKanren using the `next` primitive. We will not develop a formally complete system here, but rather provide some heuristic examples to suggest how such a system might developed.

Most temporal operators need to be defined recursively. When doing this, it is essential to control when the goal is constructed, since the goal might refer to a stateful resource. For temporal µKanren we can do this by wrapping goals in a lambda expression which are evaluated at the appropriate time. The definition of `precedes`, derived from Weak Until (`W`) and which stipulates that a goal `g` holds at least until a second goal `h` holds, shows how this is done.

```
(define (precedes* g* h*)
  (let ((g (g*)) (h (h*)))
    (disj h (conj g (next (precedes* g* h*))))))

(define-syntax precedeso
  (syntax-rules ()
    ((_ g h) (precedes* (lambda () g) (lambda () h)))))
```

Translating another basic operator, Always (`G`), reveals one of the pitfalls of mapping temporal logic to relational programming. Our first impulse is to define it analogously to `until`.

```
(define (always* g*)
  (let ((g (g*)))
    (conj g (next (always* g*))))))

(define-syntax alwayso
  (syntax-rules ()
    ((_ g) (always* (lambda () g)))))
```

A little experimentation, however, shows how this definition is problematic. A goal constructed with `always` will return a promise so long as the goal it encloses holds, and the empty stream as soon as it fails. While this behavior can be useful for a program that only wants to verify whether a state still holds, `always` will never construct a mature stream of solutions, since clearly the goal will never have been true *forever*, at least not in linear time.

There are two ways of getting around this problem. One is to modify the definition of `next` in such a way as to allow for an `eot` (end-of-time) accessor that would essentially cut off the forward recursion of delayed promises. Another approach is to define the weaker and impure `as-long-as`, which constructs a stream of solutions to the goal `h` that continues as long as the goal `g` still holds. This technique of writing 'guarded' goal constructors is reminiscent of the implementation of cuts in miniKanren.

```
(define (as-long-as* g* h*)
  (let ((g (g*)) (h (h*)))
    (lambda (s/c)
      (let (($ (g s/c)))
        (if (null? $) mzero
            (bind $ (disj h (next (as-long-as* g* h*)))))))))

(define-syntax as-long-as
  (syntax-rules ()
    ((_ g h) (as-long-as* (lambda () g) (lambda () h)))))
```

The Eventually (`F`) operator also has many useful applications, but presents a similar caveat regarding infinite time. Depending on the application, a guarded definition might be more appropriate, but the following definition will still be useful in many contexts.

```
(define (eventually* g*)
  (let ((g (g*)))
    (disj g (next (eventually* g*)))))

(define-syntax eventually
  (syntax-rules ()
    ((_ g) (eventually* (lambda () g)))))
```

We can use it to define a strong Until.

```
(define-syntax until
  (syntax-rules ()
    ((_ g h) (conj (precedes g h) (eventually h)))))
```

Clearly this is only a beginning, and as the above examples suggest, what constitutes a *useful* temporal relational programming language will be determined in part by the application domain. Still, developing a complete version of such a system would be an obvious next step. Another would integrating our basic temporal operators with a version of miniKanren that supports a constraint store and inequality. It would also be interesting to explore the integration of temporal logic with different representations of negation in miniKanren.


# Calculating Deltas With Incremental Search

Now we turn to a practical application, and see how temporal µKanren can be used to implement a simple data store with temporally-aware incremental search.

The motivation is as follows. In distributed systems such as a microservice architecture, we often want to send push updates based on *deltas*, or entries that have been  added to or removed from the database. In practice, this often means having a service that indiscriminately pushes all deltas to interested subscribers;  it is then the responsibility of each subscriber to filter the deltas and determine which, if any, are relevant to its own operations.

If we can calculate deltas to specific queries, however, this whole process can be greatly refined. Here we describe how an RDF database (triple store) can be implemented using temporal µKanren as its query language, that calculates deltas. By using the `next` constructor and a simple system of incremental indexes, we can store the final search positions for a query. Running a query will return both the current results and a delayed stream that when advanced will continue searching at the previous search-tree's leaves. Therefore, advancing the delayed stream after the database has been updated will return solutions that have been added to, or subtracted from the solution set. The full code is presented in Appendix B.

An RDF database stores semantic facts, or triples,^[Here we will only consider triples, though triple stores actually store quads, with the addition of the *graph*.] made up of a subject URI, predicate URI, and object URI or literal.

```
<http://ex.org/people/1> <http://xmlns.com/foaf/0.1/name> "John"
```

A minimalist triple store can be implemented using three indexes, allowing for the retrieval of groups of triples matching a given query pattern: `spo`, `pos`, and `osp`, where `s` is the subject, `p` the predicate, and `o` the object. Here, however, we want to know *incremental indexes:* for a given `s`, we need the indexed `p`'s in a form that can be easily compared to future `p`'s to determine whether new keys have been added. We keep separate incremental indexes for each index level, storing the incrementals as a simple `cons` list along with a map for quick existence checking. For each index we use a hash array mapped trie^[<https://github.com/ijp/pfds/blob/master/hamts.sls>] (persistent hash maps^[http://wiki.call-cc.org/eggref/4/persistent-hash-map] in Chicken) that allows for persistently storing successive states of the database through path copying. 

Our database is therefore defined as a set of seven incremental indexes (null, `s`, `sp`, `p`, `po`, `o`, `os`) plus the `spo` index for full triples. Adding a triple to the database is a matter of `cons`ing each element to the appropriate incrementals lists and adding a truthy value (here `#t`, though this could also be a more meaningful identifier or timestamp) to the full `spo` index. When deleting a triple, we leave the indexes, but update the triple's value in `spo` to `#f`. Here are the incremental indexes after adding the triple `<A> <B> <C>`.

```
<ø   [ #f => (<A> ...) ] >
<s   [ <A> => (<B> ...) ] >
<sp  [ (<A> <B>) => (<C> ...) ] >
<p   [ <B> => (<C> ...) ] >
<po  [ (<B> <C>) => (<A> ...) ] >
<o   [ <C> => (<A> ...) ] >
<os  [ (<C> <A>) => (<B> ...) ] >
<spo [ (<A> <B> <C>) => #t ] >
```

The main accessor is the goal constructor `triple-nolo` ('triple now or later') that descends recursively through the incremental indexes one level at a time, constructing an immature stream with the current indexes and saving the last search positions in a delayed stream. A dynamic parameter keeps track of the current database state. The following example shows how `triple-nolo` is used. To make clear what is going on, we keep track of the individual deltas for each goal, though in practice we usually want to know only if the solution was added (all `+`s) or removed (at least one `-`).

```
(define db0 (empty-db))

(define r 
  (parameterize ((latest-db db0))
    (run* (q)
          (fresh (o deltas d1 d2) 
                 (== q `(,deltas  ,o))
                 (== deltas `(,d1 ,d2))
                 (triple-nolo  d1 '<S> '<P> o)
                 (triple-nolo  d2 '<Q> '<R> o)))))
;; => #<promise>

(define db1
  (add-triples db0  '((<S> <P> <O1>)
                      (<S> <P> <O2>)
                      (<Q> <R> <O1>)
                      (<A> <B> <C>))))

(parameterize ((latest-db db1))
  (advance r))
;; => (((+ +) <O1>) . #<promise>)

(define db2
  (delete-triples db1 '((<S> <P> <O1>))))

(parameterize ((latest-db db2))
  (advance (advance r)))
;; => (((+ -)) <O1>) . #<promise>)

(define db3
  (add-triples db2 '((<S> <P> <O1>)
                     (<S> <P> <O3>)
                     (<Q> <R> <O3>)
                     (<S> <P> <M>)
                     (<Q> <R> <M>))))

(parameterize ((latest-db db3))
  (advance (advance (advance r))))
;; => (((+ +) <O1>) ((+ +) <M>) ((+ +) <O3>) . #<promise>)
```

Moreover, since the database states are persistent, we can calculate deltas over any two states. Keeping track of a stream of states and indexing them on time will therefore give us a truly time-traveling data store.


# Appendix A: Temporal µKanren


```
(define (var c) (vector c))
(define (var? x) (vector? x))
(define (var=? x1 x2) (= (vector-ref x1 0) (vector-ref x2 0)))

(define (walk u s)
  (let ((pr (and (var? u) (assp (lambda (v) (var=? u v)) s))))
    (if pr (walk (cdr pr) s) u)))

(define (ext-s x v s) `((,x . ,v) . ,s))

(define (== u v)
  (lambda (s/c)
    (let ((s (unify u v (car s/c))))
      (if s (unit `(,s . ,(cdr s/c))) mzero))))

(define (unit s/c) (cons s/c mzero))
(define mzero '())

(define (unify u v s)
  (let ((u (walk u s)) (v (walk v s)))
    (cond
      ((and (var? u) (var? v) (var=? u v)) s)
      ((var? u) (ext-s u v s))
      ((var? v) (ext-s v u s))
      ((and (pair? u) (pair? v))
       (let ((s (unify (car u) (car v) s)))
         (and s (unify (cdr u) (cdr v) s))))
      (else (and (eqv? u v) s)))))

(define (call/fresh f)
  (lambda (s/c)
    (let ((c (cdr s/c)))
      ((f (var c)) `(,(car s/c) . ,(+ c 1))))))

(define (disj g1 g2) (lambda (s/c) (mplus (g1 s/c) (g2 s/c))))
(define (conj g1 g2) (lambda (s/c) (bind (g1 s/c) g2)))

(define (mplus $1 $2)
  (cond
    ((null? $1) $2)
    ((procedure? $1) (lambda () (mplus $2 ($1))))
    ((and (promise? $1) (promise? $2)) 
     (delay (mplus (force $1) (force $2))))
    ((promise? $1) (mplus $2 $1))
    (else (cons (car $1) (mplus (cdr $1) $2)))))

(define (forward g)
  (lambda (s/c)
    (let rec (($ (g s/c)))
      (cond ((null? $) '())
	    ((promise? $) (force $))
            ((procedure? $) (lambda () (rec ($))))
	    (else (cons (car $) (rec (cdr $))))))))

(define (bind $ g)
   (cond
     ((null? $) mzero)
     ((procedure? $) (lambda () (bind ($) g)))
     ((promise? $) (delay (bind (force $) (forward g))))
     (else (mplus (g (car $)) (bind (cdr $) g)))))

(define-syntax next
  (syntax-rules ()
    ((_ g) (lambda (s/c) (delay (g s/c)))))) 
```


# Appendix B: RDF Store With Incremental Search

```
(define-syntax project
  (syntax-rules ()
    ((_ (x ...) g)
     (lambda (s/c)
       (let ((x (walk x (car s/c))) ...)
         (g s/c))))))

(define-record db s sp p po o os spo)

(define-record incrementals map list)

(define (empty-incrementals)
  (make-incrementals (persistent-map) '()))

(define (empty-db)
  (apply make-db
         (make-list 8 (persistent-map))))

(define latest-db (make-parameter (empty-db)))

(define (latest-incrementals accessor key)
  (incrementals-list
   (map-ref (accessor (latest-db)) key (empty-incrementals))))

(define (latest-triple s p o)
  (map-ref (db-spo (latest-db))
           (list s p o)))

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
                     (v           (disj (== delta '+) (next (leaf v))))
                     (else        (disj (== delta '-) (next (leaf v)))))))))))
```