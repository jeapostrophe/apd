#lang scheme
(require scheme/set)

; Helpers
(define (member? v l)
  (and (member v l) #t))
(define (member1 v l)
  (match (member v l)
    [(list-rest a _) a]
    [_ #f]))
(define-struct why (p) #:prefab)
(define (why-false? v)
  (if v
      (why? v)
      #t))
(define (why-path v)
  (if v
      (if (why? v)
          (why-p v)
          (error 'why-path "Not why-false?"))
      empty))
(define why-true?
  (negate why-false?))
(define why->bool
  why-true?)

(define-syntax-rule (and/why e1 e2)
  (let ([tmp e1])
    (if (why-false? tmp)
        (make-why
         (cons 'e1
               (why-path tmp)))         
        e2)))
(define-syntax-rule (or/why e1 e2)
  (let ([tmp e1])
    (if (why-false? tmp)
        e2
        tmp)))
(define-syntax-rule (for/and/why ([e seq]) body ...)
  (for/fold ([a #t])
    ([e seq]
     [i (in-naturals)])
    (if (why-true? a)
        (let ([tmp (let () body ...)])
          (if (why-false? tmp)
              (make-why 
               (cons `(seq @ ,i => ,e)
                     (why-path tmp)))
              tmp))
        a)))
(define-syntax-rule (for/or/why ([e seq]) body ...)
  (for/fold ([a #f])
    ([e seq]
     [i (in-naturals)])
    (if (why-false? a)
        (let ([tmp (let () body ...)])
          (if (why-false? tmp)
              (make-why 
               (cons `(seq @ ,i => ,e)
                     (why-path tmp)))
              tmp))
        a)))

(define (andmap/why f l)
  (for/and/why ([e (in-list l)])
               (f e)))

; Strands
(define (protocol . as) (make-immutable-hasheq as))
(define role cons)
(define strand list)
(define-struct send (m) #:prefab)
(define-struct recv (m) #:prefab)
(define-struct enc (content key) #:prefab)
(define-struct key (comment) #:prefab)

(define empty-protocol (protocol))
(define empty-role (role (set) (strand)))
(define + make-send)
(define - make-recv)
(define (nonce c) (cons 'nonce c))
(define (pubkey p) (make-key (list 'pub p)))
(define (privkey p) (make-key (list 'priv p)))
(define hash-key (make-key 'hash))
(define unknown-key (make-key 'unknown))
(define (pubenc c p) (make-enc c (pubkey p)))
(define (pubsign c p) (make-enc c (privkey p)))
(define (hash c) (make-enc c hash-key))

; Data ops
(define key-inverse
  (match-lambda
    [(struct key ((list 'pub p)))
     (privkey p)]
    [(struct key ((list 'priv p)))
     (pubkey p)]
    [_
     unknown-key]))

; Pat ops
(define (pat-send-okay? k p)
  (or/why (set-member? k p)
          (match p
            [(struct enc (c key))
             (and/why (set-member? k key)
                      (pat-send-okay? k c))]
            [(? list? l)
             (andmap/why (curry pat-send-okay? k) l)]
            [(? string?)
             #t]
            [else
             #f])))

(define (pat-recv-okay? k p)
  (or/why (set-member? k p)
          (match p
            [(struct enc (c key))
             (or/why (and/why (set-member? k key)
                              (pat-send-okay? k c))
                     (and/why (set-member? k (key-inverse key))
                              (pat-recv-okay? k c)))]
            [(? list? l)
             (andmap/why (curry pat-recv-okay? k) l)]
            [else
             #t])))

(define (pat-recv-new k p)
  (set-add
   (match p
     [(struct enc (c key))
      (if (set-member? k (key-inverse key))
          (pat-recv-new k c)
          (set))]
     [(? list? l)
      (for/fold ([nk (set)])
        ([sp (in-list l)])
        (set-union nk (pat-recv-new k sp)))]
     [else
      (set)])
   p))

; Event ops
(define (evt-okay? k e)
  (match e
    [(struct send (p))
     (pat-send-okay? k p)]
    [(struct recv (p))
     (pat-recv-okay? k p)]))

(define (evt-new k e)
  (match e
    [(struct send (p))
     (set)]
    [(struct recv (p))
     (pat-recv-new k p)]))

(define (evt-reverse e)
  (match e
    [(struct send (p))
     (- p)]
    [(struct recv (p))
     (+ p)]))

; Strand ops
(define (strand-okay? k s)
  (match s
    [(list) #t]
    [(list-rest e s)
     (and/why (evt-okay? k e)
              (strand-okay? (set-union k (evt-new k e)) s))]))

; Role ops
(define (role-merge r1 r2)
  (role (set-union (car r1) (car r2))
        (append (cdr r1) (cdr r2))))

; Protocol ops
(define (protocol-merge b1 b2)
  (for/fold ([bm b1])
    ([(role init+strand) (in-hash b2)])
    (hash-update bm role 
                 (curry role-merge init+strand)
                 empty-role)))

(define (protocol-okay? p)
  (why->bool
   (for/and/why ([init+strand (in-hash-values p)])
                (match-define (cons init strand) init+strand)
                (and/why (strand-okay? init strand)
                         (for/and/why ([e (in-list strand)])
                                      (protocol-evt-in? (evt-reverse e) p))))))

(define (protocol-evt-in? e p)
  (for/or/why ([r (in-hash-keys p)])
              (define init+strand (hash-ref p r))
              (match-define (cons init strand) init+strand)
              (member1 e strand)))

; Bundle
(define digraph hash?)
(define-struct bundle (N -> =>) #:prefab)
(define (protocol->bundle p)
  (define N
    (for*/list ([init+strand (in-hash-values p)]
                #:when (pair? init+strand)
                [e (in-list (cdr init+strand))])
      e))
  (define =>
    (for/fold ([=> (make-immutable-hasheq empty)])
      ([init+strand (in-hash-values p)]
       #:when (pair? init+strand)
       #:when (pair? (cdr init+strand)))
      (for/fold ([=> =>])
        ([n1 (in-list (cdr init+strand))]
         [n2 (in-list (cdr (cdr init+strand)))])
        (hash-set => n1 n2))))
  (define ->
    (for*/hasheq ([init+strand (in-hash-values p)]
                  #:when (pair? init+strand)
                  [n1 (in-list (cdr init+strand))]
                  #:when (send? n1))
      (values n1 (protocol-evt-in? (evt-reverse n1) p))))  
  (make-bundle N -> =>))

(define (hasheq-reverse ht)
  (for/hasheq ([(k v) (in-hash ht)])
    (values v k)))

(define (print-bundle b)
  (match-define (struct bundle (N -> =>)) b)
  (define <- (hasheq-reverse ->))
  (define <= (hasheq-reverse =>))
  (define-values (depth->N max-depth)
    (for/fold ([ht (make-immutable-hasheq empty)]
               [max-depth -inf.0])
      ([n (in-list N)])
      (define i
        (let loop ([t n])
          (let ([next (hash-ref <= t #f)])
            (if next
                (add1 (loop next))
                0))))
      (values (hash-update ht i (curry list* n) empty)
              (max max-depth i))))
  (define n->i
    (for/hasheq ([i (in-naturals)]
                 [n (in-list N)])
      (values n (format "node~a" i))))
  (printf "digraph at {~n")
  
  ; Print out the strands
  (for ([top (in-list (hash-ref depth->N 0))])
    (printf "subgraph ~a {~n" (gensym 'cluster_))
    (let loop ([n top])
      (let ([next (hash-ref => n #f)])
        (when next
          (printf "~a -> ~a [arrowhead = veevee];~n"
                  (hash-ref n->i n)
                  (hash-ref n->i next))
          (loop next))))
    (printf "}~n"))
  
  ; XXX Print node labels
  
  ; Print out the interconnections
  (for ([n1 (in-list N)])
    (define n2 (hash-ref -> n1 #f))
    (when n2
      (printf "{")
      (printf "rank = same; ")
      (printf "~a -> ~a;"
              (hash-ref n->i n1)
              (hash-ref n->i n2))
      (printf "}~n")))
  
  (printf "}~n"))

#;(define (print-bundle b)
    (match-define (struct bundle (N -> =>)) b)
    (define <- (hasheq-reverse ->))
    (define <= (hasheq-reverse =>))
    (define-values (depth->N max-depth)
      (for/fold ([ht (make-immutable-hasheq empty)]
                 [max-depth -inf.0])
        ([n (in-list N)])
        (define i
          (let loop ([t n])
            (let ([next (hash-ref <= t #f)])
              (if next
                  (add1 (loop next))
                  0))))
        (values (hash-update ht i (curry list* n) empty)
                (max max-depth i))))
    (for ([d (in-range max-depth)])
      (printf "~a. " d)
      (for ([n (hash-ref depth->N d empty)]
            [i (in-naturals)])
        (printf "\t~a" (* (expt 2 d) (expt 3 i))))
      (printf "~n")))      

; ATSPECT
(define (subprotocol c_i P Q)
  (define m0
    (pubenc (list c_i "S" 
                  (nonce (cons P Q))
                  (list 'sec P Q)
                  (list 'shared P))
            Q))
  (define n0 m0)
  (define m1
    (list (nonce (cons Q P))
          (pubsign (list c_i "A"
                         (nonce (cons P Q))
                         (hash (list (list 'sec P Q)
                                     (list 'shared P))))
                   Q)))
  (define n1 m1)
  (define m2
    (pubsign (list c_i "R"
                   (nonce (cons P Q))
                   (nonce (cons Q P))
                   (hash (list (list 'sec P Q)
                               (list 'shared P))))
             P))
  (define n2 m2)  
  (protocol (cons P (role (set (nonce (cons P Q))
                               (list 'sec P Q)
                               (list 'shared P)
                               (pubkey P)
                               (privkey P)
                               (pubkey Q)
                               hash-key)
                          (strand (+ m0) (- m1) (+ m2))))
            (cons Q (role (set (nonce (cons Q P))
                               (pubkey Q)
                               (privkey Q)
                               (pubkey P)
                               hash-key)
                          (strand (- n0) (+ n1) (- n2))))))

(define roles '("C" "M" "B"))
(define atspect
  (for*/fold ([b empty-protocol])
    ([r1 (in-list roles)]
     [r2 (in-list roles)]
     #:when (not (equal? r1 r2)))
    (protocol-merge b
                    (subprotocol (format "~a.~a" r1 r2)
                                 r1 r2))))

atspect
(protocol-okay? atspect)
(define atspect-b
  (protocol->bundle atspect))
(with-output-to-file "atspect.dot"
  #:exists 'replace
  (lambda ()
    (print-bundle atspect-b)))