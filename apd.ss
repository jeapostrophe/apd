#lang typed/scheme

; Types
(define-type-alias Strand (Listof Edge))

(define-type-alias Edge (U output input))
(define-struct: output ([pat : Pat]))
(define-struct: input ([pat : Pat]))

(define-type-alias Principal Symbol)

(define-type-alias Pat (U enc cat mt Data))
(define-struct: mt ())
(define-struct: enc ([content : Pat]
                     [key : Key]))
(define-struct: cat ([fst : Pat]
                     [snd : Pat]))

(define-type-alias Key (U public-key private-key hash-key unknowable-key))
(define-struct: public-key ([owner : Principal]) #:prefab)
(define-struct: private-key ([owner : Principal]) #:prefab)
(define-struct: hash-key () #:prefab)
(define-struct: unknowable-key () #:prefab)

(: key-inverse (Key -> Key))
(define (key-inverse k)
  (match k
    [(struct public-key (o))
     (make-private-key o)]
    [(struct private-key (o))
     (make-public-key o)]
    [(struct hash-key ())
     (make-unknowable-key)]))

(define-type-alias Data (U Symbol Key))

; Operations
(: make-cat* (Pat * -> Pat))
(define (make-cat* . ps)
  (define nmts (filter-not mt? ps))
  (match nmts
    [(list) (make-mt)]
    [(list p) p]
    [(list-rest p rs)
     (make-cat p (apply make-cat* rs))]))

(: edge-pat (Edge -> Pat))
(define (edge-pat e)
  (match e
    [(struct output (p)) p]
    [(struct input (p)) p]))

(: strand-print (Strand -> Void))
(define (strand-print s)
  (for-each edge-print s))

(: edge-print (Edge -> Void))
(define (edge-print e)
  (match e
    [(struct output (p)) (printf "+ ") (pat-print p) (printf "~n")]
    [(struct input (p)) (printf "- ") (pat-print p) (printf "~n")]))

(: pat-print (Pat -> Void))
(define (pat-print p)
  (match p
    [(struct enc (c o))
     (printf "{ ") (pat-print c) (printf " } ") (data-print o)]
    [(struct cat (f s))
     (pat-print f) (printf " ^ ") (pat-print s)]
    [(struct mt ())
     (void)]
    [s
     (when (or (symbol? s) (public-key? s) (private-key? s) (hash-key? s) (unknowable-key? s))
       (data-print s))]))

(: data-print (Data -> Void))
(define (data-print s)
  (match s
    [(? symbol? s)
     (printf "~a" s)]
    [(struct public-key (s))
     (printf "~a" s)]
    [(struct private-key (s))
     (printf "~a^-1" s)]
    [(struct hash-key ())
     (printf "H")]))

(: strand-knit (Strand -> Strand))
(define (strand-knit s)
  (match s
    [(list)
     empty]
    [(list-rest (struct output (f)) (list-rest (struct output (s)) rst))
     (strand-knit (list* (make-output (make-cat f s)) rst))]
    [(list-rest (struct input (f)) (list-rest (struct input (s)) rst))
     (strand-knit (list* (make-input (make-cat f s)) rst))]
    [(list-rest f rst)
     (list* f (strand-knit rst))]))

(define-type-alias (Setof A) (HashTable A Boolean))

(define: (A B) (empty-ht) : (HashTable A B) 
  (make-immutable-hash empty))
(define: (A B) (ht-merge [h1 : (HashTable A B)] [h2 : (HashTable A B)]) : (HashTable A B)
  (define: h2ps : (Listof (Pair A B))
    (hash-map h2 (inst cons A B)))
  (foldl (lambda: ([e : (Pair A B)] [a : (HashTable A B)])
                  (hash-set a (car e) (cdr e)))
         h1 h2ps))

(define: (A) (empty-set) : (Setof A)
  ((inst empty-ht A Boolean)))
(define: (A) (set-merge [s1 : (Setof A)] [s2 : (Setof A)]) : (Setof A)
  ((inst ht-merge A Boolean) s1 s2))
(: set-add (All (A) ((Setof A) A -> (Setof A))))
(define (set-add s x) (hash-set s x #t))
(: set-singleton (All (A) (A -> (Setof A))))
(define (set-singleton e)
  (set-add ((inst empty-set A)) e))
(: set->list (All (A) ((Setof A) -> (Listof A))))
(define (set->list s)
  (hash-map s (lambda: ([k : A] [v : Boolean]) k)))
(define: (A) (list->set [l : (Listof A)]) : (Setof A)
  (foldl (lambda: ([e : A] [a : (Setof A)])
                  (set-add a e))
         ((inst empty-set A)) l))
(define: (A) (set-diff [s : (Setof A)] [t : (Setof A)]) : (Setof A)
  (define ts (set->list t))
  (foldl (lambda: ([e : A] [a : (Setof A)])
                  (hash-remove a e))
         s ts))
(define: (A) (set-in? [s : (Setof A)] [e : A]) : Boolean
  (hash-has-key? s e))
(define: (A) (set-filter [s : (Setof A)] [p? : (A -> Boolean)]) : (Setof A)
  (define ss (set->list s))
  (foldl (lambda: ([e : A] [a : (Setof A)])
                  (if (p? e)
                      (hash-set a e #t)
                      a))
         ((inst empty-set A)) ss))
(define: (A) (set-cardinality [s : (Setof A)]) : Number
  (hash-count s))
(define: (A) (set-intersection [s : (Setof A)] [t : (Setof A)]) : (Setof A)
  (define ts (set->list t))
  (foldl (lambda: ([e : A] [a : (Setof A)])
                  (if (hash-has-key? s e)
                      (hash-set a e #t)
                      a))
         ((inst empty-set A)) ts))

(: set-any? (All (A) ((Setof A) (A -> Boolean) -> Boolean)))
(define (set-any? s p)
  (ormap p (set->list s)))
(: set-subset? (All (A) ((Setof A) (Setof A) -> Boolean)))
(define (set-subset? x y)
  (set-any? x (lambda: ([e : A]) (set-in? y e))))

(define-type-alias Summary (Option summary))
(define-struct: summary ([plain : (Setof Data)]
                         [enc : (HashTable Key Summary)]))
(define empty-summary #f)

(: summary-merge (Summary Summary -> Summary))
(define (summary-merge s1 s2)
  (match s1
    [#f s2]
    [(struct summary (p1 e1))
     (match s2
       [#f s1]
       [(struct summary (p2 e2))
        (make-summary (set-merge p1 p2)
                      (ht-merge e1 e2))])]))

(: pat->summary (Pat -> Summary))
(define (pat->summary p)
  (match p
    [(struct enc (c k))
     (make-summary (empty-set)
                   (make-immutable-hash (list (cons k (pat->summary c)))))]
    [(struct cat (f s))
     (summary-merge (pat->summary f) (pat->summary s))]
    [(struct mt ())
     empty-summary]
    [s
     (if (or (symbol? s) (public-key? s) (private-key? s) (hash-key? s) (unknowable-key? s))
         (make-summary (set-singleton s) (empty-ht))
         empty-summary)]))

(: summary->pat (Summary -> Pat))
(define (summary->pat s)
  (match s
    [#f (make-mt)]
    [(struct summary (p e))
     (make-cat* (apply make-cat* (set->list p))
                (apply make-cat*
                       (hash-map e (lambda: ([k : Key] [s : Summary])
                                            (make-enc (summary->pat s) k)))))]))

(: pat-canon (Pat -> Pat))
(define (pat-canon p)
  (summary->pat (pat->summary p)))

(: edge-canon (Edge -> Edge))
(define (edge-canon e)
  (match e
    [(struct output (p)) (make-output (pat-canon p))]
    [(struct input (p)) (make-input (pat-canon p))]))

(: strand-canon (Strand -> Strand))
(define (strand-canon s)
  (map edge-canon s))

(define-type-alias Knowledge (Option (U k-and k-or k-implies k-atoms)))
(define-struct: k-and ([lhs : Knowledge]
                       [rhs : Knowledge])
  #:prefab)
(define-struct: k-or ([lhs : Knowledge]
                      [rhs : Knowledge])
  #:prefab)
(define-struct: k-implies ([if : Data]
                           [then : Knowledge])
  #:prefab)
(define-struct: k-atoms ([d : (Setof Data)])
  #:prefab)

(: make-k-atoms* : ((Setof Data) -> Knowledge))
(define (make-k-atoms* s)
  (if (zero? (set-cardinality s))
      #f
      (make-k-atoms s)))
(: make-k-and* : (Knowledge Knowledge -> Knowledge))
(define (make-k-and* l r)
  (cond [(and (k-atoms? l) (k-atoms? r))
         (make-k-atoms* (set-merge (k-atoms-d l) (k-atoms-d r)))]
        [(and l r) (make-k-and l r)]
        [l l]
        [else r]))
(: make-k-or* : (Knowledge Knowledge -> Knowledge))
(define (make-k-or* l r)
  (cond [(and (k-atoms? l) (k-atoms? r))
         (let: ([inter : (Setof Data) (set-intersection (k-atoms-d l) (k-atoms-d r))])
               (make-k-and* (make-k-atoms* inter)
                            (make-k-or** (make-k-atoms* (set-diff (k-atoms-d l) inter))
                                         (make-k-atoms* (set-diff (k-atoms-d r) inter)))))]
        [else
         (make-k-or** l r)]))
(: make-k-or** : (Knowledge Knowledge -> Knowledge))
(define (make-k-or** l r)
  (cond [(and l r) (make-k-or l r)]
        [l l]
        [else r]))
(: make-k-implies* : (Data Knowledge -> Knowledge))
(define (make-k-implies* d k)
  (cond [(unknowable-key? d) #f]
        [(and d k) (make-k-implies d k)]
        [d #f]
        [else k]))

(define-type-alias DNF-Knowledge DNF-Or)
(define-type-alias DNF-Or (Setof DNF-And))
(define-type-alias DNF-And (Setof Data))

(: knowledge-dnf (Knowledge -> DNF-Knowledge))
(define (knowledge-dnf k)
  (match k
    [(struct k-and (l r))
     (define: ld : DNF-Knowledge
       (knowledge-dnf l))
     (define: rd : DNF-Knowledge
       (knowledge-dnf r))
     (list->set
      (apply
       append
       ((inst map (Listof DNF-And) DNF-And)
        (lambda: ([le : DNF-And])
                 ((inst map DNF-And DNF-And)
                  (lambda: ([re : DNF-And])
                           (ann (set-merge le re) DNF-And))
                  (set->list rd)))
        (set->list ld))))]
    [(struct k-or (l r))
     (set-merge (knowledge-dnf l) (knowledge-dnf r))]
    [(struct k-atoms (ds))
     (set-singleton ds)]))

(: dnf-knowledge-possible (DNF-Knowledge -> DNF-Knowledge))
(define (dnf-knowledge-possible dk)
  (set-filter dk (lambda: ([ds : DNF-And]) (not (set-in? ds (make-unknowable-key))))))

(: knowledge-in/db (Knowledge Data Knowledge -> Boolean))
(define (knowledge-in/db db d k)
  (match k
    [(struct k-and (l r))
     (or (knowledge-in/db db d l)
         (knowledge-in/db db d r))]
    [(struct k-or (l r))
     (and (knowledge-in/db db d l)
          (knowledge-in/db db d r))]
    [(struct k-implies (i t))
     (if (equal? d i)
         #f
         (if (knowledge-in/db db i db)
             (knowledge-in/db db d t)
             #f))]
    [(struct k-atoms (ds))
     (set-in? ds d)]))

(: knowledge-in (Data Knowledge -> Boolean))
(define (knowledge-in d k)
  (knowledge-in/db k d k))

(: knowledge-trim (Knowledge Knowledge -> Knowledge))
(define (knowledge-trim what-you-know what-you-want-to-know)
  (match what-you-want-to-know
    [(struct k-and (l r))
     (make-k-and* (knowledge-trim what-you-know l)
                  (knowledge-trim what-you-know r))]
    [(struct k-or (l r))
     (make-k-or* (knowledge-trim what-you-know l)
                 (knowledge-trim what-you-know r))]
    [(struct k-implies (i t))
     (if (knowledge-in i what-you-know)
         (knowledge-trim what-you-know t)
         (make-k-implies i (knowledge-trim what-you-know t)))]
    [(struct k-atoms (ds))
     (make-k-atoms* (set-filter ds
                                (lambda: ([s : Data])
                                         (not (knowledge-in s what-you-know)))))]))

(: pat-to-send (Pat -> Knowledge))
(define (pat-to-send p)
  (match p
    [(struct enc (c k))
     (make-k-and* (pat-to-send c) (make-k-atoms* (set-add ((inst empty-set Data)) k)))]
    [(struct cat (f s))
     (make-k-and* (pat-to-send f) (pat-to-send s))]
    [(struct mt ())
     #f]
    [s
     (if (or (symbol? s) (public-key? s) (private-key? s) (hash-key? s) (unknowable-key? s))
         (make-k-atoms* (set-singleton s))
         #f)]))

(: pat-to-recv (Pat -> Knowledge))
(define (pat-to-recv p)
  (match p
    [(struct enc (c k))
     (make-k-or* (pat-to-send p)
                 (make-k-and* (pat-to-recv c)
                              (make-k-atoms* (set-singleton (key-inverse k)))))]
    [(struct cat (f s))
     (make-k-and* (pat-to-recv f) (pat-to-recv s))]
    [(struct mt ())
     #f]
    [s
     #f]))

(: pat-knowledge-on-recv (Pat -> Knowledge))
(define (pat-knowledge-on-recv p)
  (match p
    [(struct enc (c k))
     (make-k-implies* (key-inverse k)
                      (pat-knowledge-on-recv c))]
    [(struct cat (f s))
     (make-k-and* (pat-knowledge-on-recv f) (pat-knowledge-on-recv s))]
    [(struct mt ())
     #f]
    [s
     (if (or (symbol? s) (public-key? s) (private-key? s) (hash-key? s) (unknowable-key? s))
         (make-k-atoms* (set-singleton s))
         #f)]))

(: strand-to-execute (Strand -> Knowledge))
(define (strand-to-execute s)
  (match s
    [(list)
     #f]
    [(list-rest e rs)
     (define rs-needed
       (strand-to-execute rs))
     (match e
       [(struct input (p))
        (make-k-and* (pat-to-recv p)
                     (knowledge-trim (pat-knowledge-on-recv p)
                                     rs-needed))]
       [(struct output (p))
        (make-k-and* (pat-to-send p)
                     rs-needed)])]))

(: dnf-knowledge-print (DNF-Knowledge -> Void))
(define (dnf-knowledge-print dk)
  (for-each dnf-and-print (set->list dk)))

(: dnf-and-print (DNF-And -> Void))
(define (dnf-and-print ds)
  (printf "{")
  (for-each
   (lambda: ([d : Data])
            (printf " ")
            (data-print d))
   (set->list ds))
  (printf " }~n"))

(: strand-can-execute? (Strand DNF-And -> Boolean))
(define (strand-can-execute? s ik)
  (define nk (knowledge-dnf (strand-to-execute s)))
  (set-any? nk (lambda: ([k : DNF-And]) (set-subset? ik k))))

; Redaction
(: pat-recv-redact (Pat DNF-And -> Pat))
(define (pat-recv-redact p K)
  (match p
    [(struct enc (c k))
     (cond
       [(or (set-in? K k)
            (set-in? K (key-inverse k)))
        (make-enc (pat-recv-redact c K) k)]
       [else
        (gensym 'wildcard)])]
    [(struct cat (f s))
     (make-cat (pat-recv-redact f K)
               (pat-recv-redact s K))]
    [(struct mt ())
     p]
    [s
     s]))

; Bundles
(define-type-alias Bundle (Listof Strand))

(: bundle-valid? (Bundle -> Boolean))
(define (bundle-valid? b)
  (andmap (lambda: ([s : Strand])
                   (strand-valid-in? b s))
          b))

(: strand-valid-in? (Bundle Strand -> Boolean))
(define (strand-valid-in? b s)
  (andmap (lambda: ([e : Edge])
                   (edge-valid-in? b e))
          s))

(: edge-valid-in? (Bundle Edge -> Boolean))
(define (edge-valid-in? b e1)
  (ormap (lambda: ([s : Strand])
                  (ormap (lambda: ([e2 : Edge])
                                  (edge-compatible? e1 e2))
                         s))
         b))

(: edge-compatible? (Edge Edge -> Boolean))
(define (edge-compatible? e1 e2)
  (or (and (output? e1) (input? e2)
           (pat-compatible? (output-pat e1) (input-pat e2)))
      (and (input? e1) (output? e2)
           (pat-compatible? (input-pat e1) (output-pat e2)))))

(: pat-compatible? (Pat Pat -> Boolean))
(define (pat-compatible? p1 p2)
  (match p1
    [(struct enc (c1 k1))
     (match p2
       [(struct enc (c2 k2))
        (and (pat-compatible? c1 c2)
             (pat-compatible? k1 k2))]
       [_
        #f])]
    [(struct cat (f1 s1))
     (match p2
       [(struct cat (f2 s2))
        (and (pat-compatible? f1 f2)
             (pat-compatible? s1 s2))]
       [_
        #f])]
    [(struct mt ())
     (match p2
       [(struct mt ()) #t]
       [_ #f])]
    [_
     (equal? p1 p2)]))

; Penetrators
(: M (Symbol -> Strand))
(define (M t)
  (list (make-output t)))
(: K (Key -> Strand))
(define (K k)
  (list (make-output k)))
(: C (Pat Pat -> Strand))
(define (C g h)
  (list (make-input g)
        (make-input h)
        (make-output (make-cat g h))))
(: S (Pat Pat -> Strand))
(define (S g h)
  (list (make-input (make-cat g h))
        (make-output g)
        (make-output h)))
(: E (Pat Key -> Strand))
(define (E h K)
  (list (make-input K)
        (make-input h)
        (make-output (make-enc h K))))
(: D (Pat Key -> Strand))
(define (D h K)
  (list (make-input (key-inverse K))
        (make-input (make-enc h K))
        (make-output h)))

; Example
(define (make-nonce o r) (string->symbol (format "N_~a,~a" o r)))
(define (make-sec o r) (string->symbol (format "sec_~a,~a" o r)))
(define (make-shared o) (string->symbol (format "shared_~a" o)))

(: auth-1/p (Principal Principal -> Strand))
(define (auth-1/p P Q)
  (list (make-output (make-enc (make-cat* (make-nonce P Q)
                                          (make-sec P Q)
                                          (make-shared P))
                               (make-public-key Q)))
        (make-input (make-enc (make-cat (make-nonce P Q)
                                        (make-enc (make-cat (make-sec P Q) (make-shared P))
                                                  (make-hash-key)))
                              (make-private-key Q)))))

(: auth-2/p (Principal Principal -> Strand))
(define (auth-2/p P Q)
  (list 
   (make-input (make-cat (make-nonce Q P) 
                         (make-enc (make-cat (make-nonce P Q)
                                             (make-enc (make-cat (make-sec P Q) (make-shared P))
                                                       (make-hash-key)))
                                   (make-private-key Q))))   
   (make-output (make-enc (make-cat* (make-nonce P Q)
                                     (make-nonce Q P)
                                     (make-enc (make-cat (make-sec P Q) (make-shared P))
                                               (make-hash-key)))
                          (make-private-key P)))))

(: subprotocol/p (Principal Principal -> Strand))
(define (subprotocol/p P Q)
  (append (auth-1/p P Q) (auth-2/p P Q)))

(: show-protocol (Strand DNF-And -> Boolean))
(define (show-protocol s k)
  (define dk (dnf-knowledge-possible (knowledge-dnf (strand-to-execute s))))
  (strand-print s)
  (printf "Knowledge:~n")
  (dnf-knowledge-print dk)
  (printf "Initial Knowledge:~n")
  (dnf-and-print k)
  (strand-can-execute? s k))

"P -> Q"
(show-protocol (subprotocol/p 'P 'Q)
               (list->set (list (make-hash-key)
                                (make-nonce 'P 'Q)
                                (make-sec 'P 'Q)
                                (make-shared 'P)
                                (make-public-key 'Q)
                                (make-public-key 'P)
                                (make-private-key 'P))))

"P -> Q (knit)"
(show-protocol (strand-knit (subprotocol/p 'P 'Q))
               (list->set (list (make-hash-key)
                                (make-nonce 'P 'Q)
                                (make-sec 'P 'Q)
                                (make-shared 'P)
                                (make-public-key 'Q)
                                (make-public-key 'P)
                                (make-private-key 'P))))

"Canon"
(show-protocol (strand-canon (strand-knit (subprotocol/p 'P 'Q)))
               (list->set (list (make-hash-key)
                                (make-nonce 'P 'Q)
                                (make-sec 'P 'Q)
                                (make-shared 'P)
                                (make-public-key 'Q)
                                (make-public-key 'P)
                                (make-private-key 'P))))

"Whole thing"
(: whole (Principal Principal Principal -> Strand)) 
(define (whole P Q S)
  (append (subprotocol/p P Q)
          (subprotocol/p P S)))
(show-protocol (whole 'P 'Q 's)
               (list->set (list (make-hash-key)
                                (make-nonce 'P 'Q)
                                (make-nonce 'P 'S)
                                (make-sec 'P 'Q)
                                (make-sec 'P 'S)
                                (make-shared 'P)
                                (make-public-key 'Q)
                                (make-public-key 'S)
                                (make-public-key 'P)
                                (make-private-key 'P))))

(: atspect (Principal Principal Principal -> Bundle)) 
(define (atspect c m b)
  (list (whole c m b)
        (whole m c b)
        (whole b m c)))
