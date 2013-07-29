#lang racket
(require racket/unit)
(require racket/trace)

(struct -unmapped ()) (define unmapped (-unmapped))

;; Temporal contracts
(struct ¬ (T) #:transparent)
(struct !ev (A) #:transparent)
(struct · (T₀ T₁) #:transparent)
(struct kl (T) #:transparent)
(struct bind (B T) #:transparent)
(struct ∪ (Ts) #:transparent)
(struct ∩ (Ts) #:transparent)
(struct -ε () #:transparent) (define ε (-ε))
(define (tcon? x)
  (or (¬? x) (·? x) (!ev? x) (event? x) (kl? x) (bind? x) (∪? x) (∩? x)))

;; Pattern-matching state machines (PMSMs)
;; δ : Map[Q, Map[Pattern, Set[Q]]]
(struct PMSM (q₀ ≃ ary δ) #:transparent)
(define (δ-extend δ q pat q′)
  (match (hash-ref δ q unmapped)
    [(== unmapped eq?) (hash-set δ q (hash pat (set q′)))]
    [pqs (match (hash-ref pqs pat unmapped)
           [(== unmapped eq?) (hash-set δ q (hash-set pqs pat (set q′)))]
           [qs (hash-set δ q (hash-set pqs pat (set-add qs q′)))])]))
(struct State (q γ t) #:transparent)
(struct constructed (c data) #:transparent)
(struct !constructed (c data) #:transparent)

(define ∅ (set))
;; Top level
(struct tl (T t) #:transparent)
;; #f is the empty machine

(define (call nf pa) (constructed 'call (list nf pa)))
(define (ret nf pa) (constructed 'call (list nf pa)))
(define-match-expander call: (λ (stx) (syntax-case stx ()
                                       [(_ nf pa) #'(constructed 'call (list nf pa))])))
(define-match-expander ret: (λ (stx) (syntax-case stx ()
                                       [(_ nf pv) #'(constructed 'ret (list nf pv))])))
(struct -Any () #:transparent) (define Any (-Any))
(define/match (event? x)
  [((constructed (or 'call 'ret) (list _ _))) #t]
  [(_) #f])
(struct $ (x) #:transparent)
(struct □ (x) #:transparent)

(define ρ₀ #hasheq())
(define Tcon0 (¬ (cons (call Any Any) ρ₀)))
(define Tcon1 (¬ (· (cons (call Any Any) ρ₀) (cons (kl Any) ρ₀))))
(define Tcon2 (¬ (cons (call Any 0) ρ₀)))
(define π0 (list (call values 0)))
(define π1 (list (call values 1)))

;; Ternary logic
(struct -must ()) (define must (-must))
(struct -may ()) (define may (-may))

(define/match (L¬ t)
  [((== must eq?)) #f]
  [((== may eq?)) may]
  [(#f) must])

(define/match (∧ t₀ t₁)
  [((== must eq?) (== must eq?)) must]
  [(#f _) #f]
  [(_ #f) #f]
  [(_ _) may])

(define/match (∨ t₀ t₁)
  [(#f #f) #f]
  [((== must eq?) _) must]
  [(_ (== must eq?)) must]
  [(_ _) may])

;; Like ∨, only may is now the top element
(define/match (U∨ t₀ t₁)
  [(#f #f) #f]
  [((== may eq?) _) may]
  [(_ (== may eq?)) may]
  [(_ _) must])

;; valuations with updated bindings
(struct mres (t ρ) #:transparent)

(define Σ̂* (kl Any))
(define Σ* (tl Σ̂* must))

(define/match (·simpl T₀ T₁)
  [((== ε eq?) T₁) T₁]
  [(T₀ (== ε eq?)) T₀]
  ;; Right-associate
  [((· T₀₀ T₀₁) T₁) (· T₀₀ (·simpl T₀₁ T₁))]
  ;; No simplifications
  [(T₀ T₁) (· T₀ T₁)])

(define (∪simpl Ts)
  (cond [(set-empty? Ts) #f]
        [(= (set-count Ts) 1) (set-first Ts)]
        [else (∪ Ts)]))

(define (∩simpl Ts)
  (cond [(set-empty? Ts) Σ̂*]
        [(= (set-count Ts) 1) (set-first Ts)]
        [else (∩ Ts)]))

(define (◃ ρ₀ ρ₁)
  (for/fold ([ρ ρ₀]) ([(k v) (in-hash ρ₁)])
    (hash-set ρ k v)))

(define ((opres op) r₀ r₁)
  (and r₀ r₁
       (match* (r₀ r₁)
         [((mres t₀ ρ₀) (mres t₁ ρ₁))
          (mres (t₀ . op . t₁) (ρ₀ . ◃ . ρ₁))])))
(define ⊓ (opres ∧))

(define (⨅ S f)
  (let/ec break
    (define-values (t ρ)
      (for/fold ([t must]
                 [ρ #hasheq()])
          ([s (in-set S)])
        (match (f s)
          [#f (break #f)]
          [(mres t′ ρ′) (values (∧ t t′) (ρ . ◃ . ρ′))])))
    (mres t ρ)))

(define (⨅/lst f L R)
  (let/ec break
    (define-values (t ρ)
      (for/fold ([t must]
                 [ρ #hasheq()])
          ([l (in-list L)]
           [r (in-list R)])
        (match (f l r)
          [#f (break #f)]
          [(mres t′ ρ′) (values (∧ t t′) (ρ . ◃ . ρ′))])))
    (mres t ρ)))

;; Is the contract nullable?
(define (ν? T)
  (match T
    [(or (kl _) (== ε eq?)) #t]
    [(· T₀ T₁) (and (ν? T₀) (ν? T₁))]
    [(∪ Ts) (for/or ([T (in-set Ts)]) (ν? T))]
    [(∩ Ts) (for/and ([T (in-set Ts)]) (ν? T))]
    [(¬ T) (not (ν? T))]
    [(cons T ρ) (ν? T)]
    [_ #f])) ;; bind, event, nonevent

(define/match (negate T)
  [((¬ T)) T]
  [(T) (¬ T)])

(define/match (flip B)
  [((call: nf xa)) (!ev (call nf Any))]
  [((ret: nf xv)) (!ev (ret nf Any))])

(define/match (C T)
  [((== ε eq?)) (set Any)]
  [((== Any eq?)) (set Any #f)]
  [((!ev A))
   (if (eq? A Any)
       (set Any #f)
       (set A (!constructed (constructed-c A) (constructed-data A))))]
  [((constructed kind pats))
   (set T (!constructed kind pats))]
  [((or (∪ Ts) (∩ Ts))) (C⋀ Ts)]
  [((or (kl T) (¬ T))) (C T)]
  [((· T₀ T₁))
   (if (ν? T₀)
       (C∧ (C T₀) (C T₁))
       (C T₀))]
  [((bind B T)) (set-union (C T) (set B (flip B)))]
  [((cons T ρ)) (C T)]
  [(_) (error 'C "bad Tcon ~a" T)])

(define/match (res-∧ r₀ r₁)
  [(#f _) #f]
  [(_ #f) #f]
  [((mres t As) (mres t′ As′))
   (mres (∧ t t′) (cond
                   [(set? As) (if (set? As′)
                                  (set-union As As′)
                                  (set-add As As′))]
                   [(set? As′) (set-add As′ As)]
                   [else (set As As′)]))])

(define (evt-intersect A A′)
  (define (pos/neg !kind !pats kind pats)
    (if (eq? !kind kind)
        ;; Same kind, so if we know all pats don't intersect, then we can use the positive pattern.
        ;; If we know they all must intersect, then we have a contradiction.
        ;; Otherwise, we have to fall back on dynamic testing.
        (match (for/fold
                   ([t #f])
                   ([!pat (in-list !pats)]
                    [pat (in-list pats)])
                 (match (evt-intersect !pat pat)
                   [#f t]
                   [(mres t′ _) (U∨ t t′)]))
          [(== must eq?) #f]
          [#f (mres must (constructed kind pats))]
          [_ (mres may (set A A′))])
        ;; Must be a kind′, which isn't a kind, so just use the positive pattern.
        (mres must (constructed kind pats))))
  ;; If A does not overlap with anything in As, then the intersection is dead.
  ;; Otherwise, we get back new, more specific patterns to combine.
  (define (set/1 As A)
    (cond
     [(= (set-count As) 1) (evt-intersect (set-first As) A)]
     [(set-member? As A) As]
     [else (let/ec break
             (for/fold ([As′ (mres must ∅)]) ([an-A (in-set As)])
               (define res (evt-intersect an-A A))
               (or (res-∧ As′ res) (break #f))))]))
  (match* (A A′)
    [(A A) (mres must A)] ;; Same, so we're done.
    [((== Any eq?) A′) (mres must A′)]
    [(A (== Any eq?)) (mres must A)]
    [((constructed kind pats) (constructed kind′ pats′))
     (and (eq? kind kind′)
          (let/ec break
            (define-values (pats-out t)
              (for/fold ([pats-out '()]
                         [t must])
                  ([pat (in-list pats)]
                   [pat′ (in-list pats′)])
                (match (evt-intersect pat pat′)
                  [#f (break #f)]
                  [(mres t′ As) (values (cons As pats-out) (∧ t t′))])))
            (mres t (constructed kind (reverse pats-out)))))]
    [((!constructed kind pats) (constructed kind′ pats′))
     (pos/neg kind pats kind′ pats′)]
    [((constructed kind pats) (!constructed kind′ pats′))
     (pos/neg kind′ pats′ kind pats)]
    [((? set? As) (? (compose not set?) A′)) (set/1 As A′)]
    [((? (compose not set?) A) (? set? As′)) (set/1 As′ A)]
    [((? set? As) (? set? As′))
     ;; Intersect the smaller set against the bigger set. Combine results.
     (define-values (A-small A-big)
       (if (<= (set-count As) (set-count As′))
           (values As As′)
           (values As′ As)))
     (let/ec break
       (for/fold ([As-new (mres must ∅)]) ([A (in-set A-small)])
         (or (res-∧ As-new (set/1 A-big A)) (break #f))))]
    ;; Bindings and two-sided negations must be dynamically checked.
    [((or (□ x) ($ x)) A′) (mres may (set A A′))]
    [(A (or (□ x) ($ x))) (mres may (set A A′))]
    [((? !constructed?) (? !constructed?)) (mres may (set A A′))]
    ;; Anything else is concrete, so do not intersect unless equal (already checked)
    [(_ _) #f]))

;; Could A and A′ possibly intersect? Let's ask!
(define (evt-overlap A A′)
  (not (not (evt-intersect A A′))))

(define (C∧ r s)
  (match (evt-intersect (C r) (C s))
    [#f #f]
    [(mres t As) As]))

;; Reduce C∧ over a set.
(define (C⋀ Ts)
  (cond [(set-empty? Ts) ∅]
        [else
         (let combo ([Ts Ts])
           (define T′ (set-first Ts))
           (define Ts′ (set-rest Ts))
           (cond [(set-empty? Ts′) (C T′)]
                 [else (C∧ (C T′) (combo Ts′))]))]))

(define-signature weak-eq^ (≃))
(define-signature TCon-deriv^ (matches ∂ run mkPMSM))

;; Single step for PMSM
(define (step M states input)
  (match-define (PMSM q₀ ≃ ary δ) M)
  (define (matches P A γ)
    (define (matches1 P) (matches P A γ))
    (define (matches2 P A) (matches P A γ))
    (match P
      [(? set?) (⨅ P matches1)]
      [(!constructed kind pats)
       (match (matches1 (constructed kind pats))
         [(mres (== must eq?) _) #f]
         [#f (mres must γ)]
         [(mres _ γ′) (mres may γ)])]
      [(constructed kind pats)
       (match A
         [(constructed (== kind eq?) data)
          (⨅/lst matches2 pats data)]
         [_ #f])]
      [(== Any eq?) (mres must γ)]
      [(□ x) (mres must (hash-set γ x A))]
      [($ x)
       (match (hash-ref γ x unmapped)
         [(== unmapped eq?) #f]
         [v (matches2 v A)])]
      [v (match (≃ v A)
           [#f #f]
           [t (mres t γ)])]))
  (for/fold ([S ∅]) ([state (in-set states)])
    (match state
      [(State q γ _)
       (define transitions (hash-ref δ q ∅))
       (for*/fold ([S S])
           ([(pat nexts) (in-hash transitions)]
            [res (in-value (matches pat input γ))]
            #:when res)
         (match res
           [(mres t γ′) (for/fold ([S S]) ([next (in-set nexts)])
                          (set-add S (State next γ′ t)))]))])))

;; What is the current state of the machine? Must or may?
(define (valuation states)
  (for/fold ([t #f]) ([state (in-set states)]) (∨ t (State-t state))))

(define (step* M states input-lst)
  (match input-lst
    ['() (and (valuation states) states)]
    [(cons input input-lst)
     (define states′ (step M states input))
     (and (valuation states′) (step* M states′ input-lst))]))

(define-unit TCon-deriv@
  (import weak-eq^)
   (export TCon-deriv^)
   (define-syntax-rule (weak-if t ρ)
     (let ([t′ t])
       (and t′ (mres t′ ρ))))

   (define (matches P A ρ)
     (define (matches1 P) (matches P A ρ))
     (match P
       [(? set?) (⨅ P matches1)] ;; Match all patterns in the set.
       [(!ev A′)
        (match (matches1 A′)
          [#f (mres must ρ)]
          [(mres (== must eq?) _) #f]
          [_ (mres may ρ)])]
       ;; Recursively match components
       [(call: nf pa)
        (match A
          [(call: fv av) (⊓ (matches nf fv ρ) (matches pa av ρ))]
          [_ #f])]
       [(ret: nf pv)
        (match A
          [(ret: fv vv) (⊓ (matches nf fv ρ) (matches pv vv ρ))]
          [_ #f])]
       [(== Any eq?) (mres must ρ)]
       [($ x) (match (hash-ref ρ x unmapped)
                [(== unmapped eq?) #f]
                [v (weak-if (≃ v A) ρ)])]
       [(□ x) (mres must (hash-set ρ x A))]
       [v (weak-if (≃ v A) ρ)]))

   (define (∂ A Tt)
     (match Tt
       [#f #f]
       [(== Σ* eq?) Σ*]
       [(tl T t)
        (let ∂* ([A A] [T T])
          (define (∂1 T) (∂* A T))
          (match T
            [(· T₀ T₁)
             (if (ν? T₀)
                 (match (∂1 T₀)
                   [#f (∂1 T₁)] ;; Might be able to pass T₀ from nullability
                   [(tl T₀′ t′)
                    (match (∂1 T₁)
                      [#f (tl (·simpl T₀′ T₁) t′)]
                      ;; Both derivatives matched.
                      [(tl T₁′ t″) (tl (∪ (set (·simpl T₀′ T₁) T₁′)) (∨ t′ t″))])]
                   [v (error '∂ "Oops0 ~a" v)])
                 (match (∂1 T₀)
                   [#f #f]
                   [(tl T′ t′) (tl (·simpl T′ T₁) t′)]
                   [v (error '∂ "Oops1 ~a" v)]))]

            ;; Negation differs because it waits until we have a /full/ match.
            ;; Thus, we do a nullability check to see if it is satisfied.
            ;; If a may state, we stay may.
            [(¬ T)
             (match (∂1 T)
               [#f Σ*]
               [(tl T′ (== must eq?))
                (and (not (ν? T′))
                     (tl (negate T′) must))]
               [(tl T′ t′) (tl (negate T′) t′)]
               [v (error '∂ "Oops2 ~a" v)])]

            [(cons (kl T′) ρ)
             (match (∂1 (cons T′ ρ))
               [#f #f]
               [(tl T″ t′) (tl (·simpl T″ T) t′)]
               [v (error '∂ "Oops3 ~a" v)])]

            ;; dseq
            [(cons (bind B T) ρ)
             (match (matches B A ρ)
               [#f #f]
               [(mres t′ ρ′) (tl (cons T ρ′) t′)]
               [v (error '∂ "Oops4 ~a" v)])]

            ;; Match some
            [(∪ Ts)
             (let/ec break
               (define-values (t′ Ts′)
                 (for/fold ([t must] [Ts′ ∅]) ([T (in-set Ts)])
                   (match (∂1 T)
                     [(== Σ* eq?) (break Σ*)]
                     [#f (values t Ts′)] ;; shortcut
                     [(tl T′ t′) (values (∨ t t′) (set-add Ts′ T′))]
                     [v (error '∂ "Oops5 ~a" v)])))
               (if (set-empty? Ts′)
                   #f
                   (tl (∪ Ts′) t′)))]

            ;; Match all
            [(∩ Ts)
             (let/ec break
               (define-values (t′ Ts′)
                 (for/fold ([t must] [Ts′ ∅]) ([T (in-set Ts)])
                   (match (∂1 T)
                     [#f (break #f)]
                     [(== Σ* eq?) (values t Ts′)] ;; shortcut
                     [(tl T′ t′) (values (∧ t t′) (set-add Ts′ T′))]
                     [v (error '∂ "Oops6 ~a" v)])))
               (tl (∩ Ts′) t′))]

            ;; Was done, now too many.
            [(== ε eq?) #f]

            ;; Event/unevent
            [(cons Aor!A ρ) (match (matches Aor!A A ρ)
                              [#f #f]
                              [(mres t ρ′) (tl ε t)])]

            [Aor!A
             (error '∂ "Missing ρ ~a" Aor!A)]))]))

   ;; Approximate derivative that defers binding to dynamics.
   (define (∂̂ A T)
     (define (∂̂1 T) (∂̂ A T))
     (cond
      [(eq? T Σ̂*) Σ̂*]
      [T
       (match T
         [(· T₀ T₁)
          (if (ν? T₀)
              (match (∂̂1 T₀)
                [#f (∂̂1 T₁)] ;; Might be able to pass T₀ from nullability
                [T₀′
                 (match (∂̂1 T₁)
                   [#f (·simpl T₀′ T₁)]
                   ;; Both derivatives matched.
                   [T₁′ (∪simpl (set (·simpl T₀′ T₁) T₁′))])])
              (match (∂̂1 T₀)
                [#f #f]
                [T′ (·simpl T′ T₁)]))]
         [(¬ T)
          (match (∂̂1 T)
            [#f Σ̂*]
            [T′ (and (not (ν? T′)) (negate T′))])]
         [(kl T′)
          (match (∂̂1 T′)
            [#f #f]
            [T″ (·simpl T″ T)])]
         ;; dseq
         [(bind B T)
          (and (evt-overlap B A) T)]
         ;; Match some
         [(∪ Ts)
          (let/ec break
            (define Ts′
              (for/fold ([Ts′ ∅]) ([T (in-set Ts)])
                (match (∂̂1 T)
                  [(== Σ̂* eq?) (break Σ̂*)]
                  [#f Ts′] ;; shortcut
                  [T′ (set-add Ts′ T′)])))
            (∪simpl Ts′))]
         ;; Match all
         [(∩ Ts)
          (let/ec break
            (define Ts′
              (for/fold ([Ts′ ∅]) ([T (in-set Ts)])
                (match (∂̂1 T)
                  [#f (break #f)]
                  [(== Σ̂* eq?) Ts′] ;; shortcut
                  [T′ (set-add Ts′ T′)])))
            (∩simpl Ts′))]
         ;; Was done, now too many.
         [(== ε eq?) #f]
         [(cons T ρ) (∂̂1 T)] ;; Kill bindings
         ;; Event/unevent
         [Aor!A (and (evt-overlap Aor!A A)
                     ε)])]
      [else #f]))

   (define (run* Tt π)
     (match π
       ['() Tt]
       [(cons A π)
        (match (∂ A Tt)
          [#f #f]
          [Tt′ (run* Tt′ π)])]))
   (define run run*)

   (define (goto q)
     (define (inner S Q δ)
       (define qc (∂̂ S q)) ;; qc is simplified on the fly like ≈ in Owens/Reppy/Turon
       (cond
        [qc
         (define δ′ (δ-extend δ q S qc))
         (cond
          [(set-member? Q qc) (values Q δ′)]
          [else
           (define Q′ (set-add Q qc))
           (explore Q′ δ′ qc)])]
        [else (values Q δ)]))
     inner)

   (define (explore Q δ q)
     (define f (goto q))
     (for/fold ([Q Q] [δ δ]) ([A (in-set (C q))])
       (f A Q δ)))

   (define (mkPMSM T)
     (define q₀
       (let remρ ([T T])
         (match T
           [(¬ T) (¬ (remρ T))]
           [(∪ Ts) (∪ (for/set ([T (in-set Ts)]) (remρ T)))]
           [(∩ Ts) (∩ (for/set ([T (in-set Ts)]) (remρ T)))]
           [(· T₀ T₁) (· (remρ T₀) (remρ T₁))]
           [(kl T) (kl (remρ T))]
           [(bind B T) (bind B (remρ T))]
           [(cons T ρ) (remρ T)]
           [T T])))
     (define-values (Q δ) (explore (set q₀) #hash() q₀))
     (PMSM (State q₀ #hasheq() must) ≃ #f δ))) ;; XXX ary unnecessary

(define-unit concrete@
  (import)
   (export weak-eq^)
   (define (≃ x y) (and (equal? x y) must)))

(define-values/invoke-unit/infer (export TCon-deriv^) (link concrete@ TCon-deriv@))

(printf "Big test~%")
(for*/list ([T (in-list (list Tcon0 Tcon1 Tcon2
                         ))]
            [TM (in-value (mkPMSM T))]
            [π (in-list (list π0 π1))])
  (cons (run (tl T must) π)
        (step* TM (set (PMSM-q₀ TM)) π)))


#|
The proper denotational semantics is Jay's with a more disciplined prefixes definition.
We need that traces with a discontinuity are excluded.
 {ABC} is a singleton set of one trace, with prefixes {ε, A, AB, ABC}
 Traces \ {ABC} is a cofinite set with prefixes ∪ {ε}, [¬A...], [A¬B...], [AB¬C...]
   it does not include a trace beginning with ABC!
 Thus, when calculating the prefixes of a set of traces Π,
  any π ∉ Π may not prefix a trace in Π (and thus not prefix a trace in prefixes(Π))
 prefixes(Π) = {π′ : π ∈ Π, π′ ⊑ π, ∀ π″ ∈ Traces \ Π. π″ ⋢ π′}
|#