#lang racket
(require racket/unit)
(require racket/trace)

(define ∅ (set))
(struct -unmapped ()) (define unmapped (-unmapped))

;; Temporal contracts
(struct ¬ (T) #:transparent)
(struct · (T₀ T₁) #:transparent)
(struct kl (T) #:transparent)
(struct bind (B T) #:transparent)
(struct ∪ (Ts) #:transparent)
(struct ∩ (Ts) #:transparent)
(struct -ε () #:transparent) (define ε (-ε))
(define T⊥ (∪ ∅)) ;; empty contract
(define Σ̂* (∩ ∅))
(define (∂? x)
  (or (¬? x) (·? x) (event? x) (kl? x) (bind? x) (∪? x) (∩? x)))
(define (ð? x)
  (match x
    [(or (cons (? ∂?) (? hash?))
         (¬ (? ð?))
         (· (? ð?) (? ð?))
         (kl (? ð?))
         (== ε eq?))
     #t]
    [(or (∪ Ts) (∩ Ts)) (for/and ([T (in-set Ts)]) (ð? T))]
    [_ #f]))

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
(struct -Any () #:transparent) (define Any (-Any))
(struct $ (x) #:transparent)
(struct □ (x) #:transparent)

;; Niceties for writing temporal contracts using the general language of patterns.
(define (call nf pa) (constructed 'call (list nf pa)))
(define (ret nf pv) (constructed 'call (list nf pv)))
(define (!call nf pa) (!constructed 'call (list nf pa)))
(define (!ret nf pv) (!constructed 'ret (list nf pv)))
(define-match-expander call: (λ (stx) (syntax-case stx ()
                                       [(_ nf pa) #'(constructed 'call (list nf pa))])))
(define-match-expander ret: (λ (stx) (syntax-case stx ()
                                       [(_ nf pv) #'(constructed 'ret (list nf pv))])))
(define/match (event? x)
  [((constructed (or 'call 'ret) (list _ _))) #t]
  [(_) #f])

;; 3-valued logic
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

;; Top level
(struct tl (T t) #:transparent)
(define M⊥ #f) ;; #f is the empty machine
(define Σ* (tl Σ̂* must))

(define/match (·simpl T₀ T₁)
  [((== ε eq?) T₁) T₁]
  [(T₀ (== ε eq?)) T₀]
  [((== T⊥ eq?) _) T⊥]
  [(_ (== T⊥ eq?)) T⊥]
  ;; Right-associate
  [((· T₀₀ T₀₁) T₁) (·simpl T₀₀ (·simpl T₀₁ T₁))]
  ;; No simplifications
  [(T₀ T₁) (· T₀ T₁)])

;; Flatten ∪s and ∪s into one big ∪ or ∩.
(define (flat-collect pred extract Ts)
  (let recur ([Ts Ts] [a ∅])
    (for/fold ([a a]) ([T (in-set Ts)])
      (if (pred T)
          (recur (extract T) a)
          (set-add a T)))))
;(trace flat-collect);
(define (∪simpl Ts)
  (define Ts′ (flat-collect ∪? ∪-Ts Ts))
  (cond [(set-empty? Ts′) T⊥]
        [(= (set-count Ts′) 1) (set-first Ts′)]
        [else (∪ Ts′)]))

(define (∩simpl Ts)
  (define Ts′ (flat-collect ∩? ∩-Ts Ts))
  (cond [(set-empty? Ts′) Σ̂*]
        [(= (set-count Ts′) 1) (set-first Ts′)]
        [else (∩ Ts′)]))

;; Combine bindings giving preference to the right hash.
(define (◃ ρ₀ ρ₁)
  (for/fold ([ρ ρ₀]) ([(k v) (in-hash ρ₁)])
    (hash-set ρ k v)))

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
    [(¬ T) #t #;(not (ν? T))
     ] ;; FIXME: tests pass if this is #f. What's up with negation?
    [(cons T ρ) (ν? T)]
    [_ #f])) ;; bind, event, nonevent

(define/match (negate T)
  [((¬ T)) T]
  [(T) (¬ T)])

(define/match (flip B)
  [((call: nf xa)) (!call nf Any)]
  [((ret: nf xv)) (!ret nf Any)])

(define/match (C T)
  [((== ε eq?)) (set Any)]
  [((or (== Any eq?) #f)) (set Any)]
  [((or (constructed kind pats) (!constructed kind pats)))
   (set (constructed kind pats) (!constructed kind pats))]
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
                 ;; !pat?
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

(define (C∧ Sr Ss)
  (match (evt-intersect Sr Ss)
    [#f ∅]
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
(define-signature TCon-deriv^ (run mkPMSM))

(define (matches≃ ≃)
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
  matches)

;; Single step for PMSM
(define (step M states input)
  (match-define (PMSM q₀ ≃ ary δ) M)
  (define matches (matches≃ ≃))
  (for/fold ([S ∅]) ([state (in-set states)])
    (match state
      [(State q γ _)
       (define transitions (hash-ref δ q #hash()))
       (for*/fold ([S S])
           ([(pat nexts) (in-hash transitions)]
            [res (in-value (matches pat input γ))]
            #:when res)
         (match res
           [(mres t γ′) (for/fold ([S S]) ([next (in-set nexts)])
                          (set-add S (State next γ′ t)))]))]
      [_ (error 'step "oops2 ~a" state)])))

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
   (define matches (matches≃ ≃))

   ;; Negation differs because it waits until we have a /full/ match.
   ;; Thus, we do a nullability check to see if it is satisfied.
   ;; If a may state, we stay may only if the contract is nullable.
   ;; FIXME: Need a may fail (#f)
   (define (¬p rec form T)
     (match (rec T)
       [(== M⊥ eq?) Σ*]
       [(tl T′ (== must eq?))
        (if (ν? T′)
            M⊥
            (form (negate T′) must))]
       [(tl T′ t′) (form (negate T′) (if (ν? T′) may must))]
       [M (error '¬p "oops3 ~a" M)]))

   (define (·p rec form T₀ T₁)
     (if (ν? T₀)
         (match (rec T₀)
           [(== M⊥ eq?) (rec T₁)] ;; Might be able to pass T₀ from nullability
           [(tl T₀′ t′)
            (match (rec T₁)
              [(== M⊥ eq?) (form (·simpl T₀′ T₁) t′)]
              ;; Both derivatives matched.
              [(tl T₁′ t″) (form (∪simpl (set (·simpl T₀′ T₁) T₁′)) (∨ t′ t″))]
              [M (error '·p "oops4 ~a" M)])]
           [M (error '·p "oops5 ~a" M)])
         (match (rec T₀)
           [(== M⊥ eq?) M⊥]
           [(tl T′ t′) (form (·simpl T′ T₁) t′)]
           [M (error '·p "oops6 ~a" M)])))

   (define (klp rec form T′ T)
     (match (rec T′)
       [(== M⊥ eq?) M⊥]
       [(tl T″ t′) (form (·simpl T″ T) t′)]
       [M (error 'klp "oops7 ~a" M)]))

   ;; Match some
   (define (∪p rec form Ts)
     (let/ec break
       (define-values (t′ Ts′)
         (for/fold ([t must] [Ts′ ∅]) ([T (in-set Ts)])
           (match (rec T)
             [(== Σ* eq?) (break Σ*)]
             [(== M⊥ eq?) (values t Ts′)] ;; shortcut
             [(tl T′ t′) (values (∨ t t′) (set-add Ts′ T′))]
             [M (error '∪p "oops8 ~a" M)])))
       (if (set-empty? Ts′)
           M⊥
           (form (∪simpl Ts′) t′))))

   ;; Match all
   (define (∩p rec form Ts)
     (let/ec break
       (define-values (t′ Ts′)
         (for/fold ([t must] [Ts′ ∅]) ([T (in-set Ts)])
           (match (rec T)
             [(== M⊥ eq?) (break M⊥)]
             [(== Σ* eq?) (values t Ts′)] ;; shortcut
             [(tl T′ t′) (values (∧ t t′) (set-add Ts′ T′))]
             [M (error '∩p "oops9 ~a" M)])))
       (if (set-empty? Ts′)
           Σ*
           (form (∩ Ts′) t′))))
   
   ;; Top level temporal contracts with distributed ρs.
   (define (ð A T)
     (define (ð1 T) (ð A T))
     (match T
       [(== Σ̂* eq?) (tl T must)]
       [(or (== T⊥ eq?) (== ε eq?)) M⊥]
       [(cons T ρ) (∂ A T ρ)]
       [(· T₀ T₁) (·p ð1 tl T₀ T₁)]
       [(¬ T) (¬p ð1 tl T)]
       [(kl T′) (klp ð1 tl T′ T)]
       [(∪ Ts) (∪p ð1 tl Ts)]
       [(∩ Ts) (∩p ð1 tl Ts)]
       [T (error 'ð "Bad top-level Tcon ~a" T)]))

   (define (∂ A T ρ)
     (define (∂1 T) (∂ A T ρ))
     (define (tlρ T t) (tl (cons T ρ) t))
     (match T
       [(== Σ̂* eq?) (tl T must)]
       [(or (== T⊥ eq?) (== ε eq?)) M⊥]
       [(· T₀ T₁) (·p ∂1 tlρ T₀ T₁)]
       [(¬ T) (¬p ∂1 tlρ T)]
       [(kl T′) (klp ∂1 tlρ T′ T)]
       [(∪ Ts) (∪p ∂1 tlρ Ts)]
       [(∩ Ts) (∩p ∂1 tlρ Ts)]
       ;; dseq
       [(bind B T)
        (match (matches B A ρ)
          [(== M⊥ eq?) M⊥]
          [(mres t′ ρ′) (tl (cons T ρ′) t′)]
          [M (error '∂ "oops10 ~a" M)])]
       ;; Event/unevent
       [Aor!A (match (matches Aor!A A ρ)
                [(== M⊥ eq?) M⊥]
                [(mres t ρ′) (tl ε t)]
                [M (error '∂ "oops11 ~a" M)])]))

#|
F⟦¬ T⟧_ρ = P⟦¬ T⟧_ρ = ¬p(F⟦T⟧_ρ)
We exclude ε from bad prefixes since it's in every prefix.
¬p(Π) = {π ∉ Π\{ε} : (∃ π′ ∈ Π. π < π′) ∨ (∀ π′ ∈ Π\{ε}. π′ ≮ π}

Lemma: ν?(T,ρ) ⇔ ε ∈ F⟦T⟧_ρ
Induction on T:
ε: Trivial
kl T′: Trivial
¬ T: Trivial
bind, event, nonevent: Trivial
T₀ · T₁:
  IH₀ ν?(T₀,ρ) ⇔ ε ∈ F⟦T₀⟧_ρ
  IH₁ ν?(T₁,ρ) ⇔ ε ∈ F⟦T₁⟧_ρ
  (⇒): Both hold, so ε in both by IH, so in ∩ by def.
  (⇐): ε in both by def ∩, so both nullable by IH and thus nullable by def ν?
∪ Ts:
  IH ∀ T ∈ Ts. ν?(T,ρ) ⇔ ε ∈ F⟦T⟧_ρ
  (⇒): Some T is nullable, so ε ∈ that T's denotation by IH. Thus in union.
  (⇐): ε in union, so some denotation has it. Thus that sub-contract is nullable.
∩ Ts: Similar
Qed.

Def: ∂_ε T = T
     ∂_Aπ T = ∂_π (∂_A T)

Lemma: F⟦T⟧_ρ ⊆ P⟦T⟧_ρ
Proof: Induction on T.

Lemma:
 (1) ν?(∂_A T,ρ) ⇒ A ∈ F⟦T⟧_ρ
 (2) ∂_A T,ρ ≠ ∅ ∧ ¬ν?(∂_A T,ρ) ⇒ ∃ π ∈ F⟦T⟧. A < π
Proof: Induction on T
Base T ≡ pat:
 Case matches(pat, A, ρ) = #f:
  Vacuous
 Case matches(pat, A, ρ) ≡ ρ′:
  (1) True by definition of F⟦_⟧_ and ∂.
  (2) Vacuous.
Base T ≡ ε: Vacously true since ∂_A ε,ρ = ∅ and ¬ν?(∅)
Ind T ≡ (· T₀ T₁):
 ∂_A T,ρ = ∪ {∂_A T₀,ρ, ν?(T₀)·∂_A T₁,ρ}
 Thus if ν?(∂_A T₀,ρ) or ν?(T₀) and ν?(∂_A T₁,ρ) then (1) by IH and def. F⟦_⟧.
 (2) ¬ν?(∂_A T,ρ) thus ¬ν? (T₀) ∨ ¬ν(T₁)
    By cases on this ∨:
    Case ¬ν?(T₀):
     In this case, ∂_A T,ρ = ∂_A T₀,ρ.
     Since ∂_A (T,ρ) ≠ ∅, ∂_A (T₀,ρ) ≠ ∅
     Suppose ¬ν?(∂_A T₀,ρ)
      then by IH, ∃ π ∈ F⟦T₀⟧. A < π.
Ind T ≡ ¬ T′:
 ∂_A ¬ T′,ρ = ν?(∂_A T′,ρ) → ∅, ¬ ∂_A T′,ρ
 Since ν?(∂_A T,ρ), ¬ν?(∂_A T′,ρ) and ν?(¬ ∂_A T′,ρ)
 ???
Ind T ≡ T′*:
Ind T ≡ (∪ Ts):
Ind T ≡ (∩ Ts):
Ind T ≡ 〈pat〉T′:

Nullability doesn't matter unless T is a negation.
Lemma:
∂_A T,ρ = T′,ρ′ ⇒ A·P⟦T′⟧_ρ′ ⊆ P⟦T⟧_ρ
∂_A T,ρ = ∅ ⇒ P⟦T⟧_ρ ∩ {Aπ : π ∈ Traces} = ∅

Theorem:
∀ π,T,ρ.
  ν?(∂_π T,ρ) ⇔ π ∈ F⟦T⟧_ρ ∧
  ∂_π T, ρ ≠ ∅ ⇔ π ∈ P⟦T⟧_ρ

Proof:
Induction on π
Base ε: ν?(T,ρ) ⇔ ε ∈ F⟦T⟧_ρ
 Above lemma:
Ind T ≡ (· T₀ T₁)
 Case (ν? T₀):
  Case (∂_A T₁) = #f:
   
  Case (∂_A T₁) ≡ T₀′:
 Case ¬(ν? T₀):
ν?(∂_π′ T, ρ) ⇔ π′ ∈ F⟦T⟧_ρ
|#

   ;; Approximate derivative that defers binding to dynamics.
   (define (∂̂ A T)
     (define (∂̂1 T) (∂̂ A T))
     (match T
       [(or (== Σ̂* eq?) (== T⊥ eq?)) T]
       [(· T₀ T₁)
        (if (ν? T₀)
            (match (∂̂1 T₀)
              [(== T⊥ eq?) (∂̂1 T₁)] ;; Might be able to pass T₀ from nullability
              [T₀′
               (match (∂̂1 T₁)
                 [(== T⊥ eq?) (·simpl T₀′ T₁)]
                 ;; Both derivatives matched.
                 [T₁′ (∪simpl (set (·simpl T₀′ T₁) T₁′))])])
            (·simpl (∂̂1 T₀) T₁))]
         
       [(¬ T)
        (match (∂̂1 T)
          [(== T⊥ eq?) Σ̂*]
          [T′ (if (ν? T′)
                  T⊥
                  (negate T′))])]
         
       [(kl T′)
        (match (∂̂1 T′)
          [(== T⊥ eq?) T⊥]
          [T″ (·simpl T″ T)])]
         
       ;; dseq
       [(bind B T)
        (if (evt-overlap B A)
            T
            T⊥)]
         
       ;; Match some
       [(∪ Ts)
        (let/ec break
          (define Ts′
            (for/fold ([Ts′ ∅]) ([T (in-set Ts)])
              (match (∂̂1 T)
                [(== Σ̂* eq?) (break Σ̂*)]
                [(== T⊥ eq?) Ts′] ;; shortcut
                [T′ (set-add Ts′ T′)])))
          (∪simpl Ts′))]

       ;; Match all
       [(∩ Ts)
        (let/ec break
          (define Ts′
            (for/fold ([Ts′ ∅]) ([T (in-set Ts)])
              (match (∂̂1 T)
                [(== T⊥ eq?) (break T⊥)]
                [(== Σ̂* eq?) Ts′] ;; shortcut
                [T′ (set-add Ts′ T′)])))
          (∩simpl Ts′))]

       ;; Was done, now too many.
       [(== ε eq?) T⊥]

       ;; Event/unevent
       [Aor!A (if (evt-overlap Aor!A A)
                  ε
                  T⊥)]))

   (define (run* Tt π)
     (match π
       ['() Tt]
       [(cons A π) 
        (match Tt
          [(tl T t) (run* (ð A T) π)]
          [(== M⊥ eq?) M⊥]
          [M (error 'run* "oops12 ~a" M)])]))
   (define run run*)

   (define (goto q)
     (define (inner S Q δ)
       (define qc (∂̂ S q)) ;; qc is simplified on the fly like ≈ in Owens/Reppy/Turon
       (cond
        ;; No match ⇒ no transition
        [(eq? qc T⊥) (values Q δ)]
        [else
         (define δ′ (δ-extend δ q S qc))
         (cond
          [(set-member? Q qc) (values Q δ′)]
          [else
           (define Q′ (set-add Q qc))
           (explore Q′ δ′ qc)])]))
     inner)

   (define (explore Q δ q)
     (define f (goto q))
     (for/fold ([Q Q] [δ δ]) ([A (in-set (C q))])
       (f A Q δ)))
;;   (trace explore goto)

   (define (mkPMSM T)
     (define q₀ T)
     (define-values (Q δ) (explore (set q₀) #hash() q₀))
     (PMSM (State q₀ #hasheq() must) ≃ #f δ))) ;; XXX ary unnecessary

(define-unit concrete@
  (import)
   (export weak-eq^)
   (define (≃ x y) (and (equal? x y) must)))

(define-values/invoke-unit/infer (export TCon-deriv^) (link concrete@ TCon-deriv@))

(module+ test
  (require rackunit)

  (define Tcon0 (¬ (call Any Any)))
  (define Tcon1 (¬ (· (call Any Any) (kl Any))))
  (define Tcon2 (¬ (call Any 0)))
  (define Tcon3 (· (kl (!call values Any))
                   (· (call values Any) (call values 0))))
  (define Tcon4 (¬ (¬ Tcon3)))
  (define π0 (list (call values 0)))
  (define π1 (list (call values 1)))
  (define π2 (list (call add1 0) (call values 1)))
  (define π3 (append π2 (list (call values 0))))
  (define π4 (append π2 (list (call values 1))))
  ;; Expect all the following combinations to be satisfied. Not otherwise
  (define expectations (set '(2 . 1) '(3 . 0) '(3 . 1) '(3 . 2) '(3 . 3)))

  (define ρ₀ #hasheq())
  (for ([T (in-list (list Tcon0 Tcon1 Tcon2 Tcon3 Tcon4))]
        [Ti (in-naturals)])
    (define TM (mkPMSM T))
    (for ([π (in-list (list π0 π1 π2 π3 π4))]
          [πi (in-naturals)])
      (test-case
       (format "T~a, π~a" Ti πi)
       (check (λ (Tt M)
                 (if (set-member? expectations (cons Ti πi))
                     (and Tt M)
                     (not (or Tt M))))
              (run (tl (cons T ρ₀) must) π)
              (step* TM (set (PMSM-q₀ TM)) π))))))

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