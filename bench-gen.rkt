#lang racket
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Generate numbers tabular (Program, LOC, Time (ms), Space (mb), Speed (states/sec)
(require "proctime.rkt" racket/trace)

(define sort1 "../benchmarks/temp-c/sort.sch")
(define sort2 "../benchmarks/temp-c/sort-pushdown.sch")
(define sort3 "../benchmarks/temp-c/sort-lists.sch")
(define file "../benchmarks/temp-c/file.sch")
(define malloc "../benchmarks/temp-c/malloc.sch")
(define to-test
  (list file malloc sort1 sort2 sort3))

;; Algorithm tags used to drive [run-benchmark.rkt]
(define baseline "ps")
(define μ "psu")
(define Ξ "psp")
(define Γ "lcg")
(define Γτ "lcgt")
(define μΓτ "lcgut")
(define μΓτΞ "lcgutp")

(define which-analyses
  (list baseline μ Ξ Γ Γτ μΓτ μΓτΞ))

(define (file->name s)
  (define path (string->path s))
  (define-values (base filename dir?) (split-path path))
  (path->string (path-replace-suffix filename "")))
(define (loc f)
  (with-input-from-file f
    (λ ()
       (for/sum ([l (in-port read-line)]) 1))))
(define (entry name fn conv n)
  (match (fn n)
    [#f (cond [(vector-ref (numbers-timeout? n) 0)
               "\\text{{\\small $t$}}"]
              [(vector-ref (numbers-exhaust? n) 0)
               "\\text{{\\small $m$}}"]
              [else (error 'bench-overview "No numbers, timeout or oom!: ~a" name)])]
    [n (conv n)]))

(define (byte->mib b) (/ b (* 1024 1024)))
(define (nfigs n)
  (compose number->string
           (cond [(zero? n) (compose inexact->exact round)]
                 [else 
                  (define factor (expt 10 n))
                  (λ (x)
                     (if (integer? x)
                         x
                         (exact->inexact (/ (round (* factor x)) factor))))])))

(define ((suffixed-number figs) n)
  (define num-zeros (truncate (/ (log n) (log 10))))
  (define (order k suff)
    (and (>= num-zeros k)
         (format "~a~a" ((nfigs figs) (/ n (expt 10 k))) suff)))
  (or (order 9 "G")
      (order 6 "M")
      (order 3 "K")
      ((nfigs figs) n)))

(define comparisons (list ;;numbers-run numbers-peak-mem numbers-state-rate
                          (λ (n)
                             (cond
                              [(or (vector-ref (numbers-timeout? n) 0)
                                   (vector-ref (numbers-exhaust? n) 0))
                               #f]
                              [else
                               (define sites (numbers-blame-sites n))
                               (define blames (numbers-blames n))
                               (define run-time (average (numbers-run n)))
                               (match (average sites)
                                 [#f #f]
                                 [0 (list run-time 0 #f)]
                                 [nsites (list run-time (average blames) nsites)])]))))
(define conversions (list #;(compose (suffixed-number 1)  (λ (x) (/ x 1000)))
                          #;(compose (nfigs 0) byte->mib)
                          #;(suffixed-number 0)
                     (match-lambda [(list rt bl bl-sites) (format "~a / ~a"
                                                          ((suffixed-number 1) (/ rt 1000))
                                                          (if bl-sites
                                                              (format "$\\frac{~a}{~a}$" bl (round bl-sites))
                                                              "0"))])))

(define-syntax-rule (for/append guards body ...)
  (for/fold ([acc '()]) guards (let ([r (let () body ...)]) (append acc r))))

(with-output-to-file "bench-overview.tex" #:mode 'text #:exists 'replace
  (λ ()
     (printf "\\begin{tabular}{@{}l||c|c|c|c|c|c|c@{}}~%")
     (printf "Program~% & \\- & $\\mu$ & $\\Xi$ & $\\Gamma$ & $\\Gamma_\\tau$ & $\\mu\\Gamma_\\tau$ & $\\mu\\Gamma_\\tau\\Xi$")
#|
     (printf "& Time {\\small (sec)}~%")
     (printf "& Space {\\small (MB)}~%")
     (printf "& Speed {\\small $\\frac{state}{sec}$}~%")
     (printf "& Imprecision {\\small (\\% spurious)}~%")
|#
     (printf "\\\\~%")
     (printf "\\hline\\hline~%")
     (printf
      (string-join
       (for/list ([file to-test])
         (define name (file->name file))
         (define numbers (hash-ref timings name))
         (format "~a & ~a"
                 (match name
                   ["sort" "sort1"]
                   ["sort-pushdown" "sort2"]
                   ["sort-lists" "sort3"]
                   [s s])
                 (string-join
                   (for/append ([fn comparisons]
                                [conversion conversions])
                     (for/list ([algo which-analyses])
                       (with-handlers ([exn:fail?
                                        (λ (e) (error 'bad-numbers "~a, ~a" file algo))])
                        (entry `(,name ,algo) fn conversion (hash-ref numbers algo)))))
                   " & ")))
       " \\\\~%"))
     (printf "~%\\end{tabular}~%")))