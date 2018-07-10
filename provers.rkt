#lang racket
(require "mk.rkt")
#|
Ben Boskin

Proof Generators for A Few Syllogistic Logical Systems:


ALL Logic -- "all cats are animals", etc.
ARC Logic -- ALL logic, with the addition of relative clauses -- "all cats (see all humans)", etc.
ARCp Logic -- ARC logic with a different set of rules
S Logic -- ALL logic with the notions SOME and NO added -- "no cats are dogs"

|#


;Some useful miniKanren relations

(define (membero x ls)
  (fresh (a d)
         (== `(,a . ,d) ls)
         (conde
          [(== a x)]
          [(membero x d)])))

(define (assvo x ls o)
  (fresh (a d y v)
         (== `(,a . ,d) ls)
         (== `(,y . ,v) a)
         (conde
          [(== y x) (== o v)]
          [(=/= y x) (assvo x d o)])))

(define (cdro ls o)
  (fresh (a d)
         (== `(,a . ,d) ls)
         (== d o)))

(define (caro ls o)
  (fresh (a d)
         (== `(,a . ,d) ls)
         (== a o)))


;Function to turn premise sentences into justified lines


(define (premises->proof^ ls i)
  (cond
   [(eqv? ls '()) '()]
   [else (cons `(,(car ls) . ((PREMISE) . ,i)) (premises->proof^ (cdr ls) (sub1 i)))]))

#|
Proof Generator for proof system of A (All Logic)
|#

(define (ALL G phi i o)
  (conde
   ; phi has been proved
   [(fresh (rule)
           (assvo phi G rule) 
           (== G o))]
   ; Axiom Rule
   [(fresh (p G^)
           (== `(((all ,p are ,p) . ((AXIOM) . ,i)) . ,G) G^)
           (ALL G^ phi (add1 i) o))]
   ; Barbara Rule
   [(fresh (p q r G^ rule1 rule2 line1 line2)
           (assvo `(all ,p are ,q) G rule1)
           (assvo `(all ,q are ,r) G rule2)
           (cdro rule1 line1)
           (cdro rule2 line2)
           (== `(((all ,p are ,r) . ((BARBARA ,line1 ,line2) . ,i)) . ,G) G^)
           (ALL G^ phi (add1 i) o))]))


; main program for user to use. 
(define (!-A G phi)
  (let ([n (length G)])
    (run 1 (P) (ALL (premises->proof^ G n) phi (add1 n) P))))

; Example uses: 
; (!-A '((all x are y) (all y are p) (all p are g)) '(all x are g))
; (!-A '((all x are y) (all y are p) (all p are g)) '(all r are r))

#|
Proof Generator for proof system of A(RC) 
(All Logic with 2-Place Relations, Constants, and DOWN rule)
|#

(define (ARC G phi i o)
  (conde
   ; phi has been proved
   [(fresh (rule)
           (assvo phi G rule)
           (== G o))]
   ; Axiom Rule
   [(fresh (p G^)
           (membero p phi)
           (== `(((all ,p ,p) . ((AXIOM) . ,i)) . ,G) G^)
           (ARC G^ phi (add1 i) o))]
   ; Barbara Rule
   [(fresh (p q r G^ rule1 rule2 line1 line2)
           (assvo `(all ,p ,q) G rule1)
           (assvo `(all ,q ,r) G rule2)
           (cdro rule1 line1)
           (cdro rule2 line2)
           (== `(((all ,p ,r) . ((BARBARA ,line1 ,line2) . ,i)) . ,G) G^)
           (ARC G^ phi (add1 i) o))]
   ; Down Rule
   [(fresh (a b c r G^ rule1 rule2 line1 line2)
           (assvo `(all ,a (,r all ,c)) G rule1)
           (assvo `(all ,b ,c) G rule2)
           (cdro rule1 line1)
           (cdro rule2 line2)
           (== `(((all ,a (,r all ,b)) . ((DOWN ,line1 ,line2) . ,i)) . ,G) G^)
           (ARC G^ phi (add1 i) o))]))

; main program for user to use. 
(define (!-ARC G phi)
  (let ([n (length G)])
    (run 1 (P) (ARC (premises->proof^ G n) phi (add1 n) P))))

; Example use: 
; (!-ARC '((all q x) (all r q) (all x y) (all z (s all y))) '(all z (s all r)))

#|
Proof Generator for proof system of A(RC)'
(All Logic with 2-Place Relations, Constants, and ANTI rule)
|#

(define (ARCp G phi i o)
  (conde
   ; phi has been proved
   [(fresh (rule)
           (assvo phi G rule)
           (== G o))]
   ; Axiom Rule
   [(fresh (p G^)
           (membero p phi)
           (== `(((all ,p ,p) . ((AXIOM) . ,i)) . ,G) G^)
           (ARCp G^ phi (add1 i) o))]
   ; Barbara Rule
   [(fresh (p q r G^ rule1 rule2 line1 line2)
           (assvo `(all ,p ,q) G rule1)
           (assvo `(all ,q ,r) G rule2)
           (cdro rule1 line1)
           (cdro rule2 line2)
           (== `(((all ,p ,r) . ((BARBARA ,line1 ,line2) . ,i)) . ,G) G^)
           (ARCp G^ phi (add1 i) o))]
   ; Anti Rule
   [(fresh (a b c r G^ rule1 line1)
           (assvo `(all ,a ,b) G rule1)
           (cdro rule1 line1)
           (== `(((all (,r all ,b) (,r all ,a)) . ((ANTI . ,line1) . ,i)) . ,G) G^)
           (ARCp G^ phi (add1 i) o))]))

; main program for user to use. 
(define (!-ARCP G phi)
  (let ([n (length G)])
    (run 3 (P) (ARCp (premises->proof^ G n) phi (add1 n) P))))


; Example use: 
; (!-ARCP '((all x y) (all y (r all z))) '(all (s all (r all z)) (s all x)))
; (!-ARCP '((all q x) (all r q) (all x y) (all z (s all y))) '(all z (s all r)))
; (this second one takes a little while, but it will find the proof!)

#|
Proof Generator for proof system of S
(All-Logic with Some and No added)
|#

(define (S G phi i o)
  (conde
   ; phi has been proved
   [(fresh (rule)
           (assvo phi G rule)
           (== G o))]
   ; Axiom Rule
   [(fresh (p G^)
           (membero p phi)
           (== `(((all ,p are ,p) . ((AXIOM) . ,i)) . ,G) G^)
           (S G^ phi (add1 i) o))]
   ; Barbara Rule
   [(fresh (p q r G^ rule1 rule2 line1 line2)
           (assvo `(all ,p are ,q) G rule1)
           (assvo `(all ,q are ,r) G rule2)
           (cdro rule1 line1)
           (cdro rule2 line2)
           (== `(((all ,p are ,r) . ((BARBARA ,line1 ,line2) . ,i)) . ,G) G^)
           (S G^ phi (add1 i) o))]
   ; Some1 Rule
   [(fresh (p q rule1 line1 G^)
           (assvo `(some ,p are ,q) G rule1)
           (cdro rule1 line1)
           (== `(((some ,q are ,p) . ((SOME1 ,line1) . ,i)) . ,G) G^)
           (S G^ phi (add1 i) o))]
   ; Some2 Rule
   [(fresh (p q rule1 line1 G^)
           (assvo `(some ,p are ,q) G rule1)
           (cdro rule1 line1)
           (== `(((some ,p are ,p) . ((SOME2 ,line1) . ,i)) . ,G) G^)
           (S G^ phi (add1 i) o))]
   ; DarII Rule
   [(fresh (p q n rule1 rule2 line1 line2 G^)
           (assvo `(all ,q are ,n) G rule1)
           (assvo `(some ,p are ,q) G rule2)
           (cdro rule1 line1)
           (cdro rule2 line2)
           (== `(((some ,p are ,n) . ((DARII ,line1 ,line2) . ,i)) . ,G) G^)
           (S G^ phi (add1 i) o))]
   ; Camestres Rule
   [(fresh (p q r rule1 rule2 line1 line2 G^)
           (assvo `(all ,p are ,q) G rule1)
           (assvo `(no ,r are ,q) G rule2)
           (cdro rule1 line1)
           (cdro rule2 line2)
           (== `(((no ,r are ,p) . ((CAMESTRES ,line1 ,line2) . ,i)) . ,G) G^)
           (S G^ phi (add1 i) o))]
   ; No1 Rule
   [(fresh (p q rule1 line1 G^)
           (assvo `(no ,p are ,q) G rule1)
           (cdro rule1 line1)
           (== `(((no ,q are ,p) . ((NO1 ,line1) . ,i)) . ,G) G^)
           (S G^ phi (add1 i) o))]
   ; No2 Rule
   [(fresh (p q rule1 line1 G^)
           (symbolo q)
           (assvo `(no ,p are ,p) G rule1)
           (cdro rule1 line1)
           (== `(((no ,p are ,q) . ((NO2 ,line1) . ,i)) . ,G) G^)
           (S G^ phi (add1 i) o))]
   ; No3 Rule
   [(fresh (p q rule1 line1 G^)
           (symbolo q)
           (assvo `(no ,p are ,p) G rule1)
           (cdro rule1 line1)
           (== `(((all ,p are ,q) . ((NO3 ,line1) . ,i)) . ,G) G^)
           (S G^ phi (add1 i) o))]
   ; X Rule
   [(fresh (p q psi rule1 line1 rule2 line2 G^)
           (assvo `(some ,p are ,q) G rule1)
           (assvo `(no ,p are ,q) G rule2)
           (cdro rule1 line1)
           (cdro rule2 line2)
           (== `((,psi . ((X ,line1 ,line2) . ,i)) . ,G) G^)
           (S G^ phi (add1 i) o))]))

; main program for user to use.
(define (!-S G phi)
  (let ([n (length G)])
    (run 1 (P) (S (premises->proof^ G n) phi (add1 n) P))))

; Example uses:
;(!-S '((some p are q) (all q are r) (no r are s) (some s are h) (all h are p)) '(some p are s))
;(!-S '((no p are q) (all g are p) (all s are q)) '(no g are s))
