#lang racket/base

(require redex/reduction-semantics
         racket/match)

(provide (all-defined-out))

(define-language FJ
  (P ::= (L P)
         ())
  (L ::= (class C extends D [FtS K MS]))
  (L? ::= L
          ⊤)
  (FtS ::= (C f ≀ FtS)
          ())
  (FS ::= (f FS)
          ())
  (K ::= (C FtS [(super FS) Is]))
  (Is ::= (this -.> f = f ≀ Is)
          ())
  (MS ::= (M MS)
          ())
  (M ::= (C m As [return e]))
  (As ::= (C x · As)
          ())
  (e ::= x
         (e -.> f)
         (e -@> m es)
         (new C es)
         ({C} e))
  (C D ::= variable-not-otherwise-mentioned
           Object)
  (f ::= variable-not-otherwise-mentioned)
  (m ::= variable-not-otherwise-mentioned)
  (x ::= variable-not-otherwise-mentioned
         this)
  )

(define-judgment-form FJ
  #:mode (well-formed I I)
  [--------------------
   (well-formed P ())
   ]

  [(where #f (definition-of P_0 C))
   (where L? (definition-of P_0 D))
   (well-formed ((class C extends D [FtS K MS]) P_0) P_1)
   ---------------------------------------------------------------------
   (well-formed P_0 ((class C extends D [FtS K MS]) P_1))
   ]
  )

(define-metafunction FJ
  definition-of : P D -> L? or #f
  [(definition-of P Object) ⊤]
  [(definition-of () D) #f]
  [(definition-of ((class C extends D [FtS K MS]) P) C)
   (class C extends D [FtS K MS])]
  [(definition-of (L P) C)
   (definition-of P C)]
  )
