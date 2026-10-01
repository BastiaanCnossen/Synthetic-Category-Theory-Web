# Expressions with terminal categories and products

The expression syntax now permits changing category expressions. Recursion produces compared objects and arrows for the cartesian fragment. Identification-category constructors and higher composition compatibility are not covered by this syntax.

```agda
{-# OPTIONS --safe --without-K #-}
module SCT.VolumeI.Chapter05.Section01.Expressions.CartesianExpressions where
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core using (Weakening)
open import SCT.VolumeI.Chapter05.Section01.Products using (PreservesProducts)
open import SCT.VolumeI.Chapter05.Section01.Expressions.Functors using (Signature; Interpretation; image)
import SCT.VolumeI.Chapter05.Section01.Expressions.ComparisonObjects as Comparisons

module Terms {l : Level} (G : Signature l) where
  open Signature G
  data Cat : Set l where
    base : Object → Cat
    one : Cat
    product : Cat → Cat → Cat
  data Fun : Cat → Cat → Set l where
    atom : {a b : Object} → Arrow a b → Fun (base a) (base b)
    identity : (C : Cat) → Fun C C
    compose : {C D E : Cat} → Fun D E → Fun C D → Fun C E
    terminate : (C : Cat) → Fun C one
    first : {C D : Cat} → Fun (product C D) C
    second : {C D : Cat} → Fun (product C D) D
    pair : {P C D : Cat} → Fun P C → Fun P D → Fun P (product C D)

module Evaluate {l : Level} {G : Signature l} {T : Theory l l l} (I : Interpretation G T) where
  private
    module T = View T
  open Terms G
  category : Cat → T.CAT
  category (base a) = Interpretation.object I a
  category one = T.One
  category (product C D) = T._×_ (category C) (category D)
  functor : {C D : Cat} → Fun C D → T.MAP (category C) (category D)
  functor (atom f) = Interpretation.arrow I f
  functor (identity C) = T.id (category C)
  functor (compose g f) = T._∘_ (functor g) (functor f)
  functor (terminate C) = T.terminate (category C)
  functor first = T.pr₁
  functor second = T.pr₂
  functor (pair f g) = T.pair (functor f) (functor g)

module Compile {l : Level} {G : Signature l} {S T : Theory l l l}
  (W : Weakening S T) (P : PreservesProducts W) (I : Interpretation G S) where
  private
    module T = View T
    module W = Weakening W
    module A = Evaluate I
    module B = Evaluate (image W I)
    module C = Comparisons W P
  open Terms G

  category : (X : Cat) → T.Equiv (W.cat (A.category X)) (B.category X)
  category (base a) = record { functor = T.id _ ; isEquiv = T.id-isEquiv _ }
  category one = W.terminal
  category (product X Y) = C.Object.comparison (C.product
    (record { source = A.category X ; target = B.category X ; comparison = category X })
    (record { source = A.category Y ; target = B.category Y ; comparison = category Y }))

  object : Cat → C.Object
  object X = record { source = A.category X ; target = B.category X ; comparison = category X }

  arrow : (X : Cat) → T.MAP (W.cat (A.category X)) (B.category X)
  arrow X = T.Equiv.functor (category X)

  pack : {X Y : Cat} (f : Fun X Y)
    → T._=₁_ (T._∘_ (arrow Y) (W.map (A.functor f))) (T._∘_ (B.functor f) (arrow X))
    → C.Arrow (object X) (object Y)
  pack f witness = record { source = A.functor f ; target = B.functor f ; square = witness }

  square : {X Y : Cat} (f : Fun X Y)
    → T._=₁_ (T._∘_ (arrow Y) (W.map (A.functor f))) (T._∘_ (B.functor f) (arrow X))
  square (atom f) = T._∙_ (T._⁻¹ (T.comp-unitʳ (W.map (Interpretation.arrow I f))))
    (T.comp-unitˡ (W.map (Interpretation.arrow I f)))
  square (identity X) = C.Arrow.square (C.identity (object X))
  square (compose g f) = C.Arrow.square (C.compose (pack g (square g)) (pack f (square f)))
  square (terminate X) = C.Arrow.square (C.terminate (object X))
  square (first {X} {Y}) = C.Arrow.square (C.first (object X) (object Y))
  square (second {X} {Y}) = C.Arrow.square (C.second (object X) (object Y))
  square (pair f g) = C.Arrow.square (C.pair (pack f (square f)) (pack g (square g)))

  functor : {X Y : Cat} → Fun X Y → C.Arrow (object X) (object Y)
  functor f = pack f (square f)

-- This is an actual recursive comparison compiler with varying category
-- expressions. It covers the cartesian fragment, not identification-category
-- constructors or their higher coherences, and does not prove its own
-- comparison-composition theorem yet.
```
