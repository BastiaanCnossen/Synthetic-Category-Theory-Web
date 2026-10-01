# Dependent sums

The pair functor and extension rule are the data of
`axiom:Contexts_Dependent_Sum`. Its identification comparison lands in a
dependent product of a local identification anima. The dependent product
structure is therefore a parameter, preceding the sum axiom.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core
import SCT.VolumeI.Chapter05.Section02.DependentProducts as Products

module SCT.VolumeI.Chapter05.Section02.DependentSums
  {l : Level} {S T : Theory l l l} (W : Weakening S T)
  (P : Products.DependentProducts W) where

private
  module S = View S
  module T = View T
module W = Weakening W
module P = Products.DependentProducts P

record SumData : Set l where
  field
    Σ : T.CAT → S.CAT
    pair : (B : T.CAT) → T.MAP B (W.cat (Σ B))

  flatten : {B : T.CAT} {D : S.CAT} → S.MAP (Σ B) D → T.MAP B (W.cat D)
  flatten {B} h = T._∘_ (W.map h) (pair B)

  field
    extend : {B : T.CAT} {D : S.CAT} → T.MAP B (W.cat D) → S.MAP (Σ B) D
    extend-β : {B : T.CAT} {D : S.CAT} (f : T.MAP B (W.cat D))
      → T._=₁_ f (flatten (extend f))

  flatten-family : {B : T.CAT} {D : S.CAT} (h k : S.MAP (Σ B) D)
    → T.MAP (W.cat (S._＝_ h k)) (T._＝_ (flatten h) (flatten k))
  flatten-family {B} h k = T._∘_ (T.preWhisker (pair B)) (W.phi h k)

  comparison : {B : T.CAT} {D : S.CAT} (h k : S.MAP (Σ B) D)
    → S.MAP (S._＝_ h k) (P.Π (T._＝_ (flatten h) (flatten k)))
  comparison h k = P.curry (flatten-family h k)

record SumLaws (D : SumData) : Set l where
  open SumData D
  field
    comparison-isEquiv : {B : T.CAT} {D : S.CAT} (h k : S.MAP (Σ B) D)
      → S.IsEquiv (comparison h k)

record DependentSums : Set l where
  field
    dataΣ : SumData
    lawsΣ : SumLaws dataΣ
  open SumData dataΣ public
  open SumLaws lawsΣ public
```
