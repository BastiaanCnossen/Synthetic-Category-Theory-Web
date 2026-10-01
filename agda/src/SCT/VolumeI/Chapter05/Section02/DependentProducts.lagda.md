# Dependent products

The source theory is the ambient context and the target theory is its
extension by an anima. Evaluation and currying are the data in
`axiom:Contexts_Dependent_Product`. The uniqueness axiom concerns the
specific functor on entire identification animae constructed from these data.
No equality between the two theories is used.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core

module SCT.VolumeI.Chapter05.Section02.DependentProducts
  {l : Level} {S T : Theory l l l} (W : Weakening S T) where

private
  module S = View S
  module T = View T
module W = Weakening W

record ProductData : Set l where
  field
    Π : T.CAT → S.CAT
    evaluation : (B : T.CAT) → T.MAP (W.cat (Π B)) B

  uncurry : {X : S.CAT} {B : T.CAT} → S.MAP X (Π B) → T.MAP (W.cat X) B
  uncurry {B = B} h = T._∘_ (evaluation B) (W.map h)

  field
    curry : {X : S.CAT} {B : T.CAT} → T.MAP (W.cat X) B → S.MAP X (Π B)
    curry-β : {X : S.CAT} {B : T.CAT} (f : T.MAP (W.cat X) B)
      → T._=₁_ f (uncurry (curry f))
    Π-isAn : {B : T.CAT} → T.isAn B → S.isAn (Π B)

  uncurry-family : {X : S.CAT} {B : T.CAT} (h k : S.MAP X (Π B))
    → T.MAP (W.cat (S._＝_ h k)) (T._＝_ (uncurry h) (uncurry k))
  uncurry-family {B = B} h k = T._∘_ (T.postWhisker (evaluation B)) (W.phi h k)

  comparison : {X : S.CAT} {B : T.CAT} (h k : S.MAP X (Π B))
    → S.MAP (S._＝_ h k) (Π (T._＝_ (uncurry h) (uncurry k)))
  comparison h k = curry (uncurry-family h k)

record ProductLaws (D : ProductData) : Set l where
  open ProductData D
  field
    comparison-isEquiv : {X : S.CAT} {B : T.CAT} (h k : S.MAP X (Π B))
      → S.IsEquiv (comparison h k)

record DependentProducts : Set l where
  field
    dataΠ : ProductData
    lawsΠ : ProductLaws dataΠ
  open ProductData dataΠ public
  open ProductLaws lawsΠ public
```
