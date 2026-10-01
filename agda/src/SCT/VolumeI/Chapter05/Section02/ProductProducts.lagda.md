# Dependent products preserve binary products

The comparison is the pair of the functors induced by the local
projections. Its inverse curries the pair of the two evaluation maps.
Both inverse identifications follow from the two universal properties.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core
import SCT.VolumeI.Chapter05.Section02.DependentProducts as Products
import SCT.VolumeI.Chapter05.Section02.ProductFunctoriality as Action
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Calculus as Calculus

module SCT.VolumeI.Chapter05.Section02.ProductProducts
  {l : Level} {S T : Theory l l l} (W : Weakening S T)
  (P : Products.DependentProducts W) (B C : View.CAT T) where

private
  module S = View S
  module T = View T
module W = Weakening W
open Products.DependentProducts P using (Π; evaluation; curry; curry-β; uncurry)
open Action W P using (reflect; uncurry-pre; Π-map; Π-map-β)
open T using (_∘_; _◁_; _▷_; _⁻¹)
open Calculus T using (_then_)

F : S.MAP (Π (T._×_ B C)) (S._×_ (Π B) (Π C))
F = S.pair (Π-map T.pr₁) (Π-map T.pr₂)

G : S.MAP (S._×_ (Π B) (Π C)) (Π (T._×_ B C))
G = curry (T.pair (uncurry S.pr₁) (uncurry S.pr₂))

first : T._=₁_ (T.pr₁ ∘ uncurry G) (uncurry S.pr₁)
first = (T.pr₁ ◁ (curry-β (T.pair (uncurry S.pr₁) (uncurry S.pr₂))) ⁻¹) then
  T.pair-β₁ (uncurry S.pr₁) (uncurry S.pr₂)

second : T._=₁_ (T.pr₂ ∘ uncurry G) (uncurry S.pr₂)
second = (T.pr₂ ◁ (curry-β (T.pair (uncurry S.pr₁) (uncurry S.pr₂))) ⁻¹) then
  T.pair-β₂ (uncurry S.pr₁) (uncurry S.pr₂)

projection-uncurry : {D E : T.CAT} {X : S.CAT} (f : T.MAP D E) (h : S.MAP X (Π D))
  → T._=₁_ (uncurry (S._∘_ (Π-map f) h)) (f ∘ uncurry h)
projection-uncurry {D} f h = uncurry-pre (Π-map f) h then
  ((Π-map-β f) ⁻¹ ▷ W.map h) then T.comp-assoc (W.map h) (evaluation D) f

right-first : S._=₁_ (S._∘_ (Π-map T.pr₁) G) S.pr₁
right-first = reflect (projection-uncurry T.pr₁ G then first)

right-second : S._=₁_ (S._∘_ (Π-map T.pr₂) G) S.pr₂
right-second = reflect (projection-uncurry T.pr₂ G then second)

right-inverse : S._=₁_ (S._∘_ F G) (S.id (S._×_ (Π B) (Π C)))
right-inverse = S._∘_ (S.IsEquiv.inverse (S.product-isoMap-isEquiv _ _)) (S.pair F₁ F₂)
  where
  F₁ : S._=₁_ (S._∘_ S.pr₁ (S._∘_ F G)) (S._∘_ S.pr₁ (S.id _))
  F₁ = S._∙_ (S._⁻¹ (S.comp-unitʳ S.pr₁))
    (S._∙_ right-first (S._∙_ (S._▷_ (S.pair-β₁ (Π-map T.pr₁) (Π-map T.pr₂)) G)
      (S._⁻¹ (S.comp-assoc G F S.pr₁))))
  F₂ : S._=₁_ (S._∘_ S.pr₂ (S._∘_ F G)) (S._∘_ S.pr₂ (S.id _))
  F₂ = S._∙_ (S._⁻¹ (S.comp-unitʳ S.pr₂))
    (S._∙_ right-second (S._∙_ (S._▷_ (S.pair-β₂ (Π-map T.pr₁) (Π-map T.pr₂)) G)
      (S._⁻¹ (S.comp-assoc G F S.pr₂))))

left-first : T._=₁_ (T.pr₁ ∘ uncurry (S._∘_ G F)) (T.pr₁ ∘ uncurry (S.id _))
left-first = (T.pr₁ ◁ uncurry-pre G F) then
  (T.comp-assoc (W.map F) (uncurry G) T.pr₁) ⁻¹ then
  (first ▷ W.map F) then (uncurry-pre S.pr₁ F) ⁻¹ then
  (evaluation B ◁ W.term (S.pair-β₁ (Π-map T.pr₁) (Π-map T.pr₂))) then
  (Π-map-β T.pr₁) ⁻¹ then
  (T.pr₁ ◁ ((T.comp-unitʳ (evaluation (T._×_ B C))) ⁻¹ then
    (evaluation (T._×_ B C) ◁ (W.unit _) ⁻¹)))

left-second : T._=₁_ (T.pr₂ ∘ uncurry (S._∘_ G F)) (T.pr₂ ∘ uncurry (S.id _))
left-second = (T.pr₂ ◁ uncurry-pre G F) then
  (T.comp-assoc (W.map F) (uncurry G) T.pr₂) ⁻¹ then
  (second ▷ W.map F) then (uncurry-pre S.pr₂ F) ⁻¹ then
  (evaluation C ◁ W.term (S.pair-β₂ (Π-map T.pr₁) (Π-map T.pr₂))) then
  (Π-map-β T.pr₂) ⁻¹ then
  (T.pr₂ ◁ ((T.comp-unitʳ (evaluation (T._×_ B C))) ⁻¹ then
    (evaluation (T._×_ B C) ◁ (W.unit _) ⁻¹)))

left-inverse : S._=₁_ (S._∘_ G F) (S.id (Π (T._×_ B C)))
left-inverse = reflect ((T.IsEquiv.inverse (T.product-isoMap-isEquiv _ _)) ∘ T.pair left-first left-second)

comparison-isEquiv : S.IsEquiv F
comparison-isEquiv = record
  { inverse = G ; sectionIso = S._⁻¹ left-inverse ; retractionIso = S._⁻¹ right-inverse }

comparison : S.Equiv (Π (T._×_ B C)) (S._×_ (Π B) (Π C))
comparison = record { functor = F ; isEquiv = comparison-isEquiv }
```
