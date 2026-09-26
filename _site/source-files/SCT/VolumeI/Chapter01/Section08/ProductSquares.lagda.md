# Product squares and their cocones

The common target of the two uncurrying calculations is the given square
multiplied by the parameter category. Its matching retains the product
composition comparisons, including the unitor in the parameter coordinate.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)

module SCT.VolumeI.Chapter01.Section08.ProductSquares
  {c m a : Level} (𝒯 : Theory c m a) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open import SCT.VolumeI.Chapter01.Section08.Squares 𝒯
open import SCT.VolumeI.Chapter01.Section08.CoconeCalculus.CoconePostcomposition 𝒯

productRestriction : (X : CAT) {A B : CAT} → MAP A B → MAP (X × A) (X × B)
productRestriction X f = productMap (id X) f

productRestriction-comp : (X : CAT) {A B C : CAT}
  (f : MAP A B) (g : MAP B C) →
  (productRestriction X g ∘ productRestriction X f) =₁ (productRestriction X (g ∘ f))
productRestriction-comp X f g =
  productMap-cong (comp-unitˡ (id X)) (idIso (g ∘ f)) ∙
    productMap-comp (id X) (id X) f g

productCocone : {A B C D : CAT}
  {u : MAP A B} {l : MAP A C} {r : MAP B D} {v : MAP C D} →
  (X : CAT) → Square u l r v →
  Cocone (productRestriction X u) (productRestriction X l) (X × D)
productCocone {u = u} {l} {r} {v} X s = record
  { left = productRestriction X r ; right = productRestriction X v
  ; match = (productRestriction-comp X l v) ⁻¹ ∙
      (productMap-cong (idIso (id X)) (Square.commute s) ∙ productRestriction-comp X u r) }

restrictionCocone : {A B C D E X : CAT}
  {u : MAP A B} {l : MAP A C} {r : MAP B D} {v : MAP C D} →
  Square u l r v → MAP (X × D) E →
  Cocone (productRestriction X u) (productRestriction X l) E
restrictionCocone {X = X} s h = coconePost h (productCocone X s)

restriction-action : {A B C D E X : CAT}
  {u : MAP A B} {l : MAP A C} {r : MAP B D} {v : MAP C D}
  (s : Square u l r v) {h k : MAP (X × D) E} → h =₁ k →
  CoconeIso (restrictionCocone s h) (restrictionCocone s k)
restriction-action {X = X} s = cocone-action (productCocone X s)
```
