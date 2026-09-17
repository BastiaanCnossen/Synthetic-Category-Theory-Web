# Functors induced by maps of cospans

The construction `con:Functoriality_Of_Pullbacks` retains both squares of
the cospan map. Its matching isomorphism passes through the image of the
source matching isomorphism, with the indicated associators.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.Setup as Setup
import SCT.VolumeI.Chapter01.Section05.PullbackLaws as Laws

module SCT.VolumeI.Chapter01.Section05.PullbackFunctor
  {c m a : Level} (𝒯 : Theory c m a) (P : Laws.PullbackStructure 𝒯) where

open Setup 𝒯
open Laws.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section05.Cones 𝒯

record CospanMap {C D E C′ D′ E′ : CAT}
  (f : MAP C E) (g : MAP D E) (f′ : MAP C′ E′) (g′ : MAP D′ E′) : Set m where
  field
    left : MAP C C′
    right : MAP D D′
    base : MAP E E′
    leftSquare : NatIso (f′ ∘ left) (base ∘ f)
    rightSquare : NatIso (g′ ∘ right) (base ∘ g)

  mapCone : {T : CAT} → Cone f g T → Cone f′ g′ T
  mapCone s = record
    { left = left ∘ Cone.left s
    ; right = right ∘ Cone.right s
    ; match = comp-assoc (Cone.right s) right g′ ∙
        ((invIso rightSquare ▷ Cone.right s) ∙
        (invIso (comp-assoc (Cone.right s) g base) ∙
        ((base ◁ Cone.match s) ∙
        (comp-assoc (Cone.left s) f base ∙
        ((leftSquare ▷ Cone.left s) ∙ invIso (comp-assoc (Cone.left s) left f′)))))) }

  pullbackMap : MAP (Pullback f g) (Pullback f′ g′)
  pullbackMap = pbLift (mapCone (pbCone f g))

  pullbackMap-β : ConeIso (conePre pullbackMap (pbCone f′ g′)) (mapCone (pbCone f g))
  pullbackMap-β = pbLift-β (mapCone (pbCone f g))
```
