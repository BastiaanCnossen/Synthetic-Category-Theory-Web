# Functors induced by maps of cospans

The construction `con:Functoriality_Of_Pullbacks` retains both squares of
the cospan map. Its matching isomorphism passes through the image of the
source matching isomorphism, with the indicated associators.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.Setup as Setup
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws

module SCT.VolumeI.Chapter01.Section06.PullbackFunctor
  {c m a : Level} (𝒯 : Theory c m a) (P : Laws.PullbackStructure 𝒯) where

open Setup 𝒯
open Laws.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯

record CospanMap {C D E C′ D′ E′ : CAT}
  (f : MAP C E) (g : MAP D E) (f′ : MAP C′ E′) (g′ : MAP D′ E′) : Set m where
  field
    left : MAP C C′
    right : MAP D D′
    base : MAP E E′
    leftSquare : (f′ ∘ left) =₁ (base ∘ f)
    rightSquare : (g′ ∘ right) =₁ (base ∘ g)

  mapCone : {T : CAT} → Cone f g T → Cone f′ g′ T
  mapCone s = record
    { left = left ∘ Cone.left s
    ; right = right ∘ Cone.right s
    ; match = comp-assoc (Cone.right s) right g′ ∙
        ((rightSquare ⁻¹ ▷ Cone.right s) ∙
        ((comp-assoc (Cone.right s) g base) ⁻¹ ∙
        ((base ◁ Cone.match s) ∙
        (comp-assoc (Cone.left s) f base ∙
        ((leftSquare ▷ Cone.left s) ∙ (comp-assoc (Cone.left s) left f′) ⁻¹))))) }

  pullbackMap : MAP (Pullback f g) (Pullback f′ g′)
  pullbackMap = pullbackLift (mapCone (pullbackCone f g))

  pullbackMap-β : ConeIso (conePre pullbackMap (pullbackCone f′ g′)) (mapCone (pullbackCone f g))
  pullbackMap-β = pullbackLift-β (mapCone (pullbackCone f g))
```
