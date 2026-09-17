# The groupoid core and its universal property

This follows `def:Animated_Core` and `cor:Animated_Core_Is_Universal`.
The core is the existing anima `Map One C`. Its inclusion is exactly the
book's composite through `Fun One C` and evaluation at the terminal object.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section06.FunctorCategories as Categories

module SCT.VolumeI.Chapter01.Section07.Core
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (F : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section06.Currying 𝒯 M F
open import SCT.VolumeI.Chapter01.Section06.TerminalDomain 𝒯 M F
open import SCT.VolumeI.Chapter01.Section07.MappingComparison 𝒯 M F
open import SCT.VolumeI.Chapter01.Section03.EquivalenceDetection 𝒯 M using (post-tests-animae)

Core : CAT → CAT
Core C = Map One C

core-isAn : (C : CAT) → isAn (Core C)
core-isAn C = map-isAn One C

coreInclusion : (C : CAT) → MAP (Core C) C
coreInclusion C = evalAt (id One) ∘ mappingInclusion One C

core-universal : (X C : CAT) → isAn X → IsEquiv (mapPost {C = X} (coreInclusion C))
core-universal X C xAn = equiv-transport (mapPost-comp (mappingInclusion One C) (evalAt (id One)))
  (equiv-compose (mapPost (mappingInclusion One C)) (mapPost (evalAt (id One)))
    (InclusionComparison.inclusion-isEquiv X One C xAn) (mapPost-isEquiv (evalAt (id One)) (evalAt-point-isEquiv C)))

module CoreLift {X C : CAT} (xAn : isAn X) (f : MAP X C) where
  chosen = equiv-lift (core-universal X C xAn) (nameMap f)
  point = FunctorLift.lift chosen
  lift : MAP X (Core C)
  lift = decodeMap point
  comparison : =₁ (coreInclusion C ∘ lift) f
  comparison = unnamedIso (FunctorLift.comparison chosen ∙
    ((mapPost (coreInclusion C) ◁ name-decode point) ∙ invIso (mapPost-name (coreInclusion C) lift)))

core-of-anima : (C : CAT) → isAn C → IsEquiv (coreInclusion C)
core-of-anima C cAn = post-tests-animae (core-isAn C) cAn (coreInclusion C)
  (λ X xAn → core-universal X C xAn)
```

