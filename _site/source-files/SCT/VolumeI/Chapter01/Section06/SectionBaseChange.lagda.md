# Base change of a section

A specified section of a functor pulls back along any base functor.
The comparison with the original section is retained as a whole cone
comparison, including its compatibility with the pullback matching.
No adjunction or interval axiom is used here.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws

module SCT.VolumeI.Chapter01.Section06.SectionBaseChange
  {c m a : Level} (𝒯 : Theory c m a) (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯 public
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P

module At {C D D′ T : CAT} (p : MAP C D) (s : MAP D C)
  (ρ : (p ∘ s) =₁ id D) (v : MAP D′ D)
  (t : Cone p v T) (et : IsPullback t) where

  section-cone : Cone p v D′
  section-cone = record
    { left = s ∘ v
    ; right = id D′
    ; match = (comp-unitʳ v) ⁻¹ ∙
        (comp-unitˡ v ∙ ((ρ ▷ v) ∙ (comp-assoc v s p) ⁻¹)) }

  module U = UniversalCone t et using (factor; factor-β)
  section : MAP D′ T
  section = U.factor section-cone

  comparison : ConeIso (conePre section t) section-cone
  comparison = U.factor-β section-cone

  original-section : (Cone.left t ∘ section) =₁ (s ∘ v)
  original-section = ConeIso.leftIso comparison

  section-identification : (Cone.right t ∘ section) =₁ id D′
  section-identification = ConeIso.rightIso comparison

  compatible : (Cone.match section-cone ∙ (p ◁ original-section)) =₂
    ((v ◁ section-identification) ∙ Cone.match (conePre section t))
  compatible = ConeIso.compatible comparison
```
