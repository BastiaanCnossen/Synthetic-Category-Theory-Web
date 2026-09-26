# The projection-induced comparison on isomorphism animae

The target is another application of the same pullback constructor, now
to three isomorphism animae. Its two maps paste a varying leg comparison
with the fixed matching isomorphisms. Interchange supplies the matching
for the comparison functor; it is derived here, not an additional axiom.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.Setup as Setup
import SCT.VolumeI.Chapter01.Section06.PullbackData as Data

module SCT.VolumeI.Chapter01.Section06.PullbackComparison
  {c m a : Level} (𝒯 : Theory c m a) (P : Data.PullbackData 𝒯) where

open Setup 𝒯
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeAction 𝒯
open Data.PullbackData P

module IsoComparison {C D E T : CAT} {f : MAP C E} {g : MAP D E}
  (h k : MAP T (Pullback f g)) where

  module A = Action (pullbackCone f g) h k

  leftMatch = Cone.match (conePre h (pullbackCone f g))
  rightMatch = Cone.match (conePre k (pullbackCone f g))

  Left = (pullback₁ ∘ h) ＝ (pullback₁ ∘ k)
  Right = (pullback₂ ∘ h) ＝ (pullback₂ ∘ k)
  Middle = (f ∘ (pullback₁ ∘ h)) ＝ (g ∘ (pullback₂ ∘ k))

  leftMap : MAP Left Middle
  leftMap = const rightMatch ∙ postWhisker f

  rightMap : MAP Right Middle
  rightMap = postWhisker g ∙ const leftMatch

  Target : CAT
  Target = Pullback leftMap rightMap

  target-isAn : isAn Target
  target-isAn = pullback-isAn leftMap rightMap (＝-isAn _ _) (＝-isAn _ _) (＝-isAn _ _)

  left-evaluation : (leftMap ∘ postWhisker pullback₁) =₁
    (const rightMatch ∙ (f ◁ postWhisker pullback₁))
  left-evaluation = isoComp-evaluate (const rightMatch) (postWhisker f) (postWhisker pullback₁)
    (const-pre rightMatch (postWhisker pullback₁)) (idIso _)

  right-evaluation : (rightMap ∘ postWhisker pullback₂) =₁
    ((g ◁ postWhisker pullback₂) ∙ const leftMatch)
  right-evaluation = isoComp-evaluate (postWhisker g) (const leftMatch) (postWhisker pullback₂)
    (idIso _) (const-pre leftMatch (postWhisker pullback₂))

  matching : (leftMap ∘ postWhisker pullback₁) =₁ (rightMap ∘ postWhisker pullback₂)
  matching = A.matching

  comparisonCone : Cone leftMap rightMap (h ＝ k)
  comparisonCone = A.universal

  forward : MAP (h ＝ k) Target
  forward = pullbackLift comparisonCone
```
