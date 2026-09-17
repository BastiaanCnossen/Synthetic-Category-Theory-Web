# The projection-induced comparison on isomorphism animae

The target is another application of the same pullback constructor, now
to three isomorphism animae. Its two maps paste a varying leg comparison
with the fixed matching isomorphisms. Interchange supplies the matching
for the comparison functor; it is derived here, not an additional axiom.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.Setup as Setup
import SCT.VolumeI.Chapter01.Section05.PullbackData as Data

module SCT.VolumeI.Chapter01.Section05.PullbackComparison
  {c m a : Level} (𝒯 : Theory c m a) (P : Data.PullbackData 𝒯) where

open Setup 𝒯
open import SCT.VolumeI.Chapter01.Section05.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section05.ConeAction 𝒯
open Data.PullbackData P

module IsoComparison {C D E T : CAT} {f : MAP C E} {g : MAP D E}
  (h k : MAP T (Pullback f g)) where

  module A = Action (pbCone f g) h k

  leftMatch = Cone.match (conePre h (pbCone f g))
  rightMatch = Cone.match (conePre k (pbCone f g))

  Left = (pb₁ ∘ h) ＝ (pb₁ ∘ k)
  Right = (pb₂ ∘ h) ＝ (pb₂ ∘ k)
  Middle = (f ∘ (pb₁ ∘ h)) ＝ (g ∘ (pb₂ ∘ k))

  leftMap : MAP Left Middle
  leftMap = const rightMatch ∙ postWhisker f

  rightMap : MAP Right Middle
  rightMap = postWhisker g ∙ const leftMatch

  Target : CAT
  Target = Pullback leftMap rightMap

  target-isAn : isAn Target
  target-isAn = pullback-isAn leftMap rightMap (iso-isAn _ _) (iso-isAn _ _) (iso-isAn _ _)

  left-evaluation : =₁ (leftMap ∘ postWhisker pb₁)
    (const rightMatch ∙ (f ◁ postWhisker pb₁))
  left-evaluation = isoComp-evaluate (const rightMatch) (postWhisker f) (postWhisker pb₁)
    (const-pre rightMatch (postWhisker pb₁)) (idIso _)

  right-evaluation : =₁ (rightMap ∘ postWhisker pb₂)
    ((g ◁ postWhisker pb₂) ∙ const leftMatch)
  right-evaluation = isoComp-evaluate (postWhisker g) (const leftMatch) (postWhisker pb₂)
    (idIso _) (const-pre leftMatch (postWhisker pb₂))

  matching : =₁ (leftMap ∘ postWhisker pb₁) (rightMap ∘ postWhisker pb₂)
  matching = A.matching

  comparisonCone : Cone leftMap rightMap (h ＝ k)
  comparisonCone = A.universal

  forward : MAP (h ＝ k) Target
  forward = pbLift comparisonCone
```
