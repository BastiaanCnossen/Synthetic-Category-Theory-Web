# Functors preserve the chosen identity expressions

The comparison comes from the associator between the two constant
interval diagrams. The split-projection calculation supplies its two
endpoint equations.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints

module SCT.VolumeI.Chapter02.Section02.IdentityExpressionPostcomposition
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I) where

open import SCT.VolumeI.Chapter02.Section01.Morphisms 𝒯 M ℱ I public
open import SCT.VolumeI.Chapter02.Section02.ExpressionIdentifications 𝒯 M ℱ I using (expressionIso-compose)
open import SCT.VolumeI.Chapter01.Section04.SplitProjectionCalculus 𝒯 using (section-comp)
open import SCT.VolumeI.Chapter01.Section06.InverseCalculus 𝒯 using (pre-inverse)
import SCT.VolumeI.Chapter01.Section03.PairingNaturality as PN
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-right)
import SCT.VolumeI.Chapter02.Section02.CurryPostcomposition as Post
import SCT.VolumeI.Chapter02.Section02.DiagramExpressionIdentifications as Diagrams

module At {Γ C D : CAT} (F : MAP C D) (x : MAP Γ C) where
  H = x ∘ pr₁ {C = Γ} {D = [1]}
  K = (F ∘ x) ∘ pr₁ {C = Γ} {D = [1]}
  aH : K =₁ (F ∘ H)
  aH = comp-assoc pr₁ x F
  module Endpoint (v : Obj-abs [1]) where
    i = insert {X = Γ} v
    old : ((F ∘ H) ∘ i) =₁ (F ∘ x)
    old = (F ◁ identity-boundary v x) ∙ comp-assoc i H F
    abstract
      comparison : (identity-boundary v (F ∘ x) ∙ (aH ⁻¹ ▷ i)) =₂ old
      comparison = cancel-right (aH ▷ i) old ∙
        isoComp-cong (section-comp pr₁ i (pair-β₁ _ _) x F) (pre-inverse aH i)
  module Source = Endpoint zero
  module Target = Endpoint one
  module Diagram = Diagrams.At 𝒯 M ℱ P I E (F ∘ H) K (aH ⁻¹)
    Source.old Target.old (identity-boundary zero (F ∘ x)) (identity-boundary one (F ∘ x))
    Source.comparison Target.comparison

  comparison : ExpressionIso (post-expression F (identity-expression x)) (identity-expression (F ∘ x))
  comparison = expressionIso-compose Diagram.comparison
    (Post.At.comparison 𝒯 M ℱ P I E F H (identity-boundary zero x) (identity-boundary one x))

post-identity : {Γ C D : CAT} (F : MAP C D) (x : MAP Γ C) →
  ExpressionIso (post-expression F (identity-expression x)) (identity-expression (F ∘ x))
post-identity = At.comparison
```
