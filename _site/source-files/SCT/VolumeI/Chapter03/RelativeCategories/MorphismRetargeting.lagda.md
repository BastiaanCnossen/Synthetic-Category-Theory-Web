# Changing the endpoints of a relative transformation

Identifications over the base change both endpoints of a transformation
over the base. Compatibility of the specified structure triangles is
exactly the frame equation required for this operation.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section02.SegalAxiom as Segal

module SCT.VolumeI.Chapter03.RelativeCategories.MorphismRetargeting
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter03.RelativeCategories.Morphisms 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
  public using (FunctorOverIso; inverse-iso-over)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionFrameCalculus 𝒯 M ℱ I
  using (post-retarget; retarget-assoc; retarget-cong; retarget-cancel)

module OverBase {C D B : CAT} (p : MAP C B) (q : MAP D B) where
  open Over p q

  abstract
    retarget-isOver : {u v u′ v′ : FunctorOver p q}
      (α : MorphismExpression (FunctorLift.lift u) (FunctorLift.lift v))
      (ξ : FunctorOverIso u u′) (ζ : FunctorOverIso v v′) → IsOver u v α →
      IsOver u′ v′ (retarget-expression α (FunctorOverIso.underlying ξ) (FunctorOverIso.underlying ζ))
    retarget-isOver {u} {v} {u′} {v′} α ξ ζ over = expressionIso-compose over
      (expressionIso-compose
        (retarget-cong (post-expression q α) (FunctorOverIso.compatible ξ) (FunctorOverIso.compatible ζ))
        (expressionIso-compose
          (retarget-assoc (post-expression q α) (q ◁ FunctorOverIso.underlying ξ) (q ◁ FunctorOverIso.underlying ζ)
            (FunctorLift.comparison u′) (FunctorLift.comparison v′))
          (retarget-expressionIso (post-retarget q α (FunctorOverIso.underlying ξ) (FunctorOverIso.underlying ζ))
            (FunctorLift.comparison u′) (FunctorLift.comparison v′))))

  abstract
    retarget-reflects : {u v u′ v′ : FunctorOver p q}
      (α : MorphismExpression (FunctorLift.lift u) (FunctorLift.lift v))
      (ξ : FunctorOverIso u u′) (ζ : FunctorOverIso v v′) →
      IsOver u′ v′ (retarget-expression α (FunctorOverIso.underlying ξ) (FunctorOverIso.underlying ζ)) → IsOver u v α
    retarget-reflects α ξ ζ over = identified-isOver
      (retarget-cancel α (FunctorOverIso.underlying ξ) (FunctorOverIso.underlying ζ))
      (retarget-isOver (retarget-expression α (FunctorOverIso.underlying ξ) (FunctorOverIso.underlying ζ))
        (inverse-iso-over ξ) (inverse-iso-over ζ) over)

  retarget : {u v u′ v′ : FunctorOver p q} → MorphismOver u v →
    FunctorOverIso u u′ → FunctorOverIso v v′ → MorphismOver u′ v′
  retarget α ξ ζ = record
    { underlying = retarget-expression (MorphismOver.underlying α)
        (FunctorOverIso.underlying ξ) (FunctorOverIso.underlying ζ)
    ; over-base = retarget-isOver (MorphismOver.underlying α) ξ ζ (MorphismOver.over-base α) }
```
