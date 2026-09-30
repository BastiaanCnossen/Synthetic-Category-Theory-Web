# Iterated restriction along a section

Restricting first along a retraction and then along its section recovers
the original expression. Both endpoints use the actual section
identification, associator, and right unitor.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking

module SCT.VolumeI.Chapter02.Section02.MorphismCalculus.RestrictionAlongSection
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter02.Section01.Morphisms 𝒯 M ℱ I public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionFrameCalculus 𝒯 M ℱ I using (retarget-assoc; retarget-cong)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionRestriction 𝒯 M ℱ I
  using (restrict-expression-compose; restrict-expression-parameter; restrict-expression-id)

module At {C D K : CAT} (p : MAP C D) (s : MAP D C) (ρ : (p ∘ s) =₁ id D)
  {x y : MAP D K} (b : MorphismExpression x y) where
  frame : (z : MAP D K) → ((z ∘ p) ∘ s) =₁ z
  frame z = comp-unitʳ z ∙ ((z ◁ ρ) ∙ comp-assoc s p z)
  restricted = restrict-expression (restrict-expression b p) s

  abstract
    value : ExpressionIso (retarget-expression restricted (frame x) (frame y)) b
    value = expressionIso-compose (restrict-expression-id b)
      (expressionIso-compose
        (retarget-expressionIso (restrict-expression-parameter b ρ) (comp-unitʳ x) (comp-unitʳ y))
        (expressionIso-compose
          (retarget-expressionIso
            (expressionIso-compose
              (retarget-expressionIso (restrict-expression-compose b p s) (x ◁ ρ) (y ◁ ρ))
              (expressionIso-inverse (retarget-assoc restricted
                (comp-assoc s p x) (comp-assoc s p y) (x ◁ ρ) (y ◁ ρ))))
            (comp-unitʳ x) (comp-unitʳ y))
          (expressionIso-inverse (retarget-assoc restricted
            ((x ◁ ρ) ∙ comp-assoc s p x) ((y ◁ ρ) ∙ comp-assoc s p y)
            (comp-unitʳ x) (comp-unitʳ y)))))
```
