# The identity functor on expressions

Postcomposition by the identity functor gives the original expression
after the external unitors identify its endpoints. The calculation uses
the proved compatibility of the left unitor with composition.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints

module SCT.VolumeI.Chapter02.Section02.MorphismCalculus.IdentityFunctorExpressions
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I) where

open import SCT.VolumeI.Chapter02.Section01.Morphisms 𝒯 M ℱ I public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionPostcomposition 𝒯 M ℱ I using (post-expressionIso)
import SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Postcomposition.CurryPostcomposition as Post
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.DiagramExpressionIdentifications as Diagrams
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.ProductFunctorUnits as ProductUnits
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural
open ProductUnits vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle using (left-unitor-comp)
open Structural vocabulary terminal products productLaws composition whiskering using (postWhisker-id-at)

module Curried {Γ C : CAT} {x y : MAP Γ C} (H : MAP (Γ × [1]) C)
  (p : (H ∘ insert zero) =₁ x) (q : (H ∘ insert one) =₁ y) where
  module Endpoint (v : Obj-abs [1]) {z : MAP Γ C} (r : (H ∘ insert v) =₁ z) where
    i = insert {X = Γ} v
    before = (id C ◁ r) ∙ comp-assoc i H (id C)
    abstract
      compatible : (r ∙ (comp-unitˡ H ▷ i)) =₂ (comp-unitˡ z ∙ before)
      compatible = isoComp-assoc-at (comp-unitˡ z) (id C ◁ r) (comp-assoc i H (id C)) ∙
        isoComp-cong ((postWhisker-id-at r) ⁻¹) (idIso (comp-assoc i H (id C))) ∙
        (isoComp-assoc-at r (comp-unitˡ (H ∘ i)) (comp-assoc i H (id C))) ⁻¹ ∙
        isoComp-cong (idIso r) ((left-unitor-comp i H) ⁻¹)
  module Source = Endpoint zero p
  module Target = Endpoint one q
  module Diagram = Diagrams.At 𝒯 M ℱ P I E (id C ∘ H) H (comp-unitˡ H)
    (comp-unitˡ x ∙ Source.before) (comp-unitˡ y ∙ Target.before) p q Source.compatible Target.compatible
    using (comparison)

  comparison : ExpressionIso
    (retarget-expression (post-expression (id C) (expression H p q)) (comp-unitˡ x) (comp-unitˡ y))
    (expression H p q)
  comparison = expressionIso-compose Diagram.comparison
    (expressionIso-compose
      (Diagrams.retarget-curried 𝒯 M ℱ P I E (id C ∘ H) Source.before Target.before (comp-unitˡ x) (comp-unitˡ y))
      (retarget-expressionIso (Post.At.comparison 𝒯 M ℱ P I E (id C) H p q) (comp-unitˡ x) (comp-unitˡ y)))

post-id : {Γ C : CAT} {x y : MAP Γ C} (f : MorphismExpression x y) →
  ExpressionIso (retarget-expression (post-expression (id C) f) (comp-unitˡ x) (comp-unitˡ y)) f
post-id {C = C} {x} {y} f = expressionIso-compose (expressionIso-inverse Recover.comparison)
  (expressionIso-compose (Curried.comparison Recover.H Recover.p Recover.q)
    (retarget-expressionIso (post-expressionIso (id C) Recover.comparison) (comp-unitˡ x) (comp-unitˡ y)))
  where module Recover = Diagrams.Recovery 𝒯 M ℱ P I E f
```
