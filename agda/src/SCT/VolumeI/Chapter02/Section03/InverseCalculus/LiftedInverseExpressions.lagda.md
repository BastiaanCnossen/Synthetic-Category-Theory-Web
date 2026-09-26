# Reading inverse equations from a lift

A lift to `Iso C` restricts the two universal inverse triangles. Their
common edge is identified with the given framed morphism expression;
their long edges remain constant. This gives both inverse equations with
the original endpoint frames, and proves the converse to
`invertible-expression-lift` for every absolute parameter category.

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

module SCT.VolumeI.Chapter02.Section03.InverseCalculus.LiftedInverseExpressions
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section03.InverseCalculus.UniversalInverseExpressions 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section03.InverseCalculus.InverseTriangleExpressions 𝒯 M ℱ P I E S
  using (module Right; module Left)

module ReadInverse {Γ C : CAT} {x y : MAP Γ C}
  (f : MorphismExpression x y) (w : IsoLift (MorphismExpression.arrow f)) where
  module W = IsoLift w
  module U = Universal C
    using (right-triangle; left-triangle; right-short; left-short; right-long; left-long)

  right-triangle left-triangle : MAP Γ (Triangles C)
  right-triangle = U.right-triangle ∘ W.lift
  left-triangle = U.left-triangle ∘ W.lift

  right-short : (edge₀ ∘ right-triangle) =₁ MorphismExpression.arrow f
  right-short = W.comparison ∙ ((U.right-short ▷ W.lift) ∙
    (comp-assoc W.lift U.right-triangle edge₀) ⁻¹)

  left-short : (edge₂ ∘ left-triangle) =₁ MorphismExpression.arrow f
  left-short = W.comparison ∙ ((U.left-short ▷ W.lift) ∙
    (comp-assoc W.lift U.left-triangle edge₂) ⁻¹)

  right-long : (edge₁ ∘ right-triangle) =₁
    (identityArrow ∘ ((pr₂ ∘ isoObjects) ∘ W.lift))
  right-long = comp-assoc W.lift (pr₂ ∘ isoObjects) identityArrow ∙
    ((U.right-long ▷ W.lift) ∙ (comp-assoc W.lift U.right-triangle edge₁) ⁻¹)

  left-long : (edge₁ ∘ left-triangle) =₁
    (identityArrow ∘ ((pr₁ ∘ isoObjects) ∘ W.lift))
  left-long = comp-assoc W.lift (pr₁ ∘ isoObjects) identityArrow ∙
    ((U.left-long ▷ W.lift) ∙ (comp-assoc W.lift U.left-triangle edge₁) ⁻¹)

  module RightInverse = Right f right-triangle right-short right-long
    using (inverse-expression; inverse-law)
  module LeftInverse = Left f left-triangle left-short left-long
    using (inverse-expression; inverse-law)

  inverse-data : IsInvertibleExpression f
  inverse-data = record
    { right-inverse = RightInverse.inverse-expression
    ; left-inverse = LeftInverse.inverse-expression
    ; right-inverse-law = RightInverse.inverse-law
    ; left-inverse-law = LeftInverse.inverse-law }

lift-invertible-expression : {Γ C : CAT} {x y : MAP Γ C}
  (f : MorphismExpression x y) → IsoLift (MorphismExpression.arrow f) → IsInvertibleExpression f
lift-invertible-expression = ReadInverse.inverse-data
```
