# The natural associativity comparison

For `prop:Composition_Is_Associative`, use the category of composable
triples as the parameter category. The comparisons in
`ExpressionAssociativity` then give an identification of the two actual
composition functors, retaining their source and target maps to `C`.

The two pullback matchings specify the middle endpoints of the universal
triple. No equality of those endpoints is imposed judgmentally.

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
import SCT.VolumeI.Chapter02.Section01.CommutativeSquareAxiom as Squares

module SCT.VolumeI.Chapter02.Section02.Associativity
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section02.ExpressionAssociativity 𝒯 M ℱ P I E S Q
  public using (associativity; global-associativity)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.GlobalCompositionExpressions 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open Laws.PullbackStructure P

module Universal (C : CAT) where
  first-of-pair second-of-pair : MAP (Composable C) (Ar C)
  first-of-pair = pullback₁ {f = ev₁} {g = ev₀}
  second-of-pair = pullback₂ {f = ev₁} {g = ev₀}
  pair-target : MAP (Composable C) C
  pair-target = ev₁ ∘ second-of-pair

  ComposableTriples : CAT
  ComposableTriples = Pullback pair-target ev₀
  pair-part : MAP ComposableTriples (Composable C)
  pair-part = pullback₁
  last-part : MAP ComposableTriples (Ar C)
  last-part = pullback₂
  first-pair : Cone (ev₁ {C}) ev₀ ComposableTriples
  first-pair = conePre pair-part (pullbackCone ev₁ ev₀)

  first-arrow second-arrow third-arrow : MAP ComposableTriples (Ar C)
  first-arrow = Cone.left first-pair
  second-arrow = Cone.right first-pair
  third-arrow = last-part
  x y z w : MAP ComposableTriples C
  x = ev₀ ∘ first-arrow
  y = ev₁ ∘ first-arrow
  z = ev₁ ∘ second-arrow
  w = ev₁ ∘ third-arrow
  last-matching : z =₁ (ev₀ ∘ third-arrow)
  last-matching = Cone.match (pullbackCone pair-target ev₀) ∙
    (comp-assoc pair-part second-of-pair ev₁) ⁻¹

  first : MorphismExpression x y
  first = record { arrow = first-arrow ; source-frame = idIso x ; target-frame = idIso y }
  second : MorphismExpression y z
  second = record { arrow = second-arrow
    ; source-frame = Cone.match first-pair ⁻¹ ; target-frame = idIso z }
  third : MorphismExpression z w
  third = record { arrow = third-arrow
    ; source-frame = last-matching ⁻¹ ; target-frame = idIso w }

  first-then-composite composite-then-third : MorphismExpression x w
  first-then-composite = global-compose-expression first (global-compose-expression second third)
  composite-then-third = global-compose-expression (global-compose-expression first second) third

  comparison : ExpressionIso first-then-composite composite-then-third
  comparison = global-associativity first second third

  associativity-functor : MorphismExpression.arrow first-then-composite =₁
    MorphismExpression.arrow composite-then-third
  associativity-functor = ExpressionIso.comparison comparison

  associativity-source :
    (MorphismExpression.source-frame composite-then-third ∙ (ev₀ ◁ associativity-functor)) =₂
    MorphismExpression.source-frame first-then-composite
  associativity-source = ExpressionIso.source-compatible comparison

  associativity-target :
    (MorphismExpression.target-frame composite-then-third ∙ (ev₁ ◁ associativity-functor)) =₂
    MorphismExpression.target-frame first-then-composite
  associativity-target = ExpressionIso.target-compatible comparison
```
