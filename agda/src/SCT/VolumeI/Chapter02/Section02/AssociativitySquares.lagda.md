# The two squares for associativity

The first square has top edge `f`, right edge `g`, left edge the identity,
and bottom edge the composite of `f` and `g`. The second has top edge
the composite of `g` and `h`, right edge the identity, left edge `g`,
and bottom edge `h`. Each comes with both triangle presentations and
the comparison along its diagonal, provided by `First` and `Second`.

Here we glue a chosen composite triangle to a unit triangle. This realizes
the boundary diagrams used in the manuscript without identifying the
result with the square obtained from its particular retraction.
`ExpressionAssociativity` composes the resulting framed squares and
uses the unit laws to prove associativity.

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

module SCT.VolumeI.Chapter02.Section02.AssociativitySquares
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section02.GluedCompositePresentations 𝒯 M ℱ P I E S Q
open import SCT.VolumeI.Chapter02.Section02.ExpressionUnitLaws 𝒯 M ℱ P I E S using (left-unit; right-unit)

module At {Γ C : CAT} {x y z w : MAP Γ C}
  (f : MorphismExpression x y) (g : MorphismExpression y z) (h : MorphismExpression z w) where

  first-composite = compose-expression f g
  second-composite = compose-expression g h

  module First = Glue (composition-presentation f g)
    (change-long (composition-presentation (identity-expression x) first-composite)
      (left-unit first-composite))

  module Second = Glue
    (change-long (composition-presentation second-composite (identity-expression w))
      (right-unit second-composite))
    (composition-presentation g h)

  first-square : MAP Γ (Fun ([1] × [1]) C)
  first-square = First.square

  second-square : MAP Γ (Fun ([1] × [1]) C)
  second-square = Second.square
```
