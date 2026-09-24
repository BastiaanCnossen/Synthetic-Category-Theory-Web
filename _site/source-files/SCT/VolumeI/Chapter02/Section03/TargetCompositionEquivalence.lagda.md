# Composition with an invertible arrow is an equivalence

The left and right inverse triangles supply a retraction and a section
of composition on arrows ending at the source. They need not use the
same inverse. The resulting functor retains its projection to the base.

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

module SCT.VolumeI.Chapter02.Section03.TargetCompositionEquivalence
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section03.ExpressionParameterChanges 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open Laws.PullbackStructure P
open import SCT.VolumeI.Chapter02.Section03.ConeOperations 𝒯 P using (ConeOperation; module Realize; module Inverse)
open import SCT.VolumeI.Chapter02.Section03.UniversalInverseExpressions 𝒯 M ℱ P I E S using (IsInvertibleExpression)
import SCT.VolumeI.Chapter02.Section03.TargetCompositionCones as Actions
import SCT.VolumeI.Chapter02.Section03.TargetCompositionInverse as Cancellation

operation : {B C : CAT} {x y : MAP B C} → MorphismExpression x y →
  ConeOperation (ev₁ {C}) x ev₁ y
operation f = record { act = F.act ; compare = F.Compared.comparison ; restrict = F.Restriction.comparison }
  where module F = Actions.Action 𝒯 M ℱ P I E S f

module At {B C : CAT} {x y : MAP B C} (f : MorphismExpression x y) where
  private
    module F = Realize (operation f)

  compose-at-target : MAP (Pullback (ev₁ {C}) x) (Pullback (ev₁ {C}) y)
  compose-at-target = F.map

  compose-at-target-base : (pullback₂ ∘ compose-at-target) =₁ (pullback₂ {f = ev₁ {C}} {x})
  compose-at-target-base = pullbackLift-β₂ (ConeOperation.act (operation f) (pullbackCone ev₁ x))

  compose-at-target-isEquiv : IsInvertibleExpression f → IsEquiv compose-at-target
  compose-at-target-isEquiv witness = section-retraction-isEquiv
    (record { section = G.map ; comparison = Right.inverse-comparison })
    (record { retraction = H.map ; comparison = Left.inverse-comparison ⁻¹ })
    where
    module W = IsInvertibleExpression witness
    module G = Realize (operation W.right-inverse)
    module H = Realize (operation W.left-inverse)
    module Right = Inverse (operation W.right-inverse) (operation f)
      (Cancellation.Inverse.inverse-law 𝒯 M ℱ P I E S Q W.right-inverse f W.right-inverse-law)
    module Left = Inverse (operation f) (operation W.left-inverse)
      (Cancellation.Inverse.inverse-law 𝒯 M ℱ P I E S Q f W.left-inverse W.left-inverse-law)
```
