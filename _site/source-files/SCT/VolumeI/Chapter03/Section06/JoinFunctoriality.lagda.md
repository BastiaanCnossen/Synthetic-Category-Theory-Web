# Functoriality of joins

For `con:Functoriality_Of_Joins`, functors on the two summands induce a
functor on their join. We use the mapping-in universal property: copair
the two functors over the boundary and apply functoriality of dependent
products. This proves the identity and composition laws with their
height triangles retained.

The auxiliary boundary presentation uses constant maps at its two
points. Its displayed comparison with `Boundary.projection` transports
the original join dependent product; the chosen join and height remain
the ones supplied by the axioms. `JoinFunctorBoundary` proves the two
summand restrictions. Agreement with the cylinder formula in the
mapping-out construction is a separate computation.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section05.Coproducts as Coproducts
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section06.UniversalCoproducts as Universality
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Interval
import SCT.VolumeI.Chapter03.Section06.JoinAxiom as Axiom

module SCT.VolumeI.Chapter03.Section06.JoinFunctoriality
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M)
  (B : Coproducts.CoproductStructure 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯)
  (U : Universality.CoproductUniversality 𝒯 M B P)
  (I : Interval.WalkingMorphism 𝒯) (J : Axiom.JoinAxiom 𝒯 M ℱ B P U I) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M hiding (_⋆_)
open Coproducts.CoproductStructure B
open import SCT.VolumeI.Chapter01.Section05.Copairing 𝒯 M B
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.Section05.DependentProducts 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.Section05.BaseChange.DependentProductTargetTransport 𝒯 M ℱ P using (module Transport)
open import SCT.VolumeI.Chapter03.Section05.DependentProductAction 𝒯 M ℱ P using (module Induced)
import SCT.VolumeI.Chapter03.Section05.DependentProductActionLaws as DependentLaws
import SCT.VolumeI.Chapter03.Section05.ProductCalculus.DependentProductActionIdentifications as ProductIdentifications
import SCT.VolumeI.Chapter03.RelativeCategories.Coproducts as Sums
import SCT.VolumeI.Chapter03.Section05.Currying.ConstantBaseFunctoriality as Constants
open import SCT.VolumeI.Chapter03.Section06.PushoutCalculus.JoinSpan 𝒯 M B P U I using (∂[1])
open import SCT.VolumeI.Chapter03.Section06.BoundaryCalculus.JoinBoundary 𝒯 M B P U I using (weakened-boundary; module Boundary)
open import SCT.VolumeI.Chapter03.Section06.Joins 𝒯 M ℱ B P U I J using (_⋆_; join-dependent-product)
open Axiom 𝒯 M ℱ B P U I
open JoinAxiom J using (height)
module Sum = Sums 𝒯 M ℱ P B
module Laws = DependentLaws 𝒯 M ℱ P
module Identifications = ProductIdentifications 𝒯 M ℱ P

point₀ point₁ : Obj-abs (One × ∂[1])
point₀ = pair (id One) in₁
point₁ = pair (id One) in₂
module Left = Constants.At 𝒯 M ℱ P point₀
module Right = Constants.At 𝒯 M ℱ P point₁

module Presentation (C D : CAT) where
  projection : MAP (C ⊔ D) (One × ∂[1])
  projection = copair (const point₀) (const point₁)
  original = Boundary.projection (terminate C) (terminate D)
  abstract
    endpoint : {X : CAT} (i : MAP One ∂[1]) →
      const {P = X} (pair (id One) i) =₁ pair (terminate X) (const i)
    endpoint {X} i = pair-cong (comp-unitˡ (terminate X)) (idIso (const i)) ∙
      pair-pre (id One) i (terminate X)
    comparison : projection =₁ original
    comparison = copair-cong (endpoint in₁) (endpoint in₂)
  over : FunctorOver original projection
  over = record { lift = id (C ⊔ D) ; comparison = comparison ∙ comp-unitʳ projection }
  dependent-product : DependentProduct (weakened-boundary One) projection
  dependent-product = Transport.dependent-product (weakened-boundary One) original projection
    over (id-isEquiv (C ⊔ D)) (join-dependent-product (terminate C) (terminate D))

module Action {C D C′ D′ : CAT} (f : MAP C C′) (g : MAP D D′) where
  module Source = Presentation C D
  module Target = Presentation C′ D′
  boundary-over = Sum.Action.over (Left.over f) (Right.over g)
  module Chosen = Induced (weakened-boundary One) Source.projection Target.projection
    Source.dependent-product Target.dependent-product boundary-over
  over = Chosen.over
  functor : MAP (C ⋆ D) (C′ ⋆ D′)
  functor = Chosen.functor
  height-comparison : (height (terminate C′) (terminate D′) ∘ functor) =₁
    height (terminate C) (terminate D)
  height-comparison = Chosen.triangle

joinMap : {C D C′ D′ : CAT} → MAP C C′ → MAP D D′ → MAP (C ⋆ D) (C′ ⋆ D′)
joinMap = Action.functor

module Identity (C D : CAT) where
  module Source = Presentation C D
  module A = Action (id C) (id D)
  abstract
    boundary-comparison : FunctorOverIso A.boundary-over (identity-over Source.projection)
    boundary-comparison = compose-iso-over (Sum.Identity.comparison (const point₀) (const point₁))
      (Sum.Identification.comparison (Left.identity C) (Right.identity D))
    over : FunctorOverIso A.over (identity-over (height (terminate C) (terminate D)))
    over = compose-iso-over (Laws.Action.identity (weakened-boundary One) Source.projection Source.dependent-product)
      (Identifications.Identification.comparison (weakened-boundary One) Source.projection Source.projection
        Source.dependent-product Source.dependent-product boundary-comparison)
    comparison : joinMap (id C) (id D) =₁ id (C ⋆ D)
    comparison = FunctorOverIso.underlying over

module Composite {C D C′ D′ C″ D″ : CAT}
  (f : MAP C C′) (f′ : MAP C′ C″) (g : MAP D D′) (g′ : MAP D′ D″) where
  module Source = Presentation C D
  module Middle = Presentation C′ D′
  module Target = Presentation C″ D″
  module A = Action f g
  module B = Action f′ g′
  module CompositeAction = Action (f′ ∘ f) (g′ ∘ g)
  abstract
    boundary-comparison : FunctorOverIso (compose-over B.boundary-over A.boundary-over) CompositeAction.boundary-over
    boundary-comparison = compose-iso-over
      (Sum.Identification.comparison (Left.composite f f′) (Right.composite g g′))
      (Sum.Composite.comparison (Left.over f) (Right.over g) (Left.over f′) (Right.over g′))
    over : FunctorOverIso (compose-over B.over A.over) CompositeAction.over
    over = compose-iso-over
      (Identifications.Identification.comparison (weakened-boundary One) Source.projection Target.projection
        Source.dependent-product Target.dependent-product boundary-comparison)
      (Laws.Action.Composite.comparison (weakened-boundary One)
        Source.projection Middle.projection Target.projection
        Source.dependent-product Middle.dependent-product Target.dependent-product
        A.boundary-over B.boundary-over)
    comparison : (joinMap f′ g′ ∘ joinMap f g) =₁ joinMap (f′ ∘ f) (g′ ∘ g)
    comparison = FunctorOverIso.underlying over
```
