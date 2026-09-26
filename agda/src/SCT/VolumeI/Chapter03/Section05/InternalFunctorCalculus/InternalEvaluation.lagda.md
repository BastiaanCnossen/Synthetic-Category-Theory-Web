# The evaluation equivalence for the relative internal functor category

For `def:Relative_Functor_Category`, the universal family first pulls back
a functor and then postcomposes it with evaluation. Its triangle uses the
specified pullback matching. Currying this family defines the literal
uncurrying map on relative mapping animae.

To prove it is an equivalence, compare the whole universal family with
the composite of relative currying, projection from the pullback target,
and change of source structure. Each step retains the triangle. Thus the
comparison identifies the stipulated map, not merely its source and target.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.Section05.InternalFunctorCalculus.InternalEvaluation
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.StructureChange 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Families.Families 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Families.FamilyReflection 𝒯 M ℱ P using (reflect-family)
open import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.Evaluation 𝒯 M ℱ P using (module Curry)
open import SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.BaseChange 𝒯 M ℱ P using (module BaseChange)
open import SCT.VolumeI.Chapter03.RelativeCategories.Composition.Postcomposition 𝒯 M ℱ P using (module Postcompose)
open import SCT.VolumeI.Chapter03.Section05.Currying.PullbackTargetFamilies 𝒯 M ℱ P using (module Families)
open import SCT.VolumeI.Chapter03.Section05.Currying.SourceChangeFamilies 𝒯 M ℱ P using (module Source)
open import SCT.VolumeI.Chapter03.Section05.DependentProducts 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.Section05.InternalFunctorCalculus.RelativeInternalFunctors 𝒯 M ℱ P using (module Internal)
open import SCT.VolumeI.Chapter03.Section05.InternalFunctorCalculus.InternalProductFamily 𝒯 M ℱ P using (module Product)
open import SCT.VolumeI.Chapter03.Section05.Currying.CurryingPostcomposition 𝒯 M ℱ P using (module PostCurry; compare-curry-via)

module Evaluation {C D S : CAT} (p : MAP C S) (q : MAP D S)
  (Π : DependentProduct p (pullback₂ {f = q} {p})) where
  module Fun = Internal p q Π
  ε = Fun.ε

  module At {E : CAT} (t : MAP E S) where
    module Old = Fun.At t
    module ProductFamily = Product p q Fun.projection Fun.ε t
    module LiteralPost = Postcompose Old.source-structure ProductFamily.evaluation-triangle
    module BC = BaseChange p t Fun.projection
    module Post = Postcompose BC.f′ ε
    module Target = Old.Target
    module Structure = Old.Structure
    module Native = Families p q BC.f′
    α = pullbackMatch {f = t} {p} ⁻¹
    K = Post.functor ∘ BC.functor
    L = Target.functor ∘ K
    composite = Structure.functor ∘ L

    projected-family : FunctorOver (Old.source-structure ∘ pr₂ {C = FunOver t Fun.projection}) q
    projected-family = change-source (α ▷ pr₂) (Native.forward (compose-over ε BC.evaluated))

    evaluation-family : FunctorOver (Old.source-structure ∘ pr₂ {C = FunOver t Fun.projection}) q
    evaluation-family = ProductFamily.evaluated

    evaluation-associator : FunctorOverIso evaluation-family projected-family
    evaluation-associator = ProductFamily.comparison

    functor : MAP (FunOver t Fun.projection) (FunOver Old.source-structure q)
    functor = Curry.functor Old.source-structure q (FunctorLift.lift evaluation-family)
      (FunctorLift.comparison evaluation-family)

    curried-uncurrying : MAP (MapOver t Fun.projection) (MapOver Old.source-structure q)
    curried-uncurrying = mapPost functor

    uncurrying : MAP (MapOver t Fun.projection) (MapOver Old.source-structure q)
    uncurrying = LiteralPost.maps ∘ ProductFamily.maps

    abstract
      literal-functor-comparison : (LiteralPost.functor ∘ ProductFamily.functor) =₁ functor
      literal-functor-comparison = PostCurry.comparison
        {X = FunOver t Fun.projection} {B = Pullback t p} {C = Pullback Fun.projection p} {D = D} {S = S}
        Old.source-structure {g = Fun.structure} {h = q}
        ProductFamily.evaluation-triangle ProductFamily.family

      literal-core-comparison : uncurrying =₁ curried-uncurrying
      literal-core-comparison = PostCurry.maps-comparison
        {X = FunOver t Fun.projection} {B = Pullback t p} {C = Pullback Fun.projection p} {D = D} {S = S}
        Old.source-structure {g = Fun.structure} {h = q}
        ProductFamily.evaluation-triangle ProductFamily.family

      composite-family : FunctorOverIso (family Old.source-structure q composite) projected-family
      composite-family = compose-iso-over
        (change-source-iso (α ▷ pr₂)
          (Native.forward-identification (postwhisker-over ε BC.family-comparison)))
        (compose-iso-over (change-source-iso (α ▷ pr₂)
          (Native.forward-identification (postcompose-family BC.f′ ε BC.functor)))
          (compose-iso-over (change-source-iso (α ▷ pr₂) (Target.family-comparison K))
            (Source.substituted-comparison α q L)))

      functor-comparison : composite =₁ functor
      functor-comparison = compare-curry-via
        {X = FunOver t Fun.projection} {B = Pullback t p} {D = D} {S = S}
        Old.source-structure q composite
        evaluation-family projected-family composite-family evaluation-associator

      core-comparison : Old.uncurry =₁ mapPost composite
      core-comparison = mapPost-comp L Structure.functor ∙
        (mapPost Structure.functor ◁
          (mapPost-comp K Target.functor ∙
            (mapPost Target.functor ◁
              (mapPost-comp BC.functor Post.functor ∙
                ((mapPost Post.functor ◁ BC.maps-as-core) ∙ (Post.maps-as-core ▷ BC.maps))))))

      comparison : Old.uncurry =₁ uncurrying
      comparison = literal-core-comparison ⁻¹ ∙ (mapPost-cong functor-comparison ∙ core-comparison)

      uncurrying-isEquiv : IsEquiv uncurrying
      uncurrying-isEquiv = equiv-transport comparison Old.uncurry-isEquiv
```
