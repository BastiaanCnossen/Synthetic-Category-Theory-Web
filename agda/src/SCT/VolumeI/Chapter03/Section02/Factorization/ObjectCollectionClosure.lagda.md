# Morphisms with endpoints in a collection are closed under composition

For the collection associated to a collection of objects, membership is
specified by lifts of the two endpoints. Source and target identities
use the same object twice. The composite uses the first source and the
second target. These are the two claims in `def:Collection_Of_Objects`.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section02.SegalAxiom as Segal

module SCT.VolumeI.Chapter03.Section02.Factorization.ObjectCollectionClosure
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open Mapping.MappingAnimae M
open Pullbacks.PullbackStructure P
open Walking.WalkingMorphism I
open import SCT.VolumeI.Chapter01.Section04.Functoriality 𝒯 M using (mapPre; mapPre-comp; mapPre-cong)
open import SCT.VolumeI.Chapter01.Section04.Composition 𝒯 M using (productMap-pair)
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯 using (Cone)
open import SCT.VolumeI.Chapter03.Section01.ClosureCalculus.CompositionClosure 𝒯 M ℱ P I E S
  using (ClosedUnderComposition; ClosedUnderIdentities; module ComposableIn)
open import SCT.VolumeI.Chapter03.Section02.ObjectCollections 𝒯 M P I
  using (ObjectCollection; endpoints; module SpannedMorphisms)

module Closure {C : CAT} (V : ObjectCollection C) where
  open ObjectCollection V renaming (collection to X; inclusion to j)
  open SpannedMorphisms V
  W = collectionOfMorphisms
  u = morphisms-inclusion
  objects = pullback₂ {f = endpoints C} {productMap j j}
  sourceObject = pr₁ ∘ objects
  targetObject = pr₂ ∘ objects

  source-frame : (mapPre zero ∘ u) =₁ (j ∘ sourceObject)
  source-frame = comp-assoc objects pr₁ j ∙
    (project-pair₁ (j ∘ pr₁) (j ∘ pr₂) objects ∙
      ((pr₁ ◁ pullbackMatch) ∙ (project-pair₁ (mapPre zero) (mapPre one) u) ⁻¹))

  target-frame : (mapPre one ∘ u) =₁ (j ∘ targetObject)
  target-frame = comp-assoc objects pr₂ j ∙
    (project-pair₂ (j ∘ pr₁) (j ∘ pr₂) objects ∙
      ((pr₂ ◁ pullbackMatch) ∙ (project-pair₂ (mapPre zero) (mapPre one) u) ⁻¹))

  lift-endpoints : {Γ : CAT} (f : MAP Γ (Map [1] C)) (x y : MAP Γ X) →
    (mapPre zero ∘ f) =₁ (j ∘ x) → (mapPre one ∘ f) =₁ (j ∘ y) → FunctorLift u f
  lift-endpoints f x y α β = record { lift = pullbackLift cone ; comparison = pullbackLift-β₁ cone }
    where
    cone : Cone (endpoints C) (productMap j j) _
    cone = record { left = f ; right = pair x y
      ; match = (productMap-pair j j x y) ⁻¹ ∙
          (pair-cong α β ∙ pair-pre (mapPre zero) (mapPre one) f) }

  identity-endpoint : (x v : Obj-abs [1]) →
    (mapPre v ∘ (mapPre (const x) ∘ u)) =₁ (mapPre x ∘ u)
  identity-endpoint x v = (mapPre-cong (const-evaluate x v) ▷ u) ∙
    ((mapPre-comp v (const x) ▷ u) ∙ (comp-assoc u (mapPre (const x)) (mapPre v)) ⁻¹)

  identities : ClosedUnderIdentities W
  identities = record
    { source-identity = lift-endpoints (mapPre (const zero) ∘ u) sourceObject sourceObject
        (source-frame ∙ identity-endpoint zero zero) (source-frame ∙ identity-endpoint zero one)
    ; target-identity = lift-endpoints (mapPre (const one) ∘ u) targetObject targetObject
        (target-frame ∙ identity-endpoint one zero) (target-frame ∙ identity-endpoint one one) }

  composition-lift : FunctorLift u (ComposableIn.composite W)
  composition-lift = lift-endpoints (ComposableIn.composite W)
    (sourceObject ∘ pullback₁) (targetObject ∘ pullback₂)
    (comp-assoc pullback₁ sourceObject j ∙ ((source-frame ▷ pullback₁) ∙ ComposableIn.composite-source W))
    (comp-assoc pullback₂ targetObject j ∙ ((target-frame ▷ pullback₂) ∙ ComposableIn.composite-target W))

  closed : ClosedUnderComposition W
  closed = record { identities = identities ; composition = composition-lift }

object-collection-morphisms-closed : {C : CAT} (V : ObjectCollection C) →
  ClosedUnderComposition (SpannedMorphisms.collectionOfMorphisms V)
object-collection-morphisms-closed = Closure.closed
```
