# The functor induced on a join pushout

Apply the product of the two functors to the cylinder and their
coproduct to the boundary. The two attaching squares are lifted with their specified restrictions
to each summand. They define a map of spans, so the source pushout extends the resulting cocone. Its beta
comparison retains both restrictions and their common matching.

This is the mapping-out construction in `con:Functoriality_Of_Joins`.
The mapping-in construction in `JoinFunctoriality` is separate; an
identification between the two constructions is not asserted here.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import Agda.Builtin.Nat using (Nat; suc) renaming (zero to zeroℕ)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section05.Coproducts as Coproducts
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section06.UniversalCoproducts as Universality
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Interval
import SCT.VolumeI.Chapter03.Section06.JoinAxiom as Axiom

module SCT.VolumeI.Chapter03.Section06.JoinPushoutAction
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M)
  (B : Coproducts.CoproductStructure 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯)
  (U : Universality.CoproductUniversality 𝒯 M B P)
  (I : Interval.WalkingMorphism 𝒯) (J : Axiom.JoinAxiom 𝒯 M ℱ B P U I) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M hiding (_⋆_)
open Coproducts.CoproductStructure B
open Interval.WalkingMorphism I
open import SCT.VolumeI.Chapter01.Section05.CoproductCalculus 𝒯 M B
open import SCT.VolumeI.Chapter01.Section05.IsomorphismRestriction 𝒯 M B using (module RestrictionLift)
open import SCT.VolumeI.Chapter01.Section05.RestrictionCalculus 𝒯 using (pair-after)
open import SCT.VolumeI.Chapter01.Section08.Cocones 𝒯
open import SCT.VolumeI.Chapter01.Section08.CoconeCalculus.CoconePostcomposition 𝒯 using (coconePost)
open import SCT.VolumeI.Chapter01.Section08.CoconeCalculus.CoconeUniversality 𝒯 using (CoconeExtensionProperty)
open import SCT.VolumeI.Chapter03.Section04.CoconeCalculus.CoconeSpanRestriction 𝒯 using (module Restriction)
open import SCT.VolumeI.Chapter03.Section06.PushoutCalculus.JoinSpanCoordinates 𝒯 M ℱ B P U I J using (insert)
open import SCT.VolumeI.Chapter03.Section06.PushoutCalculus.NormalizedJoinPushout 𝒯 M ℱ B P U I J using (module Normalized)
open import SCT.VolumeI.Chapter03.Section06.Joins 𝒯 M ℱ B P U I J using (_⋆_)

module Action {C D C′ D′ : CAT} (f : MAP C C′) (g : MAP D D′) where
  module Source = Normalized C D using (top; bottom; cylinder; boundary; cocone; extensions)
  module Target = Normalized C′ D′ using (top; bottom; cylinder; boundary; cocone)
  product = productMap f g
  doubled = coproductMap product product
  cylinder = productMap product (id [1])
  boundary = coproductMap f g
  abstract
    insert-comparison : (e : Obj-abs [1]) → (insert e ∘ product) =₁ (cylinder ∘ insert e)
    insert-comparison e =
      (pair-cong (comp-unitʳ product) (comp-unitˡ (const e)) ∙ pair-after product (id [1]) (id (C × D)) (const e)) ⁻¹ ∙
      (pair-cong (comp-unitˡ product) (const-pre e product) ∙ pair-pre (id (C′ × D′)) (const e) product)
    bottom-first : ((in₁ ∘ pr₁) ∘ product) =₁ (boundary ∘ (in₁ ∘ pr₁))
    bottom-first = (copair-pre₁ (in₁ ∘ f) (in₂ ∘ g) pr₁) ⁻¹ ∙
      ((comp-assoc pr₁ f in₁) ⁻¹ ∙
        ((in₁ ◁ pair-β₁ (f ∘ pr₁) (g ∘ pr₂)) ∙ comp-assoc product pr₁ in₁))
    bottom-second : ((in₂ ∘ pr₂) ∘ product) =₁ (boundary ∘ (in₂ ∘ pr₂))
    bottom-second = (copair-pre₂ (in₁ ∘ f) (in₂ ∘ g) pr₂) ⁻¹ ∙
      ((comp-assoc pr₂ g in₂) ⁻¹ ∙
        ((in₂ ◁ pair-β₂ (f ∘ pr₁) (g ∘ pr₂)) ∙ comp-assoc product pr₂ in₂))
    top-first : ((Target.top ∘ doubled) ∘ in₁) =₁ ((cylinder ∘ Source.top) ∘ in₁)
    top-first = (comp-assoc in₁ Source.top cylinder) ⁻¹ ∙
      ((cylinder ◁ (copair-β₁ (insert zero) (insert one)) ⁻¹) ∙
        (insert-comparison zero ∙
          (copair-pre₁ (insert zero) (insert one) product ∙
            ((Target.top ◁ copair-β₁ (in₁ ∘ product) (in₂ ∘ product)) ∙
              comp-assoc in₁ doubled Target.top))))
    top-second : ((Target.top ∘ doubled) ∘ in₂) =₁ ((cylinder ∘ Source.top) ∘ in₂)
    top-second = (comp-assoc in₂ Source.top cylinder) ⁻¹ ∙
      ((cylinder ◁ (copair-β₂ (insert zero) (insert one)) ⁻¹) ∙
        (insert-comparison one ∙
          (copair-pre₂ (insert zero) (insert one) product ∙
            ((Target.top ◁ copair-β₂ (in₁ ∘ product) (in₂ ∘ product)) ∙
              comp-assoc in₂ doubled Target.top))))
    bottom-first-restriction : ((Target.bottom ∘ doubled) ∘ in₁) =₁ ((boundary ∘ Source.bottom) ∘ in₁)
    bottom-first-restriction = (comp-assoc in₁ Source.bottom boundary) ⁻¹ ∙
      ((boundary ◁ (copair-β₁ (in₁ ∘ pr₁) (in₂ ∘ pr₂)) ⁻¹) ∙
        (bottom-first ∙
          (copair-pre₁ (in₁ ∘ pr₁) (in₂ ∘ pr₂) product ∙
            ((Target.bottom ◁ copair-β₁ (in₁ ∘ product) (in₂ ∘ product)) ∙
              comp-assoc in₁ doubled Target.bottom))))
    bottom-second-restriction : ((Target.bottom ∘ doubled) ∘ in₂) =₁ ((boundary ∘ Source.bottom) ∘ in₂)
    bottom-second-restriction = (comp-assoc in₂ Source.bottom boundary) ⁻¹ ∙
      ((boundary ◁ (copair-β₂ (in₁ ∘ pr₁) (in₂ ∘ pr₂)) ⁻¹) ∙
        (bottom-second ∙
          (copair-pre₂ (in₁ ∘ pr₁) (in₂ ∘ pr₂) product ∙
            ((Target.bottom ◁ copair-β₂ (in₁ ∘ product) (in₂ ∘ product)) ∙
              comp-assoc in₂ doubled Target.bottom))))
  module Top = RestrictionLift (Target.top ∘ doubled) (cylinder ∘ Source.top)
    top-first top-second using (lift; left-image; right-image)
  module Bottom = RestrictionLift (Target.bottom ∘ doubled) (boundary ∘ Source.bottom)
    bottom-first-restriction bottom-second-restriction using (lift; left-image; right-image)
  open Top public using () renaming
    (lift to top-comparison; left-image to top-first-image; right-image to top-second-image)
  open Bottom public using () renaming
    (lift to bottom-comparison; left-image to bottom-first-image; right-image to bottom-second-image)
  module Changed = Restriction Source.top Source.bottom Target.top Target.bottom
    doubled cylinder boundary top-comparison bottom-comparison using (value)
  cocone : Cocone Source.top Source.bottom (C′ ⋆ D′)
  cocone = Changed.value Target.cocone
  module Universal = CoconeExtensionProperty Source.extensions using (factor; factor-β)
  functor : MAP (C ⋆ D) (C′ ⋆ D′)
  functor = Universal.factor (C′ ⋆ D′) cocone
  abstract
    comparison : CoconeIso (coconePost functor Source.cocone) cocone
    comparison = Universal.factor-β (C′ ⋆ D′) cocone
    cylinder-comparison : (functor ∘ Source.cylinder) =₁ (Target.cylinder ∘ cylinder)
    cylinder-comparison = CoconeIso.leftIso comparison
    boundary-comparison : (functor ∘ Source.boundary) =₁ (Target.boundary ∘ boundary)
    boundary-comparison = CoconeIso.rightIso comparison
```
