# Lifting a family one summand at a time

A family of maps out of a coproduct factors through a given functor if
its two restrictions do. This uses the actual coproduct restriction
equivalence on mapping animae. It is useful when checking membership on
the three endomorphisms of the walking morphism.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section05.Coproducts as Coproducts

module SCT.VolumeI.Chapter03.Section01.Lifting.CoproductLifting
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (B : Coproducts.CoproductStructure 𝒯 M) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open Mapping.MappingAnimae M
open Coproducts.CoproductStructure B
open import SCT.VolumeI.Chapter01.Section04.Currying 𝒯 M
open import SCT.VolumeI.Chapter01.Section04.Functoriality 𝒯 M
open import SCT.VolumeI.Chapter01.Section04.Composition 𝒯 M using (productMap-pair)

open import SCT.VolumeI.Chapter03.Section01.MappingCalculus.MappingCommutation 𝒯 M public using (mapPre-mapPost)

restriction-post : {C D X Y : CAT} (m : MAP X Y) →
  (coproductRestriction C D Y ∘ mapPost m) =₁
    (productMap (mapPost m) (mapPost m) ∘ coproductRestriction C D X)
restriction-post {C} {D} {X} m =
  (productMap-pair (mapPost m) (mapPost m) (mapPre in₁) (mapPre in₂)) ⁻¹ ∙
    (pair-cong (mapPre-mapPost in₁ m) (mapPre-mapPost in₂ m) ∙
      pair-pre (mapPre in₁) (mapPre in₂) (mapPost m))

module Lift {Γ C D X Y : CAT} (m : MAP X Y) (h : MAP Γ (Map (C ⊔ D) Y))
  (left : FunctorLift (mapPost m) (mapPre in₁ ∘ h))
  (right : FunctorLift (mapPost m) (mapPre in₂ ∘ h)) where

  chosen = equiv-lift (coproductRestriction-isEquiv C D X)
    (pair (FunctorLift.lift left) (FunctorLift.lift right))

  lift : MAP Γ (Map (C ⊔ D) X)
  lift = FunctorLift.lift chosen

  comparison : (mapPost m ∘ lift) =₁ h
  comparison = equiv-reflect (coproductRestriction-isEquiv C D Y) _ _
    ((pair-pre (mapPre in₁) (mapPre in₂) h) ⁻¹ ∙
      (pair-cong (FunctorLift.comparison left) (FunctorLift.comparison right) ∙
        (productMap-pair (mapPost m) (mapPost m) (FunctorLift.lift left) (FunctorLift.lift right) ∙
          ((productMap (mapPost m) (mapPost m) ◁ FunctorLift.comparison chosen) ∙
            (comp-assoc lift (coproductRestriction C D X) (productMap (mapPost m) (mapPost m)) ∙
              ((restriction-post m ▷ lift) ∙ (comp-assoc lift (mapPost m) (coproductRestriction C D Y)) ⁻¹))))))

  factorization : FunctorLift (mapPost m) h
  factorization = record { lift = lift ; comparison = comparison }

lift-coproduct : {Γ C D X Y : CAT} (m : MAP X Y) (h : MAP Γ (Map (C ⊔ D) Y)) →
  FunctorLift (mapPost m) (mapPre in₁ ∘ h) →
  FunctorLift (mapPost m) (mapPre in₂ ∘ h) → FunctorLift (mapPost m) h
lift-coproduct = Lift.factorization
```
