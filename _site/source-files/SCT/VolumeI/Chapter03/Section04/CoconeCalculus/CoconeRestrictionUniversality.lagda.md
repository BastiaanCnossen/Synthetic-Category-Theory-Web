# Transferring cocone extension along restriction

A compatible map of squares compares their extension problems. If the
four restrictions into a fixed target are equivalences, extension for
the original cocone gives extension for the new one. Reflection of
extensions only needs reflection along the fourth restriction.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.Section04.CoconeCalculus.CoconeRestrictionUniversality
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section08.Cocones 𝒯
open import SCT.VolumeI.Chapter01.Section08.CoconeCalculus.CoconePostcomposition 𝒯 using (coconePost; coconeIso-post; cocone-action)
open import SCT.VolumeI.Chapter01.Section08.CoconeCalculus.CoconeUniversality 𝒯 using (CoconeExtensionProperty)
open import SCT.VolumeI.Chapter03.Section04.CoconeCalculus.CoconeSpanRestriction 𝒯 using (module Restriction)
open import SCT.VolumeI.Chapter03.Section04.CoconeCalculus.CoconeRestrictionLifting 𝒯 M P using (module Lifting; module FunctorFactor)
open import SCT.VolumeI.Chapter03.Section04.CoconeCalculus.CoconeRestrictionPostcomposition 𝒯 M using (module Post)
open import SCT.VolumeI.Chapter03.Section04.CoconeCalculus.CoconePostAssociativity 𝒯 M using (coconePost-assoc)

module Transfer {A B C A′ B′ C′ D D′ : CAT}
  (u : MAP A B) (v : MAP A C) (u′ : MAP A′ B′) (v′ : MAP A′ C′)
  (i : MAP A A′) (j : MAP B B′) (k : MAP C C′)
  (α : (u′ ∘ i) =₁ (j ∘ u)) (β : (v′ ∘ i) =₁ (k ∘ v))
  (s : Cocone u v D) (t : Cocone u′ v′ D′) (d : MAP D D′)
  (extensions : CoconeExtensionProperty s)
  (square-comparison : CoconeIso (Restriction.value u v u′ v′ i j k α β t) (coconePost d s)) where
  module Restrict = Restriction u v u′ v′ i j k α β

  abstract
    post-comparison : {E : CAT} (F : MAP D′ E) →
      CoconeIso (Restrict.value (coconePost F t)) (coconePost (F ∘ d) s)
    post-comparison F = coconeIso-compose (coconeIso-inverse (coconePost-assoc s d F))
      (coconeIso-compose (coconeIso-post F square-comparison) (Post.comparison u v u′ v′ i j k α β t F))

  module At (E : CAT) (ei : IsEquiv (mapPre {D = E} i))
    (ej : IsEquiv (mapPre {D = E} j)) (ek : IsEquiv (mapPre {D = E} k))
    (ed : IsEquiv (mapPre {D = E} d)) where
    module Cones = Lifting u v u′ v′ i j k α β ei ej ek
    module Factor (q : Cocone u′ v′ E) where
      old = CoconeExtensionProperty.factor extensions E (Restrict.value q)
      module Chosen = FunctorFactor d ed old
      abstract
        functor : MAP D′ E
        functor = Chosen.functor

        restricted-comparison : CoconeIso (Restrict.value (coconePost functor t)) (Restrict.value q)
        restricted-comparison = coconeIso-compose (CoconeExtensionProperty.factor-β extensions E (Restrict.value q))
          (coconeIso-compose (cocone-action s Chosen.comparison) (post-comparison functor))

        comparison : CoconeIso (coconePost functor t) q
        comparison = Cones.Compare.comparison (coconePost functor t) q restricted-comparison

  abstract
    reflect : {E : CAT} →
      ((F G : MAP D′ E) → (F ∘ d) =₁ (G ∘ d) → F =₁ G) →
      (F G : MAP D′ E) → CoconeIso (coconePost F t) (coconePost G t) → F =₁ G
    reflect reflection F G Φ = reflection F G
      (CoconeExtensionProperty.reflect extensions _ (F ∘ d) (G ∘ d)
        (coconeIso-compose (post-comparison G)
          (coconeIso-compose (Restrict.comparison Φ) (coconeIso-inverse (post-comparison F)))))
```
