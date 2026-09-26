# Pushouts of equivalent spans

Lift the source universal cocone through the three restriction
equivalences. Its extension property follows by restricting arbitrary
cocones and reflecting their comparisons. Uniqueness then compares it
with any universal cocone on the target span. The exported comparison
retains the two specified squares of the span equivalence.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.Section06.PushoutCalculus.SpanEquivalence
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section08.Cocones 𝒯
open import SCT.VolumeI.Chapter01.Section08.CoconeCalculus.CoconePostcomposition 𝒯 using (coconePost; coconeIso-post)
open import SCT.VolumeI.Chapter01.Section08.CoconeCalculus.CoconeUniversality 𝒯 using (CoconeExtensionProperty)
open import SCT.VolumeI.Chapter03.Section04.CoconeCalculus.CoconeSpanRestriction 𝒯 using (module Restriction)
open import SCT.VolumeI.Chapter03.Section04.CoconeCalculus.CoconeRestrictionLifting 𝒯 M P using (module Lifting)
open import SCT.VolumeI.Chapter03.Section04.CoconeCalculus.CoconeRestrictionPostcomposition 𝒯 M using (module Post)
open import SCT.VolumeI.Chapter03.Section06.PushoutCalculus.PushoutUniqueness 𝒯 M ℱ P using (module Uniqueness)

module Transfer {A B C A′ B′ C′ D : CAT}
  (u : MAP A B) (v : MAP A C) (u′ : MAP A′ B′) (v′ : MAP A′ C′)
  (i : MAP A A′) (j : MAP B B′) (k : MAP C C′)
  (α : (u′ ∘ i) =₁ (j ∘ u)) (β : (v′ ∘ i) =₁ (k ∘ v))
  (ei : IsEquiv i) (ej : IsEquiv j) (ek : IsEquiv k)
  (s : Cocone u v D) (universal : CoconeExtensionProperty s) where
  module Original = CoconeExtensionProperty universal
  module Restrict = Restriction u v u′ v′ i j k α β
  module Cones (E : CAT) = Lifting u v u′ v′ i j k α β
    (mapPre-isEquiv {E = E} i ei) (mapPre-isEquiv j ej) (mapPre-isEquiv k ek)
  module Chosen = Cones.Factor D s
  abstract
    cocone : Cocone u′ v′ D
    cocone = Chosen.value
  abstract
    computation : CoconeIso (Restrict.value cocone) s
    computation = Chosen.comparison
    restriction-comparison : {E : CAT} (F : MAP D E) →
      CoconeIso (Restrict.value (coconePost F cocone)) (coconePost F s)
    restriction-comparison F = coconeIso-compose (coconeIso-post F computation)
      (Post.comparison u v u′ v′ i j k α β cocone F)
    extensions : CoconeExtensionProperty cocone
    extensions = record
      { factor = λ E q → Original.factor E (Restrict.value q)
      ; factor-β = λ E q → Cones.Compare.comparison E _ q
          (coconeIso-compose (Original.factor-β E (Restrict.value q))
            (restriction-comparison (Original.factor E (Restrict.value q))))
      ; reflect = λ E f g Φ → Original.reflect E f g
          (coconeIso-compose (restriction-comparison g)
            (coconeIso-compose (Restrict.comparison Φ) (coconeIso-inverse (restriction-comparison f)))) }

  module Into {E : CAT} (t : Cocone u′ v′ E) (target : CoconeExtensionProperty t) where
    module Unique = Uniqueness cocone t extensions target
    abstract
      forward : MAP D E
      forward = Unique.forward
      isEquiv : IsEquiv forward
      isEquiv = Unique.isEquiv
      comparison : CoconeIso (coconePost forward s) (Restrict.value t)
      comparison = coconeIso-compose (Restrict.comparison Unique.computation)
        (coconeIso-inverse (restriction-comparison forward))

module RestrictUniversal {A B C A′ B′ C′ D : CAT}
  (u : MAP A B) (v : MAP A C) (u′ : MAP A′ B′) (v′ : MAP A′ C′)
  (i : MAP A A′) (j : MAP B B′) (k : MAP C C′)
  (α : (u′ ∘ i) =₁ (j ∘ u)) (β : (v′ ∘ i) =₁ (k ∘ v))
  (ei : IsEquiv i) (ej : IsEquiv j) (ek : IsEquiv k)
  (s : Cocone u′ v′ D) (universal : CoconeExtensionProperty s) where
  module Original = CoconeExtensionProperty universal
  module Restrict = Restriction u v u′ v′ i j k α β
  module Cones (E : CAT) = Lifting u v u′ v′ i j k α β
    (mapPre-isEquiv {E = E} i ei) (mapPre-isEquiv j ej) (mapPre-isEquiv k ek)
  cocone : Cocone u v D
  cocone = Restrict.value s
  abstract
    extensions : CoconeExtensionProperty cocone
    extensions = record
      { factor = λ E q → Original.factor E (Cones.Factor.value E q)
      ; factor-β = λ E q → coconeIso-compose (Cones.Factor.comparison E q)
          (coconeIso-compose (Restrict.comparison (Original.factor-β E (Cones.Factor.value E q)))
            (coconeIso-inverse (Post.comparison u v u′ v′ i j k α β s
              (Original.factor E (Cones.Factor.value E q)))))
      ; reflect = λ E f g Φ → Original.reflect E f g (Cones.Compare.comparison E _ _
          (coconeIso-compose (coconeIso-inverse (Post.comparison u v u′ v′ i j k α β s g))
            (coconeIso-compose Φ (Post.comparison u v u′ v′ i j k α β s f)))) }
```
