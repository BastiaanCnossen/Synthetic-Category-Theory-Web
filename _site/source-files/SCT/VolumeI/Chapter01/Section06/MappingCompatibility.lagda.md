# Uncurrying and postcomposition

The postcomposition comparison is natural on the whole isomorphism anima.
This is the compatibility needed to uncurry a cone comparison.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section05.Setup as Setup
import SCT.VolumeI.Chapter01.Section03.FamilyProductFunctor as FamilyProduct
import SCT.VolumeI.Chapter01.Section03.Parameterized as Parameterized
import SCT.VolumeI.Chapter01.Section03.FamilyNaturality as FamilyNaturality

module SCT.VolumeI.Chapter01.Section06.MappingCompatibility
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section04.Compatibility 𝒯 M
open FamilyProduct vocabulary terminal products productLaws composition vertical whiskering
  using (productFamily; paste-family-squares)
open Parameterized.WhiskeringLaws vocabulary terminal products productLaws composition vertical whiskering
  using (postWhisker-comp-general)
open FamilyNaturality vocabulary terminal products productLaws composition vertical whiskering
  using (family-interchange-fixedOuter)

mapPost-uncurry-inputs : {A X T C D : CAT} (f : MAP C D)
  {u v : MAP X (Map T C)} (γ : MAP A (u ＝ v)) →
  (const (mapPost-uncurry f v) ∙ uncurryFamily (mapPost f ◁ γ)) =₁
    ((f ◁ uncurryFamily γ) ∙ const (mapPost-uncurry f u))
mapPost-uncurry-inputs {T = T} f {u} {v} γ =
  paste-family-squares (βu ∙ αu) (βv ∙ αv) δu δv action₀ action₂ action₃
    (paste-family-squares αu αv βu βv action₀ action₁ action₂
      (uncurry-restrict-substitution (mapPost f) γ)
      (family-interchange-fixedOuter (mapPost-β f) pγ))
    (postWhisker-comp-general pγ mapEval f)
  where
  pu = productMap u (id T)
  pv = productMap v (id T)
  pγ = productFamily γ (const (idIso (id T)))
  αu = mapUncurry-restrict (mapPost f) u
  αv = mapUncurry-restrict (mapPost f) v
  βu = mapPost-β f ▷ pu
  βv = mapPost-β f ▷ pv
  δu = comp-assoc pu mapEval f
  δv = comp-assoc pv mapEval f
  action₀ = uncurryFamily (mapPost f ◁ γ)
  action₁ = mapUncurry (mapPost f) ◁ pγ
  action₂ = (f ∘ mapEval) ◁ pγ
  action₃ = f ◁ uncurryFamily γ

mapPost-uncurry-natural : {X T C D : CAT} (f : MAP C D)
  {u v : MAP X (Map T C)} (γ : u =₁ v) →
  (mapPost-uncurry f v ∙ mapUncurryIso (mapPost f ◁ γ)) =₂
    ((f ◁ mapUncurryIso γ) ∙ mapPost-uncurry f u)
mapPost-uncurry-natural f {u} {v} γ =
  isoComp-cong (postWhisker f ◁ uncurryFamily-absolute γ) (const-One (mapPost-uncurry f u)) ∙
    (mapPost-uncurry-inputs f γ ∙
      (isoComp-cong (const-One (mapPost-uncurry f v)) (uncurryFamily-absolute (mapPost f ◁ γ))) ⁻¹)
```
