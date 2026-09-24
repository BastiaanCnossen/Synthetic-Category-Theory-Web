# Uncurrying and postcomposition

The postcomposition comparison is natural on the whole isomorphism anima.
This is the compatibility needed to uncurry a cone comparison.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.Setup as Setup
import SCT.VolumeI.Chapter01.Section03.FamilyProductFunctor as FamilyProduct
import SCT.VolumeI.Chapter01.Section03.Parameterized as Parameterized
import SCT.VolumeI.Chapter01.Section03.FamilyNaturality as FamilyNaturality

import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories

module SCT.VolumeI.Chapter01.Section07.MappingCompatibility
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) (ℱ : Categories.FunctorCategories 𝒯 M) where

open Setup 𝒯 M ℱ
open FamilyProduct vocabulary terminal products productLaws composition vertical whiskering
  using (productFamily; paste-family-squares)
open Parameterized.WhiskeringLaws vocabulary terminal products productLaws composition vertical whiskering
  using (postWhisker-comp-general)
open FamilyNaturality vocabulary terminal products productLaws composition vertical whiskering
  using (family-interchange-fixedOuter)

funPost-uncurry-inputs : {A X T C D : CAT} (f : MAP C D)
  {u v : MAP X (Fun T C)} (γ : MAP A (u ＝ v)) →
  (const (funPost-uncurry f v) ∙ uncurryFamily (funPost f ◁ γ)) =₁
    ((f ◁ uncurryFamily γ) ∙ const (funPost-uncurry f u))
funPost-uncurry-inputs {T = T} f {u} {v} γ =
  paste-family-squares (βu ∙ αu) (βv ∙ αv) δu δv action₀ action₂ action₃
    (paste-family-squares αu αv βu βv action₀ action₁ action₂
      (uncurry-restrict-substitution (funPost f) γ)
      (family-interchange-fixedOuter (funPost-β f) pγ))
    (postWhisker-comp-general pγ funEval f)
  where
  pu = productMap u (id T)
  pv = productMap v (id T)
  pγ = productFamily γ (const (idIso (id T)))
  αu = funUncurry-restrict (funPost f) u
  αv = funUncurry-restrict (funPost f) v
  βu = funPost-β f ▷ pu
  βv = funPost-β f ▷ pv
  δu = comp-assoc pu funEval f
  δv = comp-assoc pv funEval f
  action₀ = uncurryFamily (funPost f ◁ γ)
  action₁ = funUncurry (funPost f) ◁ pγ
  action₂ = (f ∘ funEval) ◁ pγ
  action₃ = f ◁ uncurryFamily γ

funPost-uncurry-natural : {X T C D : CAT} (f : MAP C D)
  {u v : MAP X (Fun T C)} (γ : u =₁ v) →
  (funPost-uncurry f v ∙ funUncurryIso (funPost f ◁ γ)) =₂
    ((f ◁ funUncurryIso γ) ∙ funPost-uncurry f u)
funPost-uncurry-natural f {u} {v} γ =
  isoComp-cong (postWhisker f ◁ uncurryFamily-absolute γ) (const-One (funPost-uncurry f u)) ∙
    (funPost-uncurry-inputs f γ ∙
      (isoComp-cong (const-One (funPost-uncurry f v)) (uncurryFamily-absolute (funPost f ◁ γ))) ⁻¹)
```

