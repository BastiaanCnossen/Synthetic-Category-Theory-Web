# Lifting isomorphisms through uncurrying

The actual product-and-evaluation action on isomorphism animae is an
equivalence. This is derived from the stated mapping-anima universal
property by the naturality theorem for evaluation. Its lifts retain their
image witnesses, including for higher identifications.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories

module SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.IsomorphismLifting
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.EvaluationNaturality 𝒯 M using (evaluation-isoMap-isEquiv)

funUncurry-isoMap-isEquiv : {T C D : CAT} (f g : MAP T (Fun C D)) → IsEquiv (funUncurry-isoMap f g)
funUncurry-isoMap-isEquiv {T} {C} {D} f g = evaluation-isoMap-isEquiv funEval T (funUniversal C D T) f g

abstract
  funUncurry-lift : {T C D : CAT} (f g : MAP T (Fun C D))
    (α : (funUncurry f) =₁ (funUncurry g)) → FunctorLift (funUncurry-isoMap f g) α
  funUncurry-lift f g = equiv-lift (funUncurry-isoMap-isEquiv f g)

  funIsoReflect : {T C D : CAT} (f g : MAP T (Fun C D)) →
    (funUncurry f) =₁ (funUncurry g) → f =₁ g
  funIsoReflect f g α = FunctorLift.lift (funUncurry-lift f g α)

  funIsoReflect-β : {T C D : CAT} (f g : MAP T (Fun C D))
    (α : (funUncurry f) =₁ (funUncurry g)) → (funUncurryIso (funIsoReflect f g α)) =₂ α
  funIsoReflect-β f g α = FunctorLift.comparison (funUncurry-lift f g α)

funReflect-Iso₂ : {T C D : CAT} {f g : MAP T (Fun C D)} (α β : f =₁ g) →
  (funUncurryIso α) =₂ (funUncurryIso β) → α =₂ β
funReflect-Iso₂ {f = f} {g} α β = equiv-reflect (funUncurry-isoMap-isEquiv f g) α β

funUncurry-Iso₂-lift : {T C D : CAT} {f g : MAP T (Fun C D)} (α β : f =₁ g)
  (p : (funUncurryIso α) =₂ (funUncurryIso β)) → FunctorLift (postWhisker (funUncurry-isoMap f g)) p
funUncurry-Iso₂-lift {f = f} {g} α β = postWhisker-lift (funUncurry-isoMap f g) (funUncurry-isoMap-isEquiv f g)
```
