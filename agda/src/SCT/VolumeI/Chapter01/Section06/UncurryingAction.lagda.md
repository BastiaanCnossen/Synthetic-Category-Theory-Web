# The action of uncurrying on isomorphisms

Uncurrying acts by product with the identity followed by evaluation. The
family calculations below apply to the whole isomorphism anima. They are
instances of the calculus for an arbitrary evaluation functor.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section06.FunctorCategories as Categories

module SCT.VolumeI.Chapter01.Section06.UncurryingAction
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter01.Section03.Setup 𝒯
open import SCT.VolumeI.Chapter01.Section06.Currying 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section06.EvaluationNaturality 𝒯 M using (module Action)
open import SCT.VolumeI.Chapter01.Section03.Compatibility 𝒯 M public using (slice-comparison)
import SCT.VolumeI.Chapter01.Section02.PairingUnits as PN
open PN vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle using (cancel-right-reflect)

module _ {C D : CAT} where
  open Action (funEval {C} {D}) public
    using (uncurryFamily; uncurryFamily-cong; uncurryFamily-at; uncurryFamily-identity;
      uncurryFamily-composition; uncurryFamily-restrict; uncurryFamily-constant;
      uncurry-pre-inputs; uncurry-pre-substitution)
    renaming (isoMap to funUncurry-isoMap; uncurryIso to funUncurryIso;
      uncurryIso-at to funUncurryIso-at; uncurryIso-id to funUncurryIso-id;
      uncurryIso-comp to funUncurryIso-comp)

funUncurry-Iso₂ : {T C D : CAT} {f g : MAP T (Fun C D)}
  {α β : =₁ f g} → =₂ α β → =₂ (funUncurryIso α) (funUncurryIso β)
funUncurry-Iso₂ {f = f} {g} p = funUncurry-isoMap f g ◁ p

uncurryFamily-absolute : {T C D : CAT} {f g : MAP T (Fun C D)} (α : =₁ f g) →
  =₂ (uncurryFamily α) (funUncurryIso α)
uncurryFamily-absolute α = invIso (uncurryFamily-at α)

funUncurry-pre-inputs : {Y X C D : CAT} {f g : MAP X (Fun C D)}
  (α : =₁ f g) (r : MAP Y X) →
  =₂ (funUncurry-pre g r ∙ funUncurryIso (α ▷ r))
    ((funUncurryIso α ▷ productMap r (id C)) ∙ funUncurry-pre f r)
funUncurry-pre-inputs {C = C} {f = f} {g} α r =
  isoComp-cong (preWhisker (productMap r (id C)) ◁ uncurryFamily-absolute α)
    (const-One (funUncurry-pre f r)) ∙
  (uncurry-pre-inputs α r ∙
    invIso (isoComp-cong (const-One (funUncurry-pre g r)) (uncurryFamily-absolute (α ▷ r))))

funUncurryIso-inverse : {T C D : CAT} {f g : MAP T (Fun C D)} (α : =₁ f g) →
  =₂ (funUncurryIso (invIso α)) (invIso (funUncurryIso α))
funUncurryIso-inverse {f = f} α = cancel-right-reflect (funUncurryIso α)
  (invIso (isoComp-inverseˡ-at (funUncurryIso α)) ∙
  (funUncurryIso-id f ∙
  (funUncurry-Iso₂ (isoComp-inverseˡ-at α) ∙ invIso (funUncurryIso-comp (invIso α) α))))
```

