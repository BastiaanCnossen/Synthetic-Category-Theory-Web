# The action of uncurrying on isomorphisms

Uncurrying acts by product with the identity followed by evaluation. The
family calculations below apply to the whole isomorphism anima. They are
instances of the calculus for an arbitrary evaluation functor.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories

module SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.UncurryingAction
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open import SCT.VolumeI.Chapter01.Section07.Currying 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.EvaluationNaturality 𝒯 M using (module Action)
open import SCT.VolumeI.Chapter01.Section04.Substitution.Compatibility 𝒯 M public using (slice-comparison)
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingUnits as PN
open PN vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle using (cancel-right-reflect)

module _ {C D : CAT} where
  open Action (funEval {C} {D}) public
    using (uncurryFamily; uncurryFamily-cong; uncurryFamily-at; uncurryFamily-identity;
      uncurryFamily-composition; uncurryFamily-restrict; uncurryFamily-constant;
      uncurry-restrict-inputs; uncurry-restrict-substitution)
    renaming (isoMap to funUncurry-isoMap; uncurryIso to funUncurryIso;
      uncurryIso-at to funUncurryIso-at; uncurryIso-id to funUncurryIso-id;
      uncurryIso-comp to funUncurryIso-comp)

funUncurry-Iso₂ : {T C D : CAT} {f g : MAP T (Fun C D)}
  {α β : f =₁ g} → α =₂ β → (funUncurryIso α) =₂ (funUncurryIso β)
funUncurry-Iso₂ {f = f} {g} p = funUncurry-isoMap f g ◁ p

uncurryFamily-absolute : {T C D : CAT} {f g : MAP T (Fun C D)} (α : f =₁ g) →
  (uncurryFamily α) =₂ (funUncurryIso α)
uncurryFamily-absolute α = (uncurryFamily-at α) ⁻¹

funUncurry-restrict-inputs : {Y X C D : CAT} {f g : MAP X (Fun C D)}
  (α : f =₁ g) (r : MAP Y X) →
  (funUncurry-restrict g r ∙ funUncurryIso (α ▷ r)) =₂
    ((funUncurryIso α ▷ productMap r (id C)) ∙ funUncurry-restrict f r)
funUncurry-restrict-inputs {C = C} {f = f} {g} α r =
  isoComp-cong (preWhisker (productMap r (id C)) ◁ uncurryFamily-absolute α)
    (const-One (funUncurry-restrict f r)) ∙
  (uncurry-restrict-inputs α r ∙
    (isoComp-cong (const-One (funUncurry-restrict g r)) (uncurryFamily-absolute (α ▷ r))) ⁻¹)

funUncurryIso-inverse : {T C D : CAT} {f g : MAP T (Fun C D)} (α : f =₁ g) →
  (funUncurryIso (α ⁻¹)) =₂ ((funUncurryIso α) ⁻¹)
funUncurryIso-inverse {f = f} α = cancel-right-reflect (funUncurryIso α)
  ((isoComp-inverseˡ-at (funUncurryIso α)) ⁻¹ ∙
  (funUncurryIso-id f ∙
  (funUncurry-Iso₂ (isoComp-inverseˡ-at α) ∙ (funUncurryIso-comp (α ⁻¹) α) ⁻¹)))
```

