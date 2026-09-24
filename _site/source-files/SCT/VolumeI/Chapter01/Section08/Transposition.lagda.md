# Transposing the parameter and the source

The product symmetry changes `C → Fun X E` into `X × C → E`.
Its action on isomorphism animae is an equivalence, with a specified
inverse-image comparison. These are the transpositions used to test a
pushout at the target `Fun X E`.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories

module SCT.VolumeI.Chapter01.Section08.Transposition
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section07.IsomorphismLifting 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section08.SwapRestrictionData 𝒯 public using (swap-restriction)

transpose : {X C E : CAT} → MAP C (Fun X E) → MAP (X × C) E
transpose k = funUncurry k ∘ swap

untranspose : {X C E : CAT} → MAP (X × C) E → MAP C (Fun X E)
untranspose f = funCurry (f ∘ swap)

abstract
  transpose-β : {X C E : CAT} (f : MAP (X × C) E) → (transpose (untranspose f)) =₁ f
  transpose-β {X} {C} f = comp-unitʳ f ∙
    ((f ◁ swap-swap X C) ∙
      (comp-assoc swap swap f ∙ (funCurry-β (f ∘ swap) ▷ swap)))

transpose-isoMap : {X C E : CAT} (f g : MAP C (Fun X E)) →
  MAP (f ＝ g) (transpose f ＝ transpose g)
transpose-isoMap f g = preWhisker swap ∘ funUncurry-isoMap f g

transpose-isoMap-isEquiv : {X C E : CAT} (f g : MAP C (Fun X E)) →
  IsEquiv (transpose-isoMap f g)
transpose-isoMap-isEquiv {X} {C} f g = equiv-compose
  (funUncurry-isoMap f g) (preWhisker swap)
  (funUncurry-isoMap-isEquiv f g)
  (preWhisker-isEquiv swap (swap-isEquiv X C) (funUncurry f) (funUncurry g))

transposeIso : {X C E : CAT} {f g : MAP C (Fun X E)} →
  f =₁ g → (transpose f) =₁ (transpose g)
transposeIso {f = f} {g} α = transpose-isoMap f g ∘ α

transposeIso-at : {X C E : CAT} {f g : MAP C (Fun X E)} (α : f =₁ g) →
  (transposeIso α) =₂ (funUncurryIso α ▷ swap)
transposeIso-at {f = f} {g} α = comp-assoc α (funUncurry-isoMap f g) (preWhisker swap)

transposeIso-comp : {X C E : CAT} {f g h : MAP C (Fun X E)}
  (β : g =₁ h) (α : f =₁ g) →
  (transposeIso (β ∙ α)) =₂ (transposeIso β ∙ transposeIso α)
transposeIso-comp β α =
  isoComp-cong ((transposeIso-at β) ⁻¹) ((transposeIso-at α) ⁻¹) ∙
  (preWhisker-isoComp-at (funUncurryIso β) (funUncurryIso α) swap ∙
    ((preWhisker swap ◁ funUncurryIso-comp β α) ∙ transposeIso-at (β ∙ α)))

abstract
  transpose-reflect : {X C E : CAT} (f g : MAP C (Fun X E)) →
    (transpose f) =₁ (transpose g) → f =₁ g
  transpose-reflect f g α = FunctorLift.lift (equiv-lift (transpose-isoMap-isEquiv f g) α)

  transpose-reflect-β : {X C E : CAT} (f g : MAP C (Fun X E))
    (α : (transpose f) =₁ (transpose g)) → (transposeIso (transpose-reflect f g α)) =₂ α
  transpose-reflect-β f g α = FunctorLift.comparison (equiv-lift (transpose-isoMap-isEquiv f g) α)

transpose-reflect-Iso₂ : {X C E : CAT} {f g : MAP C (Fun X E)} (α β : f =₁ g) →
  (transposeIso α) =₂ (transposeIso β) → α =₂ β
transpose-reflect-Iso₂ {f = f} {g} α β = equiv-reflect (transpose-isoMap-isEquiv f g) α β

transpose-pre : {X A B E : CAT} (u : MAP A B) (f : MAP B (Fun X E)) →
  (transpose (f ∘ u)) =₁ (transpose f ∘ productMap (id X) u)
transpose-pre {X} u f = (comp-assoc (productMap (id X) u) swap (funUncurry f)) ⁻¹ ∙
  ((funUncurry f ◁ swap-restriction u) ∙
  (comp-assoc swap (productMap u (id X)) (funUncurry f) ∙
    (funUncurry-restrict f u ▷ swap)))
```
