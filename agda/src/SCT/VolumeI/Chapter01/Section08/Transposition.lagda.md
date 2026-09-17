# Transposing the parameter and the source

The product symmetry changes `C → Fun X E` into `X × C → E`.
Its action on isomorphism animae is an equivalence, with a specified
inverse-image comparison. These are the transpositions used to test a
pushout at the target `Fun X E`.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section06.FunctorCategories as Categories

module SCT.VolumeI.Chapter01.Section08.Transposition
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter01.Section06.Setup 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section06.IsomorphismLifting 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section08.SwapRestrictionData 𝒯 public using (swap-restriction)

transpose : {X C E : CAT} → MAP C (Fun X E) → MAP (X × C) E
transpose k = funUncurry k ∘ swap

untranspose : {X C E : CAT} → MAP (X × C) E → MAP C (Fun X E)
untranspose f = funCurry (f ∘ swap)

abstract
  transpose-β : {X C E : CAT} (f : MAP (X × C) E) → =₁ (transpose (untranspose f)) f
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
  =₁ f g → =₁ (transpose f) (transpose g)
transposeIso {f = f} {g} α = transpose-isoMap f g ∘ α

transposeIso-at : {X C E : CAT} {f g : MAP C (Fun X E)} (α : =₁ f g) →
  =₂ (transposeIso α) (funUncurryIso α ▷ swap)
transposeIso-at {f = f} {g} α = comp-assoc α (funUncurry-isoMap f g) (preWhisker swap)

transposeIso-comp : {X C E : CAT} {f g h : MAP C (Fun X E)}
  (β : =₁ g h) (α : =₁ f g) →
  =₂ (transposeIso (β ∙ α)) (transposeIso β ∙ transposeIso α)
transposeIso-comp β α =
  isoComp-cong (invIso (transposeIso-at β)) (invIso (transposeIso-at α)) ∙
  (preWhisker-isoComp-at (funUncurryIso β) (funUncurryIso α) swap ∙
    ((preWhisker swap ◁ funUncurryIso-comp β α) ∙ transposeIso-at (β ∙ α)))

abstract
  transpose-reflect : {X C E : CAT} (f g : MAP C (Fun X E)) →
    =₁ (transpose f) (transpose g) → =₁ f g
  transpose-reflect f g α = FunctorLift.lift (equiv-lift (transpose-isoMap-isEquiv f g) α)

  transpose-reflect-β : {X C E : CAT} (f g : MAP C (Fun X E))
    (α : =₁ (transpose f) (transpose g)) → =₂ (transposeIso (transpose-reflect f g α)) α
  transpose-reflect-β f g α = FunctorLift.comparison (equiv-lift (transpose-isoMap-isEquiv f g) α)

transpose-reflect-Iso₂ : {X C E : CAT} {f g : MAP C (Fun X E)} (α β : =₁ f g) →
  =₂ (transposeIso α) (transposeIso β) → =₂ α β
transpose-reflect-Iso₂ {f = f} {g} α β = equiv-reflect (transpose-isoMap-isEquiv f g) α β

transpose-pre : {X A B E : CAT} (u : MAP A B) (f : MAP B (Fun X E)) →
  =₁ (transpose (f ∘ u)) (transpose f ∘ productMap (id X) u)
transpose-pre {X} u f = invIso (comp-assoc (productMap (id X) u) swap (funUncurry f)) ∙
  ((funUncurry f ◁ swap-restriction u) ∙
  (comp-assoc swap (productMap u (id X)) (funUncurry f) ∙
    (funUncurry-pre f u ▷ swap)))
```
