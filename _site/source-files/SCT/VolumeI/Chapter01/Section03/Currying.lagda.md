# Consequences of the currying axiom

Uncurrying acts by the actual comparison functor specified in the axiom.
Its equivalence supplies lifting with an image witness and reflection of
higher identifications. The chosen currying operation is not assumed to be
a synthetic functor merely because it is an Agda function.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.Setup as Setup
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as MappingAnimae
import SCT.VolumeI.Chapter01.Section02.FamilyProductFunctor as FamilyProduct
import SCT.VolumeI.Chapter01.Section02.FamilyPairing as FamilyPairing

module SCT.VolumeI.Chapter01.Section03.Currying
  {c m a : Level} (𝒯 : Theory c m a)
  (M : MappingAnimae.MappingAnimae 𝒯) where

open Setup 𝒯
open MappingAnimae.MappingAnimae M
open FamilyProduct vocabulary terminal products productLaws composition vertical whiskering
  using (productFamily; productFamily-absolute; productFamily-pre; productFamily-cong)
open FamilyPairing vocabulary terminal products productLaws composition vertical whiskering
  using (pairing-cong; pairing-pre)

mapUncurryIso : {X C D : CAT} {f g : MAP X (Map C D)}
  → =₁ f g → =₁ (mapUncurry f) (mapUncurry g)
mapUncurryIso {f = f} {g} α = mapUncurry-isoMap f g ∘ α

mapUncurry-lift : {X C D : CAT} (xAn : isAn X) (f g : MAP X (Map C D))
  (α : =₁ (mapUncurry f) (mapUncurry g))
  → FunctorLift (mapUncurry-isoMap f g) α
mapUncurry-lift xAn f g = equiv-lift (mapUncurry-isoMap-isEquiv xAn f g)

mapReflect : {X C D : CAT} (xAn : isAn X) (f g : MAP X (Map C D))
  → =₁ (mapUncurry f) (mapUncurry g) → =₁ f g
mapReflect xAn f g α = FunctorLift.lift (mapUncurry-lift xAn f g α)

mapReflect-β : {X C D : CAT} (xAn : isAn X) (f g : MAP X (Map C D))
  (α : =₁ (mapUncurry f) (mapUncurry g))
  → =₂ (mapUncurryIso (mapReflect xAn f g α)) α
mapReflect-β xAn f g α = FunctorLift.comparison (mapUncurry-lift xAn f g α)

mapReflect-Iso₂ : {X C D : CAT} (xAn : isAn X)
  {f g : MAP X (Map C D)} (α β : =₁ f g)
  → =₂ (mapUncurryIso α) (mapUncurryIso β) → =₂ α β
mapReflect-Iso₂ xAn {f} {g} α β = equiv-reflect (mapUncurry-isoMap-isEquiv xAn f g) α β

mapUncurry-Iso₂ : {X C D : CAT} {f g : MAP X (Map C D)}
  {α β : =₁ f g} → =₂ α β → =₂ (mapUncurryIso α) (mapUncurryIso β)
mapUncurry-Iso₂ {f = f} {g} p = mapUncurry-isoMap f g ◁ p

mapUncurry-Iso₂-lift : {X C D : CAT} (xAn : isAn X)
  {f g : MAP X (Map C D)} (α β : =₁ f g)
  (p : =₂ (mapUncurryIso α) (mapUncurryIso β))
  → FunctorLift (postWhisker (mapUncurry-isoMap f g)) p
mapUncurry-Iso₂-lift xAn {f} {g} α β p =
  postWhisker-lift (mapUncurry-isoMap f g) (mapUncurry-isoMap-isEquiv xAn f g) p

mapCurry-η : {X C D : CAT} (xAn : isAn X) (f : MAP X (Map C D))
  → =₁ (mapCurry xAn (mapUncurry f)) f
mapCurry-η xAn f = mapReflect xAn _ f (mapCurry-β xAn (mapUncurry f))

mapCurry-cong : {X C D : CAT} (xAn : isAn X) {f g : MAP (X × C) D}
  → =₁ f g → =₁ (mapCurry xAn f) (mapCurry xAn g)
mapCurry-cong xAn {f} {g} α = mapReflect xAn _ _
  (invIso (mapCurry-β xAn g) ∙ (α ∙ mapCurry-β xAn f))

mapUncurry-pre : {R X C D : CAT} (f : MAP X (Map C D)) (σ : MAP R X)
  → =₁ (mapUncurry (f ∘ σ)) (mapUncurry f ∘ productMap σ (id C))
mapUncurry-pre {C = C} f σ =
  invIso (comp-assoc (productMap σ (id C)) (productMap f (id C)) mapEval) ∙
    (mapEval ◁ invIso
      (productMap-cong (idIso (f ∘ σ)) (comp-unitˡ (id C)) ∙
        productMap-comp σ f (id C) (id C)))

mapUncurry-id : (C D : CAT) → =₁ (mapUncurry (id (Map C D))) (mapEval {C} {D})
mapUncurry-id C D = comp-unitʳ mapEval ∙ (mapEval ◁ productMap-id (Map C D) C)
```

The following bridge identifies the raw action of the axiom's comparison
functor with the usual formula: product with the identity, followed by
postwhiskering with evaluation. Unit and composition preservation are derived
for that formula and then transferred back to the actual comparison functor.

```agda
productFamily-restrict : {A B C C′ D D′ : CAT}
  {f f′ : MAP C C′} {g g′ : MAP D D′}
  (α : MAP A (f ＝ f′)) (β : MAP A (g ＝ g′)) (r : MAP B A)
  → =₁ (productFamily α β ∘ r) (productFamily (α ∘ r) (β ∘ r))
productFamily-restrict α β r =
  pairing-cong (preWhisker-pre α pr₁ r) (preWhisker-pre β pr₂ r) ∙
    pairing-pre (α ▷ pr₁) (β ▷ pr₂) r

mapUncurry-cong : {X C D : CAT} {f g : MAP X (Map C D)}
  → =₁ f g → =₁ (mapUncurry f) (mapUncurry g)
mapUncurry-cong {C = C} α = mapEval ◁ productMap-cong α (idIso (id C))

mapUncurryIso-at : {X C D : CAT} {f g : MAP X (Map C D)} (α : =₁ f g)
  → =₂ (mapUncurryIso α) (mapUncurry-cong α)
mapUncurryIso-at {C = C} {f = f} {g} α =
  let family = productFamily (id (f ＝ g)) (const (idIso (id C)))
      specialize-product = productFamily-absolute α (idIso (id C)) ∙
        (productFamily-cong (comp-unitˡ α) (const-evaluate (idIso (id C)) α) ∙
          productFamily-restrict (id (f ＝ g)) (const (idIso (id C))) α)
  in (postWhisker mapEval ◁ specialize-product) ∙ comp-assoc α family (postWhisker mapEval)

mapUncurry-cong-id : {X C D : CAT} (f : MAP X (Map C D))
  → =₂ (mapUncurry-cong (idIso f)) (idIso (mapUncurry f))
mapUncurry-cong-id {C = C} f = postWhisker-idIso mapEval (productMap f (id C)) ∙
  (postWhisker mapEval ◁ productMap-cong-id f (id C))

mapUncurry-cong-comp : {X C D : CAT} {f g h : MAP X (Map C D)}
  (β : =₁ g h) (α : =₁ f g)
  → =₂ (mapUncurry-cong (β ∙ α)) (mapUncurry-cong β ∙ mapUncurry-cong α)
mapUncurry-cong-comp {C = C} β α =
  postWhisker-isoComp-at mapEval
    (productMap-cong β (idIso (id C))) (productMap-cong α (idIso (id C))) ∙
  (postWhisker mapEval ◁
    (productMap-cong-comp β α (idIso (id C)) (idIso (id C)) ∙
      productMap-cong-Iso₂ (idIso (β ∙ α)) (invIso (isoComp-unitˡ-at (idIso (id C))))))

mapUncurryIso-id : {X C D : CAT} (f : MAP X (Map C D))
  → =₂ (mapUncurryIso (idIso f)) (idIso (mapUncurry f))
mapUncurryIso-id f = mapUncurry-cong-id f ∙ mapUncurryIso-at (idIso f)

mapUncurryIso-comp : {X C D : CAT} {f g h : MAP X (Map C D)}
  (β : =₁ g h) (α : =₁ f g)
  → =₂ (mapUncurryIso (β ∙ α)) (mapUncurryIso β ∙ mapUncurryIso α)
mapUncurryIso-comp β α = invIso (isoComp-cong (mapUncurryIso-at β) (mapUncurryIso-at α)) ∙
  (mapUncurry-cong-comp β α ∙ mapUncurryIso-at (β ∙ α))

mapCurry-cong-β : {X C D : CAT} (xAn : isAn X) {f g : MAP (X × C) D}
  (α : =₁ f g)
  → =₂ (mapUncurryIso (mapCurry-cong xAn α))
      (invIso (mapCurry-β xAn g) ∙ (α ∙ mapCurry-β xAn f))
mapCurry-cong-β xAn {f} {g} α = mapReflect-β xAn _ _
  (invIso (mapCurry-β xAn g) ∙ (α ∙ mapCurry-β xAn f))

mapCurry-cong-Iso₂ : {X C D : CAT} (xAn : isAn X) {f g : MAP (X × C) D}
  {α β : =₁ f g} → =₂ α β → =₂ (mapCurry-cong xAn α) (mapCurry-cong xAn β)
mapCurry-cong-Iso₂ xAn {f} {g} {α} {β} p =
  let back = IsEquiv.inverse (mapUncurry-isoMap-isEquiv xAn (mapCurry xAn f) (mapCurry xAn g))
  in back ◁ isoComp-cong (idIso (invIso (mapCurry-β xAn g)))
    (isoComp-cong p (idIso (mapCurry-β xAn f)))
```
