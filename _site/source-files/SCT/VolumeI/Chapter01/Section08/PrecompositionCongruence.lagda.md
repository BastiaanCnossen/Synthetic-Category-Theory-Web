# Evaluating precomposition of isomorphic functors

The chosen action of precomposition on an isomorphism agrees, after
evaluation at a parameter, with its product with that parameter's identity.
The proof uses the computation rule for the lifted isomorphism and
naturality of the four factors in the product separation comparison.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section03.Structural as Structural
import SCT.VolumeI.Chapter01.Section03.PairingNaturality as PN
import SCT.VolumeI.Chapter01.Section02.Isomorphisms as Isomorphisms

module SCT.VolumeI.Chapter01.Section08.PrecompositionCongruence
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section04.Compatibility 𝒯 M
  using (mapUncurry-restrict-inputs)
open Structural vocabulary terminal products productLaws composition whiskering
  using (preWhisker-id-at; postWhisker-id-at; whisker-mixed-at; postWhisker-comp-at)
open PN vocabulary terminal products productLaws composition vertical whiskering
  using (move-square)
open Isomorphisms vocabulary terminal products productLaws composition vertical whiskering
  using (cancel-inverse)

identity-source-square : {C D : CAT} {f g : MAP C D}
  (β : f =₁ g) (u : f =₁ f) → u =₂ (idIso f) →
  (β ∙ u) =₂ (idIso g ∙ β)
identity-source-square β u p = (isoComp-unitˡ-at β) ⁻¹ ∙
  (isoComp-unitʳ-at β ∙ isoComp-cong (idIso β) p)

product-comparison-square : {C C′ D D′ : CAT}
  {a a′ b b′ : MAP C C′} {d d′ e e′ : MAP D D′}
  (u : a =₁ b) (u′ : a′ =₁ b′) (v : d =₁ e) (v′ : d′ =₁ e′)
  (α : a =₁ a′) (β : b =₁ b′) (γ : d =₁ d′) (δ : e =₁ e′) →
  (u′ ∙ α) =₂ (β ∙ u) → (v′ ∙ γ) =₂ (δ ∙ v) →
  (productMap-cong u′ v′ ∙ productMap-cong α γ) =₂
    (productMap-cong β δ ∙ productMap-cong u v)
product-comparison-square u u′ v v′ α β γ δ p q =
  productMap-cong-comp β u δ v ∙
    (productMap-cong-Iso₂ p q ∙ (productMap-cong-comp u′ α v′ γ) ⁻¹)

open import SCT.VolumeI.Chapter01.Section08.CoconePostcomposition 𝒯 using (post-square)

productMap-separate-second : {X Y A B : CAT} (h : MAP X Y)
  {f g : MAP A B} (α : f =₁ g) →
  (productMap-separate h g ∙
    (productMap-cong (idIso (id Y)) α ▷ productMap h (id A))) =₂
    ((productMap h (id B) ◁ productMap-cong (idIso (id X)) α) ∙ productMap-separate h f)
productMap-separate-second {X} {Y} {A} {B} h {f} {g} α =
  paste-squares (r₃f ⁻¹ ∙ (r₂f ∙ r₁f)) (r₃g ⁻¹ ∙ (r₂g ∙ r₁g))
    (r₄f ⁻¹) (r₄g ⁻¹) action₀ action₃ action₄
    (paste-squares (r₂f ∙ r₁f) (r₂g ∙ r₁g) (r₃f ⁻¹) (r₃g ⁻¹)
      action₀ action₂ action₃
      (paste-squares r₁f r₁g r₂f r₂g action₀ action₁ action₂ step₁ step₂) step₃) step₄
  where
  r₁f = productMap-comp h (id Y) (id A) f
  r₁g = productMap-comp h (id Y) (id A) g
  r₂f = productMap-cong (comp-unitˡ h) (comp-unitʳ f)
  r₂g = productMap-cong (comp-unitˡ h) (comp-unitʳ g)
  r₃f = productMap-cong (comp-unitʳ h) (comp-unitˡ f)
  r₃g = productMap-cong (comp-unitʳ h) (comp-unitˡ g)
  r₄f = productMap-comp (id X) h f (id B)
  r₄g = productMap-comp (id X) h g (id B)
  action₀ = productMap-cong (idIso (id Y)) α ▷ productMap h (id A)
  action₁ = productMap-cong (idIso (id Y) ▷ h) (α ▷ id A)
  action₂ = productMap-cong (idIso h) α
  action₃ = productMap-cong (h ◁ idIso (id X)) (id B ◁ α)
  action₄ = productMap h (id B) ◁ productMap-cong (idIso (id X)) α
  step₁ = productMap-comp-natural-outer h (id A) (idIso (id Y)) α
  step₂ = product-comparison-square
    (comp-unitˡ h) (comp-unitˡ h) (comp-unitʳ f) (comp-unitʳ g)
    (idIso (id Y) ▷ h) (idIso h) (α ▷ id A) α
    (identity-source-square (comp-unitˡ h) _ (preWhisker-idIso (id Y) h))
    (preWhisker-id-at α)
  step₃ = move-square r₃g action₃ action₂ r₃f
    (product-comparison-square
      (comp-unitʳ h) (comp-unitʳ h) (comp-unitˡ f) (comp-unitˡ g)
      (h ◁ idIso (id X)) (idIso h) (id B ◁ α) α
      (identity-source-square (comp-unitʳ h) _ (postWhisker-idIso h (id X)))
      (postWhisker-id-at α))
  step₄ = move-square r₄g action₄ action₃ r₄f
    (productMap-comp-natural-inner (idIso (id X)) α h (id B))
```

The remaining five squares follow the five factors of `mapPre-uncurry`.
Their composite is the required comparison at an arbitrary parameter map.

```agda
module CongruenceAt {X A B E : CAT} {f g : MAP A B}
  (α : f =₁ g) (h : MAP X (Map B E)) where

  γ : (mapPre {D = E} f) =₁ (mapPre g)
  γ = mapPre-cong α
  HA = productMap h (id A)
  HB = productMap h (id B)
  Lf = productMap (id X) f
  Lg = productMap (id X) g
  Kf = productMap (id (Map B E)) f
  Kg = productMap (id (Map B E)) g
  smallImage = productMap-cong (idIso (id X)) α
  largeImage = productMap-cong (idIso (id (Map B E))) α
  βf = mapPre-β {D = E} f
  βg = mapPre-β {D = E} g
  evaluatedImage = mapEval ◁ largeImage

  liftedImage : (mapUncurryIso γ) =₂ (βg ⁻¹ ∙ (evaluatedImage ∙ βf))
  liftedImage = mapReflect-β (map-isAn B E) _ _ (βg ⁻¹ ∙ (evaluatedImage ∙ βf))

  betaSquare : (βg ∙ mapUncurryIso γ) =₂ (evaluatedImage ∙ βf)
  betaSquare = cancel-inverse βg (evaluatedImage ∙ βf) ∙
    isoComp-cong (idIso βg) liftedImage

  r₁f = mapUncurry-restrict (mapPre f) h
  r₁g = mapUncurry-restrict (mapPre g) h
  r₂f = βf ▷ HA
  r₂g = βg ▷ HA
  r₃f = comp-assoc HA Kf mapEval
  r₃g = comp-assoc HA Kg mapEval
  r₄f = mapEval ◁ productMap-separate h f
  r₄g = mapEval ◁ productMap-separate h g
  r₅f = (comp-assoc Lf HB mapEval) ⁻¹
  r₅g = (comp-assoc Lg HB mapEval) ⁻¹
  action₀ = mapUncurryIso (γ ▷ h)
  action₁ = mapUncurryIso γ ▷ HA
  action₂ = evaluatedImage ▷ HA
  action₃ = mapEval ◁ (largeImage ▷ HA)
  action₄ = mapEval ◁ (HB ◁ smallImage)
  action₅ = mapUncurry h ◁ smallImage
  step₁ = mapUncurry-restrict-inputs γ h
  step₂ = preWhisker-isoComp-at evaluatedImage βf HA ∙
    ((preWhisker HA ◁ betaSquare) ∙
      (preWhisker-isoComp-at βg (mapUncurryIso γ) HA) ⁻¹)
  step₃ = whisker-mixed-at largeImage HA mapEval
  step₄ = post-square mapEval (productMap-separate h f) (productMap-separate h g)
    (largeImage ▷ HA) (HB ◁ smallImage) (productMap-separate-second h α)
  step₅ = move-square (comp-assoc Lg HB mapEval) action₅ action₄
    (comp-assoc Lf HB mapEval) (postWhisker-comp-at smallImage HB mapEval)

  abstract
    law : (mapPre-uncurry g h ∙ mapUncurryIso (γ ▷ h)) =₂
      ((mapUncurry h ◁ productMap-cong (idIso (id X)) α) ∙ mapPre-uncurry f h)
    law = paste-squares (r₄f ∙ (r₃f ∙ (r₂f ∙ r₁f))) (r₄g ∙ (r₃g ∙ (r₂g ∙ r₁g)))
      r₅f r₅g action₀ action₄ action₅
      (paste-squares (r₃f ∙ (r₂f ∙ r₁f)) (r₃g ∙ (r₂g ∙ r₁g)) r₄f r₄g action₀ action₃ action₄
        (paste-squares (r₂f ∙ r₁f) (r₂g ∙ r₁g) r₃f r₃g action₀ action₂ action₃
          (paste-squares r₁f r₁g r₂f r₂g action₀ action₁ action₂ step₁ step₂) step₃) step₄) step₅

mapPre-cong-at : {X A B E : CAT} {f g : MAP A B}
  (α : f =₁ g) (h : MAP X (Map B E)) →
  (mapPre-uncurry g h ∙ mapUncurryIso (mapPre-cong α ▷ h)) =₂
    ((mapUncurry h ◁ productMap-cong (idIso (id X)) α) ∙ mapPre-uncurry f h)
mapPre-cong-at = CongruenceAt.law
```
