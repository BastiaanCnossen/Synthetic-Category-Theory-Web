# Parametrized compatibility of uncurrying

The action below is a functor from any common parameter category. Its
comparison with the equality-anima functor in the mapping axiom is explicit.
In particular, preservation of composition is simultaneous in both inputs.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.Setup as Setup
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as MappingAnimae
import SCT.VolumeI.Chapter01.Section03.Currying as Currying
import SCT.VolumeI.Chapter01.Section02.FamilyProductFunctor as FamilyProduct
import SCT.VolumeI.Chapter01.Section02.FamilyPairing as FamilyPairing
import SCT.VolumeI.Chapter01.Section02.Parameterized as Parameterized
import SCT.VolumeI.Chapter01.Section02.FamilyNaturality as FamilyNaturality

module SCT.VolumeI.Chapter01.Section03.Compatibility
  {c m a : Level} (𝒯 : Theory c m a)
  (M : MappingAnimae.MappingAnimae 𝒯) where

open Setup 𝒯
open MappingAnimae.MappingAnimae M
open Currying 𝒯 M
open FamilyProduct vocabulary terminal products productLaws composition vertical whiskering
open FamilyPairing vocabulary terminal products productLaws composition vertical whiskering
  using (post-composition; post-constant; pre-constant)
open Parameterized vocabulary terminal products productLaws composition vertical
  using (const-cong; const-comp; unitˡ; unitʳ; assoc)
open Parameterized.WhiskeringLaws vocabulary terminal products productLaws composition vertical whiskering
open FamilyNaturality vocabulary terminal products productLaws composition vertical whiskering
  using (family-move-square)

uncurryFamily : {A X C D : CAT} {f g : MAP X (Map C D)}
  → MAP A (f ＝ g) → MAP A (mapUncurry f ＝ mapUncurry g)
uncurryFamily {C = C} α = mapEval ◁ productFamily α (const (idIso (id C)))

uncurryFamily-cong : {A X C D : CAT} {f g : MAP X (Map C D)}
  {α β : MAP A (f ＝ g)} → =₁ α β → =₁ (uncurryFamily α) (uncurryFamily β)
uncurryFamily-cong {C = C} p = postWhisker mapEval ◁
  productFamily-cong p (idIso (const (idIso (id C))))

uncurryFamily-at : {A X C D : CAT} {f g : MAP X (Map C D)}
  (α : MAP A (f ＝ g))
  → =₁ (mapUncurry-isoMap f g ∘ α) (uncurryFamily α)
uncurryFamily-at {C = C} {f = f} {g} α =
  (postWhisker mapEval ◁
    (productFamily-cong (comp-unitˡ α) (const-pre (idIso (id C)) α) ∙
      productFamily-restrict (id (f ＝ g)) (const (idIso (id C))) α)) ∙
  comp-assoc α (productFamily (id (f ＝ g)) (const (idIso (id C)))) (postWhisker mapEval)

uncurryFamily-identity : {A X C D : CAT} (f : MAP X (Map C D))
  → =₁ (uncurryFamily (const {P = A} (idIso f))) (const (idIso (mapUncurry f)))
uncurryFamily-identity {C = C} f =
  const-cong (postWhisker-idIso mapEval (productMap f (id C))) ∙
  (post-constant mapEval (idIso (productMap f (id C))) ∙
    (postWhisker mapEval ◁ productFamily-identity f (id C)))

uncurryFamily-composition : {A X C D : CAT} {f g h : MAP X (Map C D)}
  (β : MAP A (g ＝ h)) (α : MAP A (f ＝ g))
  → =₁ (uncurryFamily (β ∙ α)) (uncurryFamily β ∙ uncurryFamily α)
uncurryFamily-composition {C = C} β α =
  let identity = const (idIso (id C))
  in post-composition mapEval (productFamily β identity) (productFamily α identity) ∙
    (postWhisker mapEval ◁
      (productFamily-composition β α identity identity ∙
        productFamily-cong (idIso (β ∙ α)) (invIso (unitˡ identity))))

uncurryFamily-restrict : {A B X C D : CAT} {f g : MAP X (Map C D)}
  (α : MAP A (f ＝ g)) (r : MAP B A)
  → =₁ (uncurryFamily α ∘ r) (uncurryFamily (α ∘ r))
uncurryFamily-restrict {C = C} α r =
  (postWhisker mapEval ◁
    (productFamily-cong (idIso (α ∘ r)) (const-pre (idIso (id C)) r) ∙
      productFamily-restrict α (const (idIso (id C))) r)) ∙
  postWhisker-pre mapEval (productFamily α (const (idIso (id C)))) r

uncurryFamily-constant : {A X C D : CAT} {f g : MAP X (Map C D)}
  (α : =₁ f g)
  → =₁ (uncurryFamily (const {P = A} α)) (const (mapUncurry-cong α))
uncurryFamily-constant {C = C} α =
  post-constant mapEval (productMap-cong α (idIso (id C))) ∙
    (postWhisker mapEval ◁ productFamily-constant α (idIso (id C)))
```

To prove naturality of the already chosen substitution comparison, first
normalize the product-composition comparison by the left unitor of the
identity functor on `C`. The following square transports the ordinary
product comparison through that normalization. Both varying inputs remain
functors from the common parameter category throughout the calculation.

```agda

product-family-square : {A X X′ Y Y′ : CAT}
  {f f′ h h′ : MAP X X′} {g g′ k k′ : MAP Y Y′}
  (u : =₁ f h) (u′ : =₁ f′ h′) (v : =₁ g k) (v′ : =₁ g′ k′)
  (α : MAP A (f ＝ f′)) (β : MAP A (h ＝ h′))
  (γ : MAP A (g ＝ g′)) (δ : MAP A (k ＝ k′))
  → =₁ (const u′ ∙ α) (β ∙ const u)
  → =₁ (const v′ ∙ γ) (δ ∙ const v)
  → =₁ (const (productMap-cong u′ v′) ∙ productFamily α γ)
      (productFamily β δ ∙ const (productMap-cong u v))
product-family-square u u′ v v′ α β γ δ p q =
  isoComp-cong (idIso _) (productFamily-constant u v) ∙
  (productFamily-composition β (const u) δ (const v) ∙
  (productFamily-cong p q ∙
  (invIso (productFamily-composition (const u′) α (const v′) γ) ∙
    isoComp-cong (invIso (productFamily-constant u′ v′)) (idIso _))))

fixed-second-square : {A X X′ Y Y′ : CAT} {f f′ : MAP X X′} {g k : MAP Y Y′}
  (α : MAP A (f ＝ f′)) (δ : =₁ g k)
  → =₁ (const (productMap-cong (idIso f′) δ) ∙ productFamily α (const (idIso g)))
      (productFamily α (const (idIso k)) ∙ const (productMap-cong (idIso f) δ))
fixed-second-square {f = f} {f′} {g} {k} α δ =
  product-family-square (idIso f) (idIso f′) δ δ α α
    (const (idIso g)) (const (idIso k))
    (invIso (unitʳ α) ∙ unitˡ α)
    (invIso (unitˡ (const δ)) ∙ unitʳ (const δ))

slice-comparison : {Y X Z C : CAT} (f : MAP X Z) (σ : MAP Y X)
  → =₁ (productMap f (id C) ∘ productMap σ (id C)) (productMap (f ∘ σ) (id C))
slice-comparison {C = C} f σ =
  productMap-cong (idIso (f ∘ σ)) (comp-unitˡ (id C)) ∙
    productMap-comp σ f (id C) (id C)

slice-comparison-inputs : {A Y X Z C : CAT} {f g : MAP X Z}
  (α : MAP A (f ＝ g)) (σ : MAP Y X)
  → =₁
      (const (slice-comparison {C = C} g σ) ∙
        (productFamily α (const (idIso (id C))) ▷ productMap σ (id C)))
      (productFamily (α ▷ σ) (const (idIso (id C))) ∙ const (slice-comparison f σ))
slice-comparison-inputs {C = C} {f} {g} α σ =
  let identity = const (idIso (id C))
      action = productFamily α identity ▷ productMap σ (id C)
      middle = productFamily (α ▷ σ) (const (idIso (id C ∘ id C)))
      target = productFamily (α ▷ σ) identity
      reduce = const-cong (preWhisker-idIso (id C) (id C)) ∙ pre-constant (idIso (id C)) (id C)
      first = isoComp-cong (productFamily-cong (idIso (α ▷ σ)) reduce) (idIso _) ∙
        productMap-comp-family-outer σ (id C) α identity
      last = fixed-second-square (α ▷ σ) (comp-unitˡ (id C))
  in paste-family-squares
    (productMap-comp σ f (id C) (id C)) (productMap-comp σ g (id C) (id C))
    (productMap-cong (idIso (f ∘ σ)) (comp-unitˡ (id C)))
    (productMap-cong (idIso (g ∘ σ)) (comp-unitˡ (id C)))
    action middle target first last

post-family-square : {A X Y Z : CAT} {f f′ g g′ : MAP X Y}
  (u : MAP Y Z) (b : =₁ f g) (b′ : =₁ f′ g′)
  (α : MAP A (f ＝ f′)) (β : MAP A (g ＝ g′))
  → =₁ (const b′ ∙ α) (β ∙ const b)
  → =₁ (const (u ◁ b′) ∙ (u ◁ α)) ((u ◁ β) ∙ const (u ◁ b))
post-family-square u b b′ α β p =
  isoComp-cong (idIso _) (post-constant u b) ∙
  (post-composition u β (const b) ∙
  ((postWhisker u ◁ p) ∙
  (invIso (post-composition u (const b′) α) ∙
    isoComp-cong (invIso (post-constant u b′)) (idIso _))))

uncurry-pre-inputs : {A Y X C D : CAT} {f g : MAP X (Map C D)}
  (α : MAP A (f ＝ g)) (σ : MAP Y X)
  → =₁ (const (mapUncurry-pre g σ) ∙ uncurryFamily (α ▷ σ))
      ((uncurryFamily α ▷ productMap σ (id C)) ∙ const (mapUncurry-pre f σ))
uncurry-pre-inputs {C = C} {f = f} {g} α σ =
  let s = productMap σ (id C)
      pf = productMap f (id C)
      pg = productMap g (id C)
      pα = productFamily α (const (idIso (id C)))
      pασ = productFamily (α ▷ σ) (const (idIso (id C)))
      first = post-family-square mapEval
        (invIso (slice-comparison f σ)) (invIso (slice-comparison g σ)) pασ (pα ▷ s)
        (family-move-square (slice-comparison g σ) (pα ▷ s) pασ (slice-comparison f σ)
          (slice-comparison-inputs α σ))
      last = family-move-square (comp-assoc s pg mapEval)
        ((mapEval ◁ pα) ▷ s) (mapEval ◁ (pα ▷ s)) (comp-assoc s pf mapEval)
        (whisker-mixed-general pα s mapEval)
  in paste-family-squares
    (mapEval ◁ invIso (slice-comparison f σ)) (mapEval ◁ invIso (slice-comparison g σ))
    (invIso (comp-assoc s pf mapEval)) (invIso (comp-assoc s pg mapEval))
    (uncurryFamily (α ▷ σ)) (mapEval ◁ (pα ▷ s)) ((uncurryFamily α) ▷ s) first last

uncurryFamily-absolute : {X C D : CAT} {f g : MAP X (Map C D)} (α : =₁ f g)
  → =₂ (uncurryFamily α) (mapUncurryIso α)
uncurryFamily-absolute {C = C} α = invIso (mapUncurryIso-at α) ∙
  (postWhisker mapEval ◁ (productFamily-absolute α (idIso (id C)) ∙
    productFamily-cong (idIso α) (const-One (idIso (id C)))))

mapUncurry-pre-inputs : {Y X C D : CAT} {f g : MAP X (Map C D)}
  (α : =₁ f g) (σ : MAP Y X)
  → =₂ (mapUncurry-pre g σ ∙ mapUncurryIso (α ▷ σ))
      ((mapUncurryIso α ▷ productMap σ (id C)) ∙ mapUncurry-pre f σ)
mapUncurry-pre-inputs {C = C} {f = f} {g} α σ =
  isoComp-cong (preWhisker (productMap σ (id C)) ◁ uncurryFamily-absolute α)
    (const-One (mapUncurry-pre f σ)) ∙
  (uncurry-pre-inputs α σ ∙
    invIso (isoComp-cong (const-One (mapUncurry-pre g σ)) (uncurryFamily-absolute (α ▷ σ))))

slice-comparison-substitution : {A Y X Z C : CAT} (f : MAP X Z)
  {σ τ : MAP Y X} (γ : MAP A (σ ＝ τ))
  → =₁
      (const (slice-comparison {C = C} f τ) ∙
        (productMap f (id C) ◁ productFamily γ (const (idIso (id C)))))
      (productFamily (f ◁ γ) (const (idIso (id C))) ∙ const (slice-comparison f σ))
slice-comparison-substitution {C = C} f {σ} {τ} γ =
  let identity = const (idIso (id C))
      action = productMap f (id C) ◁ productFamily γ identity
      middle = productFamily (f ◁ γ) (const (idIso (id C ∘ id C)))
      target = productFamily (f ◁ γ) identity
      reduce = const-cong (postWhisker-idIso (id C) (id C)) ∙ post-constant (id C) (idIso (id C))
      first = isoComp-cong (productFamily-cong (idIso (f ◁ γ)) reduce) (idIso _) ∙
        productMap-comp-family-inner γ identity f (id C)
      last = fixed-second-square (f ◁ γ) (comp-unitˡ (id C))
  in paste-family-squares
    (productMap-comp σ f (id C) (id C)) (productMap-comp τ f (id C) (id C))
    (productMap-cong (idIso (f ∘ σ)) (comp-unitˡ (id C)))
    (productMap-cong (idIso (f ∘ τ)) (comp-unitˡ (id C)))
    action middle target first last

uncurry-pre-substitution : {A Y X C D : CAT} (f : MAP X (Map C D))
  {σ τ : MAP Y X} (γ : MAP A (σ ＝ τ))
  → =₁ (const (mapUncurry-pre f τ) ∙ uncurryFamily (f ◁ γ))
      ((mapUncurry f ◁ productFamily γ (const (idIso (id C)))) ∙ const (mapUncurry-pre f σ))
uncurry-pre-substitution {C = C} f {σ} {τ} γ =
  let s = productMap σ (id C)
      t = productMap τ (id C)
      pf = productMap f (id C)
      pγ = productFamily γ (const (idIso (id C)))
      pfγ = productFamily (f ◁ γ) (const (idIso (id C)))
      first = post-family-square mapEval
        (invIso (slice-comparison f σ)) (invIso (slice-comparison f τ)) pfγ (pf ◁ pγ)
        (family-move-square (slice-comparison f τ) (pf ◁ pγ) pfγ (slice-comparison f σ)
          (slice-comparison-substitution f γ))
      last = family-move-square (comp-assoc t pf mapEval)
        (mapUncurry f ◁ pγ) (mapEval ◁ (pf ◁ pγ)) (comp-assoc s pf mapEval)
        (postWhisker-comp-general pγ pf mapEval)
  in paste-family-squares
    (mapEval ◁ invIso (slice-comparison f σ)) (mapEval ◁ invIso (slice-comparison f τ))
    (invIso (comp-assoc s pf mapEval)) (invIso (comp-assoc t pf mapEval))
    (uncurryFamily (f ◁ γ)) (mapEval ◁ (pf ◁ pγ)) (mapUncurry f ◁ pγ) first last
```

Naturality in the two variables pastes to simultaneous naturality. This
uses preservation of vertical composition already proved above; it does
not infer a family of witnesses from its values at absolute points.

```agda

uncurry-pre-natural : {A Y X C D : CAT} {f g : MAP X (Map C D)} {σ τ : MAP Y X}
  (α : MAP A (f ＝ g)) (γ : MAP A (σ ＝ τ))
  → =₁ (const (mapUncurry-pre g τ) ∙ uncurryFamily (α ⋆ γ))
      ((uncurryFamily α ⋆ productFamily γ (const (idIso (id C)))) ∙ const (mapUncurry-pre f σ))
uncurry-pre-natural {C = C} {f = f} {g} {σ} {τ} α γ =
  let outer = uncurryFamily (α ▷ τ)
      inner = uncurryFamily (f ◁ γ)
      before = const (mapUncurry-pre f σ)
      middle = const (mapUncurry-pre f τ)
      after = const (mapUncurry-pre g τ)
      input = uncurryFamily α ▷ productMap τ (id C)
      substitution = mapUncurry f ◁ productFamily γ (const (idIso (id C)))
  in invIso (assoc input substitution before) ∙
    (isoComp-cong (idIso input) (uncurry-pre-substitution f γ) ∙
    (assoc input middle inner ∙
    (isoComp-cong (uncurry-pre-inputs α τ) (idIso inner) ∙
    (invIso (assoc after outer inner) ∙
      isoComp-cong (idIso after) (uncurryFamily-composition (α ▷ τ) (f ◁ γ))))))

module JointNaturality {Y X C D : CAT}
  (f g : MAP X (Map C D)) (σ τ : MAP Y X) where

  Parameter : CAT
  Parameter = (f ＝ g) × (σ ＝ τ)

  comparison : =₁
    (const (mapUncurry-pre g τ) ∙ uncurryFamily (pr₁ ⋆ pr₂))
    ((uncurryFamily pr₁ ⋆ productFamily pr₂ (const (idIso (id C)))) ∙
      const {P = Parameter} (mapUncurry-pre f σ))
  comparison = uncurry-pre-natural pr₁ pr₂
```

The remaining statements express these results directly using the actual
equality-anima functor from the mapping axiom. The absolute forms retain
the `=₂` witnesses required for later calculations with internal
composition. The last module displays the universal product for the
simultaneous composition law.

```agda

uncurry-pre-natural-action : {A Y X C D : CAT}
  {f g : MAP X (Map C D)} {σ τ : MAP Y X}
  (α : MAP A (f ＝ g)) (γ : MAP A (σ ＝ τ))
  → =₁
      (const (mapUncurry-pre g τ) ∙ (mapUncurry-isoMap (f ∘ σ) (g ∘ τ) ∘ (α ⋆ γ)))
      (((mapUncurry-isoMap f g ∘ α) ⋆ productFamily γ (const (idIso (id C)))) ∙
        const (mapUncurry-pre f σ))
uncurry-pre-natural-action {f = f} {g} {σ} {τ} α γ =
  isoComp-cong (hcomp-cong (invIso (uncurryFamily-at α)) (idIso _)) (idIso _) ∙
    (uncurry-pre-natural α γ ∙ isoComp-cong (idIso _) (uncurryFamily-at (α ⋆ γ)))

productFamily-single-absolute : {X Y C : CAT} {σ τ : MAP Y X} (γ : =₁ σ τ)
  → =₂ (productFamily γ (const (idIso (id C)))) (productMap-cong γ (idIso (id C)))
productFamily-single-absolute {C = C} γ = productFamily-absolute γ (idIso (id C)) ∙
  productFamily-cong (idIso γ) (const-One (idIso (id C)))

mapUncurry-pre-substitution : {Y X C D : CAT} (f : MAP X (Map C D))
  {σ τ : MAP Y X} (γ : =₁ σ τ)
  → =₂ (mapUncurry-pre f τ ∙ mapUncurryIso (f ◁ γ))
      ((mapUncurry f ◁ productMap-cong γ (idIso (id C))) ∙ mapUncurry-pre f σ)
mapUncurry-pre-substitution f {σ} {τ} γ =
  isoComp-cong (postWhisker (mapUncurry f) ◁ productFamily-single-absolute γ)
    (const-One (mapUncurry-pre f σ)) ∙
  (uncurry-pre-substitution f γ ∙
    invIso (isoComp-cong (const-One (mapUncurry-pre f τ)) (uncurryFamily-absolute (f ◁ γ))))

mapUncurry-pre-natural : {Y X C D : CAT}
  {f g : MAP X (Map C D)} {σ τ : MAP Y X}
  (α : =₁ f g) (γ : =₁ σ τ)
  → =₂ (mapUncurry-pre g τ ∙ mapUncurryIso (α ⋆ γ))
      ((mapUncurryIso α ⋆ productMap-cong γ (idIso (id C))) ∙ mapUncurry-pre f σ)
mapUncurry-pre-natural {f = f} {g} {σ} {τ} α γ =
  isoComp-cong (hcomp-cong (uncurryFamily-absolute α) (productFamily-single-absolute γ))
    (const-One (mapUncurry-pre f σ)) ∙
  (uncurry-pre-natural α γ ∙
    invIso (isoComp-cong (const-One (mapUncurry-pre g τ)) (uncurryFamily-absolute (α ⋆ γ))))

mapUncurry-action-identity : {A X C D : CAT} (f : MAP X (Map C D))
  → =₁ (mapUncurry-isoMap f f ∘ const {P = A} (idIso f)) (const (idIso (mapUncurry f)))
mapUncurry-action-identity f = uncurryFamily-identity f ∙ uncurryFamily-at (const (idIso f))

mapUncurry-action-composition : {A X C D : CAT} {f g h : MAP X (Map C D)}
  (β : MAP A (g ＝ h)) (α : MAP A (f ＝ g))
  → =₁ (mapUncurry-isoMap f h ∘ (β ∙ α))
      ((mapUncurry-isoMap g h ∘ β) ∙ (mapUncurry-isoMap f g ∘ α))
mapUncurry-action-composition β α =
  invIso (isoComp-cong (uncurryFamily-at β) (uncurryFamily-at α)) ∙
    (uncurryFamily-composition β α ∙ uncurryFamily-at (β ∙ α))

module JointComposition {X C D : CAT} (f g h : MAP X (Map C D)) where

  Parameter : CAT
  Parameter = (g ＝ h) × (f ＝ g)

  comparison : =₁ (mapUncurry-isoMap f h ∘ (pr₁ ∙ pr₂))
    ((mapUncurry-isoMap g h ∘ pr₁) ∙ (mapUncurry-isoMap f g ∘ pr₂))
  comparison = mapUncurry-action-composition {A = Parameter} pr₁ pr₂
```
