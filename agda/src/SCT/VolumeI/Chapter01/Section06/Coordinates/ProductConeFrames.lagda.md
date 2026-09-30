# Specified frames of product cones

Restriction of a product cone along a pair has the literal
productMap-pair comparisons on its two legs. Paired cone matchings also
compute against these same comparisons. Both calculations retain the
chosen matching, rather than using uniqueness of the product object.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)

module SCT.VolumeI.Chapter01.Section06.Coordinates.ProductConeFrames
  {c m a : Level} (𝒯 : Theory c m a) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeRestriction 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeAction 𝒯 using (cone-action)
open import SCT.VolumeI.Chapter01.Section03.ProductCalculus.ProductPairing
  vocabulary terminal products productLaws composition vertical whiskering using (productMap-pair)
open import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingCoherence
  vocabulary terminal products productLaws composition vertical whiskering
  using (pair-iso-extensionality; pair-cong-triangle₁; pair-cong-triangle₂)
open import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Inverses
  vocabulary terminal products productLaws composition vertical
  using (cancel-left; cancel-left-reflect)
import SCT.VolumeI.Chapter01.Section06.Coordinates.ProductCones as Products
import SCT.VolumeI.Chapter01.Section06.Coordinates.ProductFamilyFrames as Frames

private
  flatten-square : {X Y : CAT} {l r l′ r′ u v : MAP X Y}
    (L : l =₁ l′) (R : r =₁ r′) (μ : l =₁ r)
    (a : l′ =₁ u) (b : r′ =₁ v) (ω : u =₁ v) →
    (ω ∙ a) =₂ (b ∙ (R ∙ (μ ∙ L ⁻¹))) →
    (ω ∙ (a ∙ L)) =₂ ((b ∙ R) ∙ μ)
  flatten-square L R μ a b ω square =
    (isoComp-assoc-at b R μ) ⁻¹ ∙
    (isoComp-cong (idIso b) (isoComp-cong (idIso R) cancel) ∙
    (isoComp-cong (idIso b) (isoComp-assoc-at R (μ ∙ L ⁻¹) L) ∙
    (isoComp-assoc-at b (R ∙ (μ ∙ L ⁻¹)) L ∙
    (isoComp-cong square (idIso L) ∙ (isoComp-assoc-at ω a L) ⁻¹))))
    where
    cancel = isoComp-unitʳ-at μ ∙
      (isoComp-cong (idIso μ) (isoComp-inverseˡ-at L) ∙ isoComp-assoc-at μ (L ⁻¹) L)

  coordinate-square : {B E E′ : CAT} (π : MAP E E′)
    {l r u v : MAP B E} {l′ r′ x y : MAP B E′}
    (U : l =₁ u) (V : r =₁ v) (m : u =₁ v) (μ : l =₁ r)
    (L : (π ∘ l) =₁ l′) (R : (π ∘ r) =₁ r′)
    (a : l′ =₁ x) (b : r′ =₁ y) (ω : x =₁ y)
    (βU : (π ∘ u) =₁ x) (βV : (π ∘ v) =₁ y) →
    (βU ∙ (π ◁ U)) =₂ (a ∙ L) →
    (βV ∙ (π ◁ V)) =₂ (b ∙ R) →
    (βV ∙ (π ◁ m)) =₂ (ω ∙ βU) →
    (ω ∙ a) =₂ (b ∙ (R ∙ ((π ◁ μ) ∙ L ⁻¹))) →
    (π ◁ (V ∙ μ)) =₂ (π ◁ (m ∙ U))
  coordinate-square π U V m μ L R a b ω βU βV left right middle square =
    cancel-left-reflect βV
      (isoComp-cong (idIso βV) ((postWhisker-isoComp-at π m U) ⁻¹) ∙
      (isoComp-assoc-at βV (π ◁ m) (π ◁ U) ∙
      (isoComp-cong (middle ⁻¹) (idIso (π ◁ U)) ∙
      ((isoComp-assoc-at ω βU (π ◁ U)) ⁻¹ ∙
      (isoComp-cong (idIso ω) (left ⁻¹) ∙
      ((flatten-square L R (π ◁ μ) a b ω square) ⁻¹ ∙
      (isoComp-cong right (idIso (π ◁ μ)) ∙
      ((isoComp-assoc-at βV (π ◁ V) (π ◁ μ)) ⁻¹ ∙
        isoComp-cong (idIso βV) (postWhisker-isoComp-at π V μ)))))))))

module Paired {C₀ C₁ D₀ D₁ E₀ E₁ B : CAT}
  {f₀ : MAP C₀ E₀} {f₁ : MAP C₁ E₁} {g₀ : MAP D₀ E₀} {g₁ : MAP D₁ E₁}
  (s₀ : Cone f₀ g₀ B) (s₁ : Cone f₁ g₁ B) where
  private
    module Product = Products.Coordinates 𝒯 f₀ f₁ g₀ g₁ using (module Paired; module First; module Second)
    module Pair = Product.Paired s₀ s₁ using (cone; first; second; p; q; l₀; l₁; r₀; r₁)
    module Left = Frames.Paired 𝒯 f₀ f₁ (Cone.left s₀) (Cone.left s₁)
      using (first-triangle; second-triangle)
    module Right = Frames.Paired 𝒯 g₀ g₁ (Cone.right s₀) (Cone.right s₁)
      using (first-triangle; second-triangle)
  left = productMap-pair f₀ f₁ (Cone.left s₀) (Cone.left s₁)
  right = productMap-pair g₀ g₁ (Cone.right s₀) (Cone.right s₁)
  paired-match = pair-cong (Cone.match s₀) (Cone.match s₁)

  matching-computation : (right ∙ Cone.match Pair.cone) =₂ (paired-match ∙ left)
  matching-computation = pair-iso-extensionality
    (coordinate-square pr₁ left right paired-match (Cone.match Pair.cone)
      (Product.First.left-normal Pair.p) (Product.First.right-normal Pair.q)
      (f₀ ◁ Pair.l₀) (g₀ ◁ Pair.r₀) (Cone.match s₀)
      (pair-β₁ (f₀ ∘ Cone.left s₀) (f₁ ∘ Cone.left s₁))
      (pair-β₁ (g₀ ∘ Cone.right s₀) (g₁ ∘ Cone.right s₁))
      Left.first-triangle Right.first-triangle
      (pair-cong-triangle₁ (Cone.match s₀) (Cone.match s₁)) (ConeIso.compatible Pair.first))
    (coordinate-square pr₂ left right paired-match (Cone.match Pair.cone)
      (Product.Second.left-normal Pair.p) (Product.Second.right-normal Pair.q)
      (f₁ ◁ Pair.l₁) (g₁ ◁ Pair.r₁) (Cone.match s₁)
      (pair-β₂ (f₀ ∘ Cone.left s₀) (f₁ ∘ Cone.left s₁))
      (pair-β₂ (g₀ ∘ Cone.right s₀) (g₁ ∘ Cone.right s₁))
      Left.second-triangle Right.second-triangle
      (pair-cong-triangle₂ (Cone.match s₀) (Cone.match s₁)) (ConeIso.compatible Pair.second))

module Restricted {C D E S B : CAT} {f : MAP C E} {g : MAP D E}
  (s : Cone f g S) (x y : MAP B S) where
  private
    p = Cone.left s
    q = Cone.right s
    h = pair x y
    module Product = Products.Coordinates 𝒯 f f g g
      using (module First; module Second; module Paired; reflect)
    module Source = Product.Paired (conePre pr₁ s) (conePre pr₂ s)
      using (cone; first; second)
    module Target = Product.Paired (conePre x s) (conePre y s)
      using (cone; first; second; l₀; l₁; r₀; r₁)
    module Left = Frames.Paired 𝒯 p p x y using (first-triangle; second-triangle)
    module Right = Frames.Paired 𝒯 q q x y using (first-triangle; second-triangle)
  source = conePre h Source.cone
  target = Target.cone
  left = productMap-pair p p x y
  right = productMap-pair q q x y

  private
    first : ConeIso (Product.First.read source) (conePre x s)
    first = coneIso-compose (cone-action s (pair-β₁ x y))
      (coneIso-compose (conePre-assoc h pr₁ s)
        (coneIso-compose (coneIso-pre h Source.first) (Product.First.read-pre h Source.cone)))
    second : ConeIso (Product.Second.read source) (conePre y s)
    second = coneIso-compose (cone-action s (pair-β₂ x y))
      (coneIso-compose (conePre-assoc h pr₂ s)
        (coneIso-compose (coneIso-pre h Source.second) (Product.Second.read-pre h Source.cone)))

    first-left : ConeIso.leftIso first =₂ (Target.l₀ ∙ (pr₁ ◁ left))
    first-left = Left.first-triangle ⁻¹
    first-right : ConeIso.rightIso first =₂ (Target.r₀ ∙ (pr₁ ◁ right))
    first-right = Right.first-triangle ⁻¹
    second-left : ConeIso.leftIso second =₂ (Target.l₁ ∙ (pr₂ ◁ left))
    second-left = Left.second-triangle ⁻¹
    second-right : ConeIso.rightIso second =₂ (Target.r₁ ∙ (pr₂ ◁ right))
    second-right = Right.second-triangle ⁻¹

    raw = Product.reflect (coneIso-compose (coneIso-inverse Target.first) first)
      (coneIso-compose (coneIso-inverse Target.second) second)
    left-computation : ConeIso.leftIso raw =₂ left
    left-computation = pair-iso-extensionality
      (cancel-left Target.l₀ (pr₁ ◁ left) ∙
        (isoComp-cong (idIso (Target.l₀ ⁻¹)) first-left ∙ pair-iso-β₁ _ _))
      (cancel-left Target.l₁ (pr₂ ◁ left) ∙
        (isoComp-cong (idIso (Target.l₁ ⁻¹)) second-left ∙ pair-iso-β₂ _ _))
    right-computation : ConeIso.rightIso raw =₂ right
    right-computation = pair-iso-extensionality
      (cancel-left Target.r₀ (pr₁ ◁ right) ∙
        (isoComp-cong (idIso (Target.r₀ ⁻¹)) first-right ∙ pair-iso-β₁ _ _))
      (cancel-left Target.r₁ (pr₂ ◁ right) ∙
        (isoComp-cong (idIso (Target.r₁ ⁻¹)) second-right ∙ pair-iso-β₂ _ _))

  comparison : ConeIso source target
  comparison = coneIso-adjust raw left right left-computation right-computation
```
