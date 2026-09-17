# The parameter coordinate of mixed product substitution

The first projection of a product restriction preserves the parameter.
For a change of parameter `h`, its target is postcomposed with `h`.
The existing calculus of projection-preserving squares then handles
the whole pasted diagram.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section03.ProjectionSquares as Projections
import SCT.VolumeI.Chapter01.Section08.ProductComparisonProjections as Compositors
import SCT.VolumeI.Chapter01.Section08.ProductSeparationProjections as Separations
import SCT.VolumeI.Chapter01.Section02.PairingNaturality as PN

module SCT.VolumeI.Chapter01.Section08.ProductFirstCoordinate
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section08.ProductSquares 𝒯
open import SCT.VolumeI.Chapter01.Section03.ParameterSquarePasting 𝒯 using (paste)
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-left-reflect)
module PS = Projections 𝒯

restriction-base : (X : CAT) {A B : CAT} (f : MAP A B) → NatIso (pr₁ ∘ productRestriction X f) pr₁
restriction-base X f = comp-unitˡ pr₁ ∙ pair-β₁ (id X ∘ pr₁) (f ∘ pr₂)

parameter-base : {X Y : CAT} (h : MAP X Y) (A : CAT) →
  NatIso (pr₁ ∘ productMap h (id A)) (h ∘ pr₁)
parameter-base h A = pair-β₁ (h ∘ pr₁) (id A ∘ pr₂)

restriction-over : {X Y A B : CAT} (h : MAP X Y) (f : MAP A B) →
  NatIso ((h ∘ pr₁) ∘ productRestriction X f) (h ∘ pr₁)
restriction-over {X} h f = PS.lift-base h pr₁ (productRestriction X f) (restriction-base X f)

compositor : {A B C : CAT} (X : CAT) (f : MAP A B) (g : MAP B C) →
  PS.Square pr₁
    (PS.compose-base pr₁ (productRestriction X g) (restriction-base X g) (productRestriction X f) (restriction-base X f))
    (restriction-base X (g ∘ f)) (productRestriction-comp X f g)
compositor {A} {B} X f g =
  isoComp-cong (idIso (restriction-base X f))
    (isoComp-cong (invIso (preWhisker-isoComp-at unitB bg input)) (idIso tail)) ∙
  (isoComp-cong (idIso (restriction-base X f)) (invIso (isoComp-assoc-at (unitB ▷ input) (bg ▷ input) tail)) ∙
  (invIso (isoComp-assoc-at unitA bf ((unitB ▷ input) ∙ ((bg ▷ input) ∙ tail))) ∙
  (isoComp-cong (idIso unitA) (isoComp-assoc-at bf (unitB ▷ input) ((bg ▷ input) ∙ tail)) ∙
  (isoComp-cong (idIso unitA) (Compositors.Restriction.projection₁ 𝒯 X f g) ∙
    isoComp-assoc-at unitA bgf (pr₁ ◁ productRestriction-comp X f g)))))
  where
  input = productRestriction X f
  outer = productRestriction X g
  unitA = comp-unitˡ (pr₁ {X} {A})
  unitB = comp-unitˡ (pr₁ {X} {B})
  bf = pair-β₁ (id X ∘ pr₁) (f ∘ pr₂)
  bg = pair-β₁ (id X ∘ pr₁) (g ∘ pr₂)
  bgf = pair-β₁ (id X ∘ pr₁) ((g ∘ f) ∘ pr₂)
  tail = invIso (comp-assoc input outer pr₁)

compositor-over : {X Y A B C : CAT} (h : MAP X Y) (f : MAP A B) (g : MAP B C) →
  PS.Square (h ∘ pr₁)
    (PS.compose-base (h ∘ pr₁) (productRestriction X g) (restriction-over h g)
      (productRestriction X f) (restriction-over h f))
    (restriction-over h (g ∘ f)) (productRestriction-comp X f g)
compositor-over {X} h f g =
  invIso (PS.lift-compose h pr₁ (productRestriction X g) (productRestriction X f) (restriction-base X g) (restriction-base X f)) ∙
    PS.lift-square h pr₁
      (PS.compose-base pr₁ (productRestriction X g) (restriction-base X g) (productRestriction X f) (restriction-base X f))
      (restriction-base X (g ∘ f)) (productRestriction-comp X f g) (compositor X f g)

separation : {X Y A B : CAT} (h : MAP X Y) (f : MAP A B) →
  PS.Square pr₁
    (PS.compose-base pr₁ (productRestriction Y f) (restriction-base Y f) (productMap h (id A)) (parameter-base h A))
    (PS.compose-base pr₁ (productMap h (id B)) (parameter-base h B) (productRestriction X f) (restriction-over h f))
    (productMap-separate h f)
separation {X} {Y} {A} h f = normalize ∙ Separations.Separation.projection₁ 𝒯 M h f
  where
  HA = productMap h (id A)
  unit = comp-unitˡ pr₁
  β = pair-β₁ (id Y ∘ pr₁) (f ∘ pr₂)
  tail = invIso (comp-assoc HA (productRestriction Y f) pr₁)
  normalize = isoComp-cong (idIso (parameter-base h A))
    (isoComp-cong (invIso (preWhisker-isoComp-at unit β HA)) (idIso tail)) ∙
    (isoComp-cong (idIso (parameter-base h A)) (invIso (isoComp-assoc-at (unit ▷ HA) (β ▷ HA) tail)) ∙
      isoComp-assoc-at (parameter-base h A) (unit ▷ HA) ((β ▷ HA) ∙ tail))

module Mixed {X Y A B C : CAT} (h : MAP X Y) (f : MAP A B) (g : MAP B C) where
  HA = productMap h (id A)
  HB = productMap h (id B)
  HC = productMap h (id C)
  Xf = productRestriction X f
  Xg = productRestriction X g
  Yf = productRestriction Y f
  Yg = productRestriction Y g
  Xgf = productRestriction X (g ∘ f)
  Ygf = productRestriction Y (g ∘ f)
  χX = productRestriction-comp X f g
  χY = productRestriction-comp Y f g
  Sf = productMap-separate h f
  Sg = productMap-separate h g
  Sgf = productMap-separate h (g ∘ f)

  module Diagram = PS.Pasting (h ∘ pr₁) (h ∘ pr₁) (h ∘ pr₁) pr₁ pr₁ pr₁
    HA HB HC Xf Xg Yf Yg (restriction-over h f) (restriction-over h g)
    (restriction-base Y f) (restriction-base Y g) (parameter-base h A) (parameter-base h B) (parameter-base h C)
    (invIso Sf) (invIso Sg)
  final = PS.compose-base pr₁ Ygf (restriction-base Y (g ∘ f)) HA (parameter-base h A)
  middle = PS.compose-base pr₁ HC (parameter-base h C) Xgf (restriction-over h (g ∘ f))

  short = (χY ▷ HA) ∙ paste (invIso Sg) (invIso Sf)
  long = invIso Sgf ∙ (HC ◁ χX)

  abstract
    short-square : PS.Square pr₁ Diagram.b₀ final short
    short-square = PS.compose-square pr₁ Diagram.b₀ Diagram.b₅ final (χY ▷ HA)
      (paste (invIso Sg) (invIso Sf))
      (PS.pre-square pr₁ HA
        (PS.compose-base pr₁ Yg (restriction-base Y g) Yf (restriction-base Y f))
        (restriction-base Y (g ∘ f)) (parameter-base h A) χY (compositor Y f g))
      (Diagram.paste-square
        (PS.inverse-square pr₁ _ _ Sf (separation h f))
        (PS.inverse-square pr₁ _ _ Sg (separation h g)))

    long-square : PS.Square pr₁ Diagram.b₀ final long
    long-square = PS.compose-square pr₁ Diagram.b₀ middle final (invIso Sgf) (HC ◁ χX)
      (PS.inverse-square pr₁ _ _ Sgf (separation h (g ∘ f)))
      (PS.post-square pr₁ HC (parameter-base h C)
        (PS.compose-base (h ∘ pr₁) Xg (restriction-over h g) Xf (restriction-over h f))
        (restriction-over h (g ∘ f)) χX (compositor-over h f g))

    comparison : Iso₂ (pr₁ ◁ short) (pr₁ ◁ long)
    comparison = cancel-left-reflect final (invIso long-square ∙ short-square)
```



