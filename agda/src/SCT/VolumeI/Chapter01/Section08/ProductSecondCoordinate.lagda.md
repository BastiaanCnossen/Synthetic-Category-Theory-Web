# The varying coordinate of mixed product substitution

For two composable functors, all projection witnesses can be given their
common final target. The first source projection is postcomposed twice.
The specified associator compares that witness with direct postcomposition
by the composite functor.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section03.ProjectionSquares as Projections
import SCT.VolumeI.Chapter01.Section08.ProductComparisonProjections as Compositors
import SCT.VolumeI.Chapter01.Section08.ProductSeparationProjections as Separations
import SCT.VolumeI.Chapter01.Section02.PairingNaturality as PN
import SCT.VolumeI.Chapter01.Section01.Isomorphisms as Isomorphisms

module SCT.VolumeI.Chapter01.Section08.ProductSecondCoordinate
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section08.ProductSquares 𝒯
open import SCT.VolumeI.Chapter01.Section08.ProjectionBaseCalculus 𝒯
open import SCT.VolumeI.Chapter01.Section03.ParameterSquarePasting 𝒯 using (paste)
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-left-reflect)
open Isomorphisms vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)
module PS = Projections 𝒯

restriction-base : (X : CAT) {A B : CAT} (f : MAP A B) →
  =₁ (pr₂ ∘ productRestriction X f) (f ∘ pr₂)
restriction-base X f = pair-β₂ (id X ∘ pr₁) (f ∘ pr₂)

parameter-base : {X Y : CAT} (h : MAP X Y) (A : CAT) →
  =₁ (pr₂ ∘ productMap h (id A)) pr₂
parameter-base h A = comp-unitˡ pr₂ ∙ pair-β₂ (h ∘ pr₁) (id A ∘ pr₂)

restriction-over : {A B C : CAT} (X : CAT) (f : MAP A B) (g : MAP B C) →
  =₁ ((g ∘ pr₂) ∘ productRestriction X f) (g ∘ (f ∘ pr₂))
restriction-over X f g = PS.lift-base g pr₂ (productRestriction X f) (restriction-base X f)

composite-base : {A B C : CAT} (X : CAT) (f : MAP A B) (g : MAP B C) →
  =₁ (pr₂ ∘ productRestriction X (g ∘ f)) (g ∘ (f ∘ pr₂))
composite-base X f g = comp-assoc pr₂ f g ∙ restriction-base X (g ∘ f)

compositor : {A B C : CAT} (X : CAT) (f : MAP A B) (g : MAP B C) →
  PS.Square pr₂
    (PS.compose-base pr₂ (productRestriction X g) (restriction-base X g)
      (productRestriction X f) (restriction-over X f g))
    (composite-base X f g) (productRestriction-comp X f g)
compositor X f g = isoComp-cong (cancel-inverse A U) (idIso T) ∙
  (invIso (isoComp-assoc-at A (invIso A ∙ U) T) ∙
  (isoComp-cong (idIso A) (Compositors.Restriction.projection₂ 𝒯 X f g) ∙
    isoComp-assoc-at A (restriction-base X (g ∘ f)) (pr₂ ◁ productRestriction-comp X f g)))
  where
  A = comp-assoc pr₂ f g
  U = restriction-over X f g
  T = (restriction-base X g ▷ productRestriction X f) ∙
    invIso (comp-assoc (productRestriction X f) (productRestriction X g) pr₂)

separation : {X Y A B : CAT} (h : MAP X Y) (f : MAP A B) →
  PS.Square pr₂
    (PS.compose-base pr₂ (productRestriction Y f) (restriction-base Y f)
      (productMap h (id A)) (PS.lift-base f pr₂ (productMap h (id A)) (parameter-base h A)))
    (PS.compose-base pr₂ (productMap h (id B)) (parameter-base h B)
      (productRestriction X f) (restriction-base X f))
    (productMap-separate h f)
separation {X} {Y} {A} {B} h f = Separations.Separation.projection₂ 𝒯 M h f ∙
  isoComp-cong (invIso normalize) (idIso (pr₂ ◁ productMap-separate h f))
  where
  input = productRestriction X f
  HB = productMap h (id B)
  unit = comp-unitˡ pr₂
  β = pair-β₂ (h ∘ pr₁) (id B ∘ pr₂)
  tail = invIso (comp-assoc input HB pr₂)
  normalize = isoComp-cong (idIso (restriction-base X f))
    (isoComp-cong (invIso (preWhisker-isoComp-at unit β input)) (idIso tail)) ∙
    (isoComp-cong (idIso (restriction-base X f)) (invIso (isoComp-assoc-at (unit ▷ input) (β ▷ input) tail)) ∙
      isoComp-assoc-at (restriction-base X f) (unit ▷ input) ((β ▷ input) ∙ tail))

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
  bHA = PS.lift-base g (f ∘ pr₂) HA (PS.lift-base f pr₂ HA (parameter-base h A))
  bHB = PS.lift-base g pr₂ HB (parameter-base h B)
  bHC = parameter-base h C
  bXf = restriction-over X f g
  bYf = restriction-over Y f g
  bXg = restriction-base X g
  bYg = restriction-base Y g

  first-source = PS.compose-base (g ∘ pr₂) Yf bYf HA bHA
  first-target = PS.compose-base (g ∘ pr₂) HB bHB Xf bXf

  first-square : PS.Square (g ∘ pr₂) first-source first-target Sf
  first-square = invIso (PS.lift-compose g pr₂ Yf HA (restriction-base Y f)
      (PS.lift-base f pr₂ HA (parameter-base h A))) ∙
    (PS.lift-square g pr₂
      (PS.compose-base pr₂ Yf (restriction-base Y f) HA (PS.lift-base f pr₂ HA (parameter-base h A)))
      (PS.compose-base pr₂ HB (parameter-base h B) Xf (restriction-base X f)) Sf (separation h f) ∙
      isoComp-cong (PS.lift-compose g pr₂ HB Xf (parameter-base h B) (restriction-base X f))
        (idIso ((g ∘ pr₂) ◁ Sf)))

  module Diagram = PS.Pasting (g ∘ (f ∘ pr₂)) (g ∘ pr₂) pr₂
    (g ∘ (f ∘ pr₂)) (g ∘ pr₂) pr₂ HA HB HC Xf Xg Yf Yg
    bXf bXg bYf bYg bHA bHB bHC (invIso Sf) (invIso Sg)
  final = PS.compose-base pr₂ Ygf (composite-base Y f g) HA bHA
  middle = PS.compose-base pr₂ HC bHC Xgf (composite-base X f g)
  oldSource = PS.compose-base pr₂ Ygf (restriction-base Y (g ∘ f)) HA
    (PS.lift-base (g ∘ f) pr₂ HA (parameter-base h A))
  oldTarget = PS.compose-base pr₂ HC bHC Xgf (restriction-base X (g ∘ f))
  η = comp-assoc (pr₂ {X} {A}) f g

  composite-source : =₂ final (η ∙ oldSource)
  composite-source = change-middle pr₂ Ygf HA (restriction-base Y (g ∘ f))
    (PS.lift-base (g ∘ f) pr₂ HA (parameter-base h A)) (comp-assoc pr₂ f g) bHA η
    (lift-assoc pr₂ pr₂ HA (parameter-base h A) f g)

  composite-target : =₂ middle (η ∙ oldTarget)
  composite-target = isoComp-assoc-at η (restriction-base X (g ∘ f))
    ((bHC ▷ Xgf) ∙ invIso (comp-assoc Xgf HC pr₂))

  composite-square : PS.Square pr₂ final middle Sgf
  composite-square = invIso composite-source ∙
    (isoComp-cong (idIso η) (separation h (g ∘ f)) ∙
    (isoComp-assoc-at η oldTarget (pr₂ ◁ Sgf) ∙
      isoComp-cong composite-target (idIso (pr₂ ◁ Sgf))))

  short = (χY ▷ HA) ∙ paste (invIso Sg) (invIso Sf)
  long = invIso Sgf ∙ (HC ◁ χX)

  abstract
    short-square : PS.Square pr₂ Diagram.b₀ final short
    short-square = PS.compose-square pr₂ Diagram.b₀ Diagram.b₅ final (χY ▷ HA)
      (paste (invIso Sg) (invIso Sf))
      (PS.pre-square pr₂ HA (PS.compose-base pr₂ Yg bYg Yf bYf)
        (composite-base Y f g) bHA χY (compositor Y f g))
      (Diagram.paste-square (PS.inverse-square (g ∘ pr₂) _ _ Sf first-square)
        (PS.inverse-square pr₂ _ _ Sg (separation h g)))

    long-square : PS.Square pr₂ Diagram.b₀ final long
    long-square = PS.compose-square pr₂ Diagram.b₀ middle final (invIso Sgf) (HC ◁ χX)
      (PS.inverse-square pr₂ _ _ Sgf composite-square)
      (PS.post-square pr₂ HC bHC (PS.compose-base pr₂ Xg bXg Xf bXf)
        (composite-base X f g) χX (compositor X f g))

    comparison : =₂ (pr₂ ◁ short) (pr₂ ◁ long)
    comparison = cancel-left-reflect final (invIso long-square ∙ short-square)
```
