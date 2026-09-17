# The first coordinate of successive parameter changes

The two parameter changes are composed in the first coordinate. We give
each projection its common final target, then compare the pasted squares
with the square for the composite parameter change.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section03.ProjectionSquares as Projections
import SCT.VolumeI.Chapter01.Section03.ProductSubstitution as Substitution
import SCT.VolumeI.Chapter01.Section08.ProductFirstCoordinate as First
import SCT.VolumeI.Chapter01.Section02.PairingNaturality as PN
import SCT.VolumeI.Chapter01.Section01.Isomorphisms as Isomorphisms

module SCT.VolumeI.Chapter01.Section08.ParameterFirstCoordinate
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section03.Compatibility 𝒯 M using (slice-comparison)
open import SCT.VolumeI.Chapter01.Section08.ProductSquares 𝒯
open import SCT.VolumeI.Chapter01.Section08.ProjectionBaseCalculus 𝒯
open import SCT.VolumeI.Chapter01.Section03.ParameterSquarePasting 𝒯 using (paste)
open First 𝒯 M using (restriction-base; parameter-base; restriction-over; separation)
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-left-reflect)
open Isomorphisms vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)
module PS = Projections 𝒯

parameter-over : {X Y Z : CAT} (h : MAP X Y) (k : MAP Y Z) (A : CAT) →
  NatIso ((k ∘ pr₁) ∘ productMap h (id A)) (k ∘ (h ∘ pr₁))
parameter-over h k A = PS.lift-base k pr₁ (productMap h (id A)) (parameter-base h A)

composite-base : {X Y Z : CAT} (h : MAP X Y) (k : MAP Y Z) (A : CAT) →
  NatIso (pr₁ ∘ productMap (k ∘ h) (id A)) (k ∘ (h ∘ pr₁))
composite-base h k A = comp-assoc pr₁ h k ∙ parameter-base (k ∘ h) A

compositor : {X Y Z : CAT} (h : MAP X Y) (k : MAP Y Z) (A : CAT) →
  PS.Square pr₁
    (PS.compose-base pr₁ (productMap k (id A)) (parameter-base k A)
      (productMap h (id A)) (parameter-over h k A))
    (composite-base h k A) (slice-comparison {C = A} k h)
compositor h k A = isoComp-cong (cancel-inverse η U) (idIso T) ∙
  (invIso (isoComp-assoc-at η (invIso η ∙ U) T) ∙
  (isoComp-cong (idIso η) (Substitution.Coordinates.projection₁ 𝒯 M A k h) ∙
    isoComp-assoc-at η (parameter-base (k ∘ h) A) (pr₁ ◁ slice-comparison {C = A} k h)))
  where
  η = comp-assoc pr₁ h k
  U = parameter-over h k A
  T = (parameter-base k A ▷ productMap h (id A)) ∙
    invIso (comp-assoc (productMap h (id A)) (productMap k (id A)) pr₁)

module Mixed {X Y Z A B : CAT} (h : MAP X Y) (k : MAP Y Z) (f : MAP A B) where
  HA = productMap h (id A)
  HB = productMap h (id B)
  KA = productMap k (id A)
  KB = productMap k (id B)
  KHA = productMap (k ∘ h) (id A)
  KHB = productMap (k ∘ h) (id B)
  Xf = productRestriction X f
  Yf = productRestriction Y f
  Zf = productRestriction Z f
  κA = slice-comparison {C = A} k h
  κB = slice-comparison {C = B} k h
  Sh = productMap-separate h f
  Sk = productMap-separate k f
  Skh = productMap-separate (k ∘ h) f
  bHA = parameter-over h k A
  bHB = parameter-over h k B
  bKA = parameter-base k A
  bKB = parameter-base k B
  bXf = PS.lift-base k (h ∘ pr₁) Xf (restriction-over h f)
  bYf = restriction-over k f
  bZf = restriction-base Z f

  first-source = PS.compose-base (k ∘ pr₁) Yf bYf HA bHA
  first-target = PS.compose-base (k ∘ pr₁) HB bHB Xf bXf

  first-square : PS.Square (k ∘ pr₁) first-source first-target Sh
  first-square = invIso (PS.lift-compose k pr₁ Yf HA (restriction-base Y f) (parameter-base h A)) ∙
    (PS.lift-square k pr₁
      (PS.compose-base pr₁ Yf (restriction-base Y f) HA (parameter-base h A))
      (PS.compose-base pr₁ HB (parameter-base h B) Xf (restriction-over h f)) Sh
      (separation h f) ∙
      isoComp-cong (PS.lift-compose k pr₁ HB Xf (parameter-base h B) (restriction-over h f))
        (idIso ((k ∘ pr₁) ◁ Sh)))
  module Diagram = PS.Pasting (k ∘ (h ∘ pr₁)) (k ∘ pr₁) pr₁
    (k ∘ (h ∘ pr₁)) (k ∘ pr₁) pr₁ Xf Yf Zf HA KA HB KB
    bHA bKA bHB bKB bXf bYf bZf Sh Sk
  final = PS.compose-base pr₁ KHB (composite-base h k B) Xf bXf
  middle = PS.compose-base pr₁ Zf bZf KHA (composite-base h k A)
  oldSource = PS.compose-base pr₁ KHB (parameter-base (k ∘ h) B) Xf (restriction-over (k ∘ h) f)
  oldTarget = PS.compose-base pr₁ Zf bZf KHA (parameter-base (k ∘ h) A)
  η = comp-assoc (pr₁ {X} {A}) h k

  composite-source : Iso₂ final (η ∙ oldSource)
  composite-source = change-middle pr₁ KHB Xf (parameter-base (k ∘ h) B)
    (restriction-over (k ∘ h) f) (comp-assoc pr₁ h k) bXf η
    (lift-assoc pr₁ pr₁ Xf (restriction-base X f) h k)

  composite-target : Iso₂ middle (η ∙ oldTarget)
  composite-target = isoComp-assoc-at η (parameter-base (k ∘ h) A)
    ((bZf ▷ KHA) ∙ invIso (comp-assoc KHA Zf pr₁))

  composite-square : PS.Square pr₁ middle final Skh
  composite-square = invIso composite-target ∙
    (isoComp-cong (idIso η) (separation (k ∘ h) f) ∙
    (isoComp-assoc-at η oldSource (pr₁ ◁ Skh) ∙
      isoComp-cong composite-source (idIso (pr₁ ◁ Skh))))
  short = (κB ▷ Xf) ∙ paste Sk Sh
  long = Skh ∙ (Zf ◁ κA)

  abstract
    short-square : PS.Square pr₁ Diagram.b₀ final short
    short-square = PS.compose-square pr₁ Diagram.b₀ Diagram.b₅ final (κB ▷ Xf) (paste Sk Sh)
      (PS.pre-square pr₁ Xf (PS.compose-base pr₁ KB bKB HB bHB)
        (composite-base h k B) bXf κB (compositor h k B))
      (Diagram.paste-square first-square (separation k f))

    long-square : PS.Square pr₁ Diagram.b₀ final long
    long-square = PS.compose-square pr₁ Diagram.b₀ middle final Skh (Zf ◁ κA)
      composite-square
      (PS.post-square pr₁ Zf bZf (PS.compose-base pr₁ KA bKA HA bHA)
        (composite-base h k A) κA (compositor h k A))

    comparison : Iso₂ (pr₁ ◁ long) (pr₁ ◁ short)
    comparison = cancel-left-reflect final (invIso short-square ∙ long-square)
```
