# The unchanged coordinate of successive parameter changes

Parameter substitution preserves the second projection. Its normalized
projection witnesses let us apply the same square-pasting calculation
without changing the target of that projection.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section04.SquareCalculus.ProjectionSquares as Projections
import SCT.VolumeI.Chapter01.Section04.ProductCalculus.ProductSubstitution as Substitution
import SCT.VolumeI.Chapter01.Section04.ProductCalculus.ProductSecondCoordinate as SubstitutionSecond
import SCT.VolumeI.Chapter01.Section08.ProductCalculus.ProductSecondCoordinate as Second
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN

module SCT.VolumeI.Chapter01.Section08.ProductCalculus.ParameterSecondCoordinate
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section04.Substitution.Compatibility 𝒯 M using (slice-comparison)
open import SCT.VolumeI.Chapter01.Section08.ProductSquares 𝒯
open import SCT.VolumeI.Chapter01.Section04.SquareCalculus.ParameterSquarePasting 𝒯 using (paste)
open Second 𝒯 M using (restriction-base; parameter-base; separation)
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-left-reflect)
module PS = Projections 𝒯

parameter-over : {X Y A B : CAT} (h : MAP X Y) (f : MAP A B) →
  ((f ∘ pr₂) ∘ productMap h (id A)) =₁ (f ∘ pr₂)
parameter-over {A = A} h f = PS.lift-base f pr₂ (productMap h (id A)) (parameter-base h A)

compositor : {X Y Z : CAT} (h : MAP X Y) (k : MAP Y Z) (A : CAT) →
  PS.Square pr₂
    (PS.compose-base pr₂ (productMap k (id A)) (parameter-base k A)
      (productMap h (id A)) (parameter-base h A))
    (parameter-base (k ∘ h) A) (slice-comparison {C = A} k h)
compositor h k A =
  isoComp-cong (idIso (parameter-base h A))
    (isoComp-cong ((preWhisker-isoComp-at unitY bk input) ⁻¹) (idIso tail)) ∙
  (isoComp-cong (idIso (parameter-base h A)) ((isoComp-assoc-at (unitY ▷ input) (bk ▷ input) tail) ⁻¹) ∙
  ((isoComp-assoc-at unitX bh ((unitY ▷ input) ∙ ((bk ▷ input) ∙ tail))) ⁻¹ ∙
  (isoComp-cong (idIso unitX) (isoComp-assoc-at bh (unitY ▷ input) ((bk ▷ input) ∙ tail)) ∙
  (isoComp-cong (idIso unitX)
    (isoComp-cong (SubstitutionSecond.second-normalization 𝒯 M A k h) (idIso ((bk ▷ input) ∙ tail)) ∙
      Substitution.Coordinates.projection₂ 𝒯 M A k h) ∙
    isoComp-assoc-at unitX bkh (pr₂ ◁ slice-comparison {C = A} k h)))))
  where
  input = productMap h (id A)
  outer = productMap k (id A)
  unitX = comp-unitˡ pr₂
  unitY = comp-unitˡ pr₂
  bh = pair-β₂ (h ∘ pr₁) (id A ∘ pr₂)
  bk = pair-β₂ (k ∘ pr₁) (id A ∘ pr₂)
  bkh = pair-β₂ ((k ∘ h) ∘ pr₁) (id A ∘ pr₂)
  tail = (comp-assoc input outer pr₂) ⁻¹

compositor-over : {X Y Z A B : CAT} (h : MAP X Y) (k : MAP Y Z) (f : MAP A B) →
  PS.Square (f ∘ pr₂)
    (PS.compose-base (f ∘ pr₂) (productMap k (id A)) (parameter-over k f)
      (productMap h (id A)) (parameter-over h f))
    (parameter-over (k ∘ h) f) (slice-comparison {C = A} k h)
compositor-over {A = A} h k f =
  (PS.lift-compose f pr₂ (productMap k (id A)) (productMap h (id A)) (parameter-base k A) (parameter-base h A)) ⁻¹ ∙
    PS.lift-square f pr₂
      (PS.compose-base pr₂ (productMap k (id A)) (parameter-base k A) (productMap h (id A)) (parameter-base h A))
      (parameter-base (k ∘ h) A) (slice-comparison {C = A} k h) (compositor h k A)

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

  module Diagram = PS.Pasting (f ∘ pr₂) (f ∘ pr₂) (f ∘ pr₂) pr₂ pr₂ pr₂
    Xf Yf Zf HA KA HB KB (parameter-over h f) (parameter-over k f)
    (parameter-base h B) (parameter-base k B) (restriction-base X f) (restriction-base Y f) (restriction-base Z f)
    Sh Sk
  final = PS.compose-base pr₂ KHB (parameter-base (k ∘ h) B) Xf (restriction-base X f)
  middle = PS.compose-base pr₂ Zf (restriction-base Z f) KHA (parameter-over (k ∘ h) f)

  short = (κB ▷ Xf) ∙ paste Sk Sh
  long = Skh ∙ (Zf ◁ κA)

  abstract
    short-square : PS.Square pr₂ Diagram.b₀ final short
    short-square = PS.compose-square pr₂ Diagram.b₀ Diagram.b₅ final (κB ▷ Xf) (paste Sk Sh)
      (PS.pre-square pr₂ Xf
        (PS.compose-base pr₂ KB (parameter-base k B) HB (parameter-base h B))
        (parameter-base (k ∘ h) B) (restriction-base X f) κB (compositor h k B))
      (Diagram.paste-square (separation h f) (separation k f))

    long-square : PS.Square pr₂ Diagram.b₀ final long
    long-square = PS.compose-square pr₂ Diagram.b₀ middle final Skh (Zf ◁ κA)
      (separation (k ∘ h) f)
      (PS.post-square pr₂ Zf (restriction-base Z f)
        (PS.compose-base (f ∘ pr₂) KA (parameter-over k f) HA (parameter-over h f))
        (parameter-over (k ∘ h) f) κA (compositor-over h k f))

    comparison : (pr₂ ◁ long) =₂ (pr₂ ◁ short)
    comparison = cancel-left-reflect final (short-square ⁻¹ ∙ long-square)
```
