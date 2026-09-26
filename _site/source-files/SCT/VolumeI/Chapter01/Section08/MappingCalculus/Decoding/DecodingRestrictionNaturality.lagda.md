# Decoding respects isomorphic restrictions

We vary the restricting functor itself. Uncurrying first transports its
isomorphism to the product; naturality of the terminal-product inclusion then moves it
to the other coordinate.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping

import SCT.VolumeI.Chapter01.Section08.MappingCalculus.Decoding.UnitRestrictionNaturality as Unit

import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN

module SCT.VolumeI.Chapter01.Section08.MappingCalculus.Decoding.DecodingRestrictionNaturality
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section04.Substitution.DecodingNaturality 𝒯 M using (decodePre; oneProduct-natural)
open import SCT.VolumeI.Chapter01.Section08.MappingCalculus.Restriction.PrecompositionCongruence 𝒯 M using (mapPre-cong-at)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ComparisonSquares 𝒯 using (post-square)
open Structural vocabulary terminal products productLaws composition whiskering
  using (whisker-mixed-at; postWhisker-comp-at)
open PN vocabulary terminal products productLaws composition vertical whiskering using (move-square)

module Restriction {A B E : CAT} {f g : MAP A B}
  (α : f =₁ g) (h : Obj-abs (Map B E)) where
  S = oneProduct-in A
  T = oneProduct-in B
  e = mapUncurry h
  Rf = productMap (id One) f
  Rg = productMap (id One) g
  Lf = f
  Lg = g
  Rα = productMap-cong (idIso (id One)) α
  Lα = α
  qf = mapPre-uncurry f h
  qg = mapPre-uncurry g h
  r₁f = qf ▷ S
  r₁g = qg ▷ S
  r₂f = comp-assoc S Rf e
  r₂g = comp-assoc S Rg e
  r₃f = e ◁ oneProduct-natural f
  r₃g = e ◁ oneProduct-natural g
  r₄f = (comp-assoc Lf T e) ⁻¹
  r₄g = (comp-assoc Lg T e) ⁻¹
  action₀ = mapUncurryIso (mapPre-cong α ▷ h) ▷ S
  action₁ = (e ◁ Rα) ▷ S
  action₂ = e ◁ (Rα ▷ S)
  action₃ = e ◁ (T ◁ Lα)
  action₄ = decodeMap h ◁ Lα

  abstract
    first : (r₁g ∙ action₀) =₂ (action₁ ∙ r₁f)
    first = preWhisker-isoComp-at (e ◁ Rα) qf S ∙
      ((preWhisker S ◁ mapPre-cong-at α h) ∙
        (preWhisker-isoComp-at qg (mapUncurryIso (mapPre-cong α ▷ h)) S) ⁻¹)

    middle : (r₃g ∙ action₂) =₂ (action₃ ∙ r₃f)
    middle = post-square e (oneProduct-natural f) (oneProduct-natural g)
      (Rα ▷ S) (T ◁ Lα) (Unit.Naturality.comparison 𝒯 M α)

    last : (r₄g ∙ action₃) =₂ (action₄ ∙ r₄f)
    last = move-square (comp-assoc Lg T e) action₄ action₃
      (comp-assoc Lf T e) (postWhisker-comp-at Lα T e)

    comparison : (decodePre g h ∙ decodeMapIso (mapPre-cong α ▷ h)) =₂
      ((decodeMap h ◁ Lα) ∙ decodePre f h)
    comparison = paste-squares (r₃f ∙ (r₂f ∙ r₁f)) (r₃g ∙ (r₂g ∙ r₁g))
      r₄f r₄g action₀ action₃ action₄
      (paste-squares (r₂f ∙ r₁f) (r₂g ∙ r₁g) r₃f r₃g action₀ action₂ action₃
        (paste-squares r₁f r₁g r₂f r₂g action₀ action₁ action₂ first
          (whisker-mixed-at Rα S e)) middle) last ∙
      isoComp-cong (idIso (decodePre g h)) (decodeMapIso-at (mapPre-cong α ▷ h))
```
