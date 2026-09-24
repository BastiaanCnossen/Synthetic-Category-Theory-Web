# Representability of identifications

This is `post:Representability_Of_Identifications`. The supplied family
`identification` determines the matching of the fiber square with both
projections to the terminal category, right leg `b` and bottom leg `a`.
Our cone convention reads the matching from the top-right composite to
the bottom-left composite, so its matching is the inverse of the supplied
identification from the constant functor at `a` to the constant functor at `b`.
The diagonal-square formulation is derived separately in
`RepresentabilityDiagonal`, using the later pullback lemmas.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level; _⊔_)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws

module SCT.VolumeI.Chapter01.Section06.Representability
  {c m a : Level} (𝒯 : Theory c m a) (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
  using (Cone; IsPullback)

identification-square : {E : CAT} (a b : Obj-abs E)
  → (const {P = a ＝ b} a) =₁ (const b)
  → Cone b a (a ＝ b)
identification-square {E} a b ε = record
  { left = terminate (a ＝ b)
  ; right = terminate (a ＝ b)
  ; match = ε ⁻¹
  }

record Representability : Set (c ⊔ m) where
  field
    identification : {E : CAT} (a b : Obj-abs E)
      → (const {P = a ＝ b} a) =₁ (const b)
    identification-isPullback : {E : CAT} (a b : Obj-abs E)
      → IsPullback (identification-square a b (identification a b))

module Families (R : Representability) where
  open Representability R

  identification-family : {T E : CAT} (a b : Obj-abs E) (u : MAP T (a ＝ b))
    → (const {P = T} a) =₁ (const b)
  identification-family a b u = const-pre b u ∙
    ((identification a b ▷ u) ∙ (const-pre a u) ⁻¹)
```
