# Representability of identifications

For two objects a and b, the identification anima carries a universal
identification between the two constant functors. Its fiber square is a
pullback. Evaluating the universal identification at an absolute
identification returns that identification, with both constant-evaluation
comparisons retained. These are the three existing representability
assumptions; no beta law for arbitrary families is supplied.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section06.Representability where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary
import SCT.VolumeI.Chapter01.Section01.Terms as Terms
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal
open Constructions
open import SCT.VolumeI.Chapter01.Section02.Coherence using (module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Specialization
open import SCT.VolumeI.Chapter01.Section06.Cones
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares using (IsPullback)

module _ {Γ : Context} where
  identification-square : {E : CAT Γ} (a b : Obj-abs E)
    → (const {P = a ＝ b} a) =₁ const b → Cone b a (a ＝ b)
  identification-square a b ε = record
    { left = terminate (a ＝ b)
    ; right = terminate (a ＝ b)
    ; match = ε ⁻¹ }

  identification-evaluate : {E : CAT Γ} (a b : Obj-abs E)
    (ε : (const {P = a ＝ b} a) =₁ const b) → a =₁ b → a =₁ b
  identification-evaluate a b ε α = const-evaluate b α ∙
    ((ε ▷ α) ∙ (const-evaluate a α) ⁻¹)

  postulate
    identification : {E : CAT Γ} (a b : Obj-abs E)
      → (const {P = a ＝ b} a) =₁ const b
    identification-isPullback : {E : CAT Γ} (a b : Obj-abs E)
      → IsPullback (identification-square a b (identification a b))
    identification-evaluate-β : {E : CAT Γ} (a b : Obj-abs E) (α : a =₁ b)
      → identification-evaluate a b (identification a b) α =₂ α

  module _ {T : CAT Γ} where
    open Terms.InContext T using (Term)

    identification-restrict : {E : CAT Γ} (a b : Obj-abs E)
      → Term (a ＝ b) → (const {P = T} a) =₁ const b
    identification-restrict a b u = const-pre b u ∙
      ((identification a b ▷ u) ∙ (const-pre a u) ⁻¹)
```
