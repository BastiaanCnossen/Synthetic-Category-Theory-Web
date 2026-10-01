# Comparing two represented families

This elementary criterion constructs an equivalence from mutually inverse
transformations of functors with anima parameters. Only one transformation
needs a precomposition comparison. The proof tests the two represented
animae themselves, so it produces an equivalence of categories rather than
a bijection of their absolute objects.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Calculus as Calculus

module SCT.VolumeI.Chapter05.Section02.MappingCalculus.Representations
  {l : Level} (S : Theory l l l) where

open View S
open Calculus S using (_then_)

module Compare (C D : CAT) (cAn : isAn C) (dAn : isAn D)
  (forth : {R : CAT} → isAn R → MAP R C → MAP R D)
  (back : {R : CAT} → isAn R → MAP R D → MAP R C)
  (forth-cong : {R : CAT} (rAn : isAn R) {f g : MAP R C} → f =₁ g → forth rAn f =₁ forth rAn g)
  (back-cong : {R : CAT} (rAn : isAn R) {f g : MAP R D} → f =₁ g → back rAn f =₁ back rAn g)
  (back-forth : {R : CAT} (rAn : isAn R) (f : MAP R C) → back rAn (forth rAn f) =₁ f)
  (forth-back : {R : CAT} (rAn : isAn R) (f : MAP R D) → forth rAn (back rAn f) =₁ f)
  (back-pre : {R Q : CAT} (rAn : isAn R) (qAn : isAn Q) (f : MAP Q D) (r : MAP R Q)
    → back rAn (f ∘ r) =₁ (back qAn f ∘ r)) where

  F : MAP C D
  F = forth cAn (id C)
  G : MAP D C
  G = back dAn (id D)

  back-reflect : {R : CAT} (rAn : isAn R) {f g : MAP R D}
    → back rAn f =₁ back rAn g → f =₁ g
  back-reflect rAn {f} {g} α = (forth-back rAn f) ⁻¹ then
    forth-cong rAn α then forth-back rAn g

  left-inverse : (G ∘ F) =₁ id C
  left-inverse = (back-pre cAn dAn (id D) F) ⁻¹ then
    back-cong cAn (comp-unitˡ F) then back-forth cAn (id C)

  right-inverse : (F ∘ G) =₁ id D
  right-inverse = back-reflect dAn
    (back-pre dAn cAn F G then (back-forth cAn (id C) ▷ G) then comp-unitˡ G)

  isEquiv : IsEquiv F
  isEquiv = record { inverse = G ; sectionIso = left-inverse ⁻¹ ; retractionIso = right-inverse ⁻¹ }

  equivalence : Equiv C D
  equivalence = record { functor = F ; isEquiv = isEquiv }
```

The same argument applies to categories when all category parameters are allowed.

```agda
module CompareCategories (C D : CAT)
  (forth : {R : CAT} → MAP R C → MAP R D)
  (back : {R : CAT} → MAP R D → MAP R C)
  (forth-cong : {R : CAT} {f g : MAP R C} → f =₁ g → forth f =₁ forth g)
  (back-cong : {R : CAT} {f g : MAP R D} → f =₁ g → back f =₁ back g)
  (back-forth : {R : CAT} (f : MAP R C) → back (forth f) =₁ f)
  (forth-back : {R : CAT} (f : MAP R D) → forth (back f) =₁ f)
  (back-pre : {R Q : CAT} (f : MAP Q D) (r : MAP R Q)
    → back (f ∘ r) =₁ (back f ∘ r)) where

  F : MAP C D
  F = forth (id C)
  G : MAP D C
  G = back (id D)

  back-reflect : {R : CAT} {f g : MAP R D}
    → back f =₁ back g → f =₁ g
  back-reflect {f = f} {g} α = (forth-back f) ⁻¹ then
    forth-cong α then forth-back g

  left-inverse : (G ∘ F) =₁ id C
  left-inverse = (back-pre (id D) F) ⁻¹ then
    back-cong (comp-unitˡ F) then back-forth (id C)

  right-inverse : (F ∘ G) =₁ id D
  right-inverse = back-reflect
    (back-pre F G then (back-forth (id C) ▷ G) then comp-unitˡ G)

  isEquiv : IsEquiv F
  isEquiv = record { inverse = G ; sectionIso = left-inverse ⁻¹ ; retractionIso = right-inverse ⁻¹ }

  equivalence : Equiv C D
  equivalence = record { functor = F ; isEquiv = isEquiv }
```
