# Extension and comparison for cocones

This is a property to be proved, not additional structure in the axioms.
It records extension and comparison at every target category. With functor
categories available, the targets `Fun X E` also test arbitrary parameters.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level; _⊔_)
open import SCT.VolumeI.Chapter01.Theory using (Theory)

module SCT.VolumeI.Chapter01.Section08.CoconeCalculus.CoconeUniversality
  {c m a : Level} (𝒯 : Theory c m a) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open import SCT.VolumeI.Chapter01.Section08.Cocones 𝒯
open import SCT.VolumeI.Chapter01.Section08.CoconeCalculus.CoconePostcomposition 𝒯 using (coconePost)

record CoconeExtensionProperty {A B C D : CAT} {u : MAP A B} {l : MAP A C}
  (s : Cocone u l D) : Set (c ⊔ m) where
  field
    factor : (E : CAT) → Cocone u l E → MAP D E
    factor-β : (E : CAT) (t : Cocone u l E) → CoconeIso (coconePost (factor E t) s) t
    reflect : (E : CAT) (f g : MAP D E) →
      CoconeIso (coconePost f s) (coconePost g s) → f =₁ g

record CoconeComparisonLift {A B C D E : CAT} {u : MAP A B} {l : MAP A C}
  (s : Cocone u l D) (f g : MAP D E)
  (Φ : CoconeIso (coconePost f s) (coconePost g s)) : Set m where
  field
    lift : f =₁ g
    left-image : (lift ▷ Cocone.left s) =₂ (CoconeIso.leftIso Φ)
    right-image : (lift ▷ Cocone.right s) =₂ (CoconeIso.rightIso Φ)
```

The second record retains the two prescribed leg comparisons. Mere
existence of an isomorphism between extensions would not provide these
identifications, which are needed when pasting cocones.
