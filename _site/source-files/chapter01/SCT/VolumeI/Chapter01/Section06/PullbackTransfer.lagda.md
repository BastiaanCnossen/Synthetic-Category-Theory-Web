# Transferring a universal cone

A comparison of cone descriptions has an equivalence on the chosen vertices
and converts cones on anima parameters. It preserves and reflects complete
cone identifications, including their matching squares. The induced-cone
comparison relates this conversion to restriction along the vertex functor.

These are data of a comparison, not additional axioms. No identity or
composition law for the conversion is needed for the transfer argument.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section06.PullbackTransfer where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section06.Cones
open import SCT.VolumeI.Chapter01.Section06.ConeIdentifications
open import SCT.VolumeI.Chapter01.Section06.Pullbacks
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares
import SCT.VolumeI.Chapter01.Section03.Factorizations as Fact
open import SCT.VolumeI.Chapter01.Section03.Equivalences using (equiv-reflect)

module _ {Γ : Context} where
  record ConeComparison {C D E S C′ D′ E′ S′ : CAT Γ}
    {f : MAP C E} {g : MAP D E} {f′ : MAP C′ E′} {g′ : MAP D′ E′}
    (s : Cone f g S) (t : Cone f′ g′ S′) : Set (c ⊔ m ⊔ a) where
    field
      vertex : MAP S S′
      vertex-isEquiv : IsEquiv vertex
      convert : {X : CAT Γ} → isAn X → Cone f g X → Cone f′ g′ X
      preserve : {X : CAT Γ} (xAn : isAn X) {p q : Cone f g X}
        → ConeIdentification₁ p q
        → ConeIdentification₁ (convert xAn p) (convert xAn q)
      reflect : {X : CAT Γ} (xAn : isAn X) (p q : Cone f g X)
        → ConeIdentification₁ (convert xAn p) (convert xAn q)
        → ConeIdentification₁ p q
      induced : {X : CAT Γ} (xAn : isAn X) (h : MAP X S)
        → ConeIdentification₁ (convert xAn (cone-restrict h s))
            (cone-restrict (vertex ∘ h) t)
```

The target universal cone first supplies a factor. Factoring that map through
the vertex equivalence supplies the source factor. Reflecting the pasted
target beta gives its complete cone identification.

```agda
  module Transfer {C D E S C′ D′ E′ S′ : CAT Γ}
    {f : MAP C E} {g : MAP D E} {f′ : MAP C′ E′} {g′ : MAP D′ E′}
    {s : Cone f g S} {t : Cone f′ g′ S′}
    (comparison : ConeComparison s t) (target-isPullback : IsPullback t) where
    private
      module Change = ConeComparison comparison
      module Known = UniversalCone t target-isPullback

    module Factor {X : CAT Γ} (xAn : isAn X) (p : Cone f g X) where
      private
        chosen : Fact.Factorization Change.vertex (Known.factor (Change.convert xAn p))
        chosen = Fact.factor-through-equiv Change.vertex-isEquiv
          (Known.factor (Change.convert xAn p))

      factor : MAP X S
      factor = Fact.factor chosen

      β : ConeIdentification₁ (cone-restrict factor s) p
      β = Change.reflect xAn _ _
        (cone-compose (Known.β (Change.convert xAn p))
          (cone-compose (cone-action-One t (Fact.triangle chosen))
            (Change.induced xAn factor)))

    reflect : {X : CAT Γ} (xAn : isAn X) (h k : MAP X S)
      → ConeIdentification₁ (cone-restrict h s) (cone-restrict k s) → h =₁ k
    reflect xAn h k Φ = equiv-reflect Change.vertex-isEquiv h k
      (Known.reflect (Change.vertex ∘ h) (Change.vertex ∘ k)
        (cone-compose (Change.induced xAn k)
          (cone-compose (Change.preserve xAn Φ) (cone-inverse (Change.induced xAn h)))))
```

Recognition needs only the factor of the chosen pullback cone and reflection
at the source vertex. Since conversion is available only on anima parameters,
both of these vertices must explicitly be animae.

```agda
    source-isPullback : isAn S → isAn (Pullback f g) → IsPullback s
    source-isPullback sAn pAn = isPullback-from-factor-and-reflection s
      (Factor.factor pAn (pullback-cone f g))
      (Factor.β pAn (pullback-cone f g)) (reflect sAn)
```
