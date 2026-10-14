# Embeddings and their diagonals

A functor is an embedding when its diagonal cone is a pullback. Equivalently,
the first projection of its self-pullback is an equivalence. The chosen diagonal
and the full cone beta make the projection criterion explicit.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section06.Embeddings where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary
import SCT.VolumeI.Chapter01.Section01.Terms as Terms
open Operations
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (id₌; comp-unitˡ; comp-unitʳ; comp-assoc; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Specialization using (comp₌-cong)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses
  using (inverse-composite; inverse-inverse; comp₌-unitˡ-One; comp₌-inverseʳ-One)
open import SCT.VolumeI.Chapter01.Section03.Equivalences
import SCT.VolumeI.Chapter01.Section03.Factorizations as Fact
open import SCT.VolumeI.Chapter01.Section03.WhiskeringEquivalence using (factor-through-preWhisker)
open import SCT.VolumeI.Chapter01.Section06.Cones
open import SCT.VolumeI.Chapter01.Section06.ConeTransport
open import SCT.VolumeI.Chapter01.Section06.ConeUniversality
open import SCT.VolumeI.Chapter01.Section06.Pullbacks
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares using (IsPullback)
open import SCT.VolumeI.Chapter01.Section06.PullbackConstructions using (pullback₁-isEquiv; pullback-cone-isPullback)
open import SCT.VolumeI.Chapter01.Section06.PullbackArrowChange
open import SCT.VolumeI.Chapter01.Section06.NestedPullbacks


module _ {Γ : Context} where
  diagonal-cone : {C D : CAT Γ} (f : MAP C D) → Cone f f C
  diagonal-cone {C} f = record
    { left = id C; right = id C; match = id₌ (f ∘ id C) }

  diagonal : {C D : CAT Γ} (f : MAP C D) → MAP C (Pullback f f)
  diagonal f = pullback-factor (diagonal-cone f)

  IsEmbedding : {C D : CAT Γ} → MAP C D → Set m
  IsEmbedding f = IsPullback (diagonal-cone f)

  embedding-projection-isEquiv : {C D : CAT Γ} (f : MAP C D)
    → IsEmbedding f → IsEquiv (pullback₁ {f = f} {g = f})
  embedding-projection-isEquiv f ef = equiv-cancel-right (diagonal f) pullback₁ ef
    (equiv-transport ((pullback-factor-β₁ (diagonal-cone f)) ⁻¹) (id-isEquiv _))

  embedding-from-projection-isEquiv : {C D : CAT Γ} (f : MAP C D)
    → IsEquiv (pullback₁ {f = f} {g = f}) → IsEmbedding f
  embedding-from-projection-isEquiv f ep = equiv-cancel-left (diagonal f) pullback₁ ep
    (equiv-transport ((pullback-factor-β₁ (diagonal-cone f)) ⁻¹) (id-isEquiv _))
```

## Reflecting identifications

The two projections agree after restriction to the diagonal. Since the
diagonal is an equivalence, this agreement extends to the whole self-pullback.
Factoring a supplied identification through that pullback then identifies its
two source terms. This proves existence of the reflected identification;
it does not prescribe its postwhiskering image.

```agda
  embedding-projections-equal : {C D : CAT Γ} (f : MAP C D) → IsEmbedding f
    → (pullback₁ {f = f} {g = f}) =₁ pullback₂
  embedding-projections-equal f ef = Fact.factor
    (factor-through-preWhisker (diagonal f) ef
      ((pullback-factor-β₂ (diagonal-cone f)) ⁻¹ ∙ pullback-factor-β₁ (diagonal-cone f)))

  module _ {T C D : CAT Γ} where
    open Terms.InContext T using (Term)

    embedding-reflect : (f : MAP C D) → IsEmbedding f
      → (x y : Term C) → (f ∘ x) =₁ (f ∘ y) → x =₁ y
    embedding-reflect f ef x y α = pullback-factor-β₂ s ∙
      ((embedding-projections-equal f ef ▷ pullback-factor s) ∙ (pullback-factor-β₁ s) ⁻¹)
      where
      s : Cone f f T
      s = record { left = x; right = y; match = α }
```

## An embedding with a section

A supplied section gives one inverse law. Reflection gives the other by
applying the functor and using that supplied section law.

```agda
  embedding-with-section : {C D : CAT Γ} (f : MAP C D)
    → IsEmbedding f → Section f → IsEquiv f
  embedding-with-section f ef σ = record
    { inverse = Section.section σ
    ; left-inverse-law = embedding-reflect f ef _ _
        (comp-assoc f (Section.section σ) f ∙
          ((Section.section-law σ ▷ f) ∙ ((comp-unitˡ f) ⁻¹ ∙ comp-unitʳ f)))
    ; right-inverse-law = Section.section-law σ }
```

## Changing the functor

Change both arrows of the diagonal cospan along the supplied identification.
The resulting matching is an identification followed by its inverse, with
an intervening identity. Its normalization supplies a complete comparison
with the new diagonal cone. This proves invariance directly, without a
general change-of-cospan equivalence.

```agda
  embedding-cong : {C D : CAT Γ} {f g : MAP C D}
    → f =₁ g → IsEmbedding f → IsEmbedding g
  embedding-cong {C} {f = f} {g} α ef =
    isPullback-cone-identification comparison
      (RightArrowChange.isPullback α (cone-change-left α (diagonal-cone f))
        (isPullback-change-left α (diagonal-cone f) ef))
    where
    δ = α ▷ id C
    identity = id₌ (f ∘ id C)
    changed = cone-change-right α (cone-change-left α (diagonal-cone f))
    normalization : Cone.match changed =₂ id₌ (g ∘ id C)
    normalization = comp₌-inverseʳ-One δ ∙
      comp₌-cong (id₌ δ)
        (comp₌-unitˡ-One (δ ⁻¹) ∙
          (comp₌-cong (inverse-inverse identity) (id₌ (δ ⁻¹)) ∙
            inverse-composite δ (identity ⁻¹)))
    comparison : ConeIdentification₁ changed (diagonal-cone g)
    comparison = cone-retarget-match-identification changed (id₌ (g ∘ id C)) normalization
```

## Equivalences are embeddings

Base change of an equivalence makes the first self-pullback projection an
equivalence, so the projection criterion applies.

```agda
  equivalence-isEmbedding : {C D : CAT Γ} (f : MAP C D)
    → IsEquiv f → IsEmbedding f
  equivalence-isEmbedding f ef = embedding-from-projection-isEquiv f (pullback₁-isEquiv f f ef)
```

## Composition and base change

The nesting equivalence compares the relevant first projections. Its
projection consequence applies without an embedding hypothesis; the
embedding results then use the self-pullback criterion.

```agda
  composition-cone : {C D E : CAT Γ} (f : MAP C D) (g : MAP D E) → Cone (g ∘ f) g C
  composition-cone {C} f g = record { left = id C ; right = f ; match = comp-unitʳ (g ∘ f) }

  composition-cone-isPullback : {C D E : CAT Γ} (f : MAP C D) (g : MAP D E) →
    IsEmbedding g → IsPullback (composition-cone f g)
  composition-cone-isPullback f g eg = equiv-cancel-left (pullback-factor (composition-cone f g)) pullback₁
    (nested-projection-isEquiv f g g (embedding-projection-isEquiv g eg))
    (equiv-transport ((pullback-factor-β₁ (composition-cone f g)) ⁻¹) (id-isEquiv _))

  module LeftCancellation {C D E : CAT Γ} (f : MAP C D) (g : MAP D E) (eg : IsEmbedding g) where

    t : Cone g (g ∘ f) C
    t = cone-swap (composition-cone f g)
    et : IsPullback t
    et = SwappedCone.isPullback (composition-cone f g) (composition-cone-isPullback f g eg)
    module N = Nested f g (g ∘ f) t et

    compose : IsEmbedding f → IsEmbedding (g ∘ f)
    compose ef = embedding-from-projection-isEquiv (g ∘ f)
      (equiv-cancel-right N.flatten pullback₁ N.flatten-isEquiv
        (equiv-transport ((pullback-factor-β₁ N.flat-cone) ⁻¹) (embedding-projection-isEquiv f ef)))

    cancel : IsEmbedding (g ∘ f) → IsEmbedding f
    cancel egf = embedding-from-projection-isEquiv f
      (equiv-transport (pullback-factor-β₁ N.flat-cone)
        (equiv-compose N.flatten pullback₁ N.flatten-isEquiv (embedding-projection-isEquiv (g ∘ f) egf)))

```

## Base change

```agda
module _ {Γ : Context} where
  chosen-base-change-embedding : {C D E : CAT Γ} (f : MAP C E) (g : MAP D E) →
    IsEmbedding g → IsEmbedding (pullback₁ {f = f} {g})
  chosen-base-change-embedding {C = C} {D = D} f g eg = embedding-from-projection-isEquiv p
    (equiv-transport (pullback-factor-β₁ N.flat-cone)
      (equiv-compose N.flatten pullback₁ N.flatten-isEquiv outerProjection))
    where
    p : MAP (Pullback f g) C
    p = pullback₁ {f = f} {g}
    q : MAP (Pullback f g) D
    q = pullback₂ {f = f} {g}
    module N = ChosenNested p f g
    module Change = ChangeLeftArrow (pullback-match {f = f} {g}) g
    otherProjection : IsEquiv (pullback₁ {f = g ∘ q} {g})
    otherProjection = nested-projection-isEquiv q g g (embedding-projection-isEquiv g eg)
    outerProjection : IsEquiv (pullback₁ {f = f ∘ p} {g})
    outerProjection = equiv-transport (pullback-factor-β₁ (cone-change-left (pullback-match {f = f} {g}) (pullback-cone (f ∘ p) g)))
      (equiv-compose Change.forward pullback₁ Change.forward-isEquiv otherProjection)

  base-change-embedding : {C D E T : CAT Γ} {f : MAP C E} {g : MAP D E}
    (s : Cone f g T) → IsPullback s → IsEmbedding g → IsEmbedding (Cone.left s)
  base-change-embedding {f = f} {g} s es eg = embedding-cong (pullback-factor-β₁ s)
    (LeftCancellation.compose (pullback-factor s) pullback₁ (chosen-base-change-embedding f g eg)
      (equivalence-isEmbedding (pullback-factor s) es))

  chosen-base-change-embeddingʳ : {C D E : CAT Γ} (f : MAP C E) (g : MAP D E) →
    IsEmbedding f → IsEmbedding (pullback₂ {f = f} {g})
  chosen-base-change-embeddingʳ f g ef = base-change-embedding (cone-swap (pullback-cone f g))
    (SwappedCone.isPullback (pullback-cone f g) (pullback-cone-isPullback f g)) ef

```

## Relative criterion

```agda
module _ {Γ : Context} where
  module RelativeEmbedding {C D E T : CAT Γ} {f : MAP C E} {g : MAP D E}
    (s : Cone f g T) (ef : IsEmbedding f) where

    projection : IsEmbedding (pullback₂ {f = f} {g})
    projection = chosen-base-change-embeddingʳ f g ef

    factor-isEmbedding : IsEmbedding (Cone.right s) → IsEmbedding (pullback-factor s)
    factor-isEmbedding eu = LeftCancellation.cancel (pullback-factor s) pullback₂ projection
      (embedding-cong ((pullback-factor-β₂ s) ⁻¹) eu)

    right-isEmbedding : IsEmbedding (pullback-factor s) → IsEmbedding (Cone.right s)
    right-isEmbedding eh = embedding-cong (pullback-factor-β₂ s)
      (LeftCancellation.compose (pullback-factor s) pullback₂ projection eh)
```
