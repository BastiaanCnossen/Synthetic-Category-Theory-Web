# Inclusions tested on mapping animae

Subcategories and full subcategories are defined by the same kind of
square. For a test category `K`, the square compares `mapPost f` on
`Map D A` with the induced action on `Map (Map K D) (Map K A)`.
Subcategories use `K = [1]` (`def:Subcategory`) and full subcategories use
`K = One`, whose mapping anima is the core (`def:Full_Subcategory`).

The arguments below depend only on this square, so we prove them once for
an arbitrary `K`: the inclusion is an embedding, it is an equivalence when
its action on `K`-shaped diagrams is, equivalences satisfy the definition,
and the definition is invariant under equivalence of sources.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.Section01.MappingCalculus.TestedInclusions
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section04.EquivalenceDetection 𝒯 M using (post-tests-all)
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
  using (Cone; ConeIso; IsPullback; module UniversalCone)
open import SCT.VolumeI.Chapter01.Section06.EmbeddingCalculus.EmbeddingCalculus 𝒯 P
  using (IsEmbedding; base-change-embedding; embedding-cong; equivalence-isEmbedding;
    module LeftCancellation)
open import SCT.VolumeI.Chapter01.Section06.EmbeddingCharacterizations 𝒯 M P
  using (map-preserves-embedding; map-detects-embedding)
open import SCT.VolumeI.Chapter01.Section06.PullbackEquivalences 𝒯 P
  using (degenerate-pullback; degenerate-pullback-converse)
open import SCT.VolumeI.Chapter01.Section06.EmbeddingCalculus.PullbackProjections 𝒯 P
  using (embedding-pullback)
open import SCT.VolumeI.Chapter03.Section01.MappingCalculus.MappingAction 𝒯 M
  using (mappingAction; mappingAction-natural)

testSquare : {A C : CAT} (K : CAT) (f : MAP A C) (D : CAT) →
  Cone (mappingAction K D C) (mapPost (mapPost {C = K} f)) (Map D A)
testSquare {A} K f D = record
  { left = mapPost f
  ; right = mappingAction K D A
  ; match = (mappingAction-natural K D f) ⁻¹ }
```

## Cones from a boundary factorization

Suppose the action of `f` on `K`-shaped diagrams factors as `n ∘ k`.
Postcomposing the second projection of the chosen pullback for `f` with
`k` gives a cone over the cospan for `n`. Its matching pastes the boundary
factorization with the chosen pullback identification. Presentations,
changes of source, and spanned full subcategories use this cone.

```agda
module Boundary (K : CAT) {A C Y : CAT} (f : MAP A C)
  (n : MAP Y (Map K C)) (k : MAP (Map K A) Y)
  (β : (n ∘ k) =₁ mapPost {C = K} f) (D : CAT) where
  h = pullback₁ {f = mappingAction K D C} {mapPost (mapPost f)}
  q = pullback₂ {f = mappingAction K D C} {mapPost (mapPost f)}

  boundary : (mapPost {C = Map K D} n ∘ mapPost k) =₁ mapPost (mapPost f)
  boundary = mapPost-cong β ∙ mapPost-comp k n

  cone : Cone (mappingAction K D C) (mapPost n)
    (Pullback (mappingAction K D C) (mapPost (mapPost f)))
  cone = record { left = h ; right = mapPost k ∘ q
    ; match = comp-assoc q (mapPost k) (mapPost n) ∙ ((boundary ⁻¹ ▷ q) ∙ pullbackMatch) }
```

## Consequences of the squares

The embedding is tested on mapping animae: each tested map is a base
change of the action of `f` on `K`-shaped diagrams.

```agda
module Tested (K : CAT) {A C : CAT} (f : MAP A C)
  (test-isEmbedding : IsEmbedding (mapPost {C = K} f))
  (square-isPullback : (D : CAT) → IsPullback (testSquare K f D)) where

  isEmbedding : IsEmbedding f
  isEmbedding = map-detects-embedding f (λ D →
    base-change-embedding (testSquare K f D) (square-isPullback D)
      (map-preserves-embedding (Map K D) (mapPost f) test-isEmbedding))

  test-detects-equivalence : IsEquiv (mapPost {C = K} f) → IsEquiv f
  test-detects-equivalence test-equiv = post-tests-all f (λ D →
    degenerate-pullback-converse (mapPost-isEquiv (mapPost f) test-equiv)
      (testSquare K f D) (square-isPullback D))

equivalence-test-isEmbedding : (K : CAT) {A C : CAT} (f : MAP A C) →
  IsEquiv f → IsEmbedding (mapPost {C = K} f)
equivalence-test-isEmbedding K f ef = equivalence-isEmbedding (mapPost f) (mapPost-isEquiv f ef)

equivalence-square-isPullback : (K : CAT) {A C : CAT} (f : MAP A C) →
  IsEquiv f → (D : CAT) → IsPullback (testSquare K f D)
equivalence-square-isPullback K f ef D = degenerate-pullback
  (mapPost-isEquiv (mapPost f) (mapPost-isEquiv f ef))
  (testSquare K f D) (mapPost-isEquiv f ef)
```

## Changing the source by an equivalence

Transport the proposed family of `K`-shaped diagrams across the
equivalence, use the given square, and lift back. The embedding pullback
criterion then supplies the universal property, including the specified
matching.

```agda
module ChangeSource (K : CAT) {A B C : CAT} (f : MAP A C) (g : MAP B C)
  (e : MAP A B) (equivalent : IsEquiv e) (over : (g ∘ e) =₁ f)
  (g-test-isEmbedding : IsEmbedding (mapPost {C = K} g))
  (g-square-isPullback : (D : CAT) → IsPullback (testSquare K g D)) where

  embedding : IsEmbedding f
  embedding = embedding-cong over
    (LeftCancellation.compose e g
      (Tested.isEmbedding K g g-test-isEmbedding g-square-isPullback)
      (equivalence-isEmbedding e equivalent))

  module Square (D : CAT) where
    map-change = mapPost {C = D} e

    upper : (mapPost g ∘ map-change) =₁ mapPost f
    upper = mapPost-cong over ∙ mapPost-comp e g

    open Boundary K f (mapPost g) (mapPost e) (mapPost-cong over ∙ mapPost-comp e g) D
      using (h; cone)
    module U = UniversalCone (testSquare K g D) (g-square-isPullback D)
    chosen = equiv-lift (mapPost-isEquiv e equivalent) (U.factor cone)

    factorization : FunctorLift (mapPost f) h
    factorization = record { lift = FunctorLift.lift chosen
      ; comparison = ConeIso.leftIso (U.factor-β cone) ∙
          ((mapPost g ◁ FunctorLift.comparison chosen) ∙
            (comp-assoc (FunctorLift.lift chosen) map-change (mapPost g) ∙
              (upper ⁻¹ ▷ FunctorLift.lift chosen))) }

    isPullback : IsPullback (testSquare K f D)
    isPullback = embedding-pullback (testSquare K f D)
      (map-preserves-embedding (Map K D) (mapPost f) (map-preserves-embedding K f embedding))
      (map-preserves-embedding D f embedding) factorization

  test-isEmbedding : IsEmbedding (mapPost {C = K} f)
  test-isEmbedding = map-preserves-embedding K f embedding

  square-isPullback : (D : CAT) → IsPullback (testSquare K f D)
  square-isPullback = Square.isPullback
```
