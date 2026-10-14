# Products of categories over a base

The product of `(C,p)` and `(D,q)` over `S` is the actual chosen pullback,
with structural map `p ∘ pullback₁`. An arbitrary categorical family into
this product is constructed from two relative families. Its pullback beta
and its subsequent relative-family beta retain their full matching squares.

For the categorical universal property, native functor categories preserve
the actual pullback. Pullback pasting identifies its relative fiber with
the product of the two relative fibers. All arrow changes use their specified
identifications; in particular the right leg of a relative fiber is not
replaced definitionally by the terminal functor.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section09.RelativeProducts where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary hiding (_＝_)
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal
open Constructions
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (id₌; comp-assoc; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section03.RelativeFunctors
open import SCT.VolumeI.Chapter01.Section03.Equivalences
  using (equiv-compose)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Triangles
  using (restrict-triangle)
open import SCT.VolumeI.Chapter01.Section06.Cones
open import SCT.VolumeI.Chapter01.Section06.ConeIdentifications
open import SCT.VolumeI.Chapter01.Section06.ConeTransport
open import SCT.VolumeI.Chapter01.Section06.ConeUniversality
  using (isPullback-change-left; module SwappedCone)
open import SCT.VolumeI.Chapter01.Section06.Pullbacks
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares
open import SCT.VolumeI.Chapter01.Section06.PullbackConstructions
  using (pullback-cone-isPullback; pullback-swap; pullback-swap-isEquiv; module TerminalBase)
open import SCT.VolumeI.Chapter01.Section06.NestedPullbacks using (module Nested)
open import SCT.VolumeI.Chapter01.Section06.ConePasting
  using (postcompose-cone-left; postcompose-cone-left-identification; postcompose-cone-left-restrict)
open import SCT.VolumeI.Chapter01.Section07.FunctorCategories using (Fun)
open import SCT.VolumeI.Chapter01.Section07.Functoriality using (funPost; funPost-comp)
open import SCT.VolumeI.Chapter01.Section07.FunctorPullbacks
  using (mappedCone; fun-preserves-pullback; mappedCone-evaluation)
open import SCT.VolumeI.Chapter01.Section09.RelativeFunctorCategories
open import SCT.VolumeI.Chapter01.Section09.RelativeFamilyComparisons

module RelativeProduct {Γ : Context} {S : CAT Γ} (A B : CategoryOverBase S) where
  private
    C = CategoryOverBase.category A
    D = CategoryOverBase.category B
    p = CategoryOverBase.map A
    q = CategoryOverBase.map B

  category : CAT Γ
  category = Pullback p q

  cone : Cone p q category
  cone = pullback-cone p q

  over-base : CategoryOverBase S
  over-base = category-over category (p ∘ Cone.left cone)

  left : FunctorOverBase over-base A
  left = functor-over (Cone.left cone) (id₌ _)

  right : FunctorOverBase over-base B
  right = functor-over (Cone.right cone) ((Cone.match cone) ⁻¹)

  module Families (X : CategoryOverBase S) where
    module ToC = RelativeFunctorCategory X A
    module ToD = RelativeFunctorCategory X B
    module ToProduct = RelativeFunctorCategory X over-base
    module ProductFamilies = RelativeFamilies X over-base

    module Pair {K : CAT Γ} (F : ToC.Family K) (G : ToD.Family K) where
      supplied : Cone p q (K × CategoryOverBase.category X)
      supplied = record
        { left = FunctorOverBase.functor F
        ; right = FunctorOverBase.functor G
        ; match = (FunctorOverBase.cell G) ⁻¹ ∙ FunctorOverBase.cell F }

      underlying : MAP (K × CategoryOverBase.category X) category
      underlying = pullback-factor supplied

      pullback-computation : ConeIdentification₁ (cone-restrict underlying cone) supplied
      pullback-computation = pullback-factor-β supplied

      family : ToProduct.Family K
      family = functor-over underlying
        (FunctorOverBase.cell F ∙
          ((p ◁ ConeIdentification₁.left pullback-computation) ∙
            comp-assoc underlying (Cone.left cone) p))

      curried : MAP K ToProduct.category
      curried = ToProduct.ChosenFamily.factor family

      relative-computation : ConeIdentification₁
        (ProductFamilies.family-cone (ToProduct.evaluated-family curried))
        (ProductFamilies.family-cone family)
      relative-computation = ProductFamilies.FamilyComputation.comparison family
```

## The categorical product comparison

The two middle pastings use the same mapped pullback cone. Changing its
left composite uses native postcomposition coherence. Changing the next
composite uses precisely the matching of the first relative fiber. The last
pasting uses the swapped second relative fiber, with its actual right leg.

```agda
  module UniversalProperty (X : CategoryOverBase S) where
    private
      T = CategoryOverBase.category X
      module FC = RelativeFunctorCategory X A
      module FD = RelativeFunctorCategory X B
      module FP = RelativeFunctorCategory X over-base

    ordinary-cone : Cone FC.postcomposition FD.postcomposition (Fun T category)
    ordinary-cone = mappedCone T cone

    ordinary-isPullback : IsPullback ordinary-cone
    ordinary-isPullback = fun-preserves-pullback T cone (pullback-cone-isPullback p q)

    postcomposition-comparison : FP.postcomposition =₁
      (FC.postcomposition ∘ Cone.left ordinary-cone)
    postcomposition-comparison = (funPost-comp {A = T} (Cone.left cone) p) ⁻¹

    changed-fiber : Cone
      (FC.postcomposition ∘ Cone.left ordinary-cone) FC.point FP.category
    changed-fiber = cone-change-left postcomposition-comparison FP.fiber

    change : MAP FP.category
      (Pullback (FC.postcomposition ∘ Cone.left ordinary-cone) FC.point)
    change = pullback-factor changed-fiber

    change-isEquiv : IsEquiv change
    change-isEquiv = isPullback-change-left postcomposition-comparison FP.fiber
      (pullback-cone-isPullback FP.postcomposition FP.point)

    change-computation : ConeIdentification₁
      (cone-restrict change (pullback-cone
        (FC.postcomposition ∘ Cone.left ordinary-cone) FC.point)) changed-fiber
    change-computation = pullback-factor-β changed-fiber

    module First = Nested (Cone.left ordinary-cone) FC.postcomposition FC.point
      FC.fiber (pullback-cone-isPullback FC.postcomposition FC.point)

    swap : MAP First.NestedVertex (Pullback FC.inclusion (Cone.left ordinary-cone))
    swap = pullback-swap (Cone.left ordinary-cone) FC.inclusion

    swap-isEquiv : IsEquiv swap
    swap-isEquiv = pullback-swap-isEquiv (Cone.left ordinary-cone) FC.inclusion

    swap-computation : ConeIdentification₁
      (cone-restrict swap (pullback-cone FC.inclusion (Cone.left ordinary-cone)))
      (cone-swap First.nested-cone)
    swap-computation = pullback-factor-β (cone-swap First.nested-cone)

    module Second = Nested FC.inclusion FC.postcomposition FD.postcomposition
      ordinary-cone ordinary-isPullback

    fiber-matching : (FC.postcomposition ∘ FC.inclusion) =₁
      (FC.point ∘ Cone.right FC.fiber)
    fiber-matching = Cone.match FC.fiber

    changed-middle : Cone (FC.point ∘ Cone.right FC.fiber) FD.postcomposition Second.Outer
    changed-middle = cone-change-left fiber-matching Second.outer-cone

    change-middle : MAP Second.Outer
      (Pullback (FC.point ∘ Cone.right FC.fiber) FD.postcomposition)
    change-middle = pullback-factor changed-middle

    change-middle-isEquiv : IsEquiv change-middle
    change-middle-isEquiv = isPullback-change-left fiber-matching Second.outer-cone
      (pullback-cone-isPullback (FC.postcomposition ∘ FC.inclusion) FD.postcomposition)

    change-middle-computation : ConeIdentification₁
      (cone-restrict change-middle
        (pullback-cone (FC.point ∘ Cone.right FC.fiber) FD.postcomposition)) changed-middle
    change-middle-computation = pullback-factor-β changed-middle

    module Last = Nested (Cone.right FC.fiber) FC.point FD.postcomposition
      (cone-swap FD.fiber)
      (SwappedCone.isPullback FD.fiber
        (pullback-cone-isPullback FD.postcomposition FD.point))

    module Product = TerminalBase (Cone.right FC.fiber) (Cone.right FD.fiber)

    first-insertion : MAP FP.category First.NestedVertex
    first-insertion = First.insert ∘ change

    first-insertion-isEquiv : IsEquiv first-insertion
    first-insertion-isEquiv = equiv-compose change First.insert change-isEquiv First.insert-isEquiv

    exchanged : MAP FP.category Second.NestedVertex
    exchanged = swap ∘ first-insertion

    exchanged-isEquiv : IsEquiv exchanged
    exchanged-isEquiv = equiv-compose first-insertion swap first-insertion-isEquiv swap-isEquiv

    flattened : MAP FP.category Second.Outer
    flattened = Second.flatten ∘ exchanged

    flattened-isEquiv : IsEquiv flattened
    flattened-isEquiv = equiv-compose exchanged Second.flatten exchanged-isEquiv Second.flatten-isEquiv

    changed : MAP FP.category Last.Outer
    changed = change-middle ∘ flattened

    changed-isEquiv : IsEquiv changed
    changed-isEquiv = equiv-compose flattened change-middle flattened-isEquiv change-middle-isEquiv

    separated : MAP FP.category Last.NestedVertex
    separated = Last.insert ∘ changed

    separated-isEquiv : IsEquiv separated
    separated-isEquiv = equiv-compose changed Last.insert changed-isEquiv Last.insert-isEquiv

    comparison : MAP FP.category (FC.category × FD.category)
    comparison = Product.to-product ∘ separated

    comparison-isEquiv : IsEquiv comparison
    comparison-isEquiv = equiv-compose separated Product.to-product separated-isEquiv Product.to-product-isEquiv

    equivalence : Equiv FP.category (FC.category × FD.category)
    equivalence = record { functor = comparison; isEquiv = comparison-isEquiv }
```

## The induced projections and their complete fiber diagrams

The projections land in the actual relative functor categories. Their
ordinary inclusions are native postcomposition by the two pullback legs.
Transporting the complete restricted fiber cones along these triangles
retains the specified matching, rather than asserting compatibility from
the two underlying functors alone.

```agda
    to-C : MAP FP.category FC.category
    to-C = pr₁ ∘ comparison

    to-D : MAP FP.category FD.category
    to-D = pr₂ ∘ comparison

    private
      product-left : to-C =₁ (Cone.left Last.nested-cone ∘ separated)
      product-left = restrict-triangle pr₁ Product.to-product
        (pair-β₁ (Cone.left Last.nested-cone) (Cone.right Last.nested-cone)) separated

      product-right : to-D =₁ (Cone.right Last.nested-cone ∘ separated)
      product-right = restrict-triangle pr₂ Product.to-product
        (pair-β₂ (Cone.left Last.nested-cone) (Cone.right Last.nested-cone)) separated

      separated-left : (Cone.left Last.nested-cone ∘ separated) =₁
        (Cone.right First.nested-cone ∘ first-insertion)
      separated-left =
        restrict-triangle (Cone.left Second.nested-cone) swap
          (ConeIdentification₁.left swap-computation) first-insertion ∙
        (restrict-triangle (Cone.left Second.outer-cone) Second.flatten
          (ConeIdentification₁.left Second.flatten-β) exchanged ∙
        (restrict-triangle (Cone.left Last.outer-cone) change-middle
          (ConeIdentification₁.left change-middle-computation) flattened ∙
          restrict-triangle (Cone.left Last.nested-cone) Last.insert Last.insert-left changed))

      first-right : (Cone.right First.nested-cone ∘ first-insertion) =₁
        (First.inner ∘ change)
      first-right = restrict-triangle (Cone.right First.nested-cone) First.insert First.insert-right change

      first-left-image : (FC.inclusion ∘ (First.inner ∘ change)) =₁
        (Cone.left ordinary-cone ∘ FP.inclusion)
      first-left-image =
        (Cone.left ordinary-cone ◁ ConeIdentification₁.left change-computation) ∙
        (comp-assoc change (Cone.left First.outer-cone) (Cone.left ordinary-cone) ∙
          restrict-triangle FC.inclusion First.inner First.inner-left change)

      separated-right : (Cone.right Last.nested-cone ∘ separated) =₁
        (Last.inner ∘ changed)
      separated-right = restrict-triangle (Cone.right Last.nested-cone) Last.insert Last.insert-right changed

      last-right-image : (FD.inclusion ∘ (Last.inner ∘ changed)) =₁
        (Cone.right Last.outer-cone ∘ changed)
      last-right-image = restrict-triangle FD.inclusion Last.inner Last.inner-right changed

      middle-right : (Cone.right Last.outer-cone ∘ changed) =₁
        (Cone.right Second.outer-cone ∘ flattened)
      middle-right = restrict-triangle (Cone.right Last.outer-cone) change-middle
        (ConeIdentification₁.right change-middle-computation) flattened

      flat-right-image : (Cone.right Second.outer-cone ∘ flattened) =₁
        (Cone.right ordinary-cone ∘ (Cone.right Second.nested-cone ∘ exchanged))
      flat-right-image = comp-assoc exchanged (Cone.right Second.nested-cone) (Cone.right ordinary-cone) ∙
        restrict-triangle (Cone.right Second.outer-cone) Second.flatten
          (ConeIdentification₁.right Second.flatten-β) exchanged

      exchanged-right : (Cone.right Second.nested-cone ∘ exchanged) =₁
        (Cone.left First.nested-cone ∘ first-insertion)
      exchanged-right = restrict-triangle (Cone.right Second.nested-cone) swap
        (ConeIdentification₁.right swap-computation) first-insertion

      first-left : (Cone.left First.nested-cone ∘ first-insertion) =₁ FP.inclusion
      first-left = ConeIdentification₁.left change-computation ∙
        restrict-triangle (Cone.left First.nested-cone) First.insert First.insert-left change

    left-inclusion : (FC.inclusion ∘ to-C) =₁
      (funPost {C = T} (Cone.left cone) ∘ FP.inclusion)
    left-inclusion = first-left-image ∙
      ((FC.inclusion ◁ first-right) ∙
        ((FC.inclusion ◁ separated-left) ∙ (FC.inclusion ◁ product-left)))

    right-inclusion : (FD.inclusion ∘ to-D) =₁
      (funPost {C = T} (Cone.right cone) ∘ FP.inclusion)
    right-inclusion = (Cone.right ordinary-cone ◁ first-left) ∙
      ((Cone.right ordinary-cone ◁ exchanged-right) ∙
        (flat-right-image ∙
          (middle-right ∙ (last-right-image ∙
            ((FD.inclusion ◁ separated-right) ∙ (FD.inclusion ◁ product-right))))))

    left-projection-cone : Cone FC.postcomposition FC.point FP.category
    left-projection-cone = postcompose-cone-left (Cone.left ordinary-cone)
      FC.postcomposition changed-fiber

    left-projection-computation : ConeIdentification₁
      (cone-restrict to-C FC.fiber) left-projection-cone
    left-projection-computation = cone-compose
      (postcompose-cone-left-identification (Cone.left ordinary-cone) FC.postcomposition change-computation)
      (cone-compose (postcompose-cone-left-restrict
          (Cone.left ordinary-cone) FC.postcomposition change First.outer-cone)
        (cone-compose (cone-identification-restrict-One change First.inner-β)
          (cone-compose (cone-inverse (cone-restrict-assoc change First.inner FC.fiber))
            (cone-action-One FC.fiber (first-right ∙ (separated-left ∙ product-left))))))

    right-projection-cone : Cone FC.point FD.postcomposition FP.category
    right-projection-cone = postcompose-cone-left (Cone.right FC.fiber) FC.point
      (cone-restrict flattened changed-middle)

    right-projection-computation : ConeIdentification₁
      (cone-restrict to-D (cone-swap FD.fiber)) right-projection-cone
    right-projection-computation = cone-compose
      (postcompose-cone-left-identification (Cone.right FC.fiber) FC.point
        (cone-identification-restrict-One flattened change-middle-computation))
      (cone-compose (postcompose-cone-left-identification (Cone.right FC.fiber) FC.point
          (cone-inverse (cone-restrict-assoc flattened change-middle Last.outer-cone)))
      (cone-compose (postcompose-cone-left-restrict (Cone.right FC.fiber) FC.point changed Last.outer-cone)
        (cone-compose (cone-identification-restrict-One changed Last.inner-β)
          (cone-compose (cone-inverse (cone-restrict-assoc changed Last.inner (cone-swap FD.fiber)))
            (cone-action-One (cone-swap FD.fiber) (separated-right ∙ product-right))))))
```
