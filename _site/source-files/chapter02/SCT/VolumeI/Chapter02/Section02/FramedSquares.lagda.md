# Framed squares as morphisms in the arrow category

A framed square is a morphism between its left and right arrow families.
Evaluating at the two interval endpoints gives its horizontal sides. Their
comparisons with the prescribed top and bottom are comparisons of framed
families, so they include all four corner equations.

Horizontal composition is composition in the arrow category. Preservation
under evaluation and change of endpoint frames identify the resulting top
and bottom with the prescribed composites. This is the algebra of squares;
constructing such data by gluing geometric triangles is a separate step.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter02.Section02.FramedSquares where
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
import Agda.Builtin.Sigma as Data
open import SCT.VolumeI.Chapter02.Section01.Morphisms
  using (Ar; ev₀; ev₁; MorphismFamily; MorphismFamilyIdentification)
open import SCT.VolumeI.Chapter02.Section01.MorphismFunctor using (map-morphism-family)
open import SCT.VolumeI.Chapter02.Section01.MorphismFamilyOperations
  using (retarget-family; retarget-family-comparison)
open import SCT.VolumeI.Chapter02.Section01.MorphismFamilyComparisons using (compose-family-comparisons)
open import SCT.VolumeI.Chapter02.Section01.Triangles using (short-edges)
open import SCT.VolumeI.Chapter02.Section02.MorphismCompositionComparisons using (module CompositionComparisons)
open import SCT.VolumeI.Chapter02.Section02.MorphismCompositionTransport using (module CompositionTransport)
open import SCT.VolumeI.Chapter02.Section02.MorphismCompositionPostcomposition using (module FunctorComposition)
import SCT.VolumeI.Chapter02.Section02.MorphismComposition as MC

module _ {Γ : Context} where
  framed-image : {P C D : CAT Γ} (F : MAP C D) {f g : MAP P C}
    (alpha : MorphismFamily f g) {x y : MAP P D}
    → (F ∘ f) =₁ x → (F ∘ g) =₁ y → MorphismFamily x y
  framed-image F alpha p q = retarget-family (map-morphism-family F alpha) p q

  FramedSquare : {P C : CAT Γ} {x y z w : MAP P C}
    (top : MorphismFamily x y) (right : MorphismFamily y z)
    (left : MorphismFamily x w) (bottom : MorphismFamily w z) → Set m
  FramedSquare {C = C} top right left bottom =
    Data.Σ (MorphismFamily (MorphismFamily.arrow left) (MorphismFamily.arrow right)) λ vertical →
    Data.Σ (MorphismFamilyIdentification One
      (framed-image (ev₀ {C = C}) vertical (MorphismFamily.source-frame left)
        (MorphismFamily.source-frame right)) top) λ _ →
      MorphismFamilyIdentification One
        (framed-image (ev₁ {C = C}) vertical (MorphismFamily.target-frame left)
          (MorphismFamily.target-frame right)) bottom

  framed-square : {P C : CAT Γ} {x y z w : MAP P C}
    {top : MorphismFamily x y} {right : MorphismFamily y z}
    {left : MorphismFamily x w} {bottom : MorphismFamily w z}
    (vertical : MorphismFamily (MorphismFamily.arrow left) (MorphismFamily.arrow right))
    → MorphismFamilyIdentification One
        (framed-image (ev₀ {C = C}) vertical (MorphismFamily.source-frame left)
          (MorphismFamily.source-frame right)) top
    → MorphismFamilyIdentification One
        (framed-image (ev₁ {C = C}) vertical (MorphismFamily.target-frame left)
          (MorphismFamily.target-frame right)) bottom
    → FramedSquare top right left bottom
  framed-square vertical top bottom = Data._,_ vertical (Data._,_ top bottom)

  module SquareFamily {P C : CAT Γ} {x y z w : MAP P C}
    {top : MorphismFamily x y} {right : MorphismFamily y z}
    {left : MorphismFamily x w} {bottom : MorphismFamily w z}
    (given : FramedSquare top right left bottom) where
    vertical : MorphismFamily (MorphismFamily.arrow left) (MorphismFamily.arrow right)
    vertical = Data.fst given
    top-edge : MorphismFamilyIdentification One
      (framed-image (ev₀ {C = C}) vertical (MorphismFamily.source-frame left)
        (MorphismFamily.source-frame right)) top
    top-edge = Data.fst (Data.snd given)
    bottom-edge : MorphismFamilyIdentification One
      (framed-image (ev₁ {C = C}) vertical (MorphismFamily.target-frame left)
        (MorphismFamily.target-frame right)) bottom
    bottom-edge = Data.snd (Data.snd given)

module SquareComposition {Γ : Context} (C : CAT Γ)
  (segal : IsEquiv (short-edges C)) (arrow-segal : IsEquiv (short-edges (Ar C))) where
  private
    module Base = MC.Composition C segal
    module Arrow = MC.Composition (Ar C) arrow-segal
    module Comparisons = CompositionComparisons C segal
    module Transport = CompositionTransport C segal

  evaluated-composition : {P : CAT Γ} {l k r : MAP P (Ar C)}
    (B : MorphismFamily k r) (A : MorphismFamily l k) (v : MAP (Ar C) C)
    {x y z : MAP P C} (p : (v ∘ l) =₁ x) (q : (v ∘ k) =₁ y) (s : (v ∘ r) =₁ z)
    → MorphismFamilyIdentification One (framed-image v (Arrow.compose B A) p s)
        (Base.compose (framed-image v B q s) (framed-image v A p q))
  evaluated-composition B A v p q s = compose-family-comparisons
    (Transport.retarget-composition (map-morphism-family v B) (map-morphism-family v A) p q s)
    (retarget-family-comparison p s
      (FunctorComposition.preserves-composition v arrow-segal segal B A))

  module Compose {P : CAT Γ} {x₀ x₁ x₂ y₀ y₁ y₂ : MAP P C}
    {top₀ : MorphismFamily x₀ x₁} {top₁ : MorphismFamily x₁ x₂}
    {bottom₀ : MorphismFamily y₀ y₁} {bottom₁ : MorphismFamily y₁ y₂}
    {left : MorphismFamily x₀ y₀} {middle : MorphismFamily x₁ y₁} {right : MorphismFamily x₂ y₂}
    (A : FramedSquare top₀ middle left bottom₀) (B : FramedSquare top₁ right middle bottom₁) where
    private
      module S = SquareFamily A
      module T = SquareFamily B
      module L = MorphismFamily left
      module M = MorphismFamily middle
      module R = MorphismFamily right
    value : FramedSquare (Base.compose top₁ top₀) right left (Base.compose bottom₁ bottom₀)
    value = framed-square (Arrow.compose T.vertical S.vertical)
      (compose-family-comparisons (Comparisons.composition-comparison T.top-edge S.top-edge)
        (evaluated-composition T.vertical S.vertical ev₀ L.source-frame M.source-frame R.source-frame))
      (compose-family-comparisons (Comparisons.composition-comparison T.bottom-edge S.bottom-edge)
        (evaluated-composition T.vertical S.vertical ev₁ L.target-frame M.target-frame R.target-frame))
```
