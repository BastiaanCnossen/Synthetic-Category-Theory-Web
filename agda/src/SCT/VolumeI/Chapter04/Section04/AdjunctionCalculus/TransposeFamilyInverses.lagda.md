# Inverse equations for transposition over a base

Normalizing and then restoring an endpoint frame gives the original
expression. Applying these cancellations to the two component inverse
laws proves that the transposition operations over a fixed base are
inverse. The statement remains at the expression level; realization
uses the separate restriction and base-change comparisons.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section02.SegalAxiom as Segal
import SCT.VolumeI.Chapter02.Section01.CommutativeSquareAxiom as Squares

module SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.TransposeFamilyInverses
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter04.Section04.Adjunctions 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionFrameSquares 𝒯 M ℱ I using (cancel-frames)
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.TransposeFamilies as Families
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.TransposeIdentifications as Inverses
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.TransposeComparisons as Comparisons

module InverseFamilies {B C D : CAT} {l : MAP C D} {r : MAP D C}
  (adj : Adjunction l r) (x : MAP B C) (y : MAP B D) where
  private
    module A = Adjunction adj
    module F = Families.Families 𝒯 M ℱ P I E S adj x y using (left-normal; right-normal; forward; backward)
    module V = Inverses.InverseLaws 𝒯 M ℱ P I E S Q adj using (untranspose-transpose; transpose-untranspose)
    module N = Comparisons.Comparisons 𝒯 M ℱ P I E S adj using (transpose-cong; untranspose-cong)

  abstract
    backward-forward : {Γ : CAT} (b : MAP Γ B)
      (f : MorphismExpression ((l ∘ x) ∘ b) (y ∘ b)) →
      ExpressionIso (F.backward b (F.forward b f)) f
    backward-forward b f = expressionIso-compose
      (cancel-frames f (comp-assoc b x l) (idIso (y ∘ b)) ((comp-assoc b x l) ⁻¹) (idIso (y ∘ b))
        (isoComp-inverseˡ-at (comp-assoc b x l)) (isoComp-unitˡ-at (idIso (y ∘ b))))
      (retarget-expressionIso
        (expressionIso-compose (V.untranspose-transpose (x ∘ b) (y ∘ b) (F.left-normal b f))
          (N.untranspose-cong (x ∘ b) (y ∘ b)
            (cancel-frames (A.transpose (x ∘ b) (y ∘ b) (F.left-normal b f))
              (idIso (x ∘ b)) ((comp-assoc b y r) ⁻¹) (idIso (x ∘ b)) (comp-assoc b y r)
              (isoComp-unitˡ-at (idIso (x ∘ b))) (isoComp-inverseʳ-at (comp-assoc b y r)))))
        ((comp-assoc b x l) ⁻¹) (idIso (y ∘ b)))

    forward-backward : {Γ : CAT} (b : MAP Γ B)
      (f : MorphismExpression (x ∘ b) ((r ∘ y) ∘ b)) →
      ExpressionIso (F.forward b (F.backward b f)) f
    forward-backward b f = expressionIso-compose
      (cancel-frames f (idIso (x ∘ b)) (comp-assoc b y r) (idIso (x ∘ b)) ((comp-assoc b y r) ⁻¹)
        (isoComp-unitˡ-at (idIso (x ∘ b))) (isoComp-inverseˡ-at (comp-assoc b y r)))
      (retarget-expressionIso
        (expressionIso-compose (V.transpose-untranspose (x ∘ b) (y ∘ b) (F.right-normal b f))
          (N.transpose-cong (x ∘ b) (y ∘ b)
            (cancel-frames (A.untranspose (x ∘ b) (y ∘ b) (F.right-normal b f))
              ((comp-assoc b x l) ⁻¹) (idIso (y ∘ b)) (comp-assoc b x l) (idIso (y ∘ b))
              (isoComp-inverseʳ-at (comp-assoc b x l)) (isoComp-unitˡ-at (idIso (y ∘ b))))))
        (idIso (x ∘ b)) ((comp-assoc b y r) ⁻¹))
```
