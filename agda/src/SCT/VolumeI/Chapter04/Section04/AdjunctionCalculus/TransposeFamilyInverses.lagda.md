# Inverse equations for transposition over a base

The component inverse laws give an equivalence before the endpoints are
normalized. Normalize the source, apply that equivalence, and undo the target
normalization. Composition and endpoint transport of family equivalences supply
the inverse equations together with all finite operation fields.
The explicit forward and backward formulas remain those of TransposeFamilies.

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
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionFamilyEquivalences 𝒯 M ℱ I
  using (FamilyEquivalence; represented; post; associator-frame; comparison-equivalence;
    identity-endpoint-equivalence; transport-family-equivalence;
    compose-family-equivalences; inverse-family-equivalence)
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.TransposeFamilies as Families
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.TransposeIdentifications as Inverses

module InverseFamilies {B C D : CAT} {l : MAP C D} {r : MAP D C}
  (adj : Adjunction l r) (x : MAP B C) (y : MAP B D) where
  private
    module F = Families.Families 𝒯 M ℱ P I E S adj x y
      using (forward; backward; raw-forward; raw-backward)
    module V = Inverses.InverseLaws 𝒯 M ℱ P I E S Q adj
      using (untranspose-transpose; transpose-untranspose)

    raw-equivalence : FamilyEquivalence (post l (represented x)) (represented y)
      (represented x) (post r (represented y))
    raw-equivalence = record
      { forward = F.raw-forward ; backward = F.raw-backward
      ; backward-forward = λ b f → V.untranspose-transpose (x ∘ b) (y ∘ b) f
      ; forward-backward = λ b g → V.transpose-untranspose (x ∘ b) (y ∘ b) g }

    left-normalization : FamilyEquivalence (represented (l ∘ x)) (represented y)
      (post l (represented x)) (represented y)
    left-normalization = transport-family-equivalence
      {u = represented (l ∘ x)} {v = represented y}
      {s = post l (represented x)} {t = represented y}
      (comparison-equivalence {u = represented (l ∘ x)} {v = post l (represented x)} (associator-frame x l))
      (identity-endpoint-equivalence (represented y))

    right-normalization : FamilyEquivalence (represented x) (represented (r ∘ y))
      (represented x) (post r (represented y))
    right-normalization = transport-family-equivalence
      {u = represented x} {v = represented (r ∘ y)}
      {s = represented x} {t = post r (represented y)}
      (identity-endpoint-equivalence (represented x))
      (comparison-equivalence {u = represented (r ∘ y)} {v = post r (represented y)} (associator-frame y r))

  family-equivalence : FamilyEquivalence (represented (l ∘ x)) (represented y)
    (represented x) (represented (r ∘ y))
  family-equivalence = compose-family-equivalences
    {u = represented (l ∘ x)} {v = represented y}
    {s = represented x} {t = post r (represented y)}
    {x = represented x} {y = represented (r ∘ y)}
    (inverse-family-equivalence right-normalization)
    (compose-family-equivalences
      {u = represented (l ∘ x)} {v = represented y}
      {s = post l (represented x)} {t = represented y}
      {x = represented x} {y = post r (represented y)} raw-equivalence left-normalization)

  abstract
    backward-forward : {Γ : CAT} (b : MAP Γ B)
      (f : MorphismExpression ((l ∘ x) ∘ b) (y ∘ b)) →
      ExpressionIso (F.backward b (F.forward b f)) f
    backward-forward b f = FamilyEquivalence.backward-forward family-equivalence b f

    forward-backward : {Γ : CAT} (b : MAP Γ B)
      (f : MorphismExpression (x ∘ b) ((r ∘ y) ∘ b)) →
      ExpressionIso (F.forward b (F.backward b f)) f
    forward-backward b f = FamilyEquivalence.forward-backward family-equivalence b f
```
