# Restricting transposition over a fixed base

The associator frames in the fixed-base formulas commute with restriction
by the pentagon. The endpoint-family constructors combine that square with
the component restriction laws while assembling the operations. The statements
here expose those fields in the established endpoint-pullback notation.
No inverse equation is used here.

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

module SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.TransposeFamilyRestriction
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter04.Section04.Adjunctions 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionFamilies 𝒯 M ℱ I
  using (FamilyOperation)
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.EndpointFiberLifts as Lifts
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.TransposeFamilies as Families

module RestrictionFamilies {B C D : CAT} {l : MAP C D} {r : MAP D C}
  (adj : Adjunction l r) (x : MAP B C) (y : MAP B D) where
  private
    module F = Families.Families 𝒯 M ℱ P I E S adj x y
      using (left-normal; right-normal; forward; backward; normalize-left; normalize-right; forward-family; backward-family)
    module L = Lifts.Lifts 𝒯 M ℱ P I (l ∘ x) y using (restrict)
    module K = Lifts.Lifts 𝒯 M ℱ P I x (r ∘ y) using (restrict)

  abstract
    left-normal-restrict : {Γ Δ : CAT} (b : MAP Γ B)
      (f : MorphismExpression ((l ∘ x) ∘ b) (y ∘ b)) (h : MAP Δ Γ) →
      ExpressionIso (retarget-expression (restrict-expression (F.left-normal b f) h)
        ((l ◁ comp-assoc h b x) ∙ comp-assoc h (x ∘ b) l) (comp-assoc h b y))
        (F.left-normal (b ∘ h) (L.restrict b f h))
    left-normal-restrict b f h = FamilyOperation.on-restriction F.normalize-left b f h

    right-normal-restrict : {Γ Δ : CAT} (b : MAP Γ B)
      (f : MorphismExpression (x ∘ b) ((r ∘ y) ∘ b)) (h : MAP Δ Γ) →
      ExpressionIso (retarget-expression (restrict-expression (F.right-normal b f) h)
        (comp-assoc h b x) ((r ◁ comp-assoc h b y) ∙ comp-assoc h (y ∘ b) r))
        (F.right-normal (b ∘ h) (K.restrict b f h))
    right-normal-restrict b f h = FamilyOperation.on-restriction F.normalize-right b f h

    forward-restrict : {Γ Δ : CAT} (b : MAP Γ B)
      (f : MorphismExpression ((l ∘ x) ∘ b) (y ∘ b)) (h : MAP Δ Γ) →
      ExpressionIso (K.restrict b (F.forward b f) h) (F.forward (b ∘ h) (L.restrict b f h))
    forward-restrict b f h = FamilyOperation.on-restriction F.forward-family b f h

    backward-restrict : {Γ Δ : CAT} (b : MAP Γ B)
      (f : MorphismExpression (x ∘ b) ((r ∘ y) ∘ b)) (h : MAP Δ Γ) →
      ExpressionIso (L.restrict b (F.backward b f) h) (F.backward (b ∘ h) (K.restrict b f h))
    backward-restrict b f h = FamilyOperation.on-restriction F.backward-family b f h

```
