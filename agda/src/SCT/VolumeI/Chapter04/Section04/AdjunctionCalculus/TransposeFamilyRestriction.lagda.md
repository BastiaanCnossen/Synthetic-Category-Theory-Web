# Restricting transposition over a fixed base

The associator frames in the fixed-base formulas commute with restriction
by the pentagon. Combining these frame comparisons with the component
restriction laws supplies the restriction fields for the two endpoint
operations. No inverse equation is used here.

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
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionFrameCalculus 𝒯 M ℱ I using (retarget-cong)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionFrameSquares 𝒯 M ℱ I
  using (restrict-frame-square; restrict-inverse-frames; cancel-frames)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionRestriction 𝒯 M ℱ I using (restrict-expressionIso)
open import SCT.VolumeI.Chapter02.Section01.DiagramCalculus.ExpressionComparisons 𝒯 M ℱ P I
  using (reflect-retarget-comparison)
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.EndpointFiberLifts as Lifts
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.TransposeFamilies as Families
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.TransposeRestriction as Restriction
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.TransposeComparisons as Comparisons
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.IteratedPairing as Iterated
open Iterated vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (pentagon-whiskered)

private
  abstract
    id-inverse : {Γ C : CAT} (f : MAP Γ C) → (idIso f) ⁻¹ =₂ idIso f
    id-inverse f = isoComp-inverseʳ-at (idIso f) ∙ (isoComp-unitˡ-at ((idIso f) ⁻¹)) ⁻¹

    unit-pre : {Γ Δ C : CAT} (f : MAP Γ C) (h : MAP Δ Γ) {g : MAP Δ C} (a : (f ∘ h) =₁ g) →
      (idIso g ∙ a) =₂ (a ∙ (idIso f ▷ h))
    unit-pre f h a = (isoComp-cong (idIso a) (preWhisker-idIso f h)) ⁻¹ ∙
      (isoComp-unitʳ-at a) ⁻¹ ∙ isoComp-unitˡ-at a

    flat-pentagon : {Δ Γ B C D : CAT} (h : MAP Δ Γ) (b : MAP Γ B) (x : MAP B C) (l : MAP C D) →
      (comp-assoc (b ∘ h) x l ∙ comp-assoc h b (l ∘ x)) =₂
      (((l ◁ comp-assoc h b x) ∙ comp-assoc h (x ∘ b) l) ∙ (comp-assoc b x l ▷ h))
    flat-pentagon h b x l =
      (isoComp-assoc-at (l ◁ comp-assoc h b x) (comp-assoc h (x ∘ b) l) (comp-assoc b x l ▷ h)) ⁻¹ ∙
      pentagon-whiskered h b x l

module RestrictionFamilies {B C D : CAT} {l : MAP C D} {r : MAP D C}
  (adj : Adjunction l r) (x : MAP B C) (y : MAP B D) where
  private
    module A = Adjunction adj
    module F = Families.Families 𝒯 M ℱ P I E S adj x y using (left-normal; right-normal; forward; backward)
    module N = Comparisons.Comparisons 𝒯 M ℱ P I E S adj using (transpose-cong; untranspose-cong)
    module R = Restriction.RestrictionLaws 𝒯 M ℱ P I E S adj using (transpose-restrict-change; untranspose-restrict-change)
    module L = Lifts.Lifts 𝒯 M ℱ P I (l ∘ x) y using (restrict)
    module K = Lifts.Lifts 𝒯 M ℱ P I x (r ∘ y) using (restrict)

  abstract
    left-normal-restrict : {Γ Δ : CAT} (b : MAP Γ B)
      (f : MorphismExpression ((l ∘ x) ∘ b) (y ∘ b)) (h : MAP Δ Γ) →
      ExpressionIso (retarget-expression (restrict-expression (F.left-normal b f) h)
        ((l ◁ comp-assoc h b x) ∙ comp-assoc h (x ∘ b) l) (comp-assoc h b y))
        (F.left-normal (b ∘ h) (L.restrict b f h))
    left-normal-restrict b f h = restrict-frame-square f (comp-assoc b x l) (idIso (y ∘ b)) h
      ((l ◁ comp-assoc h b x) ∙ comp-assoc h (x ∘ b) l) (comp-assoc h b y)
      (comp-assoc h b (l ∘ x)) (comp-assoc h b y) (comp-assoc (b ∘ h) x l) (idIso (y ∘ (b ∘ h)))
      ((flat-pentagon h b x l) ⁻¹) ((unit-pre (y ∘ b) h (comp-assoc h b y)) ⁻¹)

    right-normal-restrict : {Γ Δ : CAT} (b : MAP Γ B)
      (f : MorphismExpression (x ∘ b) ((r ∘ y) ∘ b)) (h : MAP Δ Γ) →
      ExpressionIso (retarget-expression (restrict-expression (F.right-normal b f) h)
        (comp-assoc h b x) ((r ◁ comp-assoc h b y) ∙ comp-assoc h (y ∘ b) r))
        (F.right-normal (b ∘ h) (K.restrict b f h))
    right-normal-restrict b f h = restrict-frame-square f (idIso (x ∘ b)) (comp-assoc b y r) h
      (comp-assoc h b x) ((r ◁ comp-assoc h b y) ∙ comp-assoc h (y ∘ b) r)
      (comp-assoc h b x) (comp-assoc h b (r ∘ y)) (idIso (x ∘ (b ∘ h))) (comp-assoc (b ∘ h) y r)
      ((unit-pre (x ∘ b) h (comp-assoc h b x)) ⁻¹) ((flat-pentagon h b y r) ⁻¹)

    forward-restrict : {Γ Δ : CAT} (b : MAP Γ B)
      (f : MorphismExpression ((l ∘ x) ∘ b) (y ∘ b)) (h : MAP Δ Γ) →
      ExpressionIso (K.restrict b (F.forward b f) h) (F.forward (b ∘ h) (L.restrict b f h))
    forward-restrict b f h = reflect-retarget-comparison _ _
      (idIso (x ∘ (b ∘ h))) (comp-assoc (b ∘ h) y r)
      (expressionIso-compose (expressionIso-inverse
        (cancel-frames (A.transpose (x ∘ (b ∘ h)) (y ∘ (b ∘ h)) (F.left-normal (b ∘ h) (L.restrict b f h)))
          (idIso (x ∘ (b ∘ h))) ((comp-assoc (b ∘ h) y r) ⁻¹)
          (idIso (x ∘ (b ∘ h))) (comp-assoc (b ∘ h) y r)
          (isoComp-unitˡ-at (idIso (x ∘ (b ∘ h)))) (isoComp-inverseʳ-at (comp-assoc (b ∘ h) y r))))
        (expressionIso-compose
          (N.transpose-cong (x ∘ (b ∘ h)) (y ∘ (b ∘ h)) (left-normal-restrict b f h))
          (expressionIso-compose
            (R.transpose-restrict-change (x ∘ b) (y ∘ b) (F.left-normal b f) h (comp-assoc h b x) (comp-assoc h b y))
            (expressionIso-compose
              (restrict-inverse-frames (A.transpose (x ∘ b) (y ∘ b) (F.left-normal b f))
                (idIso (x ∘ b)) (comp-assoc b y r) h
                (comp-assoc h b x) (comp-assoc h b (r ∘ y))
                (idIso (x ∘ (b ∘ h))) (comp-assoc (b ∘ h) y r)
                (comp-assoc h b x) ((r ◁ comp-assoc h b y) ∙ comp-assoc h (y ∘ b) r)
                (unit-pre (x ∘ b) h (comp-assoc h b x)) (flat-pentagon h b y r))
              (retarget-expressionIso
                (retarget-expressionIso
                  (restrict-expressionIso
                    (retarget-cong (A.transpose (x ∘ b) (y ∘ b) (F.left-normal b f))
                      ((id-inverse (x ∘ b)) ⁻¹) (idIso ((comp-assoc b y r) ⁻¹))) h)
                  (comp-assoc h b x) (comp-assoc h b (r ∘ y)))
                (idIso (x ∘ (b ∘ h))) (comp-assoc (b ∘ h) y r))))))

    backward-restrict : {Γ Δ : CAT} (b : MAP Γ B)
      (f : MorphismExpression (x ∘ b) ((r ∘ y) ∘ b)) (h : MAP Δ Γ) →
      ExpressionIso (L.restrict b (F.backward b f) h) (F.backward (b ∘ h) (K.restrict b f h))
    backward-restrict b f h = reflect-retarget-comparison _ _
      (comp-assoc (b ∘ h) x l) (idIso (y ∘ (b ∘ h)))
      (expressionIso-compose (expressionIso-inverse
        (cancel-frames (A.untranspose (x ∘ (b ∘ h)) (y ∘ (b ∘ h)) (F.right-normal (b ∘ h) (K.restrict b f h)))
          ((comp-assoc (b ∘ h) x l) ⁻¹) (idIso (y ∘ (b ∘ h)))
          (comp-assoc (b ∘ h) x l) (idIso (y ∘ (b ∘ h)))
          (isoComp-inverseʳ-at (comp-assoc (b ∘ h) x l)) (isoComp-unitˡ-at (idIso (y ∘ (b ∘ h))))))
        (expressionIso-compose
          (N.untranspose-cong (x ∘ (b ∘ h)) (y ∘ (b ∘ h)) (right-normal-restrict b f h))
          (expressionIso-compose
            (R.untranspose-restrict-change (x ∘ b) (y ∘ b) (F.right-normal b f) h (comp-assoc h b x) (comp-assoc h b y))
            (expressionIso-compose
              (restrict-inverse-frames (A.untranspose (x ∘ b) (y ∘ b) (F.right-normal b f))
                (comp-assoc b x l) (idIso (y ∘ b)) h
                (comp-assoc h b (l ∘ x)) (comp-assoc h b y)
                (comp-assoc (b ∘ h) x l) (idIso (y ∘ (b ∘ h)))
                ((l ◁ comp-assoc h b x) ∙ comp-assoc h (x ∘ b) l) (comp-assoc h b y)
                (flat-pentagon h b x l) (unit-pre (y ∘ b) h (comp-assoc h b y)))
              (retarget-expressionIso
                (retarget-expressionIso
                  (restrict-expressionIso
                    (retarget-cong (A.untranspose (x ∘ b) (y ∘ b) (F.right-normal b f))
                      (idIso ((comp-assoc b x l) ⁻¹)) ((id-inverse (y ∘ b)) ⁻¹)) h)
                  (comp-assoc h b (l ∘ x)) (comp-assoc h b y))
                (comp-assoc (b ∘ h) x l) (idIso (y ∘ (b ∘ h))))))))
```
