# Triangle identities at arbitrary parameters

Restricting a triangle identity gives the triangle identity for the
normalized components. The proof explicitly compares the two legs:
postcomposition commutes with restriction, iterated restriction
associates, and the external pentagon and unit laws identify the
intermediate endpoint frames.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section02.SegalAxiom as Segal

module SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.ComponentTriangles
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter04.Section04.Adjunctions 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionFrameCalculus 𝒯 M ℱ I
  using (restrict-retarget-outer; retarget-cong; retarget-assoc; retarget-id; post-retarget)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionRestriction 𝒯 M ℱ I
  using (restrict-expressionIso; restrict-expression-compose)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionRestrictionPostcomposition 𝒯 M ℱ I
  using (restrict-post)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositionIdentifications 𝒯 M ℱ P I E S
  using (compose-expression-cong)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositionSubstitution 𝒯 M ℱ P I E S
  using (restrict-composition; retarget-composition)
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.IdentityExpressionSubstitution as IdRestriction
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.IteratedPairing as Iterated
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingUnits as TriangleUnits
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.ProductFunctorUnits as LeftUnits
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN
open Iterated vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (pentagon-whiskered; pre-inverse-at)
open TriangleUnits vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (triangle-whiskered)
open LeftUnits vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (left-unitor-comp)
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-right)

open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionRestrictionFrames 𝒯 M ℱ I
  using (restrict-post-retarget; restrict-restriction-retarget)

private
  corner : {Γ C D : CAT} (x : MAP Γ C) (l : MAP C D) (r : MAP D C) →
    (((l ∘ r) ∘ l) ∘ x) =₁ (l ∘ (r ∘ (l ∘ x)))
  corner x l r = comp-assoc (l ∘ x) r l ∙ comp-assoc x l (l ∘ r)

  corner-cancel : {Γ C D : CAT} (x : MAP Γ C) (l : MAP C D) (r : MAP D C) →
    (corner x l r ∙ ((comp-assoc l r l) ⁻¹ ▷ x)) =₂
    ((l ◁ comp-assoc x l r) ∙ comp-assoc x (r ∘ l) l)
  corner-cancel x l r = cancel-right (comp-assoc l r l ▷ x)
    ((l ◁ comp-assoc x l r) ∙ comp-assoc x (r ∘ l) l) ∙
    isoComp-cong
      ((isoComp-assoc-at (l ◁ comp-assoc x l r) (comp-assoc x (r ∘ l) l)
        (comp-assoc l r l ▷ x)) ⁻¹ ∙ pentagon-whiskered x l r l)
      (idIso ((comp-assoc l r l ▷ x) ⁻¹)) ∙
    isoComp-cong (idIso (corner x l r)) (pre-inverse-at (comp-assoc l r l) x)

  outer-id : {Γ Δ C : CAT} {f : MAP Γ C} (x : MAP Δ Γ)
    {z : MAP Δ C} (a : (f ∘ x) =₁ z) → (a ∙ (idIso f ▷ x)) =₂ a
  outer-id {f = f} x a = isoComp-unitʳ-at a ∙
    isoComp-cong (idIso a) (preWhisker-idIso f x)

module Components {C D : CAT} {l : MAP C D} {r : MAP D C}
  (adj : Adjunction l r) where
  private module A = Adjunction adj

  abstract
    left-unit-component : {Γ : CAT} (x : MAP Γ C) →
      ExpressionIso (retarget-expression (restrict-expression A.left-unit x)
        (idIso (l ∘ x)) (corner x l r)) (post-expression l (A.unit-at x))
    left-unit-component x = expressionIso-compose (expressionIso-inverse (post-retarget l
      (restrict-expression A.unit x) (comp-unitˡ x) (comp-assoc x l r)))
      (restrict-post-retarget l A.unit x (comp-unitʳ l) ((comp-assoc l r l) ⁻¹)
        (idIso (l ∘ x)) (corner x l r) (l ◁ comp-unitˡ x) (l ◁ comp-assoc x l r)
        (triangle-whiskered x l ∙ isoComp-unitˡ-at (comp-unitʳ l ▷ x))
        (corner-cancel x l r))

    left-counit-component : {Γ : CAT} (x : MAP Γ C) →
      ExpressionIso (retarget-expression (restrict-expression A.left-counit x)
        (corner x l r) (idIso (l ∘ x))) (A.counit-at (l ∘ x))
    left-counit-component x = restrict-restriction-retarget A.counit l x
      (idIso ((l ∘ r) ∘ l)) (comp-unitˡ l) (corner x l r) (idIso (l ∘ x))
      (comp-assoc (l ∘ x) r l) (comp-unitˡ (l ∘ x))
      (outer-id x (corner x l r))
      ((left-unitor-comp x l) ⁻¹ ∙ isoComp-unitˡ-at (comp-unitˡ l ▷ x))

    right-unit-component : {Γ : CAT} (y : MAP Γ D) →
      ExpressionIso (retarget-expression (restrict-expression A.right-unit y)
        (idIso (r ∘ y)) (corner y r l)) (A.unit-at (r ∘ y))
    right-unit-component y = restrict-restriction-retarget A.unit r y
      (comp-unitˡ r) (idIso ((r ∘ l) ∘ r)) (idIso (r ∘ y)) (corner y r l)
      (comp-unitˡ (r ∘ y)) (comp-assoc (r ∘ y) l r)
      ((left-unitor-comp y r) ⁻¹ ∙ isoComp-unitˡ-at (comp-unitˡ r ▷ y))
      (outer-id y (corner y r l))

    right-counit-component : {Γ : CAT} (y : MAP Γ D) →
      ExpressionIso (retarget-expression (restrict-expression A.right-counit y)
        (corner y r l) (idIso (r ∘ y))) (post-expression r (A.counit-at y))
    right-counit-component y = expressionIso-compose (expressionIso-inverse (post-retarget r
      (restrict-expression A.counit y) (comp-assoc y r l) (comp-unitˡ y)))
      (restrict-post-retarget r A.counit y ((comp-assoc r l r) ⁻¹) (comp-unitʳ r)
        (corner y r l) (idIso (r ∘ y)) (r ◁ comp-assoc y r l) (r ◁ comp-unitˡ y)
        (corner-cancel y r l)
        (triangle-whiskered y r ∙ isoComp-unitˡ-at (comp-unitʳ r ▷ y)))

    left-triangle-at : {Γ : CAT} (x : MAP Γ C) →
      ExpressionIso (compose-expression (post-expression l (A.unit-at x)) (A.counit-at (l ∘ x)))
        (identity-expression (l ∘ x))
    left-triangle-at x = expressionIso-compose (IdRestriction.Restrict.comparison 𝒯 M ℱ P I E l x)
      (expressionIso-compose (restrict-expressionIso A.left-triangle x)
        (expressionIso-compose (restrict-composition A.left-unit A.left-counit x)
          (expressionIso-compose (retarget-id _)
            (expressionIso-compose (retarget-composition (restrict-expression A.left-unit x)
              (restrict-expression A.left-counit x) (idIso (l ∘ x)) (corner x l r) (idIso (l ∘ x)))
              (expressionIso-inverse (compose-expression-cong (left-unit-component x) (left-counit-component x)))))))

    right-triangle-at : {Γ : CAT} (y : MAP Γ D) →
      ExpressionIso (compose-expression (A.unit-at (r ∘ y)) (post-expression r (A.counit-at y)))
        (identity-expression (r ∘ y))
    right-triangle-at y = expressionIso-compose (IdRestriction.Restrict.comparison 𝒯 M ℱ P I E r y)
      (expressionIso-compose (restrict-expressionIso A.right-triangle y)
        (expressionIso-compose (restrict-composition A.right-unit A.right-counit y)
          (expressionIso-compose (retarget-id _)
            (expressionIso-compose (retarget-composition (restrict-expression A.right-unit y)
              (restrict-expression A.right-counit y) (idIso (r ∘ y)) (corner y r l) (idIso (r ∘ y)))
              (expressionIso-inverse (compose-expression-cong (right-unit-component y) (right-counit-component y)))))))
```
