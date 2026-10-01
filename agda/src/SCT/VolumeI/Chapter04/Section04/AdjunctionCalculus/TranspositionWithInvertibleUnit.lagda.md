# Transposition with an invertible unit

A specified identification representing the unit turns adjunction
transposition into postcomposition by the right adjoint with a change of
source frame. The component frame is recorded literally, including its
associator and unit identification. Both endpoint equations are retained.
This lemma takes the identification and its expression comparison as data;
Rezk recovery can supply them for a left adjoint section.

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
import SCT.VolumeI.Chapter02.Section01.CommutativeSquareAxiom as Squares

module SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.TranspositionWithInvertibleUnit
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter04.Section04.Adjunctions 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionRestriction 𝒯 M ℱ I
  using (restrict-expressionIso)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositionIdentifications 𝒯 M ℱ P I E S
  using (compose-expression-cong)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.IsomorphismExpressionOperations 𝒯 M ℱ P I E
  using (isomorphism-restrict; isomorphism-retarget; isomorphism-cong)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositionWithIdentifications 𝒯 M ℱ P I E S
  using (precompose-identification)

open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionFrameCalculus 𝒯 M ℱ I
  using (post-retarget; retarget-assoc; retarget-cong)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯
  using (inverse-composite; inverse-identity; pre-inverse)
open import SCT.VolumeI.Chapter01.Section04.ProductCalculus.ProductAssociativity 𝒯 M
  using (cancel-inverse-tail)
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.ComponentRestriction as Components
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.TransposeFamilies as Families
import SCT.VolumeI.Chapter04.Section04.HomAdjunctions as Hom
import SCT.VolumeI.Chapter01.Section06.ConeCalculus.PullbackLifting as Reflection
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.EndpointFiberOperations 𝒯 M ℱ P I
  using (module Realize; module Lifts)
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
  using (ConeIso; conePre; coneIso-compose; coneIso-inverse)
open Laws.PullbackStructure P using (pullbackCone)

module WithUnit {C D : CAT} {l : MAP C D} {r : MAP D C}
  (adj : Adjunction l r) (κ : id C =₁ (r ∘ l))
  (unit-comparison : ExpressionIso (Adjunction.unit adj) (isomorphism-expression κ)) where
  private
    module A = Adjunction adj using (unit-at; transpose)

  unit-frame : {Γ : CAT} (x : MAP Γ C) → x =₁ (r ∘ (l ∘ x))
  unit-frame x = (comp-assoc x l r ∙ (κ ▷ x)) ∙ (comp-unitˡ x) ⁻¹

  abstract
    component-comparison : {Γ : CAT} (x : MAP Γ C) →
      ExpressionIso (A.unit-at x) (isomorphism-expression (unit-frame x))
    component-comparison x = expressionIso-compose
      (isomorphism-retarget (κ ▷ x) (comp-unitˡ x) (comp-assoc x l r))
      (retarget-expressionIso
        (expressionIso-compose (isomorphism-restrict κ x)
          (restrict-expressionIso unit-comparison x))
        (comp-unitˡ x) (comp-assoc x l r))

    transpose-comparison : {Γ : CAT} (x : MAP Γ C) (y : MAP Γ D)
      (f : MorphismExpression (l ∘ x) y) →
      ExpressionIso (A.transpose x y f)
        (retarget-expression (post-expression r f) ((unit-frame x) ⁻¹) (idIso (r ∘ y)))
    transpose-comparison x y f = expressionIso-compose
      (precompose-identification (unit-frame x) (post-expression r f))
      (compose-expression-cong (component-comparison x) (expressionIso-id (post-expression r f)))


  module Constant (b : Obj-abs C) (Γ : CAT) where
    private
      h : MAP Γ One
      h = terminate Γ
      source-assoc : const {P = Γ} (l ∘ b) =₁ (l ∘ const b)
      source-assoc = comp-assoc h b l
      outer-assoc : const {P = Γ} (r ∘ (l ∘ b)) =₁ (r ∘ const (l ∘ b))
      outer-assoc = comp-assoc h (l ∘ b) r
      mapped-assoc : (r ∘ const {P = Γ} (l ∘ b)) =₁ (r ∘ (l ∘ const b))
      mapped-assoc = r ◁ source-assoc
      restricted-frame : const {P = Γ} b =₁ const (r ∘ (l ∘ b))
      restricted-frame = unit-frame b ▷ h
      nested-frame : const {P = Γ} (r ∘ (l ∘ b)) =₁ (r ∘ (l ∘ const b))
      nested-frame = mapped-assoc ∙ outer-assoc
      component-frame : const {P = Γ} b =₁ (r ∘ (l ∘ const b))
      component-frame = nested-frame ∙ restricted-frame
      module Restriction = Components.Components 𝒯 M ℱ P I E S adj using (unit-restrict)

    source-frame : (r ∘ const {P = Γ} (l ∘ b)) =₁ const b
    source-frame = ((unit-frame b) ⁻¹ ▷ h) ∙ outer-assoc ⁻¹

    private
      abstract
        constant-component : ExpressionIso (A.unit-at (const {P = Γ} b))
          (isomorphism-expression component-frame)
        constant-component = expressionIso-compose
          (isomorphism-cong (isoComp-unitʳ-at component-frame ∙
            isoComp-cong (idIso component-frame) (inverse-identity (const b))))
          (expressionIso-compose
            (isomorphism-retarget restricted-frame (idIso (const b)) nested-frame)
            (expressionIso-compose
              (retarget-expressionIso
                (expressionIso-compose (isomorphism-restrict (unit-frame b) h)
                  (restrict-expressionIso (component-comparison b) h))
                (idIso (const b)) nested-frame)
              (expressionIso-inverse (Restriction.unit-restrict b h))))

        source-normal : ((component-frame ⁻¹) ∙ mapped-assoc) =₂ source-frame
        source-normal = isoComp-cong ((pre-inverse (unit-frame b) h) ⁻¹)
            (idIso (outer-assoc ⁻¹)) ∙
          cancel-inverse-tail ((restricted-frame ⁻¹) ∙ outer-assoc ⁻¹) mapped-assoc ∙
          isoComp-cong
            ((isoComp-assoc-at (restricted-frame ⁻¹) (outer-assoc ⁻¹) (mapped-assoc ⁻¹)) ⁻¹ ∙
              isoComp-cong (idIso (restricted-frame ⁻¹)) (inverse-composite mapped-assoc outer-assoc) ∙
              inverse-composite nested-frame restricted-frame)
            (idIso mapped-assoc)

    abstract
      transpose-constant : {y : MAP Γ D} (f : MorphismExpression (const (l ∘ b)) y) →
        ExpressionIso (A.transpose (const b) y
          (retarget-expression f source-assoc (idIso y)))
          (retarget-expression (post-expression r f) source-frame (idIso (r ∘ y)))
      transpose-constant {y} f = expressionIso-compose
        (retarget-cong (post-expression r f) source-normal
          (postWhisker-idIso r y ∙ isoComp-unitˡ-at (r ◁ idIso y)))
        (expressionIso-compose
          (retarget-assoc (post-expression r f) mapped-assoc (r ◁ idIso y)
            (component-frame ⁻¹) (idIso (r ∘ y)))
          (expressionIso-compose
            (retarget-expressionIso (post-retarget r f source-assoc (idIso y))
              (component-frame ⁻¹) (idIso (r ∘ y)))
            (expressionIso-compose
              (precompose-identification component-frame
                (post-expression r (retarget-expression f source-assoc (idIso y))))
              (compose-expression-cong constant-component
                (expressionIso-id (post-expression r (retarget-expression f source-assoc (idIso y))))))))

  module OverBase {B : CAT} (x : MAP B C) (y : MAP B D) where
    private
      module F = Families.Families 𝒯 M ℱ P I E S adj x y using (left-normal; forward)

    normalized : {Γ : CAT} (b : MAP Γ B)
      (f : MorphismExpression ((l ∘ x) ∘ b) (y ∘ b)) →
      MorphismExpression (x ∘ b) ((r ∘ y) ∘ b)
    normalized b f = retarget-expression
      (retarget-expression (post-expression r (F.left-normal b f))
        ((unit-frame (x ∘ b)) ⁻¹) (idIso (r ∘ (y ∘ b))))
      (idIso (x ∘ b)) ((comp-assoc b y r) ⁻¹)

    abstract
      normalization : {Γ : CAT} (b : MAP Γ B)
        (f : MorphismExpression ((l ∘ x) ∘ b) (y ∘ b)) →
        ExpressionIso (F.forward b f) (normalized b f)
      normalization b f = retarget-expressionIso
        (transpose-comparison (x ∘ b) (y ∘ b) (F.left-normal b f))
        (idIso (x ∘ b)) ((comp-assoc b y r) ⁻¹)

    module Realized (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E) where
      private
        module H = Hom.HomEquivalence 𝒯 M ℱ P I E S Q adj x y
          using (module Left; module Right; functor; isEquiv;
            forward-operation; forward-universal; forward-expression; forward-cone; forward-computation)
        original : MorphismExpression ((l ∘ x) ∘ H.Left.base) (y ∘ H.Left.base)
        original = H.forward-universal

      normalized-expression : MorphismExpression (x ∘ H.Left.base) ((r ∘ y) ∘ H.Left.base)
      normalized-expression = normalized H.Left.base original
      cone = H.Right.cone H.Left.base normalized-expression
      functor : MAP H.Left.category H.Right.category
      functor = H.Right.lift H.Left.base normalized-expression

      abstract
        computation : ConeIso
          (conePre H.functor (pullbackCone endpoints (pair x (r ∘ y)))) cone
        computation = coneIso-compose
          (Lifts.encode-cong x (r ∘ y) H.Left.base
            {f = H.forward-expression} {g = normalized-expression}
            (normalization H.Left.base original))
          H.forward-computation

      specified-comparison = coneIso-compose
        (coneIso-inverse (H.Right.lift-β H.Left.base normalized-expression)) computation
      private
        module Compared = Reflection.Lift 𝒯 P H.functor functor specified-comparison
          using (lift; comparison-image; left-image; right-image)
      open Compared public renaming (lift to comparison)

      abstract
        isEquiv : IsEquiv functor
        isEquiv = equiv-transport comparison H.isEquiv
```
