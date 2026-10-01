# Relaxing the normalization of an adjoint section

A deformation over the base whose restriction to the section is invertible
can be corrected to a normalized deformation. This proves
`prop:Relaxation_Axiom_Right_Adjoint_Section_1` in both directions. The
inverse is used as a morphism expression with its actual inverse equation;
no higher compatibility between independently chosen nullhomotopies is assumed.

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

module SCT.VolumeI.Chapter04.Section04.RelaxedAdjointSections
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter04.Section04.AdjointSections 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionFrameCalculus 𝒯 M ℱ I using (retarget-assoc; retarget-cong)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionPostcomposition 𝒯 M ℱ I using (post-expressionIso)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionRestriction 𝒯 M ℱ I using (restrict-expressionIso)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionRestrictionPostcomposition 𝒯 M ℱ I using (restrict-post)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositionIdentifications 𝒯 M ℱ P I E S using (compose-expression-cong)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositionSubstitution 𝒯 M ℱ P I E S using (restrict-composition; retarget-composition)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.PostcompositionPresentations 𝒯 M ℱ P I E S using (post-composition)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.IdentityExpressionPostcomposition 𝒯 M ℱ P I E using (post-identity)
open import SCT.VolumeI.Chapter02.Section02.ExpressionUnitLaws 𝒯 M ℱ P I E S using (left-unit; right-unit)
open import SCT.VolumeI.Chapter01.Section04.ProductCalculus.ProductAssociativity 𝒯 M using (cancel-inverse-tail)
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.IdentityExpressionSubstitution as IdentityRestriction
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.IdentityExpressionRetargeting as IdentityFrames
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.RestrictionAlongSection as Restriction
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.NormalizedSections as Normalized
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.SectionNormalization as Transfer
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.NormalizedRelativeDeformations as Relative

private
  mapped-right-inverse : {Γ C D : CAT} {x : MAP Γ C} (F : MAP C D)
    (a b : MorphismExpression x x) →
    ExpressionIso (compose-expression b a) (identity-expression x) →
    ExpressionIso (post-expression F a) (identity-expression (F ∘ x)) →
    ExpressionIso (post-expression F b) (identity-expression (F ∘ x))
  mapped-right-inverse F a b law image = expressionIso-compose (post-identity F _)
    (expressionIso-compose (post-expressionIso F law)
      (expressionIso-compose (post-composition F b a)
        (expressionIso-compose (compose-expression-cong (expressionIso-id (post-expression F b)) (expressionIso-inverse image))
          (expressionIso-inverse (right-unit (post-expression F b))))))

  mapped-left-inverse : {Γ C D : CAT} {x : MAP Γ C} (F : MAP C D)
    (a b : MorphismExpression x x) →
    ExpressionIso (compose-expression a b) (identity-expression x) →
    ExpressionIso (post-expression F a) (identity-expression (F ∘ x)) →
    ExpressionIso (post-expression F b) (identity-expression (F ∘ x))
  mapped-left-inverse F a b law image = expressionIso-compose (post-identity F _)
    (expressionIso-compose (post-expressionIso F law)
      (expressionIso-compose (post-composition F a b)
        (expressionIso-compose (compose-expression-cong (expressionIso-inverse image) (expressionIso-id (post-expression F b)))
          (expressionIso-inverse (left-unit (post-expression F b))))))

module WithSection {C D : CAT} (p : MAP C D) (s : MAP D C) (ρ : (p ∘ s) =₁ id D) where
  module N = Normalized.WithSection 𝒯 M ℱ P I E S p s ρ using (section-frame; base-frame; module Left; module Right)
  module R = Relative.WithSection 𝒯 M ℱ P I E S p s ρ using (source-frame; module Left; module Right)
  u = R.source-frame
  v = comp-unitʳ p
  α = N.section-frame
  β = comp-unitˡ s

  module Correction (b : MorphismExpression s s)
    (image : ExpressionIso (post-expression p b) (identity-expression (p ∘ s))) where
    term = restrict-expression b p
    module OnSection = Restriction.At 𝒯 M ℱ I p s ρ b using (value)
    A = comp-assoc p s p

    abstract
      over-base : ExpressionIso (retarget-expression (post-expression p term) u u) (identity-expression p)
      over-base = expressionIso-compose (IdentityFrames.At.comparison 𝒯 M ℱ P I E N.base-frame)
        (expressionIso-compose
          (retarget-expressionIso (IdentityRestriction.Restrict.comparison 𝒯 M ℱ P I E (p ∘ s) p) N.base-frame N.base-frame)
          (expressionIso-compose
            (retarget-expressionIso (restrict-expressionIso image p) N.base-frame N.base-frame)
            (expressionIso-compose
              (retarget-cong (restrict-expression (post-expression p b) p)
                (cancel-inverse-tail N.base-frame A) (cancel-inverse-tail N.base-frame A))
              (expressionIso-compose
                (retarget-assoc (restrict-expression (post-expression p b) p) A A u u)
                (retarget-expressionIso (expressionIso-inverse (restrict-post p b p)) u u)))))

  module Left (ε : MorphismExpression (s ∘ p) (id C))
    (over-base : ExpressionIso (retarget-expression (post-expression p ε) u v) (identity-expression p)) where
    module T = Transfer.WithSection.Left 𝒯 M ℱ P I E p s ρ ε using (on-section; identity)
    section-loop = T.on-section

    module Invertible (w : IsInvertibleExpression section-loop) where
      module W = IsInvertibleExpression w
      b = W.right-inverse
      module B = Correction b (mapped-right-inverse p section-loop b W.right-inverse-law (T.identity over-base)) using (term; over-base; module OnSection)
      corrected = compose-expression B.term ε
      module Result = N.Left corrected using (right-counit; left-counit; module Normalized)
      module Flat = R.Left corrected using (flatten)

      abstract
        corrected-over-base : ExpressionIso (retarget-expression (post-expression p corrected) u v) (identity-expression p)
        corrected-over-base = expressionIso-compose (left-unit (identity-expression p))
          (expressionIso-compose (compose-expression-cong B.over-base over-base)
            (expressionIso-compose (expressionIso-inverse (retarget-composition (post-expression p B.term) (post-expression p ε) u u v))
              (retarget-expressionIso (expressionIso-inverse (post-composition p B.term ε)) u v)))

        corrected-on-section : ExpressionIso (retarget-expression (restrict-expression corrected s) α β) (identity-expression s)
        corrected-on-section = expressionIso-compose W.right-inverse-law
          (expressionIso-compose (compose-expression-cong B.OnSection.value (expressionIso-id section-loop))
            (expressionIso-compose (expressionIso-inverse (retarget-composition (restrict-expression B.term s) (restrict-expression ε s) α α β))
              (retarget-expressionIso (expressionIso-inverse (restrict-composition B.term ε s)) α β)))

        normalized-base : ExpressionIso (retarget-expression Result.right-counit N.base-frame (idIso p)) (identity-expression p)
        normalized-base = expressionIso-compose corrected-over-base Flat.flatten

        normalized-section : ExpressionIso (retarget-expression Result.left-counit α (idIso s)) (identity-expression s)
        normalized-section = expressionIso-compose corrected-on-section
          (expressionIso-compose
            (retarget-cong (restrict-expression corrected s) (isoComp-unitʳ-at α) (isoComp-unitˡ-at β))
            (retarget-assoc (restrict-expression corrected s) (idIso ((s ∘ p) ∘ s)) β α (idIso s)))

      module Normal = Result.Normalized normalized-section normalized-base using (adjoint-section)
      value : LeftAdjointSection p s
      value = Normal.adjoint-section

  module Right (η : MorphismExpression (id C) (s ∘ p))
    (over-base : ExpressionIso (retarget-expression (post-expression p η) v u) (identity-expression p)) where
    module T = Transfer.WithSection.Right 𝒯 M ℱ P I E p s ρ η using (on-section; identity)
    section-loop = T.on-section

    module Invertible (w : IsInvertibleExpression section-loop) where
      module W = IsInvertibleExpression w
      b = W.left-inverse
      module B = Correction b (mapped-left-inverse p section-loop b W.left-inverse-law (T.identity over-base)) using (term; over-base; module OnSection)
      corrected = compose-expression η B.term
      module Result = N.Right corrected using (left-unit; right-unit; module Normalized)
      module Flat = R.Right corrected using (flatten)

      abstract
        corrected-over-base : ExpressionIso (retarget-expression (post-expression p corrected) v u) (identity-expression p)
        corrected-over-base = expressionIso-compose (left-unit (identity-expression p))
          (expressionIso-compose (compose-expression-cong over-base B.over-base)
            (expressionIso-compose (expressionIso-inverse (retarget-composition (post-expression p η) (post-expression p B.term) v u u))
              (retarget-expressionIso (expressionIso-inverse (post-composition p η B.term)) v u)))

        corrected-on-section : ExpressionIso (retarget-expression (restrict-expression corrected s) β α) (identity-expression s)
        corrected-on-section = expressionIso-compose W.left-inverse-law
          (expressionIso-compose (compose-expression-cong (expressionIso-id section-loop) B.OnSection.value)
            (expressionIso-compose (expressionIso-inverse (retarget-composition (restrict-expression η s) (restrict-expression B.term s) β α α))
              (retarget-expressionIso (expressionIso-inverse (restrict-composition η B.term s)) β α)))

        normalized-base : ExpressionIso (retarget-expression Result.left-unit (idIso p) N.base-frame) (identity-expression p)
        normalized-base = expressionIso-compose corrected-over-base Flat.flatten

        normalized-section : ExpressionIso (retarget-expression Result.right-unit (idIso s) α) (identity-expression s)
        normalized-section = expressionIso-compose corrected-on-section
          (expressionIso-compose
            (retarget-cong (restrict-expression corrected s) (isoComp-unitˡ-at β) (isoComp-unitʳ-at α))
            (retarget-assoc (restrict-expression corrected s) β (idIso ((s ∘ p) ∘ s)) (idIso s) α))

      module Normal = Result.Normalized normalized-base normalized-section using (adjoint-section)
      value : RightAdjointSection p s
      value = Normal.adjoint-section
```
