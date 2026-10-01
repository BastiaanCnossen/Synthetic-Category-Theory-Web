# Normalizing transposition in a coslice

The two endpoint changes used in the coslice adjunction retain constant
source conventions. Their unit-transposition formula agrees with the
image of the universal coslice arrow, with source changed by the inverse
unit component. The comparison below records both endpoint equations;
the constancy and unit coherence calculations are explicit.

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

module SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.CosliceTranspositionExpressions
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter04.Section04.Adjunctions 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionFrameCalculus 𝒯 M ℱ I
  using (retarget-assoc; retarget-cong; retarget-cancel)
open import SCT.VolumeI.Chapter01.Section04.Substitution.ConstantSubstitution 𝒯 M
  using (constant-image-pre)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯
  using (inverse-inverse; inverse-identity; pre-inverse)
open import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality
  vocabulary terminal products productLaws composition vertical whiskering using (move-square; cancel-right)
open import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.FunctorCoherence
  vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle using (triangle-whiskered)
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.TransposeFamilies as Families
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.TransposeComparisons as Comparisons
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.TranspositionWithInvertibleUnit as Unit

import SCT.VolumeI.Chapter04.Section04.HomAdjunctions as Hom
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.SealedFamilyTransposition as Sealed
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.EndpointFiberChangeExpressions as Change
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.EndpointFiberOperationComputations as Operations
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.EndpointFiberLifts as Lifts
import SCT.VolumeI.Chapter01.Section06.ConeCalculus.PullbackLifting as Reflection
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
  using (Cone; ConeIso; conePre; coneIso-compose; coneIso-inverse)
open Laws.PullbackStructure P using (pullbackCone)

module WithUnit {C D : CAT} {l : MAP C D} {r : MAP D C}
  (adj : Adjunction l r) (κ : id C =₁ (r ∘ l))
  (unit-comparison : ExpressionIso (Adjunction.unit adj) (isomorphism-expression κ))
  (b : Obj-abs C) where
  private
    module A = Adjunction adj using (transpose)
    module F = Families.Families 𝒯 M ℱ P I E S adj (const {P = D} b) (id D)
      using (forward; left-normal)
    module N = Comparisons.Comparisons 𝒯 M ℱ P I E S adj using (transpose-cong; transpose-retarget)
    module U = Unit.WithUnit 𝒯 M ℱ P I E S adj κ unit-comparison using (module Constant)

  module At {Γ : CAT} (q : MAP Γ D)
    (f : MorphismExpression ((const {P = D} (l ∘ b)) ∘ q) (id D ∘ q)) where
    private
      p = const-pre b q
      p-l = const-pre (l ∘ b) q
      source-assoc = comp-assoc (terminate D) b l
      a-q = source-assoc ▷ q
      a-Γ = comp-assoc (terminate Γ) b l
      assoc = comp-assoc q (const b) l
      base-unit = comp-unitˡ q
      base-assoc = comp-assoc q (id D) r
      id-source = idIso (const {P = D} b) ▷ q
      id-target = idIso (id D) ▷ q
      right-unit = comp-unitʳ r ▷ q
      module Constant = U.Constant b Γ using (source-frame; transpose-constant)

    input : MorphismExpression ((l ∘ const b) ∘ q) (id D ∘ q)
    input = retarget-expression f a-q id-target
    normalized-input : MorphismExpression (const (l ∘ b)) q
    normalized-input = retarget-expression f p-l base-unit
    transposed : MorphismExpression ((const b) ∘ q) (r ∘ q)
    transposed = retarget-expression (F.forward q input) id-source right-unit
    image : MorphismExpression (const b) (r ∘ q)
    image = retarget-expression (post-expression r normalized-input)
      Constant.source-frame (idIso (r ∘ q))
    framed-image : MorphismExpression ((const b) ∘ q) (r ∘ q)
    framed-image = retarget-expression image (p ⁻¹) (idIso (r ∘ q))

    private
      abstract
        source-square : (((l ◁ p) ∙ assoc) ∙ a-q) =₂ (a-Γ ∙ p-l)
        source-square = isoComp-cong (inverse-inverse a-Γ) (idIso p-l) ∙
          (move-square (a-Γ ⁻¹) ((l ◁ p) ∙ assoc) p-l (a-q ⁻¹)
            (isoComp-cong (idIso p-l) (pre-inverse source-assoc q) ∙
              (constant-image-pre q l b) ⁻¹)) ⁻¹ ∙
          isoComp-cong (idIso ((l ◁ p) ∙ assoc)) ((inverse-inverse a-q) ⁻¹)
        target-square : ((base-unit ∙ idIso (id D ∘ q)) ∙ id-target) =₂
          (idIso q ∙ base-unit)
        target-square = (isoComp-unitˡ-at base-unit) ⁻¹ ∙ isoComp-unitʳ-at base-unit ∙
          isoComp-cong (isoComp-unitʳ-at base-unit) (preWhisker-idIso (id D) q)

        input-comparison : ExpressionIso
          (retarget-expression (F.left-normal q input) (l ◁ p) base-unit)
          (retarget-expression normalized-input a-Γ (idIso q))
        input-comparison = expressionIso-compose
          (expressionIso-inverse (retarget-assoc f p-l base-unit a-Γ (idIso q)))
          (expressionIso-compose (retarget-cong f source-square target-square)
            (expressionIso-compose
              (retarget-assoc f a-q id-target ((l ◁ p) ∙ assoc) (base-unit ∙ idIso (id D ∘ q)))
              (retarget-assoc input assoc (idIso (id D ∘ q)) (l ◁ p) base-unit)))

        output-source : ((p ∙ id-source) ∙ idIso ((const b) ∘ q)) =₂ p
        output-source = isoComp-unitʳ-at p ∙
          isoComp-cong (idIso p) (preWhisker-idIso (const {P = D} b) q) ∙
          isoComp-unitʳ-at (p ∙ id-source)
        output-target : ((idIso (r ∘ q) ∙ right-unit) ∙ base-assoc ⁻¹) =₂ (r ◁ base-unit)
        output-target = cancel-right base-assoc (r ◁ base-unit) ∙
          isoComp-cong (triangle-whiskered q r ∙ isoComp-unitˡ-at right-unit)
            (idIso (base-assoc ⁻¹))

        output-comparison : ExpressionIso
          (retarget-expression transposed p (idIso (r ∘ q)))
          (retarget-expression (A.transpose ((const b) ∘ q) (id D ∘ q) (F.left-normal q input))
            p (r ◁ base-unit))
        output-comparison = expressionIso-compose
          (retarget-cong (A.transpose ((const b) ∘ q) (id D ∘ q) (F.left-normal q input))
            output-source output-target)
          (expressionIso-compose
            (retarget-assoc (A.transpose ((const b) ∘ q) (id D ∘ q) (F.left-normal q input))
              (idIso ((const b) ∘ q)) (base-assoc ⁻¹)
              (p ∙ id-source) (idIso (r ∘ q) ∙ right-unit))
            (retarget-assoc (F.forward q input) id-source right-unit p (idIso (r ∘ q))))

        normalized-comparison : ExpressionIso
          (retarget-expression transposed p (idIso (r ∘ q))) image
        normalized-comparison = expressionIso-compose (Constant.transpose-constant normalized-input)
          (expressionIso-compose (N.transpose-cong (const b) q input-comparison)
            (expressionIso-compose (N.transpose-retarget (F.left-normal q input) p base-unit)
              output-comparison))

    abstract
      comparison : ExpressionIso transposed framed-image
      comparison = expressionIso-compose
        (retarget-cong image (idIso (p ⁻¹)) (inverse-identity (r ∘ q)))
        (expressionIso-compose
          (retarget-expressionIso normalized-comparison (p ⁻¹) ((idIso (r ∘ q)) ⁻¹))
          (expressionIso-inverse (retarget-cancel transposed p (idIso (r ∘ q)))))


  module Realized (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E) where
    private
      module Source = EndpointFiber (const {P = D} (l ∘ b)) (id D)
      module Target = EndpointFiber (const {P = D} b) r
      module LP = Change.Along 𝒯 M ℱ P I
        {u = const {P = D} (l ∘ b)} {v = id D}
        {u′ = l ∘ const b} {v′ = id D}
        (comp-assoc (terminate D) b l) (idIso (id D))
        using (map; map-isEquiv; computation)
      module H = Hom.HomEquivalence 𝒯 M ℱ P I E S Q adj (const {P = D} b) (id D)
        using (functor; isEquiv; forward-operation; module Left; module Right)
      module HP = Operations.Of 𝒯 M ℱ P I H.forward-operation using (module Specified)
      module RP = Change.Along 𝒯 M ℱ P I
        {u = const {P = D} b} {v = r ∘ id D}
        {u′ = const b} {v′ = r}
        (idIso (const b)) (comp-unitʳ r)
        using (map; map-isEquiv; module Specified)
      module Formula = At Source.base Source.frame
        using (input; transposed; framed-image; comparison; image)
      module First = HP.Specified LP.map Source.base Formula.input LP.computation
        using (computation)
      forward-family : MorphismExpression ((const b) ∘ Source.base) ((r ∘ id D) ∘ Source.base)
      forward-family = F.forward Source.base Formula.input
      abstract
        first-computation : ConeIso
          (conePre (H.functor ∘ LP.map) (pullbackCone endpoints (pair (const b) (r ∘ id D))))
          (H.Right.cone Source.base forward-family)
        first-computation = coneIso-compose
          (Lifts.Lifts.encode-cong 𝒯 M ℱ P I (const b) (r ∘ id D) Source.base
            {f = Operations.ExpressionOperation.apply H.forward-operation Source.base Formula.input}
            {g = forward-family}
            (Sealed.forward-computation 𝒯 M ℱ P I E S Q adj (const b) (id D)
              Source.base Formula.input)) First.computation
      module Second = RP.Specified (H.functor ∘ LP.map) Source.base forward-family first-computation
        using (family-computation)

    transposed : MAP Source.category Target.category
    transposed = RP.map ∘ (H.functor ∘ LP.map)
    normalized : MAP Source.category Target.category
    normalized = Target.lift Source.base Formula.framed-image
    normalized-cone : Cone endpoints (pair (const b) r) Source.category
    normalized-cone = Target.cone Source.base Formula.framed-image

    abstract
      computation : ConeIso
        (conePre transposed (pullbackCone endpoints (pair (const b) r))) normalized-cone
      computation = coneIso-compose
        (Lifts.Lifts.encode-cong 𝒯 M ℱ P I (const b) r Source.base
          {f = Formula.transposed} {g = Formula.framed-image} Formula.comparison)
        Second.family-computation

    specified-comparison : ConeIso
      (conePre transposed (pullbackCone endpoints (pair (const b) r)))
      (conePre normalized (pullbackCone endpoints (pair (const b) r)))
    specified-comparison = coneIso-compose
      (coneIso-inverse (Target.lift-β Source.base Formula.framed-image)) computation
    private
      module Reflected = Reflection.Lift 𝒯 P
        {f = endpoints} {g = pair (const {P = D} b) r}
        transposed normalized specified-comparison
        using (lift; comparison-image; left-image; right-image)
    open Reflected public renaming (lift to comparison)

    abstract
      transposed-isEquiv : IsEquiv transposed
      transposed-isEquiv = equiv-compose (H.functor ∘ LP.map) RP.map
        (equiv-compose LP.map H.functor LP.map-isEquiv H.isEquiv) RP.map-isEquiv
      normalized-isEquiv : IsEquiv normalized
      normalized-isEquiv = equiv-transport comparison transposed-isEquiv
```
