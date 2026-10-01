# Evaluated legs of the postcomposition triangles

The chosen unit and counit on functor categories have the same evaluated
triangle legs as the original adjunction. Both legs retain a single
specified middle frame.

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

module SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.PostcompositionTriangleLegs
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter04.Section04.Adjunctions 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.UncurryingExpressions 𝒯 M ℱ P I E S using (uncurry-expression)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionFrameCalculus 𝒯 M ℱ I using (retarget-cancel-inverse; retarget-assoc; retarget-cong)
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.FunctorCategoryEvaluation as Evaluation
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.UncurryingFramedOperations as Operations
import SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.PostcompositionTriangleFrames as Middle
import SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.PostcompositionUnitFrame as UnitFrame
import SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.UncurryingUnits as UnitImages
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.ComponentRestriction as Restriction

module At {C D : CAT} {l : MAP C D} {r : MAP D C} (adj : Adjunction l r) (K : CAT) where
  module A = Adjunction adj
  module Evaluated = Evaluation.At 𝒯 M ℱ P I E S adj K
  module B = Evaluated.Postcomposition
  module LeftMiddle = Middle.At 𝒯 M ℱ K l r
  module RightMiddle = Middle.At 𝒯 M ℱ K r l
  module LeftUnitFrame = UnitFrame.At 𝒯 M ℱ K l
  module RightUnitFrame = UnitFrame.At 𝒯 M ℱ K r
  L : MAP (Fun K C) (Fun K D)
  L = B.left
  R : MAP (Fun K D) (Fun K C)
  R = B.right
  e : MAP (Fun K C × K) C
  e = funEval
  d : MAP (Fun K D × K) D
  d = funEval
  βl : funUncurry L =₁ (l ∘ e)
  βl = funPost-β l
  βr : funUncurry R =₁ (r ∘ d)
  βr = funPost-β r
  tC : funUncurry (id (Fun K C)) =₁ e
  tC = funUncurry-id K C
  tD : funUncurry (id (Fun K D)) =₁ d
  tD = funUncurry-id K D

  abstract
    unit-evaluation : ExpressionIso (retarget-expression (uncurry-expression B.unit) tC B.unit-target) (A.unit-at e)
    unit-evaluation = expressionIso-compose (retarget-cancel-inverse (A.unit-at e) tC B.unit-target)
      (retarget-expressionIso B.unit-comparison tC B.unit-target)

    counit-evaluation : ExpressionIso (retarget-expression (uncurry-expression B.counit) B.counit-source tD) (A.counit-at d)
    counit-evaluation = expressionIso-compose (retarget-cancel-inverse (A.counit-at d) B.counit-source tD)
      (retarget-expressionIso B.counit-comparison B.counit-source tD)

  module Unit = Operations.At 𝒯 M ℱ P I E S B.unit tC B.unit-target unit-evaluation
  module Counit = Operations.At 𝒯 M ℱ P I E S B.counit B.counit-source tD counit-evaluation
  module LeftPost = Operations.At 𝒯 M ℱ P I E S (post-expression L B.unit)
    ((l ◁ tC) ∙ funPost-uncurry l (id (Fun K C)))
    ((l ◁ B.unit-target) ∙ funPost-uncurry l (R ∘ L)) (Unit.post l)
  module RightPost = Operations.At 𝒯 M ℱ P I E S (post-expression R B.counit)
    ((r ◁ B.counit-source) ∙ funPost-uncurry r (L ∘ R))
    ((r ◁ tD) ∙ funPost-uncurry r (id (Fun K D))) (Counit.post r)

  abstract
    left-unit : ExpressionIso (retarget-expression (uncurry-expression B.Components.left-unit) βl LeftMiddle.middle)
      (post-expression l (A.unit-at e))
    left-unit = LeftPost.retarget (comp-unitʳ L) ((comp-assoc L R L) ⁻¹) βl LeftMiddle.middle
      LeftUnitFrame.comparison LeftMiddle.post-comparison

    right-counit : ExpressionIso (retarget-expression (uncurry-expression B.Components.right-counit) RightMiddle.middle βr)
      (post-expression r (A.counit-at d))
    right-counit = RightPost.retarget ((comp-assoc R L R) ⁻¹) (comp-unitʳ R) RightMiddle.middle βr
      RightMiddle.post-comparison RightUnitFrame.comparison

  module Restricted = Restriction.Components 𝒯 M ℱ P I E S adj
  module LeftImages = UnitImages.At 𝒯 M ℱ L
  module RightImages = UnitImages.At 𝒯 M ℱ R
  σL : MAP (Fun K C × K) (Fun K D × K)
  σL = productMap L (id K)
  σR : MAP (Fun K D × K) (Fun K C × K)
  σR = productMap R (id K)
  θL : ((l ∘ (r ∘ d)) ∘ σL) =₁ (l ∘ (r ∘ (d ∘ σL)))
  θL = (l ◁ comp-assoc σL d r) ∙ comp-assoc σL (r ∘ d) l
  θR : ((r ∘ (l ∘ e)) ∘ σR) =₁ (r ∘ (l ∘ (e ∘ σR)))
  θR = (r ◁ comp-assoc σR e l) ∙ comp-assoc σR (l ∘ e) r
  κL : ((l ∘ (r ∘ d)) ∘ σL) =₁ (l ∘ (r ∘ (l ∘ e)))
  κL = (l ◁ (r ◁ βl)) ∙ θL
  κR : ((r ∘ (l ∘ e)) ∘ σR) =₁ (r ∘ (l ∘ (r ∘ d)))
  κR = (r ◁ (l ◁ βr)) ∙ θR
  left-source : funUncurry ((L ∘ R) ∘ L) =₁ ((l ∘ (r ∘ d)) ∘ σL)
  left-source = (B.counit-source ▷ σL) ∙ funUncurry-restrict (L ∘ R) L
  left-target : funUncurry (id (Fun K D) ∘ L) =₁ (d ∘ σL)
  left-target = (tD ▷ σL) ∙ funUncurry-restrict (id (Fun K D)) L
  right-source : funUncurry (id (Fun K C) ∘ R) =₁ (e ∘ σR)
  right-source = (tC ▷ σR) ∙ funUncurry-restrict (id (Fun K C)) R
  right-target : funUncurry ((R ∘ L) ∘ R) =₁ ((r ∘ (l ∘ e)) ∘ σR)
  right-target = (B.unit-target ▷ σR) ∙ funUncurry-restrict (R ∘ L) R

  abstract
    counit-restricted : ExpressionIso (retarget-expression (restrict-expression (A.counit-at d) σL) κL βl)
      (A.counit-at (l ∘ e))
    counit-restricted = expressionIso-compose (Restricted.counit-parameter βl)
      (expressionIso-compose (retarget-expressionIso (Restricted.counit-restrict d σL) (l ◁ (r ◁ βl)) βl)
        (expressionIso-compose (expressionIso-inverse (retarget-assoc (restrict-expression (A.counit-at d) σL)
            θL (idIso (d ∘ σL)) (l ◁ (r ◁ βl)) βl))
          (retarget-cong (restrict-expression (A.counit-at d) σL) (idIso κL) ((isoComp-unitʳ-at βl) ⁻¹))))

    unit-restricted : ExpressionIso (retarget-expression (restrict-expression (A.unit-at e) σR) βr κR)
      (A.unit-at (r ∘ d))
    unit-restricted = expressionIso-compose (Restricted.unit-parameter βr)
      (expressionIso-compose (retarget-expressionIso (Restricted.unit-restrict e σR) βr (r ◁ (l ◁ βr)))
        (expressionIso-compose (expressionIso-inverse (retarget-assoc (restrict-expression (A.unit-at e) σR)
            (idIso (e ∘ σR)) θR βr (r ◁ (l ◁ βr))))
          (retarget-cong (restrict-expression (A.unit-at e) σR) ((isoComp-unitʳ-at βr) ⁻¹) (idIso κR))))

    left-restriction-evaluation : ExpressionIso (retarget-expression (uncurry-expression (restrict-expression B.counit L))
        LeftMiddle.middle (βl ∙ left-target)) (A.counit-at (l ∘ e))
    left-restriction-evaluation = expressionIso-compose counit-restricted
      (expressionIso-compose (retarget-expressionIso (Counit.restrict L) κL βl)
        (expressionIso-compose (expressionIso-inverse (retarget-assoc (uncurry-expression (restrict-expression B.counit L))
            left-source left-target κL βl))
          (retarget-cong (uncurry-expression (restrict-expression B.counit L))
            ((isoComp-assoc-at (l ◁ (r ◁ βl)) θL left-source) ⁻¹ ∙ LeftMiddle.comparison)
            (idIso (βl ∙ left-target)))))

    right-restriction-evaluation : ExpressionIso (retarget-expression (uncurry-expression (restrict-expression B.unit R))
        (βr ∙ right-source) RightMiddle.middle) (A.unit-at (r ∘ d))
    right-restriction-evaluation = expressionIso-compose unit-restricted
      (expressionIso-compose (retarget-expressionIso (Unit.restrict R) βr κR)
        (expressionIso-compose (expressionIso-inverse (retarget-assoc (uncurry-expression (restrict-expression B.unit R))
            right-source right-target βr κR))
          (retarget-cong (uncurry-expression (restrict-expression B.unit R))
            (idIso (βr ∙ right-source))
            ((isoComp-assoc-at (r ◁ (l ◁ βr)) θR right-target) ⁻¹ ∙ RightMiddle.comparison))))

  module LeftRestrict = Operations.At 𝒯 M ℱ P I E S (restrict-expression B.counit L)
    LeftMiddle.middle (βl ∙ left-target) left-restriction-evaluation
  module RightRestrict = Operations.At 𝒯 M ℱ P I E S (restrict-expression B.unit R)
    (βr ∙ right-source) RightMiddle.middle right-restriction-evaluation

  abstract
    left-counit : ExpressionIso (retarget-expression (uncurry-expression B.Components.left-counit) LeftMiddle.middle βl)
      (A.counit-at (l ∘ e))
    left-counit = LeftRestrict.retarget (idIso ((L ∘ R) ∘ L)) (comp-unitˡ L) LeftMiddle.middle βl
      (isoComp-unitʳ-at LeftMiddle.middle ∙ isoComp-cong (idIso LeftMiddle.middle) (funUncurryIso-id ((L ∘ R) ∘ L)))
      (isoComp-cong (idIso βl) LeftImages.left)

    right-unit : ExpressionIso (retarget-expression (uncurry-expression B.Components.right-unit) βr RightMiddle.middle)
      (A.unit-at (r ∘ d))
    right-unit = RightRestrict.retarget (comp-unitˡ R) (idIso ((R ∘ L) ∘ R)) βr RightMiddle.middle
      (isoComp-cong (idIso βr) RightImages.left)
      (isoComp-unitʳ-at RightMiddle.middle ∙ isoComp-cong (idIso RightMiddle.middle) (funUncurryIso-id ((R ∘ L) ∘ R)))
```
