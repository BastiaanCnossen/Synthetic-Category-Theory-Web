# Composition of functor-category restrictions after evaluation

The restriction compositor is evaluated by pasting the two separation
squares. The parameter-change comparison supplies the inner edge, and
the mixed product composition law supplies the outer edge.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter01.Section04.RetainedCompositionParameterChange as Project
import SCT.VolumeI.Chapter01.Section08.FunPrecompositionParameterChange as Parameter
import SCT.VolumeI.Chapter01.Section08.FunPrecompositionCompositeImage as Image
import SCT.VolumeI.Chapter01.Section02.Isomorphisms as Isomorphisms
import SCT.VolumeI.Chapter01.Section03.PairingNaturality as PN
import SCT.VolumeI.Chapter01.Section03.Structural as Structural

module SCT.VolumeI.Chapter01.Section08.FunPrecompositionCompositionBase
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section08.FunctorSquares 𝒯 M ℱ P
open import SCT.VolumeI.Chapter01.Section08.EvaluationMateCalculus 𝒯
open import SCT.VolumeI.Chapter01.Section08.ProductSquares 𝒯
open import SCT.VolumeI.Chapter01.Section08.ProductMixedSubstitution 𝒯 M using (separate-composition)
open import SCT.VolumeI.Chapter01.Section04.ParameterSquarePasting 𝒯 using (paste)
open import SCT.VolumeI.Chapter01.Section04.ProjectionSquares 𝒯 using (post-inverse)
open import SCT.VolumeI.Chapter01.Section06.InverseCalculus 𝒯 using (pre-inverse)
open Isomorphisms vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-left; cancel-right; move-square)
open Structural vocabulary terminal products productLaws composition whiskering using (postWhisker-comp-at; whisker-mixed-at)

module CompositorEvaluation {X A B C E : CAT} (f : MAP A B) (g : MAP B C) (h : MAP X (Fun C E)) where
  module Lifted = Image.CompositorImage 𝒯 M ℱ P f g h
  Y = Fun C E
  e = funEval {C = C} {D = E}
  U = funUncurry h
  Fg = funPre {D = E} g
  Ff = funPre {D = E} f
  Uf = funUncurry Fg
  HA = productMap h (id A)
  HB = productMap h (id B)
  HC = productMap h (id C)
  Xf = productRestriction X f
  Xg = productRestriction X g
  Yf = productRestriction Y f
  Yg = productRestriction Y g
  β = funPre-β {D = E} g
  qg = funPre-uncurry g h
  uk = funUncurry-restrict Fg h
  Shf = productMap-separate h f
  Shg = productMap-separate h g
  module Restriction = Parameter.ParameterChange 𝒯 M ℱ g h (id X)
  module Change = Parameter.ParameterChange 𝒯 M ℱ f Fg h
  module Pasted = Project.EvaluationPaste 𝒯 M Xf Xg Yf Yg HA HB HC
    e U Uf (funUncurry (Fg ∘ h))
    (idIso U) (β ⁻¹) (qg ⁻¹) (Shg ⁻¹) (Shf ⁻¹) uk

  source-base = (β ⁻¹ ▷ HB) ∙ (comp-assoc HB Yg e) ⁻¹
  target-base = (idIso U ▷ Xg) ∙ (comp-assoc Xg HC e) ⁻¹
  normalized-source = uk ⁻¹ ∙ source-base

  abstract
    inverse-square : (normalized-source ∙ (e ◁ Shg ⁻¹)) =₂ (qg ⁻¹ ∙ target-base)
    inverse-square = Project.projection-inverse-action 𝒯 M e normalized-source target-base Shg qg Restriction.square

    normalize-inverse-square : (uk ∙ (normalized-source ∙ (e ◁ Shg ⁻¹))) =₂
      (source-base ∙ (e ◁ Shg ⁻¹))
    normalize-inverse-square = isoComp-cong (cancel-inverse uk source-base) (idIso (e ◁ Shg ⁻¹)) ∙
      (isoComp-assoc-at uk normalized-source (e ◁ Shg ⁻¹)) ⁻¹

    square : (source-base ∙ (e ◁ Shg ⁻¹)) =₂
      (uk ∙ (qg ⁻¹ ∙ target-base))
    square = isoComp-cong (idIso uk) inverse-square ∙ normalize-inverse-square ⁻¹
    pasted-evaluation :
      (Pasted.target-evaluation ∙ (e ◁ paste (Shg ⁻¹) (Shf ⁻¹))) =₂
      (Pasted.evaluation-action ∙ Pasted.source-evaluation)
    pasted-evaluation = Pasted.project-paste square

  τ = funUncurryIso (comp-assoc h Fg Ff)
  r = funPre-uncurry f (Fg ∘ h) ∙ τ
  u₀ = funUncurry-restrict (Ff ∘ Fg) h
  tail = (funPre-uncurry f Fg ▷ HA) ∙ u₀
  before = comp-assoc HA Yf Uf
  across = Uf ◁ Shf
  after = comp-assoc Xf HB Uf

  abstract
    parameter-tail : (Change.Pasted.evaluation-action ∙ u₀) =₂
      (after ⁻¹ ∙ (across ∙ (before ∙ tail)))
    parameter-tail = append-four (after ⁻¹) across before (funPre-uncurry f Fg ▷ HA) u₀

    core-action : (Pasted.evaluation-action ∙ r) =₂ tail
    core-action = cancel-mate before across after (Uf ◁ Shf ⁻¹) (uk ▷ Xf) r tail
      (post-inverse Uf Shf) (parameter-tail ∙ Change.comparison)

  a₁ = qg ▷ Xf
  a₂ = comp-assoc Xf Xg U
  a₃ = comp-assoc (Xg ∘ Xf) HC e
  z = a₃ ∙ (a₂ ∙ (a₁ ∙ r))

  abstract
    source-endpoint : (Pasted.source-evaluation ∙ z) =₂ r
    source-endpoint = cancel-three-images a₁ a₂ a₃ r (qg ⁻¹ ▷ Xf)
      (idIso U ▷ (Xg ∘ Xf)) (pre-inverse qg Xf) (preWhisker-idIso U (Xg ∘ Xf))
    core-transfer :
      ((Pasted.target-evaluation ∙ (e ◁ paste (Shg ⁻¹) (Shf ⁻¹))) ∙ z) =₂ tail
    core-transfer = close-paste Pasted.target-evaluation
      (e ◁ paste (Shg ⁻¹) (Shf ⁻¹)) z Pasted.evaluation-action
      Pasted.source-evaluation r tail pasted-evaluation source-endpoint core-action
```
