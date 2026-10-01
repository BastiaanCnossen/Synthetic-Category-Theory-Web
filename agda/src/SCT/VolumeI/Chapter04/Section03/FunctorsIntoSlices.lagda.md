# Functors into slice categories

This proves both equivalences in `lem:Functors_Into_Slice_Category`
for an absolute object. Functor categories preserve the one-sided
endpoint pullbacks, and interchange of diagram variables identifies
their cospans. Each universal factorization keeps its full cone comparison.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter04.Section03.MappingCalculus.DiagramInterchange as Interchange
import SCT.VolumeI.Chapter01.Section06.Cospans.CospanEquivalences as Cospans

module SCT.VolumeI.Chapter04.Section03.FunctorsIntoSlices
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter04.Section03.MappingCalculus.EndpointSlices 𝒯 M ℱ P I public
open Laws.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
  using (Cone; ConeIso; conePre; IsPullback; module UniversalCone;
         pullback-comparison; coneIso-compose; coneIso-inverse; coneIso-pre; conePre-assoc)
open import SCT.VolumeI.Chapter01.Section06.PullbackFunctor 𝒯 P using (CospanMap)
open import SCT.VolumeI.Chapter01.Section07.FunctorPullbacks 𝒯 M ℱ P
  using (mappedCone; fun-preserves-pullback)
open import SCT.VolumeI.Chapter01.Section07.Contractible 𝒯 M ℱ
  using (fun-terminal-contractible)
open import SCT.VolumeI.Chapter02.Section04.ConstantDiagrams.ConstantExponential 𝒯 M ℱ
  using (constant-natural)

module Diagrams (D C : CAT) (x : Obj-abs C) where
  point : Obj-abs (Fun D C)
  point = nameFun (const {P = D} x)
  module Exchange = Interchange.Exchange 𝒯 M ℱ D [1] C
    using (forward; forward-isEquiv; module At)

  private
    collapse : (constantDiagram D One ∘ terminate (Fun D One)) =₁ (id (Fun D One))
    collapse = equiv-reflect (fun-terminal-contractible D) _ _ (terminal-iso _ _)

  point-boundary : (point ∘ terminate (Fun D One)) =₁ (funPost x)
  point-boundary = comp-unitʳ (funPost x) ∙
    ((funPost x ◁ collapse) ∙
      (comp-assoc (terminate (Fun D One)) (constantDiagram D One) (funPost x) ∙
        ((constant-natural D x ⁻¹ ▷ terminate (Fun D One)) ∙
          (constantDiagram-point x ⁻¹ ▷ terminate (Fun D One)))))

  module Endpoint (b : Obj-abs [1]) where
    source-map = funPost {C = D} (evaluate {C = C} b)
    source-point = funPost {C = D} x
    target-map = evaluate {C = Fun D C} b
    change : CospanMap source-map source-point target-map point
    change = record { left = Exchange.forward ; right = terminate (Fun D One)
      ; base = id (Fun D C)
      ; leftSquare = (comp-unitˡ source-map) ⁻¹ ∙ Exchange.At.boundary b
      ; rightSquare = (comp-unitˡ source-point) ⁻¹ ∙ point-boundary }
    module Change = CospanMap change
      using (mapCone; pullbackMap; pullbackMap-β)
    module Equivalent = Cospans.CospanEquivalence 𝒯 P change
      Exchange.forward-isEquiv (fun-terminal-contractible D) (id-isEquiv (Fun D C))
      using (pullbackMap-isEquiv)

    module CompareCones {S T : CAT} (s : Cone (evaluate b) x S) (es : IsPullback s)
      (t : Cone target-map point T) (et : IsPullback t) where
      mapped = mappedCone D s
      mapped-isPullback : IsPullback mapped
      mapped-isPullback = fun-preserves-pullback D s es
      mapped-comparison = pullbackLift-β mapped

      image = Change.mapCone (pullbackCone source-map source-point)
      module Target = UniversalCone t et using (factor; factor-β)
      target-comparison = Target.factor-β image
      through : MAP (Pullback source-map source-point) T
      through = Target.factor image
      through-isEquiv : IsEquiv through
      through-isEquiv = pullback-comparison image t through target-comparison
        Equivalent.pullbackMap-isEquiv et

      forward : MAP (Fun D S) T
      forward = through ∘ pullbackLift mapped
      forward-isEquiv : IsEquiv forward
      forward-isEquiv = equiv-compose (pullbackLift mapped) through mapped-isPullback through-isEquiv

      comparison : ConeIso (conePre forward t) (conePre (pullbackLift mapped) image)
      comparison = coneIso-compose (coneIso-pre (pullbackLift mapped) target-comparison)
        (coneIso-inverse (conePre-assoc (pullbackLift mapped) through t))

      arrow-comparison : (Cone.left t ∘ forward) =₁ (Exchange.forward ∘ funPost (Cone.left s))
      arrow-comparison = (Exchange.forward ◁ ConeIso.leftIso mapped-comparison) ∙
        (comp-assoc (pullbackLift mapped) pullback₁ Exchange.forward ∙ ConeIso.leftIso comparison)

  module Slice where
    module Source = SliceEndpoint x using (square; square-isPullback)
    module Target = SliceEndpoint point using (square; square-isPullback)
    open Endpoint.CompareCones one Source.square Source.square-isPullback
      Target.square Target.square-isPullback public
      using (forward; forward-isEquiv; comparison; mapped-comparison; target-comparison; arrow-comparison)

    private
      module SF = EndpointFiber (id C) (const x)
      module TF = EndpointFiber (id (Fun D C)) (const point)
      source-frame = comp-unitˡ SF.base ∙ SF.source-frame
      target-frame = comp-unitˡ TF.base ∙ TF.source-frame

    projection-comparison : (slice-projection point ∘ forward) =₁ (funPost (slice-projection x))
    projection-comparison = funPost-cong source-frame ∙
      (funPost-comp SF.arrow ev₀ ∙
        ((Exchange.At.boundary zero ▷ funPost SF.arrow) ∙
          ((comp-assoc (funPost SF.arrow) Exchange.forward ev₀) ⁻¹ ∙
            ((ev₀ ◁ arrow-comparison) ∙
              (comp-assoc forward TF.arrow ev₀ ∙ (target-frame ⁻¹ ▷ forward))))))

  module Coslice where
    module Source = CosliceEndpoint x using (square; square-isPullback)
    module Target = CosliceEndpoint point using (square; square-isPullback)
    open Endpoint.CompareCones zero Source.square Source.square-isPullback
      Target.square Target.square-isPullback public
      using (forward; forward-isEquiv; comparison; mapped-comparison; target-comparison; arrow-comparison)

    private
      module SF = EndpointFiber (const x) (id C)
      module TF = EndpointFiber (const point) (id (Fun D C))
      source-frame = comp-unitˡ SF.base ∙ SF.target-frame
      target-frame = comp-unitˡ TF.base ∙ TF.target-frame

    projection-comparison : (coslice-projection point ∘ forward) =₁ (funPost (coslice-projection x))
    projection-comparison = funPost-cong source-frame ∙
      (funPost-comp SF.arrow ev₁ ∙
        ((Exchange.At.boundary one ▷ funPost SF.arrow) ∙
          ((comp-assoc (funPost SF.arrow) Exchange.forward ev₁) ⁻¹ ∙
            ((ev₁ ◁ arrow-comparison) ∙
              (comp-assoc forward TF.arrow ev₁ ∙ (target-frame ⁻¹ ▷ forward))))))
```
