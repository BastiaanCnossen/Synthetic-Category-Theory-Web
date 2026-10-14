# Comparing successive directed-evaluation factorizations

The composite evaluation comparison lifts through the intermediate
pullback. Its prescribed first projection supplies the matching of a
comparison over the original base. Retaining this matching is the step
needed before the upper composition triangle can be reflected.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws

module SCT.VolumeI.Chapter02.Section04.PullbackCalculus.EvaluationCompositionComparison
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter02.Section01.EvaluationCalculus.EndpointEvaluation 𝒯 M ℱ public
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.CompositeCones 𝒯
  using (compositeCone; compositeConeIso; compositeCone-pre)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeSymmetry 𝒯
  using (coneSwap; coneSwap-pre; coneIso-swap)
open import SCT.VolumeI.Chapter01.Section06.PullbackSymmetry 𝒯 P using (pullback-swap)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯 using (inverse-inverse; inverse-identity)
open import SCT.VolumeI.Chapter01.Section02.Isomorphisms
  vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)
import SCT.VolumeI.Chapter01.Section06.ConeCalculus.FramedEdgeCones as Edges
import SCT.VolumeI.Chapter01.Section06.Pasting.FactoredComposition as Factored
import SCT.VolumeI.Chapter01.Section06.ConeCalculus.UniversalConeLifting as Lifting
import SCT.VolumeI.Chapter02.Section04.PullbackCalculus.CompositeEvaluationCones as EvaluationCones

module At {T A B C Y X : CAT} (z : Obj-abs T) (f : MAP A B) (g : MAP B C)
  (s : Cone (evaluate z) g Y) (es : IsPullback s)
  (t : Cone (evaluate z) (g ∘ f) X) (et : IsPullback t) where
  module EvaluatedComposite = EvaluationCones.At 𝒯 M ℱ z f g using (square; comparison)
  module Outer = Factored.At 𝒯 P f g (evaluate z)
    (coneSwap s) (pullback-swap s es) (coneSwap t) (pullback-swap t et)
    using (h; h-comparison; outer-square; outer-isPullback; module Factor)

  module Factors (dg : MAP (Fun T B) Y) (dgf : MAP (Fun T A) X)
    (βg : ConeIso (conePre dg s) (EvaluatedComposite.square g))
    (βgf : ConeIso (conePre dgf t) (EvaluatedComposite.square (g ∘ f))) where
    Ff : MAP (Fun T A) (Fun T B)
    Ff = funPost f
    bg = Cone.right s
    κ = ConeIso.rightIso βg
    J = ConeIso.rightIso βgf
    d = evaluate-post z f

    swapped-g-raw = coneIso-compose (coneIso-swap βg) (coneSwap-pre dg s)
    swapped-g = coneIso-adjust swapped-g-raw κ (ConeIso.leftIso βg)
      (isoComp-unitʳ-at κ) (isoComp-unitʳ-at (ConeIso.leftIso βg))
    swapped-gf-raw = coneIso-compose (coneIso-swap βgf) (coneSwap-pre dgf t)
    swapped-gf = coneIso-adjust swapped-gf-raw J (ConeIso.leftIso βgf)
      (isoComp-unitʳ-at J) (isoComp-unitʳ-at (ConeIso.leftIso βgf))

    first = coneIso-compose (compositeCone-pre f g dgf (coneSwap t))
      (coneIso-compose (coneIso-pre dgf Outer.h-comparison)
        (coneIso-inverse (conePre-assoc dgf Outer.h (coneSwap s))))
    second = coneIso-compose (compositeConeIso f g swapped-gf) first
    composite-raw = coneIso-compose
      (coneIso-inverse (coneSwap-pre Ff (EvaluatedComposite.square g))) EvaluatedComposite.comparison
    composite = coneIso-adjust composite-raw (d ⁻¹) (ConeIso.rightIso EvaluatedComposite.comparison)
      (isoComp-unitˡ-at (d ⁻¹) ∙ isoComp-cong (inverse-identity _) (idIso (d ⁻¹)))
      (isoComp-unitˡ-at (ConeIso.rightIso EvaluatedComposite.comparison) ∙
        isoComp-cong (inverse-identity _) (idIso (ConeIso.rightIso EvaluatedComposite.comparison)))
    third = coneIso-compose composite second
    last = coneIso-compose (coneIso-pre Ff swapped-g)
      (coneIso-inverse (conePre-assoc Ff dg (coneSwap s)))
    whole = coneIso-compose (coneIso-inverse last) third
    module Lift = Lifting.UniversalLift 𝒯 P (coneSwap s) (pullback-swap s es)
      (Outer.h ∘ dgf) (dg ∘ Ff) whole using (lift; left-image)
    χ = Lift.lift
    Kg = (κ ▷ Ff) ∙ (comp-assoc Ff dg bg) ⁻¹
    N = Cone.match (conePre dgf Outer.outer-square)
    L = (f ◁ J) ∙ N

    abstract
      first-left : ConeIso.leftIso first =₂ N
      first-left = isoComp-cong (idIso (comp-assoc dgf (Cone.right t) f))
        (isoComp-cong
          (preWhisker dgf ◁ (inverse-inverse (ConeIso.leftIso Outer.h-comparison)) ⁻¹)
          (idIso ((comp-assoc dgf Outer.h bg) ⁻¹)))

      lifted-left : (bg ◁ χ) =₂ (Kg ⁻¹ ∙ (d ⁻¹ ∙ L))
      lifted-left = isoComp-cong (idIso (Kg ⁻¹))
        (isoComp-cong (idIso (d ⁻¹)) (isoComp-cong (idIso (f ◁ J)) first-left)) ∙ Lift.left-image

      compatible : ((d ∙ Kg) ∙ (bg ◁ χ)) =₂ L
      compatible = cancel-inverse d L ∙
        (isoComp-cong (idIso d) (cancel-inverse Kg (d ⁻¹ ∙ L)) ∙
          (isoComp-cong (idIso d) (isoComp-cong (idIso Kg) lifted-left) ∙
            isoComp-assoc-at d Kg (bg ◁ χ)))

    target-cone : Cone bg f (Fun T A)
    target-cone = record { left = dg ∘ Ff ; right = evaluate z ; match = d ∙ Kg }
    comparison : ConeIso (conePre dgf Outer.outer-square) target-cone
    comparison = record { leftIso = χ ; rightIso = J ; compatible = compatible }

    module Triangle {V : CAT} (q : Cone (evaluate z) f V) (eq : IsPullback q)
      (df : MAP (Fun T A) V) (βf : ConeIso (conePre df q) (EvaluatedComposite.square f)) where
      module Candidate = Outer.Factor dg (evaluate z) κ q eq using (map; map-comparison; square; square-isPullback)
      open Candidate public using (map; square; square-isPullback)
      right-map = Outer.h
      module Edge = Edges.At 𝒯 dg bg κ f using (edge; restrict; action)
      restricted = coneIso-compose (coneIso-pre df Candidate.map-comparison)
        (coneIso-inverse (conePre-assoc df Candidate.map Outer.outer-square))
      to-target : ConeIso (conePre (Candidate.map ∘ df) Outer.outer-square) target-cone
      to-target = coneIso-compose (Edge.action βf)
        (coneIso-compose (Edge.restrict df q) restricted)
      triangle-cones = coneIso-compose (coneIso-inverse comparison) to-target
      module Result = Lifting.UniversalLift 𝒯 P Outer.outer-square Outer.outer-isPullback
        (Candidate.map ∘ df) dgf triangle-cones using (lift; left-image; right-image)
      triangle : (Candidate.map ∘ df) =₁ dgf
      triangle = Result.lift
```
