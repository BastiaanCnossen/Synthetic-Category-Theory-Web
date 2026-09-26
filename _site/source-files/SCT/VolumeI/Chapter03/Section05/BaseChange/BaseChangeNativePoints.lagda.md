# Base change on named triangles

The map on relative mapping animae agrees with pullback of a native
triangle. The comparison below retains the triangle over the new base;
it is obtained by restricting the universal pullback cone to a point.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section02.Isomorphisms as Isomorphisms
import SCT.VolumeI.Chapter03.Section05.Currying.PointPullbackCone as Points

module SCT.VolumeI.Chapter03.Section05.BaseChange.BaseChangeNativePoints
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section07.Functoriality 𝒯 M ℱ using (funPost)
open import SCT.VolumeI.Chapter01.Section07.AbsoluteObjects 𝒯 M ℱ using (nameFun)
open import SCT.VolumeI.Chapter01.Section04.Core 𝒯 M using (coreInclusion)
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeRestriction 𝒯
  using (coneIso-compose; coneIso-inverse; coneIso-pre; conePre-assoc)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeSymmetry 𝒯 using (cone-match-change)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯 using (inverse-identity)
open Isomorphisms vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.EvaluatedRelativeCones 𝒯 M ℱ P using (EvaluatedCone)
open import SCT.VolumeI.Chapter03.RelativeCategories.Families.NativePointFamilies 𝒯 M ℱ P using (point-parameter; universal-point)
open import SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.BaseChange 𝒯 M ℱ P using (module BaseChange)
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.ConeAction 𝒯 M ℱ P using (module Action; compose-action)
open import SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.Identifications 𝒯 M ℱ P using (module Change)
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.PullbackTriangles 𝒯 M ℱ P using (module Reflect)
open import SCT.VolumeI.Chapter03.RelativeCategories.IdentificationCalculus.NamingComparisons 𝒯 M ℱ P using (module Triangles)

module BaseChangePoints {C D S T : CAT} (p : MAP S T) (f : MAP C T) (g : MAP D T) where
  module BC = BaseChange p f g
  E : FunctorOver (f ∘ pr₂ {C = FunOver f g}) g
  E = EvaluatedCone (pullbackCone (funPost g) (nameFun f))

  module At (x : Obj-abs (MapOver f g)) where
    z : Obj-abs (FunOver f g)
    z = coreInclusion (FunOver f g) ∘ x
    module Point = Points.At 𝒯 M ℱ P z (pullbackCone f p)
    tail = (FunctorLift.comparison E ▷ BC.parameter) ∙
      (comp-assoc BC.parameter (FunctorLift.lift E) g) ⁻¹

    abstract
      matching : Cone.match (Action.value p E Point.parameterized) =₂ Cone.match BC.cone
      matching = isoComp-cong (idIso Point.bq)
          (isoComp-cong (idIso (Point.τ ▷ pr₂))
            (isoComp-cong (idIso (Point.br ⁻¹))
              (isoComp-assoc-at (f ◁ pair-β₂ (id BC.X ∘ pr₁) (pullback₁ ∘ pr₂))
                (comp-assoc BC.parameter pr₂ f) tail) ∙
              isoComp-assoc-at (Point.br ⁻¹) Point.bR tail) ∙
            isoComp-assoc-at (Point.τ ▷ pr₂) (Point.br ⁻¹ ∙ Point.bR) tail) ∙
          isoComp-assoc-at Point.bq ((Point.τ ▷ pr₂) ∙ (Point.br ⁻¹ ∙ Point.bR)) tail

    factorization : ConeIso BC.cone (Action.value p E Point.parameterized)
    factorization = cone-match-change _ _ _ _ (matching ⁻¹)
    u = compose-over E (point-parameter f z)
    w = compose-over BC.evaluated (point-parameter BC.f′ z)
    v = Change.functor p u
    βe = pullbackLift-β₂ BC.cone
    βv = pullbackLift-β₂ (Change.cone p u)
    κ = (βe ▷ Point.K) ∙ (comp-assoc Point.K BC.evaluation BC.g′) ⁻¹

    cones : ConeIso (conePre (FunctorLift.lift w) (pullbackCone g p))
      (conePre (FunctorLift.lift v) (pullbackCone g p))
    cones = coneIso-compose (coneIso-inverse (pullbackLift-β (Change.cone p u)))
      (coneIso-compose (coneIso-inverse (compose-action p (point-parameter f z) E (pullbackCone f p)))
        (coneIso-compose (Action.map-iso p E Point.comparison)
          (coneIso-compose (Action.restriction p E Point.K Point.parameterized)
            (coneIso-compose (coneIso-pre Point.K factorization)
              (coneIso-compose (coneIso-pre Point.K (pullbackLift-β BC.cone))
                (coneIso-inverse (conePre-assoc Point.K BC.evaluation (pullbackCone g p))))))))

    abstract
      right-comparison : (βv ∙ ConeIso.rightIso cones) =₂ FunctorLift.comparison w
      right-comparison = isoComp-cong (idIso (Point.Source.triangle BC.f′))
          (isoComp-unitˡ-at κ ∙
            (isoComp-cong (preWhisker-idIso (BC.f′ ∘ pr₂) Point.K) (idIso κ) ∙
              isoComp-unitˡ-at ((idIso (BC.f′ ∘ pr₂) ▷ Point.K) ∙ κ))) ∙
        (isoComp-unitˡ-at (Point.Source.triangle BC.f′ ∙
          (idIso ((BC.f′ ∘ pr₂) ∘ Point.K) ∙ ((idIso (BC.f′ ∘ pr₂) ▷ Point.K) ∙ κ))) ∙
          (isoComp-cong (inverse-identity BC.f′)
            (idIso (Point.Source.triangle BC.f′ ∙
              (idIso ((BC.f′ ∘ pr₂) ∘ Point.K) ∙ ((idIso (BC.f′ ∘ pr₂) ▷ Point.K) ∙ κ)))) ∙
            cancel-inverse βv ((idIso BC.f′) ⁻¹ ∙
              (Point.Source.triangle BC.f′ ∙
                (idIso ((BC.f′ ∘ pr₂) ∘ Point.K) ∙ ((idIso (BC.f′ ∘ pr₂) ▷ Point.K) ∙ κ))))))

      native : FunctorOverIso w v
      native = Reflect.comparison w v cones right-comparison

      comparison : FunctorOverIso (Over.decode-over BC.f′ BC.g′ (BC.maps ∘ x))
        (Change.functor p (Over.decode-over f g x))
      comparison = compose-iso-over (Change.Identification.comparison p (inverse-iso-over (universal-point f g x)))
        (compose-iso-over native (BC.on-points-over x))

  abstract
    on-named-points : (u : FunctorOver f g) →
      (BC.maps ∘ Over.name-over f g u) =₁ Over.name-over BC.f′ BC.g′ (Change.functor p u)
    on-named-points u = Triangles.Identification.identification BC.f′ BC.g′ _ _
        (compose-iso-over (Change.Identification.comparison p (Triangles.decode-name-native f g u))
          (At.comparison (Over.name-over f g u))) ∙
      (Over.name-decode-over BC.f′ BC.g′ (BC.maps ∘ Over.name-over f g u)) ⁻¹
```

