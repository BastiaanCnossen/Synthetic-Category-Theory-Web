# Substituting a comparison of squares into a fiber

A whole-cone comparison between two displayed squares identifies their
maps on fibers. The source frame is the right component of that same
comparison. Restriction supplies the required associators; the matching
calculation then uses the retained commutativity witness.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws

module SCT.VolumeI.Chapter01.Section06.Cospans.SquareSubstitution
  {c m a : Level} (𝒯 : Theory c m a) (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.PullbackFunctor 𝒯 P using (CospanMap)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeRestriction 𝒯
  using (conePre-assoc; coneIso-pre; coneIso-compose; coneIso-inverse)
import SCT.VolumeI.Chapter01.Section06.Cospans.FixedParameterConeAction as Map
import SCT.VolumeI.Chapter01.Section06.ConeCalculus.FramedEdgeCones as Edge

module At {A C D Z Q Γ X : CAT} (p : MAP C Z) (b : MAP D Z)
  (s : Cone p b Q) (d : MAP A Q)
  (t : Cone p b A) (Φ : ConeIso (conePre d s) t)
  (x : MAP Γ D) (v : Cone (Cone.right t) x X) where
  private
    h = Cone.left s
    k = Cone.right s
    a₀ = Cone.left v
    r = Cone.right v
    δ = Cone.match v
    module First = Map.Along 𝒯 P k x h p b (b ∘ x) (Cone.match s) (idIso (b ∘ x))
      using (cospan; value; module At)
    module Second = Map.Along 𝒯 P (Cone.right t) x (Cone.left t) p b (b ∘ x)
      (Cone.match t) (idIso (b ∘ x)) using (cospan; value; module At)
    module Source = Edge.At 𝒯 d k (ConeIso.rightIso Φ) x using (edge)

  first-cospan = First.cospan
  second-cospan = Second.cospan
  edge-cone = Source.edge v

  private
    before = First.value edge-cone
    after = Second.value v
    restricted : ConeIso (conePre (d ∘ a₀) s) (conePre a₀ t)
    restricted = coneIso-compose (coneIso-pre a₀ Φ) (coneIso-inverse (conePre-assoc a₀ d s))
    leg = ConeIso.leftIso restricted
    frame = ConeIso.rightIso restricted
    σ = Cone.match (conePre (d ∘ a₀) s)
    τ = Cone.match (conePre a₀ t)
    U = idIso (b ∘ x) ▷ r
    V = (comp-assoc r x b) ⁻¹
    R₀ = U ∙ V
    M₀ = b ◁ δ
    N = b ◁ frame
    L = p ◁ leg

    abstract
      distribute : Cone.match before =₂ (R₀ ∙ (M₀ ∙ (N ∙ σ)))
      distribute = isoComp-cong (idIso R₀) (isoComp-assoc-at M₀ N σ) ∙
        ((isoComp-assoc-at U V ((M₀ ∙ N) ∙ σ)) ⁻¹ ∙
          isoComp-cong (idIso U) (isoComp-cong (idIso V)
            (isoComp-cong (postWhisker-isoComp-at b δ frame) (idIso σ))))

      matching : Cone.match before =₂ (Cone.match after ∙ L)
      matching = isoComp-cong ((isoComp-assoc-at U V (M₀ ∙ τ))) (idIso L) ∙
        ((isoComp-assoc-at R₀ (M₀ ∙ τ) L) ⁻¹ ∙
        (isoComp-cong (idIso R₀) ((isoComp-assoc-at M₀ τ L) ⁻¹) ∙
        (isoComp-cong (idIso R₀) (isoComp-cong (idIso M₀) ((ConeIso.compatible restricted) ⁻¹)) ∙ distribute)))

    normalized-comparison : ConeIso before after
    normalized-comparison = record { leftIso = leg ; rightIso = idIso r
      ; compatible = isoComp-cong ((postWhisker-idIso (b ∘ x) r) ⁻¹) (idIso (Cone.match before)) ∙
          ((isoComp-unitˡ-at (Cone.match before)) ⁻¹ ∙ matching ⁻¹) }

  comparison : ConeIso (CospanMap.mapCone first-cospan edge-cone) (CospanMap.mapCone second-cospan v)
  comparison = coneIso-compose (coneIso-inverse (Second.At.comparison v))
    (coneIso-compose normalized-comparison (First.At.comparison edge-cone))
```
