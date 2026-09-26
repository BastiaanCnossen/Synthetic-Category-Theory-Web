# Acting on pullback cones with a relative functor

Postcomposing the left leg of a pullback cone uses the relative functor's
specified triangle. Its action on cone comparisons and its compatibility
with restriction are the usual composition calculations over the base.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN

module SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.ConeAction
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open PN vocabulary terminal products productLaws composition vertical whiskering
  using (substitution-square-projection)

cone-triangle : {X C D S : CAT} {f : MAP C S} {p : MAP D S}
  (s : Cone f p X) → FunctorOver (p ∘ Cone.right s) f
cone-triangle s = record { lift = Cone.left s ; comparison = Cone.match s }

triangle-cone : {X C D S : CAT} {f : MAP C S} {p : MAP D S}
  (r : MAP X D) → FunctorOver (p ∘ r) f → Cone f p X
triangle-cone r u = record { left = FunctorLift.lift u ; right = r ; match = FunctorLift.comparison u }

triangle-cone-iso : {X C D S : CAT} {f : MAP C S} {p : MAP D S}
  (r : MAP X D) {u v : FunctorOver (p ∘ r) f} → FunctorOverIso u v →
  ConeIso (triangle-cone r u) (triangle-cone r v)
triangle-cone-iso {p = p} r {u} Φ = record
  { leftIso = FunctorOverIso.underlying Φ ; rightIso = idIso r
  ; compatible = isoComp-cong ((postWhisker-idIso p r) ⁻¹) (idIso (FunctorLift.comparison u)) ∙
      ((isoComp-unitˡ-at (FunctorLift.comparison u)) ⁻¹ ∙ FunctorOverIso.compatible Φ) }

module Action {C D S T : CAT} {f : MAP C T} {g : MAP D T}
  (p : MAP S T) (u : FunctorOver f g) where
  value : {X : CAT} → Cone f p X → Cone g p X
  value s = triangle-cone (Cone.right s) (compose-over u (cone-triangle s))

  comparison : {X : CAT} (s : Cone f p X) →
    (g ∘ (FunctorLift.lift u ∘ Cone.left s)) =₁ (f ∘ Cone.left s)
  comparison s = (FunctorLift.comparison u ▷ Cone.left s) ∙
    (comp-assoc (Cone.left s) (FunctorLift.lift u) g) ⁻¹

  map-iso : {X : CAT} {s t : Cone f p X} → ConeIso s t → ConeIso (value s) (value t)
  map-iso {s = s} {t} Φ = record
    { leftIso = FunctorLift.lift u ◁ ConeIso.leftIso Φ ; rightIso = ConeIso.rightIso Φ
    ; compatible = isoComp-assoc-at (p ◁ ConeIso.rightIso Φ) (Cone.match s) (comparison s) ∙
        (isoComp-cong (ConeIso.compatible Φ) (idIso (comparison s)) ∙
          ((isoComp-assoc-at (Cone.match t) (f ◁ ConeIso.leftIso Φ) (comparison s)) ⁻¹ ∙
            (isoComp-cong (idIso (Cone.match t))
              (substitution-square-projection g (FunctorLift.lift u) f (FunctorLift.comparison u) (ConeIso.leftIso Φ)) ∙
              isoComp-assoc-at (Cone.match t) (comparison t) (g ◁ (FunctorLift.lift u ◁ ConeIso.leftIso Φ))))) }

  restriction : {X Y : CAT} (r : MAP Y X) (s : Cone f p X) →
    ConeIso (conePre r (value s)) (value (conePre r s))
  restriction r s = triangle-cone-iso (Cone.right s ∘ r)
    (associator-over (record { lift = r ; comparison = comp-assoc r (Cone.right s) p }) (cone-triangle s) u)

compose-action : {B C D S T X : CAT} {f : MAP B T} {g : MAP C T} {h : MAP D T}
  (p : MAP S T) (u : FunctorOver f g) (v : FunctorOver g h) (s : Cone f p X) →
  ConeIso (Action.value p (compose-over v u) s) (Action.value p v (Action.value p u s))
compose-action p u v s = triangle-cone-iso (Cone.right s) (associator-over (cone-triangle s) u v)

action-identification : {C D S T X : CAT} {f : MAP C T} {g : MAP D T}
  (p : MAP S T) {u v : FunctorOver f g} → FunctorOverIso u v →
  (s : Cone f p X) → ConeIso (Action.value p u s) (Action.value p v s)
action-identification p Φ s = triangle-cone-iso (Cone.right s)
  (prewhisker-over (cone-triangle s) Φ)
```
