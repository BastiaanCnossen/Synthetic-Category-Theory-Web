# Realizing operations on pullback cones

An operation on cones, compatible with their comparisons and parameter
restriction, induces a functor between the representing pullbacks.
Its computation rule retains the whole cone, including its matching.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level; _⊔_)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws

module SCT.VolumeI.Chapter01.Section06.ConeCalculus.Operations
  {c m a : Level} (𝒯 : Theory c m a) (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open Laws.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.PullbackLifting 𝒯 P using (pullback-reflect)

record ConeOperation {A B Z A′ B′ Z′ : CAT}
  (f : MAP A Z) (g : MAP B Z) (f′ : MAP A′ Z′) (g′ : MAP B′ Z′) : Set (c ⊔ m) where
  field
    act : {Γ : CAT} → Cone f g Γ → Cone f′ g′ Γ
    compare : {Γ : CAT} {s t : Cone f g Γ} → ConeIso s t → ConeIso (act s) (act t)
    restrict : {Γ Δ : CAT} (s : Cone f g Γ) (r : MAP Δ Γ) →
      ConeIso (conePre r (act s)) (act (conePre r s))

module Realize {A B Z A′ B′ Z′ : CAT}
  {f : MAP A Z} {g : MAP B Z} {f′ : MAP A′ Z′} {g′ : MAP B′ Z′}
  (F : ConeOperation f g f′ g′) where
  open ConeOperation F
  private
    source-cone = pullbackCone f g
    target-cone = pullbackCone f′ g′

  map : MAP (Pullback f g) (Pullback f′ g′)
  map = pullbackLift (act source-cone)

  abstract
    map-β : {Γ : CAT} (s : Cone f g Γ) →
      ConeIso (conePre (map ∘ pullbackLift s) target-cone) (act s)
    map-β s = coneIso-compose (compare (pullbackLift-β s))
      (coneIso-compose (restrict source-cone (pullbackLift s))
        (coneIso-compose (coneIso-pre (pullbackLift s) (pullbackLift-β (act source-cone)))
          (coneIso-inverse (conePre-assoc (pullbackLift s) map target-cone))))

    preserves-pullback : IsEquiv map → {Γ : CAT} (s : Cone f g Γ) →
      IsPullback s → IsPullback (act s)
    preserves-pullback em s es = pullback-cone-invariant (map-β s)
      (pullback-restrict-equivalence target-cone (map ∘ pullbackLift s)
        (pullbackCone-isPullback f′ g′) (equiv-compose (pullbackLift s) map es em))

module Inverse {A B Z A′ B′ Z′ : CAT}
  {f : MAP A Z} {g : MAP B Z} {f′ : MAP A′ Z′} {g′ : MAP B′ Z′}
  (F : ConeOperation f g f′ g′) (G : ConeOperation f′ g′ f g)
  (law : {Γ : CAT} (s : Cone f g Γ) → ConeIso (ConeOperation.act G (ConeOperation.act F s)) s) where
  private
    module Forward = Realize F
    module Backward = Realize G
    source-cone = pullbackCone f g

  inverse-comparison : (Backward.map ∘ Forward.map) =₁ (id (Pullback f g))
  inverse-comparison = pullback-reflect _ _
    (coneIso-compose (coneIso-inverse (conePre-id source-cone))
      (coneIso-compose (law source-cone) (Backward.map-β (ConeOperation.act F source-cone))))
```
