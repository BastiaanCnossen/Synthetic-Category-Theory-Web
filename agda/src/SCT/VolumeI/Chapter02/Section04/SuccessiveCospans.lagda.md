# Two successive changes of cospan

If the three composite object maps are equivalences, applying the two
cospan maps successively takes a universal cone to a universal cone.
The proof lifts its two legs and its matching through those composite
equivalences. It works directly with successive operations, avoiding any
choice of a separately normalized composite cospan map.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws

module SCT.VolumeI.Chapter02.Section04.SuccessiveCospans
  {c m a : Level} (𝒯 : Theory c m a) (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open Laws.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.PullbackFunctor 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.PullbackCriterion 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.ConeSymmetry 𝒯 using (cone-match-change)
open import SCT.VolumeI.Chapter01.Section06.ComparisonSquares 𝒯
open import SCT.VolumeI.Chapter01.Section06.ProjectionRestriction 𝒯 using (project-transport)
open import SCT.VolumeI.Chapter02.Section04.CospanCones 𝒯 P using (module Action)
open import SCT.VolumeI.Chapter02.Section04.DoubleWhiskering 𝒯 using (module Double)
open import SCT.VolumeI.Chapter01.Section04.CoherenceTransport 𝒯 using (changeEndpoints)
open import SCT.VolumeI.Chapter01.Section06.InverseCalculus 𝒯 using (inverse-composite)

transport-twice : {C D : CAT} {u v u′ v′ u″ v″ : MAP C D}
  (p : u =₁ u′) (q : v =₁ v′) (p′ : u′ =₁ u″) (q′ : v′ =₁ v″) (α : u =₁ v) →
  (changeEndpoints p′ q′ (changeEndpoints p q α)) =₂ (changeEndpoints (p′ ∙ p) (q′ ∙ q) α)
transport-twice p q p′ q′ α = isoComp-cong (idIso (q′ ∙ q))
    (isoComp-cong (idIso α) ((inverse-composite p′ p) ⁻¹) ∙ isoComp-assoc-at α (p ⁻¹) (p′ ⁻¹)) ∙
  ((isoComp-assoc-at q′ q ((α ∙ p ⁻¹) ∙ p′ ⁻¹)) ⁻¹ ∙
    isoComp-cong (idIso q′) (isoComp-assoc-at q (α ∙ p ⁻¹) (p′ ⁻¹)))

module Successive {C D E C′ D′ E′ C″ D″ E″ : CAT}
  {f : MAP C E} {g : MAP D E} {f′ : MAP C′ E′} {g′ : MAP D′ E′}
  {f″ : MAP C″ E″} {g″ : MAP D″ E″}
  (first : CospanMap f g f′ g′) (second : CospanMap f′ g′ f″ g″)
  (el : IsEquiv (CospanMap.left second ∘ CospanMap.left first))
  (er : IsEquiv (CospanMap.right second ∘ CospanMap.right first))
  (eb : IsEquiv (CospanMap.base second ∘ CospanMap.base first)) where

  module F = CospanMap first
  module G = CospanMap second
  module FA = Action first
  module GA = Action second
  module LiftsLeft = Double F.left G.left el
  module LiftsRight = Double F.right G.right er
  module LiftsBase = Double F.base G.base eb

  left-normal : {Γ : CAT} (p : MAP Γ C) →
    LiftsBase.value (f ∘ p) =₁ (f″ ∘ LiftsLeft.value p)
  left-normal p = GA.Normal.left-normal (F.left ∘ p) ∙ (G.base ◁ FA.Normal.left-normal p)
  right-normal : {Γ : CAT} (q : MAP Γ D) →
    LiftsBase.value (g ∘ q) =₁ (g″ ∘ LiftsRight.value q)
  right-normal q = GA.Normal.right-normal (F.right ∘ q) ∙ (G.base ◁ FA.Normal.right-normal q)

  value : {Γ : CAT} → Cone f g Γ → Cone f″ g″ Γ
  value s = record
    { left = LiftsLeft.value (Cone.left s) ; right = LiftsRight.value (Cone.right s)
    ; match = right-normal (Cone.right s) ∙
        ((G.base ◁ (F.base ◁ Cone.match s)) ∙ (left-normal (Cone.left s)) ⁻¹) }

  raw : {Γ : CAT} → Cone f g Γ → Cone f″ g″ Γ
  raw s = GA.Normal.read (FA.Normal.read s)

  normalize : {Γ : CAT} (s : Cone f g Γ) → ConeIso (raw s) (value s)
  normalize s = cone-match-change _ _ _ _
    (transport-twice (G.base ◁ l) (G.base ◁ r) l′ r′ (G.base ◁ (F.base ◁ Cone.match s)) ∙
      isoComp-cong (idIso r′)
        (isoComp-cong (project-transport G.base l r (F.base ◁ Cone.match s)) (idIso (l′ ⁻¹))))
    where
    l = FA.Normal.left-normal (Cone.left s)
    r = FA.Normal.right-normal (Cone.right s)
    l′ = GA.Normal.left-normal (F.left ∘ Cone.left s)
    r′ = GA.Normal.right-normal (F.right ∘ Cone.right s)

  map-comparison : {Γ : CAT} (s : Cone f g Γ) →
    ConeIso (G.mapCone (F.mapCone s)) (value s)
  map-comparison s = coneIso-compose (normalize s)
    (coneIso-compose (GA.comparison (FA.Normal.read s)) (GA.map-iso (FA.comparison s)))

  value-iso : {Γ : CAT} {s t : Cone f g Γ} → ConeIso s t → ConeIso (value s) (value t)
  value-iso {s = s} {t} Φ = coneIso-compose (normalize t)
    (coneIso-compose (GA.Normal.read-iso (FA.Normal.read-iso Φ)) (coneIso-inverse (normalize s)))

  value-pre : {Γ Δ : CAT} (r : MAP Δ Γ) (s : Cone f g Γ) →
    ConeIso (value (conePre r s)) (conePre r (value s))
  value-pre r s = coneIso-compose (coneIso-pre r (normalize s))
    (coneIso-compose (GA.Normal.read-pre r (FA.Normal.read s))
    (coneIso-compose (GA.Normal.read-iso (FA.Normal.read-pre r s))
      (coneIso-inverse (normalize (conePre r s)))))

  left-natural : {Γ : CAT} {p q : MAP Γ C} (α : p =₁ q) →
    (left-normal q ∙ (G.base ◁ (F.base ◁ (f ◁ α)))) =₂
      ((f″ ◁ (G.left ◁ (F.left ◁ α))) ∙ left-normal p)
  left-natural {p = p} {q} α = paste-squares
    (G.base ◁ FA.Normal.left-normal p) (G.base ◁ FA.Normal.left-normal q)
    (GA.Normal.left-normal (F.left ∘ p)) (GA.Normal.left-normal (F.left ∘ q)) _ _ _
    (post-square G.base _ _ _ _ (FA.Normal.left-natural α))
    (GA.Normal.left-natural (F.left ◁ α))

  right-natural : {Γ : CAT} {p q : MAP Γ D} (α : p =₁ q) →
    (right-normal q ∙ (G.base ◁ (F.base ◁ (g ◁ α)))) =₂
      ((g″ ◁ (G.right ◁ (F.right ◁ α))) ∙ right-normal p)
  right-natural {p = p} {q} α = paste-squares
    (G.base ◁ FA.Normal.right-normal p) (G.base ◁ FA.Normal.right-normal q)
    (GA.Normal.right-normal (F.right ∘ p)) (GA.Normal.right-normal (F.right ∘ q)) _ _ _
    (post-square G.base _ _ _ _ (FA.Normal.right-natural α))
    (GA.Normal.right-natural (F.right ◁ α))

  base-compose : {Γ : CAT} {p q r : MAP Γ E} (β : q =₁ r) (α : p =₁ q) →
    (G.base ◁ (F.base ◁ (β ∙ α))) =₂
      ((G.base ◁ (F.base ◁ β)) ∙ (G.base ◁ (F.base ◁ α)))
  base-compose β α = postWhisker-isoComp-at G.base (F.base ◁ β) (F.base ◁ α) ∙
    (postWhisker G.base ◁ postWhisker-isoComp-at F.base β α)

  module Reflect {Γ : CAT} (s t : Cone f g Γ) (Φ : ConeIso (value s) (value t)) where
    module LL = LiftsLeft.Isomorphisms.LiftIso (Cone.left s) (Cone.left t) (ConeIso.leftIso Φ)
    module RR = LiftsRight.Isomorphisms.LiftIso (Cone.right s) (Cone.right t) (ConeIso.rightIso Φ)
    α = LL.lift
    β = RR.lift
    raw-square = reflect-transport-square
      (left-normal (Cone.left s)) (left-normal (Cone.left t))
      (right-normal (Cone.right s)) (right-normal (Cone.right t)) _ _ _ _ _ _
      (left-natural α) (right-natural β)
      (isoComp-cong ((postWhisker g″ ◁ RR.comparison) ⁻¹) (idIso (Cone.match (value s))) ∙
        (ConeIso.compatible Φ ∙ isoComp-cong (idIso (Cone.match (value t)))
          (postWhisker f″ ◁ LL.comparison)))

    comparison : ConeIso s t
    comparison = record { leftIso = α ; rightIso = β
      ; compatible = LiftsBase.Isomorphisms.reflect (f ∘ Cone.left s) (g ∘ Cone.right t) _ _
          ((base-compose (g ◁ β) (Cone.match s)) ⁻¹ ∙
            (raw-square ∙ base-compose (Cone.match t) (f ◁ α))) }

  module LiftCone {Γ : CAT} (t : Cone f″ g″ Γ) where
    module LL = LiftsLeft.Lift (Cone.left t)
    module RR = LiftsRight.Lift (Cone.right t)
    l = left-normal LL.lift
    r = right-normal RR.lift
    α = f″ ◁ LL.comparison
    β = g″ ◁ RR.comparison
    desired = (β ∙ r) ⁻¹ ∙ (Cone.match t ∙ (α ∙ l))
    module Match = LiftsBase.Isomorphisms.LiftIso (f ∘ LL.lift) (g ∘ RR.lift) desired
    lift : Cone f g Γ
    lift = record { left = LL.lift ; right = RR.lift ; match = Match.lift }
    comparison : ConeIso (value lift) t
    comparison = record { leftIso = LL.comparison ; rightIso = RR.comparison
      ; compatible = encoded-restriction-square l r α β (Cone.match t)
          (G.base ◁ (F.base ◁ Match.lift)) Match.comparison }

  module Preserve {S : CAT} (s : Cone f g S) (es : IsPullback s) where
    module Source = UniversalCone s es
    target = pullbackCone f″ g″
    module Lift = LiftCone target
    inverse = Source.factor Lift.lift
    factorization : ConeIso (conePre inverse (value s)) target
    factorization = coneIso-compose Lift.comparison
      (coneIso-compose (value-iso (Source.factor-β Lift.lift))
        (coneIso-inverse (value-pre inverse s)))
    reflect : (h k : MAP S S) → ConeIso (conePre h (value s)) (conePre k (value s)) → h =₁ k
    reflect h k Φ = Source.reflect h k (Reflect.comparison (conePre h s) (conePre k s)
      (coneIso-compose (coneIso-inverse (value-pre k s)) (coneIso-compose Φ (value-pre h s))))
    value-isPullback : IsPullback (value s)
    value-isPullback = cone-isPullback-from-lifting (value s) inverse factorization reflect
    map-isPullback : IsPullback (G.mapCone (F.mapCone s))
    map-isPullback = pullback-cone-invariant (coneIso-inverse (map-comparison s)) value-isPullback

  pullback-map-comparison : ConeIso
    (conePre (G.pullbackMap ∘ F.pullbackMap) (pullbackCone f″ g″))
    (G.mapCone (F.mapCone (pullbackCone f g)))
  pullback-map-comparison = coneIso-compose (GA.map-iso F.pullbackMap-β)
    (coneIso-compose (coneIso-inverse (GA.map-pre F.pullbackMap (pullbackCone f′ g′)))
    (coneIso-compose (coneIso-pre F.pullbackMap G.pullbackMap-β)
      (coneIso-inverse (conePre-assoc F.pullbackMap G.pullbackMap (pullbackCone f″ g″)))))

  composite-isEquiv : IsEquiv (G.pullbackMap ∘ F.pullbackMap)
  composite-isEquiv = pullback-comparison
    (G.mapCone (F.mapCone (pullbackCone f g))) (pullbackCone f″ g″)
    (G.pullbackMap ∘ F.pullbackMap) pullback-map-comparison
    (Preserve.map-isPullback (pullbackCone f g) (pullbackCone-isPullback f g))
    (pullbackCone-isPullback f″ g″)
```
