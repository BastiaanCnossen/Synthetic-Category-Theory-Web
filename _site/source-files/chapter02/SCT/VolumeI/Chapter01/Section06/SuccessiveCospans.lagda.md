# Two successive changes of cospan

Two changes of cospan preserve universality if their three composite object
maps are equivalences. Neither change needs to be an equivalence separately.
The construction acts successively on the actual cones, including their
specified matchings. It does not identify the composite cospan with an identity
cospan. Constant diagrams followed by evaluation are the intended application.

The coordinate interface from ProductPullbacks retains the same normalization
paths in both the generic construction and its consumers.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section06.SuccessiveCospans where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary hiding (_＝_)
open import SCT.VolumeI.Chapter01.Section01.Terms using (Equal)
open Operations
open import SCT.VolumeI.Chapter01.Section02.Coherence using (comp-assoc; id₌; inv₌; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Specialization
open import SCT.VolumeI.Chapter01.Section02.IdentificationSquares using (paste-square₌; post-square₌)
open import SCT.VolumeI.Chapter01.Section03.Equivalences using (equiv-reflect; equiv-transport; equiv-cancel-left)
import SCT.VolumeI.Chapter01.Section03.Factorizations as Fact
open import SCT.VolumeI.Chapter01.Section03.WhiskeringEquivalence
  using (postWhisker-isEquiv; postWhisker-composite-isEquiv)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses
open import SCT.VolumeI.Chapter01.Section03.Identifications.EndpointTransport
  using (changeEndpoints; changeEndpoints-iterated; postWhisker-changeEndpoints;
    reflect-transported-square; encoded-restriction-square)
open import SCT.VolumeI.Chapter01.Section06.Cones
open import SCT.VolumeI.Chapter01.Section06.ConeIdentifications
open import SCT.VolumeI.Chapter01.Section06.ConeTransport using (cone-retarget-match-identification)
open import SCT.VolumeI.Chapter01.Section06.ConeUniversality using (isPullback-cone-identification)
open import SCT.VolumeI.Chapter01.Section06.Pullbacks
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares
open import SCT.VolumeI.Chapter01.Section06.PullbackConstructions using (pullback-cone-isPullback)
open import SCT.VolumeI.Chapter01.Section06.PullbackFunctoriality
  using (CospanMap; pullback-map; pullback-map-β)
import SCT.VolumeI.Chapter01.Section06.ProductPullbacks as Coordinates
```

## The action on complete cones

The native seven-factor matching is endpoint transport of the original
matching. Its comparison and restriction laws follow from the same coordinate
operation already used for products of pullbacks.

```agda
module Action {Γ : Context} {C D E C′ D′ E′ : CAT Γ}
  {f : MAP C E} {g : MAP D E} {f′ : MAP C′ E′} {g′ : MAP D′ E′}
  (F : CospanMap f g f′ g′) where
  open CospanMap F renaming
    (left to u; right to v; base to w; left-square to α; right-square to β)
  module Normal = Coordinates.Coordinate f g f′ g′ u v w (α ⁻¹) (β ⁻¹)
    using (left-normal; right-normal; left-natural; right-natural; read; read-identification; read-restrict)

  private
    left-inverse : {T : CAT Γ} (p : MAP T C) →
      (Normal.left-normal p) ⁻¹ =₂
        (comp-assoc p f w ∙ ((α ▷ p) ∙ (comp-assoc p u f′) ⁻¹))
    left-inverse p = comp₌-assoc A (α ▷ p) (B ⁻¹) ∙
      (comp₌-cong
        (comp₌-cong (inverse-inverse A)
          (inverse-inverse (α ▷ p) ∙ (inv₌ ◁ preWhisker-inverse α p)) ∙
          inverse-composite (α ⁻¹ ▷ p) (A ⁻¹))
        (id₌ (B ⁻¹)) ∙ inverse-composite B ((α ⁻¹ ▷ p) ∙ A ⁻¹))
      where
      A = comp-assoc p f w
      B = comp-assoc p u f′

  normalization : {T : CAT Γ} (s : Cone f g T) →
    Cone.match (map-cone s) =₂ Cone.match (Normal.read s)
  normalization s =
    comp₌-cong (id₌ (Normal.right-normal q))
      (comp₌-cong (id₌ (w ◁ τ)) ((left-inverse p) ⁻¹)) ∙
    ((comp₌-assoc A (B ∙ dPath) tail) ⁻¹ ∙
      comp₌-cong (id₌ A) ((comp₌-assoc B dPath tail) ⁻¹))
    where
    p = Cone.left s
    q = Cone.right s
    τ = Cone.match s
    A = comp-assoc q v g′
    B = β ⁻¹ ▷ q
    dPath = (comp-assoc q g w) ⁻¹
    tail = (w ◁ τ) ∙ (comp-assoc p f w ∙ ((α ▷ p) ∙ (comp-assoc p u f′) ⁻¹))

  comparison : {T : CAT Γ} (s : Cone f g T)
    → ConeIdentification₁ (map-cone s) (Normal.read s)
  comparison s = cone-retarget-match-identification (map-cone s) (Cone.match (Normal.read s)) (normalization s)

  map-identification : {T : CAT Γ} {s t : Cone f g T}
    → ConeIdentification₁ s t → ConeIdentification₁ (map-cone s) (map-cone t)
  map-identification {s = s} {t} Φ = cone-compose (cone-inverse (comparison t))
    (cone-compose (Normal.read-identification Φ) (comparison s))

  map-restrict : {S T : CAT Γ} (r : MAP S T) (s : Cone f g T)
    → ConeIdentification₁ (map-cone (cone-restrict r s)) (cone-restrict r (map-cone s))
  map-restrict r s = cone-compose (cone-identification-restrict-One r (cone-inverse (comparison s)))
    (cone-compose (Normal.read-restrict r s) (comparison (cone-restrict r s)))
```

## Lifting through successive functors

Lift objects through the composite equivalence, but retain the successive
expression in the comparison. The same argument on identification animae
lifts and reflects the actual twice-whiskered matching.

```agda
private
  module Double {Γ : Context} {C D E : CAT Γ}
    (u : MAP C D) (v : MAP D E) (e : IsEquiv (v ∘ u)) where
    value : {T : CAT Γ} → MAP T C → MAP T E
    value h = v ∘ (u ∘ h)

    module Lift {T : CAT Γ} (h : MAP T E) where
      chosen = Fact.factor-through-equiv e h
      lift : MAP T C
      lift = Fact.factor chosen
      comparison : value lift =₁ h
      comparison = Fact.triangle chosen ∙ (comp-assoc lift u v) ⁻¹

    module Identifications {T : CAT Γ} (h k : MAP T C) where
      action : MAP (Equal h k) (Equal (value h) (value k))
      action = postWhisker v ∘ postWhisker u
      action-isEquiv : IsEquiv action
      action-isEquiv = postWhisker-composite-isEquiv h k u v (postWhisker-isEquiv (v ∘ u) e h k)
      evaluate : (α : h =₁ k) → (action ∘ α) =₂ (v ◁ (u ◁ α))
      evaluate α = comp-assoc α (postWhisker u) (postWhisker v)
      module LiftIdentification (α : value h =₁ value k) where
        chosen = Fact.factor-through-equiv action-isEquiv α
        lift : h =₁ k
        lift = Fact.factor chosen
        comparison : (v ◁ (u ◁ lift)) =₂ α
        comparison = Fact.triangle chosen ∙ (evaluate lift) ⁻¹
      reflect : (α β : h =₁ k) → (v ◁ (u ◁ α)) =₂ (v ◁ (u ◁ β)) → α =₂ β
      reflect α β p = equiv-reflect action-isEquiv α β ((evaluate β) ⁻¹ ∙ (p ∙ evaluate α))
```

## Universality and the induced composite

The middle cone is retained literally. Normalization only regroups its endpoint
transport; no law identifying different cospan squares is assumed.

```agda
module Successive {Γ : Context} {C D E C′ D′ E′ C″ D″ E″ : CAT Γ}
  {f : MAP C E} {g : MAP D E} {f′ : MAP C′ E′} {g′ : MAP D′ E′}
  {f″ : MAP C″ E″} {g″ : MAP D″ E″}
  (first : CospanMap f g f′ g′) (second : CospanMap f′ g′ f″ g″)
  (el : IsEquiv (CospanMap.left second ∘ CospanMap.left first))
  (er : IsEquiv (CospanMap.right second ∘ CospanMap.right first))
  (eb : IsEquiv (CospanMap.base second ∘ CospanMap.base first)) where

  module F = CospanMap first
    using (base; left; map-cone; right)
  module G = CospanMap second
    using (base; left; map-cone; right)
  module FA = Action first
    using (comparison; module Normal)
  module GA = Action second
    using (comparison; map-identification; map-restrict; module Normal)
  module LiftsLeft = Double F.left G.left el
    using (value; module Identifications; module Lift)
  module LiftsRight = Double F.right G.right er
    using (value; module Identifications; module Lift)
  module LiftsBase = Double F.base G.base eb
    using (value; module Identifications)

  left-normal : {T : CAT Γ} (p : MAP T C) →
    LiftsBase.value (f ∘ p) =₁ (f″ ∘ LiftsLeft.value p)
  left-normal p = GA.Normal.left-normal (F.left ∘ p) ∙ (G.base ◁ FA.Normal.left-normal p)
  right-normal : {T : CAT Γ} (q : MAP T D) →
    LiftsBase.value (g ∘ q) =₁ (g″ ∘ LiftsRight.value q)
  right-normal q = GA.Normal.right-normal (F.right ∘ q) ∙ (G.base ◁ FA.Normal.right-normal q)

  value : {T : CAT Γ} → Cone f g T → Cone f″ g″ T
  value s = record
    { left = LiftsLeft.value (Cone.left s) ; right = LiftsRight.value (Cone.right s)
    ; match = right-normal (Cone.right s) ∙
        ((G.base ◁ (F.base ◁ Cone.match s)) ∙ (left-normal (Cone.left s)) ⁻¹) }

  raw : {T : CAT Γ} → Cone f g T → Cone f″ g″ T
  raw s = GA.Normal.read (FA.Normal.read s)

  normalize : {T : CAT Γ} (s : Cone f g T) → ConeIdentification₁ (raw s) (value s)
  normalize s = cone-retarget-match-identification (raw s) (Cone.match (value s))
    (changeEndpoints-iterated (G.base ◁ l) (G.base ◁ r) l′ r′ (G.base ◁ (F.base ◁ Cone.match s)) ∙
      comp₌-cong (id₌ r′)
        (comp₌-cong (postWhisker-changeEndpoints G.base l r (F.base ◁ Cone.match s)) (id₌ (l′ ⁻¹))))
    where
    l = FA.Normal.left-normal (Cone.left s)
    r = FA.Normal.right-normal (Cone.right s)
    l′ = GA.Normal.left-normal (F.left ∘ Cone.left s)
    r′ = GA.Normal.right-normal (F.right ∘ Cone.right s)

  map-comparison : {T : CAT Γ} (s : Cone f g T) →
    ConeIdentification₁ (G.map-cone (F.map-cone s)) (value s)
  map-comparison s = cone-compose (normalize s)
    (cone-compose (GA.comparison (FA.Normal.read s)) (GA.map-identification (FA.comparison s)))

  value-identification : {T : CAT Γ} {s t : Cone f g T} → ConeIdentification₁ s t → ConeIdentification₁ (value s) (value t)
  value-identification {s = s} {t} Φ = cone-compose (normalize t)
    (cone-compose (GA.Normal.read-identification (FA.Normal.read-identification Φ)) (cone-inverse (normalize s)))

  value-pre : {R T : CAT Γ} (r : MAP R T) (s : Cone f g T) →
    ConeIdentification₁ (value (cone-restrict r s)) (cone-restrict r (value s))
  value-pre r s = cone-compose (cone-identification-restrict-One r (normalize s))
    (cone-compose (GA.Normal.read-restrict r (FA.Normal.read s))
    (cone-compose (GA.Normal.read-identification (FA.Normal.read-restrict r s))
      (cone-inverse (normalize (cone-restrict r s)))))

  left-natural : {T : CAT Γ} {p q : MAP T C} (α : p =₁ q) →
    (left-normal q ∙ (G.base ◁ (F.base ◁ (f ◁ α)))) =₂
      ((f″ ◁ (G.left ◁ (F.left ◁ α))) ∙ left-normal p)
  left-natural {p = p} {q} α = paste-square₌
    (post-square₌ G.base (FA.Normal.left-natural α))
    (GA.Normal.left-natural (F.left ◁ α))

  right-natural : {T : CAT Γ} {p q : MAP T D} (α : p =₁ q) →
    (right-normal q ∙ (G.base ◁ (F.base ◁ (g ◁ α)))) =₂
      ((g″ ◁ (G.right ◁ (F.right ◁ α))) ∙ right-normal p)
  right-natural {p = p} {q} α = paste-square₌
    (post-square₌ G.base (FA.Normal.right-natural α))
    (GA.Normal.right-natural (F.right ◁ α))

  base-compose : {T : CAT Γ} {p q r : MAP T E} (β : q =₁ r) (α : p =₁ q) →
    (G.base ◁ (F.base ◁ (β ∙ α))) =₂
      ((G.base ◁ (F.base ◁ β)) ∙ (G.base ◁ (F.base ◁ α)))
  base-compose β α = postWhisker-comp₌ G.base (F.base ◁ β) (F.base ◁ α) ∙
    (postWhisker G.base ◁ postWhisker-comp₌ F.base β α)

  module Reflect {T : CAT Γ} (s t : Cone f g T) (Φ : ConeIdentification₁ (value s) (value t)) where
    private
      LL-comparison = LiftsLeft.Identifications.LiftIdentification.comparison
        (Cone.left s) (Cone.left t) (ConeIdentification₁.left Φ)
      RR-comparison = LiftsRight.Identifications.LiftIdentification.comparison
        (Cone.right s) (Cone.right t) (ConeIdentification₁.right Φ)
    α = LiftsLeft.Identifications.LiftIdentification.lift (Cone.left s) (Cone.left t) (ConeIdentification₁.left Φ)
    β = LiftsRight.Identifications.LiftIdentification.lift (Cone.right s) (Cone.right t) (ConeIdentification₁.right Φ)
    raw-square = reflect-transported-square
      (left-normal (Cone.left s)) (right-normal (Cone.right s))
      (left-normal (Cone.left t)) (right-normal (Cone.right t)) _ _ _ _ _ _
      (left-natural α) (right-natural β)
      (comp₌-cong ((postWhisker g″ ◁ RR-comparison) ⁻¹) (id₌ (Cone.match (value s))) ∙
        (ConeIdentification₁.compatible Φ ∙ comp₌-cong (id₌ (Cone.match (value t)))
          (postWhisker f″ ◁ LL-comparison)))

    comparison : ConeIdentification₁ s t
    comparison = record { left = α ; right = β
      ; compatible = LiftsBase.Identifications.reflect (f ∘ Cone.left s) (g ∘ Cone.right t) _ _
          ((base-compose (g ◁ β) (Cone.match s)) ⁻¹ ∙
            (raw-square ∙ base-compose (Cone.match t) (f ◁ α))) }

  module LiftCone {T : CAT Γ} (t : Cone f″ g″ T) where
    private
      LL-lift = LiftsLeft.Lift.lift (Cone.left t)
      LL-comparison = LiftsLeft.Lift.comparison (Cone.left t)
      RR-lift = LiftsRight.Lift.lift (Cone.right t)
      RR-comparison = LiftsRight.Lift.comparison (Cone.right t)
    l = left-normal LL-lift
    r = right-normal RR-lift
    α = f″ ◁ LL-comparison
    β = g″ ◁ RR-comparison
    desired = (β ∙ r) ⁻¹ ∙ (Cone.match t ∙ (α ∙ l))
    private
      match-lift = LiftsBase.Identifications.LiftIdentification.lift (f ∘ LL-lift) (g ∘ RR-lift) desired
      match-comparison = LiftsBase.Identifications.LiftIdentification.comparison (f ∘ LL-lift) (g ∘ RR-lift) desired
    lift : Cone f g T
    lift = record { left = LL-lift ; right = RR-lift ; match = match-lift }
    comparison : ConeIdentification₁ (value lift) t
    comparison = record { left = LL-comparison ; right = RR-comparison
      ; compatible = encoded-restriction-square l r α β (Cone.match t)
          (G.base ◁ (F.base ◁ match-lift)) match-comparison }

  module Preserve {S : CAT Γ} (s : Cone f g S) (es : IsPullback s) where
    private
      module Source = UniversalCone s es using (factor; β; reflect)
    target : Cone f″ g″ (Pullback f″ g″)
    target = pullback-cone f″ g″
    private
      target-lift = LiftCone.lift target
      target-comparison = LiftCone.comparison target
    inverse : MAP (Pullback f″ g″) S
    inverse = Source.factor target-lift
    factorization : ConeIdentification₁ (cone-restrict inverse (value s)) target
    factorization = cone-compose target-comparison
      (cone-compose (value-identification (Source.β target-lift))
        (cone-inverse (value-pre inverse s)))
    reflect : (h k : MAP S S) → ConeIdentification₁ (cone-restrict h (value s)) (cone-restrict k (value s)) → h =₁ k
    reflect h k Φ = Source.reflect h k (Reflect.comparison (cone-restrict h s) (cone-restrict k s)
      (cone-compose (cone-inverse (value-pre k s)) (cone-compose Φ (value-pre h s))))
    value-isPullback : IsPullback (value s)
    value-isPullback = isPullback-from-factor-and-reflection (value s) inverse factorization reflect
    map-isPullback : IsPullback (G.map-cone (F.map-cone s))
    map-isPullback = isPullback-cone-identification (cone-inverse (map-comparison s)) value-isPullback

  -- This comparison has the chosen source pullback as its domain.
  -- Universality above applies to arbitrary supplied universal cones.
  pullback-map-comparison : ConeIdentification₁
    (cone-restrict ((pullback-map second) ∘ (pullback-map first)) (pullback-cone f″ g″))
    (G.map-cone (F.map-cone (pullback-cone f g)))
  pullback-map-comparison = cone-compose (GA.map-identification (pullback-map-β first))
    (cone-compose (cone-inverse (GA.map-restrict (pullback-map first) (pullback-cone f′ g′)))
    (cone-compose (cone-identification-restrict-One (pullback-map first) (pullback-map-β second))
      (cone-inverse (cone-restrict-assoc (pullback-map first) (pullback-map second) (pullback-cone f″ g″)))))

  composite-isEquiv : IsEquiv (pullback-map second ∘ pullback-map first)
  composite-isEquiv = equiv-cancel-left composite (pullback-factor target)
    (pullback-cone-isPullback f″ g″)
    (equiv-transport (pullback-factor-restrict composite target)
      (isPullback-cone-identification (cone-inverse pullback-map-comparison)
        (Preserve.map-isPullback (pullback-cone f g) (pullback-cone-isPullback f g))))
    where
    composite = pullback-map second ∘ pullback-map first
    target = pullback-cone f″ g″
```
