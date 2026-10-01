# Restriction and extension of cones

Restricting a cone along the pair functor transports its matching as
well as its legs. Conversely, extension of the legs and reflection of
the matching extend a local cone on a weakened absolute cospan. The
computation below compares whole cones, including their matchings.

This is a consequence of the sum universal property. It does not assert
that extension preserves pullbacks. The final construction applies it
to the cospan comparison given by the pair functors, producing a cone
whose legs are the specified dependent sums of the original legs.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core using (Weakening)
open import SCT.VolumeI.Chapter05.Section01.Coherence using (OperationCompatibility)
import SCT.VolumeI.Chapter05.Section02.DependentProducts as Products
import SCT.VolumeI.Chapter05.Section02.DependentSums as Sums
import SCT.VolumeI.Chapter05.Section02.SumFunctoriality as Action
import SCT.VolumeI.Chapter05.Section02.MappingCalculus.SumIdentifications as Identifications
import SCT.VolumeI.Chapter05.Section02.MappingCalculus.SumPostcomposition as Post
import SCT.VolumeI.Chapter05.Section02.ProductCalculus.ProductPostcomposition as Pasting
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Calculus as Calculus
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.ConeTransport as Transport
import SCT.VolumeI.Chapter01.Section06.Cones as Cones
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section06.PullbackFunctor as Functor
import SCT.VolumeI.Chapter01.Section06.ConeCalculus.Comparisons as Comparisons
import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeSymmetry as Symmetry
import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus as Inverses
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as Pairing
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.BoundaryTransport as Boundary
import SCT.VolumeI.Chapter05.Section02.ConeCalculus.TransportedSquares as Squares

module SCT.VolumeI.Chapter05.Section02.SumCones
  {l : Level} {S T : Theory l l l} (W : Weakening S T)
  (K : OperationCompatibility W) (P : Products.DependentProducts W)
  (Q : Sums.DependentSums W P) where

private
  module S = View S
  module T = View T
module W = Weakening W
module SC = Cones S
module TC = Cones T
open Sums.DependentSums Q using (Σ; pair; flatten; extend; extend-β)
open Action W P Q using (Σ-map; Σ-map-β; flatten-post; reflect)
open Identifications W K P Q using (action; action₂; action-comp; reflect-β; reflect₂)
open Post W K P Q using (naturality)
open Pasting W K P using (paste)
open T using (_∘_; _∙_; _◁_; _▷_; _⁻¹)
open Calculus T
open Pairing T.vocabulary T.terminal T.products T.productLaws T.composition T.vertical T.whiskering
  using (move-square)
open Boundary T.vocabulary T.terminal T.products T.productLaws T.composition T.vertical
  using (restore-boundaries)
open Comparisons T using (coneRetarget; coneRetarget-β; coneIso-compose; coneIso-inverse; coneIso-adjust)
open Symmetry T using (cone-match-change)
open Squares T using (reflect-transported-square)
open Inverses T using (inverse-composite; isoInverse-unique)

restrictCone : {B : T.CAT} {C D E : S.CAT} {f : S.MAP C E} {g : S.MAP D E}
  → SC.Cone f g (Σ B) → TC.Cone (W.map f) (W.map g) B
restrictCone {f = f} {g} s = record
  { left = flatten (SC.Cone.left s) ; right = flatten (SC.Cone.right s)
  ; match = flatten-post g (SC.Cone.right s) ∙
      (action (SC.Cone.match s) ∙ (flatten-post f (SC.Cone.left s)) ⁻¹) }

module RestrictionComparison {B : T.CAT} {C D E : S.CAT} {f : S.MAP C E} {g : S.MAP D E}
  (s : SC.Cone f g (Σ B)) where

  module CT = Transport W K using (cone)
  private
    p = SC.Cone.left s
    q = SC.Cone.right s
    η = pair B
    a = T.comp-assoc η (W.map p) (W.map f)
    b = T.comp-assoc η (W.map q) (W.map g)
    c = W.comp p f ▷ η
    d = W.comp q g ▷ η
    τ = action (SC.Cone.match s)

    inverse-image : T._=₂_ ((W.comp p f) ⁻¹ ▷ η) (c ⁻¹)
    inverse-image = (isoInverse-unique c ((W.comp p f) ⁻¹ ▷ η)
      ((preWhisker-isoComp-at ((W.comp p f) ⁻¹) (W.comp p f) η) ⁻¹ then
        (T.preWhisker η ◁ isoComp-inverseˡ-at (W.comp p f)) then
        T.preWhisker-idIso (W.map (S._∘_ f p)) η)) ⁻¹

    transported-match : T._=₂_ (TC.Cone.match (CT.cone s) ▷ η) (d ∙ (τ ∙ c ⁻¹))
    transported-match = preWhisker-isoComp-at (W.comp q g)
        (W.term (SC.Cone.match s) ∙ (W.comp p f) ⁻¹) η then
      isoComp-cong (T.idIso d)
        (preWhisker-isoComp-at (W.term (SC.Cone.match s)) ((W.comp p f) ⁻¹) η then
          isoComp-cong (T.idIso τ) inverse-image)

  matching : T._=₂_ (TC.Cone.match (restrictCone s))
    (TC.Cone.match (TC.conePre η (CT.cone s)))
  matching = isoComp-cong (T.idIso (b ∙ d))
      (isoComp-cong (T.idIso τ) (inverse-composite a c)) then
    isoComp-assoc-at b d (τ ∙ (c ⁻¹ ∙ a ⁻¹)) then
    isoComp-cong (T.idIso b)
      (isoComp-cong (T.idIso d) ((isoComp-assoc-at τ (c ⁻¹) (a ⁻¹)) ⁻¹) then
        (isoComp-assoc-at d (τ ∙ c ⁻¹) (a ⁻¹)) ⁻¹ then
        isoComp-cong (transported-match ⁻¹) (T.idIso (a ⁻¹)))

  comparison : TC.ConeIso (restrictCone s) (TC.conePre (pair B) (CT.cone s))
  comparison = cone-match-change _ _ _ _ matching

restrictConeIso : {B : T.CAT} {C D E : S.CAT} {f : S.MAP C E} {g : S.MAP D E}
  {s t : SC.Cone f g (Σ B)}
  → SC.ConeIso s t → TC.ConeIso (restrictCone s) (restrictCone t)
restrictConeIso {f = f} {g} {s} {t} Φ = record
  { leftIso = action α ; rightIso = action β
  ; compatible = paste (τs ∙ fs ⁻¹) (τt ∙ ft ⁻¹) gs gt first third last
      (paste (fs ⁻¹) (ft ⁻¹) τs τt first second third
        (move-square ft second first fs (naturality f α)) rawSquare)
      (naturality g β) }
  where
  α = SC.ConeIso.leftIso Φ
  β = SC.ConeIso.rightIso Φ
  fs = flatten-post f (SC.Cone.left s)
  ft = flatten-post f (SC.Cone.left t)
  gs = flatten-post g (SC.Cone.right s)
  gt = flatten-post g (SC.Cone.right t)
  τs = action (SC.Cone.match s)
  τt = action (SC.Cone.match t)
  first = W.map f ◁ action α
  second = action (S._◁_ f α)
  third = action (S._◁_ g β)
  last = W.map g ◁ action β
  rawSquare = (action-comp (SC.Cone.match t) (S._◁_ f α)) ⁻¹ then
    action₂ (SC.ConeIso.compatible Φ) then
    action-comp (S._◁_ g β) (SC.Cone.match s)

module Reflection {B : T.CAT} {C D E : S.CAT} {f : S.MAP C E} {g : S.MAP D E}
  (s t : SC.Cone f g (Σ B))
  (Φ : TC.ConeIso (restrictCone s) (restrictCone t)) where

  left = reflect (TC.ConeIso.leftIso Φ)
  right = reflect (TC.ConeIso.rightIso Φ)
  adjusted = coneIso-adjust Φ (action left) (action right)
    ((reflect-β (TC.ConeIso.leftIso Φ)) ⁻¹)
    ((reflect-β (TC.ConeIso.rightIso Φ)) ⁻¹)
  fs = flatten-post f (SC.Cone.left s)
  ft = flatten-post f (SC.Cone.left t)
  gs = flatten-post g (SC.Cone.right s)
  gt = flatten-post g (SC.Cone.right t)
  τs = action (SC.Cone.match s)
  τt = action (SC.Cone.match t)
  α = action (S._◁_ f left)
  β = action (S._◁_ g right)

  rawSquare : T._=₂_ (τt ∙ α) (β ∙ τs)
  rawSquare = reflect-transported-square fs gs ft gt τs τt
    α β (W.map f ◁ action left) (W.map g ◁ action right)
    (naturality f left) (naturality g right) (TC.ConeIso.compatible adjusted)

  comparison : SC.ConeIso s t
  comparison = record
    { leftIso = left ; rightIso = right
    ; compatible = reflect₂
        ((action-comp (S._◁_ g right) (SC.Cone.match s)) ⁻¹ ∙
          (rawSquare ∙ action-comp (SC.Cone.match t) (S._◁_ f left))) }

module Extension {B : T.CAT} {C D E : S.CAT} {f : S.MAP C E} {g : S.MAP D E}
  (s : TC.Cone (W.map f) (W.map g) B) where

  left = extend (TC.Cone.left s)
  right = extend (TC.Cone.right s)
  wanted = coneRetarget s (flatten left) (flatten right)
    (extend-β (TC.Cone.left s)) (extend-β (TC.Cone.right s))
  desired = TC.Cone.match wanted
  leftChange = flatten-post f left
  rightChange = flatten-post g right
  rawMatch = rightChange ⁻¹ ∙ (desired ∙ leftChange)

  value : SC.Cone f g (Σ B)
  value = record { left = left ; right = right ; match = reflect rawMatch }

  match-β : T._=₂_ (TC.Cone.match (restrictCone value)) desired
  match-β = restore-boundaries leftChange rightChange desired
    (action (SC.Cone.match value))
    (reflect-β rawMatch)

  abstract
    comparison : TC.ConeIso (restrictCone value) s
    comparison = coneIso-compose
      (coneIso-inverse (coneRetarget-β s _ _
        (extend-β (TC.Cone.left s)) (extend-β (TC.Cone.right s))))
      (cone-match-change _ _ _ _ match-β)

module Total (PT : Pullbacks.PullbackStructure T)
  {B C D Z : T.CAT} {f : T.MAP B D} {g : T.MAP C D}
  (s : TC.Cone f g Z) where

  open Functor T PT using (CospanMap)

  cospan : CospanMap f g (W.map (Σ-map f)) (W.map (Σ-map g))
  cospan = record
    { left = pair B ; right = pair C ; base = pair D
    ; leftSquare = (Σ-map-β f) ⁻¹ ; rightSquare = (Σ-map-β g) ⁻¹ }

  pairCone : TC.Cone (W.map (Σ-map f)) (W.map (Σ-map g)) Z
  pairCone = CospanMap.mapCone cospan s

  module Extended = Extension pairCone using (value; comparison)

  cone : SC.Cone (Σ-map f) (Σ-map g) (Σ Z)
  cone = Extended.value

  pair-comparison : TC.ConeIso (restrictCone cone) pairCone
  pair-comparison = Extended.comparison
```
