# Restriction of uncurried cones

Uncurrying is the composite of transport by weakening and the action of
the evaluation cospan. We compare the specified matchings, then use
restriction for maps of cospans. No extra condition on the product
universal property is needed.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core using (Weakening)
open import SCT.VolumeI.Chapter05.Section01.Coherence using (OperationCompatibility)
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.ConeTransport as Transport
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Calculus as Calculus
import SCT.VolumeI.Chapter05.Section02.DependentProducts as Products
import SCT.VolumeI.Chapter05.Section02.ProductFunctoriality as Action
import SCT.VolumeI.Chapter05.Section02.ProductCalculus.ProductCones as ProductCones
import SCT.VolumeI.Chapter05.Section02.ProductCalculus.ProductPostcomposition as Post
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section06.PullbackFunctor as Functor
import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeRestriction as Restriction
import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeSymmetry as Symmetry
import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus as Inverses
import SCT.VolumeI.Chapter01.Section06.ConeCalculus.CospanAction as CospanAction
import SCT.VolumeI.Chapter01.Section06.ConeCalculus.CospanRestriction as CospanRestriction

module SCT.VolumeI.Chapter05.Section02.ProductCalculus.ProductConeRestriction
  {l : Level} {S T : Theory l l l} (W : Weakening S T)
  (K : OperationCompatibility W) (P : Products.DependentProducts W)
  (PT : Pullbacks.PullbackStructure T) where

private
  module S = View S
  module T = View T
module W = Weakening W
module CT = Transport W K using (cone; restrict)
open Products.DependentProducts P using (Π; evaluation)
open Action W P using (Π-map; Π-map-β; uncurry-pre)
open ProductCones W K P using (module SC; module TC; uncurryCone)
open Post W K P using () renaming (comparison to post)
open T using (_∘_; _∙_; _◁_; _▷_; _⁻¹)
open Calculus T
open Inverses T using (inverse-composite; inverse-inverse; isoInverse-unique)
open Functor T PT using (CospanMap)
open Restriction T using (coneIso-compose; coneIso-inverse; coneIso-pre)
open Symmetry T using (cone-match-change)

post-inverse : {B C D : T.CAT} (h : T.MAP C D) {f g : T.MAP B C} (α : T._=₁_ f g)
  → T._=₂_ (h ◁ (α ⁻¹)) ((h ◁ α) ⁻¹)
post-inverse h {f} α = (isoInverse-unique (h ◁ α) (h ◁ (α ⁻¹))
  ((postWhisker-isoComp-at h (α ⁻¹) α) ⁻¹ then
    (T.postWhisker h ◁ isoComp-inverseˡ-at α) then T.postWhisker-idIso h f)) ⁻¹

evaluation-cospan : {B C D : T.CAT} (f : T.MAP B D) (g : T.MAP C D)
  → CospanMap (W.map (Π-map f)) (W.map (Π-map g)) f g
evaluation-cospan {B} {C} {D} f g = record
  { left = evaluation B ; right = evaluation C ; base = evaluation D
  ; leftSquare = Π-map-β f ; rightSquare = Π-map-β g }

module Comparison {X : S.CAT} {B C D : T.CAT} {f : T.MAP B D} {g : T.MAP C D}
  (s : SC.Cone (Π-map f) (Π-map g) X) where

  module E = CospanMap (evaluation-cospan f g) using (mapCone)
  module CA = CospanAction.Action T PT (evaluation-cospan f g)
    using (normalized; left-change; right-change; module Normalization)
  source = CT.cone s
  p = SC.Cone.left s
  q = SC.Cone.right s
  e = evaluation D
  a = e ◁ W.comp p (Π-map f)
  b = e ◁ W.comp q (Π-map g)
  τ = e ◁ W.term (SC.Cone.match s)
  L = CA.left-change source
  R = CA.right-change source

  post-normal : {B : T.CAT} (f : T.MAP B D) (p : S.MAP X (Π B))
    → T._=₂_ (post f p)
      ((TC.Cone.match (TC.conePre (W.map p)
        (record { left = evaluation B ; right = W.map (Π-map f) ; match = Π-map-β f }))) ⁻¹ ∙
        (e ◁ W.comp p (Π-map f)))
  post-normal f p = (isoComp-cong inverse-change (T.idIso z) then
    isoComp-assoc-at ar (br ∙ cr) z then
    isoComp-cong (T.idIso ar) (isoComp-assoc-at br cr z)) ⁻¹
    where
    ar = T.comp-assoc (W.map p) (evaluation _) f
    br = (Π-map-β f) ⁻¹ ▷ W.map p
    cr = (T.comp-assoc (W.map p) (W.map (Π-map f)) e) ⁻¹
    z = e ◁ W.comp p (Π-map f)
    module Self = CospanAction.Action T PT (evaluation-cospan f f)
    self-source : TC.Cone (W.map (Π-map f)) (W.map (Π-map f)) (W.cat X)
    self-source = record { left = W.map p ; right = W.map p ; match = T.idIso _ }
    inverse-change = Self.Normalization.inverse-right self-source

  transported-match : T._=₂_ (e ◁ TC.Cone.match source) (b ∙ (τ ∙ a ⁻¹))
  transported-match = postWhisker-isoComp-at e (W.comp q (Π-map g))
      (W.term (SC.Cone.match s) ∙ (W.comp p (Π-map f)) ⁻¹) then
    isoComp-cong (T.idIso b)
      (postWhisker-isoComp-at e (W.term (SC.Cone.match s)) ((W.comp p (Π-map f)) ⁻¹) then
       isoComp-cong (T.idIso τ) (post-inverse e (W.comp p (Π-map f))))

  matching : T._=₂_ (TC.Cone.match (uncurryCone s)) (TC.Cone.match (CA.normalized source))
  matching = isoComp-cong (post-normal g q)
      (isoComp-cong (T.idIso τ) (T.＝-inv ◁ post-normal f p)) then
    isoComp-cong (T.idIso (R ⁻¹ ∙ b))
      (isoComp-cong (T.idIso τ)
        (inverse-composite (L ⁻¹) a then isoComp-cong (T.idIso (a ⁻¹)) (inverse-inverse L))) then
    isoComp-assoc-at (R ⁻¹) b (τ ∙ (a ⁻¹ ∙ L)) then
    isoComp-cong (T.idIso (R ⁻¹))
      (isoComp-cong (T.idIso b) ((isoComp-assoc-at τ (a ⁻¹) L) ⁻¹) then
       (isoComp-assoc-at b (τ ∙ a ⁻¹) L) ⁻¹ then
       isoComp-cong (transported-match ⁻¹) (T.idIso L))

  comparison : TC.ConeIso (uncurryCone s) (E.mapCone source)
  comparison = coneIso-compose (CA.Normalization.comparison source)
    (cone-match-change _ _ _ _ matching)

restrict : {X Y : S.CAT} {B C D : T.CAT} {f : T.MAP B D} {g : T.MAP C D}
  (h : S.MAP X Y) (s : SC.Cone (Π-map f) (Π-map g) Y)
  → TC.ConeIso (uncurryCone (SC.conePre h s)) (TC.conePre (W.map h) (uncurryCone s))
restrict {f = f} {g} h s = coneIso-compose
  (coneIso-inverse (coneIso-pre (W.map h) (Comparison.comparison s)))
  (coneIso-compose
    (coneIso-inverse (CospanRestriction.Restriction.comparison T PT cospan (W.map h) (CT.cone s)))
    (coneIso-compose
      (CospanAction.Action.Identification.comparison T PT cospan (CT.restrict h s))
      (Comparison.comparison (SC.conePre h s))))
  where cospan = evaluation-cospan f g
```
