# A cone acts on isomorphisms of its parameters

For a fixed cone, its leg functors act on an isomorphism between maps into
the vertex. The compatibility with the cone's matching follows from
fixed-outer interchange (`family-interchange-fixedOuter`), transported
through the associators at both endpoints. The outer isomorphism is the
fixed cone matching; the input isomorphisms may share an arbitrary parameter.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.Setup as Setup
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Parameterized as Parameterized
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.FamilyNaturality as FamilyNaturality
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.FamilyProductFunctor as FamilyProduct

module SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeAction
  {c m a : Level} (𝒯 : Theory c m a) where

open Setup 𝒯
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeComparisonEncoding 𝒯 using (module Encoding)
open Parameterized.WhiskeringLaws vocabulary terminal products productLaws composition vertical whiskering
  using (postWhisker-comp-general)
open FamilyNaturality vocabulary terminal products productLaws composition vertical whiskering
  using (family-move-square; family-interchange-fixedOuter)
open FamilyProduct vocabulary terminal products productLaws composition vertical whiskering
  using (paste-family-squares)

cone-action-family : {A C D E S T : CAT} {f : MAP C E} {g : MAP D E}
  (s : Cone f g T) {h k : MAP S T} (δ : MAP A (h ＝ k))
  →
      (const (Cone.match (conePre k s)) ∙ (f ◁ (Cone.left s ◁ δ))) =₁
      ((g ◁ (Cone.right s ◁ δ)) ∙ const (Cone.match (conePre h s)))
cone-action-family {f = f} {g} s {h} {k} δ =
  paste-family-squares
    (th ∙ ah ⁻¹) (tk ∙ ak ⁻¹) bh bk u v₀ v
    (paste-family-squares (ah ⁻¹) (ak ⁻¹) th tk u u₀ v₀
      (family-move-square ak u₀ u ah (postWhisker-comp-general δ p f))
      (family-interchange-fixedOuter (Cone.match s) δ))
    (postWhisker-comp-general δ q g)
  where
  p = Cone.left s
  q = Cone.right s
  ah = comp-assoc h p f
  ak = comp-assoc k p f
  bh = comp-assoc h q g
  bk = comp-assoc k q g
  th = Cone.match s ▷ h
  tk = Cone.match s ▷ k
  u = f ◁ (p ◁ δ)
  u₀ = (f ∘ p) ◁ δ
  v₀ = (g ∘ q) ◁ δ
  v = g ◁ (q ◁ δ)

module Action {C D E S T : CAT} {f : MAP C E} {g : MAP D E}
  (s : Cone f g T) (h k : MAP S T) where

  module Boundary = Encoding (conePre h s) (conePre k s)
  leftMatch = Cone.match (conePre h s)
  rightMatch = Cone.match (conePre k s)
  p = Cone.left s
  q = Cone.right s

  left-evaluation : (Boundary.leftMap ∘ postWhisker p) =₁
    (const rightMatch ∙ (f ◁ postWhisker p))
  left-evaluation = isoComp-evaluate (const rightMatch) (postWhisker f) (postWhisker p)
    (const-pre rightMatch (postWhisker p)) (idIso _)

  right-evaluation : (Boundary.rightMap ∘ postWhisker q) =₁
    ((g ◁ postWhisker q) ∙ const leftMatch)
  right-evaluation = isoComp-evaluate (postWhisker g) (const leftMatch) (postWhisker q)
    (idIso _) (const-pre leftMatch (postWhisker q))

  matching : (Boundary.leftMap ∘ postWhisker p) =₁ (Boundary.rightMap ∘ postWhisker q)
  matching = right-evaluation ⁻¹ ∙
    (isoComp-cong (postWhisker g ◁ comp-unitʳ (postWhisker q)) (idIso _) ∙
    (cone-action-family s (id (h ＝ k)) ∙
    ((isoComp-cong (idIso _) (postWhisker f ◁ comp-unitʳ (postWhisker p))) ⁻¹ ∙
      left-evaluation)))

  universal : Cone Boundary.leftMap Boundary.rightMap (h ＝ k)
  universal = record { left = postWhisker p ; right = postWhisker q ; match = matching }

cone-action : {C D E S T : CAT} {f : MAP C E} {g : MAP D E}
  (s : Cone f g T) {h k : MAP S T} → h =₁ k → ConeIso (conePre h s) (conePre k s)
cone-action s {h} {k} δ = Action.Boundary.decode s h k (conePre δ (Action.universal s h k))
```

The absolute action specializes this single universal cone. The pullback
comparison uses that same cone, so its computation rule retains precisely
the specified action and matching, without a second normalization route.
