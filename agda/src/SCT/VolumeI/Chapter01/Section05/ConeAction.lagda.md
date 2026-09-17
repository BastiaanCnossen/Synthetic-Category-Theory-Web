# A cone acts on isomorphisms of its parameters

The matching square follows from joint interchange, transported through
the associators at both endpoints. The calculation works with an arbitrary
common parameter for the input isomorphisms.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.Setup as Setup
import SCT.VolumeI.Chapter01.Section02.Parameterized as Parameterized
import SCT.VolumeI.Chapter01.Section02.FamilyNaturality as FamilyNaturality
import SCT.VolumeI.Chapter01.Section02.FamilyProductFunctor as FamilyProduct

module SCT.VolumeI.Chapter01.Section05.ConeAction
  {c m a : Level} (𝒯 : Theory c m a) where

open Setup 𝒯
open import SCT.VolumeI.Chapter01.Section05.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section05.ConeComparisonEncoding 𝒯 using (module Encoding)
open Parameterized.WhiskeringLaws vocabulary terminal products productLaws composition vertical whiskering
  using (postWhisker-comp-general)
open FamilyNaturality vocabulary terminal products productLaws composition vertical whiskering
  using (family-move-square; family-interchange-fixedOuter)
open FamilyProduct vocabulary terminal products productLaws composition vertical whiskering
  using (paste-family-squares)

cone-action-family : {A C D E S T : CAT} {f : MAP C E} {g : MAP D E}
  (s : Cone f g T) {h k : MAP S T} (δ : MAP A (h ＝ k))
  → =₁
      (const (Cone.match (conePre k s)) ∙ (f ◁ (Cone.left s ◁ δ)))
      ((g ◁ (Cone.right s ◁ δ)) ∙ const (Cone.match (conePre h s)))
cone-action-family {f = f} {g} s {h} {k} δ =
  paste-family-squares
    (th ∙ invIso ah) (tk ∙ invIso ak) bh bk u v₀ v
    (paste-family-squares (invIso ah) (invIso ak) th tk u u₀ v₀
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

  left-evaluation : =₁ (Boundary.leftMap ∘ postWhisker p)
    (const rightMatch ∙ (f ◁ postWhisker p))
  left-evaluation = isoComp-evaluate (const rightMatch) (postWhisker f) (postWhisker p)
    (const-pre rightMatch (postWhisker p)) (idIso _)

  right-evaluation : =₁ (Boundary.rightMap ∘ postWhisker q)
    ((g ◁ postWhisker q) ∙ const leftMatch)
  right-evaluation = isoComp-evaluate (postWhisker g) (const leftMatch) (postWhisker q)
    (idIso _) (const-pre leftMatch (postWhisker q))

  matching : =₁ (Boundary.leftMap ∘ postWhisker p) (Boundary.rightMap ∘ postWhisker q)
  matching = invIso right-evaluation ∙
    (isoComp-cong (postWhisker g ◁ comp-unitʳ (postWhisker q)) (idIso _) ∙
    (cone-action-family s (id (h ＝ k)) ∙
    (invIso (isoComp-cong (idIso _) (postWhisker f ◁ comp-unitʳ (postWhisker p))) ∙
      left-evaluation)))

  universal : Cone Boundary.leftMap Boundary.rightMap (h ＝ k)
  universal = record { left = postWhisker p ; right = postWhisker q ; match = matching }

cone-action : {C D E S T : CAT} {f : MAP C E} {g : MAP D E}
  (s : Cone f g T) {h k : MAP S T} → =₁ h k → ConeIso (conePre h s) (conePre k s)
cone-action s {h} {k} δ = Action.Boundary.decode s h k (conePre δ (Action.universal s h k))
```

The absolute action specializes this single universal cone. The pullback
comparison uses that same cone, so its computation rule retains precisely
the specified action and matching, without a second normalization route.
