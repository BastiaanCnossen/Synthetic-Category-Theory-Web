# Transporting the anima of cone comparisons

Changing either cone by a specified cone comparison gives an equivalence
between the pullbacks that encode their comparisons. The two cospan squares
use the compatibility witnesses of the supplied cone comparisons. This does
not identify independently chosen interchange witnesses.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.Setup as Setup
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter01.Section03.Parameterized as Parameterized
import SCT.VolumeI.Chapter01.Section03.FamilyPairing as FamilyPairing
import SCT.VolumeI.Chapter01.Section03.FamilyNaturality as Naturality
import SCT.VolumeI.Chapter01.Section03.Whiskering as Multiplication
import SCT.VolumeI.Chapter01.Section03.PairingNaturality as Squares

module SCT.VolumeI.Chapter01.Section06.ConeIdentificationTransport
  {c m a : Level} (𝒯 : Theory c m a) (P : Laws.PullbackStructure 𝒯) where

open Setup 𝒯
open Laws.PullbackStructure P
open Parameterized vocabulary terminal products productLaws composition vertical
open FamilyPairing vocabulary terminal products productLaws composition vertical whiskering
  using (post-composition)
open Naturality vocabulary terminal products productLaws composition vertical whiskering
  using (post-const)
open Multiplication vocabulary terminal products productLaws composition vertical whiskering
  using (leftMultiply; rightMultiply; leftMultiply-isEquiv; rightMultiply-isEquiv;
         left-evaluate; right-evaluate)
open Squares vocabulary terminal products productLaws composition vertical whiskering
  using (move-square)
open import SCT.VolumeI.Chapter01.Section04.ProjectionSquares 𝒯 using (post-inverse)
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeComparisonEncoding 𝒯 using (module Encoding)
open import SCT.VolumeI.Chapter01.Section06.PullbackFunctor 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.CospanEquivalences 𝒯 P

module Conjugation {X Y : CAT} {x x′ y y′ : MAP X Y}
  (α : x =₁ x′) (β : y =₁ y′) where

  family : {A : CAT} → MAP A (x ＝ y) → MAP A (x′ ＝ y′)
  family u = const β ∙ (u ∙ const (α ⁻¹))

  forward : MAP (x ＝ y) (x′ ＝ y′)
  forward = leftMultiply β ∘ rightMultiply (α ⁻¹)

  isEquiv : IsEquiv forward
  isEquiv = equiv-compose (rightMultiply (α ⁻¹)) (leftMultiply β)
    (rightMultiply-isEquiv (α ⁻¹)) (leftMultiply-isEquiv β)

  evaluate : {A : CAT} (u : MAP A (x ＝ y)) → (forward ∘ u) =₁ (family u)
  evaluate u = isoComp-cong (idIso (const β)) (right-evaluate (α ⁻¹) u) ∙
    (left-evaluate β (rightMultiply (α ⁻¹) ∘ u) ∙
      comp-assoc u (rightMultiply (α ⁻¹)) (leftMultiply β))

post-conjugation : {A X Y Z : CAT} {x x′ y y′ : MAP X Y}
  (F : MAP Y Z) (α : x =₁ x′) (β : y =₁ y′) (u : MAP A (x ＝ y)) →
  (F ◁ Conjugation.family α β u) =₁
    (Conjugation.family (F ◁ α) (F ◁ β) (F ◁ u))
post-conjugation F α β u =
  isoComp-cong (post-const F β)
    (isoComp-cong (idIso (F ◁ u))
      (const-cong (post-inverse F α) ∙ post-const F (α ⁻¹)) ∙
      post-composition F u (const (α ⁻¹))) ∙
    post-composition F (const β) (u ∙ const (α ⁻¹))

module Transport {C D E T : CAT} {f : MAP C E} {g : MAP D E}
  {s s′ t t′ : Cone f g T} (Φ : ConeIso s s′) (Ψ : ConeIso t t′) where

  module Before = Encoding s t
  module After = Encoding s′ t′
  α = ConeIso.leftIso Φ
  β = ConeIso.leftIso Ψ
  γ = ConeIso.rightIso Φ
  δ = ConeIso.rightIso Ψ
  τ = Cone.match s
  υ = Cone.match t
  τ′ = Cone.match s′
  υ′ = Cone.match t′

  module Left = Conjugation α β
  module Right = Conjugation γ δ
  module Middle = Conjugation (f ◁ α) (g ◁ δ)

  boundary-left-evaluate : {A : CAT} (u : MAP A Before.Left) →
    (Before.leftMap ∘ u) =₁ (const υ ∙ (f ◁ u))
  boundary-left-evaluate u = isoComp-evaluate (const υ) (postWhisker f) u
    (const-pre υ u) (idIso _)

  boundary-right-evaluate : {A : CAT} (v : MAP A Before.Right) →
    (Before.rightMap ∘ v) =₁ ((g ◁ v) ∙ const τ)
  boundary-right-evaluate v = isoComp-evaluate (postWhisker g) (const τ) v
    (idIso _) (const-pre τ v)

  module LeftSquare where
    u = id Before.Left
    F = f ◁ u
    A = const {P = Before.Left} ((f ◁ α) ⁻¹)
    B = const {P = Before.Left} (f ◁ β)
    δ-family = const {P = Before.Left} (g ◁ δ)
    V = const {P = Before.Left} υ
    V′ = const {P = Before.Left} υ′

    source-normal : Before.leftMap =₁ (V ∙ F)
    source-normal = boundary-left-evaluate u ∙ (comp-unitʳ Before.leftMap) ⁻¹

    expanded : (After.leftMap ∘ Left.forward) =₁ (V′ ∙ (B ∙ (F ∙ A)))
    expanded = isoComp-cong (idIso V′)
      (post-conjugation f α β u ∙
        (postWhisker f ◁ (Left.evaluate u ∙ (comp-unitʳ Left.forward) ⁻¹))) ∙
      isoComp-evaluate (const υ′) (postWhisker f) Left.forward
        (const-pre υ′ Left.forward) (idIso _)

    compatibility : (V′ ∙ B) =₁ (δ-family ∙ V)
    compatibility = (const-comp (g ◁ δ) υ) ⁻¹ ∙
      (const-cong (ConeIso.compatible Ψ) ∙ const-comp υ′ (f ◁ β))

    normalized : (V′ ∙ (B ∙ (F ∙ A))) =₁ (δ-family ∙ ((V ∙ F) ∙ A))
    normalized = isoComp-cong (idIso δ-family) ((assoc V F A) ⁻¹) ∙
      (assoc δ-family V (F ∙ A) ∙
        (isoComp-cong compatibility (idIso (F ∙ A)) ∙ (assoc V′ B (F ∙ A)) ⁻¹))


  opaque
    left-square : (After.leftMap ∘ Left.forward) =₁ (Middle.forward ∘ Before.leftMap)
    left-square = (Middle.evaluate Before.leftMap) ⁻¹ ∙
      (isoComp-cong (idIso (const {P = Before.Left} (g ◁ δ)))
        (isoComp-cong (LeftSquare.source-normal ⁻¹) (idIso (const {P = Before.Left} ((f ◁ α) ⁻¹)))) ∙
        (LeftSquare.normalized ∙ LeftSquare.expanded))


  module RightSquare where
    v = id Before.Right
    G = g ◁ v
    A = const {P = Before.Right} ((f ◁ α) ⁻¹)
    γ-inverse = const {P = Before.Right} ((g ◁ γ) ⁻¹)
    δ-family = const {P = Before.Right} (g ◁ δ)
    U = const {P = Before.Right} τ
    U′ = const {P = Before.Right} τ′

    source-normal : Before.rightMap =₁ (G ∙ U)
    source-normal = boundary-right-evaluate v ∙ (comp-unitʳ Before.rightMap) ⁻¹

    expanded : (After.rightMap ∘ Right.forward) =₁ ((δ-family ∙ (G ∙ γ-inverse)) ∙ U′)
    expanded = isoComp-cong
      (post-conjugation g γ δ v ∙
        (postWhisker g ◁ (Right.evaluate v ∙ (comp-unitʳ Right.forward) ⁻¹))) (idIso U′) ∙
      isoComp-evaluate (postWhisker g) (const τ′) Right.forward
        (idIso _) (const-pre τ′ Right.forward)

    compatibility : (γ-inverse ∙ U′) =₁ (U ∙ A)
    compatibility = (const-comp τ ((f ◁ α) ⁻¹)) ⁻¹ ∙
      (const-cong (move-square (g ◁ γ) τ τ′ (f ◁ α)
        ((ConeIso.compatible Φ) ⁻¹)) ∙ const-comp ((g ◁ γ) ⁻¹) τ′)

    normalized : ((δ-family ∙ (G ∙ γ-inverse)) ∙ U′) =₁ (δ-family ∙ ((G ∙ U) ∙ A))
    normalized = isoComp-cong (idIso δ-family)
      ((assoc G U A) ⁻¹ ∙ (isoComp-cong (idIso G) compatibility ∙ assoc G γ-inverse U′)) ∙
      assoc δ-family (G ∙ γ-inverse) U′


  opaque
    right-square : (After.rightMap ∘ Right.forward) =₁ (Middle.forward ∘ Before.rightMap)
    right-square = (Middle.evaluate Before.rightMap) ⁻¹ ∙
      (isoComp-cong (idIso (const {P = Before.Right} (g ◁ δ)))
        (isoComp-cong (RightSquare.source-normal ⁻¹) (idIso (const {P = Before.Right} ((f ◁ α) ⁻¹)))) ∙
        (RightSquare.normalized ∙ RightSquare.expanded))


  cospan : CospanMap Before.leftMap Before.rightMap After.leftMap After.rightMap
  cospan = record
    { left = Left.forward ; right = Right.forward ; base = Middle.forward
    ; leftSquare = left-square ; rightSquare = right-square }

  open CospanMap cospan public using (mapCone)

  abstract
    pullbackMap : MAP (Pullback Before.leftMap Before.rightMap)
      (Pullback After.leftMap After.rightMap)
    pullbackMap = CospanMap.pullbackMap cospan

    pullbackMap-β : ConeIso
      (conePre pullbackMap (pullbackCone After.leftMap After.rightMap))
      (mapCone (pullbackCone Before.leftMap Before.rightMap))
    pullbackMap-β = CospanMap.pullbackMap-β cospan

    left-projection :
      (pullback₁ {f = After.leftMap} {g = After.rightMap} ∘ pullbackMap) =₁
      (Left.forward ∘ pullback₁ {f = Before.leftMap} {g = Before.rightMap})
    left-projection = ConeIso.leftIso pullbackMap-β

    right-projection :
      (pullback₂ {f = After.leftMap} {g = After.rightMap} ∘ pullbackMap) =₁
      (Right.forward ∘ pullback₂ {f = Before.leftMap} {g = Before.rightMap})
    right-projection = ConeIso.rightIso pullbackMap-β

    equivalence : IsEquiv pullbackMap
    equivalence = CospanEquivalence.pullbackMap-isEquiv cospan Left.isEquiv Right.isEquiv Middle.isEquiv
```
