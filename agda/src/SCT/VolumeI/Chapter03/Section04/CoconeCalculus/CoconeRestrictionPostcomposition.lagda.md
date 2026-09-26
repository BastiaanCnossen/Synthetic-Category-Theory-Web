# Postcomposition commutes with cocone restriction

The leg comparisons are the ordinary associators. Their compatibility
uses the previously proved coordinate associativity law, followed by
naturality of mixed whiskering. Thus the comparison retains the full
matching when a restricted cocone is postcomposed.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural
import SCT.VolumeI.Chapter01.Section02.Isomorphisms as Isomorphisms

module SCT.VolumeI.Chapter03.Section04.CoconeCalculus.CoconeRestrictionPostcomposition
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section08.Cocones 𝒯
open import SCT.VolumeI.Chapter01.Section08.CoconeCalculus.CoconePostcomposition 𝒯 using (coconePost)
open import SCT.VolumeI.Chapter01.Section04.ProductCalculus.ProductSubstitution 𝒯 M using (coordinate-outer-comp)
open import SCT.VolumeI.Chapter01.Section04.SquareCalculus.ProjectionSquares 𝒯 using (post-inverse)
open import SCT.VolumeI.Chapter03.Section04.CoconeCalculus.CoconeSpanRestriction 𝒯 using (module Bridge; module Restriction)
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-left; move-square)
open Structural vocabulary terminal products productLaws composition whiskering using (whisker-mixed-at)
open Isomorphisms vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)

module BridgePost {A B A′ B′ D E : CAT} (u : MAP A B) (u′ : MAP A′ B′)
  (i : MAP A A′) (j : MAP B B′) (α : (u′ ∘ i) =₁ (j ∘ u))
  (p : MAP B′ D) (F : MAP D E) where
  module B = Bridge u u′ i j α
  first = comp-assoc u (p ∘ j) F
  last = comp-assoc i (p ∘ u′) F
  δ = comp-assoc j p F ▷ u
  ν = comp-assoc u′ p F ▷ i
  start = first ∙ δ
  finish = last ∙ ν

  abstract
    comparison : (finish ∙ B.value (F ∘ p)) =₂ ((F ◁ B.value p) ∙ start)
    comparison = isoComp-assoc-at (F ◁ B.value p) first δ ∙
      (isoComp-cong (cancel-inverse last ((F ◁ B.value p) ∙ first)) (idIso δ) ∙
        ((isoComp-assoc-at last ((last ⁻¹) ∙ ((F ◁ B.value p) ∙ first)) δ) ⁻¹ ∙
          (isoComp-cong (idIso last) (coordinate-outer-comp i u′ j u (α ⁻¹) p F) ∙
            isoComp-assoc-at last ν (B.value (F ∘ p)))))

module Post {A B C A′ B′ C′ D E : CAT}
  (u : MAP A B) (v : MAP A C) (u′ : MAP A′ B′) (v′ : MAP A′ C′)
  (i : MAP A A′) (j : MAP B B′) (k : MAP C C′)
  (α : (u′ ∘ i) =₁ (j ∘ u)) (β : (v′ ∘ i) =₁ (k ∘ v))
  (s : Cocone u′ v′ D) (F : MAP D E) where
  module Restrict = Restriction u v u′ v′ i j k α β
  p = Cocone.left s
  q = Cocone.right s
  σ = Cocone.match s
  module Left = BridgePost u u′ i j α p F
  module Right = BridgePost v v′ i k β q F
  source = Restrict.value (coconePost F s)
  target = coconePost F (Restrict.value s)
  L = Restrict.Left.value p
  R = Restrict.Right.value q
  L′ = Restrict.Left.value (F ∘ p)
  R′ = Restrict.Right.value (F ∘ q)
  τ = Cocone.match (coconePost F s)
  δ = comp-assoc j p F
  ε = comp-assoc k q F
  Au = comp-assoc u′ p F
  Av = comp-assoc v′ q F
  Ai = comp-assoc i (p ∘ u′) F
  Aj = comp-assoc i (q ∘ v′) F
  factored = ((F ◁ R) ⁻¹) ∙ ((F ◁ (σ ▷ i)) ∙ (F ◁ L))
  image = F ◁ Cocone.match (Restrict.value s)

  abstract
    cancel-corner : (Av ∙ τ) =₂ ((F ◁ σ) ∙ Au)
    cancel-corner = cancel-inverse Av ((F ◁ σ) ∙ Au)

    restricted-corner : ((Av ▷ i) ∙ (τ ▷ i)) =₂ (((F ◁ σ) ▷ i) ∙ (Au ▷ i))
    restricted-corner = preWhisker-isoComp-at (F ◁ σ) Au i ∙
      ((preWhisker i ◁ cancel-corner) ∙ (preWhisker-isoComp-at Av τ i) ⁻¹)

    middle : ((F ◁ (σ ▷ i)) ∙ Left.finish) =₂ (Right.finish ∙ (τ ▷ i))
    middle = (isoComp-assoc-at Aj (Av ▷ i) (τ ▷ i)) ⁻¹ ∙
      (isoComp-cong (idIso Aj) (restricted-corner ⁻¹) ∙
        (isoComp-assoc-at Aj ((F ◁ σ) ▷ i) (Au ▷ i) ∙
          (isoComp-cong ((whisker-mixed-at σ i F) ⁻¹) (idIso (Au ▷ i)) ∙
            (isoComp-assoc-at (F ◁ (σ ▷ i)) Ai (Au ▷ i)) ⁻¹)))

    raw-square : (factored ∙ Left.start) =₂ (Right.start ∙ Cocone.match source)
    raw-square = paste-squares
      ((τ ▷ i) ∙ L′) ((F ◁ (σ ▷ i)) ∙ (F ◁ L)) (R′ ⁻¹) ((F ◁ R) ⁻¹)
      Left.start Right.finish Right.start
      (paste-squares L′ (F ◁ L) (τ ▷ i) (F ◁ (σ ▷ i))
        Left.start Left.finish Right.finish (Left.comparison ⁻¹) middle)
      (move-square (F ◁ R) Right.start Right.finish R′ (Right.comparison ⁻¹))

    merge : factored =₂ image
    merge = (postWhisker-isoComp-at F (R ⁻¹) ((σ ▷ i) ∙ L)) ⁻¹ ∙
      isoComp-cong ((post-inverse F R) ⁻¹) ((postWhisker-isoComp-at F (σ ▷ i) L) ⁻¹)

    matching : (Cocone.match target ∙ (δ ▷ u)) =₂ ((ε ▷ v) ∙ Cocone.match source)
    matching = cancel-left Right.first ((ε ▷ v) ∙ Cocone.match source) ∙
      (isoComp-cong (idIso (Right.first ⁻¹))
        (isoComp-assoc-at Right.first (ε ▷ v) (Cocone.match source) ∙
          (raw-square ∙ isoComp-cong (merge ⁻¹) (idIso Left.start))) ∙
        (isoComp-cong (idIso (Right.first ⁻¹)) (isoComp-assoc-at image Left.first (δ ▷ u)) ∙
          isoComp-assoc-at (Right.first ⁻¹) (image ∙ Left.first) (δ ▷ u)))

  comparison : CoconeIso source target
  comparison = record { leftIso = δ ; rightIso = ε ; compatible = matching }
```
