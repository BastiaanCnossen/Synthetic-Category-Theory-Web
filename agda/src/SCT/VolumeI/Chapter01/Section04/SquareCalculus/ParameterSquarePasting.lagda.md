# Pasting squares between varying parameters

The comparison for two composable squares retains all four external
associators and whiskerings in its boundary. This module uses only the
finite categorical calculus of `Theory`.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.Substitution.ProofCalculus as Setup
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.ProductFunctorCoherence as ProductFunctorCoherence
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.IteratedPairing as IteratedPairing
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section04.ProductCalculus.ProductSubstitution as ProductSubstitution
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PairingNaturality
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural
import SCT.VolumeI.Chapter01.Section02.Isomorphisms as Isomorphisms

module SCT.VolumeI.Chapter01.Section04.SquareCalculus.ParameterSquarePasting
  {c m a : Level} (𝒯 : Theory c m a) where

open Setup 𝒯
open IteratedPairing vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (transport-pre; transport-pre-assoc; pentagon-whiskered)
open PairingNaturality vocabulary terminal products productLaws composition vertical whiskering
  using (cancel-left-reflect)
open Structural vocabulary terminal products productLaws composition whiskering
  using (whisker-mixed-at)
open Isomorphisms vocabulary terminal products productLaws composition vertical whiskering
  using (cancel-inverse)

paste : {A₀ A₁ A₂ B₀ B₁ B₂ : CAT}
  {f : MAP A₀ A₁} {g : MAP A₁ A₂} {F : MAP B₀ B₁} {G : MAP B₁ B₂}
  {x₀ : MAP A₀ B₀} {x₁ : MAP A₁ B₁} {x₂ : MAP A₂ B₂}
  → (x₂ ∘ g) =₁ (G ∘ x₁) → (x₁ ∘ f) =₁ (F ∘ x₀)
  → (x₂ ∘ (g ∘ f)) =₁ ((G ∘ F) ∘ x₀)
paste {f = f} {g} {F} {G} {x₀} {x₁} {x₂} β α =
  (comp-assoc x₀ F G) ⁻¹ ∙
    ((G ◁ α) ∙ (comp-assoc f x₁ G ∙ ((β ▷ f) ∙ (comp-assoc f g x₂) ⁻¹)))

abstract
  paste-factor : {A₀ A₁ A₂ B₀ B₁ B₂ : CAT}
    {f : MAP A₀ A₁} {g : MAP A₁ A₂} {F : MAP B₀ B₁} {G : MAP B₁ B₂}
    {x₀ : MAP A₀ B₀} {x₁ : MAP A₁ B₁} {x₂ : MAP A₂ B₂}
    (β : (x₂ ∘ g) =₁ (G ∘ x₁)) (α : (x₁ ∘ f) =₁ (F ∘ x₀))
    → (paste β α) =₂
        (coordinate-comparison x₀ F x₁ f α G ∙ transport-pre x₂ g β f)
  paste-factor {f = f} {g} {F} {G} {x₀} {x₁} {x₂} β α =
    (isoComp-assoc-at ((comp-assoc x₀ F G) ⁻¹) ((G ◁ α) ∙ comp-assoc f x₁ G)
      (transport-pre x₂ g β f)) ⁻¹ ∙
      isoComp-cong (idIso ((comp-assoc x₀ F G) ⁻¹))
        ((isoComp-assoc-at (G ◁ α) (comp-assoc f x₁ G) (transport-pre x₂ g β f)) ⁻¹)
  
  pre-cancel-inverse : {R X Y : CAT} {u v w : MAP X Y}
    (β : v =₁ w) (α : u =₁ w) (r : MAP R X)
    → ((β ▷ r) ∙ ((β ⁻¹ ∙ α) ▷ r)) =₂ (α ▷ r)
  pre-cancel-inverse β α r = (preWhisker r ◁ cancel-inverse β α) ∙
    (preWhisker-isoComp-at β (β ⁻¹ ∙ α) r) ⁻¹
  
  post-cancel-inverse : {X Y Z : CAT} (F : MAP Y Z) {u v : MAP X Y}
    (β : u =₁ v) {w : MAP X Z} (α : w =₁ (F ∘ v))
    → ((F ◁ β) ∙ ((F ◁ β ⁻¹) ∙ α)) =₂ α
  post-cancel-inverse F {v = v} β α = isoComp-unitˡ-at α ∙
    (isoComp-cong
      (postWhisker-idIso F v ∙
        ((postWhisker F ◁ isoComp-inverseʳ-at β) ∙
          (postWhisker-isoComp-at F β (β ⁻¹)) ⁻¹)) (idIso α) ∙
      (isoComp-assoc-at (F ◁ β) (F ◁ β ⁻¹) α) ⁻¹)
  
  transport-paste : {A₀ A₁ A₂ A₃ B₁ B₂ B₃ : CAT}
    (f : MAP A₀ A₁) {g : MAP A₁ A₂} {h : MAP A₂ A₃}
    {G : MAP B₁ B₂} {H : MAP B₂ B₃}
    {x₁ : MAP A₁ B₁} {x₂ : MAP A₂ B₂} {x₃ : MAP A₃ B₃}
    (γ : (x₃ ∘ h) =₁ (H ∘ x₂)) (β : (x₂ ∘ g) =₁ (G ∘ x₁))
    →
        (comp-assoc f (G ∘ x₁) H ∙
          ((comp-assoc x₁ G H ▷ f) ∙ transport-pre x₃ (h ∘ g) (paste γ β) f)) =₂
        ((H ◁ transport-pre x₂ g β f) ∙
          (comp-assoc (g ∘ f) x₂ H ∙
            (transport-pre x₃ h γ (g ∘ f) ∙ (x₃ ◁ comp-assoc f g h))))
  transport-paste f {g} {h} {G} {H} {x₁} {x₂} {x₃} γ β =
    let A = comp-assoc f (G ∘ x₁) H
        B = comp-assoc x₁ G H
        C = comp-assoc g x₂ H
        T = transport-pre x₃ h γ g
        tail = (comp-assoc f (h ∘ g) x₃) ⁻¹
        S = (H ◁ β) ∙ (C ∙ T)
        β′ = (H ◁ β) ▷ f
        C′ = C ▷ f
        T′ = T ▷ f
        βImage = H ◁ (β ▷ f)
        middle = comp-assoc f (x₂ ∘ g) H
        inputA = comp-assoc f g x₂
        nextA = comp-assoc (g ∘ f) x₂ H
        endA = comp-assoc f g (H ∘ x₂)
        end = transport-pre x₃ h γ (g ∘ f) ∙ (x₃ ◁ comp-assoc f g h)
        corner = cancel-left-reflect (H ◁ inputA)
          ((post-cancel-inverse H inputA (nextA ∙ endA)) ⁻¹ ∙
            (pentagon-whiskered f g x₂ H) ⁻¹)
        transport = transport-pre-assoc x₃ h (H ∘ x₂) γ g f
        expandS = isoComp-cong (idIso β′) (preWhisker-isoComp-at C T f) ∙
          preWhisker-isoComp-at (H ◁ β) (C ∙ T) f
        cancelB = isoComp-cong (pre-cancel-inverse B S f) (idIso tail) ∙
          (isoComp-assoc-at (B ▷ f) (paste γ β ▷ f) tail) ⁻¹
        expand = isoComp-cong (idIso A)
          (isoComp-cong (idIso β′) (isoComp-assoc-at C′ T′ tail) ∙
            (isoComp-assoc-at β′ (C′ ∙ T′) tail ∙
              isoComp-cong expandS (idIso tail)))
        firstExchange = isoComp-cong (whisker-mixed-at β f H) (idIso (C′ ∙ (T′ ∙ tail))) ∙
          (isoComp-assoc-at A β′ (C′ ∙ (T′ ∙ tail))) ⁻¹
        secondExchange = isoComp-assoc-at βImage middle (C′ ∙ (T′ ∙ tail))
        useCorner = isoComp-cong (idIso βImage)
          (isoComp-cong corner (idIso (T′ ∙ tail)) ∙
            (isoComp-assoc-at middle C′ (T′ ∙ tail)) ⁻¹)
        finishTail = isoComp-cong (idIso βImage)
          (isoComp-cong (idIso (H ◁ inputA ⁻¹))
              (isoComp-cong (idIso nextA)
                  (transport ∙ (isoComp-assoc-at endA T′ tail) ⁻¹) ∙
                isoComp-assoc-at nextA endA (T′ ∙ tail)) ∙
            isoComp-assoc-at (H ◁ inputA ⁻¹) (nextA ∙ endA) (T′ ∙ tail))
    in isoComp-cong ((postWhisker-isoComp-at H (β ▷ f) (inputA ⁻¹)) ⁻¹) (idIso (nextA ∙ end)) ∙
      ((isoComp-assoc-at βImage (H ◁ inputA ⁻¹) (nextA ∙ end)) ⁻¹ ∙
      (finishTail ∙ (useCorner ∙ (secondExchange ∙ (firstExchange ∙
        (expand ∙ isoComp-cong (idIso A) cancelB))))))
```

The associativity proof reuses the already verified coordinate transport
calculation. Its module carries `M` solely because that helper currently
lives in `ProductSubstitution`; the calculation itself uses only `Theory`.

```agda
module Coherence (M : Mapping.MappingAnimae 𝒯) where
  open ProductSubstitution 𝒯 M using (coordinate-outer-comp)

  abstract
    paste-assoc : {A₀ A₁ A₂ A₃ B₀ B₁ B₂ B₃ : CAT}
      {f : MAP A₀ A₁} {g : MAP A₁ A₂} {h : MAP A₂ A₃}
      {F : MAP B₀ B₁} {G : MAP B₁ B₂} {H : MAP B₂ B₃}
      {x₀ : MAP A₀ B₀} {x₁ : MAP A₁ B₁} {x₂ : MAP A₂ B₂} {x₃ : MAP A₃ B₃}
      (γ : (x₃ ∘ h) =₁ (H ∘ x₂)) (β : (x₂ ∘ g) =₁ (G ∘ x₁))
      (α : (x₁ ∘ f) =₁ (F ∘ x₀))
      →
          ((comp-assoc F G H ▷ x₀) ∙ paste (paste γ β) α) =₂
          (paste γ (paste β α) ∙ (x₃ ◁ comp-assoc f g h))
    paste-assoc {f = f} {g} {h} {F} {G} {H} {x₀} {x₁} {x₂} {x₃} γ β α =
      let c = coordinate-comparison x₀ F x₁ f α G
          cHG = coordinate-comparison x₀ F x₁ f α (H ∘ G)
          nested = coordinate-comparison x₀ (G ∘ F) (G ∘ x₁) f c H
          lead = comp-assoc F G H ▷ x₀
          B = comp-assoc x₁ G H ▷ f
          t = transport-pre x₃ (h ∘ g) (paste γ β) f
          tβ = transport-pre x₂ g β f
          tγ = transport-pre x₃ h γ (g ∘ f)
          last = x₃ ◁ comp-assoc f g h
          I = (comp-assoc x₀ (G ∘ F) H) ⁻¹
          A = comp-assoc f (G ∘ x₁) H
          N = comp-assoc (g ∘ f) x₂ H
          hc = H ◁ c
          hβ = H ◁ tβ
          hp = H ◁ paste β α
          start = isoComp-cong (idIso lead) (paste-factor (paste γ β) α)
          outer = isoComp-assoc-at nested B t ∙
            (isoComp-cong (coordinate-outer-comp x₀ F x₁ f α G H) (idIso t) ∙
              (isoComp-assoc-at lead cHG t) ⁻¹)
          expand = isoComp-cong (idIso I) (isoComp-assoc-at hc A (B ∙ t)) ∙
            isoComp-assoc-at I (hc ∙ A) (B ∙ t)
          transport = isoComp-cong (idIso I)
            (isoComp-cong (idIso hc) (transport-paste f γ β))
          merge = isoComp-cong (idIso I)
            (isoComp-cong
              ((postWhisker H ◁ (paste-factor β α) ⁻¹) ∙
                (postWhisker-isoComp-at H c tβ) ⁻¹)
              (idIso (N ∙ (tγ ∙ last))) ∙
              (isoComp-assoc-at hc hβ (N ∙ (tγ ∙ last))) ⁻¹)
          finish = (isoComp-assoc-at I (hp ∙ (N ∙ tγ)) last) ⁻¹ ∙
            (isoComp-cong (idIso I)
              ((isoComp-assoc-at hp (N ∙ tγ) last) ⁻¹ ∙
                isoComp-cong (idIso hp) ((isoComp-assoc-at N tγ last) ⁻¹)))
      in finish ∙ (merge ∙ (transport ∙ (expand ∙ (outer ∙ start))))
```
