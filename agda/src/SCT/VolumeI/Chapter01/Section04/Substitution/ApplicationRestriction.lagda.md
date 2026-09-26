# Composition and change of parameter

The comparison for applying a mapping term commutes with iterated
substitution. We retain the chosen pairing comparisons and the external
associator in this calculation.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.Setup as Setup
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section04.Composition as MapComposition
import SCT.VolumeI.Chapter01.Section04.ProductCalculus.ProductAssociativity as ProductAssociativity
import SCT.VolumeI.Chapter01.Section04.CompositionCalculus.CompositionNaturality as CompositionNaturality
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PairingNaturality
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.IteratedPairing as IteratedPairing
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural

module SCT.VolumeI.Chapter01.Section04.Substitution.ApplicationRestriction
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open Setup 𝒯
open Mapping.MappingAnimae M
open MapComposition 𝒯 M
open ProductAssociativity 𝒯 M using (post-pasting; cancel-inverse-tail)
open CompositionNaturality 𝒯 M
  using (apply-cong-comp; apply-cong-Iso₂; binary-pre-inputs; binary-pre-substitution; coordinate-at)
open Structural vocabulary terminal products productLaws composition whiskering
  using (postWhisker-comp-at)
open PairingNaturality vocabulary terminal products productLaws composition vertical whiskering
  using (cancel-right)
open IteratedPairing vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (pair-pre-iterated)

post-iterated-comparison : {Q R X A B : CAT}
  (F : MAP A B) (H : MAP X A) (r : MAP R X) (s : MAP Q R)
  {H₁ : MAP R A} {H₂ H₃ : MAP Q A}
  (u : (H ∘ r) =₁ H₁) (v : (H₁ ∘ s) =₁ H₂)
  (w : (H ∘ (r ∘ s)) =₁ H₃) (z : H₂ =₁ H₃)
  → (w ∙ comp-assoc s r H) =₂ (z ∙ (v ∙ (u ▷ s)))
  →
      (((F ◁ w) ∙ comp-assoc (r ∘ s) H F) ∙ comp-assoc s r (F ∘ H)) =₂
      ((F ◁ z) ∙ (((F ◁ v) ∙ comp-assoc s H₁ F) ∙
        (((F ◁ u) ∙ comp-assoc r H F) ▷ s)))
post-iterated-comparison F H r s {H₁} u v w z p =
  let A = comp-assoc s r H
      pre = u ▷ s
      normalize = isoComp-assoc-at (z ∙ v) pre (A ⁻¹) ∙
        (isoComp-cong ((isoComp-assoc-at z v pre) ⁻¹) (idIso (A ⁻¹)) ∙
          (isoComp-cong p (idIso (A ⁻¹)) ∙ (cancel-right A w) ⁻¹))
      image = ((F ◁ u) ∙ comp-assoc r H F) ▷ s
      targetA = comp-assoc s H₁ F
      finish = isoComp-cong (idIso (F ◁ z)) ((isoComp-assoc-at (F ◁ v) targetA image) ⁻¹) ∙
        (isoComp-assoc-at (F ◁ z) (F ◁ v) (targetA ∙ image) ∙
          isoComp-cong (postWhisker-isoComp-at F z v) (idIso (targetA ∙ image)))
  in finish ∙
    (post-pasting F H r s u (z ∙ v) ∙
      (isoComp-cong (postWhisker F ◁ normalize)
        (idIso (comp-assoc (r ∘ s) H F ∙ comp-assoc s r (F ∘ H))) ∙
        isoComp-assoc-at (F ◁ w) (comp-assoc (r ∘ s) H F) (comp-assoc s r (F ∘ H))))

binary-pre-iterated : {Q R X A B C : CAT}
  (F : MAP (A × B) C) (f : MAP X A) (x : MAP X B)
  (σ : MAP R X) (τ : MAP Q R)
  → let pre : {Y Z : CAT} (g : MAP Y A) (y : MAP Y B) (r : MAP Z Y)
            → ((F ∘ pair g y) ∘ r) =₁ (F ∘ pair (g ∘ r) (y ∘ r))
        pre g y r = (F ◁ pair-pre g y r) ∙ comp-assoc r (pair g y) F
    in (pre f x (σ ∘ τ) ∙ comp-assoc τ σ (F ∘ pair f x)) =₂
      ((F ◁ pair-cong (comp-assoc τ σ f) (comp-assoc τ σ x)) ∙
        (pre (f ∘ σ) (x ∘ σ) τ ∙ (pre f x σ ▷ τ)))
binary-pre-iterated F f x σ τ = post-iterated-comparison F (pair f x) σ τ
  (pair-pre f x σ) (pair-pre (f ∘ σ) (x ∘ σ) τ) (pair-pre f x (σ ∘ τ))
  (pair-cong (comp-assoc τ σ f) (comp-assoc τ σ x)) (pair-pre-iterated f x σ τ)

applyTerm-pre-iterated : {Q R X C D : CAT}
  (f : MAP X (Map C D)) (x : MAP X C) (σ : MAP R X) (τ : MAP Q R)
  → (applyTerm-pre f x (σ ∘ τ) ∙ comp-assoc τ σ (applyTerm f x)) =₂
      (applyTerm-cong (comp-assoc τ σ f) (comp-assoc τ σ x) ∙
        (applyTerm-pre (f ∘ σ) (x ∘ σ) τ ∙ (applyTerm-pre f x σ ▷ τ)))
applyTerm-pre-iterated = binary-pre-iterated mapEval
```

A normalized application is obtained by restricting the two inputs and
then comparing them with their intended values. The following assembly
transports the normalization through another restriction, given the two
corresponding input squares.

```agda
combine-apply : {X C D : CAT}
  {f₀ f₁ f₂ : MAP X (Map C D)} {x₀ x₁ x₂ : MAP X C} {source : MAP X D}
  (α : f₁ =₁ f₂) (β : x₁ =₁ x₂)
  (γ : f₀ =₁ f₁) (δ : x₀ =₁ x₁)
  (base : source =₁ (applyTerm f₀ x₀))
  → (applyTerm-cong α β ∙ (applyTerm-cong γ δ ∙ base)) =₂
      (applyTerm-cong (α ∙ γ) (β ∙ δ) ∙ base)
combine-apply α β γ δ base =
  isoComp-cong ((apply-cong-comp α γ β δ) ⁻¹) (idIso base) ∙
    (isoComp-assoc-at (applyTerm-cong α β) (applyTerm-cong γ δ) base) ⁻¹

module ApplicationAssembly {R Γ X C D : CAT}
  (H : MAP X (Map C D)) (K : MAP X C)
  (q : MAP Γ X) (r : MAP R Γ) (q′ : MAP R X) (δ : (q ∘ r) =₁ q′)
  {f : MAP Γ (Map C D)} {x : MAP Γ C}
  {f′ : MAP R (Map C D)} {x′ : MAP R C}
  (a : (H ∘ q) =₁ f) (b : (K ∘ q) =₁ x)
  (a′ : (H ∘ q′) =₁ f′) (b′ : (K ∘ q′) =₁ x′)
  (c : (f ∘ r) =₁ f′) (d : (x ∘ r) =₁ x′) where

  normalization = applyTerm-cong a b ∙ applyTerm-pre H K q
  normalization′ = applyTerm-cong a′ b′ ∙ applyTerm-pre H K q′

  short = normalization′ ∙ ((applyTerm H K ◁ δ) ∙ comp-assoc r q (applyTerm H K))
  long = applyTerm-cong c d ∙ (applyTerm-pre f x r ∙ (normalization ▷ r))

  base = applyTerm-pre (H ∘ q) (K ∘ q) r ∙ (applyTerm-pre H K q ▷ r)

  short-normalization : short =₂
    (applyTerm-cong (a′ ∙ ((H ◁ δ) ∙ comp-assoc r q H))
      (b′ ∙ ((K ◁ δ) ∙ comp-assoc r q K)) ∙ base)
  short-normalization =
    let paired = applyTerm-cong a′ b′
        changed = applyTerm-cong (H ◁ δ) (K ◁ δ)
        A = comp-assoc r q (applyTerm H K)
        substitute = isoComp-assoc-at changed (applyTerm-pre H K (q ∘ r)) A ∙
          (isoComp-cong (binary-pre-substitution mapEval H K δ) (idIso A) ∙
            (isoComp-assoc-at (applyTerm-pre H K q′) (applyTerm H K ◁ δ) A) ⁻¹)
        iterate = isoComp-cong (idIso changed) (applyTerm-pre-iterated H K q r)
        combineInner = combine-apply (H ◁ δ) (K ◁ δ)
          (comp-assoc r q H) (comp-assoc r q K) base
    in combine-apply a′ b′ ((H ◁ δ) ∙ comp-assoc r q H) ((K ◁ δ) ∙ comp-assoc r q K) base ∙
      (isoComp-cong (idIso paired) (combineInner ∙ (iterate ∙ substitute)) ∙
        isoComp-assoc-at paired (applyTerm-pre H K q′) ((applyTerm H K ◁ δ) ∙ A))

  long-normalization : long =₂
    (applyTerm-cong (c ∙ (a ▷ r)) (d ∙ (b ▷ r)) ∙ base)
  long-normalization =
    let outer = applyTerm-cong c d
        before = applyTerm-pre H K q ▷ r
        middle = applyTerm-pre f x r
        input = applyTerm-cong a b ▷ r
        output = applyTerm-cong (a ▷ r) (b ▷ r)
        exchange = isoComp-assoc-at output (applyTerm-pre (H ∘ q) (K ∘ q) r) before ∙
          (isoComp-cong (binary-pre-inputs mapEval a b r) (idIso before) ∙
            (isoComp-assoc-at middle input before) ⁻¹)
    in combine-apply c d (a ▷ r) (b ▷ r) base ∙
      (isoComp-cong (idIso outer) exchange ∙
        isoComp-cong (idIso outer) (isoComp-cong (idIso middle)
          (preWhisker-isoComp-at (applyTerm-cong a b) (applyTerm-pre H K q) r)))

  assemble :
    (a′ ∙ ((H ◁ δ) ∙ comp-assoc r q H)) =₂ (c ∙ (a ▷ r))
    → (b′ ∙ ((K ◁ δ) ∙ comp-assoc r q K)) =₂ (d ∙ (b ▷ r))
    → short =₂ long
  assemble first second = long-normalization ⁻¹ ∙
    (isoComp-cong (apply-cong-Iso₂ first second) (idIso base) ∙ short-normalization)
```

The next two helpers carry projection witnesses through a restriction.
The second applies an additional fixed functor to the coordinate.

```agda
projection-square-forward : {R Γ X A : CAT} (π : MAP X A)
  (q : MAP Γ X) (r : MAP R Γ) (q′ : MAP R X)
  {p : MAP Γ A} {p′ : MAP R A}
  (δ : (q ∘ r) =₁ q′) (b : (π ∘ q) =₁ p)
  (b′ : (π ∘ q′) =₁ p′) (c : (p ∘ r) =₁ p′)
  → (b′ ∙ (π ◁ δ)) =₂ (c ∙ ((b ▷ r) ∙ (comp-assoc r q π) ⁻¹))
  → (b′ ∙ ((π ◁ δ) ∙ comp-assoc r q π)) =₂ (c ∙ (b ▷ r))
projection-square-forward π q r q′ δ b b′ c square =
  let A = comp-assoc r q π
  in isoComp-cong (idIso c) (cancel-inverse-tail (b ▷ r) A) ∙
    (isoComp-assoc-at c ((b ▷ r) ∙ A ⁻¹) A ∙
      (isoComp-cong square (idIso A) ∙ (isoComp-assoc-at b′ (π ◁ δ) A) ⁻¹))

coordinate-restriction : {R Γ X A B : CAT} (F : MAP A B) (π : MAP X A)
  (q : MAP Γ X) (r : MAP R Γ) (q′ : MAP R X)
  {p : MAP Γ A} {p′ : MAP R A}
  (δ : (q ∘ r) =₁ q′) (b : (π ∘ q) =₁ p)
  (b′ : (π ∘ q′) =₁ p′) (c : (p ∘ r) =₁ p′)
  → (b′ ∙ (π ◁ δ)) =₂ (c ∙ ((b ▷ r) ∙ (comp-assoc r q π) ⁻¹))
  →
      (coordinate-at F π q′ b′ ∙ (((F ∘ π) ◁ δ) ∙ comp-assoc r q (F ∘ π))) =₂
      ((F ◁ c) ∙ (comp-assoc r p F ∙ (coordinate-at F π q b ▷ r)))
coordinate-restriction F π q r q′ δ b b′ c square =
  let leftImage = F ◁ b′
      inputA = comp-assoc q′ π F
      change = (F ∘ π) ◁ δ
      sourceA = comp-assoc r q (F ∘ π)
      across = F ◁ (π ◁ δ)
      afterA = comp-assoc (q ∘ r) π F
      projectImage = (postWhisker F ◁ square) ∙
        (postWhisker-isoComp-at F b′ (π ◁ δ)) ⁻¹
      moveInput = isoComp-assoc-at across afterA sourceA ∙
        (isoComp-cong (postWhisker-comp-at δ π F) (idIso sourceA) ∙
          (isoComp-assoc-at inputA change sourceA) ⁻¹)
      removeInner = isoComp-cong projectImage (idIso (afterA ∙ sourceA)) ∙
        (isoComp-assoc-at leftImage across (afterA ∙ sourceA)) ⁻¹
  in post-pasting F π q r b c ∙
    (removeInner ∙
      (isoComp-cong (idIso leftImage) moveInput ∙
        isoComp-assoc-at leftImage inputA (change ∙ sourceA)))
```

