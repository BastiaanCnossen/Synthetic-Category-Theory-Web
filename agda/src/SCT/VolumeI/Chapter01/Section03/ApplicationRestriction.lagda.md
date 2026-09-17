# Composition and change of parameter

The comparison for applying a mapping term commutes with iterated
substitution. We retain the chosen pairing comparisons and the external
associator in this calculation.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.Setup as Setup
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section03.Composition as MapComposition
import SCT.VolumeI.Chapter01.Section03.ProductAssociativity as ProductAssociativity
import SCT.VolumeI.Chapter01.Section03.CompositionNaturality as CompositionNaturality
import SCT.VolumeI.Chapter01.Section02.PairingNaturality as PairingNaturality
import SCT.VolumeI.Chapter01.Section02.IteratedPairing as IteratedPairing
import SCT.VolumeI.Chapter01.Section02.Structural as Structural

module SCT.VolumeI.Chapter01.Section03.ApplicationRestriction
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
  (u : NatIso (H ∘ r) H₁) (v : NatIso (H₁ ∘ s) H₂)
  (w : NatIso (H ∘ (r ∘ s)) H₃) (z : NatIso H₂ H₃)
  → Iso₂ (w ∙ comp-assoc s r H) (z ∙ (v ∙ (u ▷ s)))
  → Iso₂
      (((F ◁ w) ∙ comp-assoc (r ∘ s) H F) ∙ comp-assoc s r (F ∘ H))
      ((F ◁ z) ∙ (((F ◁ v) ∙ comp-assoc s H₁ F) ∙
        (((F ◁ u) ∙ comp-assoc r H F) ▷ s)))
post-iterated-comparison F H r s {H₁} u v w z p =
  let A = comp-assoc s r H
      pre = u ▷ s
      normalize = isoComp-assoc-at (z ∙ v) pre (invIso A) ∙
        (isoComp-cong (invIso (isoComp-assoc-at z v pre)) (idIso (invIso A)) ∙
          (isoComp-cong p (idIso (invIso A)) ∙ invIso (cancel-right A w)))
      image = ((F ◁ u) ∙ comp-assoc r H F) ▷ s
      targetA = comp-assoc s H₁ F
      finish = isoComp-cong (idIso (F ◁ z)) (invIso (isoComp-assoc-at (F ◁ v) targetA image)) ∙
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
            → NatIso ((F ∘ pair g y) ∘ r) (F ∘ pair (g ∘ r) (y ∘ r))
        pre g y r = (F ◁ pair-pre g y r) ∙ comp-assoc r (pair g y) F
    in Iso₂ (pre f x (σ ∘ τ) ∙ comp-assoc τ σ (F ∘ pair f x))
      ((F ◁ pair-cong (comp-assoc τ σ f) (comp-assoc τ σ x)) ∙
        (pre (f ∘ σ) (x ∘ σ) τ ∙ (pre f x σ ▷ τ)))
binary-pre-iterated F f x σ τ = post-iterated-comparison F (pair f x) σ τ
  (pair-pre f x σ) (pair-pre (f ∘ σ) (x ∘ σ) τ) (pair-pre f x (σ ∘ τ))
  (pair-cong (comp-assoc τ σ f) (comp-assoc τ σ x)) (pair-pre-iterated f x σ τ)

applyTerm-pre-iterated : {Q R X C D : CAT}
  (f : MAP X (Map C D)) (x : MAP X C) (σ : MAP R X) (τ : MAP Q R)
  → Iso₂ (applyTerm-pre f x (σ ∘ τ) ∙ comp-assoc τ σ (applyTerm f x))
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
  (α : NatIso f₁ f₂) (β : NatIso x₁ x₂)
  (γ : NatIso f₀ f₁) (δ : NatIso x₀ x₁)
  (base : NatIso source (applyTerm f₀ x₀))
  → Iso₂ (applyTerm-cong α β ∙ (applyTerm-cong γ δ ∙ base))
      (applyTerm-cong (α ∙ γ) (β ∙ δ) ∙ base)
combine-apply α β γ δ base =
  isoComp-cong (invIso (apply-cong-comp α γ β δ)) (idIso base) ∙
    invIso (isoComp-assoc-at (applyTerm-cong α β) (applyTerm-cong γ δ) base)

module ApplicationAssembly {R Γ X C D : CAT}
  (H : MAP X (Map C D)) (K : MAP X C)
  (q : MAP Γ X) (r : MAP R Γ) (q′ : MAP R X) (δ : NatIso (q ∘ r) q′)
  {f : MAP Γ (Map C D)} {x : MAP Γ C}
  {f′ : MAP R (Map C D)} {x′ : MAP R C}
  (a : NatIso (H ∘ q) f) (b : NatIso (K ∘ q) x)
  (a′ : NatIso (H ∘ q′) f′) (b′ : NatIso (K ∘ q′) x′)
  (c : NatIso (f ∘ r) f′) (d : NatIso (x ∘ r) x′) where

  normalization = applyTerm-cong a b ∙ applyTerm-pre H K q
  normalization′ = applyTerm-cong a′ b′ ∙ applyTerm-pre H K q′

  short = normalization′ ∙ ((applyTerm H K ◁ δ) ∙ comp-assoc r q (applyTerm H K))
  long = applyTerm-cong c d ∙ (applyTerm-pre f x r ∙ (normalization ▷ r))

  base = applyTerm-pre (H ∘ q) (K ∘ q) r ∙ (applyTerm-pre H K q ▷ r)

  short-normalization : Iso₂ short
    (applyTerm-cong (a′ ∙ ((H ◁ δ) ∙ comp-assoc r q H))
      (b′ ∙ ((K ◁ δ) ∙ comp-assoc r q K)) ∙ base)
  short-normalization =
    let paired = applyTerm-cong a′ b′
        changed = applyTerm-cong (H ◁ δ) (K ◁ δ)
        A = comp-assoc r q (applyTerm H K)
        substitute = isoComp-assoc-at changed (applyTerm-pre H K (q ∘ r)) A ∙
          (isoComp-cong (binary-pre-substitution mapEval H K δ) (idIso A) ∙
            invIso (isoComp-assoc-at (applyTerm-pre H K q′) (applyTerm H K ◁ δ) A))
        iterate = isoComp-cong (idIso changed) (applyTerm-pre-iterated H K q r)
        combineInner = combine-apply (H ◁ δ) (K ◁ δ)
          (comp-assoc r q H) (comp-assoc r q K) base
    in combine-apply a′ b′ ((H ◁ δ) ∙ comp-assoc r q H) ((K ◁ δ) ∙ comp-assoc r q K) base ∙
      (isoComp-cong (idIso paired) (combineInner ∙ (iterate ∙ substitute)) ∙
        isoComp-assoc-at paired (applyTerm-pre H K q′) ((applyTerm H K ◁ δ) ∙ A))

  long-normalization : Iso₂ long
    (applyTerm-cong (c ∙ (a ▷ r)) (d ∙ (b ▷ r)) ∙ base)
  long-normalization =
    let outer = applyTerm-cong c d
        before = applyTerm-pre H K q ▷ r
        middle = applyTerm-pre f x r
        input = applyTerm-cong a b ▷ r
        output = applyTerm-cong (a ▷ r) (b ▷ r)
        exchange = isoComp-assoc-at output (applyTerm-pre (H ∘ q) (K ∘ q) r) before ∙
          (isoComp-cong (binary-pre-inputs mapEval a b r) (idIso before) ∙
            invIso (isoComp-assoc-at middle input before))
    in combine-apply c d (a ▷ r) (b ▷ r) base ∙
      (isoComp-cong (idIso outer) exchange ∙
        isoComp-cong (idIso outer) (isoComp-cong (idIso middle)
          (preWhisker-isoComp-at (applyTerm-cong a b) (applyTerm-pre H K q) r)))

  assemble :
    Iso₂ (a′ ∙ ((H ◁ δ) ∙ comp-assoc r q H)) (c ∙ (a ▷ r))
    → Iso₂ (b′ ∙ ((K ◁ δ) ∙ comp-assoc r q K)) (d ∙ (b ▷ r))
    → Iso₂ short long
  assemble first second = invIso long-normalization ∙
    (isoComp-cong (apply-cong-Iso₂ first second) (idIso base) ∙ short-normalization)
```

The next two helpers carry projection witnesses through a restriction.
The second applies an additional fixed functor to the coordinate.

```agda
projection-square-forward : {R Γ X A : CAT} (π : MAP X A)
  (q : MAP Γ X) (r : MAP R Γ) (q′ : MAP R X)
  {p : MAP Γ A} {p′ : MAP R A}
  (δ : NatIso (q ∘ r) q′) (b : NatIso (π ∘ q) p)
  (b′ : NatIso (π ∘ q′) p′) (c : NatIso (p ∘ r) p′)
  → Iso₂ (b′ ∙ (π ◁ δ)) (c ∙ ((b ▷ r) ∙ invIso (comp-assoc r q π)))
  → Iso₂ (b′ ∙ ((π ◁ δ) ∙ comp-assoc r q π)) (c ∙ (b ▷ r))
projection-square-forward π q r q′ δ b b′ c square =
  let A = comp-assoc r q π
  in isoComp-cong (idIso c) (cancel-inverse-tail (b ▷ r) A) ∙
    (isoComp-assoc-at c ((b ▷ r) ∙ invIso A) A ∙
      (isoComp-cong square (idIso A) ∙ invIso (isoComp-assoc-at b′ (π ◁ δ) A)))

coordinate-restriction : {R Γ X A B : CAT} (F : MAP A B) (π : MAP X A)
  (q : MAP Γ X) (r : MAP R Γ) (q′ : MAP R X)
  {p : MAP Γ A} {p′ : MAP R A}
  (δ : NatIso (q ∘ r) q′) (b : NatIso (π ∘ q) p)
  (b′ : NatIso (π ∘ q′) p′) (c : NatIso (p ∘ r) p′)
  → Iso₂ (b′ ∙ (π ◁ δ)) (c ∙ ((b ▷ r) ∙ invIso (comp-assoc r q π)))
  → Iso₂
      (coordinate-at F π q′ b′ ∙ (((F ∘ π) ◁ δ) ∙ comp-assoc r q (F ∘ π)))
      ((F ◁ c) ∙ (comp-assoc r p F ∙ (coordinate-at F π q b ▷ r)))
coordinate-restriction F π q r q′ δ b b′ c square =
  let leftImage = F ◁ b′
      inputA = comp-assoc q′ π F
      change = (F ∘ π) ◁ δ
      sourceA = comp-assoc r q (F ∘ π)
      across = F ◁ (π ◁ δ)
      afterA = comp-assoc (q ∘ r) π F
      projectImage = (postWhisker F ◁ square) ∙
        invIso (postWhisker-isoComp-at F b′ (π ◁ δ))
      moveInput = isoComp-assoc-at across afterA sourceA ∙
        (isoComp-cong (postWhisker-comp-at δ π F) (idIso sourceA) ∙
          invIso (isoComp-assoc-at inputA change sourceA))
      removeInner = isoComp-cong projectImage (idIso (afterA ∙ sourceA)) ∙
        invIso (isoComp-assoc-at leftImage across (afterA ∙ sourceA))
  in post-pasting F π q r b c ∙
    (removeInner ∙
      (isoComp-cong (idIso leftImage) moveInput ∙
        isoComp-assoc-at leftImage inputA (change ∙ sourceA)))
```

