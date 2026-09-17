# Associativity of product substitution

We compare the two iterated substitutions using the existing product
comparison. The pairing calculation below reduces this to its two
coordinate comparisons, preserving the specified external associator.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.Setup as Setup
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section03.Compatibility as Compatibility
import SCT.VolumeI.Chapter01.Section03.ProductSubstitution as ProductSubstitution
import SCT.VolumeI.Chapter01.Section03.ProductSecondCoordinate as ProductSecondCoordinate
import SCT.VolumeI.Chapter01.Section02.PairingCoherence as PairingCoherence
import SCT.VolumeI.Chapter01.Section02.PairingNaturality as PairingNaturality
import SCT.VolumeI.Chapter01.Section02.IteratedPairing as IteratedPairing
import SCT.VolumeI.Chapter01.Section02.Structural as Structural

module SCT.VolumeI.Chapter01.Section03.ProductAssociativity
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open Setup 𝒯
open Compatibility 𝒯 M using (slice-comparison)
open ProductSubstitution 𝒯 M
open ProductSecondCoordinate 𝒯 M using (second-coordinate-assoc)
open PairingCoherence vocabulary terminal products productLaws composition vertical whiskering
  using (pair-cong-comp; pair-cong-Iso₂)
open PairingNaturality vocabulary terminal products productLaws composition vertical whiskering
  using (pair-pre-natural-inputs; pair-pre-natural-substitution)
open IteratedPairing vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (pair-pre-iterated; pentagon-whiskered)
open Structural vocabulary terminal products productLaws composition whiskering
  using (whisker-mixed-at; postWhisker-comp-at)

combine-pair : {X A B : CAT} {a₀ a₁ a₂ : MAP X A} {b₀ b₁ b₂ : MAP X B}
  {source : MAP X (A × B)}
  (α : NatIso a₁ a₂) (β : NatIso b₁ b₂)
  (γ : NatIso a₀ a₁) (δ : NatIso b₀ b₁)
  (base : NatIso source (pair a₀ b₀))
  → Iso₂ (pair-cong α β ∙ (pair-cong γ δ ∙ base))
      (pair-cong (α ∙ γ) (β ∙ δ) ∙ base)
combine-pair α β γ δ base =
  isoComp-cong (invIso (pair-cong-comp α γ β δ)) (idIso base) ∙
    invIso (isoComp-assoc-at (pair-cong α β) (pair-cong γ δ) base)

module PairingAssembly {Q R X A B : CAT}
  (b : MAP X A) (c : MAP X B) (r : MAP R X) (t : MAP Q R)
  (s : MAP Q X) (δ : NatIso (r ∘ t) s)
  {b₁ : MAP R A} {c₁ : MAP R B} {b₂ b₃ : MAP Q A} {c₂ c₃ : MAP Q B}
  (u : NatIso (b ∘ r) b₁) (v : NatIso (c ∘ r) c₁)
  (w : NatIso (b₁ ∘ t) b₂) (z : NatIso (c₁ ∘ t) c₂)
  (a : NatIso (b ∘ s) b₃) (d : NatIso (c ∘ s) c₃)
  (η : NatIso b₂ b₃) (θ : NatIso c₂ c₃) where

  base : NatIso ((pair b c ∘ r) ∘ t) (pair ((b ∘ r) ∘ t) ((c ∘ r) ∘ t))
  base = pair-pre (b ∘ r) (c ∘ r) t ∙ (pair-pre b c r ▷ t)

  shortFirst : NatIso ((b ∘ r) ∘ t) b₃
  shortFirst = a ∙ ((b ◁ δ) ∙ comp-assoc t r b)

  shortSecond : NatIso ((c ∘ r) ∘ t) c₃
  shortSecond = d ∙ ((c ◁ δ) ∙ comp-assoc t r c)

  longFirst : NatIso ((b ∘ r) ∘ t) b₃
  longFirst = η ∙ (w ∙ (u ▷ t))

  longSecond : NatIso ((c ∘ r) ∘ t) c₃
  longSecond = θ ∙ (z ∙ (v ▷ t))

  short : NatIso ((pair b c ∘ r) ∘ t) (pair b₃ c₃)
  short = (pair-cong a d ∙ pair-pre b c s) ∙
    ((pair b c ◁ δ) ∙ comp-assoc t r (pair b c))

  long : NatIso ((pair b c ∘ r) ∘ t) (pair b₃ c₃)
  long = pair-cong η θ ∙ ((pair-cong w z ∙ pair-pre b₁ c₁ t) ∙
    ((pair-cong u v ∙ pair-pre b c r) ▷ t))

  short-normalization : Iso₂ short (pair-cong shortFirst shortSecond ∙ base)
  short-normalization =
    let paired = pair-cong a d
        changed = pair-cong (b ◁ δ) (c ◁ δ)
        A = comp-assoc t r (pair b c)
        pairedA = pair-cong (comp-assoc t r b) (comp-assoc t r c)
        substitute = isoComp-assoc-at changed (pair-pre b c (r ∘ t)) A ∙
          (isoComp-cong (invIso (pair-pre-natural-substitution b c δ)) (idIso A) ∙
            invIso (isoComp-assoc-at (pair-pre b c s) (pair b c ◁ δ) A))
        iterate = isoComp-cong (idIso changed) (pair-pre-iterated b c r t)
        combineInner = combine-pair (b ◁ δ) (c ◁ δ)
          (comp-assoc t r b) (comp-assoc t r c) base
    in combine-pair a d ((b ◁ δ) ∙ comp-assoc t r b) ((c ◁ δ) ∙ comp-assoc t r c) base ∙
      (isoComp-cong (idIso paired) (combineInner ∙ (iterate ∙ substitute)) ∙
        isoComp-assoc-at paired (pair-pre b c s) ((pair b c ◁ δ) ∙ A))

  intermediate-normalization : Iso₂
    ((pair-cong w z ∙ pair-pre b₁ c₁ t) ∙ ((pair-cong u v ∙ pair-pre b c r) ▷ t))
    (pair-cong (w ∙ (u ▷ t)) (z ∙ (v ▷ t)) ∙ base)
  intermediate-normalization =
    let outer = pair-cong w z
        before = pair-pre b c r ▷ t
        middle = pair-pre b₁ c₁ t
        input = pair-cong u v ▷ t
        output = pair-cong (u ▷ t) (v ▷ t)
        exchange = isoComp-assoc-at output (pair-pre (b ∘ r) (c ∘ r) t) before ∙
          (isoComp-cong (invIso (pair-pre-natural-inputs u v t)) (idIso before) ∙
            invIso (isoComp-assoc-at middle input before))
    in combine-pair w z (u ▷ t) (v ▷ t) base ∙
      (isoComp-cong (idIso outer) exchange ∙
        (isoComp-assoc-at outer middle (input ∙ before) ∙
          isoComp-cong (idIso (outer ∙ middle))
            (preWhisker-isoComp-at (pair-cong u v) (pair-pre b c r) t)))

  long-normalization : Iso₂ long (pair-cong longFirst longSecond ∙ base)
  long-normalization =
    combine-pair η θ (w ∙ (u ▷ t)) (z ∙ (v ▷ t)) base ∙
      isoComp-cong (idIso (pair-cong η θ)) intermediate-normalization

  assemble : Iso₂ shortFirst longFirst → Iso₂ shortSecond longSecond → Iso₂ short long
  assemble first second = invIso long-normalization ∙
    (isoComp-cong (pair-cong-Iso₂ first second) (idIso base) ∙ short-normalization)
```

Postcomposition carries a pasted coordinate square to the pasted image
square. The external pentagon accounts for the three reassociations.

```agda
cancel-inverse-tail : {X Y : CAT} {a b c : MAP X Y}
  (α : NatIso b c) (β : NatIso b a)
  → Iso₂ ((α ∙ invIso β) ∙ β) α
cancel-inverse-tail α β = isoComp-unitʳ-at α ∙
  (isoComp-cong (idIso α) (isoComp-inverseˡ-at β) ∙ isoComp-assoc-at α (invIso β) β)

post-pasting : {Q R K A B : CAT}
  (F : MAP A B) (π : MAP K A) (h : MAP R K) (k : MAP Q R)
  {q : MAP R A} {v : MAP Q A}
  (b : NatIso (π ∘ h) q) (c : NatIso (q ∘ k) v)
  → Iso₂
      ((F ◁ (c ∙ ((b ▷ k) ∙ invIso (comp-assoc k h π)))) ∙
        (comp-assoc (h ∘ k) π F ∙ comp-assoc k h (F ∘ π)))
      ((F ◁ c) ∙ (comp-assoc k q F ∙ (((F ◁ b) ∙ comp-assoc h π F) ▷ k)))
post-pasting F π h k {q} b c =
  let A = comp-assoc k h π
      B = comp-assoc k (π ∘ h) F
      C = comp-assoc h π F ▷ k
      D = comp-assoc k q F
      e = F ◁ c
      d = F ◁ (b ▷ k)
      p = F ◁ (c ∙ ((b ▷ k) ∙ invIso A))
      cancellation = cancel-inverse-tail (c ∙ (b ▷ k)) A ∙
        isoComp-cong (invIso (isoComp-assoc-at c (b ▷ k) (invIso A))) (idIso A)
      join = postWhisker-isoComp-at F c (b ▷ k) ∙
        ((postWhisker F ◁ cancellation) ∙
          invIso (postWhisker-isoComp-at F (c ∙ ((b ▷ k) ∙ invIso A)) A))
      mixed = invIso (whisker-mixed-at b k F)
      finish = isoComp-cong (idIso e)
        (isoComp-cong (idIso D)
          (invIso (preWhisker-isoComp-at (F ◁ b) (comp-assoc h π F) k)) ∙
          isoComp-assoc-at D ((F ◁ b) ▷ k) C)
      exchange = isoComp-cong (idIso e) (isoComp-cong mixed (idIso C)) ∙
        (isoComp-cong (idIso e) (invIso (isoComp-assoc-at d B C)) ∙
          isoComp-assoc-at e d (B ∙ C))
  in finish ∙ (exchange ∙
    (isoComp-cong join (idIso (B ∙ C)) ∙
      (invIso (isoComp-assoc-at p (F ◁ A) (B ∙ C)) ∙
        isoComp-cong (idIso p) (pentagon-whiskered k h π F))))

cancel-forward : {X Y : CAT} {a b c : MAP X Y}
  (α : NatIso a b) (β : NatIso c b)
  → Iso₂ (α ∙ (invIso α ∙ β)) β
cancel-forward α β = isoComp-unitˡ-at β ∙
  (isoComp-cong (isoComp-inverseʳ-at α) (idIso β) ∙
    invIso (isoComp-assoc-at α (invIso α) β))

first-coordinate-assoc : {Q R X Z : CAT} (C : CAT)
  (f : MAP X Z) (σ : MAP R X) (τ : MAP Q R)
  → Iso₂
      (Coordinates.first C f (σ ∘ τ) ∙
        (((f ∘ pr₁) ◁ slice-comparison {C = C} σ τ) ∙
          comp-assoc (productMap τ (id C)) (productMap σ (id C)) (f ∘ pr₁)))
      ((comp-assoc τ σ f ▷ pr₁) ∙
        (Coordinates.first C (f ∘ σ) τ ∙
          (Coordinates.first C f σ ▷ productMap τ (id C))))
first-coordinate-assoc C f σ τ =
  let h = productMap σ (id C)
      k = productMap τ (id C)
      l = productMap (σ ∘ τ) (id C)
      κ = slice-comparison {C = C} σ τ
      b = pair-β₁ (σ ∘ pr₁) (id C ∘ pr₂)
      b′ = pair-β₁ ((σ ∘ τ) ∘ pr₁) (id C ∘ pr₂)
      c = Coordinates.first C σ τ
      outside = invIso (comp-assoc pr₁ (σ ∘ τ) f)
      leftImage = f ◁ b′
      inputA = comp-assoc l pr₁ f
      change = (f ∘ pr₁) ◁ κ
      sourceA = comp-assoc k h (f ∘ pr₁)
      across = f ◁ (pr₁ ◁ κ)
      afterA = comp-assoc (h ∘ k) pr₁ f
      projected = c ∙ ((b ▷ k) ∙ invIso (comp-assoc k h pr₁))
      projectImage = (postWhisker f ◁ Coordinates.projection₁ C σ τ) ∙
        invIso (postWhisker-isoComp-at f b′ (pr₁ ◁ κ))
      moveInput = isoComp-assoc-at across afterA sourceA ∙
        (isoComp-cong (postWhisker-comp-at κ pr₁ f) (idIso sourceA) ∙
          invIso (isoComp-assoc-at inputA change sourceA))
      removeInner = isoComp-cong projectImage (idIso (afterA ∙ sourceA)) ∙
        invIso (isoComp-assoc-at leftImage across (afterA ∙ sourceA))
      normalizeShort = isoComp-cong (idIso outside)
        (post-pasting f pr₁ h k b c ∙
          (removeInner ∙
            (isoComp-cong (idIso leftImage) moveInput ∙
              isoComp-assoc-at leftImage inputA (change ∙ sourceA)))) ∙
        isoComp-assoc-at outside (leftImage ∙ inputA) (change ∙ sourceA)
      u = Coordinates.first C f σ
      w = Coordinates.first C (f ∘ σ) τ
      η = comp-assoc τ σ f ▷ pr₁
      sourceCorner = comp-assoc pr₁ σ f
      imageBefore = (f ◁ b) ∙ comp-assoc h pr₁ f
      nextCoordinate = coordinate-comparison pr₁ (σ ∘ τ) (σ ∘ pr₁) k c f
      outerSquare = coordinate-outer-comp pr₁ τ pr₁ k
        (pair-β₁ (τ ∘ pr₁) (id C ∘ pr₂)) σ f
      simplifyCorner = (preWhisker k ◁ cancel-forward sourceCorner imageBefore) ∙
        invIso (preWhisker-isoComp-at sourceCorner u k)
      normalizeLong = isoComp-cong (idIso outside)
        (isoComp-assoc-at (f ◁ c) (comp-assoc k (σ ∘ pr₁) f) (imageBefore ▷ k)) ∙
        (isoComp-assoc-at outside ((f ◁ c) ∙ comp-assoc k (σ ∘ pr₁) f) (imageBefore ▷ k) ∙
          (isoComp-cong (idIso nextCoordinate) simplifyCorner ∙
            (isoComp-assoc-at nextCoordinate (sourceCorner ▷ k) (u ▷ k) ∙
              (isoComp-cong outerSquare (idIso (u ▷ k)) ∙
                invIso (isoComp-assoc-at η w (u ▷ k))))))
  in invIso normalizeLong ∙ normalizeShort
```

We now apply the assembly to the two projections of the chosen product
substitution comparison. The normalization witnesses return the conclusion
to `slice-comparison` itself.

```agda
slice-comparison-assoc : {Q R X Z : CAT} (C : CAT)
  (f : MAP X Z) (σ : MAP R X) (τ : MAP Q R)
  → Iso₂
      (slice-comparison {C = C} f (σ ∘ τ) ∙
        ((productMap f (id C) ◁ slice-comparison {C = C} σ τ) ∙
          comp-assoc (productMap τ (id C)) (productMap σ (id C)) (productMap f (id C))))
      (productMap-cong (comp-assoc τ σ f) (idIso (id C)) ∙
        (slice-comparison {C = C} (f ∘ σ) τ ∙
          (slice-comparison {C = C} f σ ▷ productMap τ (id C))))
slice-comparison-assoc C f σ τ =
  let h = productMap σ (id C)
      k = productMap τ (id C)
      l = productMap (σ ∘ τ) (id C)
      κ = slice-comparison {C = C} σ τ
      sourceTail = (productMap f (id C) ◁ κ) ∙ comp-assoc k h (productMap f (id C))
      η = productMap-cong (comp-assoc τ σ f) (idIso (id C))
      normalizeShort = isoComp-cong (Coordinates.normalization C f (σ ∘ τ)) (idIso sourceTail)
      normalizeLong = isoComp-cong (idIso η)
        (isoComp-cong (Coordinates.normalization C (f ∘ σ) τ)
          (preWhisker k ◁ Coordinates.normalization C f σ))
      assembled = PairingAssembly.assemble (f ∘ pr₁) (id C ∘ pr₂) h k l κ
        (Coordinates.first C f σ) (Coordinates.second C f σ)
        (Coordinates.first C (f ∘ σ) τ) (Coordinates.second C (f ∘ σ) τ)
        (Coordinates.first C f (σ ∘ τ)) (Coordinates.second C f (σ ∘ τ))
        (comp-assoc τ σ f ▷ pr₁) (idIso (id C) ▷ pr₂)
        (first-coordinate-assoc C f σ τ) (second-coordinate-assoc C f σ τ)
  in invIso normalizeLong ∙ (assembled ∙ normalizeShort)
```

