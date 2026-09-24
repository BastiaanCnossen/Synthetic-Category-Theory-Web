# Associativity of product substitution

We compare the two iterated substitutions using the existing product
comparison. The pairing calculation below reduces this to its two
coordinate comparisons, preserving the specified external associator.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.Setup as Setup
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section04.Compatibility as Compatibility
import SCT.VolumeI.Chapter01.Section04.ProductSubstitution as ProductSubstitution
import SCT.VolumeI.Chapter01.Section04.ProductSecondCoordinate as ProductSecondCoordinate
import SCT.VolumeI.Chapter01.Section03.PairingCoherence as PairingCoherence
import SCT.VolumeI.Chapter01.Section03.PairingNaturality as PairingNaturality
import SCT.VolumeI.Chapter01.Section03.IteratedPairing as IteratedPairing
import SCT.VolumeI.Chapter01.Section03.Structural as Structural

module SCT.VolumeI.Chapter01.Section04.ProductAssociativity
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
  (α : a₁ =₁ a₂) (β : b₁ =₁ b₂)
  (γ : a₀ =₁ a₁) (δ : b₀ =₁ b₁)
  (base : source =₁ (pair a₀ b₀))
  → (pair-cong α β ∙ (pair-cong γ δ ∙ base)) =₂
      (pair-cong (α ∙ γ) (β ∙ δ) ∙ base)
combine-pair α β γ δ base =
  isoComp-cong ((pair-cong-comp α γ β δ) ⁻¹) (idIso base) ∙
    (isoComp-assoc-at (pair-cong α β) (pair-cong γ δ) base) ⁻¹

module PairingAssembly {Q R X A B : CAT}
  (b : MAP X A) (c : MAP X B) (r : MAP R X) (t : MAP Q R)
  (s : MAP Q X) (δ : (r ∘ t) =₁ s)
  {b₁ : MAP R A} {c₁ : MAP R B} {b₂ b₃ : MAP Q A} {c₂ c₃ : MAP Q B}
  (u : (b ∘ r) =₁ b₁) (v : (c ∘ r) =₁ c₁)
  (w : (b₁ ∘ t) =₁ b₂) (z : (c₁ ∘ t) =₁ c₂)
  (a : (b ∘ s) =₁ b₃) (d : (c ∘ s) =₁ c₃)
  (η : b₂ =₁ b₃) (θ : c₂ =₁ c₃) where

  base : ((pair b c ∘ r) ∘ t) =₁ (pair ((b ∘ r) ∘ t) ((c ∘ r) ∘ t))
  base = pair-pre (b ∘ r) (c ∘ r) t ∙ (pair-pre b c r ▷ t)

  shortFirst : ((b ∘ r) ∘ t) =₁ b₃
  shortFirst = a ∙ ((b ◁ δ) ∙ comp-assoc t r b)

  shortSecond : ((c ∘ r) ∘ t) =₁ c₃
  shortSecond = d ∙ ((c ◁ δ) ∙ comp-assoc t r c)

  longFirst : ((b ∘ r) ∘ t) =₁ b₃
  longFirst = η ∙ (w ∙ (u ▷ t))

  longSecond : ((c ∘ r) ∘ t) =₁ c₃
  longSecond = θ ∙ (z ∙ (v ▷ t))

  short : ((pair b c ∘ r) ∘ t) =₁ (pair b₃ c₃)
  short = (pair-cong a d ∙ pair-pre b c s) ∙
    ((pair b c ◁ δ) ∙ comp-assoc t r (pair b c))

  long : ((pair b c ∘ r) ∘ t) =₁ (pair b₃ c₃)
  long = pair-cong η θ ∙ ((pair-cong w z ∙ pair-pre b₁ c₁ t) ∙
    ((pair-cong u v ∙ pair-pre b c r) ▷ t))

  short-normalization : short =₂ (pair-cong shortFirst shortSecond ∙ base)
  short-normalization =
    let paired = pair-cong a d
        changed = pair-cong (b ◁ δ) (c ◁ δ)
        A = comp-assoc t r (pair b c)
        pairedA = pair-cong (comp-assoc t r b) (comp-assoc t r c)
        substitute = isoComp-assoc-at changed (pair-pre b c (r ∘ t)) A ∙
          (isoComp-cong ((pair-pre-natural-substitution b c δ) ⁻¹) (idIso A) ∙
            (isoComp-assoc-at (pair-pre b c s) (pair b c ◁ δ) A) ⁻¹)
        iterate = isoComp-cong (idIso changed) (pair-pre-iterated b c r t)
        combineInner = combine-pair (b ◁ δ) (c ◁ δ)
          (comp-assoc t r b) (comp-assoc t r c) base
    in combine-pair a d ((b ◁ δ) ∙ comp-assoc t r b) ((c ◁ δ) ∙ comp-assoc t r c) base ∙
      (isoComp-cong (idIso paired) (combineInner ∙ (iterate ∙ substitute)) ∙
        isoComp-assoc-at paired (pair-pre b c s) ((pair b c ◁ δ) ∙ A))

  intermediate-normalization :
    ((pair-cong w z ∙ pair-pre b₁ c₁ t) ∙ ((pair-cong u v ∙ pair-pre b c r) ▷ t)) =₂
    (pair-cong (w ∙ (u ▷ t)) (z ∙ (v ▷ t)) ∙ base)
  intermediate-normalization =
    let outer = pair-cong w z
        before = pair-pre b c r ▷ t
        middle = pair-pre b₁ c₁ t
        input = pair-cong u v ▷ t
        output = pair-cong (u ▷ t) (v ▷ t)
        exchange = isoComp-assoc-at output (pair-pre (b ∘ r) (c ∘ r) t) before ∙
          (isoComp-cong ((pair-pre-natural-inputs u v t) ⁻¹) (idIso before) ∙
            (isoComp-assoc-at middle input before) ⁻¹)
    in combine-pair w z (u ▷ t) (v ▷ t) base ∙
      (isoComp-cong (idIso outer) exchange ∙
        (isoComp-assoc-at outer middle (input ∙ before) ∙
          isoComp-cong (idIso (outer ∙ middle))
            (preWhisker-isoComp-at (pair-cong u v) (pair-pre b c r) t)))

  long-normalization : long =₂ (pair-cong longFirst longSecond ∙ base)
  long-normalization =
    combine-pair η θ (w ∙ (u ▷ t)) (z ∙ (v ▷ t)) base ∙
      isoComp-cong (idIso (pair-cong η θ)) intermediate-normalization

  assemble : shortFirst =₂ longFirst → shortSecond =₂ longSecond → short =₂ long
  assemble first second = long-normalization ⁻¹ ∙
    (isoComp-cong (pair-cong-Iso₂ first second) (idIso base) ∙ short-normalization)
```

Postcomposition carries a pasted coordinate square to the pasted image
square. The external pentagon accounts for the three reassociations.

```agda
cancel-inverse-tail : {X Y : CAT} {a b c : MAP X Y}
  (α : b =₁ c) (β : b =₁ a)
  → ((α ∙ β ⁻¹) ∙ β) =₂ α
cancel-inverse-tail α β = isoComp-unitʳ-at α ∙
  (isoComp-cong (idIso α) (isoComp-inverseˡ-at β) ∙ isoComp-assoc-at α (β ⁻¹) β)

post-pasting : {Q R K A B : CAT}
  (F : MAP A B) (π : MAP K A) (h : MAP R K) (k : MAP Q R)
  {q : MAP R A} {v : MAP Q A}
  (b : (π ∘ h) =₁ q) (c : (q ∘ k) =₁ v)
  →
      ((F ◁ (c ∙ ((b ▷ k) ∙ (comp-assoc k h π) ⁻¹))) ∙
        (comp-assoc (h ∘ k) π F ∙ comp-assoc k h (F ∘ π))) =₂
      ((F ◁ c) ∙ (comp-assoc k q F ∙ (((F ◁ b) ∙ comp-assoc h π F) ▷ k)))
post-pasting F π h k {q} b c =
  let A = comp-assoc k h π
      B = comp-assoc k (π ∘ h) F
      C = comp-assoc h π F ▷ k
      D = comp-assoc k q F
      e = F ◁ c
      d = F ◁ (b ▷ k)
      p = F ◁ (c ∙ ((b ▷ k) ∙ A ⁻¹))
      cancellation = cancel-inverse-tail (c ∙ (b ▷ k)) A ∙
        isoComp-cong ((isoComp-assoc-at c (b ▷ k) (A ⁻¹)) ⁻¹) (idIso A)
      join = postWhisker-isoComp-at F c (b ▷ k) ∙
        ((postWhisker F ◁ cancellation) ∙
          (postWhisker-isoComp-at F (c ∙ ((b ▷ k) ∙ A ⁻¹)) A) ⁻¹)
      mixed = (whisker-mixed-at b k F) ⁻¹
      finish = isoComp-cong (idIso e)
        (isoComp-cong (idIso D)
          ((preWhisker-isoComp-at (F ◁ b) (comp-assoc h π F) k) ⁻¹) ∙
          isoComp-assoc-at D ((F ◁ b) ▷ k) C)
      exchange = isoComp-cong (idIso e) (isoComp-cong mixed (idIso C)) ∙
        (isoComp-cong (idIso e) ((isoComp-assoc-at d B C) ⁻¹) ∙
          isoComp-assoc-at e d (B ∙ C))
  in finish ∙ (exchange ∙
    (isoComp-cong join (idIso (B ∙ C)) ∙
      ((isoComp-assoc-at p (F ◁ A) (B ∙ C)) ⁻¹ ∙
        isoComp-cong (idIso p) (pentagon-whiskered k h π F))))

cancel-forward : {X Y : CAT} {a b c : MAP X Y}
  (α : a =₁ b) (β : c =₁ b)
  → (α ∙ (α ⁻¹ ∙ β)) =₂ β
cancel-forward α β = isoComp-unitˡ-at β ∙
  (isoComp-cong (isoComp-inverseʳ-at α) (idIso β) ∙
    (isoComp-assoc-at α (α ⁻¹) β) ⁻¹)

first-coordinate-assoc : {Q R X Z : CAT} (C : CAT)
  (f : MAP X Z) (σ : MAP R X) (τ : MAP Q R)
  →
      (Coordinates.first C f (σ ∘ τ) ∙
        (((f ∘ pr₁) ◁ slice-comparison {C = C} σ τ) ∙
          comp-assoc (productMap τ (id C)) (productMap σ (id C)) (f ∘ pr₁))) =₂
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
      outside = (comp-assoc pr₁ (σ ∘ τ) f) ⁻¹
      leftImage = f ◁ b′
      inputA = comp-assoc l pr₁ f
      change = (f ∘ pr₁) ◁ κ
      sourceA = comp-assoc k h (f ∘ pr₁)
      across = f ◁ (pr₁ ◁ κ)
      afterA = comp-assoc (h ∘ k) pr₁ f
      projected = c ∙ ((b ▷ k) ∙ (comp-assoc k h pr₁) ⁻¹)
      projectImage = (postWhisker f ◁ Coordinates.projection₁ C σ τ) ∙
        (postWhisker-isoComp-at f b′ (pr₁ ◁ κ)) ⁻¹
      moveInput = isoComp-assoc-at across afterA sourceA ∙
        (isoComp-cong (postWhisker-comp-at κ pr₁ f) (idIso sourceA) ∙
          (isoComp-assoc-at inputA change sourceA) ⁻¹)
      removeInner = isoComp-cong projectImage (idIso (afterA ∙ sourceA)) ∙
        (isoComp-assoc-at leftImage across (afterA ∙ sourceA)) ⁻¹
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
        (preWhisker-isoComp-at sourceCorner u k) ⁻¹
      normalizeLong = isoComp-cong (idIso outside)
        (isoComp-assoc-at (f ◁ c) (comp-assoc k (σ ∘ pr₁) f) (imageBefore ▷ k)) ∙
        (isoComp-assoc-at outside ((f ◁ c) ∙ comp-assoc k (σ ∘ pr₁) f) (imageBefore ▷ k) ∙
          (isoComp-cong (idIso nextCoordinate) simplifyCorner ∙
            (isoComp-assoc-at nextCoordinate (sourceCorner ▷ k) (u ▷ k) ∙
              (isoComp-cong outerSquare (idIso (u ▷ k)) ∙
                (isoComp-assoc-at η w (u ▷ k)) ⁻¹))))
  in normalizeLong ⁻¹ ∙ normalizeShort
```

We now apply the assembly to the two projections of the chosen product
substitution comparison. The normalization witnesses return the conclusion
to `slice-comparison` itself.

```agda
slice-comparison-assoc : {Q R X Z : CAT} (C : CAT)
  (f : MAP X Z) (σ : MAP R X) (τ : MAP Q R)
  →
      (slice-comparison {C = C} f (σ ∘ τ) ∙
        ((productMap f (id C) ◁ slice-comparison {C = C} σ τ) ∙
          comp-assoc (productMap τ (id C)) (productMap σ (id C)) (productMap f (id C)))) =₂
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
  in normalizeLong ⁻¹ ∙ (assembled ∙ normalizeShort)
```

