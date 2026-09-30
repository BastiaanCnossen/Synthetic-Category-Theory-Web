# Pasting and composition of coordinate comparisons

A coordinate square can be transported by postcomposition. Its composite
comparison records the source and target associators explicitly. The following
calculations compare successive transports and transport of a pasted square;
the external pentagon accounts for the reassociations.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
import SCT.VolumeI.Chapter01.Section01.Terminal as Terminal
import SCT.VolumeI.Chapter01.Section01.Products as Products
import SCT.VolumeI.Chapter01.Section02.Coherence as Coherence
import SCT.VolumeI.Chapter01.Section02.Specialization as Specialization
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.FunctorCoherence as FunctorCoherence

import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.CoordinateNaturality as CoordinateNaturality
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PairingNaturality

module SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.CoordinateComparisons
  {c m a : Level} (V : Vocabulary c m a)
  (T : Terminal.TerminalStructure V) (P : Products.ProductData V)
  (PL : Products.ProductLaws V P)
  (S : Coherence.CompositionStructure V T P)
  (VC : Coherence.VerticalCoherence V T P S)
  (W : Coherence.WhiskeringCoherence V T P S)
  (PT : Coherence.PentagonTriangleCoherence V T P S) where

open PairingNaturality V T P PL S VC W using (cancel-right)

open Vocabulary V
open Operations V
open Coherence.CompositionStructure S
open Coherence.Composition V T P S
open Coherence.WhiskeringCoherence W
open Specialization V T P PL S
open Specialization.Units V T P PL S VC
open Specialization.Whiskering V T P PL S W
open Structural V T P PL S W using (whisker-mixed-at; postWhisker-comp-at)
open FunctorCoherence V T P PL S VC W PT using (pentagon-whiskered; cancel-right-reflect)

coordinate-comparison : {R X K C D : CAT}
  (ρ : MAP R X) (f : MAP X C) (π : MAP K C) (h : MAP R K)
  → (π ∘ h) =₁ (f ∘ ρ) → (F : MAP C D)
  → ((F ∘ π) ∘ h) =₁ ((F ∘ f) ∘ ρ)
coordinate-comparison ρ f π h b F =
  (comp-assoc ρ f F) ⁻¹ ∙ ((F ◁ b) ∙ comp-assoc h π F)

open CoordinateNaturality V T P PL S VC W public using (paste-squares; coordinate-at)

private
  cancel-inverse-pair : {C D : CAT} {f g g′ : MAP C D}
    (q : g =₁ g′) (u : f =₁ g)
    → (q ⁻¹ ∙ (q ∙ u)) =₂ u
  cancel-inverse-pair q u = isoComp-unitˡ-at u ∙
    (isoComp-cong (isoComp-inverseˡ-at q) (idIso u) ∙
      (isoComp-assoc-at (q ⁻¹) q u) ⁻¹)

pentagon-left-corner : {C D : CAT} {x₀ x₁ x₂ x₃ x₄ : MAP C D}
  (A : x₁ =₁ x₄) (B : x₀ =₁ x₁) (C′ : x₃ =₁ x₄)
  (D′ : x₂ =₁ x₃) (E : x₀ =₁ x₂)
  → (A ∙ B) =₂ (C′ ∙ (D′ ∙ E))
  → (D′ ⁻¹ ∙ (C′ ⁻¹ ∙ A)) =₂ (E ∙ B ⁻¹)
pentagon-left-corner A B C′ D′ E pentagon =
  let clear : ((A ∙ B) ∙ B ⁻¹) =₂ A
      clear = isoComp-unitʳ-at A ∙
        (isoComp-cong (idIso A) (isoComp-inverseʳ-at B) ∙ isoComp-assoc-at A B (B ⁻¹))
      expandCorner : A =₂ (C′ ∙ (D′ ∙ (E ∙ B ⁻¹)))
      expandCorner = isoComp-cong (idIso C′) (isoComp-assoc-at D′ E (B ⁻¹)) ∙
        (isoComp-assoc-at C′ (D′ ∙ E) (B ⁻¹) ∙
          (isoComp-cong pentagon (idIso (B ⁻¹)) ∙ clear ⁻¹))
  in cancel-inverse-pair D′ (E ∙ B ⁻¹) ∙
    (isoComp-cong (idIso (D′ ⁻¹)) (cancel-inverse-pair C′ (D′ ∙ (E ∙ B ⁻¹))) ∙
      isoComp-cong (idIso (D′ ⁻¹)) (isoComp-cong (idIso (C′ ⁻¹)) expandCorner))
```

Successive postcomposition is governed by three squares: the source
pentagon, associator naturality, and the target pentagon.

```agda
private
  post-inverse : {X C D : CAT} (F : MAP C D) {u v : MAP X C} (α : u =₁ v)
    → (F ◁ α ⁻¹) =₂ ((F ◁ α) ⁻¹)
  post-inverse F {u} α = cancel-right-reflect (F ◁ α)
    ((isoComp-inverseˡ-at (F ◁ α)) ⁻¹ ∙
    (postWhisker-idIso F u ∙
    ((postWhisker F ◁ isoComp-inverseˡ-at α) ∙
      (postWhisker-isoComp-at F (α ⁻¹) α) ⁻¹)))

coordinate-outer-comp : {R X K C D E : CAT}
  (ρ : MAP R X) (s : MAP X C) (π : MAP K C) (h : MAP R K)
  (b : (π ∘ h) =₁ (s ∘ ρ)) (g : MAP C D) (f : MAP D E)
  →
      ((comp-assoc s g f ▷ ρ) ∙ coordinate-comparison ρ s π h b (f ∘ g)) =₂
      (coordinate-comparison ρ (g ∘ s) (g ∘ π) h
        (coordinate-comparison ρ s π h b g) f ∙ (comp-assoc π g f ▷ h))
coordinate-outer-comp ρ s π h b g f =
  let inputLeft = comp-assoc h π (f ∘ g)
      middleLeft = (f ∘ g) ◁ b
      outputLeft = (comp-assoc ρ s (f ∘ g)) ⁻¹
      inputRight = (f ◁ comp-assoc h π g) ∙ comp-assoc h (g ∘ π) f
      middleRight = f ◁ (g ◁ b)
      outputRight = (comp-assoc ρ (g ∘ s) f) ⁻¹ ∙ (f ◁ (comp-assoc ρ s g) ⁻¹)
      atSource = comp-assoc π g f ▷ h
      afterInput = comp-assoc (π ∘ h) g f
      beforeOutput = comp-assoc (s ∘ ρ) g f
      atTarget = comp-assoc s g f ▷ ρ

      inputSquare : (inputRight ∙ atSource) =₂ (afterInput ∙ inputLeft)
      inputSquare = (pentagon-whiskered h π g f) ⁻¹ ∙
        isoComp-assoc-at (f ◁ comp-assoc h π g) (comp-assoc h (g ∘ π) f) atSource

      middleSquare : (middleRight ∙ afterInput) =₂ (beforeOutput ∙ middleLeft)
      middleSquare = (postWhisker-comp-at b g f) ⁻¹

      outputSquare : (outputRight ∙ beforeOutput) =₂ (atTarget ∙ outputLeft)
      outputSquare = pentagon-left-corner beforeOutput (comp-assoc ρ s (f ∘ g))
          (f ◁ comp-assoc ρ s g) (comp-assoc ρ (g ∘ s) f) atTarget
          (pentagon-whiskered ρ s g f) ∙
        (isoComp-assoc-at ((comp-assoc ρ (g ∘ s) f) ⁻¹)
          ((f ◁ comp-assoc ρ s g) ⁻¹) beforeOutput ∙
        isoComp-cong
          (isoComp-cong (idIso ((comp-assoc ρ (g ∘ s) f) ⁻¹)) (post-inverse f (comp-assoc ρ s g)))
          (idIso beforeOutput))

      assembled : ((outputRight ∙ (middleRight ∙ inputRight)) ∙ atSource) =₂
        (atTarget ∙ (outputLeft ∙ (middleLeft ∙ inputLeft)))
      assembled = paste-squares (middleLeft ∙ inputLeft) (middleRight ∙ inputRight)
        outputLeft outputRight atSource beforeOutput atTarget
        (paste-squares inputLeft inputRight middleLeft middleRight
          atSource afterInput beforeOutput inputSquare middleSquare) outputSquare

      outside = (comp-assoc ρ (g ∘ s) f) ⁻¹
      firstImage = f ◁ (comp-assoc ρ s g) ⁻¹
      lastImage = f ◁ comp-assoc h π g
      finalInput = comp-assoc h (g ∘ π) f
      mergeImages : (firstImage ∙ (middleRight ∙ lastImage)) =₂
        (f ◁ coordinate-comparison ρ s π h b g)
      mergeImages = (postWhisker-isoComp-at f ((comp-assoc ρ s g) ⁻¹)
          ((g ◁ b) ∙ comp-assoc h π g)) ⁻¹ ∙
        isoComp-cong (idIso firstImage) ((postWhisker-isoComp-at f (g ◁ b) (comp-assoc h π g)) ⁻¹)

      normalizeRight : (outputRight ∙ (middleRight ∙ inputRight)) =₂
        (coordinate-comparison ρ (g ∘ s) (g ∘ π) h (coordinate-comparison ρ s π h b g) f)
      normalizeRight = isoComp-cong (idIso outside)
        (isoComp-cong mergeImages (idIso finalInput) ∙
        ((isoComp-assoc-at firstImage (middleRight ∙ lastImage) finalInput) ⁻¹ ∙
          isoComp-cong (idIso firstImage) ((isoComp-assoc-at middleRight lastImage finalInput) ⁻¹))) ∙
        isoComp-assoc-at outside firstImage (middleRight ∙ (lastImage ∙ finalInput))
  in isoComp-cong normalizeRight (idIso atSource) ∙ assembled ⁻¹
```

For a pasted coordinate square, compatibility of postwhiskering with
composition and the mixed whiskering square give the corresponding
comparison of the two image pastings.

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
```

A change of substitution also transports a specified projection square.
We postcompose that square, then use the pasting calculation to remove
the intermediate associators.

```agda
coordinate-at-change : {Q R K A B : CAT}
  (F : MAP A B) (π : MAP K A) (h : MAP R K) (t : MAP Q R)
  (s : MAP Q K) (δ : (h ∘ t) =₁ s)
  {q : MAP R A} {v : MAP Q A}
  (b : (π ∘ h) =₁ q) (b′ : (π ∘ s) =₁ v) (c : (q ∘ t) =₁ v)
  → (b′ ∙ (π ◁ δ)) =₂ (c ∙ ((b ▷ t) ∙ (comp-assoc t h π) ⁻¹))
  →
      (coordinate-at F π s b′ ∙ (((F ∘ π) ◁ δ) ∙ comp-assoc t h (F ∘ π))) =₂
      ((F ◁ c) ∙ (comp-assoc t q F ∙ (coordinate-at F π h b ▷ t)))
coordinate-at-change F π h t s δ b b′ c square =
  let leftImage = F ◁ b′
      inputA = comp-assoc s π F
      change = (F ∘ π) ◁ δ
      sourceA = comp-assoc t h (F ∘ π)
      across = F ◁ (π ◁ δ)
      afterA = comp-assoc (h ∘ t) π F
      projected = c ∙ ((b ▷ t) ∙ (comp-assoc t h π) ⁻¹)
      projectImage = (postWhisker F ◁ square) ∙ (postWhisker-isoComp-at F b′ (π ◁ δ)) ⁻¹
      moveInput = isoComp-assoc-at across afterA sourceA ∙
        (isoComp-cong (postWhisker-comp-at δ π F) (idIso sourceA) ∙
          (isoComp-assoc-at inputA change sourceA) ⁻¹)
      removeInner = isoComp-cong projectImage (idIso (afterA ∙ sourceA)) ∙
        (isoComp-assoc-at leftImage across (afterA ∙ sourceA)) ⁻¹
  in post-pasting F π h t b c ∙
    (removeInner ∙ (isoComp-cong (idIso leftImage) moveInput ∙
      isoComp-assoc-at leftImage inputA (change ∙ sourceA)))
```

Postcomposition also preserves the specified comparison for two successive
substitutions. The second form permits an identification of their composite
with another substitution; both forms keep the supplied square explicit.

```agda
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

post-change-comparison : {Q R X A B : CAT}
  (F : MAP A B) (H : MAP X A) (h : MAP R X) (t : MAP Q R)
  (s : MAP Q X) (δ : (h ∘ t) =₁ s)
  {H₁ : MAP R A} {H₂ H₃ : MAP Q A}
  (u : (H ∘ h) =₁ H₁) (v : (H₁ ∘ t) =₁ H₂)
  (w : (H ∘ s) =₁ H₃) (z : H₂ =₁ H₃)
  → (w ∙ ((H ◁ δ) ∙ comp-assoc t h H)) =₂ (z ∙ (v ∙ (u ▷ t)))
  →
      (((F ◁ w) ∙ comp-assoc s H F) ∙ (((F ∘ H) ◁ δ) ∙ comp-assoc t h (F ∘ H))) =₂
      ((F ◁ z) ∙ (((F ◁ v) ∙ comp-assoc t H₁ F) ∙
        (((F ◁ u) ∙ comp-assoc h H F) ▷ t)))
post-change-comparison F H h t s δ u v w z square =
  let image = F ◁ w
      inputA = comp-assoc s H F
      change = (F ∘ H) ◁ δ
      outsideA = comp-assoc t h (F ∘ H)
      across = F ◁ (H ◁ δ)
      middleA = comp-assoc (h ∘ t) H F
      normalization = (isoComp-assoc-at (F ◁ (w ∙ (H ◁ δ))) middleA outsideA) ⁻¹ ∙
        (isoComp-cong ((postWhisker-isoComp-at F w (H ◁ δ)) ⁻¹) (idIso (middleA ∙ outsideA)) ∙
        ((isoComp-assoc-at image across (middleA ∙ outsideA)) ⁻¹ ∙
        (isoComp-cong (idIso image) (isoComp-assoc-at across middleA outsideA) ∙
        (isoComp-cong (idIso image) (isoComp-cong (postWhisker-comp-at δ H F) (idIso outsideA)) ∙
        (isoComp-cong (idIso image) ((isoComp-assoc-at inputA change outsideA) ⁻¹) ∙
          isoComp-assoc-at image inputA (change ∙ outsideA))))))
  in post-iterated-comparison F H h t u v (w ∙ (H ◁ δ)) z
      (square ∙ isoComp-assoc-at w (H ◁ δ) (comp-assoc t h H)) ∙ normalization

```

Successive postcomposition of a coordinate comparison is governed by the
external pentagon and naturality of the associator.

```agda
coordinate-at-outer-composition : {R K X Y Z : CAT}
  (F : MAP Y Z) (G : MAP X Y) (π : MAP K X) (t : MAP R K)
  {p : MAP R X} (b : (π ∘ t) =₁ p)
  → (comp-assoc p G F ∙ coordinate-at (F ∘ G) π t b) =₂
      ((F ◁ coordinate-at G π t b) ∙
        (comp-assoc t (G ∘ π) F ∙ (comp-assoc π G F ▷ t)))
coordinate-at-outer-composition F G π t {p} b =
  let A = comp-assoc p G F
      B = (F ∘ G) ◁ b
      C = comp-assoc t π (F ∘ G)
      D = F ◁ (G ◁ b)
      E = comp-assoc (π ∘ t) G F
      I = F ◁ comp-assoc t π G
      J = comp-assoc t (G ∘ π) F
      K = comp-assoc π G F ▷ t
  in isoComp-cong ((postWhisker-isoComp-at F (G ◁ b) (comp-assoc t π G)) ⁻¹) (idIso (J ∙ K)) ∙
    ((isoComp-assoc-at D I (J ∙ K)) ⁻¹ ∙
    (isoComp-cong (idIso D) (pentagon-whiskered t π G F) ∙
    (isoComp-assoc-at D E C ∙
    (isoComp-cong (postWhisker-comp-at b G F) (idIso C) ∙ (isoComp-assoc-at A B C) ⁻¹))))
```

A chosen reverse comparison can be used to solve the image square for its
upper side. The cancellation witness is an input: the statement therefore
applies to the specified reverse comparison, without replacing it by an
unspecified inverse with the same endpoints.

```agda
post-change-with-inverse : {Q R X A B : CAT}
  (F : MAP A B) (H : MAP X A) (h : MAP R X) (t : MAP Q R)
  (s : MAP Q X) (δ : (h ∘ t) =₁ s)
  {H₁ : MAP R A} {H₂ H₃ : MAP Q A}
  (u : (H ∘ h) =₁ H₁) (v : (H₁ ∘ t) =₁ H₂)
  (w : (H ∘ s) =₁ H₃) (z : H₂ =₁ H₃)
  (square : (w ∙ ((H ◁ δ) ∙ comp-assoc t h H)) =₂ (z ∙ (v ∙ (u ▷ t))))
  (back : (F ∘ H₁) =₁ ((F ∘ H) ∘ h))
  (inverse : (((F ◁ u) ∙ comp-assoc h H F) ∙ back) =₂ idIso (F ∘ H₁))
  → ((F ◁ z) ∙ ((F ◁ v) ∙ comp-assoc t H₁ F)) =₂
      (((F ◁ w) ∙ comp-assoc s H F) ∙
        (((F ∘ H) ◁ δ) ∙ (comp-assoc t h (F ∘ H) ∙ (back ▷ t))))
post-change-with-inverse F H h t s δ {H₁} u v w z square back inverse =
  let A = comp-assoc t h (F ∘ H)
      forward = (F ◁ u) ∙ comp-assoc h H F
      before = forward ▷ t
      backT = back ▷ t
      target = (F ◁ z) ∙ ((F ◁ v) ∙ comp-assoc t H₁ F)
      short = (F ◁ w) ∙ comp-assoc s H F
      step = (F ∘ H) ◁ δ
      cancel = preWhisker-idIso (F ∘ H₁) t ∙
        ((preWhisker t ◁ inverse) ∙ (preWhisker-isoComp-at forward back t) ⁻¹)
      compare = (isoComp-assoc-at (F ◁ z) ((F ◁ v) ∙ comp-assoc t H₁ F) before) ⁻¹ ∙
        post-change-comparison F H h t s δ u v w z square
  in isoComp-cong (idIso short) (isoComp-assoc-at step A backT) ∙
    (isoComp-assoc-at short (step ∙ A) backT ∙
    (isoComp-cong (compare ⁻¹) (idIso backT) ∙
    ((isoComp-assoc-at target before backT) ⁻¹ ∙
    (isoComp-cong (idIso target) (cancel ⁻¹) ∙ (isoComp-unitʳ-at target) ⁻¹))))
```
