# Assembling pairing comparisons

A comparison between successive substitutions is determined by its two
coordinate comparisons. We retain both routes explicitly and normalize each
to a paired coordinate comparison followed by the common substitution base.
This calculation uses only the specified pairing functoriality laws.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
import SCT.VolumeI.Chapter01.Section01.Terminal as Terminal
import SCT.VolumeI.Chapter01.Section01.Products as Products
import SCT.VolumeI.Chapter01.Section02.Coherence as Coherence
import SCT.VolumeI.Chapter01.Section02.Specialization as Specialization
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingInterface as Interface

module SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingAssembly
  {c m a : Level} (V : Vocabulary c m a)
  (T : Terminal.TerminalStructure V) (P : Products.ProductData V)
  (PL : Products.ProductLaws V P)
  (S : Coherence.CompositionStructure V T P)
  (VC : Coherence.VerticalCoherence V T P S)
  (W : Coherence.WhiskeringCoherence V T P S)
  (O : Interface.PairingOperations V T P S)
  (F : Interface.PairingFunctoriality V T P S O) where

open Vocabulary V
open Operations V
open Products.ProductData P
open Coherence.CompositionStructure S
open Coherence.Composition V T P S
open Specialization V T P PL S hiding (pair-cong; pair-pre)
open Specialization.Units V T P PL S VC
open Specialization.Whiskering V T P PL S W
open Interface.PairingOperations O
open Interface.PairingFunctoriality F

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

Changing the two coordinate frames gives a square for the paired comparison.
Normalize the given substitution comparison and both boundary routes, then
apply the two supplied coordinate squares.

```agda
module FramedPairing {Q R A B : CAT} (s : MAP Q R)
  {a₀ a₁ : MAP R A} {b₀ b₁ : MAP R B}
  {a₂ a₃ a₄ : MAP Q A} {b₂ b₃ b₄ : MAP Q B}
  (u : a₀ =₁ a₁) (v : b₀ =₁ b₁)
  (u′ : a₂ =₁ a₃) (v′ : b₂ =₁ b₃)
  (η : a₃ =₁ a₄) (θ : b₃ =₁ b₄)
  (e : (a₀ ∘ s) =₁ a₂) (d : (b₀ ∘ s) =₁ b₂)
  (first : (a₁ ∘ s) =₁ a₄) (second : (b₁ ∘ s) =₁ b₄)
  (κ : (pair a₀ b₀ ∘ s) =₁ (pair a₂ b₂))
  (normalization : κ =₂ (pair-cong e d ∙ pair-pre a₀ b₀ s)) where

  before = pair-cong u v
  after = pair-cong u′ v′
  finish = pair-cong η θ
  changed = pair-cong first second ∙ pair-pre a₁ b₁ s

  comparison-square :
    (η ∙ (u′ ∙ e)) =₂ (first ∙ (u ▷ s))
    → (θ ∙ (v′ ∙ d)) =₂ (second ∙ (v ▷ s))
    → ((finish ∙ after) ∙ κ) =₂ (changed ∙ (before ▷ s))
  comparison-square firstNormalize secondNormalize =
    let base = pair-pre a₀ b₀ s
        normalizeLeft = combine-pair η θ (u′ ∙ e) (v′ ∙ d) base ∙
          (isoComp-cong (idIso finish) (combine-pair u′ v′ e d base) ∙
          (isoComp-assoc-at finish after (pair-cong e d ∙ base) ∙
            isoComp-cong (idIso (finish ∙ after)) normalization))
        normalizeRight = combine-pair first second (u ▷ s) (v ▷ s) base ∙
          (isoComp-cong (idIso (pair-cong first second))
            ((pair-pre-natural-inputs u v s) ⁻¹) ∙
            isoComp-assoc-at (pair-cong first second) (pair-pre a₁ b₁ s) (before ▷ s))
    in normalizeRight ⁻¹ ∙
      (isoComp-cong (pair-cong-Iso₂ firstNormalize secondNormalize) (idIso base) ∙ normalizeLeft)
```
