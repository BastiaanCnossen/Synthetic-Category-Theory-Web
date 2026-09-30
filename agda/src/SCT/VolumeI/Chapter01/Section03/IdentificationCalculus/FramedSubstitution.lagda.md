# Changing frames in a substitution square

Suppose a coordinate comparison is normalized by a fixed frame `v`, and
its composite has the specified projection square. Moving the frame through
substitution then reduces the composition law to that projection square.
The comparison identifying the composite substitution is retained explicitly.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
import SCT.VolumeI.Chapter01.Section01.Terminal as Terminal
import SCT.VolumeI.Chapter01.Section01.Products as Products
import SCT.VolumeI.Chapter01.Section02.Coherence as Coherence
import SCT.VolumeI.Chapter01.Section02.Specialization as Specialization
import SCT.VolumeI.Chapter01.Section02.Isomorphisms as Isomorphisms
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PairingNaturality

module SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.FramedSubstitution
  {c m a : Level} (V : Vocabulary c m a)
  (T₀ : Terminal.TerminalStructure V) (P : Products.ProductData V)
  (PL : Products.ProductLaws V P)
  (S₀ : Coherence.CompositionStructure V T₀ P)
  (VC : Coherence.VerticalCoherence V T₀ P S₀)
  (W : Coherence.WhiskeringCoherence V T₀ P S₀) where

open PairingNaturality V T₀ P PL S₀ VC W using (cancel-right)

open Vocabulary V
open Operations V
open Coherence.WhiskeringCoherence W using (postWhisker-idIso)
open Coherence.CompositionStructure S₀
open Coherence.Composition V T₀ P S₀
open Specialization V T₀ P PL S₀
open Specialization.Units V T₀ P PL S₀ VC
open Specialization.Whiskering V T₀ P PL S₀ W
open Structural V T₀ P PL S₀ W using (preWhisker-comp-at; whisker-mixed-at)
open Isomorphisms V T₀ P PL S₀ VC W using (reassociateFour; cancel-inverse)

module Composition {K₀ K₁ K₂ C : CAT}
  (s : MAP K₁ K₀) (t : MAP K₂ K₁) (st : MAP K₂ K₀)
  (κ : (s ∘ t) =₁ st)
  (q π : MAP K₀ C) (q₁ : MAP K₁ C) (q₂ : MAP K₂ C)
  (v : q =₁ π)
  (b : (π ∘ s) =₁ q₁) (bst : (π ∘ st) =₁ q₂)
  (S : (q ∘ s) =₁ q₁) (T : (q₁ ∘ t) =₁ q₂)
  (Sst : (q ∘ st) =₁ q₂)
  (normalize-first : S =₂ (b ∙ (v ▷ s)))
  (normalize-composite : Sst =₂ (bst ∙ (v ▷ st)))
  (projection : (bst ∙ (π ◁ κ)) =₂
    (T ∙ ((b ▷ t) ∙ (comp-assoc t s π) ⁻¹))) where

  private
    Aq = comp-assoc t s q
    Aπ = comp-assoc t s π
    vv = (v ▷ s) ▷ t
    normalized = T ∙ (S ▷ t)

  leftStart :
    (Sst ∙ ((q ◁ κ) ∙ Aq)) =₂
    ((bst ∙ (π ◁ κ)) ∙ ((v ▷ (s ∘ t)) ∙ Aq))
  leftStart = (isoComp-assoc-at bst (π ◁ κ) ((v ▷ (s ∘ t)) ∙ Aq)) ⁻¹ ∙
    (isoComp-cong (idIso bst) (isoComp-assoc-at (π ◁ κ) (v ▷ (s ∘ t)) Aq) ∙
    (isoComp-cong (idIso bst) (isoComp-cong (interchange-at v κ) (idIso Aq)) ∙
    (reassociateFour bst (v ▷ st) (q ◁ κ) Aq ∙
      isoComp-cong (normalize-composite) (idIso ((q ◁ κ) ∙ Aq)))))

  middle :
    ((bst ∙ (π ◁ κ)) ∙ ((v ▷ (s ∘ t)) ∙ Aq)) =₂
    ((T ∙ ((b ▷ t) ∙ Aπ ⁻¹)) ∙ (Aπ ∙ vv))
  middle = isoComp-cong (projection)
    ((preWhisker-comp-at v s t) ⁻¹)

  cancellation :
    ((T ∙ ((b ▷ t) ∙ Aπ ⁻¹)) ∙ (Aπ ∙ vv)) =₂
    (T ∙ ((b ▷ t) ∙ vv))
  cancellation = isoComp-cong (idIso T)
      (isoComp-cong (idIso (b ▷ t))
        (isoComp-unitˡ-at vv ∙
          (isoComp-cong (isoComp-inverseˡ-at Aπ) (idIso vv) ∙
            (isoComp-assoc-at (Aπ ⁻¹) Aπ vv) ⁻¹)) ∙
        isoComp-assoc-at (b ▷ t) (Aπ ⁻¹) (Aπ ∙ vv)) ∙
    isoComp-assoc-at T ((b ▷ t) ∙ Aπ ⁻¹) (Aπ ∙ vv)

  rightFinish : (T ∙ ((b ▷ t) ∙ vv)) =₂ normalized
  rightFinish = isoComp-cong (idIso T)
    ((preWhisker t ◁ (normalize-first) ⁻¹) ∙
      (preWhisker-isoComp-at b (v ▷ s) t) ⁻¹)
  compatible : (Sst ∙ ((q ◁ κ) ∙ comp-assoc t s q)) =₂ (T ∙ (S ▷ t))
  compatible = rightFinish ∙ (cancellation ∙ (middle ∙ leftStart))
```

A commutative square of specified frames remains commutative after
postcomposition. Writing the restriction comparison in the reverse direction
introduces an inverse and two associators. The following calculation keeps
that particular route, including the given square, explicit.

```agda
post-frame-square : {Q R A B : CAT} (e : MAP A B) (s : MAP Q R)
  {H J : MAP R A} {H′ J′ K L : MAP Q A}
  (before : H =₁ J) (after : H′ =₁ J′) (finish : J′ =₁ L)
  (out : K =₁ L) (pre : (J ∘ s) =₁ K) (κ : (H ∘ s) =₁ H′)
  → ((finish ∙ after) ∙ κ) =₂ ((out ∙ pre) ∙ (before ▷ s))
  → ((e ◁ finish) ∙ (e ◁ after)) =₂
    ((e ◁ out) ∙ (((e ◁ pre) ∙ comp-assoc s J e) ∙
      (((e ◁ before) ▷ s) ∙ ((comp-assoc s H e) ⁻¹ ∙ (e ◁ κ ⁻¹)))))
post-frame-square e s {H} {J} before after finish out pre κ comparison-square =
  (let changed = out ∙ pre
       x = e ◁ out
       y = e ◁ pre
       A = comp-assoc s J e
       b = (e ◁ before) ▷ s
       Aold = comp-assoc s H e
       B = Aold ⁻¹
       c = e ◁ κ ⁻¹
       d = e ◁ (before ▷ s)
       natural = whisker-mixed-at before s e
       collapse = isoComp-cong (idIso d) (cancel-inverse Aold c) ∙
         (isoComp-assoc-at d Aold (B ∙ c) ∙
         (isoComp-cong natural (idIso (B ∙ c)) ∙
           (isoComp-assoc-at A b (B ∙ c)) ⁻¹))
       normalize = isoComp-cong (idIso x)
         (isoComp-cong (idIso y) collapse ∙ isoComp-assoc-at y A (b ∙ (B ∙ c)))
       merge = (postWhisker-isoComp-at e out (pre ∙ ((before ▷ s) ∙ κ ⁻¹))) ⁻¹ ∙
         isoComp-cong (idIso x)
           ((postWhisker-isoComp-at e pre ((before ▷ s) ∙ κ ⁻¹)) ⁻¹ ∙
             isoComp-cong (idIso y) ((postWhisker-isoComp-at e (before ▷ s) (κ ⁻¹)) ⁻¹))
       solve = cancel-right κ (finish ∙ after) ∙
         (isoComp-cong (comparison-square ⁻¹) (idIso (κ ⁻¹)) ∙
         ((isoComp-assoc-at changed (before ▷ s) (κ ⁻¹)) ⁻¹ ∙
           (isoComp-assoc-at out pre ((before ▷ s) ∙ κ ⁻¹)) ⁻¹))
     in postWhisker-isoComp-at e finish after ∙
     ((postWhisker e ◁ solve) ∙ (merge ∙ normalize))) ⁻¹
```

The forward image comparison cancels the reverse comparison obtained by
inverting the given comparison before postcomposition. This keeps the
particular inverse route used by restriction explicit.

```agda
post-comparison-inverse : {Q R A B : CAT}
  (e : MAP A B) (H : MAP R A) (s : MAP Q R)
  {H′ : MAP Q A} (κ : (H ∘ s) =₁ H′)
  → (((e ◁ κ) ∙ comp-assoc s H e) ∙
      ((comp-assoc s H e) ⁻¹ ∙ (e ◁ κ ⁻¹))) =₂ idIso (e ∘ H′)
post-comparison-inverse e H s {H′} κ =
  let A = comp-assoc s H e
  in postWhisker-idIso e H′ ∙
    ((postWhisker e ◁ isoComp-inverseʳ-at κ) ∙
    ((postWhisker-isoComp-at e κ (κ ⁻¹)) ⁻¹ ∙
    (isoComp-cong (idIso (e ◁ κ)) (cancel-inverse A (e ◁ κ ⁻¹)) ∙
      isoComp-assoc-at (e ◁ κ) A (A ⁻¹ ∙ (e ◁ κ ⁻¹)))))
```
