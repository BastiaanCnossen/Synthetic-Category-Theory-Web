# Evaluation and restriction of its input

We keep the comparison `mapUncurry-at` chosen in the composition module.
The proof first checks the product-pair comparison on its two coordinates,
then transports that calculation through evaluation.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.Setup as Setup
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section03.Composition as MapComposition
import SCT.VolumeI.Chapter01.Section03.CompositionNaturality as CompositionNaturality
import SCT.VolumeI.Chapter01.Section03.ProductAssociativity as ProductAssociativity
import SCT.VolumeI.Chapter01.Section03.ProductSubstitution as ProductSubstitution
import SCT.VolumeI.Chapter01.Section03.ProductSecondCoordinate as ProductSecondCoordinate
import SCT.VolumeI.Chapter01.Section03.Compatibility as Compatibility
import SCT.VolumeI.Chapter01.Section03.Currying as Currying
import SCT.VolumeI.Chapter01.Section01.Isomorphisms as Isomorphisms
import SCT.VolumeI.Chapter01.Section03.ApplicationRestriction as ApplicationRestriction
import SCT.VolumeI.Chapter01.Section02.PairingCoherence as PairingCoherence
import SCT.VolumeI.Chapter01.Section02.PairingNaturality as PairingNaturality
import SCT.VolumeI.Chapter01.Section02.ProductFunctorUnits as ProductFunctorUnits
import SCT.VolumeI.Chapter01.Section02.Structural as Structural

module SCT.VolumeI.Chapter01.Section03.EvaluationParameterChange
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open Setup 𝒯
open Mapping.MappingAnimae M
open Currying 𝒯 M using (mapUncurry-pre)
open MapComposition 𝒯 M
open CompositionNaturality 𝒯 M using (coordinate-at)
open ProductAssociativity 𝒯 M using (post-pasting; module PairingAssembly; combine-pair; cancel-forward)
open Compatibility 𝒯 M using (slice-comparison)
module ProductCoordinates = ProductSubstitution.Coordinates 𝒯 M
open ProductSecondCoordinate 𝒯 M using (second-normalization)
open ApplicationRestriction 𝒯 M using (post-iterated-comparison)
open PairingCoherence vocabulary terminal products productLaws composition vertical whiskering
  using (pair-cong-comp; pair-cong-Iso₂; pair-cong-id; pair-pre-triangle₁; pair-pre-triangle₂)
open PairingNaturality vocabulary terminal products productLaws composition vertical whiskering
  using (cancel-right; pair-pre-natural-inputs)
open ProductFunctorUnits vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (left-unitor-comp)
open Structural vocabulary terminal products productLaws composition whiskering
  using (postWhisker-comp-at; whisker-mixed-at)
open Isomorphisms vocabulary terminal products productLaws composition vertical whiskering
  using (cancel-inverse)

coordinate-at-change : {Q R K A B : CAT}
  (F : MAP A B) (π : MAP K A) (h : MAP R K) (t : MAP Q R)
  (s : MAP Q K) (δ : =₁ (h ∘ t) s)
  {q : MAP R A} {v : MAP Q A}
  (b : =₁ (π ∘ h) q) (b′ : =₁ (π ∘ s) v) (c : =₁ (q ∘ t) v)
  → =₂ (b′ ∙ (π ◁ δ)) (c ∙ ((b ▷ t) ∙ invIso (comp-assoc t h π)))
  → =₂
      (coordinate-at F π s b′ ∙ (((F ∘ π) ◁ δ) ∙ comp-assoc t h (F ∘ π)))
      ((F ◁ c) ∙ (comp-assoc t q F ∙ (coordinate-at F π h b ▷ t)))
coordinate-at-change F π h t s δ b b′ c square =
  let leftImage = F ◁ b′
      inputA = comp-assoc s π F
      change = (F ∘ π) ◁ δ
      sourceA = comp-assoc t h (F ∘ π)
      across = F ◁ (π ◁ δ)
      afterA = comp-assoc (h ∘ t) π F
      projected = c ∙ ((b ▷ t) ∙ invIso (comp-assoc t h π))
      projectImage = (postWhisker F ◁ square) ∙ invIso (postWhisker-isoComp-at F b′ (π ◁ δ))
      moveInput = isoComp-assoc-at across afterA sourceA ∙
        (isoComp-cong (postWhisker-comp-at δ π F) (idIso sourceA) ∙
          invIso (isoComp-assoc-at inputA change sourceA))
      removeInner = isoComp-cong projectImage (idIso (afterA ∙ sourceA)) ∙
        invIso (isoComp-assoc-at leftImage across (afterA ∙ sourceA))
  in post-pasting F π h t b c ∙
    (removeInner ∙ (isoComp-cong (idIso leftImage) moveInput ∙
      isoComp-assoc-at leftImage inputA (change ∙ sourceA)))

module AtCoordinates {Γ X Y C : CAT} (f : MAP X Y) (p : MAP Γ X) (x : MAP Γ C) where

  first : =₁ ((f ∘ pr₁) ∘ pair p x) (f ∘ p)
  first = coordinate-at f pr₁ (pair p x) (pair-β₁ p x)

  second : =₁ ((id C ∘ pr₂) ∘ pair p x) x
  second = comp-unitˡ x ∙ coordinate-at (id C) pr₂ (pair p x) (pair-β₂ p x)

  comparison : =₁ (productMap f (id C) ∘ pair p x) (pair (f ∘ p) x)
  comparison = pair-cong (idIso (f ∘ p)) (comp-unitˡ x) ∙ productMap-pair f (id C) p x

  normalized : =₁ (productMap f (id C) ∘ pair p x) (pair (f ∘ p) x)
  normalized = pair-cong first second ∙ pair-pre (f ∘ pr₁) (id C ∘ pr₂) (pair p x)

  normalization : =₂ comparison normalized
  normalization =
    isoComp-cong
      (pair-cong-Iso₂ (isoComp-unitˡ-at first) (idIso second) ∙
        invIso (pair-cong-comp (idIso (f ∘ p)) first (comp-unitˡ x)
          (coordinate-at (id C) pr₂ (pair p x) (pair-β₂ p x)))) (idIso _) ∙
    invIso (isoComp-assoc-at (pair-cong (idIso (f ∘ p)) (comp-unitˡ x))
      (pair-cong first (coordinate-at (id C) pr₂ (pair p x) (pair-β₂ p x)))
      (pair-pre (f ∘ pr₁) (id C ∘ pr₂) (pair p x)))

first-restriction : {R Γ X Y C : CAT} (f : MAP X Y) (p : MAP Γ X) (x : MAP Γ C) (r : MAP R Γ)
  → =₂
      (AtCoordinates.first f (p ∘ r) (x ∘ r) ∙
        (((f ∘ pr₁) ◁ pair-pre p x r) ∙ comp-assoc r (pair p x) (f ∘ pr₁)))
      (comp-assoc r p f ∙ (AtCoordinates.first f p x ▷ r))
first-restriction f p x r =
  isoComp-unitˡ-at _ ∙
  (isoComp-cong (postWhisker-idIso f (p ∘ r)) (idIso _) ∙
    coordinate-at-change f pr₁ (pair p x) r (pair (p ∘ r) (x ∘ r)) (pair-pre p x r)
      (pair-β₁ p x) (pair-β₁ (p ∘ r) (x ∘ r)) (idIso (p ∘ r))
      (invIso (isoComp-unitˡ-at _) ∙ pair-pre-triangle₁ p x r))

second-restriction : {R Γ X Y C : CAT} (f : MAP X Y) (p : MAP Γ X) (x : MAP Γ C) (r : MAP R Γ)
  → =₂
      (AtCoordinates.second f (p ∘ r) (x ∘ r) ∙
        (((id C ∘ pr₂) ◁ pair-pre p x r) ∙ comp-assoc r (pair p x) (id C ∘ pr₂)))
      (AtCoordinates.second f p x ▷ r)
second-restriction {C = C} f p x r =
  let before = coordinate-at (id C) pr₂ (pair p x) (pair-β₂ p x)
      after = coordinate-at (id C) pr₂ (pair (p ∘ r) (x ∘ r)) (pair-β₂ (p ∘ r) (x ∘ r))
      change = ((id C ∘ pr₂) ◁ pair-pre p x r) ∙ comp-assoc r (pair p x) (id C ∘ pr₂)
      coordinate = isoComp-unitˡ-at _ ∙
        (isoComp-cong (postWhisker-idIso (id C) (x ∘ r)) (idIso _) ∙
          coordinate-at-change (id C) pr₂ (pair p x) r (pair (p ∘ r) (x ∘ r)) (pair-pre p x r)
            (pair-β₂ p x) (pair-β₂ (p ∘ r) (x ∘ r)) (idIso (x ∘ r))
            (invIso (isoComp-unitˡ-at _) ∙ pair-pre-triangle₂ p x r))
  in invIso (preWhisker-isoComp-at (comp-unitˡ x) before r) ∙
    (isoComp-cong (left-unitor-comp r x) (idIso (before ▷ r)) ∙
    (invIso (isoComp-assoc-at (comp-unitˡ (x ∘ r)) (comp-assoc r x (id C)) (before ▷ r)) ∙
    (isoComp-cong (idIso (comp-unitˡ (x ∘ r))) coordinate ∙
      isoComp-assoc-at (comp-unitˡ (x ∘ r)) after change)))

at-comparison-restriction : {R Γ X Y C : CAT}
  (f : MAP X Y) (p : MAP Γ X) (x : MAP Γ C) (r : MAP R Γ)
  → =₂
      (AtCoordinates.comparison f (p ∘ r) (x ∘ r) ∙
        ((productMap f (id C) ◁ pair-pre p x r) ∙ comp-assoc r (pair p x) (productMap f (id C))))
      (pair-cong (comp-assoc r p f) (idIso (x ∘ r)) ∙
        (pair-pre (f ∘ p) x r ∙ (AtCoordinates.comparison f p x ▷ r)))
at-comparison-restriction {C = C} f p x r =
  let u = AtCoordinates.first f p x
      v = AtCoordinates.second f p x
      w = idIso ((f ∘ p) ∘ r)
      z = idIso (x ∘ r)
      a = AtCoordinates.first f (p ∘ r) (x ∘ r)
      d = AtCoordinates.second f (p ∘ r) (x ∘ r)
      η = comp-assoc r p f
      θ = idIso (x ∘ r)
      base = pair-pre (f ∘ p) x r
      assembled = PairingAssembly.assemble (f ∘ pr₁) (id C ∘ pr₂)
        (pair p x) r (pair (p ∘ r) (x ∘ r)) (pair-pre p x r)
        u v w z a d η θ
        (isoComp-cong (idIso η) (invIso (isoComp-unitˡ-at (u ▷ r))) ∙ first-restriction f p x r)
        (invIso (isoComp-unitˡ-at _) ∙
          (invIso (isoComp-unitˡ-at (v ▷ r)) ∙ second-restriction f p x r))
      long-normal = isoComp-cong (idIso (pair-cong η θ))
        (isoComp-cong (isoComp-unitˡ-at base ∙ isoComp-cong (pair-cong-id ((f ∘ p) ∘ r) (x ∘ r)) (idIso base))
          (preWhisker r ◁ invIso (AtCoordinates.normalization f p x)))
  in long-normal ∙
    (assembled ∙ isoComp-cong (AtCoordinates.normalization f (p ∘ r) (x ∘ r)) (idIso _))

post-change-comparison : {Q R X A B : CAT}
  (F : MAP A B) (H : MAP X A) (h : MAP R X) (t : MAP Q R)
  (s : MAP Q X) (δ : =₁ (h ∘ t) s)
  {H₁ : MAP R A} {H₂ H₃ : MAP Q A}
  (u : =₁ (H ∘ h) H₁) (v : =₁ (H₁ ∘ t) H₂)
  (w : =₁ (H ∘ s) H₃) (z : =₁ H₂ H₃)
  → =₂ (w ∙ ((H ◁ δ) ∙ comp-assoc t h H)) (z ∙ (v ∙ (u ▷ t)))
  → =₂
      (((F ◁ w) ∙ comp-assoc s H F) ∙ (((F ∘ H) ◁ δ) ∙ comp-assoc t h (F ∘ H)))
      ((F ◁ z) ∙ (((F ◁ v) ∙ comp-assoc t H₁ F) ∙
        (((F ◁ u) ∙ comp-assoc h H F) ▷ t)))
post-change-comparison F H h t s δ u v w z square =
  let image = F ◁ w
      inputA = comp-assoc s H F
      change = (F ∘ H) ◁ δ
      outsideA = comp-assoc t h (F ∘ H)
      across = F ◁ (H ◁ δ)
      middleA = comp-assoc (h ∘ t) H F
      normalization = invIso (isoComp-assoc-at (F ◁ (w ∙ (H ◁ δ))) middleA outsideA) ∙
        (isoComp-cong (invIso (postWhisker-isoComp-at F w (H ◁ δ))) (idIso (middleA ∙ outsideA)) ∙
        (invIso (isoComp-assoc-at image across (middleA ∙ outsideA)) ∙
        (isoComp-cong (idIso image) (isoComp-assoc-at across middleA outsideA) ∙
        (isoComp-cong (idIso image) (isoComp-cong (postWhisker-comp-at δ H F) (idIso outsideA)) ∙
        (isoComp-cong (idIso image) (invIso (isoComp-assoc-at inputA change outsideA)) ∙
          isoComp-assoc-at image inputA (change ∙ outsideA))))))
  in post-iterated-comparison F H h t u v (w ∙ (H ◁ δ)) z
      (square ∙ isoComp-assoc-at w (H ◁ δ) (comp-assoc t h H)) ∙ normalization

mapUncurry-at-restriction : {R Γ X C D : CAT}
  (f : MAP X (Map C D)) (p : MAP Γ X) (x : MAP Γ C) (r : MAP R Γ)
  → =₂
      (applyTerm-cong (comp-assoc r p f) (idIso (x ∘ r)) ∙
        (applyTerm-pre (f ∘ p) x r ∙ (mapUncurry-at f p x ▷ r)))
      (mapUncurry-at f (p ∘ r) (x ∘ r) ∙
        ((mapUncurry f ◁ pair-pre p x r) ∙ comp-assoc r (pair p x) (mapUncurry f)))
mapUncurry-at-restriction {C = C} f p x r = invIso
  (post-change-comparison mapEval (productMap f (id C)) (pair p x) r
    (pair (p ∘ r) (x ∘ r)) (pair-pre p x r)
    (AtCoordinates.comparison f p x) (pair-pre (f ∘ p) x r)
    (AtCoordinates.comparison f (p ∘ r) (x ∘ r))
    (pair-cong (comp-assoc r p f) (idIso (x ∘ r)))
    (at-comparison-restriction f p x r))

module AsApplyChange {P Q C D : CAT} (f : MAP P (Map C D)) (σ : MAP Q P) where

  s : MAP (Q × C) (P × C)
  s = productMap σ (id C)

  κ : =₁ (productMap f (id C) ∘ s) (productMap (f ∘ σ) (id C))
  κ = slice-comparison f σ

  before : =₁ (productMap f (id C)) (pair (f ∘ pr₁) pr₂)
  before = pair-cong (idIso (f ∘ pr₁)) (comp-unitˡ pr₂)

  after : =₁ (productMap (f ∘ σ) (id C)) (pair ((f ∘ σ) ∘ pr₁) pr₂)
  after = pair-cong (idIso ((f ∘ σ) ∘ pr₁)) (comp-unitˡ pr₂)

  first : =₁ ((f ∘ pr₁) ∘ s) (f ∘ (σ ∘ pr₁))
  first = (f ◁ pair-β₁ (σ ∘ pr₁) (id C ∘ pr₂)) ∙ comp-assoc s pr₁ f

  second : =₁ (pr₂ ∘ s) pr₂
  second = comp-unitˡ pr₂ ∙ pair-β₂ (σ ∘ pr₁) (id C ∘ pr₂)

  finish : =₁ {C = Q × C} (pair ((f ∘ σ) ∘ pr₁) pr₂) (pair (f ∘ (σ ∘ pr₁)) pr₂)
  finish = pair-cong (comp-assoc pr₁ σ f) (idIso pr₂)

  changed : =₁ (pair (f ∘ pr₁) pr₂ ∘ s) (pair (f ∘ (σ ∘ pr₁)) pr₂)
  changed = pair-cong first second ∙ pair-pre (f ∘ pr₁) pr₂ s

  comparison-square : =₂ ((finish ∙ after) ∙ κ) (changed ∙ (before ▷ s))
  comparison-square =
    let A = comp-assoc pr₁ σ f
        e = ProductCoordinates.first C f σ
        d = ProductCoordinates.second C f σ
        unitBefore = comp-unitˡ pr₂
        unitAfter = comp-unitˡ pr₂
        base = pair-pre (f ∘ pr₁) (id C ∘ pr₂) s
        leftFirst = A ∙ (idIso ((f ∘ σ) ∘ pr₁) ∙ e)
        leftSecond = idIso pr₂ ∙ (unitAfter ∙ d)
        rightFirst = first ∙ (idIso (f ∘ pr₁) ▷ s)
        rightSecond = second ∙ (unitBefore ▷ s)
        firstNormalize = invIso (isoComp-cong (idIso first) (preWhisker-idIso (f ∘ pr₁) s)) ∙
          (invIso (isoComp-unitʳ-at first) ∙
            (cancel-forward A first ∙ isoComp-cong (idIso A) (isoComp-unitˡ-at e)))
        secondNormalize = invIso (isoComp-assoc-at unitAfter
            (pair-β₂ (σ ∘ pr₁) (id C ∘ pr₂)) (unitBefore ▷ s)) ∙
          (isoComp-cong (idIso unitAfter) (second-normalization C f σ) ∙
            isoComp-unitˡ-at (unitAfter ∙ d))
        normalizeLeft = combine-pair A (idIso pr₂)
            (idIso ((f ∘ σ) ∘ pr₁) ∙ e) (unitAfter ∙ d) base ∙
          (isoComp-cong (idIso finish)
              (combine-pair (idIso ((f ∘ σ) ∘ pr₁)) unitAfter e d base) ∙
          (isoComp-assoc-at finish after (pair-cong e d ∙ base) ∙
            isoComp-cong (idIso (finish ∙ after)) (ProductCoordinates.normalization C f σ)))
        normalizeRight = combine-pair first second
            (idIso (f ∘ pr₁) ▷ s) (unitBefore ▷ s) base ∙
          (isoComp-cong (idIso (pair-cong first second))
            (invIso (pair-pre-natural-inputs (idIso (f ∘ pr₁)) unitBefore s)) ∙
            isoComp-assoc-at (pair-cong first second) (pair-pre (f ∘ pr₁) pr₂ s) (before ▷ s))
    in invIso normalizeRight ∙
      (isoComp-cong (pair-cong-Iso₂ firstNormalize secondNormalize) (idIso base) ∙ normalizeLeft)

  comparison : =₂
    (applyTerm-cong (comp-assoc pr₁ σ f) (idIso pr₂) ∙ mapUncurry-as-apply (f ∘ σ))
    (applyTerm-cong first second ∙
      (applyTerm-pre (f ∘ pr₁) pr₂ s ∙ ((mapUncurry-as-apply f ▷ s) ∙ mapUncurry-pre f σ)))
  comparison = invIso
    (let e = mapEval
         out = pair-cong first second
         pre = pair-pre (f ∘ pr₁) pr₂ s
         x = e ◁ out
         y = e ◁ pre
         A = comp-assoc s (pair (f ∘ pr₁) pr₂) e
         b = (e ◁ before) ▷ s
         Aold = comp-assoc s (productMap f (id C)) e
         B = invIso Aold
         c = e ◁ invIso κ
         d = e ◁ (before ▷ s)
         natural = whisker-mixed-at before s e
         collapse = isoComp-cong (idIso d) (cancel-inverse Aold c) ∙
           (isoComp-assoc-at d Aold (B ∙ c) ∙
           (isoComp-cong natural (idIso (B ∙ c)) ∙
             invIso (isoComp-assoc-at A b (B ∙ c))))
         normalize = isoComp-cong (idIso x)
           (isoComp-cong (idIso y) collapse ∙ isoComp-assoc-at y A (b ∙ (B ∙ c)))
         merge = invIso (postWhisker-isoComp-at e out (pre ∙ ((before ▷ s) ∙ invIso κ))) ∙
           isoComp-cong (idIso x)
             (invIso (postWhisker-isoComp-at e pre ((before ▷ s) ∙ invIso κ)) ∙
               isoComp-cong (idIso y) (invIso (postWhisker-isoComp-at e (before ▷ s) (invIso κ))))
         solve = cancel-right κ (finish ∙ after) ∙
           (isoComp-cong (invIso comparison-square) (idIso (invIso κ)) ∙
           (invIso (isoComp-assoc-at changed (before ▷ s) (invIso κ)) ∙
             invIso (isoComp-assoc-at out pre ((before ▷ s) ∙ invIso κ))))
     in postWhisker-isoComp-at e finish after ∙
       ((postWhisker e ◁ solve) ∙ (merge ∙ normalize)))

mapUncurry-as-apply-parameter-change : {P Q C D : CAT}
  (f : MAP P (Map C D)) (σ : MAP Q P)
  → let s = productMap σ (id C)
        a = (f ◁ pair-β₁ (σ ∘ pr₁) (id C ∘ pr₂)) ∙ comp-assoc s pr₁ f
        b = comp-unitˡ pr₂ ∙ pair-β₂ (σ ∘ pr₁) (id C ∘ pr₂)
    in =₂
      (applyTerm-cong (comp-assoc pr₁ σ f) (idIso pr₂) ∙ mapUncurry-as-apply (f ∘ σ))
      (applyTerm-cong a b ∙
        (applyTerm-pre (f ∘ pr₁) pr₂ s ∙ ((mapUncurry-as-apply f ▷ s) ∙ mapUncurry-pre f σ)))
mapUncurry-as-apply-parameter-change = AsApplyChange.comparison
```
