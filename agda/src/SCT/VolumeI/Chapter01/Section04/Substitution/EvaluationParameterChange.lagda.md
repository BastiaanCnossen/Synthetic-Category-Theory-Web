# Evaluation and restriction of its input

We keep the comparison `mapUncurry-at` chosen in the composition module.
The proof first checks the product-pair comparison on its two coordinates,
then transports that calculation through evaluation.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.Setup as Setup
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section04.Composition as MapComposition
import SCT.VolumeI.Chapter01.Section04.CompositionCalculus.CompositionNaturality as CompositionNaturality
import SCT.VolumeI.Chapter01.Section04.ProductCalculus.ProductAssociativity as ProductAssociativity
import SCT.VolumeI.Chapter01.Section04.ProductCalculus.ProductSubstitution as ProductSubstitution
import SCT.VolumeI.Chapter01.Section04.ProductCalculus.ProductSecondCoordinate as ProductSecondCoordinate
import SCT.VolumeI.Chapter01.Section04.Substitution.Compatibility as Compatibility
import SCT.VolumeI.Chapter01.Section04.Currying as Currying
import SCT.VolumeI.Chapter01.Section02.Isomorphisms as Isomorphisms
import SCT.VolumeI.Chapter01.Section04.Substitution.ApplicationRestriction as ApplicationRestriction
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingCoherence as PairingCoherence
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PairingNaturality
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.ProductFunctorUnits as ProductFunctorUnits
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural

module SCT.VolumeI.Chapter01.Section04.Substitution.EvaluationParameterChange
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open Setup 𝒯
open Mapping.MappingAnimae M
open Currying 𝒯 M using (mapUncurry-restrict)
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

module AtCoordinates {Γ X Y C : CAT} (f : MAP X Y) (p : MAP Γ X) (x : MAP Γ C) where

  first : ((f ∘ pr₁) ∘ pair p x) =₁ (f ∘ p)
  first = coordinate-at f pr₁ (pair p x) (pair-β₁ p x)

  second : ((id C ∘ pr₂) ∘ pair p x) =₁ x
  second = comp-unitˡ x ∙ coordinate-at (id C) pr₂ (pair p x) (pair-β₂ p x)

  comparison : (productMap f (id C) ∘ pair p x) =₁ (pair (f ∘ p) x)
  comparison = pair-cong (idIso (f ∘ p)) (comp-unitˡ x) ∙ productMap-pair f (id C) p x

  normalized : (productMap f (id C) ∘ pair p x) =₁ (pair (f ∘ p) x)
  normalized = pair-cong first second ∙ pair-pre (f ∘ pr₁) (id C ∘ pr₂) (pair p x)

  normalization : comparison =₂ normalized
  normalization =
    isoComp-cong
      (pair-cong-Iso₂ (isoComp-unitˡ-at first) (idIso second) ∙
        (pair-cong-comp (idIso (f ∘ p)) first (comp-unitˡ x)
          (coordinate-at (id C) pr₂ (pair p x) (pair-β₂ p x))) ⁻¹) (idIso _) ∙
    (isoComp-assoc-at (pair-cong (idIso (f ∘ p)) (comp-unitˡ x))
      (pair-cong first (coordinate-at (id C) pr₂ (pair p x) (pair-β₂ p x)))
      (pair-pre (f ∘ pr₁) (id C ∘ pr₂) (pair p x))) ⁻¹

first-restriction : {R Γ X Y C : CAT} (f : MAP X Y) (p : MAP Γ X) (x : MAP Γ C) (r : MAP R Γ)
  →
      (AtCoordinates.first f (p ∘ r) (x ∘ r) ∙
        (((f ∘ pr₁) ◁ pair-pre p x r) ∙ comp-assoc r (pair p x) (f ∘ pr₁))) =₂
      (comp-assoc r p f ∙ (AtCoordinates.first f p x ▷ r))
first-restriction f p x r =
  isoComp-unitˡ-at _ ∙
  (isoComp-cong (postWhisker-idIso f (p ∘ r)) (idIso _) ∙
    coordinate-at-change f pr₁ (pair p x) r (pair (p ∘ r) (x ∘ r)) (pair-pre p x r)
      (pair-β₁ p x) (pair-β₁ (p ∘ r) (x ∘ r)) (idIso (p ∘ r))
      ((isoComp-unitˡ-at _) ⁻¹ ∙ pair-pre-triangle₁ p x r))

second-restriction : {R Γ X Y C : CAT} (f : MAP X Y) (p : MAP Γ X) (x : MAP Γ C) (r : MAP R Γ)
  →
      (AtCoordinates.second f (p ∘ r) (x ∘ r) ∙
        (((id C ∘ pr₂) ◁ pair-pre p x r) ∙ comp-assoc r (pair p x) (id C ∘ pr₂))) =₂
      (AtCoordinates.second f p x ▷ r)
second-restriction {C = C} f p x r =
  let before = coordinate-at (id C) pr₂ (pair p x) (pair-β₂ p x)
      after = coordinate-at (id C) pr₂ (pair (p ∘ r) (x ∘ r)) (pair-β₂ (p ∘ r) (x ∘ r))
      change = ((id C ∘ pr₂) ◁ pair-pre p x r) ∙ comp-assoc r (pair p x) (id C ∘ pr₂)
      coordinate = isoComp-unitˡ-at _ ∙
        (isoComp-cong (postWhisker-idIso (id C) (x ∘ r)) (idIso _) ∙
          coordinate-at-change (id C) pr₂ (pair p x) r (pair (p ∘ r) (x ∘ r)) (pair-pre p x r)
            (pair-β₂ p x) (pair-β₂ (p ∘ r) (x ∘ r)) (idIso (x ∘ r))
            ((isoComp-unitˡ-at _) ⁻¹ ∙ pair-pre-triangle₂ p x r))
  in (preWhisker-isoComp-at (comp-unitˡ x) before r) ⁻¹ ∙
    (isoComp-cong (left-unitor-comp r x) (idIso (before ▷ r)) ∙
    ((isoComp-assoc-at (comp-unitˡ (x ∘ r)) (comp-assoc r x (id C)) (before ▷ r)) ⁻¹ ∙
    (isoComp-cong (idIso (comp-unitˡ (x ∘ r))) coordinate ∙
      isoComp-assoc-at (comp-unitˡ (x ∘ r)) after change)))

at-comparison-restriction : {R Γ X Y C : CAT}
  (f : MAP X Y) (p : MAP Γ X) (x : MAP Γ C) (r : MAP R Γ)
  →
      (AtCoordinates.comparison f (p ∘ r) (x ∘ r) ∙
        ((productMap f (id C) ◁ pair-pre p x r) ∙ comp-assoc r (pair p x) (productMap f (id C)))) =₂
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
        (isoComp-cong (idIso η) ((isoComp-unitˡ-at (u ▷ r)) ⁻¹) ∙ first-restriction f p x r)
        ((isoComp-unitˡ-at _) ⁻¹ ∙
          ((isoComp-unitˡ-at (v ▷ r)) ⁻¹ ∙ second-restriction f p x r))
      long-normal = isoComp-cong (idIso (pair-cong η θ))
        (isoComp-cong (isoComp-unitˡ-at base ∙ isoComp-cong (pair-cong-id ((f ∘ p) ∘ r) (x ∘ r)) (idIso base))
          (preWhisker r ◁ (AtCoordinates.normalization f p x) ⁻¹))
  in long-normal ∙
    (assembled ∙ isoComp-cong (AtCoordinates.normalization f (p ∘ r) (x ∘ r)) (idIso _))

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

mapUncurry-at-restriction : {R Γ X C D : CAT}
  (f : MAP X (Map C D)) (p : MAP Γ X) (x : MAP Γ C) (r : MAP R Γ)
  →
      (applyTerm-cong (comp-assoc r p f) (idIso (x ∘ r)) ∙
        (applyTerm-pre (f ∘ p) x r ∙ (mapUncurry-at f p x ▷ r))) =₂
      (mapUncurry-at f (p ∘ r) (x ∘ r) ∙
        ((mapUncurry f ◁ pair-pre p x r) ∙ comp-assoc r (pair p x) (mapUncurry f)))
mapUncurry-at-restriction {C = C} f p x r =
  (post-change-comparison mapEval (productMap f (id C)) (pair p x) r
    (pair (p ∘ r) (x ∘ r)) (pair-pre p x r)
    (AtCoordinates.comparison f p x) (pair-pre (f ∘ p) x r)
    (AtCoordinates.comparison f (p ∘ r) (x ∘ r))
    (pair-cong (comp-assoc r p f) (idIso (x ∘ r)))
    (at-comparison-restriction f p x r)) ⁻¹

module AsApplyChange {P Q C D : CAT} (f : MAP P (Map C D)) (σ : MAP Q P) where

  s : MAP (Q × C) (P × C)
  s = productMap σ (id C)

  κ : (productMap f (id C) ∘ s) =₁ (productMap (f ∘ σ) (id C))
  κ = slice-comparison f σ

  before : (productMap f (id C)) =₁ (pair (f ∘ pr₁) pr₂)
  before = pair-cong (idIso (f ∘ pr₁)) (comp-unitˡ pr₂)

  after : (productMap (f ∘ σ) (id C)) =₁ (pair ((f ∘ σ) ∘ pr₁) pr₂)
  after = pair-cong (idIso ((f ∘ σ) ∘ pr₁)) (comp-unitˡ pr₂)

  first : ((f ∘ pr₁) ∘ s) =₁ (f ∘ (σ ∘ pr₁))
  first = (f ◁ pair-β₁ (σ ∘ pr₁) (id C ∘ pr₂)) ∙ comp-assoc s pr₁ f

  second : (pr₂ ∘ s) =₁ pr₂
  second = comp-unitˡ pr₂ ∙ pair-β₂ (σ ∘ pr₁) (id C ∘ pr₂)

  finish : _=₁_ {C = Q × C} (pair ((f ∘ σ) ∘ pr₁) pr₂) (pair (f ∘ (σ ∘ pr₁)) pr₂)
  finish = pair-cong (comp-assoc pr₁ σ f) (idIso pr₂)

  changed : (pair (f ∘ pr₁) pr₂ ∘ s) =₁ (pair (f ∘ (σ ∘ pr₁)) pr₂)
  changed = pair-cong first second ∙ pair-pre (f ∘ pr₁) pr₂ s

  comparison-square : ((finish ∙ after) ∙ κ) =₂ (changed ∙ (before ▷ s))
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
        firstNormalize = (isoComp-cong (idIso first) (preWhisker-idIso (f ∘ pr₁) s)) ⁻¹ ∙
          ((isoComp-unitʳ-at first) ⁻¹ ∙
            (cancel-forward A first ∙ isoComp-cong (idIso A) (isoComp-unitˡ-at e)))
        secondNormalize = (isoComp-assoc-at unitAfter
            (pair-β₂ (σ ∘ pr₁) (id C ∘ pr₂)) (unitBefore ▷ s)) ⁻¹ ∙
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
            ((pair-pre-natural-inputs (idIso (f ∘ pr₁)) unitBefore s) ⁻¹) ∙
            isoComp-assoc-at (pair-cong first second) (pair-pre (f ∘ pr₁) pr₂ s) (before ▷ s))
    in normalizeRight ⁻¹ ∙
      (isoComp-cong (pair-cong-Iso₂ firstNormalize secondNormalize) (idIso base) ∙ normalizeLeft)

  comparison :
    (applyTerm-cong (comp-assoc pr₁ σ f) (idIso pr₂) ∙ mapUncurry-as-apply (f ∘ σ)) =₂
    (applyTerm-cong first second ∙
      (applyTerm-pre (f ∘ pr₁) pr₂ s ∙ ((mapUncurry-as-apply f ▷ s) ∙ mapUncurry-restrict f σ)))
  comparison =
    (let e = mapEval
         out = pair-cong first second
         pre = pair-pre (f ∘ pr₁) pr₂ s
         x = e ◁ out
         y = e ◁ pre
         A = comp-assoc s (pair (f ∘ pr₁) pr₂) e
         b = (e ◁ before) ▷ s
         Aold = comp-assoc s (productMap f (id C)) e
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

mapUncurry-as-apply-parameter-change : {P Q C D : CAT}
  (f : MAP P (Map C D)) (σ : MAP Q P)
  → let s = productMap σ (id C)
        a = (f ◁ pair-β₁ (σ ∘ pr₁) (id C ∘ pr₂)) ∙ comp-assoc s pr₁ f
        b = comp-unitˡ pr₂ ∙ pair-β₂ (σ ∘ pr₁) (id C ∘ pr₂)
    in
      (applyTerm-cong (comp-assoc pr₁ σ f) (idIso pr₂) ∙ mapUncurry-as-apply (f ∘ σ)) =₂
      (applyTerm-cong a b ∙
        (applyTerm-pre (f ∘ pr₁) pr₂ s ∙ ((mapUncurry-as-apply f ▷ s) ∙ mapUncurry-restrict f σ)))
mapUncurry-as-apply-parameter-change = AsApplyChange.comparison
```
