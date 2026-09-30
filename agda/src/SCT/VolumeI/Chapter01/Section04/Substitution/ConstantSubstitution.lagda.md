# Successive substitutions in a constant diagram

The comparison `const-pre` is built from the chosen terminal comparison.
Its composition law follows by comparing the two maps to the terminal
category, then applying the general projection-pasting calculation. No
uniqueness of identifications in the target category is used.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.IteratedPairing as Iterated

module SCT.VolumeI.Chapter01.Section04.Substitution.ConstantSubstitution
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section04.SquareCalculus.ProjectionSquares 𝒯 using (compose-base; lift-base; lift-compose)
open import SCT.VolumeI.Chapter01.Section08.ProductCalculus.ProjectionBaseCalculus 𝒯 using (lift-assoc)
open PN vocabulary terminal products productLaws composition vertical whiskering using (move-square)
open Iterated vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle using (pre-inverse-at)
import SCT.VolumeI.Chapter01.Section03.Equivalences as TerminalComparisons
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural
open Structural vocabulary terminal products productLaws composition whiskering using (postWhisker-comp-at)
open TerminalComparisons.TerminalTargets vocabulary terminal products productLaws composition
  using (terminal-Iso₂)

abstract
  const-pre-compose : {X Y Z A : CAT} (x : MAP One A) (h : MAP X Y) (k : MAP Y Z) →
    (compose-base (const x) k (const-pre x k) h (const-pre x h)) =₂
      (const-pre x (k ∘ h))
  const-pre-compose {X} {Y} {Z} x h k =
    isoComp-cong
      (postWhisker x ◁ terminal-Iso₂
        (compose-base (terminate Z) k (terminal-iso _ _) h (terminal-iso _ _))
        (terminal-iso _ _))
      (idIso (comp-assoc (k ∘ h) (terminate Z) x)) ∙
    lift-compose x (terminate Z) k h (terminal-iso _ _) (terminal-iso _ _)
```

```agda
constant-image : {A B : CAT} (X : CAT) (r : MAP A B) (x : MAP One A) →
  (r ∘ const {P = X} x) =₁ (const (r ∘ x))
constant-image X r x = (comp-assoc (terminate X) x r) ⁻¹

abstract
  constant-image-pre : {X Y A B : CAT} (h : MAP X Y) (r : MAP A B) (x : MAP One A) →
    (const-pre (r ∘ x) h ∙ (constant-image Y r x ▷ h)) =₂
      (constant-image X r x ∙ lift-base r (const x) h (const-pre x h))
  constant-image-pre {X} {Y} h r x =
    (move-square (comp-assoc (terminate X) x r) (const-pre (r ∘ x) h)
      (lift-base r (const x) h (const-pre x h)) (comp-assoc (terminate Y) x r ▷ h)
      (lift-assoc (terminate Y) (terminate X) h (terminal-iso _ _) x r)) ⁻¹ ∙
    isoComp-cong (idIso (const-pre (r ∘ x) h)) (pre-inverse-at (comp-assoc (terminate Y) x r) h)
```

The source normalization is natural under an identification of parameter
maps. The only uniqueness used is again that of identifications into the
terminal category.

```agda
abstract
  const-pre-natural : {Γ B C : CAT} (x : Obj-abs C) {b d : MAP Γ B} (σ : b =₁ d) →
    (const-pre x d ∙ (const x ◁ σ)) =₂ const-pre x b
  const-pre-natural {Γ} {B} x {b} {d} σ =
    isoComp-cong
      ((postWhisker x ◁ terminal-Iso₂ (ηd ∙ (terminate B ◁ σ)) ηb) ∙
        (postWhisker-isoComp-at x ηd (terminate B ◁ σ)) ⁻¹)
      (idIso (comp-assoc b (terminate B) x)) ∙
    ((isoComp-assoc-at (x ◁ ηd) (x ◁ (terminate B ◁ σ)) (comp-assoc b (terminate B) x)) ⁻¹ ∙
    (isoComp-cong (idIso (x ◁ ηd)) (postWhisker-comp-at σ (terminate B) x) ∙
      isoComp-assoc-at (x ◁ ηd) (comp-assoc d (terminate B) x) (const x ◁ σ)))
    where
    ηb : (terminate B ∘ b) =₁ terminate Γ
    ηb = terminal-iso (terminate B ∘ b) (terminate Γ)
    ηd : (terminate B ∘ d) =₁ terminate Γ
    ηd = terminal-iso (terminate B ∘ d) (terminate Γ)
```
