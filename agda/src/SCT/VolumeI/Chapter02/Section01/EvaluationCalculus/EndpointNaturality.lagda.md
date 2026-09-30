# Naturality of endpoint evaluation

The comparison between evaluating a curried family and restricting its
uncurried diagram is natural in that family. Retaining this square lets
us lift comparisons without losing the specified endpoint identifications.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories

module SCT.VolumeI.Chapter02.Section01.EvaluationCalculus.EndpointNaturality
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter02.Section01.EvaluationCalculus.EndpointEvaluation 𝒯 M ℱ public
open import SCT.VolumeI.Chapter01.Section04.Uncurrying 𝒯 M using (productMap-pair)
import SCT.VolumeI.Chapter01.Section03.Equivalences as TerminalComparisons
open TerminalComparisons.TerminalTargets vocabulary terminal products productLaws composition
  using (terminal-Iso₂)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ComparisonSquares 𝒯 using (quotient-square; post-square)
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingCoherence as PC
open PN vocabulary terminal products productLaws composition vertical whiskering
  using (pair-pre-natural-inputs; pair-pre-natural-substitution; move-square)
open Structural vocabulary terminal products productLaws composition whiskering
open PC vocabulary terminal products productLaws composition vertical whiskering
  using (pair-cong-Iso₂; pair-cong-comp)

application-natural : {X Y Z W : CAT} (p : MAP Y Z) (r : MAP X Y)
  {q : MAP X Z} (ε : (p ∘ r) =₁ q)
  {F G : MAP Z W} (α : F =₁ G) →
  (((G ◁ ε) ∙ comp-assoc r p G) ∙ ((α ▷ p) ▷ r)) =₂
    ((α ▷ q) ∙ ((F ◁ ε) ∙ comp-assoc r p F))
application-natural p r ε {F} {G} α = paste-squares
  (comp-assoc r p F) (comp-assoc r p G) (F ◁ ε) (G ◁ ε)
  ((α ▷ p) ▷ r) (α ▷ (p ∘ r)) (α ▷ _)
  (preWhisker-comp-at α p r) ((interchange-at α ε) ⁻¹)

product-pair-natural : {X A B C D : CAT} {f f′ : MAP A C} {g g′ : MAP B D}
  (α : f =₁ f′) (β : g =₁ g′) (u : MAP X A) (v : MAP X B) →
  (productMap-pair f′ g′ u v ∙ (productMap-cong α β ▷ pair u v)) =₂
    (pair-cong (α ▷ u) (β ▷ v) ∙ productMap-pair f g u v)
product-pair-natural {f = f} {f′} {g} {g′} α β u v = paste-squares
  (pair-pre (f ∘ pr₁) (g ∘ pr₂) (pair u v))
  (pair-pre (f′ ∘ pr₁) (g′ ∘ pr₂) (pair u v))
  (pair-cong bf bg) (pair-cong bf′ bg′)
  (productMap-cong α β ▷ pair u v)
  (pair-cong ((α ▷ pr₁) ▷ pair u v) ((β ▷ pr₂) ▷ pair u v))
  (pair-cong (α ▷ u) (β ▷ v))
  ((pair-pre-natural-inputs (α ▷ pr₁) (β ▷ pr₂) (pair u v)) ⁻¹)
  (pair-square bf bf′ bg bg′ _ _ _ _
    (application-natural pr₁ (pair u v) (pair-β₁ u v) α)
    (application-natural pr₂ (pair u v) (pair-β₂ u v) β))
  where
  bf = (f ◁ pair-β₁ u v) ∙ comp-assoc (pair u v) pr₁ f
  bf′ = (f′ ◁ pair-β₁ u v) ∙ comp-assoc (pair u v) pr₁ f′
  bg = (g ◁ pair-β₂ u v) ∙ comp-assoc (pair u v) pr₂ g
  bg′ = (g′ ◁ pair-β₂ u v) ∙ comp-assoc (pair u v) pr₂ g′

constant-input : {X Y C : CAT} (x : Obj-abs C) {h k : MAP X Y} (α : h =₁ k) →
  (const-pre x k ∙ (const x ◁ α)) =₂ (idIso (const x) ∙ const-pre x h)
constant-input {X} {Y} x {h} {k} α = paste-squares
  (comp-assoc h (terminate Y) x) (comp-assoc k (terminate Y) x)
  (x ◁ th) (x ◁ tk) (const x ◁ α) (x ◁ (terminate Y ◁ α)) (idIso (const x))
  (postWhisker-comp-at α (terminate Y) x)
  ((isoComp-unitˡ-at (x ◁ th)) ⁻¹ ∙
    ((postWhisker x ◁ terminal-Iso₂ (tk ∙ (terminate Y ◁ α)) th) ∙
      (postWhisker-isoComp-at x tk (terminate Y ◁ α)) ⁻¹))
  where
  th = terminal-iso (terminate Y ∘ h) (terminate X)
  tk = terminal-iso (terminate Y ∘ k) (terminate X)

module Insertion {X Y I : CAT} (x : Obj-abs I) {h k : MAP X Y} (α : h =₁ k) where
  input-h = pair-pre (id Y) (const x) h
  input-k = pair-pre (id Y) (const x) k
  finish-h = pair-cong (comp-unitˡ h) (const-pre x h)
  finish-k = pair-cong (comp-unitˡ k) (const-pre x k)
  result = pair-cong α (idIso (const x))

  first : ((finish-k ∙ input-k) ∙ (insert x ◁ α)) =₂ (result ∙ (finish-h ∙ input-h))
  first = paste-squares input-h input-k finish-h finish-k
    (insert x ◁ α) (pair-cong (id Y ◁ α) (const x ◁ α)) result
    ((pair-pre-natural-substitution (id Y) (const x) α) ⁻¹)
    (pair-square (comp-unitˡ h) (comp-unitˡ k) (const-pre x h) (const-pre x k)
      _ _ _ _ (postWhisker-id-at α) (constant-input x α))

  output-h = productMap-pair h (id I) (id X) (const x)
  output-k = productMap-pair k (id I) (id X) (const x)
  close-h = pair-cong (comp-unitʳ h) (comp-unitˡ (const x))
  close-k = pair-cong (comp-unitʳ k) (comp-unitˡ (const x))

  second : ((close-k ∙ output-k) ∙ (productMap-cong α (idIso (id I)) ▷ insert x)) =₂
    (result ∙ (close-h ∙ output-h))
  second = paste-squares output-h output-k close-h close-k
    (productMap-cong α (idIso (id I)) ▷ insert x)
    (pair-cong (α ▷ id X) (idIso (id I) ▷ const x)) result
    (product-pair-natural α (idIso (id I)) (id X) (const x))
    (pair-square (comp-unitʳ h) (comp-unitʳ k) (comp-unitˡ (const x)) (comp-unitˡ (const x))
      _ _ _ _ (preWhisker-id-at α)
      ((isoComp-unitˡ-at (comp-unitˡ (const x))) ⁻¹ ∙
        (isoComp-unitʳ-at (comp-unitˡ (const x)) ∙
          isoComp-cong (idIso (comp-unitˡ (const x))) (preWhisker-idIso (id I) (const x)))))

  natural : (insert-natural k x ∙ (insert x ◁ α)) =₂
    ((productMap-cong α (idIso (id I)) ▷ insert x) ∙ insert-natural h x)
  natural = quotient-square (finish-h ∙ input-h) (close-h ∙ output-h)
    (finish-k ∙ input-k) (close-k ∙ output-k) _ _ result first second

module Evaluation {X I C : CAT} (x : Obj-abs I) {h k : MAP X (Fun I C)} (α : h =₁ k) where
  ph = productMap h (id I)
  pk = productMap k (id I)
  δ = productMap-cong α (idIso (id I))
  first :
    (((funEval ◁ insert-natural k x) ∙ comp-assoc k (insert x) funEval) ∙ (evaluate x ◁ α)) =₂
    ((funEval ◁ (δ ▷ insert x)) ∙ ((funEval ◁ insert-natural h x) ∙ comp-assoc h (insert x) funEval))
  first = paste-squares (comp-assoc h (insert x) funEval) (comp-assoc k (insert x) funEval)
    (funEval ◁ insert-natural h x) (funEval ◁ insert-natural k x)
    (evaluate x ◁ α) (funEval ◁ (insert x ◁ α)) (funEval ◁ (δ ▷ insert x))
    (postWhisker-comp-at α (insert x) funEval)
    (post-square funEval (insert-natural h x) (insert-natural k x) _ _ (Insertion.natural x α))

  natural : (evaluate-uncurry x k ∙ (evaluate x ◁ α)) =₂
    ((funUncurryIso α ▷ insert x) ∙ evaluate-uncurry x h)
  natural = isoComp-cong (preWhisker (insert x) ◁ (funUncurryIso-at α) ⁻¹) (idIso (evaluate-uncurry x h)) ∙
    paste-squares
      ((funEval ◁ insert-natural h x) ∙ comp-assoc h (insert x) funEval)
      ((funEval ◁ insert-natural k x) ∙ comp-assoc k (insert x) funEval)
      ((comp-assoc (insert x) ph funEval) ⁻¹) ((comp-assoc (insert x) pk funEval) ⁻¹)
      (evaluate x ◁ α) (funEval ◁ (δ ▷ insert x)) ((funEval ◁ δ) ▷ insert x)
      first (move-square (comp-assoc (insert x) pk funEval) ((funEval ◁ δ) ▷ insert x)
        (funEval ◁ (δ ▷ insert x)) (comp-assoc (insert x) ph funEval) (whisker-mixed-at δ (insert x) funEval))
```
