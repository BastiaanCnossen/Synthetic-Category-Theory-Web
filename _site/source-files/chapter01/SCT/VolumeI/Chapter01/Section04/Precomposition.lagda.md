# Precomposition and decoding

Decoding a named parameter after precomposition agrees with precomposing
its decoded functor. The comparison retains the specified uncurrying beta,
product separation and terminal insertion. Its naturality square acts on
whole identification animae, with the actual decoding functors as edges.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section04.Precomposition where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary hiding (_＝_)
import SCT.VolumeI.Chapter01.Section01.Terms as Terms
open Terms using (Equal)
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal
open Constructions
open import SCT.VolumeI.Chapter01.Section02.Coherence
open Composition
open Boundaries using (SquareCell₌)
open import SCT.VolumeI.Chapter01.Section02.Specialization
open import SCT.VolumeI.Chapter01.Section02.Whiskering
open import SCT.VolumeI.Chapter01.Section02.IdentificationSquares
open import SCT.VolumeI.Chapter01.Section03.ProductConstructions
open import SCT.VolumeI.Chapter01.Section03.Products.ProductFunctor
open import SCT.VolumeI.Chapter01.Section03.Products.ProductFunctorCoherence
open import SCT.VolumeI.Chapter01.Section04.MappingAnimae
open import SCT.VolumeI.Chapter01.Section04.Currying
open import SCT.VolumeI.Chapter01.Section04.Points
open import SCT.VolumeI.Chapter01.Section04.Functoriality
open import SCT.VolumeI.Chapter01.Section04.UncurryingRestriction
  using (uncurry-restrict-substitution)

module _ {Γ : Context} where
  private
    module _ {X A B : CAT Γ} where
      open Terms.Equalities X using (_＝_)

      paste-fixed : {f g f′ g′ f″ g″ : MAP A B}
        {t : f ＝ g} {m : f′ ＝ g′} {b : f″ ＝ g″}
        {l₁ : f =₁ f′} {r₁ : g =₁ g′} {l₂ : f′ =₁ f″} {r₂ : g′ =₁ g″}
        → SquareCell₌ t m (const l₁) (const r₁)
        → SquareCell₌ m b (const l₂) (const r₂)
        → SquareCell₌ t b (const (l₂ ∙ l₁)) (const (r₂ ∙ r₁))
      paste-fixed {l₁ = l₁} {r₁} {l₂} {r₂} first second =
        replace-sides₌ (const-comp l₂ l₁) (const-comp r₂ r₁)
          (paste-square₌ first second)

      inverse-fixed : {f g f′ g′ : MAP A B} {t : f ＝ g} {b : f′ ＝ g′}
        {l : f =₁ f′} {r : g =₁ g′}
        → SquareCell₌ t b (const l) (const r)
        → SquareCell₌ b t (const (l ⁻¹)) (const (r ⁻¹))
      inverse-fixed {l = l} {r} square =
        replace-sides₌ ((const-inv l) ⁻¹) ((const-inv r) ⁻¹) (inverse-square₌ square)

  module _ {X : CAT Γ} where
    open Terms.Equalities X using (_＝_)

    mapPre-uncurry-inputs : {P B C D : CAT Γ} (i : MAP B C)
      {u v : MAP P (Map C D)} (α : u ＝ v)
      → SquareCell₌ (uncurry⁼ (mapPre i ◁ α))
          (uncurry⁼ α ▷ productMap (id P) i)
          (const (mapPre-uncurry i u)) (const (mapPre-uncurry i v))
    mapPre-uncurry-inputs {P} {B} {C} {D} i {u} {v} α =
      let K = productMap (id (Map C D)) i
          R = productMap (id P) i
          pα = productMap-cong α (const (id₌ (id B)))
          qα = productMap-cong α (const (id₌ (id C)))
          first = uncurry-restrict-substitution (mapPre i) α
          second = interchange-fixedOuter (mapPre-β i) pα
          third = postWhisker-comp pα K mapEval
          fourth = replace-sides₌
            (post-constant mapEval (productMap-separate u i))
            (post-constant mapEval (productMap-separate v i))
            (post-square₌ mapEval (productMap-separate-inputs α i))
          fifth = replace-edges₌ (id₌ _) ((preWhisker R ◁ uncurry⁼-evaluate α) ⁻¹)
            (inverse-fixed (whisker-mixed qα R mapEval))
      in paste-fixed (paste-fixed (paste-fixed (paste-fixed first second) third) fourth) fifth

  module _ {B C D : CAT Γ} where
    open Terms.InContext (One {Γ}) using (Term)

    decode-pre : (i : MAP B C) (u : Term (Map C D))
      → decode (mapPre i ∘ u) =₁ (decode u ∘ i)
    decode-pre i u = (comp-assoc i (product-unitˡ-inverse C) (uncurry u)) ⁻¹ ∙
      ((uncurry u ◁ product-unitˡ-inverse-natural i) ∙
      (comp-assoc (product-unitˡ-inverse B) (productMap (id (One {Γ})) i) (uncurry u) ∙
        (mapPre-uncurry i u ▷ product-unitˡ-inverse B)))

    module _ {X : CAT Γ} where
      open Terms.Equalities X using (_＝_)

      decode-pre-natural : (i : MAP B C) {u v : Term (Map C D)} (α : u ＝ v)
        → SquareCell₌ (decode⁼ (mapPre i ◁ α)) (decode⁼ α ▷ i)
            (const (decode-pre i u)) (const (decode-pre i v))
      decode-pre-natural i {u} {v} α =
        let R = productMap (id (One {Γ})) i
            insertionB = product-unitˡ-inverse B
            insertionC = product-unitˡ-inverse C
            first = replace-sides₌
              (pre-constant (mapPre-uncurry i u) insertionB)
              (pre-constant (mapPre-uncurry i v) insertionB)
              (pre-square₌ insertionB (mapPre-uncurry-inputs i α))
            second = preWhisker-comp (uncurry⁼ α) R insertionB
            third = (interchange-fixedInner (uncurry⁼ α) (product-unitˡ-inverse-natural i)) ⁻¹
            fourth = inverse-fixed (preWhisker-comp (uncurry⁼ α) insertionC i)
            pasted = paste-fixed (paste-fixed (paste-fixed first second) third) fourth
        in replace-edges₌ ((decode⁼-evaluate (mapPre i ◁ α)) ⁻¹)
          ((preWhisker i ◁ decode⁼-evaluate α) ⁻¹) pasted

    decode-pre-square : (i : MAP B C) (u v : Term (Map C D))
      → SquareCell₌
          (decode⁼-functor (mapPre i ∘ u) (mapPre i ∘ v) ∘ postWhisker (mapPre i))
          (preWhisker i ∘ decode⁼-functor u v)
          (const (decode-pre i u)) (const (decode-pre i v))
    decode-pre-square i u v = replace-edges₌
      (decode⁼-functor _ _ ◁ comp-unitʳ (postWhisker (mapPre i)))
      (preWhisker i ◁ comp-unitʳ (decode⁼-functor u v))
      (decode-pre-natural i (id (Equal u v)))
```
