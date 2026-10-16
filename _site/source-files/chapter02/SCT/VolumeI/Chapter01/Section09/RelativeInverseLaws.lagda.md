# Inverse laws over a base

The inverse of a functor over the base uses its chosen right inverse law
to specify its base triangle. That right law lies over the base. To obtain
the other law, cancel the original equivalence from a relative comparison.
This retains the chosen inverse and its base triangle, while choosing a
left law with the required compatibility.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section09.RelativeInverseLaws where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary hiding (_＝_)
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal using (module Constructions)
open Constructions
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (id₌; comp-unitˡ; comp-unitʳ; comp-assoc; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Specialization
open import SCT.VolumeI.Chapter01.Section03.RelativeFunctors
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses
  using (cancel-right; inverse-composite; inverse-inverse; preWhisker-inverse)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Triangles
  using (restrict-triangle; restrict-change-square-One)
open import SCT.VolumeI.Chapter01.Section03.Identifications.OverBase
open import SCT.VolumeI.Chapter01.Section03.WhiskeringEquivalence
  using (factor-through-postWhisker)
import SCT.VolumeI.Chapter01.Section03.Factorizations as Fact

module _ {Γ : Context} where
  private
    abstract
      compatible-post-reflect : {W X Y S : CAT Γ}
        (q : MAP Y S) (f : MAP X Y) {p : MAP X S}
        (a : (q ∘ f) =₁ p) {u v : MAP W X} {r : MAP W S}
        (bu : (p ∘ u) =₁ r) (bv : (p ∘ v) =₁ r) (α : u =₁ v)
        → CompatibleOver q (compose-triangle q f a u bu)
            (compose-triangle q f a v bv) (f ◁ α)
        → CompatibleOver p bu bv α
      compatible-post-reflect q f {p} a {u} {v} bu bv α given =
        let t = restrict-triangle q f a u
            t′ = restrict-triangle q f a v
            rearrange = (comp₌-assoc bv (p ◁ α) t) ⁻¹ ∙
              (comp₌-cong (id₌ bv) (restrict-change-square-One q f p a α) ∙
                comp₌-assoc bv t′ (q ◁ (f ◁ α)))
        in cancel-right t (given ∙ rearrange ⁻¹)

  module RelativeCancellation {S : CAT Γ} {X Y Z : CategoryOverBase S}
    (F : FunctorOverBase X Y) (e : IsEquiv (FunctorOverBase.functor F))
    (U V : FunctorOverBase Z X)
    (β : IdentificationOver {A = One} (comp-over F U) (comp-over F V)) where
    private
      f = FunctorOverBase.functor F
      q = CategoryOverBase.map Y
      chosen : Fact.Factorization (postWhisker f) (IdentificationOver.identification β)
      chosen = factor-through-postWhisker f e (IdentificationOver.identification β)

    identification : FunctorOverBase.functor U =₁ FunctorOverBase.functor V
    identification = Fact.factor chosen

    image : (f ◁ identification) =₂ IdentificationOver.identification β
    image = Fact.triangle chosen

    over : IsIdentificationOver U V identification
    over = compatible-to-over
      (compatible-post-reflect q f (FunctorOverBase.cell F)
        (FunctorOverBase.cell U) (FunctorOverBase.cell V) identification
        (over-to-compatible (IdentificationOver.over β) ∙
          comp₌-cong (id₌ (FunctorOverBase.cell (comp-over F V)))
            (postWhisker q ◁ image)))

    value : IdentificationOver {A = One} U V
    value = identification-over identification over

  module RelativeInverse {S : CAT Γ} {X Y : CategoryOverBase S}
    (F : FunctorOverBase X Y) (e : IsEquiv (FunctorOverBase.functor F)) where
    private
      f = FunctorOverBase.functor F
      g = IsEquiv.inverse e
      q = CategoryOverBase.map Y
      base-cell = FunctorOverBase.cell F
      ε = (IsEquiv.right-inverse-law e) ⁻¹

    inverse : FunctorOverBase Y X
    inverse = inverse-over F e

    private
      t : (q ∘ (f ∘ g)) =₁ (CategoryOverBase.map X ∘ g)
      t = restrict-triangle q f base-cell g

      tail-image : (comp-assoc g f q ∙ (base-cell ⁻¹ ▷ g)) =₂ (t ⁻¹)
      tail-image =
        ((inverse-composite (base-cell ▷ g) ((comp-assoc g f q) ⁻¹)) ⁻¹) ∙
          comp₌-cong ((inverse-inverse (comp-assoc g f q)) ⁻¹) (preWhisker-inverse base-cell g)

      inverse-cell-image : FunctorOverBase.cell inverse =₂
        ((comp-unitʳ q ∙ (q ◁ ε)) ∙ (t ⁻¹))
      inverse-cell-image = (comp₌-assoc (comp-unitʳ q) (q ◁ ε) (t ⁻¹)) ⁻¹ ∙
        comp₌-cong (id₌ (comp-unitʳ q)) (comp₌-cong (id₌ (q ◁ ε)) tail-image)

      right-compatible : CompatibleOver q
        (FunctorOverBase.cell (comp-over F inverse)) (comp-unitʳ q) ε
      right-compatible =
        (inv-comp-right (comp-unitʳ q ∙ (q ◁ ε)) t ∙
          comp₌-cong inverse-cell-image (id₌ t)) ⁻¹

    right-law : IdentificationOver {A = One} (comp-over F inverse) (id-over Y)
    right-law = identification-over ε (compatible-to-over right-compatible)

    private
      whiskered-left : IdentificationOver {A = One}
        (comp-over F (comp-over inverse F)) (comp-over F (id-over X))
      whiskered-left = identification-over
        ((comp-unitʳ f) ⁻¹ ∙
          (comp-unitˡ f ∙ ((ε ▷ f) ∙ (comp-assoc f g f) ⁻¹)))
        (identification-over-comp
          (identification-over-inverse (identification-over-unitʳ F))
          (identification-over-comp (identification-over-unitˡ F)
            (identification-over-comp
              (identification-over-pre F (IdentificationOver.over right-law))
              (identification-over-inverse (identification-over-assoc F inverse F)))))

      module Left = RelativeCancellation F e (comp-over inverse F) (id-over X) whiskered-left

    left-law : IdentificationOver {A = One} (comp-over inverse F) (id-over X)
    left-law = Left.value

    left-image : (f ◁ IdentificationOver.identification left-law) =₂
      IdentificationOver.identification whiskered-left
    left-image = Left.image
```
