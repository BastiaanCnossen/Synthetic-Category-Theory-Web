# Products distribute over coproducts

The actual copair of the two product inclusions is an equivalence. Both
component calculations retain the selected inclusion projections and the
swapped terminal-base presentation. Their copair comparison is the displayed
descent route; no earlier higher proof-witness agreement is asserted.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section06.Distributivity where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary hiding (_⊔_; _＝_)
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal
open Constructions
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (comp-unitˡ; comp-assoc; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Products
open Coordinates
open Calculus
open import SCT.VolumeI.Chapter01.Section02.Specialization
open import SCT.VolumeI.Chapter01.Section03.Equivalences
open import SCT.VolumeI.Chapter01.Section03.ProductConstructions using (productMap)
open import SCT.VolumeI.Chapter01.Section05.Coproducts
open import SCT.VolumeI.Chapter01.Section05.Copairing
open import SCT.VolumeI.Chapter01.Section05.CoproductConstructions using (coproductMap; coproductMap-isEquiv)
open import SCT.VolumeI.Chapter01.Section06.Pullbacks
open import SCT.VolumeI.Chapter01.Section06.PullbackConstructions using (module TerminalBase)
open import SCT.VolumeI.Chapter01.Section06.CoproductDescent using (module Descent; module Inclusion)

module _ {Γ : Context} where
  module Distributivity (E C D : CAT Γ) where

    module Base = Descent (terminate C) (terminate D) (terminate E)
      using (combined; descent; include₁; include₂; descent-isEquiv)
    module Total = TerminalBase Base.combined (terminate E) using (to-swapped; to-swapped-isEquiv)
    module Left = TerminalBase (terminate C) (terminate E) using (from-swapped; from-swapped-isEquiv)
    module Right = TerminalBase (terminate D) (terminate E) using (from-swapped; from-swapped-isEquiv)

    module Component {A : CAT Γ} (i : MAP A (C ⊔ D)) (α : (terminate A) =₁ (Base.combined ∘ i)) where
      module I = Inclusion i Base.combined (terminate E) α using (include; include-β₁; include-β₂)
      module Source = TerminalBase (terminate A) (terminate E)
        using (from-swapped; from-swapped-β₁; from-swapped-β₂)

      opaque
        inclusion-law : (Total.to-swapped ∘ (I.include ∘ Source.from-swapped)) =₁ (productMap (id E) i)
        inclusion-law = pair₌
          ((comp-unitˡ pr₁ ∙ pair-β₁ (id E ∘ pr₁) (i ∘ pr₂)) ⁻¹ ∙
          (Source.from-swapped-β₂ ∙
          ((I.include-β₂ ▷ Source.from-swapped) ∙
          ((comp-assoc Source.from-swapped I.include pullback₂) ⁻¹ ∙
            project-pair₁ pullback₂ pullback₁ (I.include ∘ Source.from-swapped)))))
          ((pair-β₂ (id E ∘ pr₁) (i ∘ pr₂)) ⁻¹ ∙
          ((i ◁ Source.from-swapped-β₁) ∙
          (comp-assoc Source.from-swapped pullback₁ i ∙
          ((I.include-β₁ ▷ Source.from-swapped) ∙
          ((comp-assoc Source.from-swapped I.include pullback₁) ⁻¹ ∙
            project-pair₂ pullback₂ pullback₁ (I.include ∘ Source.from-swapped))))))


    module LeftComponent = Component in₁ ((copair-β₁ (terminate C) (terminate D)) ⁻¹) using (inclusion-law)
    module RightComponent = Component in₂ ((copair-β₂ (terminate C) (terminate D)) ⁻¹) using (inclusion-law)

    distribute : MAP ((E × C) ⊔ (E × D)) (E × (C ⊔ D))
    distribute = copair (productMap (id E) in₁) (productMap (id E) in₂)

    sourceChange : MAP ((E × C) ⊔ (E × D))
      (Pullback (terminate C) (terminate E) ⊔ Pullback (terminate D) (terminate E))
    sourceChange = coproductMap Left.from-swapped Right.from-swapped
    viaDescent : MAP ((E × C) ⊔ (E × D)) (E × (C ⊔ D))
    viaDescent = Total.to-swapped ∘ (Base.descent ∘ sourceChange)

    descent-law : viaDescent =₁ distribute
    descent-law = copair-cong LeftComponent.inclusion-law RightComponent.inclusion-law ∙
      (copair-post (Base.include₁ ∘ Left.from-swapped) (Base.include₂ ∘ Right.from-swapped) Total.to-swapped ∙
        (Total.to-swapped ◁
          (copair-cong (copair-pre₁ Base.include₁ Base.include₂ Left.from-swapped)
            (copair-pre₂ Base.include₁ Base.include₂ Right.from-swapped) ∙
            copair-post (in₁ ∘ Left.from-swapped) (in₂ ∘ Right.from-swapped) Base.descent)))

    opaque
      distribute-isEquiv : IsEquiv distribute
      distribute-isEquiv = equiv-transport descent-law
        (equiv-compose (Base.descent ∘ sourceChange) Total.to-swapped
          (equiv-compose sourceChange Base.descent
            (coproductMap-isEquiv Left.from-swapped Right.from-swapped Left.from-swapped-isEquiv Right.from-swapped-isEquiv)
            Base.descent-isEquiv) Total.to-swapped-isEquiv)
```
