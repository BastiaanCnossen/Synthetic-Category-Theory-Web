# Products distribute over coproducts

The descent equivalence over `One`, expressed using the two projection
comparisons for pullbacks over `One`, is the actual copairing
`copair (productMap (id E) in₁) (productMap (id E) in₂)`.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section05.Setup as Setup
import SCT.VolumeI.Chapter01.Section05.Coproducts as Coproducts
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter01.Section06.UniversalCoproducts as Universality

module SCT.VolumeI.Chapter01.Section06.Distributivity
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (B : Coproducts.CoproductStructure 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (U : Universality.CoproductUniversality 𝒯 M B P) where

open Setup 𝒯 M
open Coproducts.CoproductStructure B
open Laws.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section05.CoproductCalculus 𝒯 M B
open import SCT.VolumeI.Chapter01.Section06.CoproductDescent 𝒯 M B P U using (module Descent)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.BaseChangeInclusion 𝒯 P using (module Inclusion)
open import SCT.VolumeI.Chapter01.Section06.PullbackProducts 𝒯 P using (module TerminalBase)

module Distributivity (E C D : CAT) where

  module Base = Descent (terminate C) (terminate D) (terminate E)
  module Total = TerminalBase Base.combined (terminate E)
  module Left = TerminalBase (terminate C) (terminate E)
  module Right = TerminalBase (terminate D) (terminate E)

  module Component {A : CAT} (i : MAP A (C ⊔ D)) (α : (terminate A) =₁ (Base.combined ∘ i)) where
    module I = Inclusion i Base.combined (terminate E) α
    module Source = TerminalBase (terminate A) (terminate E)

    comparison : (Total.toSwapped ∘ (I.include ∘ Source.fromSwapped)) =₁ (productMap (id E) i)
    comparison = pair-iso
      ((comp-unitˡ pr₁ ∙ pair-β₁ (id E ∘ pr₁) (i ∘ pr₂)) ⁻¹ ∙
      (Source.fromSwapped-β₂ ∙
      ((I.include-β₂ ▷ Source.fromSwapped) ∙
      ((comp-assoc Source.fromSwapped I.include pullback₂) ⁻¹ ∙
        project-pair₁ pullback₂ pullback₁ (I.include ∘ Source.fromSwapped)))))
      ((pair-β₂ (id E ∘ pr₁) (i ∘ pr₂)) ⁻¹ ∙
      ((i ◁ Source.fromSwapped-β₁) ∙
      (comp-assoc Source.fromSwapped pullback₁ i ∙
      ((I.include-β₁ ▷ Source.fromSwapped) ∙
      ((comp-assoc Source.fromSwapped I.include pullback₁) ⁻¹ ∙
        project-pair₂ pullback₂ pullback₁ (I.include ∘ Source.fromSwapped))))))

  module LeftComponent = Component in₁ ((copair-β₁ (terminate C) (terminate D)) ⁻¹)
  module RightComponent = Component in₂ ((copair-β₂ (terminate C) (terminate D)) ⁻¹)

  distribute : MAP ((E × C) ⊔ (E × D)) (E × (C ⊔ D))
  distribute = copair (productMap (id E) in₁) (productMap (id E) in₂)

  sourceChange = coproductMap Left.fromSwapped Right.fromSwapped
  viaDescent = Total.toSwapped ∘ (Base.descent ∘ sourceChange)

  comparison : viaDescent =₁ distribute
  comparison = copair-cong LeftComponent.comparison RightComponent.comparison ∙
    (copair-post (Base.include₁ ∘ Left.fromSwapped) (Base.include₂ ∘ Right.fromSwapped) Total.toSwapped ∙
      (Total.toSwapped ◁
        (copair-cong (copair-pre₁ Base.include₁ Base.include₂ Left.fromSwapped)
          (copair-pre₂ Base.include₁ Base.include₂ Right.fromSwapped) ∙
          copair-post (in₁ ∘ Left.fromSwapped) (in₂ ∘ Right.fromSwapped) Base.descent)))

  distribute-isEquiv : IsEquiv distribute
  distribute-isEquiv = equiv-transport comparison
    (equiv-compose (Base.descent ∘ sourceChange) Total.toSwapped
      (equiv-compose sourceChange Base.descent
        (coproductMap-isEquiv Left.fromSwapped Right.fromSwapped Left.fromSwapped-isEquiv Right.fromSwapped-isEquiv)
        Base.descent-isEquiv) Total.toSwapped-isEquiv)
```
