# Directed evaluation over the terminal category

For `rmk:Directed_Evaluation_Map_Specializes_To_Evaluation_Map`,
both directed pullbacks are equivalent to the original category.
The displayed comparisons identify directed evaluation with ordinary
source or target evaluation after these particular equivalences.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking

module SCT.VolumeI.Chapter04.Section01.TerminalBase
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter04.Section01.DirectedEvaluation 𝒯 M ℱ P I public
open import SCT.VolumeI.Chapter01.Section07.Contractible 𝒯 M ℱ
  using (fun-terminal-contractible; contractible-map)
open import SCT.VolumeI.Chapter01.Section06.PullbackSymmetry 𝒯 P
  using (pullback-equivalenceʳ)

terminal-endpoints-equivalence : IsEquiv (endpoints {One})
terminal-endpoints-equivalence = contractible-map endpoints (fun-terminal-contractible [1])
  (equiv-transport (terminal-iso pr₁ (terminate (One × One))) (product-unitʳ-isEquiv One))

module OverTerminal (A : CAT) where
  open Evaluation (terminate A)

  left-equivalence : IsEquiv Left.left
  left-equivalence = equiv-compose Left.base pr₁
    (pullback-equivalenceʳ endpoints (productMap (terminate A) (id One)) terminal-endpoints-equivalence)
    (product-unitʳ-isEquiv A)

  right-equivalence : IsEquiv Right.right
  right-equivalence = equiv-compose Right.base pr₂
    (pullback-equivalenceʳ endpoints (productMap (id One) (terminate A)) terminal-endpoints-equivalence)
    (equiv-transport (pair-β₁ pr₂ pr₁)
      (equiv-compose swap pr₁ (swap-isEquiv One A) (product-unitʳ-isEquiv A)))

  source-comparison : (Left.left ∘ directed-ev₀) =₁ ev₀
  source-comparison = pair-β₁ ev₀ (terminate A ∘ ev₁) ∙
    ((pr₁ ◁ directed-ev₀-base) ∙ comp-assoc directed-ev₀ Left.base pr₁)

  target-comparison : (Right.right ∘ directed-ev₁) =₁ ev₁
  target-comparison = pair-β₂ (terminate A ∘ ev₀) ev₁ ∙
    ((pr₂ ◁ directed-ev₁-base) ∙ comp-assoc directed-ev₁ Right.base pr₂)

  left-to-source : IsEquiv directed-ev₀ → IsEquiv (ev₀ {A})
  left-to-source e = equiv-transport source-comparison
    (equiv-compose directed-ev₀ Left.left e left-equivalence)

  source-to-left : IsEquiv (ev₀ {A}) → IsEquiv directed-ev₀
  source-to-left e = equiv-cancel-left directed-ev₀ Left.left left-equivalence
    (equiv-transport (source-comparison ⁻¹) e)

  right-to-target : IsEquiv directed-ev₁ → IsEquiv (ev₁ {A})
  right-to-target e = equiv-transport target-comparison
    (equiv-compose directed-ev₁ Right.right e right-equivalence)

  target-to-right : IsEquiv (ev₁ {A}) → IsEquiv directed-ev₁
  target-to-right e = equiv-cancel-left directed-ev₁ Right.right right-equivalence
    (equiv-transport (target-comparison ⁻¹) e)
```
