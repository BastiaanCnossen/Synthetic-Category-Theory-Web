# The common vertex with both endpoint equations

The two presentations of the middle vertex are arrows from `0` to `1`.
Initiality compares them with their endpoint frames. We choose the middle
face identification by this comparison, retaining the equations needed
when applying either degeneracy.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints

module SCT.VolumeI.Chapter02.Section01.MiddleVertex
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I) where

open import SCT.VolumeI.Chapter02.Section01.Lattice 𝒯 M ℱ P I E public
open import SCT.VolumeI.Chapter02.Section01.UniversalComparisons 𝒯 M ℱ P I using (initial-comparison)
import SCT.VolumeI.Chapter01.Section03.PairingNaturality as PN
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-left-reflect)

max-source = MorphismExpression.source-frame max-expression
max-target = MorphismExpression.target-frame max-expression
min-source = MorphismExpression.source-frame min-expression
min-target = MorphismExpression.target-frame min-expression

source-before : (ev₀ ∘ (max̄ ∘ zero)) =₁ zero
source-before = (comp-unitˡ zero ∙ (max-source ▷ zero)) ∙ (comp-assoc zero max̄ ev₀) ⁻¹
source-after : (ev₀ ∘ (min̄ ∘ one)) =₁ zero
source-after = ((constant-boundary one zero) ∙ (min-source ▷ one)) ∙
  (comp-assoc one min̄ ev₀) ⁻¹

target-before : (ev₁ ∘ (max̄ ∘ zero)) =₁ one
target-before = ((constant-boundary zero one) ∙ (max-target ▷ zero)) ∙
  (comp-assoc zero max̄ ev₁) ⁻¹
target-after : (ev₁ ∘ (min̄ ∘ one)) =₁ one
target-after = (comp-unitˡ one ∙ (min-target ▷ one)) ∙ (comp-assoc one min̄ ev₁) ⁻¹

before after : MorphismExpression (const zero) one
before = record { arrow = max̄ ∘ zero ; source-frame = (const-One zero) ⁻¹ ∙ source-before ; target-frame = target-before }
after = record { arrow = min̄ ∘ one ; source-frame = (const-One zero) ⁻¹ ∙ source-after ; target-frame = target-after }

comparison : ExpressionIso before after
comparison = initial-comparison zero zero-isInitial one before after

middle : (max̄ ∘ zero) =₁ (min̄ ∘ one)
middle = ExpressionIso.comparison comparison

source-compatible : (source-after ∙ (ev₀ ◁ middle)) =₂ source-before
source-compatible = cancel-left-reflect ((const-One zero) ⁻¹)
  (ExpressionIso.source-compatible comparison ∙
    (isoComp-assoc-at ((const-One zero) ⁻¹) source-after (ev₀ ◁ middle)) ⁻¹)

target-compatible : (target-after ∙ (ev₁ ◁ middle)) =₂ target-before
target-compatible = ExpressionIso.target-compatible comparison
```

