# The common vertex with both endpoint equations

The two presentations of the middle vertex are arrows from `0` to `1`.
Initiality compares them with their endpoint frames. We choose the middle
face identification by this comparison, retaining the equations needed
when applying either degeneracy.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section06.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section05.PullbackLaws as Laws
import SCT.VolumeI.Chapter01.Section09.WalkingMorphism as Walking
import SCT.VolumeI.Chapter01.Section09.IntervalEndpoints as Endpoints

module SCT.VolumeI.Chapter01.Section09.MiddleVertex
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I) where

open import SCT.VolumeI.Chapter01.Section09.Lattice 𝒯 M ℱ P I E public
open import SCT.VolumeI.Chapter01.Section09.UniversalComparisons 𝒯 M ℱ P I using (initial-comparison)
import SCT.VolumeI.Chapter01.Section02.PairingNaturality as PN
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-left-reflect)

max-source = MorphismExpression.source-frame max-expression
max-target = MorphismExpression.target-frame max-expression
min-source = MorphismExpression.source-frame min-expression
min-target = MorphismExpression.target-frame min-expression

source-before : =₁ (ev₀ ∘ (max̄ ∘ zero)) zero
source-before = (comp-unitˡ zero ∙ (max-source ▷ zero)) ∙ invIso (comp-assoc zero max̄ ev₀)
source-after : =₁ (ev₀ ∘ (min̄ ∘ one)) zero
source-after = ((constant-boundary one zero) ∙ (min-source ▷ one)) ∙
  invIso (comp-assoc one min̄ ev₀)

target-before : =₁ (ev₁ ∘ (max̄ ∘ zero)) one
target-before = ((constant-boundary zero one) ∙ (max-target ▷ zero)) ∙
  invIso (comp-assoc zero max̄ ev₁)
target-after : =₁ (ev₁ ∘ (min̄ ∘ one)) one
target-after = (comp-unitˡ one ∙ (min-target ▷ one)) ∙ invIso (comp-assoc one min̄ ev₁)

before after : MorphismExpression (const zero) one
before = record { arrow = max̄ ∘ zero ; source-frame = invIso (const-One zero) ∙ source-before ; target-frame = target-before }
after = record { arrow = min̄ ∘ one ; source-frame = invIso (const-One zero) ∙ source-after ; target-frame = target-after }

comparison : ExpressionIso before after
comparison = initial-comparison zero zero-isInitial one before after

middle : =₁ (max̄ ∘ zero) (min̄ ∘ one)
middle = ExpressionIso.comparison comparison

source-compatible : =₂ (source-after ∙ (ev₀ ◁ middle)) source-before
source-compatible = cancel-left-reflect (invIso (const-One zero))
  (ExpressionIso.source-compatible comparison ∙
    invIso (isoComp-assoc-at (invIso (const-One zero)) source-after (ev₀ ◁ middle)))

target-compatible : =₂ (target-after ∙ (ev₁ ◁ middle)) target-before
target-compatible = ExpressionIso.target-compatible comparison
```

