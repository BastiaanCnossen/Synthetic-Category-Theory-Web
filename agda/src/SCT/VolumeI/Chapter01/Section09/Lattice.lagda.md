# Minimum and maximum on the interval

For `cons:Lattice_Structure`, the inverse coslice and slice projections
give families of arrows `0 → x` and `x → 1`. Their uncurrying defines
`min` and `max`. The eight relations of `lem:Lattice_Structure` use only
initiality and terminality of the endpoints.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section06.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section05.PullbackLaws as Laws
import SCT.VolumeI.Chapter01.Section09.WalkingMorphism as Walking
import SCT.VolumeI.Chapter01.Section09.IntervalEndpoints as Endpoints

module SCT.VolumeI.Chapter01.Section09.Lattice
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I) where

open import SCT.VolumeI.Chapter01.Section09.UniversalArrows 𝒯 M ℱ P I public
open Endpoints.IntervalEndpoints E public
open import SCT.VolumeI.Chapter01.Section03.Uncurrying 𝒯 M using (productMap-pair)
open import SCT.VolumeI.Chapter01.Section03.Points 𝒯 M using (oneProduct-in)

min-expression : MorphismExpression (const zero) (id [1])
min-expression = initial-expression zero zero-isInitial (id [1])

max-expression : MorphismExpression (id [1]) (const one)
max-expression = terminal-expression one one-isTerminal (id [1])

min̄ max̄ : MAP [1] (Ar [1])
min̄ = MorphismExpression.arrow min-expression
max̄ = MorphismExpression.arrow max-expression

min max : MAP ([1] × [1]) [1]
min = funUncurry min̄
max = funUncurry max̄

min-right-zero : =₁ (min ∘ insert zero) (const zero)
min-right-zero = MorphismExpression.source-frame min-expression ∙ invIso (evaluate-uncurry zero min̄)

min-right-one : =₁ (min ∘ insert one) (id [1])
min-right-one = MorphismExpression.target-frame min-expression ∙ invIso (evaluate-uncurry one min̄)

max-right-zero : =₁ (max ∘ insert zero) (id [1])
max-right-zero = MorphismExpression.source-frame max-expression ∙ invIso (evaluate-uncurry zero max̄)

max-right-one : =₁ (max ∘ insert one) (const one)
max-right-one = MorphismExpression.target-frame max-expression ∙ invIso (evaluate-uncurry one max̄)

canonical : MorphismExpression (const zero) one
canonical = record
  { arrow = nameFun (id [1])
  ; source-frame = invIso (const-One zero) ∙ (comp-unitˡ zero ∙ evaluate-name zero (id [1]))
  ; target-frame = comp-unitˡ one ∙ evaluate-name one (id [1]) }

constant-zero : MorphismExpression (const zero) zero
constant-zero = record
  { arrow = nameFun (const zero)
  ; source-frame = const-pre zero zero ∙ evaluate-name zero (const zero)
  ; target-frame = const-One zero ∙ (const-pre zero one ∙ evaluate-name one (const zero)) }

constant-one : MorphismExpression one (const one)
constant-one = record
  { arrow = nameFun (const one)
  ; source-frame = const-One one ∙ (const-pre one zero ∙ evaluate-name zero (const one))
  ; target-frame = const-pre one one ∙ evaluate-name one (const one) }

min-at : (x : Obj-abs [1]) → MorphismExpression (const zero) x
min-at x = retarget-expression (restrict-expression min-expression x) (const-pre zero x) (comp-unitˡ x)

max-at : (x : Obj-abs [1]) → MorphismExpression x (const one)
max-at x = retarget-expression (restrict-expression max-expression x) (comp-unitˡ x) (const-pre one x)

min-at-zero : =₁ (min̄ ∘ zero) (nameFun (const zero))
min-at-zero = initial-compare zero zero-isInitial zero (min-at zero) constant-zero

min-at-one : =₁ (min̄ ∘ one) (nameFun (id [1]))
min-at-one = initial-compare zero zero-isInitial one (min-at one) canonical

max-at-zero : =₁ (max̄ ∘ zero) (nameFun (id [1]))
max-at-zero = terminal-compare one one-isTerminal zero (max-at zero)
  (retarget-expression canonical (const-One zero) (invIso (const-One one)))

max-at-one : =₁ (max̄ ∘ one) (nameFun (const one))
max-at-one = terminal-compare one one-isTerminal one (max-at one) constant-one

row-from-point : {X C : CAT} (h : MAP X (Ar C)) (x : Obj-abs X) (f : MAP [1] C) →
  =₁ (h ∘ x) (nameFun f) →
  =₁ (funUncurry h ∘ pair (const x) (id [1])) f
row-from-point h x f α = decode-nameFun f ∙
  ((funUncurry-cong α ▷ oneProduct-in [1]) ∙ invIso decode-row)
  where
  decode-row : =₁ (decodeFun (h ∘ x)) (funUncurry h ∘ pair (const x) (id [1]))
  decode-row = (funUncurry h ◁
    (pair-cong (idIso (const x)) (comp-unitˡ (id [1])) ∙
      productMap-pair x (id [1]) (terminate [1]) (id [1]))) ∙
    (comp-assoc (oneProduct-in [1]) (productMap x (id [1])) (funUncurry h) ∙
      (funUncurry-pre h x ▷ oneProduct-in [1]))

min-left-zero : =₁ (min ∘ pair (const zero) (id [1])) (const zero)
min-left-zero = row-from-point min̄ zero (const zero) min-at-zero

min-left-one : =₁ (min ∘ pair (const one) (id [1])) (id [1])
min-left-one = row-from-point min̄ one (id [1]) min-at-one

max-left-zero : =₁ (max ∘ pair (const zero) (id [1])) (id [1])
max-left-zero = row-from-point max̄ zero (id [1]) max-at-zero

max-left-one : =₁ (max ∘ pair (const one) (id [1])) (const one)
max-left-one = row-from-point max̄ one (const one) max-at-one
```
