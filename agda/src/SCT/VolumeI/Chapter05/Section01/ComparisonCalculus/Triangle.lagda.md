# The two triangle paths

The short and long triangle paths are displayed with their identity and composition comparisons. They supply the endpoints for transport of the chosen triangle witness.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core
open import SCT.VolumeI.Chapter05.Section01.Coherence

module SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Triangle {l : Level} {S T : Theory l l l} (W : Weakening S T)
  {C D E : View.CAT S} (f : View.MAP S C D) (g : View.MAP S D E) where
private
  module S = View S
  module T = View T
open Weakening W
open T using (_∘_; _∙_; _◁_; _▷_; _⁻¹)

source-left = S._∘_ (S._∘_ g (S.id D)) f
source-right = S._∘_ g f
target-left = (map g ∘ T.id (cat D)) ∘ map f
target-right = map g ∘ map f

left-compositor : T._=₁_ (map source-left) target-left
left-compositor = ((map g ◁ unit D) ▷ map f) ∙
  ((comp (S.id D) g ▷ map f) ∙ comp f (S._∘_ g (S.id D)))
right-compositor : T._=₁_ (map source-right) target-right
right-compositor = comp f g

source-short source-long : S._=₁_ source-left source-right
source-short = S._⋆_ (S.comp-unitʳ g) (S.idIso f)
source-long = S._∙_ (S._⋆_ (S.idIso g) (S.comp-unitˡ f)) (S.comp-assoc f (S.id D) g)

target-short target-long : T._=₁_ target-left target-right
target-short = T._⋆_ (T.comp-unitʳ (map g)) (T.idIso (map f))
target-long = T._∙_ (T._⋆_ (T.idIso (map g)) (T.comp-unitˡ (map f)))
  (T.comp-assoc (map f) (T.id (cat D)) (map g))

adjust : T.MAP (T._＝_ (map source-left) (map source-right)) (T._＝_ target-left target-right)
adjust = Boundaries.conjugate W left-compositor right-compositor
normalized-short = adjust ∘ term source-short
normalized-long = adjust ∘ term source-long

record BoundaryNormalization : Set l where
  field
    short : T._=₂_ normalized-short target-short
    long : T._=₂_ normalized-long target-long

transported : T._=₂_ normalized-short normalized-long
transported = adjust ◁ cell2 (S.comp-triangle f g)

normalized : BoundaryNormalization → T._=₂_ target-short target-long
normalized b = BoundaryNormalization.long b ∙
  (transported ∙ (BoundaryNormalization.short b) ⁻¹)

record PreservesChosenTriangle (b : BoundaryNormalization) : Set l where
  field
    comparison : T._=₃_ (normalized b) (T.comp-triangle (map f) (map g))
```
