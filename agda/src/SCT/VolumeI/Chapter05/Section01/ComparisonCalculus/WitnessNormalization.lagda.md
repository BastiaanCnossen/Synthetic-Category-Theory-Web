# Normalizing a witness with adjusted boundaries

After the two identification boundaries have been compared, conjugation transports a witness between them. The resulting normalization is the input to a separate preservation condition.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core
open import SCT.VolumeI.Chapter05.Section01.Coherence
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Calculus as Calculus
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Squares as Squares
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.WitnessAction as WitnessAction

module SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.WitnessNormalization {l : Level} {S T : Theory l l l}
  (W : Weakening S T)
  {C D : View.CAT S} {f g : View.MAP S C D}
  (alpha beta : View._=₁_ S f g)
  {X Y : View.CAT T} {f' g' : View.MAP T X Y}
  (adjust : View.MAP T (View._＝_ T (Weakening.map W f) (Weakening.map W g)) (View._＝_ T f' g'))
  (alpha' beta' : View._=₁_ T f' g')
  (left : View._=₁_ T (View._∘_ T adjust (Weakening.term W alpha)) alpha')
  (right : View._=₁_ T (View._∘_ T adjust (Weakening.term W beta)) beta') where
private
  module S = View S
  module T = View T
open Weakening W
open T using (_∘_; _∙_; _◁_; _▷_; _⁻¹)
open Calculus T

witness-map : T.MAP (cat (S._＝_ alpha beta)) (T._＝_ alpha' beta')
witness-map = Boundaries.conjugate W left right ∘
  (T.postWhisker adjust ∘ (lift2 alpha beta ∘ phi alpha beta))

normalized : S._=₂_ alpha beta → T._=₂_ alpha' beta'
normalized p = right ∙ ((adjust ◁ cell2 p) ∙ (left ⁻¹))

opaque
  evaluation : (p : S._=₂_ alpha beta)
    → T._=₁_ (WitnessAction.Action.act W witness-map p) (normalized p)
  evaluation p =
    WitnessAction.Action.post W (Boundaries.conjugate W left right)
      (T.postWhisker adjust ∘ (lift2 alpha beta ∘ phi alpha beta)) p then
    (Boundaries.conjugate W left right ◁
      (WitnessAction.Action.post W (T.postWhisker adjust) (lift2 alpha beta ∘ phi alpha beta) p then
        (T.postWhisker adjust ◁ WitnessAction.Action.post W (lift2 alpha beta) (phi alpha beta) p))) then
    Squares.evaluate T left right (adjust ◁ cell2 p) then
    isoComp-cong (const-One right) (isoComp-cong (T.idIso _) (const-One (left ⁻¹)))
```
