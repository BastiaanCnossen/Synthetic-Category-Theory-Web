# Transporting a law between families

A law between parameterized functors is transported on the whole weakened parameter category. Comparing it with a specified target law requires a further identification.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core
open import SCT.VolumeI.Chapter05.Section01.Coherence
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Calculus as Calculus
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Squares as Squares
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.WitnessAction as WitnessAction

-- A law between parameterized functors. The target parameter is W(X),
-- not One. No evaluation on absolute points, or point-detection axiom, occurs.
module SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.FamilyWitness {l : Level} {S T : Theory l l l}
  (W : Weakening S T)
  {X Y : View.CAT S} (alpha beta : View.MAP S X Y)
  {Y' : View.CAT T} (output : View.MAP T (Weakening.cat W Y) Y')
  (alpha' beta' : View.MAP T (Weakening.cat W X) Y')
  (left : View._=₁_ T (View._∘_ T output (Weakening.map W alpha)) alpha')
  (right : View._=₁_ T (View._∘_ T output (Weakening.map W beta)) beta') where
private
  module S = View S
  module T = View T
open Weakening W
open T using (_∘_; _∙_; _◁_; _⁻¹)
open Calculus T using (_then_; isoComp-cong; const-One)

opaque
  action : T.MAP (cat (S._＝_ alpha beta)) (T._＝_ alpha' beta')
  action = Boundaries.conjugate W left right ∘ (T.postWhisker output ∘ phi alpha beta)

  normalized : S._=₁_ alpha beta → T._=₁_ alpha' beta'
  normalized p = right ∙ ((output ◁ term p) ∙ (left ⁻¹))

  expansion : (p : S._=₁_ alpha beta)
    → T._=₂_ (normalized p) (right ∙ ((output ◁ term p) ∙ (left ⁻¹)))
  expansion p = T.idIso _

  evaluation : (p : S._=₁_ alpha beta)
    → T._=₁_ (WitnessAction.Action.act W action p) (normalized p)
  evaluation p =
    WitnessAction.Action.post W (Boundaries.conjugate W left right)
      (T.postWhisker output ∘ phi alpha beta) p then
    (Boundaries.conjugate W left right ◁
      WitnessAction.Action.post W (T.postWhisker output) (phi alpha beta) p) then
    Squares.evaluate T left right (output ◁ term p) then
    isoComp-cong (const-One right) (isoComp-cong (T.idIso _) (const-One (left ⁻¹)))

Preserves : S._=₁_ alpha beta → T._=₁_ alpha' beta' → Set l
Preserves p q = T._=₂_ (normalized p) q
```
