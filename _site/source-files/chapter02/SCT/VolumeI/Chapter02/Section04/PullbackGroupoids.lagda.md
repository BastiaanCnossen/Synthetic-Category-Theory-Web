# Pullbacks of groupoids over an arbitrary category

Constant diagrams induce a map from the original cospan to its arrow cospan.
The end maps are equivalences and the base map is an embedding, so the induced
map of pullbacks is an equivalence. Evaluation follows it, and all three
composite object maps are equivalences. The successive-cospan theorem then
makes the composite induced map an equivalence; cancellation gives the
evaluation-induced map. The complete evaluation-cone comparison identifies
this with evaluation on the pullback itself.

Thus the pullback is a groupoid. The base category need not be a groupoid.
This covers lem:Pullback_Of_Groupoids_Is_Groupoid and the presented-pullback
version lem:Groupoids_Closed_Under_Pullback.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter02.Section04.PullbackGroupoids where
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section02.Coherence using (module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section03.Equivalences
  using (equiv-transport; id-isEquiv; equiv-cancel-right)
open import SCT.VolumeI.Chapter01.Section06.Cones using (Cone)
open import SCT.VolumeI.Chapter01.Section06.Pullbacks using (Pullback; pullback-factor)
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares using (IsPullback)
open import SCT.VolumeI.Chapter01.Section06.PullbackFunctoriality using (CospanMap; pullback-map)
open import SCT.VolumeI.Chapter01.Section06.EmbeddingPullbackSquares using (cospan-embedding-isEquiv)
open import SCT.VolumeI.Chapter01.Section06.SuccessiveCospans using (module Successive)
open import SCT.VolumeI.Chapter01.Section07.Functoriality using (funPost)
open import SCT.VolumeI.Chapter02.Section01.WalkingMorphism using ([1]; zero)
open import SCT.VolumeI.Chapter02.Section01.Morphisms using (identityArrow; identity-source; ev₀)
open import SCT.VolumeI.Chapter02.Section03.RezkAxiom using (identityArrow-isEmbedding)
open import SCT.VolumeI.Chapter02.Section04.Groupoids using (IsGroupoid; groupoid-from-source-equivalence)
open import SCT.VolumeI.Chapter02.Section04.BasicClosure using (constant-natural; equivalence-reflects-groupoid)
open import SCT.VolumeI.Chapter02.Section04.EvaluationCones using (module EvaluationCone)

private
  module _ {Γ : Context} where
    constant-evaluation-isEquiv : (C : CAT Γ) → IsEquiv (ev₀ ∘ identityArrow {C = C})
    constant-evaluation-isEquiv C = equiv-transport ((identity-source {C = C}) ⁻¹) (id-isEquiv C)

module PullbackGroupoid {Γ : Context} {X Y C : CAT Γ}
  (f : MAP X C) (g : MAP Y C) (xGroupoid : IsGroupoid X) (yGroupoid : IsGroupoid Y) where
  constant-cospan : CospanMap f g (funPost {C = [1]} f) (funPost {C = [1]} g)
  constant-cospan = record
    { left = identityArrow; right = identityArrow; base = identityArrow
    ; left-square = constant-natural [1] f; right-square = constant-natural [1] g }
  private
    module AtZero = EvaluationCone zero f g using (cospan; module PullbackEvaluation)
    module Both = Successive constant-cospan AtZero.cospan
      (constant-evaluation-isEquiv X) (constant-evaluation-isEquiv Y) (constant-evaluation-isEquiv C)
      using (composite-isEquiv)

  constant-comparison-isEquiv : IsEquiv (pullback-map constant-cospan)
  constant-comparison-isEquiv = cospan-embedding-isEquiv constant-cospan
    xGroupoid yGroupoid (identityArrow-isEmbedding C)

  evaluation-comparison-isEquiv : IsEquiv (pullback-map AtZero.cospan)
  evaluation-comparison-isEquiv = equiv-cancel-right
    (pullback-map constant-cospan) (pullback-map AtZero.cospan)
    constant-comparison-isEquiv Both.composite-isEquiv

  isGroupoid : IsGroupoid (Pullback f g)
  isGroupoid = groupoid-from-source-equivalence
    (AtZero.PullbackEvaluation.evaluation-isEquiv evaluation-comparison-isEquiv)

module _ {Γ : Context} where
  pullback-isGroupoid : {X Y C : CAT Γ} (f : MAP X C) (g : MAP Y C)
    → IsGroupoid X → IsGroupoid Y → IsGroupoid (Pullback f g)
  pullback-isGroupoid = PullbackGroupoid.isGroupoid

  pullback-square-isGroupoid : {X Y C T : CAT Γ} {f : MAP X C} {g : MAP Y C}
    (s : Cone f g T) → IsPullback s → IsGroupoid X → IsGroupoid Y → IsGroupoid T
  pullback-square-isGroupoid {f = f} {g} s es ex ey =
    equivalence-reflects-groupoid (pullback-factor s) es (pullback-isGroupoid f g ex ey)
```
