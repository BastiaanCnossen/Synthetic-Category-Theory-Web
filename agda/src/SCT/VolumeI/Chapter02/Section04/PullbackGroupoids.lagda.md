# Pullbacks of groupoids over an arbitrary category

Constant arrows give a map from the original cospan to its arrow
cospan. Its end maps are equivalences and its base map is an embedding,
so it induces an equivalence of pullbacks. Following by evaluation at
zero gives equivalences at all three objects. The successive-cospan
argument therefore makes the evaluation map of pullbacks an equivalence.

The whole-cone evaluation comparison identifies this with evaluation on
the arrow category of the pullback. Since evaluation retracts constant
arrows, the pullback is a groupoid. This proves
`lem:Pullback_Of_Groupoids_Is_Groupoid` with the specified matching.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section02.SegalAxiom as Segal
import SCT.VolumeI.Chapter02.Section01.CommutativeSquareAxiom as Squares
import SCT.VolumeI.Chapter02.Section03.RezkAxiom as Rezk

module SCT.VolumeI.Chapter02.Section04.PullbackGroupoids
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E)
  (R : Rezk.RezkAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section04.Groupoids 𝒯 M ℱ P I E R public
open import SCT.VolumeI.Chapter02.Section04.BasicClosure 𝒯 M ℱ P I E R
  using (equivalence-reflects-groupoid)
open Laws.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.PullbackFunctor 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.EmbeddingCalculus.CospanEmbeddings 𝒯 P
open import SCT.VolumeI.Chapter02.Section04.ConstantDiagrams.ConstantExponential 𝒯 M ℱ using (constant-natural)
open import SCT.VolumeI.Chapter02.Section04.PullbackCalculus.EvaluationPullbacks 𝒯 M ℱ P
open import SCT.VolumeI.Chapter02.Section04.PullbackCalculus.SuccessiveCospans 𝒯 P
import SCT.VolumeI.Chapter02.Section03.IsomorphismEmbedding as Embedding
open Embedding.WithRezk 𝒯 M ℱ P I E S Q R using (identityArrow-isEmbedding)

constant-evaluation-isEquiv : (C : CAT) → IsEquiv (ev₀ ∘ identityArrow {C})
constant-evaluation-isEquiv C = equiv-transport (identity-source ⁻¹) (id-isEquiv C)

module PullbackGroupoid {X Y C : CAT} (f : MAP X C) (g : MAP Y C)
  (xGroupoid : IsGroupoid X) (yGroupoid : IsGroupoid Y) where
  constant-cospan : CospanMap f g (funPost {C = [1]} f) (funPost g)
  constant-cospan = record
    { left = identityArrow ; right = identityArrow ; base = identityArrow
    ; leftSquare = constant-natural [1] f ; rightSquare = constant-natural [1] g }
  module Constant = CospanMap constant-cospan using (pullbackMap)
  module AtZero = EvaluatePullback zero f g
    using (evaluation-isEquiv; module Evaluation)
  module Evaluation = AtZero.Evaluation
    using (cospan; module Induced)
  module Both = Successive constant-cospan Evaluation.cospan
    (constant-evaluation-isEquiv X) (constant-evaluation-isEquiv Y) (constant-evaluation-isEquiv C)
    using (composite-isEquiv)

  constant-comparison-isEquiv : IsEquiv Constant.pullbackMap
  constant-comparison-isEquiv = cospan-embedding-isEquiv constant-cospan
    xGroupoid yGroupoid (identityArrow-isEmbedding C)

  evaluation-comparison-isEquiv : IsEquiv Evaluation.Induced.pullbackMap
  evaluation-comparison-isEquiv = equiv-cancel-right Constant.pullbackMap Evaluation.Induced.pullbackMap
    constant-comparison-isEquiv Both.composite-isEquiv

  evaluation-isEquiv : IsEquiv (ev₀ {Pullback f g})
  evaluation-isEquiv = AtZero.evaluation-isEquiv evaluation-comparison-isEquiv

  isGroupoid : IsGroupoid (Pullback f g)
  isGroupoid = equiv-cancel-left identityArrow ev₀ evaluation-isEquiv
    (constant-evaluation-isEquiv (Pullback f g))

pullback-isGroupoid : {X Y C : CAT} (f : MAP X C) (g : MAP Y C) →
  IsGroupoid X → IsGroupoid Y → IsGroupoid (Pullback f g)
pullback-isGroupoid = PullbackGroupoid.isGroupoid

pullback-square-isGroupoid : {X Y C T : CAT} {f : MAP X C} {g : MAP Y C}
  (s : Cone f g T) → IsPullback s → IsGroupoid X → IsGroupoid Y → IsGroupoid T
pullback-square-isGroupoid {f = f} {g} s es ex ey =
  equivalence-reflects-groupoid (pullbackLift s) es (pullback-isGroupoid f g ex ey)
```
