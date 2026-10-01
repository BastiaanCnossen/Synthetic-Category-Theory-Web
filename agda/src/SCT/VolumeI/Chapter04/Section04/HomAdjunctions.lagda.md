# The hom-equivalence supplied by an adjunction

Apply the unit and counit transposition formulas to the universal families
in the two endpoint pullbacks. Their restriction and endpoint-change laws
make them functors over the chosen base; their inverse equations make the
underlying functors equivalences. The earlier relative-equivalence theorem
then supplies an inverse and both inverse identifications over the base.

Taking the base to be the product of the two categories gives the endpoint
presentation of the forward implication in
`prop:Adjunctions_Via_Natural_Equivalence_Hom_Groupoids`. The converse is a
separate result. The directed-pullback version below changes the identity-functor endpoint
frames by the specified unit identifications.

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

module SCT.VolumeI.Chapter04.Section04.HomAdjunctions
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter04.Section04.Adjunctions 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.EndpointFiberOperations 𝒯 M ℱ P I
  using (ExpressionOperation; module Realize; module Lifts)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P using (FunctorOver; identity-over; compose-over)
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P using (FunctorOverIso)
import SCT.VolumeI.Chapter03.RelativeCategories.Equivalences as Relative
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.EndpointFiberEquivalences as EndpointsChange
import SCT.VolumeI.Chapter04.Section01.DirectedPullbacks as Directed
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.SealedFamilyTransposition as Transposition
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.TransposeFamilies as Families
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P using (Cone; ConeIso; conePre; coneIso-compose)
open Laws.PullbackStructure P using (pullbackCone)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.EndpointFiberOperationEquivalences 𝒯 M ℱ P I
  using (ExpressionOperationEquivalence)

module HomEquivalence {B C D : CAT} {l : MAP C D} {r : MAP D C}
  (adj : Adjunction l r) (x : MAP B C) (y : MAP B D) where
  private
    module Transposes = ExpressionOperationEquivalence (Transposition.transposition 𝒯 M ℱ P I E S Q adj x y)
  module Left = EndpointFiber (l ∘ x) y
  module Right = EndpointFiber x (r ∘ y)

  forward-operation : ExpressionOperation (l ∘ x) y x (r ∘ y)
  forward-operation = Transposes.forward

  backward-operation : ExpressionOperation x (r ∘ y) (l ∘ x) y
  backward-operation = Transposes.backward

  functor : MAP Left.category Right.category
  functor = Realize.functor forward-operation

  -- Name the universal input and encoded output before specializing their
  -- computation. These are the existing expressions, with explicit types.
  forward-universal : MorphismExpression
    ((l ∘ x) ∘ Left.base) (y ∘ Left.base)
  forward-universal = Realize.universal forward-operation

  encoded-forward-expression : MorphismExpression
    (x ∘ Left.base) ((r ∘ y) ∘ Left.base)
  encoded-forward-expression = ExpressionOperation.apply forward-operation Left.base forward-universal

  -- Keep the literal unit-transposition expression and its complete boundary.
  forward-expression : MorphismExpression
    (x ∘ Left.base) ((r ∘ y) ∘ Left.base)
  forward-expression = Families.Families.forward 𝒯 M ℱ P I E S adj x y
    Left.base forward-universal

  forward-cone : Cone endpoints (pair x (r ∘ y)) Left.category
  forward-cone = Right.cone Left.base forward-expression

  abstract
    forward-computation : ConeIso
      (conePre functor (pullbackCone endpoints (pair x (r ∘ y)))) forward-cone
    forward-computation = coneIso-compose
      (Lifts.encode-cong x (r ∘ y) Left.base
        {f = encoded-forward-expression} {g = forward-expression}
        (Transposition.forward-computation 𝒯 M ℱ P I E S Q adj x y
          Left.base forward-universal))
      (Right.lift-β Left.base encoded-forward-expression)

  isEquiv : IsEquiv functor
  isEquiv = Transposes.isEquiv

  over-base : FunctorOver Left.base Right.base
  over-base = record { lift = functor ; comparison = Realize.base forward-operation }

  private
    module Over = Relative.Inverse 𝒯 M ℱ P over-base isEquiv using (inverse; left-inverse; right-inverse)

  inverse-over-base : FunctorOver Right.base Left.base
  inverse-over-base = Over.inverse

  left-inverse-over-base : FunctorOverIso (compose-over inverse-over-base over-base) (identity-over Left.base)
  left-inverse-over-base = Over.left-inverse

  right-inverse-over-base : FunctorOverIso (compose-over over-base inverse-over-base) (identity-over Right.base)
  right-inverse-over-base = Over.right-inverse

private
  inverse-triangle : {A B T : CAT} {p : MAP A T} {q : MAP B T}
    (f : FunctorOver p q) (e : IsEquiv (FunctorLift.lift f)) → FunctorOver q p
  inverse-triangle {q = q} f e = record
    { lift = IsEquiv.inverse e
    ; comparison = comp-unitʳ q ∙
        (q ◁ (IsEquiv.retractionIso e) ⁻¹) ∙
        comp-assoc (IsEquiv.inverse e) (FunctorLift.lift f) q ∙
        (FunctorLift.comparison f ▷ IsEquiv.inverse e) ⁻¹ }

module DirectedHomEquivalence {C D : CAT} {l : MAP C D} {r : MAP D C}
  (adj : Adjunction l r) where
  module Left = Directed.DirectedPullback 𝒯 M ℱ P I l (id D)
  module Right = Directed.DirectedPullback 𝒯 M ℱ P I (id C) r
  private
    module H = HomEquivalence adj (pr₁ {C = C} {D = D}) pr₂
      using (functor; isEquiv; over-base)
    module L = EndpointsChange.ChangeEndpoints 𝒯 M ℱ P I
      {u = l ∘ pr₁ {C = C} {D = D}} {v = id D ∘ pr₂}
      {u′ = l ∘ pr₁} {v′ = pr₂}
      (idIso (l ∘ pr₁)) (comp-unitˡ pr₂) using (map; map-isEquiv; projection)
    module R = EndpointsChange.ChangeEndpoints 𝒯 M ℱ P I
      {u = id C ∘ pr₁ {C = C} {D = D}} {v = r ∘ pr₂}
      {u′ = pr₁} {v′ = r ∘ pr₂}
      (comp-unitˡ pr₁) (idIso (r ∘ pr₂)) using (map; map-isEquiv; projection)

    left-change : FunctorOver Left.base (EndpointFiber.base (l ∘ pr₁) pr₂)
    left-change = record { lift = L.map ; comparison = L.projection }

    right-change : FunctorOver Right.base (EndpointFiber.base pr₁ (r ∘ pr₂))
    right-change = record { lift = R.map ; comparison = R.projection }

  over-base : FunctorOver Left.base Right.base
  over-base = compose-over (inverse-triangle right-change R.map-isEquiv) (compose-over H.over-base left-change)

  functor : MAP Left.category Right.category
  functor = FunctorLift.lift over-base

  isEquiv : IsEquiv functor
  isEquiv = equiv-compose (H.functor ∘ L.map) (IsEquiv.inverse R.map-isEquiv)
    (equiv-compose L.map H.functor L.map-isEquiv H.isEquiv) (equiv-inverse R.map-isEquiv)

  equivalence : Equiv Left.category Right.category
  equivalence = record { functor = functor ; isEquiv = isEquiv }

  private
    module Over = Relative.Inverse 𝒯 M ℱ P over-base isEquiv using (inverse; left-inverse; right-inverse)

  inverse-over-base : FunctorOver Right.base Left.base
  inverse-over-base = Over.inverse

  left-inverse-over-base : FunctorOverIso (compose-over inverse-over-base over-base) (identity-over Left.base)
  left-inverse-over-base = Over.left-inverse

  right-inverse-over-base : FunctorOverIso (compose-over over-base inverse-over-base) (identity-over Right.base)
  right-inverse-over-base = Over.right-inverse
```
