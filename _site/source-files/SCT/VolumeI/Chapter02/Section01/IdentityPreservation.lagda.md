# Functors preserve identity morphisms with their endpoints

The constant diagram comparison lifts through uncurrying. Its two endpoint
equations are the same calculation at `0` and `1`: cancel the currying
comparisons, apply the pentagon and unit law, and restore the frames.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking

module SCT.VolumeI.Chapter02.Section01.IdentityPreservation
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter02.Section01.Morphisms 𝒯 M ℱ I public
open import SCT.VolumeI.Chapter02.Section01.DiagramComparisons 𝒯 M ℱ I using (module Lift)
import SCT.VolumeI.Chapter02.Section01.IdentityBoundaries as Boundaries
open import SCT.VolumeI.Chapter01.Section08.EvaluationSquares 𝒯 using (append-square)
import SCT.VolumeI.Chapter01.Section03.Structural as Structural
import SCT.VolumeI.Chapter01.Section03.PairingNaturality as PN
import SCT.VolumeI.Chapter01.Section02.Isomorphisms as Iso
open Structural vocabulary terminal products productLaws composition whiskering using (whisker-mixed-at)
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-right)
open Iso vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)

remove-last : {X C : CAT} {u v w z : MAP X C}
  (p : w =₁ z) (q : v =₁ w) (r : u =₁ v) →
  ((p ∙ (q ∙ r)) ∙ r ⁻¹) =₂ (p ∙ q)
remove-last p q r = cancel-right r (p ∙ q) ∙
  isoComp-cong ((isoComp-assoc-at p q r) ⁻¹) (idIso (r ⁻¹))

module Endpoint {Γ C D : CAT} (x : Obj-abs [1]) (F : MAP C D) (f : MAP Γ C) where
  i : MAP Γ (Γ × [1])
  i = insert {X = Γ} x
  h : MAP Γ (Ar C)
  h = funCurry (f ∘ pr₁)
  k : MAP Γ (Ar D)
  k = funCurry ((F ∘ f) ∘ pr₁)
  H : MAP Γ (Ar D)
  H = funPost F ∘ h
  ah : (funUncurry h) =₁ (f ∘ pr₁)
  ah = funCurry-β (f ∘ pr₁)
  bk : (funUncurry k) =₁ ((F ∘ f) ∘ pr₁)
  bk = funCurry-β ((F ∘ f) ∘ pr₁)
  u : (funUncurry H) =₁ (F ∘ funUncurry h)
  u = funPost-uncurry F h
  v : (F ∘ (f ∘ pr₁ {Γ} {[1]})) =₁ ((F ∘ f) ∘ pr₁)
  v = (comp-assoc pr₁ f F) ⁻¹
  ψ : (funUncurry H) =₁ ((F ∘ f) ∘ pr₁)
  ψ = v ∙ ((F ◁ ah) ∙ u)
  θ : (funUncurry H) =₁ (funUncurry k)
  θ = bk ⁻¹ ∙ ψ
  r : (evaluate x ∘ h) =₁ (funUncurry h ∘ i)
  r = evaluate-uncurry x h
  s : (evaluate x ∘ k) =₁ (funUncurry k ∘ i)
  s = evaluate-uncurry x k
  t : (evaluate x ∘ H) =₁ (funUncurry H ∘ i)
  t = evaluate-uncurry x H
  e : ((f ∘ pr₁) ∘ i) =₁ f
  e = identity-boundary x f
  d : (((F ∘ f) ∘ pr₁) ∘ i) =₁ (F ∘ f)
  d = identity-boundary x (F ∘ f)
  Ah : ((F ∘ funUncurry h) ∘ i) =₁ (F ∘ (funUncurry h ∘ i))
  Ah = comp-assoc i (funUncurry h) F
  A : ((F ∘ (f ∘ pr₁)) ∘ i) =₁ (F ∘ ((f ∘ pr₁) ∘ i))
  A = comp-assoc i (f ∘ pr₁) F
  before : (evaluate x ∘ H) =₁ (F ∘ f)
  before = post-boundary x F h (e ∙ ((ah ▷ i) ∙ r))
  after : (evaluate x ∘ k) =₁ (F ∘ f)
  after = d ∙ ((bk ▷ i) ∙ s)
  normal : (funUncurry H ∘ i) =₁ (F ∘ f)
  normal = (F ◁ (e ∙ (ah ▷ i))) ∙ (Ah ∙ (u ▷ i))

  abstract
    source-normal : (before ∙ t ⁻¹) =₂ normal
    source-normal = isoComp-cong (postWhisker F ◁ remove-last e (ah ▷ i) r) (idIso (Ah ∙ (u ▷ i))) ∙
      (remove-last (F ◁ ((e ∙ ((ah ▷ i) ∙ r)) ∙ r ⁻¹)) (Ah ∙ (u ▷ i)) t ∙
        isoComp-cong (isoComp-cong (idIso (F ◁ ((e ∙ ((ah ▷ i) ∙ r)) ∙ r ⁻¹)))
          ((isoComp-assoc-at Ah (u ▷ i) t) ⁻¹)) (idIso (t ⁻¹)))

    target-normal : (after ∙ s ⁻¹) =₂ (d ∙ (bk ▷ i))
    target-normal = remove-last d (bk ▷ i) s

    cancel-target : ((d ∙ (bk ▷ i)) ∙ (θ ▷ i)) =₂ (d ∙ (ψ ▷ i))
    cancel-target = isoComp-cong (idIso d)
      ((preWhisker i ◁ cancel-inverse bk ψ) ∙ (preWhisker-isoComp-at bk θ i) ⁻¹) ∙
        isoComp-assoc-at d (bk ▷ i) (θ ▷ i)

    middle : (d ∙ (ψ ▷ i)) =₂ normal
    middle = isoComp-cong ((postWhisker-isoComp-at F e (ah ▷ i)) ⁻¹) (idIso (Ah ∙ (u ▷ i))) ∙
      ((isoComp-assoc-at (F ◁ e) (F ◁ (ah ▷ i)) (Ah ∙ (u ▷ i))) ⁻¹ ∙
      (isoComp-cong (idIso (F ◁ e))
        (append-square A ((F ◁ ah) ▷ i) (F ◁ (ah ▷ i)) Ah (u ▷ i) (whisker-mixed-at ah i F)) ∙
      (append-square d (v ▷ i) (F ◁ e) A (((F ◁ ah) ▷ i) ∙ (u ▷ i))
        (Boundaries.Boundary.comparison 𝒯 M ℱ I x F f) ∙
      (isoComp-cong (idIso d) (isoComp-cong (idIso (v ▷ i)) (preWhisker-isoComp-at (F ◁ ah) u i)) ∙
        isoComp-cong (idIso d) (preWhisker-isoComp-at v ((F ◁ ah) ∙ u) i)))))

    compatible : ((after ∙ s ⁻¹) ∙ (θ ▷ i)) =₂ (before ∙ t ⁻¹)
    compatible = source-normal ⁻¹ ∙
      (middle ∙ (cancel-target ∙ isoComp-cong target-normal (idIso (θ ▷ i))))

post-identity : {Γ C D : CAT} (F : MAP C D) (f : MAP Γ C) →
  ExpressionIso (post-expression F (identity-expression f)) (identity-expression (F ∘ f))
post-identity F f = Lift.comparison (post-expression F (identity-expression f))
  (identity-expression (F ∘ f)) (Endpoint.θ zero F f)
  (Endpoint.compatible zero F f) (Endpoint.compatible one F f)
```


