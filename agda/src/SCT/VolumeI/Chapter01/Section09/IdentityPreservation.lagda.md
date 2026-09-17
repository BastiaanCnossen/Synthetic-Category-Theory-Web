# Functors preserve identity morphisms with their endpoints

The constant diagram comparison lifts through uncurrying. Its two endpoint
equations are the same calculation at `0` and `1`: cancel the currying
comparisons, apply the pentagon and unit law, and restore the frames.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section06.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section09.WalkingMorphism as Walking

module SCT.VolumeI.Chapter01.Section09.IdentityPreservation
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter01.Section09.Morphisms 𝒯 M ℱ I public
open import SCT.VolumeI.Chapter01.Section09.DiagramComparisons 𝒯 M ℱ I using (module Lift)
import SCT.VolumeI.Chapter01.Section09.IdentityBoundaries as Boundaries
open import SCT.VolumeI.Chapter01.Section08.EvaluationSquares 𝒯 using (append-square)
import SCT.VolumeI.Chapter01.Section02.Structural as Structural
import SCT.VolumeI.Chapter01.Section02.PairingNaturality as PN
import SCT.VolumeI.Chapter01.Section01.Isomorphisms as Iso
open Structural vocabulary terminal products productLaws composition whiskering using (whisker-mixed-at)
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-right)
open Iso vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)

remove-last : {X C : CAT} {u v w z : MAP X C}
  (p : =₁ w z) (q : =₁ v w) (r : =₁ u v) →
  =₂ ((p ∙ (q ∙ r)) ∙ invIso r) (p ∙ q)
remove-last p q r = cancel-right r (p ∙ q) ∙
  isoComp-cong (invIso (isoComp-assoc-at p q r)) (idIso (invIso r))

module Endpoint {Γ C D : CAT} (x : Obj-abs [1]) (F : MAP C D) (f : MAP Γ C) where
  i : MAP Γ (Γ × [1])
  i = insert {X = Γ} x
  h : MAP Γ (Ar C)
  h = funCurry (f ∘ pr₁)
  k : MAP Γ (Ar D)
  k = funCurry ((F ∘ f) ∘ pr₁)
  H : MAP Γ (Ar D)
  H = funPost F ∘ h
  ah : =₁ (funUncurry h) (f ∘ pr₁)
  ah = funCurry-β (f ∘ pr₁)
  bk : =₁ (funUncurry k) ((F ∘ f) ∘ pr₁)
  bk = funCurry-β ((F ∘ f) ∘ pr₁)
  u : =₁ (funUncurry H) (F ∘ funUncurry h)
  u = funPost-uncurry F h
  v : =₁ (F ∘ (f ∘ pr₁ {Γ} {[1]})) ((F ∘ f) ∘ pr₁)
  v = invIso (comp-assoc pr₁ f F)
  ψ : =₁ (funUncurry H) ((F ∘ f) ∘ pr₁)
  ψ = v ∙ ((F ◁ ah) ∙ u)
  θ : =₁ (funUncurry H) (funUncurry k)
  θ = invIso bk ∙ ψ
  r : =₁ (evaluate x ∘ h) (funUncurry h ∘ i)
  r = evaluate-uncurry x h
  s : =₁ (evaluate x ∘ k) (funUncurry k ∘ i)
  s = evaluate-uncurry x k
  t : =₁ (evaluate x ∘ H) (funUncurry H ∘ i)
  t = evaluate-uncurry x H
  e : =₁ ((f ∘ pr₁) ∘ i) f
  e = identity-boundary x f
  d : =₁ (((F ∘ f) ∘ pr₁) ∘ i) (F ∘ f)
  d = identity-boundary x (F ∘ f)
  Ah : =₁ ((F ∘ funUncurry h) ∘ i) (F ∘ (funUncurry h ∘ i))
  Ah = comp-assoc i (funUncurry h) F
  A : =₁ ((F ∘ (f ∘ pr₁)) ∘ i) (F ∘ ((f ∘ pr₁) ∘ i))
  A = comp-assoc i (f ∘ pr₁) F
  before : =₁ (evaluate x ∘ H) (F ∘ f)
  before = post-boundary x F h (e ∙ ((ah ▷ i) ∙ r))
  after : =₁ (evaluate x ∘ k) (F ∘ f)
  after = d ∙ ((bk ▷ i) ∙ s)
  normal : =₁ (funUncurry H ∘ i) (F ∘ f)
  normal = (F ◁ (e ∙ (ah ▷ i))) ∙ (Ah ∙ (u ▷ i))

  abstract
    source-normal : =₂ (before ∙ invIso t) normal
    source-normal = isoComp-cong (postWhisker F ◁ remove-last e (ah ▷ i) r) (idIso (Ah ∙ (u ▷ i))) ∙
      (remove-last (F ◁ ((e ∙ ((ah ▷ i) ∙ r)) ∙ invIso r)) (Ah ∙ (u ▷ i)) t ∙
        isoComp-cong (isoComp-cong (idIso (F ◁ ((e ∙ ((ah ▷ i) ∙ r)) ∙ invIso r)))
          (invIso (isoComp-assoc-at Ah (u ▷ i) t))) (idIso (invIso t)))

    target-normal : =₂ (after ∙ invIso s) (d ∙ (bk ▷ i))
    target-normal = remove-last d (bk ▷ i) s

    cancel-target : =₂ ((d ∙ (bk ▷ i)) ∙ (θ ▷ i)) (d ∙ (ψ ▷ i))
    cancel-target = isoComp-cong (idIso d)
      ((preWhisker i ◁ cancel-inverse bk ψ) ∙ invIso (preWhisker-isoComp-at bk θ i)) ∙
        isoComp-assoc-at d (bk ▷ i) (θ ▷ i)

    middle : =₂ (d ∙ (ψ ▷ i)) normal
    middle = isoComp-cong (invIso (postWhisker-isoComp-at F e (ah ▷ i))) (idIso (Ah ∙ (u ▷ i))) ∙
      (invIso (isoComp-assoc-at (F ◁ e) (F ◁ (ah ▷ i)) (Ah ∙ (u ▷ i))) ∙
      (isoComp-cong (idIso (F ◁ e))
        (append-square A ((F ◁ ah) ▷ i) (F ◁ (ah ▷ i)) Ah (u ▷ i) (whisker-mixed-at ah i F)) ∙
      (append-square d (v ▷ i) (F ◁ e) A (((F ◁ ah) ▷ i) ∙ (u ▷ i))
        (Boundaries.Boundary.comparison 𝒯 M ℱ I x F f) ∙
      (isoComp-cong (idIso d) (isoComp-cong (idIso (v ▷ i)) (preWhisker-isoComp-at (F ◁ ah) u i)) ∙
        isoComp-cong (idIso d) (preWhisker-isoComp-at v ((F ◁ ah) ∙ u) i)))))

    compatible : =₂ ((after ∙ invIso s) ∙ (θ ▷ i)) (before ∙ invIso t)
    compatible = invIso source-normal ∙
      (middle ∙ (cancel-target ∙ isoComp-cong target-normal (idIso (θ ▷ i))))

post-identity : {Γ C D : CAT} (F : MAP C D) (f : MAP Γ C) →
  ExpressionIso (post-expression F (identity-expression f)) (identity-expression (F ∘ f))
post-identity F f = Lift.comparison (post-expression F (identity-expression f))
  (identity-expression (F ∘ f)) (Endpoint.θ zero F f)
  (Endpoint.compatible zero F f) (Endpoint.compatible one F f)
```


