# Whiskering with parameters

The selected primitive laws specialize to arbitrary parameter categories. These calculations use the two fixed-input interchange clauses, without assuming joint interchange.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Calculus as Calculus

module SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.ParameterizedWhiskering {l : Level} (T : Theory l l l) where
open View T
open Calculus T

-- Specializations of the selected primitive witnesses, with arbitrary
-- parameter category. These do not assume joint interchange.
opaque
  post-comp : {X C D E : CAT} {f g h : MAP C D}
    (u : MAP D E) (beta : MAP X (g ＝ h)) (alpha : MAP X (f ＝ g))
    → (u ◁ (beta ∙ alpha)) =₁ ((u ◁ beta) ∙ (u ◁ alpha))
  post-comp {f = f} {g} {h} u beta alpha =
    specialize (postWhisker-isoComp f g h u) (pair beta alpha)
      (postWhisker-evaluate u (pr₁ ∙ pr₂) (pair beta alpha)
        (isoComp-evaluate pr₁ pr₂ (pair beta alpha) (pair-β₁ beta alpha) (pair-β₂ beta alpha)))
      (isoComp-evaluate (u ◁ pr₁) (u ◁ pr₂) (pair beta alpha)
        (postWhisker-evaluate u pr₁ (pair beta alpha) (pair-β₁ beta alpha))
        (postWhisker-evaluate u pr₂ (pair beta alpha) (pair-β₂ beta alpha)))

  pre-comp : {X B C D : CAT} {f g h : MAP C D}
    (beta : MAP X (g ＝ h)) (alpha : MAP X (f ＝ g)) (k : MAP B C)
    → ((beta ∙ alpha) ▷ k) =₁ ((beta ▷ k) ∙ (alpha ▷ k))
  pre-comp {f = f} {g} {h} beta alpha k =
    specialize (preWhisker-isoComp f g h k) (pair beta alpha)
      (preWhisker-evaluate (pr₁ ∙ pr₂) k (pair beta alpha)
        (isoComp-evaluate pr₁ pr₂ (pair beta alpha) (pair-β₁ beta alpha) (pair-β₂ beta alpha)))
      (isoComp-evaluate (pr₁ ▷ k) (pr₂ ▷ k) (pair beta alpha)
        (preWhisker-evaluate pr₁ k (pair beta alpha) (pair-β₁ beta alpha))
        (preWhisker-evaluate pr₂ k (pair beta alpha) (pair-β₂ beta alpha)))

  fixed-outer : {X B C D : CAT} {F G : MAP C D} {h k : MAP B C}
    (tau : F =₁ G) (sigma : MAP X (h ＝ k))
    → (const (tau ▷ k) ∙ (F ◁ sigma)) =₁ ((G ◁ sigma) ∙ const (tau ▷ h))
  fixed-outer {F = F} {G} {h} {k} tau sigma =
    specialize (interchange-fixedOuter F G h k tau) sigma
      (isoComp-evaluate (const (tau ▷ k)) (F ◁ id _) sigma
        (const-pre (tau ▷ k) sigma) (postWhisker-evaluate F (id _) sigma (comp-unitˡ sigma)))
      (isoComp-evaluate (G ◁ id _) (const (tau ▷ h)) sigma
        (postWhisker-evaluate G (id _) sigma (comp-unitˡ sigma)) (const-pre (tau ▷ h) sigma))

  fixed-inner : {X B C D : CAT} {F G : MAP C D} {h k : MAP B C}
    (tau : MAP X (F ＝ G)) (sigma : h =₁ k)
    → ((tau ▷ k) ∙ const (F ◁ sigma)) =₁ (const (G ◁ sigma) ∙ (tau ▷ h))
  fixed-inner {F = F} {G} {h} {k} tau sigma =
    specialize (interchange-fixedInner F G h k sigma) tau
      (isoComp-evaluate (id _ ▷ k) (const (F ◁ sigma)) tau
        (preWhisker-evaluate (id _) k tau (comp-unitˡ tau)) (const-pre (F ◁ sigma) tau))
      (isoComp-evaluate (const (G ◁ sigma)) (id _ ▷ h) tau
        (const-pre (G ◁ sigma) tau) (preWhisker-evaluate (id _) h tau (comp-unitˡ tau)))

opaque
  horizontal-pre : {X Y B C D : CAT} {f f' : MAP B C} {g g' : MAP C D}
    (beta : MAP X (g ＝ g')) (alpha : MAP X (f ＝ f')) (r : MAP Y X)
    → ((beta ⋆ alpha) ∘ r) =₁ ((beta ∘ r) ⋆ (alpha ∘ r))
  horizontal-pre {f' = f'} {g = g} beta alpha r =
    isoComp-evaluate (beta ▷ f') (g ◁ alpha) r
      (preWhisker-pre beta f' r) (postWhisker-pre g alpha r)

  horizontal-evaluate : {X Y B C D : CAT} {f f' : MAP B C} {g g' : MAP C D}
    (beta : MAP X (g ＝ g')) (alpha : MAP X (f ＝ f')) (r : MAP Y X)
    {beta' : MAP Y (g ＝ g')} {alpha' : MAP Y (f ＝ f')}
    → (beta ∘ r) =₁ beta' → (alpha ∘ r) =₁ alpha'
    → ((beta ⋆ alpha) ∘ r) =₁ (beta' ⋆ alpha')
  horizontal-evaluate beta alpha r b a = horizontal-pre beta alpha r then hcomp-cong b a

  horizontal-unit-left : {X C D : CAT} {f g : MAP C D} (alpha : MAP X (f ＝ g))
    → (const (comp-unitˡ g) ∙ (const (idIso (id D)) ⋆ alpha)) =₁ (alpha ∙ const (comp-unitˡ f))
  horizontal-unit-left {D = D} {f} {g} alpha = specialize (hcomp-unitˡ f g) alpha
    (isoComp-evaluate (const (comp-unitˡ g)) (const (idIso (id D)) ⋆ id _) alpha
      (const-pre (comp-unitˡ g) alpha)
      (horizontal-evaluate (const (idIso (id D))) (id _) alpha (const-pre (idIso (id D)) alpha) (comp-unitˡ alpha)))
    (isoComp-evaluate (id _) (const (comp-unitˡ f)) alpha (comp-unitˡ alpha) (const-pre (comp-unitˡ f) alpha))

  horizontal-unit-right : {X C D : CAT} {f g : MAP C D} (alpha : MAP X (f ＝ g))
    → (const (comp-unitʳ g) ∙ (alpha ⋆ const (idIso (id C)))) =₁ (alpha ∙ const (comp-unitʳ f))
  horizontal-unit-right {C = C} {f = f} {g} alpha = specialize (hcomp-unitʳ f g) alpha
    (isoComp-evaluate (const (comp-unitʳ g)) (id _ ⋆ const (idIso (id C))) alpha
      (const-pre (comp-unitʳ g) alpha)
      (horizontal-evaluate (id _) (const (idIso (id C))) alpha (comp-unitˡ alpha) (const-pre (idIso (id C)) alpha)))
    (isoComp-evaluate (id _) (const (comp-unitʳ f)) alpha (comp-unitˡ alpha) (const-pre (comp-unitʳ f) alpha))

  horizontal-assoc : {X B C D E : CAT} {f f' : MAP B C} {g g' : MAP C D} {h h' : MAP D E}
    (gamma : MAP X (h ＝ h')) (beta : MAP X (g ＝ g')) (alpha : MAP X (f ＝ f'))
    → (const (comp-assoc f' g' h') ∙ ((gamma ⋆ beta) ⋆ alpha)) =₁
      ((gamma ⋆ (beta ⋆ alpha)) ∙ const (comp-assoc f g h))
  horizontal-assoc {f = f} {f'} {g} {g'} {h} {h'} gamma beta alpha =
    let r = pair (pair gamma beta) alpha
        a = pair-β₂ (pair gamma beta) alpha
        b = comp-assoc r pr₁ pr₂ then (pr₂ ◁ pair-β₁ (pair gamma beta) alpha) then pair-β₂ gamma beta
        c = comp-assoc r pr₁ pr₁ then (pr₁ ◁ pair-β₁ (pair gamma beta) alpha) then pair-β₁ gamma beta
    in specialize (hcomp-assoc f f' g g' h h') r
      (isoComp-evaluate (const (comp-assoc f' g' h')) (((pr₁ ∘ pr₁) ⋆ (pr₂ ∘ pr₁)) ⋆ pr₂) r
        (const-pre (comp-assoc f' g' h') r)
        (horizontal-evaluate ((pr₁ ∘ pr₁) ⋆ (pr₂ ∘ pr₁)) pr₂ r
          (horizontal-evaluate (pr₁ ∘ pr₁) (pr₂ ∘ pr₁) r c b) a))
      (isoComp-evaluate ((pr₁ ∘ pr₁) ⋆ ((pr₂ ∘ pr₁) ⋆ pr₂)) (const (comp-assoc f g h)) r
        (horizontal-evaluate (pr₁ ∘ pr₁) ((pr₂ ∘ pr₁) ⋆ pr₂) r c
          (horizontal-evaluate (pr₂ ∘ pr₁) pr₂ r b a)) (const-pre (comp-assoc f g h) r))
```
