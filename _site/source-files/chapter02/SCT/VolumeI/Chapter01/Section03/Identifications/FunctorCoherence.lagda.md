# Coherence of functor composition

The coherence axioms state the pentagon and the triangle with horizontal
composites with identity identifications. Calculations use them with
whiskerings instead; the first part rewrites them in that form, as diagrams
of Section02.Coherence. Calculations that solve the pentagon for a corner
also use its target route right-associated (`pentagon-whiskered-right`). From the whiskered pentagon and triangle we derive
Kelly's lemmas: the right and left unitors are compatible with composition,
and the two unitors agree at an identity functor. The proofs reflect
equations through whiskering by an identity functor, which is possible
because whiskering by an identity is identified with the identity by the
unitors. These are consequences of the supplied axioms; no coherence
theorem beyond them is assumed.

The laws about fixed specified identifications (associators and unitors) are
stated for individual identifications. The first section therefore records
the individual forms of the five whiskering laws and of the horizontal
identity normalizations; they are the family laws at `One`, with constant
sides identified with their values.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section03.Identifications.FunctorCoherence where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary hiding (_＝_)
import SCT.VolumeI.Chapter01.Section01.Terms as Terms
open Terms using (Equal)
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal using (module Constructions)
open Constructions
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (id₌; comp-unitˡ; comp-unitʳ; comp-assoc; comp-pentagon; comp-triangle;
    associativityPentagon; unitTriangle; module Composition; module Boundaries)
open Composition
open Boundaries
open import SCT.VolumeI.Chapter01.Section02.Specialization
open import SCT.VolumeI.Chapter01.Section02.Whiskering
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses
open import SCT.VolumeI.Chapter01.Section03.Identifications.IdentificationSquares
```

## Individual identifications

```agda
module _ {Γ : Context} where
  postWhisker-id-One : {C D : CAT Γ} {f g : MAP C D} (α : f =₁ g)
    → (comp-unitˡ g ∙ (id D ◁ α)) =₂ (α ∙ comp-unitˡ f)
  postWhisker-id-One {D = D} {f} {g} α = unconst-sides₌
    {t = id D ◁ α} {b = α} {l = comp-unitˡ f} {r = comp-unitˡ g} (postWhisker-id α)

  preWhisker-id-One : {C D : CAT Γ} {f g : MAP C D} (α : f =₁ g)
    → (comp-unitʳ g ∙ (α ▷ id C)) =₂ (α ∙ comp-unitʳ f)
  preWhisker-id-One {C} {f = f} {g} α = unconst-sides₌
    {t = α ▷ id C} {b = α} {l = comp-unitʳ f} {r = comp-unitʳ g} (preWhisker-id α)

  postWhisker-comp-One : {C D E F : CAT Γ} {f g : MAP C D}
    (α : f =₁ g) (u : MAP D E) (v : MAP E F)
    → (comp-assoc g u v ∙ ((v ∘ u) ◁ α)) =₂ ((v ◁ (u ◁ α)) ∙ comp-assoc f u v)
  postWhisker-comp-One {f = f} {g} α u v = unconst-sides₌
    {t = (v ∘ u) ◁ α} {b = v ◁ (u ◁ α)} {l = comp-assoc f u v} {r = comp-assoc g u v}
    (postWhisker-comp α u v)

  preWhisker-comp-One : {A B C D : CAT Γ} {f g : MAP C D}
    (α : f =₁ g) (k : MAP B C) (l : MAP A B)
    → (comp-assoc l k g ∙ ((α ▷ k) ▷ l)) =₂ ((α ▷ (k ∘ l)) ∙ comp-assoc l k f)
  preWhisker-comp-One {f = f} {g} α k l = unconst-sides₌
    {t = (α ▷ k) ▷ l} {b = α ▷ (k ∘ l)} {l = comp-assoc l k f} {r = comp-assoc l k g}
    (preWhisker-comp α k l)

  whisker-mixed-One : {B C D E : CAT Γ} {f g : MAP C D}
    (α : f =₁ g) (k : MAP B C) (u : MAP D E)
    → (comp-assoc k g u ∙ ((u ◁ α) ▷ k)) =₂ ((u ◁ (α ▷ k)) ∙ comp-assoc k f u)
  whisker-mixed-One {f = f} {g} α k u = unconst-sides₌
    {t = (u ◁ α) ▷ k} {b = u ◁ (α ▷ k)} {l = comp-assoc k f u} {r = comp-assoc k g u}
    (whisker-mixed α k u)

  hcomp-id-outer-One : {C D E : CAT Γ} {f f′ : MAP C D}
    (g : MAP D E) (α : f =₁ f′) → (id₌ g ⋆ α) =₂ (g ◁ α)
  hcomp-id-outer-One g α =
    hcomp-id-outer g α ∙ hcomp-cong ((const-One (id₌ g)) ⁻¹) (id₌ α)

  hcomp-id-inner-One : {C D E : CAT Γ} {g g′ : MAP D E}
    (β : g =₁ g′) (f : MAP C D) → (β ⋆ id₌ f) =₂ (β ▷ f)
  hcomp-id-inner-One β f =
    hcomp-id-inner β f ∙ hcomp-cong (id₌ β) ((const-One (id₌ f)) ⁻¹)

  assoc-natural-One : {B C D E : CAT Γ}
    {f f′ : MAP B C} {g g′ : MAP C D} {h h′ : MAP D E}
    (γ : h =₁ h′) (β : g =₁ g′) (α : f =₁ f′)
    → (comp-assoc f′ g′ h′ ∙ ((γ ⋆ β) ⋆ α)) =₂ ((γ ⋆ (β ⋆ α)) ∙ comp-assoc f g h)
  assoc-natural-One {f = f} {f′} {g} {g′} {h} {h′} γ β α = unconst-sides₌
    {t = (γ ⋆ β) ⋆ α} {b = γ ⋆ (β ⋆ α)} {l = comp-assoc f g h} {r = comp-assoc f′ g′ h′}
    (assoc-natural γ β α)
```

## The whiskered pentagon and triangle

The whiskered pentagon has the vertices of the associativity pentagon; its
two outer target edges are whiskerings of associators instead of horizontal
composites with identities. The whiskered triangle likewise has the
whiskered unitors. Their commutativity follows from the axioms by replacing
those edges with the horizontal identity normalizations.

```agda
module _ {Γ : Context} where
  whiskeredPentagon : {A B C D E : CAT Γ} (f : MAP A B) (g : MAP B C)
    (h : MAP C D) (k : MAP D E)
    → PentagonDiagram {X = One}
        (((k ∘ h) ∘ g) ∘ f) ((k ∘ h) ∘ (g ∘ f)) (k ∘ (h ∘ (g ∘ f)))
        ((k ∘ (h ∘ g)) ∘ f) (k ∘ ((h ∘ g) ∘ f))
  whiskeredPentagon f g h k = pentagon-diagram
    (comp-assoc f g (k ∘ h)) (comp-assoc (g ∘ f) h k)
    (comp-assoc g h k ▷ f) (comp-assoc f (h ∘ g) k) (k ◁ comp-assoc f g h)

  pentagon-whiskered : {A B C D E : CAT Γ} (f : MAP A B) (g : MAP B C)
    (h : MAP C D) (k : MAP D E)
    → PentagonCommutes (whiskeredPentagon f g h k)
  pentagon-whiskered f g h k =
    comp₌-cong
      (comp₌-cong (hcomp-id-outer-One k (comp-assoc f g h)) (id₌ (comp-assoc f (h ∘ g) k)))
      (hcomp-id-inner-One (comp-assoc g h k) f)
    ∙ comp-pentagon f g h k

  whiskeredTriangle : {C D E : CAT Γ} (f : MAP C D) (g : MAP D E)
    → TriangleDiagram {X = One} ((g ∘ id D) ∘ f) (g ∘ (id D ∘ f)) (g ∘ f)
  whiskeredTriangle {D = D} f g = triangle-diagram
    (comp-unitʳ g ▷ f) (comp-assoc f (id D) g) (g ◁ comp-unitˡ f)

  triangle-whiskered : {C D E : CAT Γ} (f : MAP C D) (g : MAP D E)
    → TriangleCommutes (whiskeredTriangle f g)
  triangle-whiskered {D = D} f g =
    comp₌-cong (hcomp-id-outer-One g (comp-unitˡ f)) (id₌ (comp-assoc f (id D) g)) ∙
      (comp-triangle f g ∙ (hcomp-id-inner-One (comp-unitʳ g) f) ⁻¹)

  pentagon-whiskered-right : {A B C D E : CAT Γ} (f : MAP A B) (g : MAP B C)
    (h : MAP C D) (k : MAP D E)
    → (comp-assoc (g ∘ f) h k ∙ comp-assoc f g (k ∘ h)) =₂
        ((k ◁ comp-assoc f g h) ∙ (comp-assoc f (h ∘ g) k ∙ (comp-assoc g h k ▷ f)))
  pentagon-whiskered-right f g h k =
    comp₌-assoc (k ◁ comp-assoc f g h) (comp-assoc f (h ∘ g) k) (comp-assoc g h k ▷ f)
    ∙ pentagon-whiskered f g h k

```

## Reflection through whiskering by an identity

Whiskering a family by an identity functor is identified with the family by
the unitors, so an equation between two such whiskerings yields an equation
between the families. The same argument transfers equations between
whiskerings along composites and along identified whiskering functors; these
are transfers of an equation, not faithfulness of an arbitrary functor.

```agda
module _ {Γ : Context} where
  module _ {A : CAT Γ} where
    open Terms.Equalities A using (_＝_)

    preWhisker-id-reflect : {X C : CAT Γ} {f g : MAP X C} {α β : f ＝ g}
      → (α ▷ id X) =₁ (β ▷ id X) → α =₁ β
    preWhisker-id-reflect {f = f} {g} {α} {β} p =
      cancel-right (const (comp-unitʳ f))
        (preWhisker-id β ∙ (comp₌-cong (id₌ (const (comp-unitʳ g))) p ∙ (preWhisker-id α) ⁻¹))

    postWhisker-id-reflect : {X C : CAT Γ} {f g : MAP X C} {α β : f ＝ g}
      → (id C ◁ α) =₁ (id C ◁ β) → α =₁ β
    postWhisker-id-reflect {f = f} {g} {α} {β} p =
      cancel-right (const (comp-unitˡ f))
        (postWhisker-id β ∙ (comp₌-cong (id₌ (const (comp-unitˡ g))) p ∙ (postWhisker-id α) ⁻¹))

  module _ {X : CAT Γ} where
    open Terms.Equalities X using (_＝_)

    postWhisker-comp-transfer : {A B C D : CAT Γ} {f g : MAP A B}
      (u : MAP B C) (v : MAP C D) {α β : f ＝ g}
      → (v ◁ (u ◁ α)) =₁ (v ◁ (u ◁ β)) → ((v ∘ u) ◁ α) =₁ ((v ∘ u) ◁ β)
    postWhisker-comp-transfer {f = f} {g} u v {α} {β} p =
      cancel-left (const (comp-assoc g u v))
        ((postWhisker-comp β u v) ⁻¹ ∙
          (comp₌-cong p (id₌ (const (comp-assoc f u v))) ∙ postWhisker-comp α u v))

    postWhisker-change-transfer : {A B C : CAT Γ} {f g : MAP A B}
      {u v : MAP B C} (η : u =₁ v) {α β : f ＝ g}
      → (u ◁ α) =₁ (u ◁ β) → (v ◁ α) =₁ (v ◁ β)
    postWhisker-change-transfer {f = f} {g} η {α} {β} p =
      cancel-right (const (η ▷ f))
        (interchange-fixedOuter η β ∙
          (comp₌-cong (id₌ (const (η ▷ g))) p ∙ (interchange-fixedOuter η α) ⁻¹))
```

## Kelly's lemmas

The right unitor of a composite `π ∘ h` is the whiskered right unitor of `h`
followed by the associator, and dually for the left unitor. Each proof
computes one edge of a whiskered pentagon in two ways, using the triangle,
and reflects the resulting equation through whiskering by an identity.
Consequently the right and left unitors of an identity functor agree, and an
identification of an endofunctor with the identity is natural with respect
to itself.

```agda
module _ {Γ : Context} where

  right-unitor-comp : {X K C : CAT Γ} (h : MAP X K) (π : MAP K C)
    → (comp-unitʳ (π ∘ h)) =₂ ((π ◁ comp-unitʳ h) ∙ comp-assoc (id X) h π)
  right-unitor-comp {X} h π =
    let I = id X
        A = comp-assoc I h π
        B = comp-assoc I I (π ∘ h)
        C′ = comp-assoc (I ∘ I) h π
        D′ = comp-assoc I (h ∘ I) π
        E = A ▷ I
        L = comp-unitˡ I
        q = (π ∘ h) ◁ L
        t = π ◁ (h ◁ L)
        s = π ◁ comp-assoc I I h
        left-normal = comp₌-assoc t C′ B ∙
          (comp₌-cong (postWhisker-comp-One L h π) (id₌ B) ∙
          ((comp₌-assoc A q B) ⁻¹ ∙
            comp₌-cong (id₌ A) (triangle-whiskered I (π ∘ h))))
        triangle-h = postWhisker-comp₌ π (h ◁ L) (comp-assoc I I h) ∙
          (postWhisker π ◁ triangle-whiskered I h)
        right-normal = comp₌-cong (id₌ t) ((pentagon-whiskered-right I I h π) ⁻¹) ∙
          (comp₌-assoc t s (D′ ∙ E) ∙
          (comp₌-cong triangle-h (id₌ (D′ ∙ E)) ∙
          (comp₌-assoc (π ◁ (comp-unitʳ h ▷ I)) D′ E ∙
          (comp₌-cong (whisker-mixed-One (comp-unitʳ h) I π) (id₌ E) ∙
          ((comp₌-assoc A ((π ◁ comp-unitʳ h) ▷ I) E) ⁻¹ ∙
            comp₌-cong (id₌ A) (preWhisker-comp₌ (π ◁ comp-unitʳ h) A I))))))
    in preWhisker-id-reflect (cancel-left A (right-normal ⁻¹ ∙ left-normal))

  left-unitor-comp : {X K C : CAT Γ} (f : MAP X K) (g : MAP K C)
    → (comp-unitˡ (g ∘ f) ∙ comp-assoc f g (id C)) =₂ (comp-unitˡ g ▷ f)
  left-unitor-comp {C = C} f g =
    let I = id C
        A = comp-assoc f g I
        B = comp-assoc (g ∘ f) I I
        C′ = comp-assoc f g (I ∘ I)
        D′ = comp-assoc f (I ∘ g) I
        E = comp-assoc g I I ▷ f
        tail = D′ ∙ E
        r = comp-unitʳ I
        left-normal = (preWhisker-comp-One r g f) ⁻¹ ∙
          (comp₌-cong ((triangle-whiskered (g ∘ f) I) ⁻¹) (id₌ C′) ∙
          ((comp₌-assoc (I ◁ comp-unitˡ (g ∘ f)) B C′) ⁻¹ ∙
          (comp₌-cong (id₌ (I ◁ comp-unitˡ (g ∘ f))) ((pentagon-whiskered-right f g I I) ⁻¹) ∙
          (comp₌-assoc (I ◁ comp-unitˡ (g ∘ f)) (I ◁ A) tail ∙
            comp₌-cong (postWhisker-comp₌ I (comp-unitˡ (g ∘ f)) A) (id₌ tail)))))
        right-normal = comp₌-cong (id₌ A)
          ((preWhisker f ◁ (triangle-whiskered g I) ⁻¹) ∙
            (preWhisker-comp₌ (I ◁ comp-unitˡ g) (comp-assoc g I I) f) ⁻¹) ∙
          (comp₌-assoc A ((I ◁ comp-unitˡ g) ▷ f) E ∙
          (comp₌-cong ((whisker-mixed-One (comp-unitˡ g) f I) ⁻¹) (id₌ E) ∙
            (comp₌-assoc (I ◁ (comp-unitˡ g ▷ f)) D′ E) ⁻¹))
    in postWhisker-id-reflect (cancel-right tail (right-normal ⁻¹ ∙ left-normal))

  identity-unitors : (D : CAT Γ) → comp-unitʳ (id D) =₂ comp-unitˡ (id D)
  identity-unitors D = postWhisker-id-reflect
    (cancel-right (comp-assoc i i i)
      (triangle-whiskered i i ∙
        ((cancel-left r (preWhisker-id-One r)) ⁻¹ ∙ (right-unitor-comp i i) ⁻¹)))
    where
    i : MAP D D
    i = id D
    r : (i ∘ i) =₁ i
    r = comp-unitʳ i

  module _ {A : CAT Γ} where
    open Terms.Equalities A using (_＝_)

    self-naturality : {D : CAT Γ} {t : MAP D D} (ρ : t ＝ id D)
      → (const (comp-unitʳ t) ∙ (t ◁ ρ)) =₁ (const (comp-unitˡ t) ∙ (ρ ▷ t))
    self-naturality {D} {t} ρ = cancel-left ρ
      (comp₌-assoc ρ (const (comp-unitˡ t)) (ρ ▷ t) ∙
        (comp₌-cong (postWhisker-id ρ) (id₌ (ρ ▷ t)) ∙
        (comp₌-cong (comp₌-cong (const-cong (identity-unitors D)) (id₌ (id D ◁ ρ))) (id₌ (ρ ▷ t)) ∙
        ((comp₌-assoc (const (comp-unitʳ (id D))) (id D ◁ ρ) (ρ ▷ t)) ⁻¹ ∙
        (comp₌-cong (id₌ (const (comp-unitʳ (id D)))) (interchange ρ ρ) ∙
        (comp₌-assoc (const (comp-unitʳ (id D))) (ρ ▷ id D) (t ◁ ρ) ∙
        (comp₌-cong ((preWhisker-id ρ) ⁻¹) (id₌ (t ◁ ρ)) ∙
          (comp₌-assoc ρ (const (comp-unitʳ t)) (t ◁ ρ)) ⁻¹)))))))
  self-naturality-One : {D : CAT Γ} {t : MAP D D} (ρ : t =₁ id D)
    → (comp-unitʳ t ∙ (t ◁ ρ)) =₂ (comp-unitˡ t ∙ (ρ ▷ t))
  self-naturality-One {t = t} ρ =
    comp₌-cong (const-One (comp-unitˡ t)) (id₌ (ρ ▷ t)) ∙
      (self-naturality ρ ∙
        (comp₌-cong (const-One (comp-unitʳ t)) (id₌ (t ◁ ρ))) ⁻¹)

```

## Unit routes

A specified identification `ε : j = id` of an endofunctor can be inserted in
the triangle, and unit routes through such an `ε` are natural in the functor
being whiskered. An identification of `θ` with a unitor route determines the
whiskering of `θ` by the identity.

```agda
module _ {Γ : Context} where
  triangle-with-identity : {A B C : CAT Γ}
    (g : MAP B C) (f : MAP A B) (j : MAP B B) (ε : j =₁ (id B))
    → ((comp-unitʳ g ▷ f) ∙ ((g ◁ ε) ▷ f)) =₂
        ((g ◁ (comp-unitˡ f ∙ (ε ▷ f))) ∙ comp-assoc f j g)
  triangle-with-identity g f j ε =
    comp₌-cong ((postWhisker-comp₌ g (comp-unitˡ f) (ε ▷ f)) ⁻¹)
      (id₌ (comp-assoc f j g)) ∙
    ((comp₌-assoc (g ◁ comp-unitˡ f) (g ◁ (ε ▷ f)) (comp-assoc f j g)) ⁻¹ ∙
    (comp₌-cong (id₌ (g ◁ comp-unitˡ f)) (whisker-mixed-One ε f g) ∙
    (comp₌-assoc (g ◁ comp-unitˡ f) (comp-assoc f (id _) g) ((g ◁ ε) ▷ f) ∙
      comp₌-cong (triangle-whiskered f g) (id₌ ((g ◁ ε) ▷ f)))))

  left-unit-route-natural : {X Y : CAT Γ} {u u′ : MAP X Y}
    (F F′ : MAP X Y) (J : MAP Y Y) (ε : J =₁ id Y)
    (z : F =₁ F′) (c : u =₁ (J ∘ F)) (c′ : u′ =₁ (J ∘ F′)) (a : u =₁ u′)
    → SquareCell₌ a (J ◁ z) c c′
    → SquareCell₌ a z (comp-unitˡ F ∙ ((ε ▷ F) ∙ c)) (comp-unitˡ F′ ∙ ((ε ▷ F′) ∙ c′))
  left-unit-route-natural {Y = Y} F F′ J ε z c c′ a natural =
    paste-square₌ {t = a} {m = id Y ◁ z} {b = z}
      (paste-square₌ {t = a} {m = J ◁ z} {b = id Y ◁ z} natural (interchange ε z))
      (postWhisker-id-One z)

  right-unit-route-natural : {X Y : CAT Γ} {u u′ : MAP X Y}
    (F F′ : MAP X Y) (J : MAP X X) (ε : J =₁ id X)
    (z : F =₁ F′) (c : u =₁ (F ∘ J)) (c′ : u′ =₁ (F′ ∘ J)) (a : u =₁ u′)
    → SquareCell₌ a (z ▷ J) c c′
    → SquareCell₌ a z (comp-unitʳ F ∙ ((F ◁ ε) ∙ c)) (comp-unitʳ F′ ∙ ((F′ ◁ ε) ∙ c′))
  right-unit-route-natural {X} F F′ J ε z c c′ a natural =
    paste-square₌ {t = a} {m = z ▷ id X} {b = z}
      (paste-square₌ {t = a} {m = z ▷ J} {b = z ▷ id X} natural ((interchange z ε) ⁻¹))
      (preWhisker-id-One z)

  identity-action-from-square : {X C : CAT Γ} {x y : MAP X C}
    (θ : x =₁ y) (γ : x =₁ (id C ∘ y))
    → θ =₂ (comp-unitˡ y ∙ γ)
    → (id C ◁ θ) =₂ (γ ∙ comp-unitˡ x)
  identity-action-from-square {x = x} {y} θ γ square =
    cancel-left (comp-unitˡ y)
      (comp₌-assoc (comp-unitˡ y) γ (comp-unitˡ x) ∙
      (comp₌-cong square (id₌ (comp-unitˡ x)) ∙ postWhisker-id-One θ))
```
