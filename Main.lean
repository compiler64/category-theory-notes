module

public import Mathlib
public import CommDiag

/-
# The Abstract Nonsense Guide to Monads

Useful resources:
- [Monad chapter in FPIL](https://lean-lang.org/functional_programming_in_lean/Monads/)
- [A great category theory book](https://raw.githubusercontent.com/BartoszMilewski/DaoFP/refs/heads/master/DaoFP.pdf)
- [Curry-Howard-Lambek correspondence](https://ncatlab.org/nlab/show/computational+trilogy#rosetta_stone)
- [Hask is not a category](https://math.andrej.com/2016/08/06/hask-is-not-a-category/)
- [Another monad explanation](https://old.reddit.com/r/math/comments/ap25mr/a_monad_is_a_monoid_in_the_category_of/)

## Lean, the category!

Objects: Types
Morphisms: Total functions

In Lean and Haskell, not all functions are total (defined on all inputs) since they could run forever, so we restrict our category to only total functions. Lean does require the programmer to prove termination for certain function declarations, but this is to prevent proofs of false, not to ensure all functions are total. Lean has a `partial` keyword for declaring functions without needing a termination proof, but this is not infectious like `unsafe` so a regular function can call a `partial` function and thus no longer be total.

Let's check that Lean is actually a category.

Tip: You can Ctrl-click on anything to see its definition.
-/

-- Composition of morphisms is just function composition, denoted `∘`
#check Function.comp

-- Identity morphism
#check Id
-- `Id` works for all types, whereas `id` is different and works for all terms.

-- Composition of morphisms is associative
#check Function.comp_assoc

-- Equality of morphisms
#check funext
-- If two functions return the same values for every input, then they're equal. This ignores time complexity though so in practice the two functions might not be interchangeable.


/-
## Bicartesian closed categories

Lean is a bicartesian closed category, which means it has an initial object, terminal object, sums, products, exponentials, sums distribute over products, and products distribute over exponentials.
-/

-- Initial object
#check False
-- Morphism from initial object
#check False.elim
-- The logic interpretation of this is that we can prove anything from `False`
-- Isomorphic to initial object but in higher universes, because Lean universes are not cumulative
#check PEmpty
#check PEmpty.elim

-- Terminal object
#check True
-- Morphism to terminal object
#check fun _ ↦ True.intro
-- Also isomorphic
#check PUnit
#check fun _ ↦ PUnit.unit

-- Sums (coproducts), which correspond to `∨` in logic
#check Sum
-- Morphism from first type
#check Sum.inl
-- Morphism from second type
#check Sum.inr
#html sumDiag

-- Products, which correspond to `∧` in logic
#check Prod
-- Morphism to first type
#check Prod.fst
-- Morphism to second type
#check Prod.snd
#html prodDiag

-- Exponentials
#check (· → ·)
-- Lean is self-enriched because we can view any hom-set between `α` and `β` as the object `α → β`.

/-- Sums distribute over products -/
def sum_distrib_prod : α × (β ⊕ γ) ≃ α × β ⊕ α × γ where
  toFun
    | (a, .inl b) => .inl (a, b)
    | (a, .inr b) => .inr (a, b)
  invFun
    | .inl (a, b) => (a, .inl b)
    | .inr (a, b) => (a, .inr b)
  left_inv := by grind
  right_inv := by grind

/-- Products distribute over exponentials -/
def prod_distrib_exp {α : Type u} : (α → (β × γ)) ≃ (α → β) × (α → γ) where
  toFun f := (Prod.fst ∘ f, Prod.snd ∘ f)
  invFun f := fun x ↦ (f.1 x, f.2 x)
  left_inv := by grind


/-
## Universes

You might have noticed the `Type u` in some of those previous examples. In Lean, `2 : ℕ : Type : Type 1 : Type 2 : Type 3`, and so on, where each level of the hierarchy is called a universe. However, if we had `Type : Type`, then that would cause Girard's paradox (a variant of Russell's paradox).

We can't actually assign `Type` a different type in Lean, not even with an axiom, but instead we can assume that there's an injective function from `Type 1` to `Type` and derive a contradiction. Basically, we're trying to fit `Type` (which lives in `Type 1`) into the universe `Type`. The code below proves something slightly more general, namely that if there's an injective function from `Type (u + 1)` or higher to `Type u`, then we can get a contradiction.
-/

def girard (f : Type (max (u + 1) v) ↪ Type u) : False := by
  -- Let `g` be the inverse of `f`, where `g x` is any arbitrary value if `f` doesn't map anything to `x`
  let g := f.toFun.invFun
  -- `g` is surjective because `f` is injective
  have hg : g.Surjective := by
    intro a
    use f.toFun a
    simp [g, Function.invFun]
  -- Now we can use `g` to construct a sigma type (dependent pair)
  let T := Sigma g
  -- Some `U : Type u` must map to `Set T`
  obtain ⟨U, hU⟩ := hg (Set T)
  -- This function is like mapping a power set of `T` to `T` itself
  let k (s : Set T) : T :=
    -- If the first element of the dependent pair is `U`, then the second element must have type `h U`, which conveniently is `Set T`
    -- So, we can use `s` for the second element
    ⟨U, cast hU.symm s⟩
  -- `k` is injective because each pair has a different `s`
  have hk : k.Injective := by
    intro s t _
    have : cast hU (k s).2 = cast hU (k t).2 := by congr
    simpa [k]
  -- Now we have an injective `k` from `Set T → T` which violates `Function.cantor_injective k` in mathlib
  -- We can also manually finish the proof using a diagonalization argument
  -- This is like the set of sets that don't contain themselves
  let Q := { b : T | ∃ P, k P = b ∧ b ∉ P }
  -- If `k Q ∈ Q`, then there exists `P` with `k P = k Q` and `k Q ∉ P`, but `k` is injective so `P = Q` and `k Q ∉ Q`
  have down (h : k Q ∈ Q) : k Q ∉ Q := by
    obtain ⟨P, hP⟩ := h
    exact (hk hP.1) ▸ hP.2
  -- If `k Q ∉ Q` then choose `P := Q` so `k Q ∈ Q` holds by definition
  have up (h : k Q ∉ Q) : k Q ∈ Q :=
    ⟨Q, rfl, h⟩
  -- We can either use the law of excluded middle, or do something trippy
  let f := fun h ↦ down h h
  exact f (up f)

/-
Universes in Lean are weird. For instance, for two universe levels `u` and `v`, `max u v` is only guaranteed to be at least as large as `u` and `v`, but could be larger! https://leanprover-community.github.io/mathlib4_docs/Mathlib/Logic/UnivLE.html#UnivLE

However, we do know that `UnivLE` is a total preorder: https://leanprover-community.github.io/mathlib4_docs/Mathlib/SetTheory/Cardinal/UnivLE.html#univLE_total
-/


/-
## Functors

Recall that a functor is a function from one category to another. An endofunctor is a functor from a category to itself. The type class `[LawfulFunctor F]` corresponds to endofunctors in Lean.

`F` maps objects (it's a type constructor)
`Functor.map (f := F)` (denoted `<$>`) maps morphisms

Note the the `<$>`'s type signature, `(α → β) → f α → f β` is the same thing as `(α → β) → (f α → f β)` because of partial application.
-/

-- Type class containing `map`
#check Functor
-- This diagram commutes by definition
#html functorDiag

-- Type class containing functor laws (I'm not sure why it's split like this in Lean)
#check LawfulFunctor
-- `F` preserves composition, so the blue and red arrows on the right should be equal
#html functorCompDiag

-- Examples of functors
#synth Functor List
#synth Functor Tree
#synth Functor Option
#synth Functor (Except String)

-- Using functors
#eval (· * 2) <$> [1, 2, 3]
#eval (· * 2) <$> some 2
#eval (· * 2) <$> none

/-- `List` satisfies the functor laws, yay -/
instance : LawfulFunctor List where
  map_const := by solve_by_elim
  id_map := by simp
  comp_map := by simp

/-- Hom-functor in self-enriched category -/
instance (α : Type u) : Functor (α → ·) where
  map f g := f ∘ g

attribute [simp] Functor.map

instance (α : Type u) : LawfulFunctor (α → ·) where
  map_const := by solve_by_elim
  id_map := by simp
  comp_map := by simp [Function.comp_assoc]

-- Exercise: Come up with another example of a functor in Lean, and prove it satisfies the functor laws


/--
## Contravariant functors

If `(α → ·)` is a functor, then what about `(· → α)`? If you try defining `<$>` for `(· → α)`, you'll find out that it doesn't work, because `(· → α)` is actually a contravariant functor.

Normal functors, sometimes called covariant functors, map Lean to Lean. Contravariant functors map Colean to Lean. They're occasionally called "cofunctors", but that's a misnomer because functors are self-dual.
-/

public class Contrafunctor (F : Type u → Type v) where
  contramap : (β → α) → F α → F β
  -- `contramap` preserves `id`
  id_contramap (x : F α) : contramap id x = x
  -- `contramap` preserves function composition
  comp_contramap (g : β → α) (h : γ → β) (x : F α) : contramap (g ∘ h) x = contramap h (contramap g x)

/-- This is not standard notation but just something I made up -/
infixr:100 " <¥> " => Contrafunctor.contramap

attribute [simp] Contrafunctor.contramap

-- Intuitively, `<$>` turns a "producer of α" into a "producer of β" while `<¥>` turns a "consumer of α" into a "consumer of β".

/-- Some useful lemmas -/
lemma Contrafunctor.id_contramap' [Contrafunctor f] : Contrafunctor.contramap (F := f) (@id α) = id := by
  ext x
  exact Contrafunctor.id_contramap x

lemma Contrafunctor.contramap_comp_contramap [Contrafunctor F] (g : α → β) (h : β → γ) :
    ((g <¥> ·) ∘ (h <¥> ·) : F γ → F α) = Contrafunctor.contramap (h ∘ g) :=
  funext fun _ ↦ (comp_contramap _ _ _).symm

/-- The other kind of hom-functor is contravariant -/
instance (α : Type u) : Contrafunctor (· → α) where
  contramap f g := g ∘ f
  id_contramap := by simp
  comp_contramap := by simp [Function.comp_assoc]

/-
Contravariant functors are rarely used in Lean, and most examples of them are function object things like the hom-functor.

A function type is covariant if the free parameter is in an even depth and contravariant if at an odd depth.

- `(α → ·)` is covariant
- `(· → α)` is contravariant
- `((· → α) → β)` is covariant
- `(((· → α) → β) → γ)` is contravariant
- And so on
-/


/-
## Composition of functors

Since functors map Lean to Lean, we can compose two functors to get a new functor. For the object map, we simply compose the object maps of the two functors. To map a morphism `f`, we use the outer functor's `<$>` to map `f` over the inner functor.
-/

/-- Composition of two functors of same variance is a functor -/
instance [Functor F] [Functor G] : Functor (F ∘ G) where
  map f x := Functor.map (f := F) (f <$> ·) x

instance [Functor F] [LawfulFunctor F] [Functor G] [LawfulFunctor G] : LawfulFunctor (F ∘ G) where
  map_const := by solve_by_elim
  id_map := by simp
  comp_map f g x := by simp; rfl

instance [Contrafunctor F] [Contrafunctor G] : Functor (F ∘ G) where
  map f x := Contrafunctor.contramap (F := F) (Contrafunctor.contramap f) x

instance [Contrafunctor F] [Contrafunctor G] : LawfulFunctor (F ∘ G) where
  map_const := by solve_by_elim
  id_map := by simp [Contrafunctor.id_contramap']
  comp_map f g x := by simp [← Contrafunctor.contramap_comp_contramap]

-- If functors are sort of like "containers" for data, then functor composition is like "nesting" two "containers"
#synth LawfulFunctor (List ∘ Option)

/-- Composition of functors of opposite variance is a contravariant functor -/
instance [Functor F] [LawfulFunctor F] [Contrafunctor G] : Contrafunctor (F ∘ G) where
  contramap f x := Functor.map (f := F) (f <¥> ·) x
  id_contramap := by simp [Contrafunctor.id_contramap]
  comp_contramap := by simp [Contrafunctor.comp_contramap]

instance [Contrafunctor F] [Functor G] [LawfulFunctor G] : Contrafunctor (F ∘ G) where
  contramap f x := Contrafunctor.contramap (F := F) (f <$> ·) x
  id_contramap := by
    simp only [Function.comp_apply, id_map]
    exact Contrafunctor.id_contramap
  comp_contramap f g x := by simp only [← Functor.map_comp_map g f, Contrafunctor.comp_contramap]


/-
## Other kinds of functors (optional)

We can also define functors for products of categories.
-/

-- Bifunctors map Lean × Lean to Lean
#check Bifunctor
#check LawfulBifunctor

-- `Sum` and `Prod` are bifunctors
#synth LawfulBifunctor Sum
#synth LawfulBifunctor Prod

-- Multivariate functors
#check MvFunctor
#check LawfulMvFunctor

-- Profunctors map Colean × Lean to Lean and are useful for lenses and [optics](https://marcosh.github.io/post/2025/10/07/the-mondrian-introduction-to-functional-optics.html)
class Profunctor (P : Type u → Type v → Type*) where
  dimap : (σ → α) → (β → τ) → P α β → P σ τ
  -- `dimap` preserves `id`
  id_dimap (x : P α β) : dimap id id x = x
  -- `dimap` preserves function composition
  dimap_dimap (f : α₁ → α₀) (f' : α₂ → α₁) (g : β₀ → β₁) (g' : β₁ → β₂) (x : P α₀ β₀) :
    dimap f' g' (dimap f g x) = dimap (f ∘ f') (g' ∘ g) x

/-- Exponentials are profunctors -/
instance : Profunctor (· → ·) where
  dimap f g h := g ∘ h ∘ f
  id_dimap := by simp
  dimap_dimap := by simp [Function.comp_assoc]

/-- We can compose two profunctors -/
inductive Procompose P Q [Profunctor P] [Profunctor Q] a b
  | mk : Q a x → P x b → Procompose P Q a b

instance [Profunctor P] [Profunctor Q] : Profunctor (Procompose P Q) where
  dimap l r
    | ⟨qax, pxb⟩ => ⟨Profunctor.dimap l id qax, Profunctor.dimap id r pxb⟩
  id_dimap := by simp [Profunctor.id_dimap]
  dimap_dimap := by simp [Profunctor.dimap_dimap]

-- TODO: Is the wedge condition automatically satisfied in Lean?
abbrev End P [Profunctor P] := ∀ x, P x x

abbrev Coend P [Profunctor P] := Σ x, P x x

abbrev ProPair Q P [Profunctor P] [Profunctor Q] a b x y :=
  Q a y × P x b

instance [Profunctor P] [Profunctor Q] : Profunctor (ProPair Q P a b) where
  dimap l r
    | ⟨qax, pxb⟩ => ⟨Profunctor.dimap id r qax, Profunctor.dimap l id pxb⟩
  id_dimap := by simp [Profunctor.id_dimap]
  dimap_dimap := by simp [Profunctor.dimap_dimap]

-- We can use coends to compose profunctors
abbrev CoendCompose P Q [Profunctor P] [Profunctor Q] a b :=
  Coend (ProPair Q P a b)

instance [Profunctor P] [Profunctor Q] : Profunctor (CoendCompose P Q) where
  dimap l r
    | ⟨x, (qay, pxb)⟩ => ⟨x, (Profunctor.dimap l id qay, Profunctor.dimap id r pxb)⟩
  id_dimap := by simp [Profunctor.id_dimap]
  dimap_dimap := by simp [Profunctor.dimap_dimap]


/-
## Natural transformations

A natural transformation is a function between two functors that satisfies a naturality condition. Intuitively, a natural transformation "moves" data from one "container" to another.
-/

/-- Type of a natural transformation (without the naturality condition) -/
abbrev NaturalType.{u} (F : Type u → Type v) (G : Type u → Type w) :=
  {α : Type u} → F α → G α

/--
The naturality condition, which intuitively states that "moving" data is simply just a move and does not meaningfully change it

TODO: Use a subtype?
-/
class Natural F [Functor F] [LawfulFunctor F] G [Functor G] [LawfulFunctor G] (η : NaturalType F G) where
  naturality (f : α → β) (x : F α) : f <$> (η x) = η (f <$> x)

#html natTransDiag

-- In Haskell, naturality is automatically guarenteed because all polymorphic functions in Haskell are parametrically polymorphic functions, which intuitively means that the function does "the same thing" for every type. This is classic example of "theorems for free". However, in Lean we're not so lucky, because a polymorphic function in Lean can do something different depending on its input type.

-- TODO: Proof that parametrically polymorphic and naturality are the same thing

/-- A practical example of a natural transformation -/
instance : Natural List Option List.head? :=
  ⟨by simp⟩

/-- Another example -/
abbrev OptionToList : Option α → List α
  | some a => [a]
  | none => []

instance : Natural Option List OptionToList :=
  ⟨by simp; grind⟩

/-- A natural transformation from the hom-functor to `Option` -/
noncomputable abbrev FunToOption (f : α → β) : Option β := by
  by_cases h : Nonempty α
  · exact some <| f <| Classical.choice h
  · exact none

instance : Natural (α → ·) Option FunToOption :=
  ⟨by by_cases h : Nonempty α <;> simp [h]⟩

/-- Naturality for functions between contravariant functors -/
class Contranatural F [Contrafunctor F] G [Contrafunctor G] (η : NaturalType F G) where
  naturality (f : β → α) (x : F α) : f <¥> (η x) = η (f <¥> x)

-- Vertical composition of natural transformations, which intuitively is like doing two data moves
instance [Functor F] [LawfulFunctor F] [Functor G] [LawfulFunctor G] [Functor H] [LawfulFunctor H] [M : Natural F G η] [N : Natural G H μ] :
    Natural F H (fun {α : Type u} ↦ @μ α ∘ @η α) :=
  ⟨by simp [N.naturality, M.naturality]⟩

namespace HorizontalComp

variable (η : NaturalType F F') (μ : NaturalType G G') [Functor F] [LawfulFunctor F] [Functor F'] [LawfulFunctor F'] [Functor G] [LawfulFunctor G] [Functor G'] [LawfulFunctor G']

-- Horizontal composition of natural transformations, which intuitively is like repackaging data in nested "containers"
instance [M : Natural F F' η] [N : Natural G G' μ] : Natural (G ∘ F) (G' ∘ F') (μ ∘ (η <$> ·)) :=
  ⟨by simp [N.naturality, M.naturality]⟩

/-- Alternatively we do `μ` first and then the map second -/
instance [M : Natural F F' η] [N : Natural G G' μ] : Natural (G ∘ F) (G' ∘ F') ((Functor.map (f := G') η ·) ∘ μ) :=
  ⟨by simp [N.naturality, M.naturality]⟩

/-- The two orderings are equivalent, and this lemma only requires the outer transformation to be natural -/
lemma horizontal_comp_equiv [N : Natural G G' μ] : (μ ∘ (η <$> ·)) x = ((Functor.map (f := G') η ·) ∘ μ) x := by
  simp [N.naturality]

end HorizontalComp

/-
## The Yoneda lemma (optional)

"In his Algebraic Geometry class a few years back, Ravi Vakil explained Yoneda's lemma like this: You work at a particle accelerator. You want to understand some particle. All you can do are throw other particles at it and see what happens. If you understand how your mystery particle responds to all possible test particles at all possible test energies, then you know everything there is to know about your mystery particle." (from https://mathoverflow.net/questions/3184/philosophical-meaning-of-the-yoneda-lemma)

To motivate the Yoneda lemma in Lean, let's say we're trying to come up with a natural transformation from the hom-functor `(α → ·)` to an arbitrary functor `F`. This is a function from `α → β` to `F β`.
-/

def FunToFunctor [Functor F] [LawfulFunctor F] (g : α → β) : F β :=
  sorry

/--
Yoneda reverse map

If we had some value `x : F α`, then we could get a value of type `F β` using `g <$> x`
-/
def yoneda' [Functor F] [LawfulFunctor F] (x : F α) : NaturalType (α → ·) F :=
  (· <$> x)

/-- The reverse map always produces a natural transformation -/
instance [Functor F] [LawfulFunctor F] : Natural (α → ·) F (yoneda' y) :=
  ⟨fun f x ↦ by simp [yoneda']; rfl⟩

/--
Yoneda forward map (`η` is not necessarily natural)

If we have some natural transformation `η`, was it produced by some `x : F α`? We can specialize `η` to type `α` so that it has type signature `(α → α) → F α`. Then by feeding it `id`, we get some value of type `F α`!
-/
def yoneda (η : NaturalType (α → ·) F) [Functor F] [LawfulFunctor F] : F α :=
  η id

/--
Mapping and unmapping a natural transformation returns itself!

If we start with some `η`, then extracting out that `x : F α` and using it to construct a natural transformation gives us `η` again. Note that this doesn't work for an arbitrary function between the hom-functor and `F` because we use the naturality condition.
-/
theorem yoneda_lemma (η : NaturalType (α → ·) F) [Functor F] [LawfulFunctor F] [N : Natural (α → ·) F η] : yoneda' (yoneda η) x = η x := by
  simp [yoneda, yoneda', N.naturality]

/-- Mapping and unmapping an element `f α` returns itself -/
theorem yoneda_lemma' (x : F α) [Functor F] [LawfulFunctor F] : yoneda (yoneda' x) = x := by
  simp [yoneda, yoneda']

/-
Intuitively, using some `x : F α`, we can determine what `η` does when specialized to type `α`, and the behavior of `η` on other types is fully determined because it's parametrically polymorphic.

Another nice property of the Yoneda isomorphism is that it's natural in both `α` and `F` when we view both sides as functors.
-/

/-- Subtype for natural transformations -/
abbrev NaturalSub F [Functor F] [LawfulFunctor F] G [Functor G] [LawfulFunctor G] :=
  { η : NaturalType F G // {α β : Type _} → (f : α → β) → (x : F α) → f <$> (η x) = η (f <$> x) }

/--
The set of natural transformations between the hom-functor and `F` is a functor in `α`

Exercise: Expand the function type for `(fun α ↦ NaturalSub (α → ·) F)` and show that it is covariant, not contravariant.
-/
instance [Functor F] [LawfulFunctor F] : Functor (fun α ↦ NaturalSub (α → ·) F) where
  map f g :=
    ⟨fun h ↦ g.val (h ∘ f), fun h x ↦ g.prop h (x ∘ f)⟩

instance [Functor F] [LawfulFunctor F] : LawfulFunctor (fun α ↦ NaturalSub (α → ·) F) where
  map_const := by solve_by_elim
  id_map := by simp
  comp_map g h := by simp [Function.comp_assoc]

/-- The Yoneda isomorphism is natural in `α` -/
def yoneda_natural_α [Functor F] [LawfulFunctor F] : NaturalSub (fun α ↦ NaturalSub (α → ·) F) F :=
  ⟨(yoneda ·.val), fun f η ↦ by simp [yoneda, η.prop]⟩

/-- Functor from the category of Lean endofunctors to Lean -/
class EndofunctorFunctor (F : (Type u → Type v) → Type w) where
  map : {α β : Type u → Type v} → ({ε : Type u} → α ε → β ε) → F α → F β
  id_map (x : F α) : map id x = x
  comp_map {α β γ : Type u → Type v} (g : {ε : Type u} → α ε → β ε) (h : {ε : Type u} → β ε → γ ε) (x : F α) : map (h ∘ g) x = map h (map g x)

instance : EndofunctorFunctor (fun (F : Type u → Type v) ↦ F α) where
  map f x := f x
  id_map := by simp
  comp_map := by simp

/-- The set of natural transformations between the hom-functor and `F` is a functor in `F` from the category of Lean endofunctors to Lean -/
instance (α : Type u) : EndofunctorFunctor (fun (F : Type u → Type v) ↦ NaturalType (α → ·) F) where
  map f g := f ∘ g
  id_map := by simp
  comp_map g h := by simp [Function.comp_assoc]

abbrev NaturalSub' (F : (Type u → Type v) → Type w) [EndofunctorFunctor F] (G : (Type u → Type v) → Type w) [EndofunctorFunctor G] :=
  { η : {α : Type u → Type v} → F α → G α // {α β : Type u → Type v} → (f : {ε : Type u} → α ε → β ε) → (x : F α) → EndofunctorFunctor.map f (η x) = η (EndofunctorFunctor.map f x) }

/--
The Yoneda isomorphism is natural in `F`

I didn't use `yoneda` since that function requires the input to be a functor, but the implementation here is the same.
-/
def yoneda_natural_F : NaturalSub' (fun F ↦ NaturalType (α → ·) F) (· α) :=
  ⟨(· id), by simp [EndofunctorFunctor.map]⟩

-- Surprisingly, the Yoneda lemma has a few practical applications, such as continuation-passing style. `yoneda (F := Id)` has the type signature `{β} → (α → β) → β`, which is a function that takes a callback. The Yoneda lemma implies that any type `α` can instead be replaced by that function instead.
#simp [NaturalType] fun (α : Type*) ↦ NaturalType (α → ·) Id

-- There's a very similar theorem for contravariant functors.

/-- Coyoneda forward map -/
def coyoneda (η : NaturalType (· → α) F) [Contrafunctor F] : F α :=
  η id

/-- Coyoneda reverse map -/
def coyoneda' [Contrafunctor F] (x : F α) : NaturalType (· → α) F :=
  (· <¥> x)

/-- Reverse map always produces a natural transformation -/
instance [Contrafunctor F] : Contranatural (· → α) F (coyoneda' y) :=
  ⟨fun f x ↦ by simp [coyoneda', Contrafunctor.comp_contramap]⟩

/-- Same but for Coyoneda -/
theorem coyoneda_lemma (η : NaturalType (· → α) F) [Contrafunctor F] [N : Contranatural (· → α) F η] : coyoneda' (coyoneda η) x = η x := by
  simp [coyoneda, coyoneda', N.naturality]

/-- Same but for Coyoneda -/
theorem coyoneda_lemma' (x : F α) [Contrafunctor F] : coyoneda (coyoneda' x) = x := by
  simp [coyoneda, coyoneda', Contrafunctor.id_contramap]

-- Exercise: Prove that the Coyoneda lemma is natural in `F` and `α`.

-- TODO: We can also formulate the Yoneda lemma using profunctors, ends, and coends
def Yo F [Functor F] [LawfulFunctor F] (α x y : Type u) := (α → x) → F y

instance [Functor F] [LawfulFunctor F] : Profunctor (Yo F α) where
  dimap g h i j := h <$> (i (g ∘ j))
  id_dimap := by simp
  dimap_dimap f f' g g' x := by simp; rfl

def yonedaEnd [Functor F] [LawfulFunctor F] (g : End (Yo F α)) : F α :=
  g α id

def yonedaEnd' [Functor F] [LawfulFunctor F] (x : F α) : End (Yo F α) :=
  fun _ f ↦ f <$> x

def Coyo F [Functor F] [LawfulFunctor F] (α x y : Type u) := (x → α) × F y

instance [Functor F] [LawfulFunctor F] : Profunctor (Coyo F α) where
  dimap g h i := (i.1 ∘ g, h <$> i.2)
  id_dimap := by simp
  dimap_dimap f f' g g' x := by simp; rfl

def coyonedaCoend [Functor F] [LawfulFunctor F] (g : Coend (Coyo F α)) : F α :=
  g.2.1 <$> g.2.2

def coyonedaCoend' [Functor F] [LawfulFunctor F] (x : F α) : Coend (Coyo F α) :=
  ⟨α, (id, x)⟩


/-
## Applicative functors and monads

Motivation: functors are great, but how can we `<$>` a multi-argument function? We need a functor but with an additional feature.
-/

#simp (· * ·) <$> (some 3)

#eval (· * ·) <$> (some 3) <*> (some 4)

-- Applicative functors
#check Applicative
#check LawfulApplicative

/-- Composition of two applicatives is an applicative -/
instance [Applicative F] [Applicative G] : Applicative (F ∘ G) where
  pure x := pure (f := F) (pure x)
  seq f x := Seq.seq (f := F) ((· <*> ·) <$> f) x

attribute [simp] Pure.pure Seq.seq

instance [Applicative F] [LawfulApplicative F] [Applicative G] [LawfulApplicative G] : LawfulApplicative (F ∘ G) where
  seqLeft_eq := by simp [SeqLeft.seqLeft]
  seqRight_eq := by simp [SeqRight.seqRight]
  pure_seq := by simp [pure_seq]
  map_pure := by simp
  seq_pure := by simp
  seq_assoc x f g := by
    simp [seq_assoc, seq_map_assoc, map_seq]
    congr
    ext
    simp [seq_assoc]

-- TODO: Lax monoidal functors

/-
Lean is a purely functional programming language, so functions must only depend on their arguments and have no access to the outside world. For instance, a function `f : ℕ → ℕ` isn't allowed to have side effects like printing out "Hello, world!" or throwing exceptions.

Then how can we do IO or have mutable state in Lean? The solution is to encode a function's side effects into the return type of the function. For instance, if `f` can throw exceptions, its type signature instead becomes `ℕ → Except String ℕ`.
-/

def one_over (x : ℚ) : Except String ℚ :=
  if x = 0 then
    .error "Division by 0 is undefined"
  else
    .ok <| 1 / x

#eval one_over 2
-- Oops! Can't feed an `Except` into `one_over`.
#eval one_over (one_over 2)

/-
- Functors let us apply `α → β` to `F α`
- Applicatives let us apply `F (a → β)` to `F α`
- But what about applying an effectful function `α → F β` to `F α`, or composing two effectful functions `α → F β` and `β → F γ`?

Solution: `>>=`, which enables us to "shove" a `F α` into a function `α → F β`.
-/

-- Monads, AKA "warm fuzzy things"
#check Monad
-- The monad laws
#check LawfulMonad

#eval one_over 2 >>= one_over

/-
Kleisli category: A monad `m` creates a category where the objects are still types but the morphisms are `α → β` for every `α → F β` in Lean. Then composition of effectful functions becomes composition of morphisms. This construction also motivates the monad laws.

In fact, using `>>=` and `pure` we can implement `<$>` and `<*>` so every monad is also a functor and applicative.

Exercise: Find an example of a functor which is not applicative and an applicative which is not a monad.
-/

-- Some examples
#synth Monad List
#synth Monad Option
#synth Monad IO
#synth Monad (StateM ℕ)
#synth Monad (Writer ℕ)
#synth Monad (ST ℕ)
#synth Monad (Except String)
#synth Monad (Sum ℕ)

-- Exercise: Come up with another example of a monad in Lean

instance : LawfulMonad Option :=
  LawfulMonad.mk' Option
    (id_map := by simp)
    (pure_bind := by simp [Option.bind])
    (bind_assoc := by simp; grind)
    (bind_pure_comp := by simp [Option.map]; grind)

#synth LawfulMonad List

/--
This function looks ugly, but we can simplify it with `do` notation, which is syntactic sugar that lets us unwrap monadic values and automatically inserts `>>=` when we use the unwrapped values

https://slightknack.dev/blog/do-notation/
-/
def option_div (x_wrapped : Option ℕ) (y_wrapped : Option ℕ) : Option ℚ :=
  y_wrapped >>= fun y ↦
    if y = 0 then
      none
    else
      x_wrapped >>= fun x ↦ some <| x / y

#eval option_div (some 3) (some 0)

/-- Much better now! -/
def option_div' (x_wrapped : Option ℕ) (y_wrapped : Option ℕ) : Option ℚ := do
  let x ← x_wrapped
  let y ← y_wrapped
  if y = 0 then none else some <| x / y

/--
Even the identity monad is powerful! We can write code with locally mutable variables, for loops, breaks, and early returns and it gets automatically desugared into nice, purely functional code.

https://dl.acm.org/doi/10.1145/3547640
-/
def Array.insSort [LinearOrder α] (A : Array α) := Id.run do
  let N := A.size
  let mut A := A.toVector
  for hi : i in [:N] do
    for hj : j in [:i] do
      have := Membership.get_elem_helper hi rfl
      if A[i - j] < A[i - j - 1] then
        A := A.swap (i - j - 1) (i - j)
      else
        break
  return A.toArray

/-- We can use `do` notation with any monad, such as the `List` monad -/
def UpToN (xs : List ℕ) : List ℕ := do
  let x ← xs
  let y ← List.range x
  return y

#eval UpToN [1, 2, 3]

/-
Sadly, in general monads do not compose 😿, but in some cases we can use monad transformers to compose them.

https://carlo-hamalainen.net/2014/01/02/applicatives-compose-monads-do-not/

TODO: More about monad transformers
-/

-- Equivalent definition of monads using `>=>` (pronounced "fish")
#check Bind.kleisliRight
-- Equivalent definition of monads using `join`
#check joinM
-- Exercise: Implement `>>=` using `>=>`


/-
## Monoidal categories

We're now ready to explain the meme quote "A monad is just a monoid in the category of endofunctors".

So what's the category of endofunctors in Lean?

Objects: `LawfulFunctor`s
Morphisms: Natural transformations

We can compose morphisms using vertical composition, which we proved earlier produces another natural transformation.
-/

/-- Every object has an identity morphism -/
instance [Functor F] [LawfulFunctor F] : Natural F F id :=
  ⟨by simp⟩

/-- Vertical composition is associative -/
lemma nat_trans_comp_assoc (η : NaturalType f g) (μ : NaturalType g h) (ν : NaturalType h i) [Functor f] [LawfulFunctor f] [Functor g] [LawfulFunctor g] [Functor h] [LawfulFunctor h] [Functor i] [LawfulFunctor i] :
    ((ν ∘ μ) ∘ η) x = (ν ∘ μ ∘ η) x := by
  simp only [Function.comp_assoc]

-- Note that monoids from set theory are not the same thing as monoids in category theory!
#check Monoid

/-
A monoidal category is a category C equipped with a bifunctor ⨂ (called the tensor product) from C × C to C and an identity object I such that ⨂ is associative up to isomorphism, I is an identity with respect to ⨂ up to isomorphism, and some scary diagrams called the coherence conditions commute.

For the category of Lean endofunctors, let ⨂ be functor composition and I be the identity functor `Id`.
-/

/-- ⨂ is obviously associative -/
lemma functor_comp_assoc [Functor F] [LawfulFunctor F] [Functor G] [LawfulFunctor G] [Functor H] [LawfulFunctor H] : (F ∘ G) ∘ H = F ∘ G ∘ H := by
  apply Function.comp_assoc

/-- `Id` is an identity for ⨂ -/
lemma functor_left_id [Functor F] [LawfulFunctor F] : id ∘ F = F := by
  simp

/-- `Id` is an identity for ⨂ -/
lemma functor_right_id [Functor F] [LawfulFunctor F] : F ∘ id = F := by
  simp

-- In the category of Lean endofunctors, these properties are satisfied with equalities, not just up to isomorphism, so the coherence conditions (insert scary pentagon diagram here) are automatically satisfied, phew.

/-
A monoidal object is an object M in (C, ⨂, I) with an arrow μ from M ⨂ M to M and η from I to M such that μ is associative and η is an identity with respect to μ.

A monoidal object in the category of Lean endofunctors is a functor with natural transformations `join` (corresponding to μ) and `pure` (η) with the following properties:
-/

class EndofunctorMonoid M extends Functor M, LawfulFunctor M where
  -- Has type signature `M (M α) → α`
  join : NaturalType (M ∘ M) M
  -- Has type signature `α → M α`
  pure : NaturalType Id M
  /-
  Adding another `M` layer with `pure` and then removing it with `join` does nothing:
     M α
    /   \
  M (M α)
  \   /
   M α
  -/
  join_pure (x : M α) : (join ∘ pure) x = x
  /-
  Adding another `M` layer on the inside with `pure` and then removing the outer layer with `join` does nothing:
    M α
     / \
  M (M α)
   \   /
    M α
  (When using <$>, Lean synthesizes the wrong type class instance here for some weird reason)
  -/
  join_map_pure (x : M α) : (join ∘ (map pure ·)) x = x
  /-
  Removing the inner `M` layer and then the outer layer is the same as removing the outer layer and then the inner layer:
  M (M (M α))  M (M (M α))
     \     /   \ /
    M (M α)  =  M (M α)
     \   /       \   /
      M α         M α
  -/
  join_join (x : M (M (M α))) : (join ∘ (map join ·)) x = (join ∘ join) x

/-- We can implement `>>=` using a monoid's `join` function -/
@[simp]
def bindFromJoin [EndofunctorMonoid M] (join : NaturalType (M ∘ M) M) (x : M α) (f : α → M β) :=
  join (Functor.map (f := M) f x)

/-- Any monoid corresponds to a monad -/
instance [EndofunctorMonoid M] : Monad M where
  pure := EndofunctorMonoid.pure
  bind := bindFromJoin EndofunctorMonoid.join

attribute [simp] Bind.bind

/-- A monoid in the category of endofunctors is a monad! -/
instance [EndofunctorMonoid M] [J : Natural (M ∘ M) M EndofunctorMonoid.join] [P : Natural Id M EndofunctorMonoid.pure] : LawfulMonad M :=
  LawfulMonad.mk' M id_map
    (pure_bind := fun x f ↦ by
      simpa [P.naturality, Functor.map] using EndofunctorMonoid.join_pure (f x))
    (bind_assoc := fun x f g ↦ by
      have := EndofunctorMonoid.join_join (x := (fun a ↦ Functor.map (f := M) g (f a)) <$> x)
      simp at this
      simp [J.naturality, ← this])
    (map_const := by simp [map_const])
    (bind_pure_comp := fun f x ↦ by
      simpa [← Functor.map_map] using EndofunctorMonoid.join_map_pure (f <$> x))

/-- Similarly, we can implement `join` using `>>=` -/
@[simp]
def joinFromBind [Monad M] (bind : {α β : Type u} → M α → (α → M β) → M β) (x : M (M α)) :=
  bind x id

/-- A monad is a monoid in the category of endofunctors! -/
instance [Monad M] [LawfulMonad M] : EndofunctorMonoid M where
  pure := pure
  join := joinFromBind bind
  join_pure x := by
    simp
    exact pure_bind x id
  join_map_pure x := by
    simp
    exact bind_pure x
  join_join := by simp

instance [Monad M] [LawfulMonad M] : Natural (M ∘ M) M EndofunctorMonoid.join :=
  ⟨by simp [EndofunctorMonoid.join]⟩

instance [Monad M] [LawfulMonad M] : Natural Id M EndofunctorMonoid.pure :=
  ⟨by
    simp
    exact map_pure⟩

/-- `bindFromJoin` and `joinFromBind` form a bijection, so thus monads are the same thing as monoids in the category of endofunctors -/
theorem bind_join_equiv [Monad M] [LawfulMonad M] : (bindFromJoin (M := M) (joinFromBind bind)) x f = bind x f := by
  simp

theorem bind_join_equiv' [E : EndofunctorMonoid M] : joinFromBind (bindFromJoin E.join) x = E.join x := by
  simp

/-
Wait, not so fast! There's a subtle problem: universes.

Consider the definition of functors in Lean, which functions from `Type u → Type v`. However, the category theory definition of an endofunctor requires mapping all of the category Lean, so we need our functor to be universe polymorphic so that it's defined on inputs in any universe. For instance, `List` works for an input type in any universe `u` and returns a type that's also in universe `u`. Using this restricted definition of a functor, the rest of our proof goes through, except only universe polymorphic monads end up corresponding to monoids in the category of endofunctors.

We can also view each universe `u` of Lean as its own category Lean.{u} and drop the universe polymorphism requirement. Then monads from `Type u → Type u` correspond exactly with monoids in the category of Lean.{u} endofunctors. The problem is monads from `Type u → Type v`, since the category of functors from Lean.{u} to Lean.{v} does not have an obvious tensor product. I think if `u > v`, we can define `f ⨂ g := f ∘ PLift ∘ g` using `PLift` to lift the output of `g` from universe `v` to `u`, but I'm not sure what to do in the case when `u < v`. If you have any ideas, I'd love to hear about it.
-/

-- An example of a monad that I don't know how to view categorically yet
abbrev Bad (_ : Type u) : Type v := PUnit

instance : Monad Bad where
  pure _ := ()
  bind x _ := x

instance : LawfulMonad Bad :=
  LawfulMonad.mk' Bad (by simp) (by simp) (by simp) (by simp)

-- TODO: Monads and adjunctions

-- TODO: String diagrams


/-
## Category theory in Lean

Unlike Haskell, Lean is powerful enough that we can also use it for doing category theory in any category, not just the category Lean.
-/

#check CategoryTheory.Category
#check CategoryTheory.Functor
#check CategoryTheory.yoneda
#check CategoryTheory.Monad
#check CategoryTheory.Monad.monadMonEquiv
