#import "@preview/theorion:0.4.1": *
#import "header.typ": *
#show: show-theorion

= Elementary Category Theory and Univalent Foundations
Lecture Notes \
Max Misterka

== Tentative Schedule
- Week 1 (Jan 12 - Jan 15):
  - Jan 12: Intro to Category Theory
  - Jan 13: Lec 1 continued; Universal Properties
  - Jan 14: Functors and Natural Transformations
  - Jan 15: Lec 3 continued
  - Jan 16: canceled due to lecturer availability

- Week 2 (Jan 20 - Jan 23)
  - Jan 19: canceled due to the holiday (Problem Set 1 will be released!)
  - Jan 20: Intro to Algebraic Topology and Homological Algebra (including applications of category theory)
  - Jan 21: Yoneda Lemma; Enriched and Higher Category Theory
  - Jan 22: TBD
  - Jan 23: Category Theory in Haskell ("a monad is a monoid in the category of endofunctors")

- Week 3 (Jan 26 -- Jan 29)
  - Likely no lecture Jan 30
  - Lectures will mostly consist of special topics and applications (order TBD), probably including:
    - Category Theory in Deep Learning
    - Intro to Topos Theory / Toquos Theory
    - Intro to Homotopy Type Theory
    - David Spivak's ideas
    - Connections to philosophy
- Recommended problem sets
  - One per week
  - One or two problems (some with multiple parts) from each lecture, for a total of 5-10 problems
  - Problems relating to a lecture will be written on the blackboard at the end of lecture and will be compiled at the end of the week on this document in the Exercises sections

== What is Category Theory?
Consider the following mathematical objects:
- Sets
- Groups
- Rings
- Topological spaces
Hopefully, if you're in this class, you've heard of at least one of these mathematical objects. If you're familiar with multiple, then you may have noticed some similarities between them:
- The objects are generally sets with extra structure.
- There are "special functions" between two objects which preserve the structure of the objects:
  - Sets: functions
  - Groups: group homomorphisms
  - Rings: ring homomorphisms
  - Vector spaces: linear map
  - Topological spaces: continuous functions
- There is some notion of "equality" between pairs of objects:
  - Sets: bijections
  - Groups: group isomorphisms
  - Rings: ring isomorphisms
  - Vector spaces: vector space isomorphisms
  - Topological spaces: homeomorphisms

Category theory provides a general way to think about all of these classes of objects at once. It is extremely useful in algebraic geometry and algebraic topology, and a few applications have been found outside of math, as we will see later in the course.

== Basic Definitions

#definition(title: "category")[#emph[
  A category $C = (O, M, of)$, where $O$ is a collection of "objects," $M$ is a collection of "morphisms" between objects, and $of$ is an operator that "composes" two morphisms. These must satisfy the following properties:
  - Each morphism $f in M$ is assigned to a "domain" object $dom(f) in O$ and a "codomain" object $cod(f) in O$. If $dom(f) = A$ and $cod(f) = B$, we write $f : A -> B$.
  - If $f : A -> B$ and $g : B -> C$, then the composition operator produces a morphism $g of f : A -> C$.
  - (Identity) For each object $A in O$, there is an identity morphism $1_A : A -> A$ which acts like an identity for the composition operator:
    - if $f : A -> B$ then $f of 1_A = f$,
    - if $g : B -> A$ then $1_A of g = g$.
  - (Associativity) If $f : A -> B$, $g : B -> C$, and $h : C -> D$, then $(h of g) of f = h of (g of f)$.
]]

#example[
  The following are examples of categories:
  - $Set$
  - $Grp$
  - $Ring$
  - $K"-"#h(-0.1em)Vect$, for a field $K$
  - $Top$
  - $NN$, where there is a unique morphism $a -> b$ when $a <= b$
  - $Trivial$
  - $G$, for any group $G$, with one object
]

*TODO: WRITE MORE ABOUT THESE CATEGORIES*

== Isomorphism

How can we generalize the idea of two sets, groups, etc. being isomorphic? Ideally we would define a notion of isomorphism between pairs of objects in a category $C$. This means that we need to state isomorphism purely in terms of the morphisms between sets, groups, etc., ignoring their set-theoretic elements. This can be done using inverse maps.

#definition(title: "isomorphism")[#emph[
  Two objects $A$ and $B$ in the object set of a category $C$ are isomorphic if there are morphisms $f : A -> B$ and $g : B -> A$ such that $f of g = 1_B$ and $g of f = 1_A$.
]]

This is the first example of a recurring trend: we will try to state many important properties of objects like sets, groups, rings, etc. using purely functions and function composition, while ignoring elements.

== Universal Constructions

*TODO: write out the formal definition of a product* (for now, just look at Wikipedia if you want to see it)

- Products

#image("images/product.png")

- Coproducts (duality)
- Initial objects and terminal objects
  - Initial: for every $X$ there is a unique morphism $I -> X$
- Equalizer (kernel of difference)

#image("images/equalizer.png")

- Tensor products (groups, rings, and vector spaces)

#image("images/tensor_product.png")

All of these constructions are unique up to isomorphism. This can be proved by noting that if we have two objects $P_1$ and $P_2$ which are both products, we have a morphism $P_1 -> P_2$ since $P_1$ maps into $X_1$ and $X_2$, but we also have a morphism $P_2 -> P_1$ since $P_2$ maps into $X_1$ and $X_2$, and the diagram commutes. Since these morphisms are the unique morphisms making this diagram commute, $P_1$ and $P_2$ are isomorphic. TODO expand this paragraph

== Functors

All of the objects (groups, rings, etc.) we were considering above have some kind of structure on top of a set. But you may have noticed that categories also have such a structure: they are a set of objects and a set of morphisms with the additional structure of the composition operator. So is there a notion of structure-preserving functions between categories? Yes, and it is called a functor.

#definition(title: "functor")[#emph[
  A functor from a category $C = (O, M, of)$ to a category $C' = (O', M', of')$ is a pair $(F_O, F_M)$, where $F_O : O -> O'$ and $F_M : M -> M'$, such that:
  - If $f in M$ then $dom(F_M (f)) = F_O (dom(f))$ and $cod(F_M (f)) = F_O (cod(f))$.
  - If $A in O$ then $F_M (1_A) = 1'_(F_O (A))$, where $1'$ denotes an identity morphism for an object in $C'$.
  - If $f, g in M$ such that $f of g$ is defined, then $F_M (f of g) = F_M (f) of' F_M (g)$.
]]

We can now consider categories themselves as objects and functors as morphisms between these objects, allowing us to define the category of categories, $Cat$.

*TODO: discuss duality and natural transformations*

#image("images/natural.png")

== Exercises

All of the exercises require answering with a proof for a fully complete answer, but an intuitive justification is good enough if your main goal is to learn the intuition of category theory rather than the entire subject.

- Prove that for the category of sets, the map $Q -> S times T$ in the definition of the product is unique.
- Do all categories have at least one product?
- In general, what is the equalizer between two linear maps in $K"-"#h(-0.1em)Vect$?
- Do all pairs of objects in $Set$ have a coproduct? If so, what is it?
  - What about in $Grp$?
  - What about in $K"-"#h(-0.1em)Vect$?
  - What about in $NN$? What about in the opposite category of $NN$?
- Is $K"-"#h(-0.1em)Vect$ isomorphic (as an object of $Cat$) to its opposite category?

== The Yoneda Lemma

Here $h_A$ is the Hom-functor in a locally small category (which is a category where between a pair of objects, the morphisms can be put into a set): $ h_A (B) = Hom(A, B) = {"morphisms" f : A -> B "in" C}. $

#image("images/yoneda.png")

This generalizes Cayley's theorem from group theory. If the category $C$ is the one-object category constructed from a group $G$, then a functor $F$ from $C$ to $Set$ is just a group action of $G$ on some set $S$. Each object Letting $A$ be the unique object of $C$, Yoneda implies that $Nat(h_A, F)$ is in bijection with $F(A)$. But $F(A)$ is just our set $S$, and $h_A$ can only take in $A$ and output $h_A (A) = Hom(A, A) = G$. So a natural transformation $eta : h_A => F$ must consist of a single map $eta_A : A -> A$ such that for any $f : A -> A$, we have $eta_A of h_A (f) = F(f) of eta_A$. Morphisms $f : A -> A$ are just group elements $g$, and $F$ maps a group element $g$ to its corresponding permutation of the elements of $S$ under the group action. Also, $h_A$ maps $g$ to the map $G -> G$ given by $g' |-> g of g'$. But composition here is just the group operation. So we have that $eta_A (g dot g') = g dot eta_A (g')$, where the $dot$ on the left is the group operation and the dot on the right is the group action. Here $eta_A : G -> S$. Plugging in $g' = e$ gives $eta_A (g) = g dot eta_A (e)$, which causes the condition reduces to $g dot g' dot eta_A (e) = g dot g' dot eta_A (e)$, so this is necessary and sufficient. This means that these natural transformations are given by a single choice of element $eta_A (e) in S$. This proves the lemma for this specific case, and it also shows how it is related to Cayley's theorem: if we set $F = h_A$, then natural transformations from $h_A$ to $F$ can be composed with each other, giving a group structure. This group is a subgroup of the permutation group on the elements of $G$, since each natural transformation consists of a function $eta_A : G -> G$. Also, the map provided by Cayley's theorem happens to be a homomorphism in this case, showing that $G$ is isomorphic to a subgroup of its permutation group.
