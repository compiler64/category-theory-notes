#import "@preview/theorion:0.4.1": *
#import "header.typ": *
#show: show-theorion

= Elementary Category Theory and Univalent Foundations
Lecture Note 1 \
Jan 12, 2026 \
Max Misterka

== Tentative Schedule
- Week 1 (Jan 12 - Jan 16):
  - Jan 12: Intro to Category Theory
  - Jan 13: Important Results (incl. Yoneda Lemma) and More Constructions
  - Jan 14: Enriched and Higher Category Theory
  - Jan 15: Intro to Algebraic Topology and Homological Algebra
  - Jan 16: ??? (potentially canceled)
- Weeks 2 and 3 (Jan 19 - Jan 23, Jan 26 - Jan 29, probably no lecture Jan 30)
  - Will mostly consist of special topics and applications (order TBD), probably including:
    - Category Theory in Haskell
    - Category Theory in Deep Learning
    - Intro to Topos Theory / Toquos Theory
    - Intro to Homotopy Type Theory
    - David Spivak's ideas
- Recommended problem sets
  - One per week
  - One or two problems (some with multiple parts) from each lecture
  - Problems relating to a lecture will be released later that day

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

== Other Universal Constructions

- Products

#image("images/product.png")

- Coproducts (duality)
- Initial objects and terminal objects
  - Initial: for every $X$ there is a unique morphism $I -> X$
- Equalizer (kernel of difference)

#image("images/equalizer.png")

- Tensor products (groups, rings, and vector spaces)

#image("images/tensor_product.png")

*TODO: note that all of these constructions are unique up to isomorphism*

*TODO: introduce functors, $Cat$, and opposite categories*

== Exercises

All of the exercises require answering with a proof for a fully complete answer.

- Do all categories have at least one product?
- Do all pairs of objects in $Set$ have a coproduct? If so, what is it?
  - What about in $Grp$?
  - What about in $K"-"#h(-0.1em)Vect$?
  - What about in $Nat$? What about in the opposite category of $Nat$?
- Is $K"-"#h(-0.1em)Vect$ isomorphic (as an object of $Cat$) to its opposite category?
